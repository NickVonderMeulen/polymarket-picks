#!/usr/bin/env python3
"""
Polymarket smart-money tracker, v2 (READ-ONLY, places no orders).

Each run:
  1. Finds top traders: a wide net from the leaderboard (top 100 by profit this month and all time), drops market
     makers (two-sided books, very high volume, near-certain bets), and ranks the rest by settled-bet edge.
  2. Reads their open positions and groups them by market + side.
  3. Scores every candidate 0-100 (Stage A) on seven signals:
        trader quality 15 | wallet agreement 20 | entry price vs theirs 15 | recent buying 15
        conviction 10 | low opposition 10 | execution quality 15
     then applies hard safety filters (Stage B). A pick is ABOVE THE LINE only if it passes every
     filter and scores at least the cutoff. Everything else is listed below the line with the reasons.
  4. Cross-checks NFL and NBA picks against sportsbook odds (The Odds API, vig removed): a pick is only a bet when the
     books think it is underpriced by at least 3 cents. Other markets cannot be verified and stay below the line.
  4b. Uses the real order book to model a resting limit buy (no taker fee) with a price ceiling near their entry,
     and the spread and available liquidity. If the market has already moved past the ceiling, the pick fails.
  5. Compares with earlier snapshots of the wallets' positions to see who is adding, trimming or has exited.
  6. Drops picks that are the same event as a higher-ranked pick, and caps total suggested exposure.
  7. Logs every pick at the price you would have paid, then tracks how they turned out
     (win rate vs break-even, average return, closing-line move) in a Track Record section.

Also: ranks wallets by settled-bet skill (return on money put in, win rate vs the odds they paid) when the
API provides that history, counts wallets that trade alike once, favors category specialists, reads each
market's real minimum order size, and publishes Picks / Wallets / Activity / Results tabs.

Standard library only. Python 3.9+.

  python polytracker.py              run, write report.html
  python polytracker.py --email      also email the report
  python polytracker.py --debug      print coverage stats
  python polytracker.py --evaluate   print the track record and exit

Email env vars (Gmail App Password): SMTP_HOST SMTP_PORT SMTP_USER SMTP_PASS MAIL_TO
Bankroll can be set with env var BANKROLL (e.g. BANKROLL=31.50) or in CONFIG below.
The weights and limits below are starting guesses, not proven settings. The Track Record decides.
"""
import argparse
import json
import math
import os
import re
import smtplib
import sqlite3
import ssl
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from email.mime.text import MIMEText
from html import escape

DATA_API = "https://data-api.polymarket.com"
GAMMA_API = "https://gamma-api.polymarket.com"
CLOB_API = "https://clob.polymarket.com"
HERE = os.path.dirname(os.path.abspath(__file__))
# Change this whenever you change the scoring or the rules. Picks are stamped with it, and the Results verdict
# counts only picks made under the current version, so every rule set gets its own clean paper-trade sample.
ENGINE_VERSION = "2.4"
DB_PATH = os.environ.get("DB_PATH", os.path.join(HERE, "picks.db"))
REPORT_PATH = os.path.join(HERE, "report.html")

# ---------------- Settings you can tune ----------------
CONFIG = {
    # Who to follow
    # Wallets come from a wide net (top N by profit this month and all time), are screened for market makers,
    # then ranked by settled-bet edge, not by raw profit.
    "windows": ["month", "all"],
    "leaderboard_size": 100,       # top N per window
    "min_windows": 1,              # wallet must be top-N in this many windows to enter the screening pool
    "screen_pool": 60,             # wallets whose settled history is checked
    "max_wallets": 30,             # wallets followed after screening
    "min_settled_bets": 20,        # settled bets needed before a wallet counts as proven
    "min_proven_wallets": 15,      # below this many proven wallets, unproven ones fill the list
    "max_two_sided_frac": 0.15,    # drop wallets that held both sides in more than this share of their markets
    "max_settled_positions": 0,    # 0 = off. A cap of 500 dropped 27 of 66 wallets, i.e. almost every active top trader
    "high_price": 0.93,            # entries at or above this are near-certain bets
    "max_high_price_frac": 0.50,   # drop wallets whose bets are mostly near-certain (liquidity farming at 93c+)
    "hedge_ratio": 0.10,           # a wallet holding both sides of a market, smaller side at least this share, is hedged
    "positions_limit": 200,
    # What counts as a candidate
    "min_position_usd": 100,       # ignore small positions when forming a pick
    "snapshot_min_usd": 25,        # positions this big are remembered between runs
    "min_wallets_listed": 2,       # list anything with at least this many wallets agreeing
    "max_listed": 25,
    "enrich_limit": 35,            # how many top candidates get order-book + date lookups
    # Stage B: safety filters. Failing ANY of these puts a pick below the line.
    "cutoff_score": 60,
    "min_wallets_bet": 2,
    "min_price": 0.10,             # what you would actually pay, fee included
    "max_price": 0.85,
    "max_drift": 0.05,             # limit price ceiling: never more than 5c over their average entry
    "max_opposition_ratio": 0.35,  # top-wallet money on the other side vs agreeing money
    "max_spread": 0.08,            # best ask minus best bid
    "min_depth_multiple": 3.0,     # shares for sale within 3c of the best ask must cover this many stakes
    "exit_fraction": 0.5,          # fail if this share of earlier top holders has since sold out
    # Stage A: score weights (must add to 100)
    "weights": {"quality": 15, "agreement": 20, "entry": 15, "buying": 15,
                "conviction": 10, "opposition": 10, "execution": 15},
    # Independent check: devigged sportsbook odds (The Odds API, free key in env ODDS_API_KEY) for NFL and NBA games
    "verify_required": True,       # a pick can only be above the line if sportsbooks agree it is underpriced
    "min_book_edge": 0.03,         # sportsbook fair probability must beat your limit price by this much (3 cents)
    "odds_regions": "us",
    "odds_markets": "h2h,spreads,totals",   # credits per call = markets x regions = 3, once per sport per run
    "odds_min_books": 2,           # sportsbooks quoting the exact same line before the consensus is trusted
    "odds_min_remaining": 20,      # stop calling when this few credits are left
    # Staking: a % of bankroll, never more than the exposure cap in total per report
    "bankroll": 25.0,
    "stake_pct_min": 0.01,         # at the cutoff score
    "stake_pct_max": 0.03,         # at a perfect score (max single position)
    "max_total_exposure_pct": 0.10,
    "min_stake": 1.0,              # Polymarket's practical minimum order, about $1
    # History
    "snapshot_min_age_hours": 6,   # compare against a snapshot at least this old
    "snapshot_max_age_hours": 96,
    "snapshot_keep_days": 4,
    "tracking_days": 90,
    "tracking_lookups": 120,       # max market lookups per run for the track record
    "min_resolved_for_verdict": 30,
    # Wallet skill (from settled bets), independence and category specialists
    "skill_pages": 3,              # pages of settled positions read per wallet and status
    "skill_prior": 30,             # settled bets needed before a wallet's record counts fully
    "skill_refresh_days": 3,       # settled-bet stats are cached this long
    "unknown_skill": 0.40,         # a wallet with no settled history counts as unproven: below a good record
    "skill_refresh_per_run": 30,   # wallets refreshed per run, so one run never makes hundreds of calls
    "conviction_full_x": 5.0,      # a bet this many times the wallet's median bet earns full conviction points
    "conviction_unknown": 0.25,    # share of conviction points when the wallet's usual bet size is unknown
    "independence_overlap": 0.6,   # wallets sharing this much of their bets are treated as one strategy
    "independence_min_positions": 5,
    "categories": ["sports", "politics", "crypto", "economics"],
    "category_board_size": 50,     # top N this month in the category counts as a specialist
    "category_bonus": 0.15,        # added to trader quality when all agreeing wallets are specialists
    "activity_limit": 25,
    "timezone": "America/New_York",
    "pause_seconds": 0.2,
}

# Taker fee rate by market category, from Polymarket's published fee table.
# fee per share = rate * price * (1 - price). Check docs.polymarket.com/trading/fees for changes.
FEE_RATES = [("geopolitic", 0.0), ("crypto", 0.07), ("sport", 0.05), ("politic", 0.04),
             ("financ", 0.04), ("econom", 0.05), ("culture", 0.05), ("weather", 0.05),
             ("tech", 0.04), ("mention", 0.04)]
DEFAULT_FEE_RATE = 0.05

WEIGHT_LABELS = [("agreement", "agree"), ("quality", "quality"), ("entry", "entry"), ("buying", "buying"),
                 ("conviction", "conviction"), ("opposition", "opposition"), ("execution", "execution")]


# ---------------- HTTP + small helpers ----------------
def get_json(base, path, params=None, retries=3):
    url = base + path
    if params:
        url += "?" + urllib.parse.urlencode(params)
    last = None
    for attempt in range(retries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "polytracker/2.0"})
            with urllib.request.urlopen(req, timeout=30) as r:
                return json.loads(r.read().decode())
        except Exception as e:
            last = e
            time.sleep(1.5 * (attempt + 1))
    raise RuntimeError("GET " + url + " failed: " + str(last))


def num(x, default=0.0):
    try:
        return float(x)
    except (TypeError, ValueError):
        return default


def clamp(x, lo=0.0, hi=1.0):
    return max(lo, min(hi, x))


def rows_of(resp):
    """Data API v2 wraps results as {"data": [...], "pagination": {...}}. Accept a bare list too."""
    if isinstance(resp, dict):
        resp = resp.get("data")
    return resp if isinstance(resp, list) else []


def field(d, *names, default=None):
    """First present key among names (v2 uses snake_case; camelCase kept as a fallback)."""
    for n in names:
        if d.get(n) not in (None, ""):
            return d[n]
    return default


def json_list(x):
    if isinstance(x, list):
        return x
    if isinstance(x, str):
        try:
            v = json.loads(x)
            return v if isinstance(v, list) else []
        except ValueError:
            return []
    return []


def now_local():
    """Current time in the configured time zone (falls back to the machine's own)."""
    try:
        from zoneinfo import ZoneInfo
        return datetime.now(ZoneInfo(CONFIG["timezone"]))
    except Exception:
        return datetime.now().astimezone()


# ---------------- Step 1: pick wallets ----------------
def fetch_leaderboard(window):
    last = None
    for size in dict.fromkeys([CONFIG["leaderboard_size"], 50, 40]):   # fall back if the API caps the page size
        try:
            resp = get_json(DATA_API, "/v2/leaderboard", {
                "category": "overall",
                "time_period": window,   # day / week / month / all
                "sort_by": "PNL",
                "limit": size,
            })
            return rows_of(resp)
        except Exception as e:
            last = e
    raise last


def shrunk_edge(st):
    """Win rate minus the win rate their entry prices implied, pulled toward zero for small samples."""
    n = st["n"]
    return (st["win_rate"] - st["implied"]) * n / float(n + CONFIG["skill_prior"])


def wallet_flag(st):
    """Reason to drop a wallet as a market maker or farmer rather than a directional trader, or ''."""
    if st.get("two_sided") is not None and st["two_sided"] > CONFIG["max_two_sided_frac"]:
        return "holds both sides in %.0f%% of its markets (market maker)" % (st["two_sided"] * 100)
    if CONFIG["max_settled_positions"] and (st.get("positions") or 0) > CONFIG["max_settled_positions"]:
        return "%d settled positions (high-frequency)" % st["positions"]
    if st.get("hi_price") is not None and st["hi_price"] > CONFIG["max_high_price_frac"]:
        return "%.0f%% of bets entered at %.0fc or more (liquidity farming)" % (st["hi_price"] * 100, CONFIG["high_price"] * 100)
    return ""


_SCREEN = {}


def choose_wallets(con=None):
    appearances = defaultdict(lambda: {"windows": set(), "name": "", "pnl": 0.0, "best_rank": None})
    for w in CONFIG["windows"]:
        for idx, row in enumerate(fetch_leaderboard(w), 1):
            addr = str(field(row, "user_id", "proxy_wallet", "proxyWallet", default="")).lower()
            if not addr:
                continue
            a = appearances[addr]
            a["windows"].add(w)
            a["name"] = field(row, "user_name", "userName", default=a["name"] or addr[:8])
            a["pnl"] = max(a["pnl"], num(row.get("pnl")))
            rank = int(num(row.get("rank"), idx)) or idx
            a["best_rank"] = rank if a["best_rank"] is None else min(a["best_rank"], rank)
        time.sleep(CONFIG["pause_seconds"])
    kept = {k: v for k, v in appearances.items() if len(v["windows"]) >= CONFIG["min_windows"]}
    ranked = sorted(kept.items(), key=lambda kv: (-len(kv[1]["windows"]), -kv[1]["pnl"]))
    if con is None:
        return dict(ranked[: CONFIG["max_wallets"]])
    return screen_wallets(con, dict(ranked[: CONFIG["screen_pool"]]))


def screen_wallets(con, pool):
    """Drop market makers and farmers, then rank what is left by settled-bet edge instead of raw profit."""
    stats = ensure_wallet_stats(con, pool)
    proven, unproven, dropped = [], [], []
    for addr in pool:                       # pool order = leaderboard standing
        st = stats.get(addr)
        if not st:
            unproven.append(addr)           # no settled history found (yet)
            continue
        flag = wallet_flag(st)
        if flag:
            dropped.append((pool[addr]["name"], flag))
        elif st["n"] < CONFIG["min_settled_bets"]:
            unproven.append(addr)
        elif st["roi"] <= 0 or shrunk_edge(st) <= 0:
            dropped.append((pool[addr]["name"], "no edge on %d settled bets (return %+.0f%%, win rate %.0f%% vs %.0f%% implied)" % (
                st["n"], st["roi"] * 100, st["win_rate"] * 100, st["implied"] * 100)))
        else:
            proven.append((skill_score(st), addr))
    proven.sort(key=lambda x: -x[0])
    chosen = [a for _, a in proven[: CONFIG["max_wallets"]]]
    filled = 0
    if len(chosen) < CONFIG["min_proven_wallets"]:
        for a in unproven:
            if len(chosen) >= CONFIG["max_wallets"]:
                break
            chosen.append(a)
            filled += 1
    _SCREEN.update({"pool": len(pool), "proven": len(proven), "unproven": len(unproven), "dropped": dropped, "filled": filled})
    return {a: pool[a] for a in chosen}


def board_standing(info):
    """0-1. Showing up in more leaderboard windows and ranking higher counts for more."""
    w = len(info["windows"]) / float(max(len(CONFIG["windows"]), 1))
    r = info.get("best_rank")
    size = CONFIG["leaderboard_size"]
    rk = 0.5 if not r else 1 - (min(r, size) - 1) / float(size)
    return 0.6 * w + 0.4 * rk


def skill_score(stats):
    """0-1 from settled-bet history, or None when there is none. Small samples are pulled toward average."""
    if not stats or not stats.get("n"):
        return None
    n = stats["n"]
    shrink = n / float(n + CONFIG["skill_prior"])
    roi_s = clamp((stats["roi"] * shrink + 0.05) / 0.30)
    edge_s = clamp(((stats["win_rate"] - stats["implied"]) * shrink + 0.05) / 0.15)
    return 0.6 * roi_s + 0.4 * edge_s


def wallet_quality(info, stats=None, unknown=None):
    """0-1. Leaderboard standing, blended 40/60 with settled-bet skill. `unknown` is the skill given to a wallet with
    no history; it is None when nobody has any history (the data is simply unavailable), so standing alone is used."""
    standing = board_standing(info)
    skill = skill_score(stats)
    if skill is None:
        if unknown is None:
            return standing
        skill = unknown
    return 0.4 * standing + 0.6 * skill


# ---------------- Step 2: positions ----------------
def fetch_positions(addr):
    """Returns (rows, truncated). Follows the cursor for up to 3 pages."""
    rows, cursor = [], None
    for _ in range(3):
        params = {"user": addr, "status": "OPEN", "limit": CONFIG["positions_limit"]}
        if cursor:
            params["cursor"] = cursor
        resp = get_json(DATA_API, "/v2/positions", params)
        rows += rows_of(resp)
        cursor = None
        if isinstance(resp, dict):
            cursor = (resp.get("pagination") or {}).get("next_cursor")
        if not cursor:
            break
        time.sleep(CONFIG["pause_seconds"])
    return rows, bool(cursor)


def fetch_status_rows(addr, status):
    """Positions with one lifecycle status (CLOSED, REDEEMABLE, REDEEMABLE_LOST). Follows the cursor."""
    rows, cursor = [], None
    for _ in range(CONFIG["skill_pages"]):
        params = {"user": addr, "status": status, "limit": CONFIG["positions_limit"]}
        if cursor:
            params["cursor"] = cursor
        resp = get_json(DATA_API, "/v2/positions", params, retries=2)
        rows += rows_of(resp)
        cursor = (resp.get("pagination") or {}).get("next_cursor") if isinstance(resp, dict) else None
        if not cursor:
            break
        time.sleep(CONFIG["pause_seconds"])
    return rows


def wallet_track(rows):
    """Skill stats from settled positions: count, win rate, return on money put in, the win rate their prices implied,
    plus market-maker tells (both sides held, position count, near-certain entries) and their median bet size."""
    n = wins = 0
    cost_sum = pnl_sum = implied_sum = 0.0
    costs, hi = [], 0
    sides = defaultdict(set)
    for r in rows:
        avg = num(field(r, "avg_price", "avgPrice"), 0.5)
        cost = num(field(r, "entry_cost_usdc", "entryCostUsdc", "initialValue"))
        if cost <= 0:
            cost = num(field(r, "total_bought", "totalBought", "current_size", "size")) * avg
        if cost <= 0:
            continue
        realized, unrealized = field(r, "realized_pnl", "realizedPnl"), field(r, "unrealized_pnl", "unrealizedPnl")
        if realized is None and unrealized is None:
            pnl = num(field(r, "current_value", "currentValue", default=0)) - cost
        else:
            pnl = num(realized) + num(unrealized)
        n += 1
        wins += 1 if pnl > 0 else 0
        cost_sum += cost
        pnl_sum += pnl
        implied_sum += clamp(avg)
        costs.append(cost)
        hi += 1 if avg >= CONFIG["high_price"] else 0
        cond = field(r, "condition_id", "conditionId")
        side = field(r, "outcome", "token_id", "asset", "asset_id")
        if cond and side is not None:
            sides[cond].add(str(side))
    if n == 0:
        return None
    costs.sort()
    med = costs[n // 2] if n % 2 else (costs[n // 2 - 1] + costs[n // 2]) / 2.0
    return {"n": n, "wins": wins, "roi": pnl_sum / cost_sum, "win_rate": wins / float(n), "implied": implied_sum / n,
            "positions": len(rows), "med_cost": med, "hi_price": hi / float(n),
            "two_sided": (sum(1 for v in sides.values() if len(v) >= 2) / float(len(sides))) if sides else None}


STAT_COLS = ("n", "wins", "roi", "win_rate", "implied", "positions", "med_cost", "hi_price", "two_sided")


def ensure_wallet_stats(con, wallets):
    """Settled-bet stats per wallet, cached in the database and refreshed a few wallets per run."""
    out, stale = {}, []
    cutoff = datetime.now(timezone.utc) - timedelta(days=CONFIG["skill_refresh_days"])
    for addr in wallets:
        r = con.execute("SELECT ts, %s FROM wallet_stats WHERE wallet = ?" % ", ".join(STAT_COLS), (addr,)).fetchone()
        if r:
            out[addr] = {k: r[k] for k in STAT_COLS} if r["n"] else None
        # never looked up, cached by an older version (no position count), or past the refresh age
        if r is None or r["positions"] is None or datetime.fromisoformat(r["ts"]) < cutoff:
            stale.append((addr, r is not None))
    stale.sort(key=lambda x: x[1])   # wallets never looked up come first
    failed = 0
    for addr, _ in stale[: CONFIG["skill_refresh_per_run"]]:
        try:
            rows = []
            for status in ("CLOSED", "REDEEMABLE", "REDEEMABLE_LOST"):
                rows += fetch_status_rows(addr, status)
            st = wallet_track(rows)
        except Exception as e:
            failed += 1
            if failed <= 2:
                print("no settled-bet history for", addr[:10], str(e)[:90])
            continue
        vals = [st[k] for k in STAT_COLS] if st else [0, 0, 0.0, 0.0, 0.0, 0, None, None, None]
        con.execute("INSERT OR REPLACE INTO wallet_stats(wallet, ts, %s) VALUES (?,?,%s)" % (
            ", ".join(STAT_COLS), ",".join("?" * len(STAT_COLS))),
            (addr, datetime.now(timezone.utc).isoformat()) + tuple(vals))
        out[addr] = st
        time.sleep(CONFIG["pause_seconds"])
    con.commit()
    return out


def fetch_category_boards():
    """{category: set of wallets in that category's top N this month}. Categories the API rejects are skipped."""
    boards = {}
    for cat in CONFIG["categories"]:
        try:
            resp = get_json(DATA_API, "/v2/leaderboard", {"category": cat, "time_period": "month", "sort_by": "PNL",
                                                           "limit": CONFIG["category_board_size"]}, retries=1)
            addrs = {str(field(r, "user_id", "proxy_wallet", "proxyWallet", default="")).lower() for r in rows_of(resp)}
            addrs.discard("")
            if addrs:
                boards[cat] = addrs
        except Exception:
            pass
        time.sleep(CONFIG["pause_seconds"])
    return boards


_CAT_BOARDS = {}
_GAMMA_CACHE = {}


def gamma_market(condition_id, closed_fallback=False):
    """One market from the Gamma API (cached for this run). None if not found."""
    if condition_id in _GAMMA_CACHE:
        return _GAMMA_CACHE[condition_id]
    m = None
    try:
        rows = get_json(GAMMA_API, "/markets", {"condition_ids": condition_id}, retries=1)
        if not rows and closed_fallback:
            rows = get_json(GAMMA_API, "/markets", {"condition_ids": condition_id, "closed": "true"}, retries=1)
        if rows:
            m = rows[0]
    except Exception:
        m = None
    _GAMMA_CACHE[condition_id] = m
    return m


def market_info(m):
    """Slug, dates, category and outcome->token map from a Gamma market. Missing pieces are ''."""
    out = {"slug": "", "event_slug": "", "start": "", "end": "", "category": "", "tokens": {}, "is_sports": False}
    if not m:
        return out
    evs = m.get("events") or [{}]
    ev = evs[0] if isinstance(evs[0], dict) else {}
    out["event_slug"] = ev.get("slug") or ""
    out["slug"] = ev.get("slug") or m.get("slug") or ""
    out["start"] = m.get("gameStartTime") or ""   # real game start times only; an event's listing date is not a start
    out["end"] = m.get("endDate") or ev.get("endDate") or ""
    tag_items = list(m.get("tags") or []) + list(ev.get("tags") or [])
    tags = " ".join("%s %s" % (t.get("label") or "", t.get("slug") or "") for t in tag_items if isinstance(t, dict))
    cat_items = list(m.get("categories") or []) + list(ev.get("categories") or [])
    cats = " ".join(str(c.get("label") or "") for c in cat_items if isinstance(c, dict))
    # Polymarket marks game markets with these fields even when no text category is set
    out["is_sports"] = bool(m.get("sportsMarketType") or m.get("gameId") or m.get("teamAID") or m.get("teamBID"))
    out["category"] = ("%s %s %s%s" % (m.get("category") or ev.get("category") or "", cats, tags,
                                       " sports" if out["is_sports"] else "")).strip().lower()
    out["tokens"] = dict(zip(json_list(m.get("outcomes")), json_list(m.get("clobTokenIds"))))
    return out


def outcome_price(m, outcome):
    """(current price, closed) of an outcome from a Gamma market; (None, closed) if unknown."""
    if not m:
        return None, False
    outcomes, prices = json_list(m.get("outcomes")), json_list(m.get("outcomePrices"))
    closed = bool(m.get("closed"))
    if outcome in outcomes and len(prices) == len(outcomes):
        return num(prices[outcomes.index(outcome)]), closed
    return None, closed


def fee_rate_for(category_text):
    t = category_text or ""
    for key, rate in FEE_RATES:
        if key in t:
            return rate
    return DEFAULT_FEE_RATE


def analyze_book(book, ref_stake):
    """Best ask/bid, spread, nearby liquidity and the average price to fill ref_stake dollars."""
    asks = sorted(((num(a.get("price")), num(a.get("size"))) for a in (book.get("asks") or [])
                   if num(a.get("size")) > 0), key=lambda x: x[0])
    bids = sorted(((num(b.get("price")), num(b.get("size"))) for b in (book.get("bids") or [])
                   if num(b.get("size")) > 0), key=lambda x: -x[0])
    out = {"ask": None, "bid": bids[0][0] if bids else None, "spread": None, "depth": 0.0, "exec_price": None,
           "min_size": num(book.get("min_order_size")), "tick": num(book.get("tick_size"), 0.01) or 0.01, "mid": None}
    if not asks:
        return out
    best = asks[0][0]
    out["ask"] = best
    if bids:
        out["spread"] = best - bids[0][0]
        out["mid"] = (best + bids[0][0]) / 2.0
    out["depth"] = sum(pr * sz for pr, sz in asks if pr <= best + 0.03)
    remaining, cost, shares = ref_stake, 0.0, 0.0
    for pr, sz in asks:
        if pr <= 0:
            continue
        take = min(remaining / pr, sz)
        cost += take * pr
        shares += take
        remaining -= take * pr
        if remaining <= 1e-9:
            break
    if remaining <= 1e-6 and shares > 0:
        out["exec_price"] = cost / shares
    return out


# ---------------- Step 3: history (snapshots of what the wallets hold) ----------------
def load_baseline(con):
    """Newest snapshot that is at least snapshot_min_age_hours old. Returns (timestamp, {(wallet,cond,outcome): shares}, {(wallet,cond,outcome): (value, title)})."""
    now = datetime.now(timezone.utc)
    hi = (now - timedelta(hours=CONFIG["snapshot_min_age_hours"])).isoformat()
    lo = (now - timedelta(hours=CONFIG["snapshot_max_age_hours"])).isoformat()
    row = con.execute("SELECT MAX(ts) FROM snapshots WHERE ts <= ? AND ts >= ?", (hi, lo)).fetchone()
    if not row or not row[0]:
        return None, {}, {}
    data, meta = {}, {}
    for w, c, o, sh, v, t in con.execute(
            "SELECT wallet, condition_id, outcome, shares, value, title FROM snapshots WHERE ts = ?", (row[0],)):
        data[(w, c, o)] = sh
        meta[(w, c, o)] = (v or 0.0, t or "")
    return row[0], data, meta


def save_snapshot(con, wallet_positions):
    ts = datetime.now(timezone.utc).isoformat()
    rows = []
    for addr, info in wallet_positions.items():
        for p in info["positions"]:
            if p.get("redeemable") or p.get("mergeable"):
                continue
            cond, outcome = field(p, "condition_id", "conditionId"), p.get("outcome")
            shares = num(field(p, "current_size", "size", default=0))
            value = num(field(p, "current_value", "currentValue", default=0))
            if cond and outcome is not None and shares > 0 and value >= CONFIG["snapshot_min_usd"]:
                rows.append((ts, addr, cond, outcome, shares, value, p.get("title") or ""))
    con.executemany("INSERT INTO snapshots(ts, wallet, condition_id, outcome, shares, value, title) VALUES (?,?,?,?,?,?,?)", rows)
    keep = (datetime.now(timezone.utc) - timedelta(days=CONFIG["snapshot_keep_days"])).isoformat()
    con.execute("DELETE FROM snapshots WHERE ts < ?", (keep,))
    con.commit()
    con.execute("VACUUM")


def compute_flow(g, cond, outcome, baseline, base_by_side, baseline_wallets, wallet_positions):
    """Who is adding, trimming or has exited since the baseline snapshot."""
    new = added = trimmed = exited = 0
    for a, sh in g["shares_by"].items():
        if a not in baseline_wallets:
            continue   # wallet was not tracked back then, so we cannot say what changed
        before = baseline.get((a, cond, outcome), 0.0)
        if before <= 0:
            new += 1
        elif sh > before * 1.10:
            added += 1
        elif sh < before * 0.90:
            trimmed += 1
    for a, before in base_by_side.get((cond, outcome), []):
        if a in g["wallets"]:
            continue
        info = wallet_positions.get(a)
        if info and not info["truncated"]:
            exited += 1
    return {"new": new, "added": added, "trimmed": trimmed, "exited": exited, "holders_now": len(g["wallets"])}


def compute_activity(wallet_positions, baseline, meta):
    """Moves by every followed wallet since the baseline snapshot, biggest dollar moves first."""
    if not baseline:
        return []
    tracked = {w for (w, _, _) in baseline}
    events, still = [], set()
    for addr, info in wallet_positions.items():
        if addr not in tracked:
            continue
        for p in info["positions"]:
            if p.get("redeemable") or p.get("mergeable"):
                continue
            cond, outcome = field(p, "condition_id", "conditionId"), p.get("outcome")
            shares = num(field(p, "current_size", "size", default=0))
            value = num(field(p, "current_value", "currentValue", default=0))
            if not cond or outcome is None or shares <= 0 or value < CONFIG["snapshot_min_usd"]:
                continue
            key = (addr, cond, outcome)
            still.add(key)
            before, price = baseline.get(key, 0.0), value / shares
            if before <= 0:
                kind, delta = "new", value
            elif shares > before * 1.10:
                kind, delta = "added", (shares - before) * price
            elif shares < before * 0.90:
                kind, delta = "trimmed", (shares - before) * price
            else:
                continue
            events.append({"name": info["name"], "kind": kind, "title": p.get("title") or "", "outcome": outcome,
                           "delta": delta, "now": value})
    for key in baseline:
        addr = key[0]
        info = wallet_positions.get(addr)
        if key in still or not info or info["truncated"]:
            continue
        value, title = meta.get(key, (0.0, ""))
        if value >= CONFIG["snapshot_min_usd"]:
            events.append({"name": info["name"], "kind": "gone", "title": title, "outcome": key[2],
                           "delta": -value, "now": 0.0})
    events.sort(key=lambda e: -abs(e["delta"]))
    return events[: CONFIG["activity_limit"]]


def independent_count(addrs, sides_of):
    """How many separate groups the wallets form. Wallets whose bets overlap heavily likely follow one strategy."""
    addrs = list(addrs)
    parent = {a: a for a in addrs}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for i, a in enumerate(addrs):
        for b in addrs[i + 1:]:
            sa, sb = sides_of.get(a, set()), sides_of.get(b, set())
            if min(len(sa), len(sb)) < CONFIG["independence_min_positions"]:
                continue
            if len(sa & sb) / float(len(sa | sb)) >= CONFIG["independence_overlap"]:
                parent[find(a)] = find(b)
    return len({find(a) for a in addrs})


# ---------------- Step 4: candidates, scoring, safety filters ----------------
def build_candidates(wallet_positions, baseline):
    groups = defaultdict(lambda: {
        "title": "", "outcome": "", "slug": "", "wallets": {}, "shares_by": {}, "cost_by": {},
        "cur_price": 0.0, "cost_total": 0.0, "shares_total": 0.0, "token_id": "", "end": "",
    })
    side_money = defaultdict(lambda: defaultdict(float))
    sides_of = defaultdict(set)
    # A wallet holding both sides of a market is quoting or hedging, not making a directional bet: skip those markets.
    hedged = {}
    for addr, info in wallet_positions.items():
        legs = defaultdict(dict)
        for p in info["positions"]:
            cond = field(p, "condition_id", "conditionId")
            if not cond or p.get("outcome") is None or p.get("redeemable") or p.get("mergeable"):
                continue
            legs[cond][p["outcome"]] = legs[cond].get(p["outcome"], 0.0) + num(field(p, "current_value", "currentValue", default=0))
        hedged[addr] = {c for c, d in legs.items()
                        if len(d) >= 2 and sorted(d.values())[-2] >= CONFIG["hedge_ratio"] * max(d.values())}

    for addr, info in wallet_positions.items():
        for p in info["positions"]:
            cond = field(p, "condition_id", "conditionId")
            outcome = p.get("outcome")
            if not cond or outcome is None:
                continue
            if p.get("redeemable") or p.get("mergeable"):   # already resolved
                continue
            if cond in hedged[addr]:
                continue
            shares = num(field(p, "current_size", "size", default=0))
            value = num(field(p, "current_value", "currentValue", default=0))
            if value < CONFIG["min_position_usd"] or shares <= 0:
                continue
            side_money[cond][outcome] += value
            sides_of[addr].add((cond, outcome))
            g = groups[(cond, outcome)]
            g["title"] = p.get("title", g["title"])
            g["slug"] = field(p, "event_slug", "eventSlug", "slug", default=g["slug"])
            g["outcome"] = outcome
            g["token_id"] = str(field(p, "token_id", "asset", "asset_id", default=g["token_id"]))
            g["end"] = field(p, "end_date", "endDate", default=g["end"])
            g["cur_price"] = num(field(p, "cur_price", "curPrice", "current_price"), value / shares)
            g["cost_total"] += shares * num(field(p, "avg_price", "avgPrice", default=0))
            paid = num(field(p, "entry_cost_usdc", "entryCostUsdc"))
            if paid <= 0:
                paid = shares * num(field(p, "avg_price", "avgPrice", default=0))
            g["cost_by"][addr] = g["cost_by"].get(addr, 0.0) + paid
            g["shares_total"] += shares
            g["wallets"][addr] = g["wallets"].get(addr, 0.0) + value
            g["shares_by"][addr] = g["shares_by"].get(addr, 0.0) + shares

    base_by_side = defaultdict(list)
    baseline_wallets = set()
    for (w, c, o), sh in baseline.items():
        base_by_side[(c, o)].append((w, sh))
        baseline_wallets.add(w)

    picks = []
    for (cond, outcome), g in groups.items():
        n = len(g["wallets"])
        if n < CONFIG["min_wallets_listed"] or g["shares_total"] <= 0:
            continue
        agree = sum(g["wallets"].values())
        oppose = sum(m for o, m in side_money[cond].items() if o != outcome)
        quality = (sum(wallet_positions[a]["quality"] * v for a, v in g["wallets"].items()) / agree) if agree else 0.5
        # Conviction = this bet's cost as a multiple of the wallet's own median settled bet (not a share of open positions,
        # which ignores idle cash and punishes wallets that spread across many markets).
        convs = [min(c / wallet_positions[a]["med_cost"], 20.0) for a, c in g["cost_by"].items()
                 if (wallet_positions[a].get("med_cost") or 0) > 0]
        flow = compute_flow(g, cond, outcome, baseline, base_by_side, baseline_wallets, wallet_positions) if baseline else None
        picks.append({
            "condition_id": cond, "title": g["title"], "outcome": outcome, "slug": g["slug"],
            "event_slug": "", "wallets": n, "eff_wallets": independent_count(g["wallets"], sides_of),
            "agree_money": agree, "oppose_money": oppose,
            "opp_ratio": oppose / agree if agree else 1.0,
            "avg_entry": g["cost_total"] / g["shares_total"], "mid": g["cur_price"],
            "quality": quality, "conviction": (sum(convs) / len(convs)) if convs else None, "flow": flow,
            "holders": sorted(g["wallets"].items(), key=lambda kv: -kv[1]),
            "token_id": g["token_id"], "start": "", "end": g["end"], "category": "", "fee_rate": DEFAULT_FEE_RATE,
            "book": None, "exec_price": None, "all_in": None, "limit": None, "limit_ceiling": None, "fillable": True,
            "fair": None, "book_edge": None, "books": None, "verify_note": "not checked yet",
            "tier": "watch", "why": [], "parts": {}, "score": 0.0, "drift": 0.0,
            "stake": None, "stake_pct": None, "capped": False,
            "specialty": "", "specialists": 0, "specialist_share": 0.0, "min_order_usd": None, "min_over_cap": False,
        })
    return picks


def ref_stake():
    return max(CONFIG["min_stake"], CONFIG["bankroll"] * CONFIG["stake_pct_max"])


def entry_price(p):
    """The limit price we model: a resting buy just above the best bid (no taker fee), capped near their entry.
    Without a usable order book, the midpoint."""
    if p.get("limit") is not None:
        return p["limit"]
    return p["all_in"] if p.get("all_in") else p["mid"]


def set_limit(p):
    """Maker execution: rest a buy one tick above the best bid instead of crossing the spread and paying the taker fee.
    The ceiling is their average entry plus max_drift, and never above the midpoint. If the best bid is already over the
    ceiling, there is no price near their entry where an order would fill, so the pick fails."""
    b = p.get("book")
    if not b or b["bid"] is None:
        return
    tick, bid, ask = b["tick"], b["bid"], b["ask"]
    maker = bid + tick
    if ask is not None and maker >= ask - 1e-9:
        maker = bid                      # spread is a single tick: join the bid instead of crossing
    ref_mid = b["mid"] if b["mid"] is not None else p["mid"]
    ceiling = min(p["avg_entry"] + CONFIG["max_drift"], ref_mid)
    ceiling = round(math.floor(ceiling / tick + 1e-9) * tick, 4)
    p["limit_ceiling"] = ceiling
    p["limit"] = round(min(maker, ceiling), 4)
    p["fillable"] = ceiling >= bid - 1e-9


def buying_fraction(flow):
    if flow is None:
        return 0.5   # no history yet: neutral
    buyers, sellers = flow["new"] + flow["added"], flow["trimmed"] + flow["exited"]
    denom = max(flow["holders_now"] + flow["exited"], 1)
    return 0.5 + 0.5 * clamp((buyers - sellers) / float(denom), -1.0, 1.0)


def execution_fraction(p):
    b = p.get("book")
    if not b:
        return 0.5   # no order book: neutral
    if b["exec_price"] is None:
        return 0.0
    spread_score = 0.5 if b["spread"] is None else 1 - clamp(b["spread"] / 0.10)
    depth_score = clamp(b["depth"] / (5.0 * ref_stake()))
    return 0.6 * spread_score + 0.4 * depth_score


def assess(p):
    """Compute the score (Stage A) and the hard filters (Stage B) from the pick's current data."""
    W, C = CONFIG["weights"], CONFIG
    price = entry_price(p)
    drift = price - p["avg_entry"]
    p["drift"] = drift
    parts = {
        "agreement": W["agreement"] * min(p.get("eff_wallets", p["wallets"]), 6) / 6.0,
        "quality": W["quality"] * clamp(p["quality"] + C["category_bonus"] * p.get("specialist_share", 0.0)),
        "entry": W["entry"] * (1 - clamp(max(drift, 0) / (2 * C["max_drift"]))),
        "buying": W["buying"] * buying_fraction(p["flow"]),
        "conviction": W["conviction"] * (C["conviction_unknown"] if p["conviction"] is None
                                         else clamp((p["conviction"] - 0.5) / (C["conviction_full_x"] - 0.5))),
        "opposition": W["opposition"] * (1 - clamp(p["opp_ratio"])),
        "execution": W["execution"] * execution_fraction(p),
    }
    score = sum(parts.values())
    why = []
    n = p.get("eff_wallets", p["wallets"])
    if n < C["min_wallets_bet"]:
        extra = (" (%d wallets agree, but several trade alike)" % p["wallets"]) if n < p["wallets"] else ""
        why.append("only %d independent top wallet%s agree (need %d)%s" % (n, "" if n == 1 else "s", C["min_wallets_bet"], extra))
    if price < C["min_price"]:
        why.append("you would pay %.0fc, a longshot" % (price * 100))
    if price > C["max_price"]:
        why.append("you would pay %.0fc, leaving little upside" % (price * 100))
    if p.get("limit") is not None:
        if not p.get("fillable", True):
            why.append("the best buy order is already %s, above the %s limit ceiling (their entry + %.0fc): the price has moved, do not chase" % (
                cents(p["book"]["bid"]), cents(p["limit_ceiling"]), C["max_drift"] * 100))
    elif drift > C["max_drift"]:
        why.append("the price is %.0fc above their average entry" % (drift * 100))
    if p["opp_ratio"] > C["max_opposition_ratio"]:
        why.append("top wallets on the other side hold %.0f%% as much" % (p["opp_ratio"] * 100))
    if C["verify_required"]:
        if p.get("fair") is None:
            why.append("not verified against sportsbooks: %s" % (p.get("verify_note") or "not checked"))
        elif p["book_edge"] < C["min_book_edge"]:
            why.append("sportsbooks price this at %.0f%%, only %+.1fc vs your %s limit (need +%.0fc)" % (
                p["fair"] * 100, p["book_edge"] * 100, cents(entry_price(p)), C["min_book_edge"] * 100))
    b = p.get("book")
    if b:
        if b["exec_price"] is None:
            why.append("not enough shares for sale to fill a $%.2f order" % ref_stake())
        else:
            if b["spread"] is not None and b["spread"] > C["max_spread"]:
                why.append("wide spread (%.0fc between buy and sell)" % (b["spread"] * 100))
            if b["depth"] < C["min_depth_multiple"] * ref_stake():
                why.append("thin liquidity ($%.0f for sale near the best price)" % b["depth"])
    f = p["flow"]
    if f:
        total_prev = f["holders_now"] + f["exited"]
        if f["exited"] >= 1 and f["exited"] / float(total_prev) >= C["exit_fraction"]:
            why.append("%d of %d earlier top holders have since sold out" % (f["exited"], total_prev))
        buyers, sellers = f["new"] + f["added"], f["trimmed"] + f["exited"]
        if sellers - buyers >= 2:
            why.append("net selling by top wallets (%d selling, %d buying)" % (sellers, buyers))
    start, _ = parse_dt(p.get("start"))
    end, _ = parse_dt(p.get("end"))
    now = datetime.now(timezone.utc)
    if start and now > start:
        why.append("event already underway")
    elif end and now > end + timedelta(hours=24):
        why.append("past its listed end date")
    if not why and score < C["cutoff_score"]:
        why.append("score %.0f is under the cutoff of %d" % (score, C["cutoff_score"]))
    p["parts"], p["score"], p["why"] = parts, score, why
    p["tier"] = "bet" if not why else "watch"


def enrich(p):
    """Add dates, category, order book and fee-adjusted price. Every step degrades gracefully."""
    info = market_info(gamma_market(p["condition_id"]))
    p["slug"] = p["slug"] or info["slug"]
    p["event_slug"] = info["event_slug"] or p["slug"]
    p["start"] = info["start"]
    p["end"] = info["end"] or p["end"]
    p["category"] = info["category"]
    p["is_sports"] = info["is_sports"]
    p["fee_rate"] = fee_rate_for(info["category"])
    for name, board in _CAT_BOARDS.items():
        if name[:5] in info["category"]:
            hits = [a for a, _ in p["holders"] if a in board]
            if hits:
                p["specialty"], p["specialists"] = name, len(hits)
                p["specialist_share"] = len(hits) / float(max(len(p["holders"]), 1))
            break
    token = p["token_id"] or info["tokens"].get(p["outcome"], "")
    time.sleep(CONFIG["pause_seconds"])
    if token:
        try:
            book = analyze_book(get_json(CLOB_API, "/book", {"token_id": token}, retries=2), ref_stake())
            p["book"] = book
            if book["exec_price"] is not None:
                ep = book["exec_price"]
                p["exec_price"] = ep
                p["all_in"] = ep + p["fee_rate"] * ep * (1 - ep)   # what crossing the spread would cost: kept as a reference
            set_limit(p)
            ref = p.get("limit") or p.get("exec_price")
            if book["min_size"] > 0 and ref:
                p["min_order_usd"] = book["min_size"] * ref
        except Exception:
            pass
        time.sleep(CONFIG["pause_seconds"])


# ---------------- Independent check: sportsbook consensus (The Odds API) ----------------
ODDS_API = "https://api.the-odds-api.com"
ODDS_SPORTS = {"nfl": "americanfootball_nfl", "nba": "basketball_nba"}
_ODDS = {"events": {}, "remaining": None, "note": "", "calls": 0}


def norm_text(s):
    return " " + re.sub(r"[^a-z0-9]+", " ", str(s or "").lower()).strip() + " "


def team_in(full, text):
    """True if a team's full name, or its last 1-3 words (the nickname: 'Trail Blazers', '49ers'), is in the normalized text."""
    w = norm_text(full).split()
    return any(len(w) >= k and (" " + " ".join(w[-k:]) + " ") in text for k in (3, 2, 1))


def league_of(p):
    slug = (p.get("event_slug") or p.get("slug") or "").lower()
    for lg in ODDS_SPORTS:
        if slug.startswith(lg + "-"):
            return lg
    return None


def parse_market(p):
    """(kind, line, line_team) for the market shapes Polymarket uses for games, or None.
    'A vs. B: O/U 232.5' -> totals; 'Spread: A (-7.5)' -> spreads (the line belongs to A); 'A vs. B' -> moneyline."""
    title = p.get("title") or ""
    m = re.search(r"o/u\s*(\d+(?:\.\d+)?)", title, re.I)
    if m and str(p.get("outcome") or "").lower() in ("over", "under"):
        return "totals", float(m.group(1)), None
    m = re.match(r"\s*spread:\s*(.+?)\s*\(([+-]?\d+(?:\.\d+)?)\)\s*$", title, re.I)
    if m:
        return "spreads", float(m.group(2)), m.group(1)
    if re.search(r"\bvs\.?\s", title, re.I) and "o/u" not in title.lower():
        return "h2h", None, None
    return None


def odds_get(league, key):
    """One Odds API call. Returns (events, credits remaining or None). Never puts the key in an error message."""
    q = urllib.parse.urlencode({"apiKey": key, "regions": CONFIG["odds_regions"], "markets": CONFIG["odds_markets"],
                                "oddsFormat": "decimal", "dateFormat": "iso"})
    url = "%s/v4/sports/%s/odds/?%s" % (ODDS_API, ODDS_SPORTS[league], q)
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "polytracker/2.4"})
        with urllib.request.urlopen(req, timeout=30) as r:
            data = json.loads(r.read().decode())
            rem = r.headers.get("x-requests-remaining")
    except urllib.error.HTTPError as e:
        raise RuntimeError("HTTP %d" % e.code)
    except Exception as e:
        raise RuntimeError(e.__class__.__name__)
    return (data if isinstance(data, list) else []), (int(float(rem)) if rem not in (None, "") else None)


def odds_events(league):
    """Upcoming games with bookmaker odds for a league, fetched at most once per run. None when unavailable."""
    if league in _ODDS["events"]:
        return _ODDS["events"][league]
    data = None
    key = os.environ.get("ODDS_API_KEY", "").strip()
    if not key:
        _ODDS["note"] = "no ODDS_API_KEY set"
    elif _ODDS["remaining"] is not None and _ODDS["remaining"] < CONFIG["odds_min_remaining"]:
        _ODDS["note"] = "Odds API credits nearly used up (%d left)" % _ODDS["remaining"]
    else:
        try:
            data, rem = odds_get(league, key)
            _ODDS["calls"] += 1
            if rem is not None:
                _ODDS["remaining"] = rem
        except Exception as e:
            _ODDS["note"] = "Odds API request failed (%s)" % e
    _ODDS["events"][league] = data
    return data


def slug_date(p):
    m = re.search(r"(\d{4}-\d{2}-\d{2})$", (p.get("event_slug") or p.get("slug") or ""))
    if m:
        try:
            return datetime.strptime(m.group(1), "%Y-%m-%d").replace(hour=18, tzinfo=timezone.utc)
        except ValueError:
            pass
    return None


def book_probs(ev, kind, line, line_is_mine, outcome):
    """Each bookmaker's vig-free probability for this exact outcome and line (proportional devig), one per bookmaker."""
    out_text = norm_text(outcome)
    target = None
    if kind == "spreads":
        target = line if line_is_mine else -line
    probs = []
    for bk in ev.get("bookmakers") or []:
        for m in bk.get("markets") or []:
            if m.get("key") != kind:
                continue
            outs = [o for o in (m.get("outcomes") or []) if num(o.get("price")) > 1.0]
            if len(outs) < 2:
                continue
            if kind == "totals" and any(abs(num(o.get("point"), -999) - line) > 1e-6 for o in outs):
                continue
            imp = [1.0 / num(o["price"]) for o in outs]
            tot = sum(imp)
            hits = []
            for o, i in zip(outs, imp):
                if kind == "totals":
                    ok = str(o.get("name") or "").lower() == str(outcome).lower()
                elif kind == "spreads":
                    ok = team_in(o.get("name"), out_text) and abs(num(o.get("point"), -999) - target) < 1e-6
                else:
                    ok = team_in(o.get("name"), out_text)
                if ok:
                    hits.append(i / tot)
            if len(hits) == 1:
                probs.append(hits[0])
    return probs


def verify_pick(p):
    """Compare our limit price with the sportsbook consensus. Sets fair, books, book_edge (fair minus limit) and a note."""
    p["fair"] = p["book_edge"] = p["books"] = None
    p["verify_note"] = "no sportsbook check for this market"
    lg = league_of(p)
    if not lg:
        return
    mk = parse_market(p)
    if not mk:
        p["verify_note"] = "no sportsbook check for this type of market"
        return
    events = odds_events(lg)
    if events is None:
        p["verify_note"] = "sportsbook data unavailable (%s)" % (_ODDS["note"] or "no data")
        return
    kind, line, line_team = mk
    text = norm_text("%s %s" % (p["title"], "" if kind == "totals" else p["outcome"]))
    line_is_mine = bool(line_team) and norm_text(line_team) == norm_text(p["outcome"])
    need = 1 if (kind == "spreads" and line_is_mine) else 2
    start, _ = parse_dt(p.get("start"))
    ref, window = (start, 6.0) if start else (slug_date(p), 36.0)
    cands = []
    for ev in events:
        teams = [t for t in (ev.get("home_team"), ev.get("away_team")) if t]
        if sum(1 for t in teams if team_in(t, text)) < need:
            continue
        when, _ = parse_dt(ev.get("commence_time"))
        gap = abs((when - ref).total_seconds()) / 3600.0 if (when and ref) else None
        if gap is not None and gap > window:
            continue
        cands.append((gap if gap is not None else 0.0, ev))
    if not cands or (ref is None and len(cands) > 1):
        p["verify_note"] = "no matching %s game found at the sportsbooks" % lg.upper()
        return
    ev = min(cands, key=lambda x: x[0])[1]
    probs = book_probs(ev, kind, line, line_is_mine, p["outcome"])
    if len(probs) < CONFIG["odds_min_books"]:
        p["verify_note"] = "only %d sportsbook%s quote this exact line" % (len(probs), "" if len(probs) == 1 else "s")
        return
    p["fair"] = sum(probs) / len(probs)
    p["books"] = len(probs)
    p["book_edge"] = p["fair"] - entry_price(p)
    p["verify_note"] = ""


def verify_line(p):
    if p.get("fair") is None:
        return "Sportsbook check: " + (p.get("verify_note") or "not checked")
    return "Sportsbook check: %d books price this at %.0f%% (vig removed); your limit is %s, an edge of %+.1f¢" % (
        p["books"], p["fair"] * 100, cents(entry_price(p)), p["book_edge"] * 100)


def apply_correlation(picks):
    """Only the best pick per event stays above the line: the others win or lose together with it."""
    picks.sort(key=lambda p: (p["tier"] != "bet", -p["score"]))
    seen = {}
    for p in picks:
        key = p.get("event_slug")
        if p["tier"] != "bet" or not key:
            continue
        if key in seen:
            p["tier"] = "watch"
            p["why"].append("same event as a higher-ranked pick (%s), so the bets move together" % seen[key][:45])
        else:
            seen[key] = p["title"]
    picks.sort(key=lambda p: (p["tier"] != "bet", -p["score"]))


def assign_stakes(picks):
    """Stake = % of bankroll scaled by score. Stop handing out stakes once the total exposure cap is hit."""
    c = CONFIG
    bankroll = max(c["bankroll"], 0.01)
    cap = bankroll * c["max_total_exposure_pct"]
    used = 0.0
    for p in picks:
        if p["tier"] != "bet":
            continue
        t = clamp((p["score"] - c["cutoff_score"]) / float(max(100 - c["cutoff_score"], 1)))
        pct = c["stake_pct_min"] + (c["stake_pct_max"] - c["stake_pct_min"]) * t
        floor = math.ceil(max(c["min_stake"], p.get("min_order_usd") or 0.0) * 100 - 1e-9) / 100.0
        stake = max(floor, round(bankroll * pct, 2))
        if used + stake > cap + 1e-9:
            p["capped"] = True
            p["min_over_cap"] = floor > cap + 1e-9   # the market's minimum order alone is bigger than the limit
            continue
        used += stake
        p["stake"], p["stake_pct"] = stake, stake / bankroll
    return used, cap


# ---------------- Step 5: paper-trade log + track record ----------------
PICK_COLS = [("fair_prob", "REAL"), ("book_edge", "REAL"), ("books", "INTEGER"), ("flagged_at", "TEXT"), ("condition_id", "TEXT"), ("outcome", "TEXT"), ("title", "TEXT"),
             ("entry_price", "REAL"), ("wallets", "INTEGER"), ("score", "REAL"), ("tier", "TEXT"), ("exec_price", "REAL"),
             ("bet_at", "TEXT"), ("bet_price", "REAL"), ("last_score", "REAL"), ("slug", "TEXT"), ("end_date", "TEXT"),
             ("resolved", "INTEGER"), ("final_price", "REAL"), ("last_price", "REAL"), ("last_checked", "TEXT"),
             ("engine", "TEXT")]


def db():
    con = sqlite3.connect(DB_PATH)
    con.row_factory = sqlite3.Row
    con.execute("""CREATE TABLE IF NOT EXISTS picks (
        id INTEGER PRIMARY KEY, flagged_at TEXT, condition_id TEXT, outcome TEXT, title TEXT,
        entry_price REAL, wallets INTEGER, score REAL)""")
    have = {r[1] for r in con.execute("PRAGMA table_info(picks)")}
    for name, typ in PICK_COLS:
        if name not in have:
            con.execute("ALTER TABLE picks ADD COLUMN %s %s" % (name, typ))
    # Picks logged before versions existed were made under older, different rules.
    con.execute("UPDATE picks SET engine = 'earlier' WHERE engine IS NULL")
    # Older versions only stored the tier a pick had when first seen. Treat those 'bet' rows as bets at that time.
    con.execute("UPDATE picks SET bet_at = flagged_at, bet_price = entry_price WHERE tier = 'bet' AND bet_at IS NULL")
    con.commit()
    # Older databases allow one row per market. Rebuild so each rules version can log the same market separately.
    sql = (con.execute("SELECT sql FROM sqlite_master WHERE type = 'table' AND name = 'picks'").fetchone() or [""])[0] or ""
    if "UNIQUE" in sql.upper():
        names = [r[1] for r in con.execute("PRAGMA table_info(picks)")]
        con.execute("BEGIN")
        try:
            con.execute("ALTER TABLE picks RENAME TO picks_old")
            con.execute("CREATE TABLE picks (id INTEGER PRIMARY KEY, %s)" % ", ".join("%s %s" % c for c in PICK_COLS))
            con.execute("INSERT INTO picks (%s) SELECT %s FROM picks_old" % (", ".join(names), ", ".join(names)))
            con.execute("DROP TABLE picks_old")
            con.execute("COMMIT")
        except Exception:
            con.execute("ROLLBACK")
            raise
    con.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_pick_key ON picks(condition_id, outcome, engine)")
    con.execute("""CREATE TABLE IF NOT EXISTS snapshots (
        ts TEXT, wallet TEXT, condition_id TEXT, outcome TEXT, shares REAL, value REAL)""")
    if "title" not in {r[1] for r in con.execute("PRAGMA table_info(snapshots)")}:
        con.execute("ALTER TABLE snapshots ADD COLUMN title TEXT")
    con.execute("CREATE INDEX IF NOT EXISTS idx_snap_ts ON snapshots(ts)")
    con.execute("""CREATE TABLE IF NOT EXISTS wallet_stats (
        wallet TEXT PRIMARY KEY, ts TEXT, n INTEGER, wins INTEGER, roi REAL, win_rate REAL, implied REAL)""")
    have_ws = {r[1] for r in con.execute("PRAGMA table_info(wallet_stats)")}
    for name, typ in (("positions", "INTEGER"), ("med_cost", "REAL"), ("hi_price", "REAL"), ("two_sided", "REAL")):
        if name not in have_ws:
            con.execute("ALTER TABLE wallet_stats ADD COLUMN %s %s" % (name, typ))
    con.commit()
    return con


def log_picks(con, picks):
    now = datetime.now(timezone.utc).isoformat()
    for p in picks:
        price = entry_price(p)
        bet = p["tier"] == "bet"
        row = con.execute("SELECT id, bet_at FROM picks WHERE condition_id = ? AND outcome = ? AND engine = ?",
                          (p["condition_id"], p["outcome"], ENGINE_VERSION)).fetchone()
        if row is None:
            con.execute(
                "INSERT INTO picks(flagged_at, condition_id, outcome, title, entry_price, wallets, score, tier,"
                " exec_price, last_score, slug, end_date, bet_at, bet_price, engine, fair_prob, book_edge, books)"
                " VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (now, p["condition_id"], p["outcome"], p["title"], p["mid"], p["wallets"], p["score"], p["tier"],
                 p["all_in"], p["score"], p["slug"], p["end"], now if bet else None, price if bet else None, ENGINE_VERSION,
                 p.get("fair"), p.get("book_edge"), p.get("books")))
        else:
            if bet and not row["bet_at"]:
                con.execute("UPDATE picks SET bet_at = ?, bet_price = ?, exec_price = COALESCE(?, exec_price),"
                            " fair_prob = COALESCE(?, fair_prob), book_edge = COALESCE(?, book_edge), books = COALESCE(?, books)"
                            " WHERE id = ?", (now, price, p["all_in"], p.get("fair"), p.get("book_edge"), p.get("books"), row["id"]))
            elif p.get("fair") is not None:
                con.execute("UPDATE picks SET fair_prob = COALESCE(fair_prob, ?), book_edge = COALESCE(book_edge, ?),"
                            " books = COALESCE(books, ?) WHERE id = ?", (p["fair"], p["book_edge"], p["books"], row["id"]))
            con.execute("UPDATE picks SET tier = ?, last_score = ?, wallets = ?, slug = ?, end_date = ? WHERE id = ?",
                        (p["tier"], p["score"], p["wallets"], p["slug"], p["end"], row["id"]))
    con.commit()


def wilson(k, n, z=1.96):
    """95% range for a win rate."""
    if n == 0:
        return 0.0, 1.0
    ph = k / float(n)
    d = 1 + z * z / n
    c = ph + z * z / (2.0 * n)
    a = z * math.sqrt(ph * (1 - ph) / n + z * z / (4.0 * n * n))
    return (c - a) / d, (c + a) / d


def summarize(items):
    if not items:
        return None
    res = [i for i in items if i["resolved"]]
    opn = [i for i in items if not i["resolved"]]
    wins = sum(1 for i in res if i["cur"] > 0.5)

    def avg(xs):
        return (sum(xs) / len(xs)) if xs else None
    return {
        "n": len(items), "resolved": len(res), "wins": wins, "open": len(opn),
        "avg_ret": sum(i["cur"] / i["entry"] - 1 for i in items) / len(items),
        "settled_ret": avg([i["cur"] / i["entry"] - 1 for i in res]),
        "open_ret": avg([i["cur"] / i["entry"] - 1 for i in opn]),
        "settled_ret_taker": avg([i["cur"] / i["taker"] - 1 for i in res if i.get("taker")]),
        "open_ret_taker": avg([i["cur"] / i["taker"] - 1 for i in opn if i.get("taker")]),
        "avg_move": sum((i["cur"] - i["entry"]) * 100 for i in items) / len(items),
        "breakeven": (sum(i["entry"] for i in res) / len(res)) if res else None,
        "ci": wilson(wins, len(res)) if res else None,
    }


def track_record(con, refresh=True):
    since = (datetime.now(timezone.utc) - timedelta(days=CONFIG["tracking_days"])).isoformat()
    cols = ("id, condition_id, outcome, entry_price, exec_price, bet_at, bet_price, last_score, "
            "resolved, final_price, last_price, engine, flagged_at, book_edge")
    rows = con.execute("SELECT " + cols + " FROM picks WHERE flagged_at >= ? ORDER BY flagged_at DESC", (since,)).fetchall()
    if refresh:
        lookups, seen = 0, {}
        stamp = datetime.now(timezone.utc).isoformat()
        for r in rows:
            if r["resolved"]:
                continue
            cond = r["condition_id"]
            if cond not in seen:
                if cond not in _GAMMA_CACHE and lookups >= CONFIG["tracking_lookups"]:
                    continue
                if cond not in _GAMMA_CACHE:
                    lookups += 1
                    time.sleep(CONFIG["pause_seconds"])
                seen[cond] = gamma_market(cond, closed_fallback=True)
            price, closed = outcome_price(seen[cond], r["outcome"])
            if price is None:
                continue
            if closed:
                con.execute("UPDATE picks SET resolved = 1, final_price = ?, last_price = ?, last_checked = ? WHERE id = ?",
                            (1.0 if price > 0.5 else 0.0, price, stamp, r["id"]))
            else:
                con.execute("UPDATE picks SET last_price = ?, last_checked = ? WHERE id = ?", (price, stamp, r["id"]))
        con.commit()
        rows = con.execute("SELECT " + cols + " FROM picks WHERE flagged_at >= ? ORDER BY flagged_at DESC", (since,)).fetchall()
    bets, watch, all_items, old_bets, old_watch, started = [], [], [], [], [], []
    for r in rows:
        is_bet = bool(r["bet_at"])
        entry = r["bet_price"] if is_bet else (r["exec_price"] or r["entry_price"])
        cur = r["final_price"] if r["resolved"] else r["last_price"]
        if not entry or entry < 0.02 or cur is None:
            continue
        item = {"entry": entry, "cur": cur, "resolved": bool(r["resolved"]), "score": r["last_score"] or 0.0, "edge": r["book_edge"],
                "taker": (r["exec_price"] if (is_bet and r["engine"] == ENGINE_VERSION and r["exec_price"]
                                              and r["exec_price"] >= 0.02) else None)}
        if r["engine"] == ENGINE_VERSION:
            (bets if is_bet else watch).append(item)
            all_items.append(item)
            started.append(r["flagged_at"])
        else:
            (old_bets if is_bet else old_watch).append(item)
    buckets = []
    for lo, hi, label in [(90, 101, "90-100"), (80, 90, "80-89"), (70, 80, "70-79"), (60, 70, "60-69"), (0, 60, "Under 60")]:
        buckets.append((label, summarize([i for i in all_items if lo <= i["score"] < hi])))
    edge_items = [i for i in all_items if i.get("edge") is not None]
    edge_buckets = [(label, summarize([i for i in edge_items if lo <= i["edge"] < hi]))
                    for lo, hi, label in [(0.03, 9.0, "+3c or more"), (0.0, 0.03, "0 to +3c"), (-9.0, 0.0, "Below 0")]]
    return {"bet": summarize(bets), "watch": summarize(watch), "buckets": buckets, "total": len(all_items),
            "edge_buckets": edge_buckets,
            "engine": ENGINE_VERSION, "since": min(started)[:10] if started else None,
            "earlier": {"bet": summarize(old_bets), "watch": summarize(old_watch), "n": len(old_bets) + len(old_watch)}}


def print_track_record(tr):
    def show(prefix, s):
        if not s:
            print("%-26s no picks yet" % prefix)
            return
        line = "%-26s %3d picks (%d settled, %d open)" % (prefix, s["n"], s["resolved"], s["open"])
        if s["resolved"]:
            line += ", won %d/%d (break-even about %.0f%%), return on settled %+.1f%%" % (
                s["wins"], s["resolved"], s["breakeven"] * 100, s["settled_ret"] * 100)
        if s["open"]:
            line += ", open marked %+.1f%%" % (s["open_ret"] * 100)
        print(line)
    print("Rules version %s%s" % (tr["engine"], (" since " + tr["since"]) if tr["since"] else ""))
    show("Above the line", tr["bet"])
    show("Below the line", tr["watch"])
    if tr["earlier"]["n"]:
        print("\nEarlier rules (reference only, not used for the verdict):")
        show("Above the line", tr["earlier"]["bet"])
        show("Below the line", tr["earlier"]["watch"])
    if any(s for _, s in tr.get("edge_buckets", [])):
        print("\nBy sportsbook edge at entry (current rules):")
        for label, s in tr["edge_buckets"]:
            if s:
                print("  %-12s %3d picks (%d settled), won %d, avg return %+.1f%%" % (label, s["n"], s["resolved"], s["wins"], s["avg_ret"] * 100))
    print("\nBy score (current rules):")
    for label, s in tr["buckets"]:
        if s:
            print("  %-9s %3d picks, avg return %+.1f%%" % (label, s["n"], s["avg_ret"] * 100))


# ---------------- Step 6: report + email ----------------
REPORT_CSS = """
body{margin:0;background:#f3f4f6;color:#111827;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;line-height:1.45}
a{color:#1d4ed8;text-decoration:none}
a:hover{text-decoration:underline}
.wrap{max-width:800px;margin:0 auto;padding:28px 16px 40px}
.top{margin-bottom:18px}
.top h1{margin:0;font-size:24px;letter-spacing:-.01em}
.top .sub{color:#6b7280;font-size:13px;margin-top:4px}
.stats{width:100%;border-collapse:separate;border-spacing:10px 0;margin:0 -10px 6px}
.stat{width:25%;background:#fff;border:1px solid #e5e7eb;border-radius:10px;padding:12px 14px}
.stat .v{font-size:22px;font-weight:700}
.stat .l{font-size:11px;text-transform:uppercase;letter-spacing:.06em;color:#6b7280}
.banner{margin:12px 0;background:#eff6ff;border:1px solid #bfdbfe;color:#1e3a8a;border-radius:10px;padding:10px 14px;font-size:13px}
.sec{margin:26px 0 6px;font-size:12px;font-weight:700;letter-spacing:.09em;text-transform:uppercase}
.sec.go{color:#15803d}
.sec.stop{color:#b91c1c}
.sec.rec{color:#4338ca}
.note{color:#6b7280;font-size:13px;margin:0 0 6px}
.card{background:#fff;border:1px solid #e5e7eb;border-radius:12px;padding:16px 18px;margin:12px 0}
.card.bet{border-left:5px solid #16a34a}
.card.watch{border-left:5px solid #d1d5db}
.row1{width:100%;border-collapse:collapse}
.rank{width:30px;color:#9ca3af;font-weight:700;font-size:15px;vertical-align:top}
.ttl{font-size:16px;font-weight:600;vertical-align:top}
.sc{width:70px;text-align:right;vertical-align:top}
.pill{display:inline-block;min-width:34px;padding:3px 9px;border-radius:999px;font-weight:700;font-size:14px;text-align:center}
.pill.hi{background:#dcfce7;color:#166534}
.pill.mid{background:#fef3c7;color:#92400e}
.pill.lo{background:#f3f4f6;color:#4b5563}
.sclabel{font-size:10px;color:#9ca3af;margin-top:2px}
.facts{width:100%;border-collapse:collapse;margin:12px 0 4px}
.facts td{padding:0 12px 0 0;vertical-align:top}
.facts .l{font-size:10px;text-transform:uppercase;letter-spacing:.06em;color:#9ca3af}
.facts .v{font-size:15px;font-weight:600}
.side{display:inline-block;background:#eef2ff;color:#3730a3;border-radius:6px;padding:1px 8px;font-weight:700}
.pos{color:#15803d}.neg{color:#b91c1c}
.line2{font-size:13px;color:#4b5563;margin-top:8px}
.sig{font-size:12px;color:#6b7280;margin-top:3px}
.holders{font-size:12px;color:#6b7280;margin-top:4px}
.parts{font-size:11px;color:#9ca3af;margin-top:8px}
.stake{margin-top:12px;background:#ecfdf3;border:1px solid #bbf7d0;color:#14532d;border-radius:8px;padding:9px 12px;font-size:14px}
.capped{margin-top:12px;background:#f3f4f6;border:1px solid #e5e7eb;color:#4b5563;border-radius:8px;padding:9px 12px;font-size:13px}
.why{margin-top:12px;background:#fffbeb;border:1px solid #fde68a;color:#92400e;border-radius:8px;padding:8px 12px;font-size:13px}
.cutoff{margin:30px 0 4px;border-top:3px dashed #ef4444}
.cutlabel{display:inline-block;margin-top:-13px;margin-left:12px;background:#f3f4f6;padding:0 10px;color:#b91c1c;font-size:12px;font-weight:700;letter-spacing:.08em;text-transform:uppercase}
.tr{width:100%;border-collapse:collapse;font-size:13px;background:#fff;border:1px solid #e5e7eb;border-radius:10px;margin:8px 0}
.tr th{text-align:left;font-size:10px;text-transform:uppercase;letter-spacing:.06em;color:#9ca3af;padding:8px 10px;border-bottom:1px solid #e5e7eb}
.tr td{padding:8px 10px;border-bottom:1px solid #f3f4f6}
.verdict{background:#eef2ff;border:1px solid #c7d2fe;color:#312e81;border-radius:10px;padding:10px 14px;font-size:13px;margin:8px 0}
.foot{margin-top:28px;font-size:12px;color:#9ca3af}
.empty{background:#fff;border:1px dashed #d1d5db;border-radius:12px;padding:18px;color:#4b5563;margin:12px 0}
@media (prefers-color-scheme:dark){
 body{background:#0f1218;color:#e5e7eb}
 a{color:#93c5fd}
 .stat,.card,.empty,.tr{background:#171b23;border-color:#262c38}
 .card.watch{border-left-color:#3b4252}
 .top .sub,.stat .l,.note,.holders,.line2,.sig{color:#9aa3b2}
 .pill.hi{background:#12361f;color:#86efac}.pill.mid{background:#3a2e0c;color:#fcd34d}.pill.lo{background:#232936;color:#b4bcc9}
 .side{background:#232a52;color:#c7d2fe}
 .stake{background:#102a1a;border-color:#1c4a2c;color:#bbf7d0}
 .capped{background:#1f242e;border-color:#2b3240;color:#aab3c2}
 .why{background:#33290c;border-color:#5a4713;color:#fcd34d}
 .banner{background:#12233f;border-color:#1e3a6b;color:#bfdbfe}
 .verdict{background:#1b1f3d;border-color:#2e3470;color:#c7d2fe}
 .tr th{border-color:#262c38}.tr td{border-color:#20262f}
 .cutlabel{background:#0f1218;color:#f87171}
 .pos{color:#4ade80}.neg{color:#f87171}
}
.tabs{display:none;gap:6px;margin:14px 0 4px;flex-wrap:wrap}
.js .tabs{display:flex}
.tabbtn{background:#fff;border:1px solid #e5e7eb;border-radius:999px;padding:7px 16px;font-size:13px;font-weight:600;color:#4b5563;cursor:pointer;font-family:inherit}
.tabbtn.on{background:#111827;color:#fff;border-color:#111827}
.scroll{overflow-x:auto}
.chips{display:none;gap:6px;margin:12px 0 0;flex-wrap:wrap}
.js .chips{display:flex}
.chip{background:#fff;border:1px solid #e5e7eb;border-radius:8px;padding:5px 12px;font-size:12px;font-weight:600;color:#4b5563;cursor:pointer;font-family:inherit}
.chip.on{background:#eef2ff;border-color:#a5b4fc;color:#3730a3}
.paneh{margin:22px 0 4px;font-size:12px;font-weight:700;letter-spacing:.09em;text-transform:uppercase;color:#4338ca}
@media (prefers-color-scheme:dark){.chip{background:#171b23;border-color:#262c38;color:#aab3c2}.chip.on{background:#232a52;border-color:#4b55a8;color:#c7d2fe}}
@media (prefers-color-scheme:dark){.tabbtn{background:#171b23;border-color:#262c38;color:#aab3c2}.tabbtn.on{background:#e5e7eb;color:#111827;border-color:#e5e7eb}.paneh{color:#a5b4fc}}
@media (max-width:520px){.facts td{display:inline-block;width:46%;padding-bottom:8px}.stats{border-spacing:6px 0}}
"""


SPORT_WORDS = ("sport", "nba", "nfl", "nhl", "mlb", "wnba", "ncaa", "soccer", "football", "basketball", "baseball",
               "hockey", "tennis", "golf", "ufc", "mma", "boxing", "formula", "f1", "premier league", "champions league", "olympic")


LEAGUE_PREFIXES = ("nba-", "nfl-", "nhl-", "mlb-", "wnba-", "cbb-", "cfb-", "ncaa", "epl-", "mls-", "ucl-", "uel-",
                   "atp-", "wta-", "ufc-", "lal-", "bun-", "sea-", "fl1-", "cs2-", "lol-", "dota")


def pick_group(p):
    t = (p.get("category") or "").lower()
    slug = (p.get("event_slug") or p.get("slug") or "").lower()
    title = (p.get("title") or "").lower()
    if (p.get("is_sports") or any(w in t for w in SPORT_WORDS) or slug.startswith(LEAGUE_PREFIXES)
            or "o/u " in title or "spread:" in title or "moneyline" in title):
        return "sports"
    if "politic" in t or "election" in t:
        return "politics"
    if "crypto" in t or "bitcoin" in t or "ethereum" in t:
        return "crypto"
    return "other"


def money(x):
    return "$%s" % format(x, ",.0f")


def pill_class(score, tier):
    """Green only for picks above the line, so a high score below the line never looks like a go."""
    if tier != "bet":
        return "lo"
    return "hi" if score >= CONFIG["cutoff_score"] + 10 else "mid"


def parse_dt(text):
    """Parse the date strings Polymarket returns. Returns (aware datetime in UTC, date_only) or (None, False)."""
    if not text:
        return None, False
    t = str(text).strip().replace("Z", "+00:00").replace(" ", "T", 1)
    if re.search(r"[+-]\d\d$", t):
        t += ":00"
    try:
        dt = datetime.fromisoformat(t)
    except ValueError:
        return None, False
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    dt = dt.astimezone(timezone.utc)
    date_only = len(str(text).strip()) <= 10 or (dt.hour, dt.minute, dt.second) == (0, 0, 0)
    return dt, date_only


def when_info(p):
    """(label, date text, relative text) for a pick, e.g. ('Starts', 'Thu Nov 12, 7:30 PM', 'in 5h')."""
    start, s_only = parse_dt(p.get("start"))
    end, e_only = parse_dt(p.get("end"))
    label, dt, date_only = ("Starts", start, s_only) if start else ("Ends", end, e_only)
    if not dt:
        return None
    try:
        from zoneinfo import ZoneInfo
        local = dt.astimezone(ZoneInfo(CONFIG["timezone"]))
    except Exception:
        local = dt.astimezone()
    if date_only:
        shown = dt.strftime("%a %b %-d")   # date-only values: keep the stated date, no time zone shift
        days = (dt.date() - now_local().date()).days
    else:
        shown = local.strftime("%a %b %-d, %-I:%M %p")
        days = (local.date() - now_local().date()).days
    if date_only or abs(days) >= 1:
        rel = "today" if days == 0 else ("in %dd" % days if days > 0 else "%dd ago" % -days)
    else:
        hrs = (dt - datetime.now(timezone.utc)).total_seconds() / 3600
        rel = ("in %.0fh" % hrs) if hrs > 0 else ("already started" if label == "Starts" else "past due")
    return label, shown, rel


def cents(x):
    v = x * 100
    return "%.0f¢" % v if abs(v - round(v)) < 0.05 else "%.1f¢" % v


def conviction_text(p):
    x = p.get("conviction")
    if x is None:
        return "Their usual bet size is not known yet, so conviction is not scored."
    return "Bet size averages %.1fx these wallets' own median bet." % x


def flow_line(p, ctx):
    f = p["flow"]
    if f is None:
        return "Buying trend: building history (needs a snapshot from at least %d hours earlier)" % CONFIG["snapshot_min_age_hours"]
    bits = []
    for key, word in (("new", "new"), ("added", "added"), ("trimmed", "trimmed"), ("exited", "sold out")):
        if f[key]:
            bits.append("%d %s" % (f[key], word))
    net = (f["new"] + f["added"]) - (f["trimmed"] + f["exited"])
    tone = "net buying" if net > 0 else ("net selling" if net < 0 else "no net change")
    return "Since the last snapshot: %s (%s)" % (", ".join(bits) if bits else "no changes", tone)


def exec_line(p):
    b = p.get("book")
    if not b:
        return "No order-book data: price shown is the midpoint, so the real price may be a little higher"
    if b["exec_price"] is None:
        return "Order book: not enough shares for sale to fill a $%.2f order" % ref_stake()
    sp = "n/a" if b["spread"] is None else "%.0f¢" % (b["spread"] * 100)
    if p.get("limit") is not None:
        extra = (" Buying at the ask instead would cost %s all-in, %.1f¢ more." % (cents(p["all_in"]), (p["all_in"] - p["limit"]) * 100)
                 if p.get("all_in") else "")
        return ("Order book: best buy %s, best sell %s, spread %s. Rest a limit buy at %s, never above %s (no taker fee).%s "
                "If it does not fill near their entry, skip it." % (
                    cents(b["bid"]), cents(b["ask"]) if b["ask"] is not None else "n/a", sp, cents(p["limit"]),
                    cents(p["limit_ceiling"]), extra))
    fee = (p["all_in"] - p["exec_price"]) * 100
    return "Order book: you would pay %s per share, about %.1f¢ more with the taker fee; spread %s; %s for sale within 3¢" % (
        cents(p["exec_price"]), fee, sp, money(b["depth"]))


def card(i, p, wallets):
    link = ("https://polymarket.com/event/" + escape(p["slug"])) if p["slug"] else None
    title = escape(p["title"])
    title_html = "<a href='%s'>%s</a>" % (link, title) if link else title
    holders = ", ".join("%s %s" % (escape(str(wallets.get(a, {}).get("name", a[:8]))), money(v)) for a, v in p["holders"][:4])
    wi = when_info(p)
    when_td = ("<td><div class='l'>%s</div><div class='v'>%s</div><div class='holders' style='margin:0'>%s</div></td>"
               % (wi[0], escape(wi[1]), escape(wi[2]))) if wi else ""
    price = entry_price(p)
    if p.get("limit") is not None:
        pay_label, pay_sub = "Limit buy at", "never above %s; resting order, no taker fee" % cents(p["limit_ceiling"])
    else:
        pay_label = "You would pay"
        pay_sub = ("with fee, from order book" if p.get("all_in")
                   else ("midpoint; order book too thin to fill" if p.get("book") else "midpoint, no order book"))
    drift_cls = "neg" if p["drift"] > CONFIG["max_drift"] else ("pos" if p["drift"] <= 0.02 else "")
    parts = " · ".join("%s %.0f/%d" % (label, p["parts"][k], CONFIG["weights"][k]) for k, label in WEIGHT_LABELS)
    indep_note = (" (only %d independent)" % p["eff_wallets"]) if p.get("eff_wallets", p["wallets"]) < p["wallets"] else ""
    spec_line = ("<div class='sig'>%d of %d agreeing wallets also rank in the top %d this month for %s</div>" % (
        p["specialists"], len(p["holders"]), CONFIG["category_board_size"], escape(p["specialty"]))) if p.get("specialists") else ""
    if p["tier"] == "bet" and p["stake"]:
        note = ""
        if p["stake_pct"] > CONFIG["stake_pct_max"] + 1e-9:
            note = " <small>(the $%.2f minimum order is more than your %.0f%% per-bet limit)</small>" % (
                max(CONFIG["min_stake"], p.get("min_order_usd") or 0.0), CONFIG["stake_pct_max"] * 100)
        extra = ("<div class='stake'><b>Suggested stake: $%.2f</b> (%.1f%% of your $%s bankroll)%s</div>"
                 % (p["stake"], p["stake_pct"] * 100, format(CONFIG["bankroll"], ",.2f"), note))
    elif p["tier"] == "bet":
        if p.get("min_over_cap"):
            extra = ("<div class='capped'>Passes every rule, but this market's minimum order ($%.2f) is more than your total exposure limit "
                     "(%.0f%% of a $%s bankroll). Treat it as paper-only, or raise the bankroll or the limit.</div>" % (
                         max(CONFIG["min_stake"], p.get("min_order_usd") or 0.0), CONFIG["max_total_exposure_pct"] * 100,
                         format(CONFIG["bankroll"], ",.0f")))
        else:
            extra = "<div class='capped'>Passes every rule, but higher-ranked picks already use the suggested exposure limit. Skip it for now.</div>"
    else:
        extra = "<div class='why'><b>Below the line:</b> %s</div>" % escape("; ".join(p["why"]))
    return (
        "<div class='card %s' data-g='%s'>" % (p["tier"], pick_group(p)) +
        "<table class='row1'><tr><td class='rank'>%d</td><td class='ttl'>%s</td>" % (i, title_html) +
        "<td class='sc'><span class='pill %s'>%.0f</span><div class='sclabel'>of 100</div></td></tr></table>" % (
            pill_class(p["score"], p["tier"]), p["score"]) +
        "<table class='facts'><tr>" +
        "<td><div class='l'>Side</div><div class='v'><span class='side'>%s</span></div></td>" % escape(p["outcome"]) +
        "<td><div class='l'>%s</div><div class='v'>%s</div><div class='holders' style='margin:0'>%s</div></td>" % (
            pay_label, cents(price), pay_sub) +
        "<td><div class='l'>Their avg entry</div><div class='v'>%s</div></td>" % cents(p["avg_entry"]) +
        "<td><div class='l'>Drift</div><div class='v %s'>%+.0f¢</div></td>" % (drift_cls, p["drift"] * 100) +
        when_td + "</tr></table>" +
        "<div class='line2'><b>%d</b> top wallets agree%s with %s; %s on the other side. %s</div>" % (
            p["wallets"], indep_note, money(p["agree_money"]), money(p["oppose_money"]), conviction_text(p)) +
        "<div class='sig'>%s</div><div class='sig'>%s</div><div class='sig'>%s</div>" % (
            escape(flow_line(p, None)), escape(exec_line(p)), escape(verify_line(p))) +
        spec_line +
        "<div class='holders'>Biggest: %s</div>" % holders +
        "<div class='parts'>Score parts: %s</div>" % parts +
        extra + "</div>")


def pct_text(x):
    return "%+.1f%%" % (x * 100)


def track_row(label, s):
    if not s:
        return "<tr><td><b>%s</b></td><td colspan='6'>No picks yet</td></tr>" % label
    wr, be = "-", "-"
    if s["resolved"]:
        lo, hi = s["ci"]
        wr = "%d of %d (%.0f%%, range %.0f-%.0f%%)" % (s["wins"], s["resolved"], 100.0 * s["wins"] / s["resolved"], lo * 100, hi * 100)
        be = "%.0f%%" % (s["breakeven"] * 100)
    if s["settled_ret"] is None:
        settled = "-"
    else:
        settled = "<span class='%s'>%s</span>" % ("pos" if s["settled_ret"] > 0 else "neg", pct_text(s["settled_ret"]))
        if s.get("settled_ret_taker") is not None:
            settled += "<br><small>crossing the spread: %s</small>" % pct_text(s["settled_ret_taker"])
    if s["open_ret"] is None:
        opened = "-"
    else:
        opened = "%d: <span class='%s'>%s</span>" % (s["open"], "pos" if s["open_ret"] > 0 else "neg", pct_text(s["open_ret"]))
        if s.get("open_ret_taker") is not None:
            opened += "<br><small>crossing the spread: %s</small>" % pct_text(s["open_ret_taker"])
    return ("<tr><td><b>%s</b></td><td>%d</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%+.1f¢</td></tr>"
            % (label, s["n"], wr, be, settled, opened, s["avg_move"]))


TRACK_HEAD = ("<div class='scroll'><table class='tr'><tr><th>Group</th><th>Picks</th><th>Settled wins</th>"
              "<th>Win rate needed to break even</th><th>Return on settled picks</th><th>Open picks, marked to today</th>"
              "<th>Avg price move</th></tr>")


def track_html(tr):
    if not tr:
        return "<div class='empty'>No results yet.</div>"
    out = []
    if not tr["total"]:
        out.append("<div class='empty'>No picks yet under the current rules (version %s). They will appear after the next run.</div>"
                   % escape(tr.get("engine", "")))
    else:
        out.append("<p class='note'>Counting only picks made under rules version %s, since %s. Return is per $1 staked at the price "
                   "you would have paid; settled picks have a final result, open picks are marked at today's price and can reverse. "
                   "The main figure assumes your limit order filled at the limit price. Real limit orders miss some trades, often the ones "
                   "that ran away, so the truth sits between it and the smaller &quot;crossing the spread&quot; figure (ask price plus taker fee).</p>"
                   % (escape(tr["engine"]), escape(tr["since"] or "")))
        out.append(TRACK_HEAD + track_row("Above the line", tr["bet"]) + track_row("Below the line", tr["watch"]) + "</table></div>")
        out.append("<div class='scroll'><table class='tr'><tr><th>Score</th><th>Picks</th><th>Avg return (settled and open)</th><th>Avg price move</th></tr>")
        for label, s in tr["buckets"]:
            if s:
                out.append("<tr><td>%s</td><td>%d</td><td class='%s'>%s</td><td>%+.1f¢</td></tr>" % (
                    label, s["n"], "pos" if s["avg_ret"] > 0 else "neg", pct_text(s["avg_ret"]), s["avg_move"]))
        out.append("</table></div>")
        if any(s for _, s in tr.get("edge_buckets", [])):
            out.append("<p class='note'>The independent test: do picks that sportsbooks say are underpriced do better than the rest?</p>"
                       "<div class='scroll'><table class='tr'><tr><th>Sportsbook edge at entry</th><th>Picks</th><th>Settled wins</th>"
                       "<th>Avg return (settled and open)</th></tr>")
            for label, s in tr["edge_buckets"]:
                if s:
                    out.append("<tr><td>%s</td><td>%d</td><td>%d of %d</td><td class='%s'>%s</td></tr>" % (
                        label, s["n"], s["wins"], s["resolved"], "pos" if s["avg_ret"] > 0 else "neg", pct_text(s["avg_ret"])))
            out.append("</table></div>")
        b = tr["bet"]
        need = CONFIG["min_resolved_for_verdict"]
        if not b or b["resolved"] < need:
            have = b["resolved"] if b else 0
            out.append("<div class='verdict'><b>Too early to judge.</b> %d of the %d settled above-the-line picks needed under the "
                       "current rules before this means anything. Keep paper-trading.</div>" % (have, need))
        else:
            edge = b["wins"] / float(b["resolved"]) - b["breakeven"]
            out.append("<div class='verdict'>Above-the-line picks under the current rules have won %.0f%% against a break-even rate of "
                       "%.0f%% (%+.0f points) and returned %s on settled picks. Picks in the same event move together, so treat this "
                       "as less certain than it looks.</div>" % (100.0 * b["wins"] / b["resolved"], b["breakeven"] * 100,
                                                                 edge * 100, pct_text(b["settled_ret"])))
    e = tr.get("earlier")
    if e and e["n"]:
        out.append("<div class='sec rec'>Earlier rules (reference only)</div>"
                   "<p class='note'>Picks made before the current rules, when the definition of &quot;above the line&quot; was different. "
                   "They are not used for the verdict.</p>")
        out.append(TRACK_HEAD + track_row("Above the line", e["bet"]) + track_row("Below the line", e["watch"]) + "</table></div>")
    return "\n".join(out)


def site_url():
    u = os.environ.get("SITE_URL", "")
    repo = os.environ.get("GITHUB_REPOSITORY", "")
    if not u and "/" in repo:
        owner, name = repo.split("/", 1)
        u = "https://%s.github.io/%s/" % (owner.lower(), name)
    return u


def wallets_html(rows):
    if not rows:
        return "<div class='empty'>No wallet data yet.</div>"
    out = ["<p class='note'>Quality blends leaderboard standing (40%) with settled-bet skill (60%) when Polymarket provides that history: "
           "return on money put in, and win rate compared with the odds the wallet paid. Small samples are pulled toward average, and wallets with no settled history count as unproven. "
           "This is a heuristic, not a proven predictor.</p>",
           "<div class='scroll'><table class='tr'><tr><th>Wallet</th><th>Boards</th><th>Best rank</th><th>Profit</th>"
           "<th>Settled bets</th><th>Return on money in</th><th>Win rate vs odds paid</th><th>Quality</th><th>Open now</th></tr>"]
    for r in rows:
        st = r["stats"]
        if st and st["n"]:
            n, roi, cls = str(st["n"]), pct_text(st["roi"]), ("pos" if st["roi"] > 0 else "neg")
            wr = "%.0f%% vs %.0f%%" % (st["win_rate"] * 100, st["implied"] * 100)
        else:
            n, roi, cls, wr = "-", "-", "", "-"
        out.append("<tr><td><b>%s</b></td><td>%d/%d</td><td>%s</td><td>%s</td><td>%s</td><td class='%s'>%s</td><td>%s</td><td>%.0f</td><td>%s</td></tr>" % (
            escape(str(r["name"])[:28]), r["windows"], len(CONFIG["windows"]), ("#%d" % r["best_rank"]) if r["best_rank"] else "-",
            money(r["pnl"]), n, cls, roi, wr, r["quality"] * 100, money(r["open"])))
    out.append("</table></div>")
    return "\n".join(out)


def activity_html(ctx):
    ts = ctx.get("baseline_ts")
    if not ts:
        return ("<div class='empty'>Building history. Wallet activity appears after a run that is at least %d hours after an earlier one.</div>"
                % CONFIG["snapshot_min_age_hours"])
    head = ("<p class='note'>What the followed wallets did since %s UTC: new positions, additions, reductions, and positions that "
            "disappeared (sold, or the market settled). Biggest dollar moves first.</p>" % escape(ts[:16].replace("T", " ")))
    ev = ctx.get("activity") or []
    if not ev:
        return head + "<div class='empty'>No notable moves.</div>"
    label = {"new": "Opened", "added": "Added", "trimmed": "Reduced", "gone": "Closed out"}
    out = [head, "<div class='scroll'><table class='tr'><tr><th>Wallet</th><th>Move</th><th>Market</th><th>Side</th><th>Change</th><th>Now</th></tr>"]
    for e in ev:
        cls = "pos" if e["delta"] > 0 else "neg"
        out.append("<tr><td><b>%s</b></td><td>%s</td><td>%s</td><td>%s</td><td class='%s'>%s%s</td><td>%s</td></tr>" % (
            escape(str(e["name"])[:24]), label[e["kind"]], escape(e["title"][:60]), escape(str(e["outcome"])[:20]), cls,
            "+" if e["delta"] > 0 else "-", money(abs(e["delta"])), money(e["now"]) if e["now"] else "-"))
    out.append("</table></div>")
    return "\n".join(out)


def picks_section(picks, wallets, ctx, include_below=True):
    above = [p for p in picks if p["tier"] == "bet"]
    below = [p for p in picks if p["tier"] != "bet"]
    parts = []
    if above:
        bk = max(CONFIG["bankroll"], 0.01)
        floor = max([CONFIG["min_stake"]] + [p.get("min_order_usd") or 0.0 for p in above])
        if floor / bk > CONFIG["stake_pct_max"] + 1e-9:
            parts.append("<div class='banner'>At a $%s bankroll the $%.2f minimum order is %.1f%% of your bankroll, above your %.0f%% per-bet limit. "
                         "That is why stakes show at the minimum. Suggested stakes add up to at most $%.2f (%.0f%% of bankroll): "
                         "keep everything you have open under that.</div>" % (
                             format(bk, ",.0f"), floor, 100 * floor / bk, CONFIG["stake_pct_max"] * 100,
                             ctx.get("exposure_cap", 0), CONFIG["max_total_exposure_pct"] * 100))
    if include_below:
        counts = defaultdict(int)
        for p in picks:
            counts[pick_group(p)] += 1
        chips = ["<button class='chip' data-f='all'>All (%d)</button>" % len(picks)]
        for key, label in (("sports", "Sports"), ("politics", "Politics"), ("crypto", "Crypto"), ("other", "Other")):
            if counts[key]:
                chips.append("<button class='chip' data-f='%s'>%s (%d)</button>" % (key, label, counts[key]))
        parts.append("<div class='chips'>%s</div>" % "".join(chips))
    parts.append("<div class='sec go'>Above the line</div>"
                 "<p class='note'>Passes every safety filter: enough independent top wallets agree, the price you would actually pay "
                 "has not run away from their entries, liquidity is adequate, they are not selling, and it is not the same event as a better pick.</p>")
    if not above:
        parts.append("<div class='empty'><b>Nothing meets every rule today.</b> Sitting out is a valid trade.</div>")
    for i, p in enumerate(above, 1):
        parts.append(card(i, p, wallets))
    if include_below:
        parts.append("<div class='cutoff'><span class='cutlabel'>Cutoff line</span></div>"
                     "<div class='sec stop'>Below the line</div>"
                     "<p class='note'>Watch only. The odds are less in your favor; the reasons are shown on each. "
                     "These are logged too, so the results can show whether the line works.</p>")
        for i, p in enumerate(below, len(above) + 1):
            parts.append(card(i, p, wallets))
    return parts


def page_head(picks, wallets, ctx):
    above = [p for p in picks if p["tier"] == "bet"]
    below = [p for p in picks if p["tier"] != "bet"]
    stamp = now_local().strftime("%a %b %d, %Y at %-I:%M %p %Z")
    if ctx.get("baseline_ts"):
        hist = "Buying trends compare with the snapshot from %s." % escape(ctx["baseline_ts"][:16].replace("T", " ") + " UTC")
    else:
        hist = "Buying trends are still building history and will appear after the next run."
    return [
        "<!doctype html><html><head><meta charset='utf-8'>"
        "<meta name='viewport' content='width=device-width,initial-scale=1'>"
        "<title>Polymarket Picks</title><style>" + REPORT_CSS + "</style></head><body><div class='wrap'>",
        "<div class='top'><h1>Polymarket Picks</h1><div class='sub'>Updated %s. %s</div></div>" % (escape(stamp), hist),
        "<table class='stats'><tr>"
        "<td class='stat'><div class='v'>%d</div><div class='l'>Above the line</div></td>" % len(above) +
        "<td class='stat'><div class='v'>%d</div><div class='l'>Watching</div></td>" % len(below) +
        "<td class='stat'><div class='v'>%d</div><div class='l'>Top wallets followed</div></td>" % len(wallets) +
        "<td class='stat'><div class='v'>$%s</div><div class='l'>Bankroll</div></td>" % format(CONFIG["bankroll"], ",.0f") +
        "</tr></table>",
    ]


FOOT = ("<div class='foot'>Wallets come from the top %d by profit in at least %d of these windows: %s. Market makers (two-sided books, "
        "very high volume, near-certain bets) are dropped, and the rest are ranked by settled-bet edge, not raw profit. "
        "Score = trader quality (15) + wallet agreement (20, wallets that trade alike count once) + entry price (15) + recent buying (15) + "
        "conviction (10, bet size vs the wallet's own median bet) + low opposition (10) + execution (15). These weights are starting guesses, "
        "not proven settings. Prices are resting limit buys (no taker fee), capped a few cents above their entry; if the market has moved past "
        "that, the pick is below the line. NFL and NBA picks are also checked against sportsbook odds (vig removed) and only count as "
        "bets when the sportsbooks agree the price is low; other markets have no outside check and stay below the line. Not financial advice. Copying means worse prices than the original traders, and no ranking "
        "guarantees profit.</div>")

TAB_JS = r"""<script>
(function(){
var panes=document.querySelectorAll('.tabpane'),btns=document.querySelectorAll('.tabbtn');
if(!btns.length)return;
document.body.className+=' js';
function show(id){
 for(var i=0;i<panes.length;i++){panes[i].style.display=panes[i].id===id?'block':'none';}
 for(var j=0;j<btns.length;j++){btns[j].className='tabbtn'+(btns[j].getAttribute('data-t')===id?' on':'');}
 try{history.replaceState(null,'','#'+id);}catch(e){}
}
for(var k=0;k<btns.length;k++){(function(b){b.addEventListener('click',function(){show(b.getAttribute('data-t'));});})(btns[k]);}
var chips=document.querySelectorAll('.chip');
function filt(f){
 var cards=document.querySelectorAll('.card[data-g]');
 for(var i=0;i<cards.length;i++){cards[i].style.display=(f==='all'||cards[i].getAttribute('data-g')===f)?'':'none';}
 for(var j=0;j<chips.length;j++){chips[j].className='chip'+(chips[j].getAttribute('data-f')===f?' on':'');}
 try{localStorage.setItem('pmfilter',f);}catch(e){}
}
for(var m=0;m<chips.length;m++){(function(c){c.addEventListener('click',function(){filt(c.getAttribute('data-f'));});})(chips[m]);}
var saved='all';
try{saved=localStorage.getItem('pmfilter')||'all';}catch(e){}
if(!document.querySelector('.chip[data-f="'+saved+'"]')){saved='all';}
filt(saved);
var h=location.hash.slice(1);
show(h&&document.getElementById(h)?h:'picks');
})();
</script>"""


def render_html(picks, wallets, ctx=None):
    ctx = ctx or {}
    parts = page_head(picks, wallets, ctx)
    parts.append("<div class='tabs'><button class='tabbtn' data-t='picks'>Picks</button><button class='tabbtn' data-t='wallets'>Wallets</button>"
                 "<button class='tabbtn' data-t='activity'>Activity</button><button class='tabbtn' data-t='results'>Results</button></div>")
    parts.append("<div class='tabpane' id='picks'>")
    parts += picks_section(picks, wallets, ctx)
    parts.append("</div><div class='tabpane' id='wallets'><div class='paneh'>Wallets we follow</div>")
    parts.append(wallets_html(ctx.get("wallet_rows")))
    parts.append("</div><div class='tabpane' id='activity'><div class='paneh'>Wallet activity</div>")
    parts.append(activity_html(ctx))
    parts.append("</div><div class='tabpane' id='results'><div class='paneh'>Results</div>"
                 "<p class='note'>Every pick is saved at the price you would have paid. This is the evidence for whether any of this works. "
                 "Only picks made under the current rules (version " + ENGINE_VERSION + ") count toward the verdict.</p>")
    parts.append(track_html(ctx.get("track")))
    parts.append("</div>")
    parts.append(FOOT % (CONFIG["leaderboard_size"], CONFIG["min_windows"], ", ".join(CONFIG["windows"])))
    parts.append("</div>" + TAB_JS + "</body></html>")
    return "\n".join(parts)


def render_email(picks, wallets, ctx=None, weekly=False):
    """Short version for the inbox: the picks above the line, a pointer to the full page, and on Sundays the results."""
    ctx = ctx or {}
    parts = page_head(picks, wallets, ctx)
    parts += picks_section(picks, wallets, ctx, include_below=False)
    watching = sum(1 for p in picks if p["tier"] != "bet")
    url = site_url()
    link = ("<a href='%s'>Open the full page</a> to see the %d picks below the line, wallet activity and results." % (escape(url), watching)
            if url else "%d more picks are below the line on the full page." % watching)
    parts.append("<div class='banner'>%s</div>" % link)
    if weekly:
        parts.append("<div class='sec rec'>Weekly results</div>")
        parts.append(track_html(ctx.get("track")))
    parts.append(FOOT % (CONFIG["leaderboard_size"], CONFIG["min_windows"], ", ".join(CONFIG["windows"])))
    parts.append("</div></body></html>")
    return "\n".join(parts)


def build_wallet_rows(wallets, wallet_positions, stats):
    rows = []
    for addr, info in wallets.items():
        wp = wallet_positions.get(addr)
        if not wp:
            continue
        rows.append({"name": info["name"], "windows": len(info["windows"]), "best_rank": info.get("best_rank"),
                     "pnl": info["pnl"], "stats": stats.get(addr), "quality": wp["quality"],
                     "open": sum(num(field(p, "current_value", "currentValue", default=0)) for p in wp["positions"]
                                 if not (p.get("redeemable") or p.get("mergeable")))})
    rows.sort(key=lambda r: -r["quality"])
    return rows


def send_email(html, n_above, weekly=False):
    host = os.environ.get("SMTP_HOST", "smtp.gmail.com")
    port = int(os.environ.get("SMTP_PORT", "465"))
    user, pw, to = os.environ.get("SMTP_USER"), os.environ.get("SMTP_PASS"), os.environ.get("MAIL_TO")
    if not (user and pw and to):
        print("Email skipped: set SMTP_USER, SMTP_PASS and MAIL_TO.")
        return
    msg = MIMEText(html, "html")
    msg["Subject"] = "Polymarket %s: %d above the line%s" % (now_local().strftime("%b %d"), n_above, " + weekly results" if weekly else "")
    msg["From"], msg["To"] = user, to
    with smtplib.SMTP_SSL(host, port, context=ssl.create_default_context(), timeout=60) as s:
        s.login(user, pw)
        s.send_message(msg)
    print("Email sent to", to)


# ---------------- main ----------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--email", action="store_true", help="email the report")
    ap.add_argument("--evaluate", action="store_true", help="print the track record and exit")
    ap.add_argument("--debug", action="store_true", help="print coverage stats")
    ap.add_argument("--out", default=REPORT_PATH, help="where to write the HTML report")
    ap.add_argument("--db", default=None, help="path of the pick log (SQLite)")
    args = ap.parse_args()

    global DB_PATH
    if args.db:
        DB_PATH = args.db
    os.makedirs(os.path.dirname(os.path.abspath(DB_PATH)), exist_ok=True)
    if os.environ.get("BANKROLL"):
        CONFIG["bankroll"] = num(os.environ["BANKROLL"], CONFIG["bankroll"])

    con = db()
    if args.evaluate:
        print_track_record(track_record(con))
        return

    baseline_ts, baseline, base_meta = load_baseline(con)
    wallets = choose_wallets(con)
    print("Following %d wallets" % len(wallets))
    if _SCREEN:
        print("Screened %d wallets: %d proven, %d too little history, %d dropped%s" % (
            _SCREEN["pool"], _SCREEN["proven"], _SCREEN["unproven"], len(_SCREEN["dropped"]),
            (", %d unproven added to fill the list" % _SCREEN["filled"]) if _SCREEN["filled"] else ""))
        for name, why in _SCREEN["dropped"][:8]:
            print("  dropped %s: %s" % (str(name)[:20], why))
    stats = ensure_wallet_stats(con, wallets)
    have_stats = any(stats.get(a) for a in wallets)
    _CAT_BOARDS.update(fetch_category_boards())
    wallet_positions = {}
    for addr, info in wallets.items():
        try:
            rows, truncated = fetch_positions(addr)
            wallet_positions[addr] = {"name": info["name"], "positions": rows, "truncated": truncated,
                                      "med_cost": (stats.get(addr) or {}).get("med_cost"),
                                      "quality": wallet_quality(info, stats.get(addr), CONFIG["unknown_skill"] if have_stats else None)}
        except Exception as e:
            print("skip", addr[:10], e)
        time.sleep(CONFIG["pause_seconds"])

    candidates = build_candidates(wallet_positions, baseline)
    for p in candidates:
        assess(p)                                    # first pass with midpoint prices, to choose who to look up
    candidates.sort(key=lambda p: -p["score"])
    shortlist = candidates[: CONFIG["enrich_limit"]]
    for p in shortlist:
        enrich(p)
        verify_pick(p)                               # sportsbook consensus for NFL and NBA games
        assess(p)                                    # second pass with dates, order book, fees and the sportsbook check
    nl = sum(1 for p in shortlist if league_of(p))
    nv = sum(1 for p in shortlist if p.get("fair") is not None)
    print("Sportsbook check: %d of %d NFL/NBA picks matched%s%s" % (
        nv, nl, ("; credits left %d" % _ODDS["remaining"]) if _ODDS["remaining"] is not None else "",
        ("; " + _ODDS["note"]) if _ODDS["note"] else ""))
    apply_correlation(shortlist)
    picks = shortlist[: CONFIG["max_listed"]]
    used, cap = assign_stakes(picks)

    activity = compute_activity(wallet_positions, baseline, base_meta)
    save_snapshot(con, wallet_positions)
    log_picks(con, picks)
    tr = track_record(con)
    con.close()

    ctx = {"baseline_ts": baseline_ts, "exposure_used": used, "exposure_cap": cap, "track": tr,
           "activity": activity, "wallet_rows": build_wallet_rows(wallets, wallet_positions, stats)}
    html = render_html(picks, wallets, ctx)
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as f:
        f.write(html)
    above = [p for p in picks if p["tier"] == "bet"]
    print("%d listed, %d above the line. Report: %s" % (len(picks), len(above), args.out))
    if args.debug:
        books = sum(1 for p in picks if p["book"])
        dated = sum(1 for p in picks if p["start"] or p["end"])
        print("[debug] wallets with positions: %d, raw candidates: %d, listed: %d" % (len(wallet_positions), len(candidates), len(picks)))
        print("[debug] order books found: %d/%d, dates found: %d/%d, history baseline: %s" % (
            books, len(picks), dated, len(picks), baseline_ts or "none yet"))
        groups_seen = defaultdict(int)
        for p in picks:
            groups_seen[pick_group(p)] += 1
        print("[debug] pick groups: %s; with a category label: %d/%d, marked as sports by Polymarket: %d" % (
            ", ".join("%s %d" % kv for kv in sorted(groups_seen.items())) or "none",
            sum(1 for p in picks if p.get("category")), len(picks), sum(1 for p in picks if p.get("is_sports"))))
        with_stats = sum(1 for a in wallets if stats.get(a))
        print("[debug] wallets with settled-bet stats: %d/%d, category boards loaded: %s, wallets alike (listed picks with fewer independent than raw): %d" % (
            with_stats, len(wallets), ", ".join(sorted(_CAT_BOARDS)) or "none",
            sum(1 for p in picks if p.get("eff_wallets", p["wallets"]) < p["wallets"])))
    for p in picks:
        mark = "BET  " if p["tier"] == "bet" else "watch"
        stake = (" stake $%.2f" % p["stake"]) if p["stake"] else ""
        print("  %s %3.0f | %d wallets | %.2f | %s | %s%s" % (mark, p["score"], p["wallets"], entry_price(p), p["outcome"], p["title"][:55], stake))
    if args.email:
        weekly = now_local().weekday() == 6
        send_email(render_email(picks, wallets, ctx, weekly), len(above), weekly)


if __name__ == "__main__":
    main()
