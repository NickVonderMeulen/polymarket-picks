#!/usr/bin/env python3
"""
Polymarket consensus tracker (READ-ONLY, places no orders).

Each run:
  1. Finds top traders: wallets ranked in the top N of the leaderboard in several time windows.
  2. Reads their current open positions.
  3. Groups them by market + side and SCORES every candidate 0-100 on how strong the
     cross-check is. Everything is ranked best to worst, with a CUTOFF LINE:
        above the line = meets every rule (3+ wallets, fresh price, little opposition, ...)
        below the line = watch only, odds less in your favor (the reason is shown)
  4. Suggests a stake per pick above the line, as a % of your bankroll (grows as the bankroll grows).
  5. Logs every listed pick (both tiers) so --evaluate can show whether the line really separates
     better bets from worse ones.
  6. Writes report.html and optionally emails it.

Standard library only. Python 3.9+.

  python polytracker.py            run, write report.html
  python polytracker.py --email    also email the report
  python polytracker.py --debug    print funnel stats
  python polytracker.py --evaluate paper-trade results of past picks, by tier

Email env vars (Gmail App Password): SMTP_HOST SMTP_PORT SMTP_USER SMTP_PASS MAIL_TO
Bankroll can be set with env var BANKROLL (e.g. BANKROLL=31.50) or in CONFIG below.
"""
import argparse
import json
import os
import smtplib
import sqlite3
import ssl
import time
import urllib.parse
import urllib.request
from collections import defaultdict
from datetime import datetime, timezone
from email.mime.text import MIMEText
from html import escape

DATA_API = "https://data-api.polymarket.com"
GAMMA_API = "https://gamma-api.polymarket.com"
HERE = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.environ.get("DB_PATH", os.path.join(HERE, "picks.db"))
REPORT_PATH = os.path.join(HERE, "report.html")

# ---------------- Settings you can tune ----------------
CONFIG = {
    # Who to follow
    "windows": ["week", "month", "all"],
    "leaderboard_size": 50,        # top N per window
    "min_windows": 2,              # wallet must be top-N in this many windows
    "max_wallets": 50,
    # What counts as a candidate
    "min_position_usd": 100,       # ignore tiny positions by a wallet
    "min_wallets_listed": 2,       # list anything with at least this many wallets agreeing
    "max_listed": 25,
    # The cutoff line: a pick is "above the line" only if ALL of these hold
    "cutoff_score": 60,
    "min_wallets_bet": 3,
    "min_price": 0.10,
    "max_price": 0.85,
    "max_drift": 0.08,             # price may not be more than 8c above their average entry
    "max_opposition_ratio": 0.35,  # top-wallet money on the other side vs agreeing money
    # Staking (fractional, scales with bankroll)
    "bankroll": 25.0,
    "stake_pct_min": 0.02,         # 2% of bankroll at the cutoff...
    "stake_pct_max": 0.05,         # ...up to 5% for the strongest picks
    "min_stake": 1.0,
    "timezone": "America/New_York",
    "pause_seconds": 0.25,
}


# ---------------- HTTP helpers ----------------
def get_json(base, path, params=None, retries=3):
    url = base + path
    if params:
        url += "?" + urllib.parse.urlencode(params)
    last = None
    for attempt in range(retries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "polytracker/1.0"})
            with urllib.request.urlopen(req, timeout=30) as r:
                return json.loads(r.read().decode())
        except Exception as e:
            last = e
            time.sleep(1.5 * (attempt + 1))
    raise RuntimeError(f"GET {url} failed: {last}")


def num(x, default=0.0):
    try:
        return float(x)
    except (TypeError, ValueError):
        return default


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


# ---------------- Step 1: pick wallets ----------------
def fetch_leaderboard(window):
    resp = get_json(DATA_API, "/v2/leaderboard", {
        "category": "overall",
        "time_period": window,   # day / week / month / all
        "sort_by": "PNL",
        "limit": CONFIG["leaderboard_size"],
    })
    return rows_of(resp)


def choose_wallets():
    appearances = defaultdict(lambda: {"windows": set(), "name": "", "pnl": 0.0})
    for w in CONFIG["windows"]:
        for row in fetch_leaderboard(w):
            addr = str(field(row, "user_id", "proxy_wallet", "proxyWallet", default="")).lower()
            if not addr:
                continue
            a = appearances[addr]
            a["windows"].add(w)
            a["name"] = field(row, "user_name", "userName", default=a["name"] or addr[:8])
            a["pnl"] = max(a["pnl"], num(row.get("pnl")))
        time.sleep(CONFIG["pause_seconds"])
    kept = {k: v for k, v in appearances.items() if len(v["windows"]) >= CONFIG["min_windows"]}
    ranked = sorted(kept.items(), key=lambda kv: (-len(kv[1]["windows"]), -kv[1]["pnl"]))
    return dict(ranked[: CONFIG["max_wallets"]])


# ---------------- Step 2: positions ----------------
def fetch_positions(addr):
    resp = get_json(DATA_API, "/v2/positions", {"user": addr, "status": "OPEN", "limit": 200})
    return rows_of(resp)


def lookup_slug(condition_id):
    """Position rows may not include the event slug, so ask the Gamma API. '' on failure."""
    try:
        rows = get_json(GAMMA_API, "/markets", {"condition_ids": condition_id}, retries=1)
        if rows:
            m = rows[0]
            ev = (m.get("events") or [{}])[0]
            return ev.get("slug") or m.get("slug") or ""
    except Exception:
        pass
    return ""


# ---------------- Step 3: scoring ----------------
def score_pick(n, agree_money, opp_ratio, drift, price):
    """0-100. Wallet agreement 40, price freshness 20, low opposition 20, money 10, price zone 10."""
    s_wallets = min(n, 6) / 6 * 40
    s_money = min(agree_money / 20000.0, 1.0) * 10
    s_fresh = 20 * (1 - min(max(drift, 0) / 0.15, 1.0))
    s_opp = 20 * (1 - min(opp_ratio, 1.0))
    if price < 0.10 or price > 0.90:
        s_zone = 0
    elif price < 0.25 or price > 0.75:
        s_zone = 5
    else:
        s_zone = 10
    return s_wallets + s_money + s_fresh + s_opp + s_zone


def below_line_reasons(n, price, drift, opp_ratio, score):
    why = []
    if n < CONFIG["min_wallets_bet"]:
        why.append(f"only {n} top wallets agree (need {CONFIG['min_wallets_bet']})")
    if price < CONFIG["min_price"]:
        why.append(f"price {price:.2f} is a longshot")
    if price > CONFIG["max_price"]:
        why.append(f"price {price:.2f} leaves little upside")
    if drift > CONFIG["max_drift"]:
        why.append(f"price already {drift:+.2f} above their entry")
    if opp_ratio > CONFIG["max_opposition_ratio"]:
        why.append(f"top wallets on the other side hold {opp_ratio:.0%} as much")
    if not why and score < CONFIG["cutoff_score"]:
        why.append(f"score {score:.0f} under the cutoff of {CONFIG['cutoff_score']}")
    return why


def suggest_stake(score):
    c = CONFIG
    span = max(100 - c["cutoff_score"], 1)
    t = min(max((score - c["cutoff_score"]) / span, 0.0), 1.0)
    pct = c["stake_pct_min"] + (c["stake_pct_max"] - c["stake_pct_min"]) * t
    return max(c["min_stake"], round(c["bankroll"] * pct, 2)), pct


def build_picks(wallet_positions, debug=False):
    """wallet_positions: {addr: {"name": str, "positions": [position dicts]}}"""
    groups = defaultdict(lambda: {
        "title": "", "outcome": "", "slug": "", "wallets": {},
        "cur_price": 0.0, "cost_total": 0.0, "shares_total": 0.0,
    })
    market_side_money = defaultdict(lambda: defaultdict(float))

    for addr, info in wallet_positions.items():
        for p in info["positions"]:
            cond = field(p, "condition_id", "conditionId")
            outcome = p.get("outcome")
            if not cond or outcome is None:
                continue
            if p.get("redeemable") or p.get("mergeable"):   # already resolved
                continue
            shares = num(field(p, "current_size", "size", default=0))
            value = num(field(p, "current_value", "currentValue", default=0))
            if value < CONFIG["min_position_usd"] or shares <= 0:
                continue
            market_side_money[cond][outcome] += value
            g = groups[(cond, outcome)]
            g["title"] = p.get("title", g["title"])
            g["slug"] = field(p, "event_slug", "eventSlug", "slug", default=g["slug"])
            g["outcome"] = outcome
            g["cur_price"] = num(field(p, "cur_price", "curPrice", "current_price"), value / shares)
            avg = num(field(p, "avg_price", "avgPrice", default=0))
            g["cost_total"] += shares * avg
            g["shares_total"] += shares
            g["wallets"][addr] = g["wallets"].get(addr, 0.0) + value

    candidates = []
    for (cond, outcome), g in groups.items():
        n = len(g["wallets"])
        if n < CONFIG["min_wallets_listed"] or g["shares_total"] <= 0:
            continue
        price = g["cur_price"]
        avg_entry = g["cost_total"] / g["shares_total"]
        drift = price - avg_entry
        agree_money = sum(g["wallets"].values())
        oppose_money = sum(m for o, m in market_side_money[cond].items() if o != outcome)
        opp_ratio = oppose_money / agree_money if agree_money else 1.0
        score = score_pick(n, agree_money, opp_ratio, drift, price)
        why = below_line_reasons(n, price, drift, opp_ratio, score)
        above = not why
        pick = {
            "condition_id": cond, "title": g["title"], "outcome": outcome, "slug": g["slug"],
            "wallets": n, "agree_money": agree_money, "oppose_money": oppose_money,
            "avg_entry": avg_entry, "price": price, "drift": drift, "score": score,
            "tier": "bet" if above else "watch", "why": why,
            "holders": sorted(g["wallets"].items(), key=lambda kv: -kv[1]),
            "stake": None, "stake_pct": None,
        }
        if above:
            pick["stake"], pick["stake_pct"] = suggest_stake(score)
        candidates.append(pick)

    # Above-the-line picks first (best to worst), then below-the-line (best to worst)
    candidates.sort(key=lambda p: (p["tier"] != "bet", -p["score"]))
    if debug:
        total_pos = sum(len(i["positions"]) for i in wallet_positions.values())
        hist = defaultdict(int)
        for g in groups.values():
            hist[len(g["wallets"])] += 1
        print(f"\n[debug] wallets: {len(wallet_positions)}, raw open positions: {total_pos}, "
              f"market sides held with >= ${CONFIG['min_position_usd']}: {len(groups)}")
        print("[debug] market sides by number of agreeing wallets:",
              ", ".join(f"{k}: {v}" for k, v in sorted(hist.items(), reverse=True)))
        print(f"[debug] listed: {len(candidates)}, above the line: "
              f"{sum(1 for c in candidates if c['tier'] == 'bet')}\n")
    return candidates[: CONFIG["max_listed"]]


# ---------------- Step 4: paper-trade log ----------------
def db():
    con = sqlite3.connect(DB_PATH)
    con.execute("""CREATE TABLE IF NOT EXISTS picks (
        id INTEGER PRIMARY KEY, flagged_at TEXT, condition_id TEXT, outcome TEXT, title TEXT,
        entry_price REAL, wallets INTEGER, score REAL, UNIQUE(condition_id, outcome))""")
    try:
        con.execute("ALTER TABLE picks ADD COLUMN tier TEXT")
    except sqlite3.OperationalError:
        pass  # column already exists
    return con


def log_picks(picks):
    con = db()
    now = datetime.now(timezone.utc).isoformat()
    for p in picks:
        con.execute(
            "INSERT OR IGNORE INTO picks(flagged_at, condition_id, outcome, title, entry_price, wallets, score, tier)"
            " VALUES (?,?,?,?,?,?,?,?)",
            (now, p["condition_id"], p["outcome"], p["title"], p["price"], p["wallets"], p["score"], p["tier"]))
    con.commit()
    con.close()


def current_price(condition_id, outcome):
    """Current price of an outcome via the Gamma API. Returns (price, closed)."""
    rows = get_json(GAMMA_API, "/markets", {"condition_ids": condition_id})
    if not rows:
        return None, False
    m = rows[0]
    outcomes, prices = m.get("outcomes"), m.get("outcomePrices")
    if isinstance(outcomes, str):
        outcomes = json.loads(outcomes)
    if isinstance(prices, str):
        prices = json.loads(prices)
    if outcomes and prices and outcome in outcomes:
        return num(prices[outcomes.index(outcome)]), bool(m.get("closed"))
    return None, bool(m.get("closed"))


def evaluate():
    con = db()
    rows = con.execute(
        "SELECT flagged_at, condition_id, outcome, title, entry_price, COALESCE(tier,'bet') FROM picks").fetchall()
    con.close()
    if not rows:
        print("No logged picks yet. Run the tracker for a few days first.")
        return
    tot = defaultdict(lambda: {"cost": 0.0, "value": 0.0, "n": 0, "won": 0, "lost": 0})
    print(f"{'Flagged':<11}{'Tier':<7}{'Entry':>7}{'Now':>7}{'Return':>9}  Market")
    for flagged, cond, outcome, title, entry, tier in rows:
        now_price, closed = current_price(cond, outcome)
        time.sleep(CONFIG["pause_seconds"])
        if now_price is None or entry <= 0:
            continue
        t = tot[tier]
        t["cost"] += entry
        t["value"] += now_price
        t["n"] += 1
        if closed:
            t["won" if now_price > 0.5 else "lost"] += 1
        tag = " (resolved)" if closed else ""
        print(f"{flagged[:10]:<11}{tier:<7}{entry:>7.2f}{now_price:>7.2f}{(now_price/entry-1)*100:>8.0f}%"
              f"  {title[:50]} [{outcome}]{tag}")
    print("\nEqual-stake paper return by tier (mark-to-market):")
    for tier in ("bet", "watch"):
        t = tot.get(tier)
        if t and t["cost"]:
            print(f"  {tier:<6} {t['n']:>3} picks  {(t['value']/t['cost']-1)*100:>7.1f}%   "
                  f"resolved: {t['won']} won / {t['lost']} lost")
    print("If 'bet' is not clearly beating 'watch' (and above zero), do not use real money yet.")


# ---------------- Step 5: report + email ----------------
REPORT_CSS = """
body{margin:0;background:#f3f4f6;color:#111827;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;line-height:1.45}
a{color:#1d4ed8;text-decoration:none}
a:hover{text-decoration:underline}
.wrap{max-width:780px;margin:0 auto;padding:28px 16px 40px}
.top{margin-bottom:18px}
.top h1{margin:0;font-size:24px;letter-spacing:-.01em}
.top .sub{color:#6b7280;font-size:13px;margin-top:4px}
.stats{width:100%;border-collapse:separate;border-spacing:10px 0;margin:0 -10px 6px}
.stat{width:25%;background:#fff;border:1px solid #e5e7eb;border-radius:10px;padding:12px 14px}
.stat .v{font-size:22px;font-weight:700}
.stat .l{font-size:11px;text-transform:uppercase;letter-spacing:.06em;color:#6b7280}
.sec{margin:26px 0 6px;font-size:12px;font-weight:700;letter-spacing:.09em;text-transform:uppercase}
.sec.go{color:#15803d}
.sec.stop{color:#b91c1c}
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
.holders{font-size:12px;color:#6b7280;margin-top:4px}
.stake{margin-top:12px;background:#ecfdf3;border:1px solid #bbf7d0;color:#14532d;border-radius:8px;padding:9px 12px;font-size:14px}
.why{margin-top:12px;background:#fffbeb;border:1px solid #fde68a;color:#92400e;border-radius:8px;padding:8px 12px;font-size:13px}
.cutoff{margin:30px 0 4px;border-top:3px dashed #ef4444}
.cutlabel{display:inline-block;margin-top:-13px;margin-left:12px;background:#f3f4f6;padding:0 10px;color:#b91c1c;font-size:12px;font-weight:700;letter-spacing:.08em;text-transform:uppercase}
.foot{margin-top:28px;font-size:12px;color:#9ca3af}
.empty{background:#fff;border:1px dashed #d1d5db;border-radius:12px;padding:18px;color:#4b5563;margin:12px 0}
@media (prefers-color-scheme:dark){
 body{background:#0f1218;color:#e5e7eb}
 a{color:#93c5fd}
 .stat,.card,.empty{background:#171b23;border-color:#262c38}
 .card.watch{border-left-color:#3b4252}
 .top .sub,.stat .l,.note,.holders,.line2{color:#9aa3b2}
 .pill.hi{background:#12361f;color:#86efac}.pill.mid{background:#3a2e0c;color:#fcd34d}.pill.lo{background:#232936;color:#b4bcc9}
 .side{background:#232a52;color:#c7d2fe}
 .stake{background:#102a1a;border-color:#1c4a2c;color:#bbf7d0}
 .why{background:#33290c;border-color:#5a4713;color:#fcd34d}
 .cutlabel{background:#0f1218;color:#f87171}
 .pos{color:#4ade80}.neg{color:#f87171}
}
@media (max-width:520px){.facts td{display:inline-block;width:46%;padding-bottom:8px}.stats{border-spacing:6px 0}}
"""


def now_local():
    """Current time in the configured time zone (falls back to the machine's own)."""
    try:
        from zoneinfo import ZoneInfo
        return datetime.now(ZoneInfo(CONFIG["timezone"]))
    except Exception:
        return datetime.now().astimezone()


def money(x):
    return f"${x:,.0f}"


def pill_class(score, tier):
    """Green only for picks above the line, so a high score below the line never looks like a go."""
    if tier != "bet":
        return "lo"
    return "hi" if score >= CONFIG["cutoff_score"] + 10 else "mid"


def card(i, p, wallets):
    link = f"https://polymarket.com/event/{escape(p['slug'])}" if p["slug"] else None
    title = escape(p["title"])
    title_html = f"<a href='{link}'>{title}</a>" if link else title
    holders = ", ".join(f"{escape(str(wallets.get(a, {}).get('name', a[:8])))} {money(v)}"
                        for a, v in p["holders"][:4])
    drift_cls = "neg" if p["drift"] > CONFIG["max_drift"] else ("pos" if p["drift"] <= 0.02 else "")
    cents = lambda x: f"{x*100:.0f}¢"
    if p["tier"] == "bet":
        extra = (f"<div class='stake'><b>Suggested stake: ${p['stake']:.2f}</b> "
                 f"({p['stake_pct']:.1%} of your ${CONFIG['bankroll']:,.2f} bankroll)</div>")
    else:
        extra = f"<div class='why'><b>Below the line:</b> {escape('; '.join(p['why']))}</div>"
    return (
        f"<div class='card {p['tier']}'>"
        f"<table class='row1'><tr><td class='rank'>{i}</td><td class='ttl'>{title_html}</td>"
        f"<td class='sc'><span class='pill {pill_class(p['score'], p['tier'])}'>{p['score']:.0f}</span>"
        f"<div class='sclabel'>of 100</div></td></tr></table>"
        f"<table class='facts'><tr>"
        f"<td><div class='l'>Side</div><div class='v'><span class='side'>{escape(p['outcome'])}</span></div></td>"
        f"<td><div class='l'>Price now</div><div class='v'>{cents(p['price'])}</div></td>"
        f"<td><div class='l'>Their avg entry</div><div class='v'>{cents(p['avg_entry'])}</div></td>"
        f"<td><div class='l'>Drift</div><div class='v {drift_cls}'>{p['drift']*100:+.0f}¢</div></td>"
        f"</tr></table>"
        f"<div class='line2'><b>{p['wallets']}</b> top wallets agree with {money(p['agree_money'])}; "
        f"{money(p['oppose_money'])} on the other side</div>"
        f"<div class='holders'>Biggest: {holders}</div>"
        f"{extra}</div>")


def render_html(picks, wallets):
    above = [p for p in picks if p["tier"] == "bet"]
    below = [p for p in picks if p["tier"] != "bet"]
    stamp = now_local().strftime("%a %b %d, %Y at %-I:%M %p %Z")
    parts = [
        "<!doctype html><html><head><meta charset='utf-8'>"
        "<meta name='viewport' content='width=device-width,initial-scale=1'>"
        "<title>Polymarket Picks</title><style>" + REPORT_CSS + "</style></head><body><div class='wrap'>",
        f"<div class='top'><h1>Polymarket Picks</h1><div class='sub'>Updated {escape(stamp)}</div></div>",
        "<table class='stats'><tr>"
        f"<td class='stat'><div class='v'>{len(above)}</div><div class='l'>Above the line</div></td>"
        f"<td class='stat'><div class='v'>{len(below)}</div><div class='l'>Watching</div></td>"
        f"<td class='stat'><div class='v'>{len(wallets)}</div><div class='l'>Top wallets followed</div></td>"
        f"<td class='stat'><div class='v'>${CONFIG['bankroll']:,.0f}</div><div class='l'>Bankroll</div></td>"
        "</tr></table>",
        "<div class='sec go'>Above the line</div>"
        "<p class='note'>Meets every rule: several top wallets agree, the price has not run away from their "
        "entries, and little top-wallet money is on the other side.</p>",
    ]
    if not above:
        parts.append("<div class='empty'><b>Nothing meets every rule today.</b> Sitting out is a valid trade.</div>")
    for i, p in enumerate(above, 1):
        parts.append(card(i, p, wallets))
    parts.append("<div class='cutoff'><span class='cutlabel'>Cutoff line</span></div>"
                 "<div class='sec stop'>Below the line</div>"
                 "<p class='note'>Watch only. The odds are less in your favor; the reason is shown on each. "
                 "These are logged too, so the track record can show whether the line works.</p>")
    for i, p in enumerate(below, len(above) + 1):
        parts.append(card(i, p, wallets))
    parts.append(
        f"<div class='foot'>Following wallets ranked in the top {CONFIG['leaderboard_size']} on the leaderboard in at "
        f"least {CONFIG['min_windows']} of these windows: {', '.join(CONFIG['windows'])}. Score = wallet agreement (40) + "
        "price freshness (20) + low opposition (20) + position size (10) + price zone (10). "
        "Not financial advice. Copying means worse prices than the original traders, and no ranking "
        "guarantees profit.</div></div></body></html>")
    return "\n".join(parts)


def send_email(html, n_above):
    host = os.environ.get("SMTP_HOST", "smtp.gmail.com")
    port = int(os.environ.get("SMTP_PORT", "465"))
    user, pw, to = os.environ.get("SMTP_USER"), os.environ.get("SMTP_PASS"), os.environ.get("MAIL_TO")
    if not (user and pw and to):
        print("Email skipped: set SMTP_USER, SMTP_PASS and MAIL_TO.")
        return
    msg = MIMEText(html, "html")
    msg["Subject"] = f"Polymarket {now_local().strftime('%b %d')}: {n_above} above the line"
    msg["From"], msg["To"] = user, to
    with smtplib.SMTP_SSL(host, port, context=ssl.create_default_context()) as s:
        s.login(user, pw)
        s.send_message(msg)
    print("Email sent to", to)


# ---------------- main ----------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--email", action="store_true", help="email the report")
    ap.add_argument("--evaluate", action="store_true", help="show paper-trade results and exit")
    ap.add_argument("--debug", action="store_true", help="print funnel stats")
    ap.add_argument("--out", default=REPORT_PATH, help="where to write the HTML report")
    ap.add_argument("--db", default=None, help="path of the paper-trade log (SQLite)")
    args = ap.parse_args()

    global DB_PATH
    if args.db:
        DB_PATH = args.db
    os.makedirs(os.path.dirname(os.path.abspath(DB_PATH)), exist_ok=True)
    if os.environ.get("BANKROLL"):
        CONFIG["bankroll"] = num(os.environ["BANKROLL"], CONFIG["bankroll"])
    if args.evaluate:
        evaluate()
        return

    wallets = choose_wallets()
    print(f"Following {len(wallets)} wallets")
    wallet_positions = {}
    for addr, info in wallets.items():
        try:
            wallet_positions[addr] = {"name": info["name"], "positions": fetch_positions(addr)}
        except Exception as e:
            print("skip", addr[:10], e)
        time.sleep(CONFIG["pause_seconds"])

    picks = build_picks(wallet_positions, debug=args.debug)
    for p in picks:
        if not p["slug"]:
            p["slug"] = lookup_slug(p["condition_id"])
            time.sleep(CONFIG["pause_seconds"])
    log_picks(picks)
    html = render_html(picks, wallets)
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as f:
        f.write(html)
    above = [p for p in picks if p["tier"] == "bet"]
    print(f"{len(picks)} listed, {len(above)} above the line. Report: {args.out}")
    for p in picks:
        mark = "BET  " if p["tier"] == "bet" else "watch"
        stake = f" stake ${p['stake']:.2f}" if p["stake"] else ""
        print(f"  {mark} {p['score']:>3.0f} | {p['wallets']} wallets | {p['price']:.2f} | "
              f"{p['outcome']} | {p['title'][:55]}{stake}")
    if args.email:
        send_email(html, len(above))


if __name__ == "__main__":
    main()
