/* C.A. Creative Bot — created and owned by Charles Amankwah */

const API = "https://api.hyperliquid.xyz/info";
const WS_URL = "wss://api.hyperliquid.xyz/ws";
const IV_MS = { "1m": 60000, "5m": 300000, "15m": 900000, "1h": 3600000, "4h": 14400000, "1d": 86400000 };
const HIP3_DEX = "xyz";
const STOCKS = ["NVDA","TSLA","AAPL","MSFT","GOOGL","AMZN","META","PLTR"];
const COMMODITIES = ["GOLD","SILVER","BRENTOIL"];
const MIN_CRYPTO_VOL = 2_000_000;
const TOP_N_CRYPTO = 20;
const SCAN_INTERVAL = 60_000;
const STATE_POLL_MS = 4_000;
const CANDLE_CACHE_MS = 90_000;
const CACHE_TTL_BY_IV = { "1m": 30_000, "5m": 90_000, "15m": 300_000, "1h": 1_800_000, "4h": 7_200_000, "1d": 14_400_000 };
const MAINT_FRAC = 0.9;
const AUTO_MAX_OPEN = 5;
const AUTO_COOLDOWN_MS = 15 * 60 * 1000;

const $ = id => document.getElementById(id);
const fmt = x => x == null ? "—" : (x >= 1000 ? Number(x).toLocaleString(undefined,{maximumFractionDigits:2}) : Number(x).toPrecision(6)).toString();
const fmt2 = x => x == null ? "—" : Number(x).toLocaleString(undefined,{minimumFractionDigits:2,maximumFractionDigits:2});
const esc = s => String(s).replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;","\"":"&quot;","'":"&#39;"}[c]));

const store = {
  getTrades: () => { try { return JSON.parse(localStorage.getItem("legend_trades") || "[]"); } catch { return []; } },
  setTrades: t => localStorage.setItem("legend_trades", JSON.stringify(t)),
  getLastSignals: () => { try { return JSON.parse(localStorage.getItem("legend_last_signals") || "{}"); } catch { return {}; } },
  setLastSignals: m => localStorage.setItem("legend_last_signals", JSON.stringify(m)),
  getLastConf: () => { try { return JSON.parse(localStorage.getItem("legend_last_confidence") || "{}"); } catch { return {}; } },
  setLastConf: m => localStorage.setItem("legend_last_confidence", JSON.stringify(m)),
  getBtLast: () => { try { return JSON.parse(localStorage.getItem("legend_backtest_last") || "null"); } catch { return null; } },
  setBtLast: x => localStorage.setItem("legend_backtest_last", JSON.stringify(x)),
  getHistory: () => { try { return JSON.parse(localStorage.getItem("legend_history") || "{}"); } catch { return {}; } },
  setHistory: h => localStorage.setItem("legend_history", JSON.stringify(h)),
};

const STATE = { status: "starting", lastScan: null, error: null, mids: {}, coins: {}, watchlist: [] };
let currentCoin = null, currentIv = "5m", assetFilter = "ALL";
let chart, candleSeries, ema20S, ema50S, ema200S;
let lastBars = [], lastBarTime = 0;
let priceLines = [], _lastPriceLineHash = "";
let dragState = { active: false, line: null, trade: null, field: null };

function ema(vals, n) {
  if (vals.length < n) return null;
  const k = 2 / (n + 1);
  let e = vals.slice(0, n).reduce((a, b) => a + b, 0) / n;
  for (let i = n; i < vals.length; i++) e = vals[i] * k + e * (1 - k);
  return e;
}
function emaSeries(vals, n) {
  if (vals.length < n) return [];
  const k = 2 / (n + 1);
  let e = vals.slice(0, n).reduce((a, b) => a + b, 0) / n;
  const out = [e];
  for (let i = n; i < vals.length; i++) { e = vals[i] * k + e * (1 - k); out.push(e); }
  return out;
}
function wilderLast(vals, n) {
  if (vals.length < n) return null;
  let a = vals.slice(0, n).reduce((x, y) => x + y, 0) / n;
  for (let i = n; i < vals.length; i++) a = (a * (n - 1) + vals[i]) / n;
  return a;
}
function wilderSeries(vals, n) {
  if (vals.length < n) return [];
  let a = vals.slice(0, n).reduce((x, y) => x + y, 0) / n;
  const out = [a];
  for (let i = n; i < vals.length; i++) { a = (a * (n - 1) + vals[i]) / n; out.push(a); }
  return out;
}
function rsi(cs, n = 14) {
  if (cs.length <= n + 1) return null;
  const g = [], l = [];
  for (let i = 1; i < cs.length; i++) {
    g.push(Math.max(cs[i] - cs[i - 1], 0));
    l.push(Math.max(cs[i - 1] - cs[i], 0));
  }
  const ag = wilderLast(g, n), al = wilderLast(l, n);
  if (ag == null || al == null) return null;
  return al === 0 ? 100 : 100 - 100 / (1 + ag / al);
}
function atr(cs, n = 14) {
  if (cs.length <= n) return null;
  const trs = [];
  for (let i = 1; i < cs.length; i++) trs.push(Math.max(cs[i].h - cs[i].l, Math.abs(cs[i].h - cs[i-1].c), Math.abs(cs[i].l - cs[i-1].c)));
  return wilderLast(trs, n);
}
function adx(cs, n = 14) {
  if (cs.length < 2 * n + 1) return { adx: null };
  const pdm = [], mdm = [], trs = [];
  for (let i = 1; i < cs.length; i++) {
    const up = cs[i].h - cs[i-1].h, dn = cs[i-1].l - cs[i].l;
    pdm.push(up > dn && up > 0 ? up : 0);
    mdm.push(dn > up && dn > 0 ? dn : 0);
    trs.push(Math.max(cs[i].h - cs[i].l, Math.abs(cs[i].h - cs[i-1].c), Math.abs(cs[i].l - cs[i-1].c)));
  }
  const st = wilderSeries(trs, n), sp = wilderSeries(pdm, n), sm = wilderSeries(mdm, n);
  if (!st.length) return { adx: null };
  const dx = [];
  for (let i = 0; i < st.length; i++) {
    if (st[i] === 0) { dx.push(0); continue; }
    const lp = 100 * sp[i] / st[i], lm = 100 * sm[i] / st[i];
    dx.push((lp + lm) === 0 ? 0 : 100 * Math.abs(lp - lm) / (lp + lm));
  }
  const as = wilderSeries(dx, n);
  return { adx: as.length ? as[as.length - 1] : null };
}
function volRatio(cs) {
  if (cs.length < 12) return 1;
  const recent = cs.slice(-6).map(c => c.v);
  const base = cs.length >= 72 ? cs.slice(-72, -6).map(c => c.v) : cs.slice(0, -6).map(c => c.v);
  const mR = recent.reduce((a,b)=>a+b,0)/recent.length;
  const mB = base.reduce((a,b)=>a+b,0)/Math.max(base.length, 1);
  return mB > 0 ? mR / mB : 1;
}

const candleCache = new Map();
async function fetchCandles(coin, interval, lookback = 320, dex = "", retries = 3) {
  const step = IV_MS[interval];
  const end = Date.now(), start = end - step * (lookback + 2);
  const payload = { type: "candleSnapshot", req: { coin, interval, startTime: start, endTime: end } };
  if (dex) payload.dex = dex;
  let lastErr = null;
  for (let i = 0; i < retries; i++) {
    try {
      const r = await fetch(API, { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(payload) });
      if (r.status === 429) { await new Promise(x => setTimeout(x, 2000 * (i + 1))); lastErr = "429"; continue; }
      if (!r.ok) throw new Error("HTTP " + r.status);
      const data = await r.json();
      return data.map(c => ({ t: c.t, T: c.T, o: +c.o, h: +c.h, l: +c.l, c: +c.c, v: +c.v }));
    } catch (e) {
      lastErr = e.message || String(e);
      if (i < retries - 1) await new Promise(x => setTimeout(x, 1500 * (i + 1)));
    }
  }
  throw new Error("candles failed: " + lastErr);
}
async function getCandles(coin, interval, lookback = 320, dex = "") {
  const key = `${coin}|${interval}|${dex}`;
  const hit = candleCache.get(key);
  const _ttl = CACHE_TTL_BY_IV[interval] || CANDLE_CACHE_MS;
  if (hit && Date.now() - hit.ts < _ttl) return hit.data;
  try {
    const data = await fetchCandles(coin, interval, lookback, dex);
    candleCache.set(key, { ts: Date.now(), data });
    return data;
  } catch (e) { if (hit) return hit.data; throw e; }
}

const metaCache = new Map();
async function fetchMeta(dex = "") {
  const cached = metaCache.get(dex);
  if (cached && Date.now() - cached.ts < 60000) return cached.data;
  const payload = { type: "metaAndAssetCtxs" };
  if (dex) payload.dex = dex;
  const r = await fetch(API, { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(payload) });
  if (!r.ok) throw new Error("meta HTTP " + r.status);
  const data = await r.json();
  const universe = data[0].universe, ctxs = data[1];
  const out = [];
  for (let i = 0; i < universe.length; i++) {
    const m = universe[i], c = ctxs[i];
    if (!m || m.isDelisted) continue;
    out.push({ raw: m.name, coin: dex ? `${dex}:${m.name}` : m.name, dex,
      maxLev: parseInt(m.maxLeverage || 3), vol: parseFloat(c.dayNtlVlm || 0),
      funding: parseFloat(c.funding || 0), markPx: parseFloat(c.markPx || 0) });
  }
  metaCache.set(dex, { ts: Date.now(), data: out });
  return out;
}

function tf(candles, livePrice) {
  if (!candles || candles.length < 10) return null;
  const cs = candles.map(c => ({ ...c }));
  const last = cs[cs.length - 1];
  if (livePrice > 0) { last.c = livePrice; last.h = Math.max(last.h, livePrice); last.l = Math.min(last.l, livePrice); }
  const closes = cs.map(c => c.c);
  return { candles: cs, closes, e20: ema(closes, 20), e50: ema(closes, 50), e200: ema(closes, 200),
    e20s: emaSeries(closes, 20), e50s: emaSeries(closes, 50),
    rsi: rsi(closes), atr: atr(cs), adx: adx(cs).adx, price: livePrice || closes[closes.length - 1] };
}

function trendOf(t) {
  if (!t || t.e20 == null || t.e50 == null) return "FLAT";
  const up = t.e20 > t.e50 && (t.e200 == null || t.e50 > t.e200) && t.price > t.e50;
  const dn = t.e20 < t.e50 && (t.e200 == null || t.e50 < t.e200) && t.price < t.e50;
  if (t.e20s.length >= 6 && t.e50s.length >= 6) {
    let upCount = 0, dnCount = 0;
    const off = t.closes.length - t.e20s.length;
    for (let i = t.e20s.length - 6; i < t.e20s.length - 1; i++) {
      const c = t.closes[i + off];
      if (t.e20s[i] > t.e50s[i] && c > t.e50s[i]) upCount++;
      if (t.e20s[i] < t.e50s[i] && c < t.e50s[i]) dnCount++;
    }
    let fresh = false;
    for (let i = Math.max(2, t.e20s.length - 3); i < t.e20s.length; i++) {
      if ((t.e20s[i-1] - t.e50s[i-1]) * (t.e20s[i] - t.e50s[i]) < 0) { fresh = true; break; }
    }
    if (fresh) return "FLAT";
    if (up && upCount >= 4) return "UP";
    if (dn && dnCount >= 4) return "DOWN";
  }
  return "FLAT";
}

function computeBullScore(T, adx5, volR, setupOk, momentumOk) {
  let s = 0;
  if (T["4h"]?.trend === "UP") s += 20;
  if (T["1h"]?.trend === "UP") s += 20;
  if (T["15m"]?.trend === "UP") s += 10;
  if (adx5 >= 35) s += 15; else if (adx5 >= 30) s += 10; else if (adx5 >= 25) s += 5;
  if (volR >= 1.8) s += 15; else if (volR >= 1.5) s += 10; else if (volR >= 1.2) s += 5;
  if (setupOk) s += 10;
  if (momentumOk) s += 10;
  if (T["1d"]?.trend === "UP") s += 10;
  return Math.min(100, s);
}

function computeBearScore(T, price, atr5, adx5, volR, rsi5) {
  let s = 0;
  const t1 = T["1h"], t4 = T["4h"], t5 = T["5m"];
  if (t1?.trend === "DOWN") s += 25; else if (t1?.e50 && price < t1.e50) s += 15;
  if (t4?.trend === "DOWN") s += 20;
  if (t5?.trend === "DOWN") s += 8;
  if (adx5 >= 30) s += 22; else if (adx5 >= 25) s += 18; else if (adx5 < 15) s -= 8;
  if (volR >= 1.5) s += 12; else if (volR >= 1.2) s += 7;
  if (rsi5 < 30) s += 12; else if (rsi5 < 40) s += 8; else if (rsi5 < 45) s += 4; else if (rsi5 > 55) s -= 8;
  if (t1?.e50 && atr5 > 0) {
    const d = (price - t1.e50) / atr5;
    if (d < -2) s += 10; else if (d < -1) s += 5;
  }
  return Math.max(0, Math.min(100, s));
}

function signalFrom(candlesByTf, livePrice) {
  if (!candlesByTf["5m"] || !candlesByTf["1h"] || !candlesByTf["4h"]) return null;
  const T = {};
  for (const iv of ["5m","15m","1h","4h","1d"]) {
    if (!candlesByTf[iv]) continue;
    const t = tf(candlesByTf[iv], livePrice);
    if (t) { t.trend = trendOf(t); T[iv] = t; }
  }
  if (!T["5m"] || !T["1h"] || !T["4h"]) return null;
  const price = T["5m"].price;
  if (!price || price <= 0) return null;
  const a5 = T["5m"].atr || 0;
  if (a5 <= 0) return null;
  const rsi5 = T["5m"].rsi, rsi1 = T["1h"].rsi;
  const adx5 = T["5m"].adx, adx15 = T["15m"]?.adx, adx1 = T["1h"].adx;
  const volR = volRatio(T["5m"].candles);
  const anyUptrend = T["4h"].trend === "UP" && T["1h"].trend === "UP";

  if (!anyUptrend) {
    const bear = computeBearScore(T, price, a5, adx5 || 0, volR, rsi5 || 50);
    const sellGates = [
      { name: "1-hour trend is down", pass: T["1h"].trend === "DOWN" || (T["1h"].e50 && price < T["1h"].e50) },
      { name: "4-hour trend is weak", pass: (T["4h"].e20 && T["4h"].e20 < T["4h"].e50) || (T["4h"].e50 && price < T["4h"].e50) },
      { name: "Trend is strong (ADX 28+)", pass: adx5 != null && adx5 >= 28 },
      { name: "Bearish strength is high (65+)", pass: bear >= 65 },
      { name: "Trading volume is high (1.2x+)", pass: volR >= 1.2 },
      { name: "Momentum is negative", pass: (() => {
          const c = T["5m"].closes; if (c.length < 4) return false;
          return !(c[c.length-2] > c[c.length-3] && c[c.length-3] > c[c.length-4]);
        })() },
      { name: "Not already oversold", pass: rsi1 != null && rsi1 > 28 },
    ];
    const passed = sellGates.filter(g => g.pass).length;
    const allPass = passed === sellGates.length;
    const conflicts = [];
    if (allPass && rsi1 != null && rsi1 < 25) conflicts.push("already deeply oversold");
    if (allPass && T["1h"].e50 && a5 > 0 && price < T["1h"].e50 - 6 * a5) conflicts.push("price way below trend line (exhaustion)");
    if (allPass && adx1 != null && adx1 < 15) conflicts.push("the bigger trend is still too weak");
    const tfT = [T["1d"]?.trend, T["4h"].trend, T["1h"].trend].filter(x => x && x !== "FLAT");
    if (tfT.length >= 2 && new Set(tfT).size >= 2) conflicts.push("timeframes disagree with each other");

    const soft = [
      T["1d"]?.trend === "DOWN", adx5 != null && adx5 >= 35, adx1 != null && adx1 >= 25,
      volR >= 1.7, rsi5 != null && rsi5 >= 55 && rsi5 <= 65,
      T["1h"].e50 && a5 > 0 && Math.abs(price - T["1h"].e50) / a5 < 2,
      rsi1 != null && rsi1 >= 45 && rsi1 <= 65,
      T["1d"]?.e50 && T["4h"].e50 && T["1h"].e50 && T["15m"]?.e50 && T["5m"].e50 &&
        price < T["1d"].e50 && price < T["4h"].e50 && price < T["1h"].e50 && price < T["15m"].e50 && price < T["5m"].e50,
    ].filter(Boolean).length;

    if (allPass && conflicts.length === 0 && soft >= 4) {
      const tier = soft >= 6 ? "CERTAIN" : "CONFIDENT";
      const why = "The 1-hour trend has broken down and momentum has flipped negative. If you already own this coin, sell. If you don't own it, stay out — do not buy until the trend recovers.";
      return { signal: "SELL", confidence: tier, score: bear, price, stop: price * 1.03, tp2: price * 0.97, why, gatesPassed: passed, gatesTotal: sellGates.length, soft, trend: T };
    }
    const failed = sellGates.filter(g => !g.pass).map(g => g.name);
    let why = "No clear signal right now. ";
    if (failed.length) why += "Still missing: " + failed.join(", ") + ". ";
    if (conflicts.length) why += "Indicators disagree (" + conflicts.join("; ") + "). ";
    why += "The bot is waiting for more clarity rather than guessing.";
    return { signal: "NEUTRAL", confidence: "LOW", score: bear, price, why, gatesPassed: passed, gatesTotal: sellGates.length, soft, trend: T };
  }

  const t5c = T["5m"].candles, e20_5 = T["5m"].e20;
  const distEma = e20_5 ? (price - e20_5) / a5 : 0;
  const recentHigh = t5c.length >= 21 ? Math.max(...t5c.slice(-21, -1).map(c => c.h)) : price;
  const bounced = (() => {
    if (!e20_5 || t5c.length < 4) return false;
    for (let i = t5c.length - 4; i < t5c.length - 1; i++) {
      if (t5c[i].l <= e20_5 * 1.002 && t5c[i].c > e20_5) return true;
    }
    return false;
  })();
  const pullbackOk = distEma >= -0.5 && distEma <= 0.2 && rsi5 != null && rsi5 >= 50 && rsi5 <= 65 && bounced;
  const breakoutOk = (() => {
    if (t5c.length < 24) return false;
    for (let i = t5c.length - 4; i < t5c.length - 1; i++) {
      const hi = Math.max(...t5c.slice(i - 20, i).map(c => c.h));
      const base = t5c.slice(Math.max(0, i - 72), Math.max(1, i - 6));
      const baseAvg = base.length ? base.reduce((s, c) => s + c.v, 0) / base.length : t5c[i].v;
      if (t5c[i].c > hi && baseAvg > 0 && t5c[i].v / baseAvg >= 1.3) return true;
    }
    return false;
  })();
  const setupOk = pullbackOk || breakoutOk;
  const momentumOk = (() => {
    const c = T["5m"].closes; if (c.length < 4) return false;
    return !(c[c.length-2] < c[c.length-3] && c[c.length-3] < c[c.length-4]);
  })();

  const gates = [
    { name: "1-day trend is up", pass: T["1d"] ? (T["1d"].trend === "UP" || (T["1d"].e50 && a5 > 0 && Math.abs(price - T["1d"].e50) / a5 < 3)) : true },
    { name: "4-hour trend is up", pass: T["4h"].trend === "UP" },
    { name: "1-hour trend is up", pass: T["1h"].trend === "UP" },
    { name: "15-minute trend is up", pass: T["15m"] ? T["15m"].trend === "UP" : false },
    { name: "Price above key trend levels", pass: T["4h"].e50 && T["1h"].e50 && price > T["4h"].e50 && price > T["1h"].e50 },
    { name: "Price is at a good entry spot", pass: setupOk },
    { name: "Trend is strong (ADX 28+)", pass: adx5 != null && adx5 >= 28 },
    { name: "Trend is strong on 15-min (ADX 18+)", pass: adx15 != null && adx15 >= 18 },
    { name: "Trading volume is high (1.15x+)", pass: volR >= 1.15 },
    { name: "Momentum is pointing up", pass: momentumOk },
    { name: "Not overbought", pass: rsi1 != null && rsi1 < 72 },
    { name: "Not too far from trend line", pass: T["1h"].e50 && a5 > 0 && Math.abs(price - T["1h"].e50) / a5 <= 4 },
  ];
  const bullScore = computeBullScore(T, adx5 || 0, volR, setupOk, momentumOk);
  gates.push({ name: "Overall confidence is high (78+)", pass: bullScore >= 78 });
  const passed = gates.filter(g => g.pass).length;

  const soft = [
    T["1d"]?.trend === "UP", adx5 != null && adx5 >= 35, adx1 != null && adx1 >= 25,
    volR >= 1.7, rsi5 != null && rsi5 >= 55 && rsi5 <= 65,
    T["1h"].e50 && a5 > 0 && Math.abs(price - T["1h"].e50) / a5 < 2,
    rsi1 != null && rsi1 >= 45 && rsi1 <= 65,
    T["1d"]?.e50 && T["4h"].e50 && T["1h"].e50 && T["15m"]?.e50 && T["5m"].e50 &&
      price > T["1d"].e50 && price > T["4h"].e50 && price > T["1h"].e50 && price > T["15m"].e50 && price > T["5m"].e50,
  ].filter(Boolean).length;

  const conflicts = [];
  if (rsi1 != null && rsi1 > 75) conflicts.push("already overbought");
  if (T["1h"].e50 && a5 > 0 && price > T["1h"].e50 + 6 * a5) conflicts.push("price way above trend line (chasing)");
  if (adx1 != null && adx1 < 15) conflicts.push("bigger trend is too weak");
  const tfT = [T["1d"]?.trend, T["4h"].trend, T["1h"].trend].filter(x => x && x !== "FLAT");
  if (tfT.length >= 2 && new Set(tfT).size >= 2) conflicts.push("timeframes disagree");

  const allPass = passed === gates.length;

  if (allPass && conflicts.length === 0 && soft >= 4) {
    const swingLow = Math.min(...t5c.slice(-12).map(c => c.l));
    let stop = Math.min(swingLow - 0.2 * a5, price - 1.5 * a5);
    stop = Math.max(stop, price - 3 * a5);
    const risk = price - stop;
    const tp1 = price + 2 * risk, tp2 = price + 3 * risk;
    const tier = soft >= 6 ? "CERTAIN" : "CONFIDENT";
    const setup = pullbackOk ? "PULLBACK" : "BREAKOUT";
    const why = "The 4-hour, 1-hour, and 15-minute trends are all up, and the 1-day trend confirms it. The price just pulled back to the 20-period moving average (a healthy buy point), with strong volume and positive momentum. Everything is aligned. Buy at the current price.";
    return { signal: "BUY", setup, confidence: tier, score: bullScore, price, entry: price, stop, tp1, tp2, why, gatesPassed: passed, gatesTotal: gates.length, soft, trend: T };
  }

  if (bullScore >= 60 && passed >= gates.length - 4 && conflicts.length === 0) {
    const failed = gates.filter(g => !g.pass).map(g => g.name);
    const why = "Uptrend is healthy, but the current price isn't a safe entry yet. Wait for a small dip or a clean breakout. What's still missing: " + failed.join(", ") + ".";
    const entryZone = e20_5 ? e20_5 - 0.25 * a5 : price;
    return { signal: "WAIT", confidence: "MED", score: bullScore, price, entryZone, why, gatesPassed: passed, gatesTotal: gates.length, soft, trend: T };
  }

  const failed = gates.filter(g => !g.pass).map(g => g.name);
  let why = "No clear signal right now. ";
  if (failed.length) why += "Still missing: " + failed.slice(0, 3).join(", ") + ". ";
  if (conflicts.length) why += "Indicators disagree (" + conflicts.join("; ") + "). ";
  why += "The bot is being patient instead of guessing.";
  return { signal: "NEUTRAL", confidence: "LOW", score: bullScore, price, why, gatesPassed: passed, gatesTotal: gates.length, soft, trend: T };
}

async function buildUniverse() {
  const list = [];
  try {
    const crypto = await fetchMeta("");
    crypto.sort((a, b) => b.vol - a.vol);
    for (const m of crypto.filter(m => m.vol > MIN_CRYPTO_VOL).slice(0, TOP_N_CRYPTO))
      list.push({ ...m, assetClass: "CRYPTO" });
  } catch (e) {}
  try {
    const hip = await fetchMeta(HIP3_DEX);
    for (const m of hip) {
      if (STOCKS.includes(m.raw)) list.push({ ...m, assetClass: "STOCK" });
      else if (COMMODITIES.includes(m.raw)) list.push({ ...m, assetClass: "COMMODITY" });
    }
  } catch (e) {}
  return list;
}

let scanRunning = false;
async function runScan() {
  if (scanRunning) return;
  scanRunning = true;
  STATE.status = "scanning"; render();
  try {
    const universe = await buildUniverse();
    const results = {};
    const queue = [...universe];
    const total = queue.length;
    let done = 0;
    let lastProgressiveRender = 0;
    const order = { BUY:0, WAIT:1, SELL:2, NEUTRAL:3 };
    async function worker() {
      while (queue.length) {
        const m = queue.shift();
        try {
          const candles = {};
          await Promise.all(["5m","15m","1h","4h","1d"].map(async iv => {
            try { candles[iv] = await getCandles(m.raw, iv, 320, m.dex); } catch(e) {}
          }));
          const live = parseFloat(STATE.mids[m.coin] || 0) || m.markPx;
          const sig = signalFrom(candles, live);
          if (sig) {
            sig.coin = m.coin; sig.assetClass = m.assetClass; sig.dex = m.dex;
            results[m.coin] = sig;
            const now = Date.now();
            if (now - lastProgressiveRender > 400 || done + 1 === total) {
              STATE.coins = { ...results };
              STATE.watchlist = Object.values(STATE.coins).sort((a,b) => (order[a.signal]||9) - (order[b.signal]||9) || (b.score||0) - (a.score||0)).map(c => c.coin);
              STATE.status = `scanning ${done + 1}/${total}`;
              render();
              lastProgressiveRender = now;
            }
          }
        } catch(e) {}
        done++;
        STATE.status = `scanning ${done}/${total}`;
      }
    }
    await Promise.all(Array(12).fill(0).map(() => worker()));
    const sorted = Object.values(results).sort((a,b) => (order[a.signal]||9) - (order[b.signal]||9) || (b.score||0) - (a.score||0));
    STATE.coins = results;
    STATE.watchlist = sorted.map(c => c.coin);
    STATE.lastScan = Date.now();
    STATE.status = "live"; STATE.error = null;
    checkSignalTransitions(sorted);
  } catch (e) { STATE.error = String(e); STATE.status = "error"; }
  scanRunning = false;
  render();
}

let ws;
function connectWS() {
  try {
    ws = new WebSocket(WS_URL);
    ws.onopen = () => ws.send(JSON.stringify({ method: "subscribe", subscription: { type: "allMids" } }));
    ws.onmessage = (ev) => { try { const m = JSON.parse(ev.data); if (m.channel === "allMids") STATE.mids = m.data.mids || {}; } catch(e) {} };
    ws.onclose = () => setTimeout(connectWS, 3000);
    ws.onerror = () => {};
  } catch(e) { setTimeout(connectWS, 5000); }
}

function initChart() {
  const el = $("chart"); el.innerHTML = "";
  chart = LightweightCharts.createChart(el, {
    layout: { background: { color: getComputedStyle(document.documentElement).getPropertyValue("--card").trim() || "#171b24" }, textColor: getComputedStyle(document.documentElement).getPropertyValue("--tx").trim() || "#e8ebf2", fontSize: 11 },
    grid: { vertLines: { color: getComputedStyle(document.documentElement).getPropertyValue("--bd").trim() || "#262c38" }, horzLines: { color: getComputedStyle(document.documentElement).getPropertyValue("--bd").trim() || "#262c38" } },
    timeScale: { timeVisible: true, secondsVisible: false, borderColor: getComputedStyle(document.documentElement).getPropertyValue("--bd").trim() || "#262c38" },
    rightPriceScale: { borderColor: getComputedStyle(document.documentElement).getPropertyValue("--bd").trim() || "#262c38" },
    crosshair: { mode: 0 },
    handleScroll: true, handleScale: true,
  });
  candleSeries = chart.addCandlestickSeries({ upColor: "#2ecc83", downColor: "#ff5d68", borderVisible: false, wickUpColor: "#2ecc83", wickDownColor: "#ff5d68" });
  ema20S = chart.addLineSeries({ color: "#4ea8ff", lineWidth: 1, priceLineVisible: false, lastValueVisible: false });
  ema50S = chart.addLineSeries({ color: "#f0b429", lineWidth: 1, priceLineVisible: false, lastValueVisible: false });
  ema200S = chart.addLineSeries({ color: "#8b93a1", lineWidth: 1, priceLineVisible: false, lastValueVisible: false });
  new ResizeObserver(() => { if (chart) chart.applyOptions({ width: el.clientWidth, height: el.clientHeight }); }).observe(el);
  attachDragHandlers(el);
}

function buildEmaSeries(arr, offset, stepMs) {
  if (!lastBars.length || !arr.length) return [];
  const t0 = lastBars[0].time;
  return arr.map((v, i) => ({ time: t0 + Math.round((offset + i) * (stepMs/1000)), value: v }));
}

function prefetchAdjacent(coin, iv) {
  const order = ["1m","5m","15m","1h","4h","1d"];
  const idx = order.indexOf(iv);
  if (idx < 0) return;
  const meta = STATE.coins[coin] || {};
  const raw = coin.includes(":") ? coin.split(":")[1] : coin;
  const dex = meta.dex || "";
  [idx - 1, idx + 1].forEach(i => {
    if (i >= 0 && i < order.length) getCandles(raw, order[i], 320, dex).catch(() => {});
  });
}

async function loadCandles(coin, iv, preserveView = false) {
  if (!coin || !chart) return;
  let savedRange = null, wasAtEnd = false;
  if (preserveView) {
    try {
      savedRange = chart.timeScale().getVisibleRange();
      if (savedRange && lastBarTime > 0) {
        const barSec = IV_MS[iv] / 1000;
        wasAtEnd = Math.abs(savedRange.to - lastBarTime) < barSec * 2;
      }
    } catch(e) {}
  }
  try {
    const meta = STATE.coins[coin] || {};
    const raw = coin.includes(":") ? coin.split(":")[1] : coin;
    const dex = meta.dex || "";
    const _ck = `${raw}|${iv}|${dex}`;
    const _cached = candleCache.get(_ck);
    if (_cached && _cached.data.length && candleSeries && !lastBars.length) {
      try {
        const _bars = _cached.data.map(c => ({ time: Math.floor(c.t/1000), open: c.o, high: c.h, low: c.l, close: c.c }));
        candleSeries.setData(_bars);
      } catch(e) {}
    }
    const data = await getCandles(raw, iv, 320, dex);
    if (!data.length) return;
    lastBars = data.map(c => ({ time: Math.floor(c.t/1000), open: c.o, high: c.h, low: c.l, close: c.c }));
    lastBarTime = lastBars[lastBars.length-1].time;
    candleSeries.setData(lastBars);
    const closes = data.map(c => c.c);
    ema20S.setData(buildEmaSeries(emaSeries(closes, 20), 19, IV_MS[iv]));
    ema50S.setData(buildEmaSeries(emaSeries(closes, 50), 49, IV_MS[iv]));
    ema200S.setData(buildEmaSeries(emaSeries(closes, 200), 199, IV_MS[iv]));
    if (wasAtEnd) {
      chart.timeScale().scrollToRealTime();
    } else if (savedRange) {
      try { chart.timeScale().setVisibleRange(savedRange); }
      catch(e) { chart.timeScale().fitContent(); }
    } else {
      chart.timeScale().fitContent();
    }
    drawPriceLines(coin, true);
    prefetchAdjacent(coin, iv);
  } catch(e) {}
}

function updateFormingBar(live) {
  if (!lastBars.length || !live || !chart) return;
  const step = IV_MS[currentIv];
  if (Math.floor(Date.now() / step) * step / 1000 > lastBarTime) {
    loadCandles(currentCoin, currentIv, true);
    return;
  }
  const last = lastBars[lastBars.length-1];
  last.close = live; last.high = Math.max(last.high, live); last.low = Math.min(last.low, live);
  candleSeries.update(last);
}

function drawPriceLines(coin, force = false) {
  if (!candleSeries || !coin) return;
  if (dragState.active && !force) return;
  const open = store.getTrades().filter(t => !t.closed_at && t.coin === coin);
  const hash = coin + "|" + open.map(t => `${t.id}:${t.entry}:${t.stop}:${t.tp2}`).join(",");
  if (!force && hash === _lastPriceLineHash) return;
  _lastPriceLineHash = hash;
  priceLines.forEach(p => { try { candleSeries.removePriceLine(p.line); } catch(e) {} });
  priceLines = [];
  for (const t of open) {
    try {
      priceLines.push({ line: candleSeries.createPriceLine({ price: t.entry, color: "#4ea8ff", lineWidth: 1, lineStyle: LightweightCharts.LineStyle.Solid, axisLabelVisible: true, title: (t.side || "LONG") + " entry" }), trade: t, field: null });
      priceLines.push({ line: candleSeries.createPriceLine({ price: t.stop, color: "#ff5d68", lineWidth: 2, lineStyle: LightweightCharts.LineStyle.Dashed, axisLabelVisible: true, title: "Stop (drag)" }), trade: t, field: "stop" });
      priceLines.push({ line: candleSeries.createPriceLine({ price: t.tp2, color: "#2ecc83", lineWidth: 2, lineStyle: LightweightCharts.LineStyle.Dashed, axisLabelVisible: true, title: "TP2 (drag)" }), trade: t, field: "tp2" });
    } catch(e) {}
  }
}

function attachDragHandlers(el) {
  const getXY = (ev) => ev.touches?.length ? { x: ev.touches[0].clientX, y: ev.touches[0].clientY } : { x: ev.clientX, y: ev.clientY };
  const tryStart = (ev) => {
    if (!chart || !candleSeries) return;
    const yRel = getXY(ev).y - el.getBoundingClientRect().top;
    let hit = null, best = 12;
    for (const pl of priceLines) {
      if (!pl.field) continue;
      const py = candleSeries.priceToCoordinate(pl.line.options().price);
      if (py == null) continue;
      const d = Math.abs(py - yRel);
      if (d < best) { hit = pl; best = d; }
    }
    if (hit) { dragState = { active: true, line: hit.line, trade: hit.trade, field: hit.field }; ev.preventDefault(); }
  };
  const doMove = (ev) => {
    if (!dragState.active) return;
    const price = candleSeries.coordinateToPrice(getXY(ev).y - el.getBoundingClientRect().top);
    if (price == null) return;
    const t = dragState.trade, side = t.side || "LONG";
    if (dragState.field === "stop" && ((side === "LONG" && price >= t.entry) || (side === "SHORT" && price <= t.entry))) return;
    if (dragState.field === "tp2" && ((side === "LONG" && price <= t.entry) || (side === "SHORT" && price >= t.entry))) return;
    const mag = Math.pow(10, Math.floor(Math.log10(price)) - 3);
    const snapped = Math.round(price / mag) * mag;
    try { dragState.line.applyOptions({ price: snapped }); } catch(e) {}
    t[dragState.field] = snapped;
    ev.preventDefault();
  };
  const doEnd = () => {
    if (!dragState.active) return;
    const trades = store.getTrades();
    const idx = trades.findIndex(x => x.id === dragState.trade.id);
    if (idx >= 0) {
      const oldV = trades[idx][dragState.field], newV = dragState.trade[dragState.field];
      if (oldV !== newV) {
        trades[idx][dragState.field] = newV;
        trades[idx].adjustments = trades[idx].adjustments || [];
        trades[idx].adjustments.push({ at: Date.now(), field: dragState.field, from: oldV, to: newV });
        store.setTrades(trades);
        toast("BUY", `${dragState.trade.coin} ${dragState.field.toUpperCase()} → ${fmt(newV)}`);
      }
    }
    dragState = { active: false, line: null, trade: null, field: null };
    render();
  };
  el.addEventListener("mousedown", tryStart);
  el.addEventListener("mousemove", doMove);
  window.addEventListener("mouseup", doEnd);
  el.addEventListener("touchstart", tryStart, { passive: false });
  el.addEventListener("touchmove", doMove, { passive: false });
  window.addEventListener("touchend", doEnd);
}

function calcLiq(entry, lev, side) { const f = MAINT_FRAC / lev; return side === "LONG" ? entry * (1 - f) : entry * (1 + f); }
function tradePnl(t, live) { const n = t.notional_usd, e = t.entry; return (t.side || "LONG") === "LONG" ? (live - e) / e * n : (e - live) / e * n; }
function tradeMargin(t) { return t.margin_usd || (t.notional_usd / t.leverage); }

function executeTrade(side) {
  const coin = $("execCoin").value;
  if (!coin) return toast("ERR", "pick a coin");
  const meta = STATE.coins[coin];
  const live = parseFloat(STATE.mids[coin] || 0) || (meta ? meta.price : 0);
  if (!live) return toast("ERR", "no live price");
  const margin = parseFloat($("execSize").value);
  const lev = Math.min(20, Math.max(1, parseFloat($("execLev").value) || 1));
  if (!margin || margin <= 0) return toast("ERR", "enter margin");
  const stopIn = parseFloat($("execStop").value), tpIn = parseFloat($("execTP").value);
  let stop, tp2;
  if (side === "LONG") {
    stop = stopIn || (meta && meta.signal === "BUY" && meta.stop) || live * 0.97;
    tp2 = tpIn || (meta && meta.signal === "BUY" && meta.tp2) || live * 1.03;
    if (stop >= live || tp2 <= live) return toast("ERR", "invalid LONG levels");
  } else {
    stop = stopIn || live * 1.03; tp2 = tpIn || live * 0.97;
    if (stop <= live || tp2 >= live) return toast("ERR", "invalid SHORT levels");
  }
  const trades = store.getTrades();
  trades.push({ id: Date.now() + "-" + Math.random().toString(36).slice(2, 6), coin, side, entry: live, stop, tp1: (live + tp2) / 2, tp2,
    margin_usd: margin, notional_usd: margin * lev, leverage: lev,
    opened_at: Date.now(), closed_at: null, close_price: null, close_reason: null,
    signal_at_open: meta?.signal, confidence_at_open: meta?.confidence, score_at_open: meta?.score, why_at_open: meta?.why, setup_at_open: meta?.setup, adjustments: [] });
  store.setTrades(trades);
  toast(side === "LONG" ? "BUY" : "SELL", `${coin} ${side} $${(margin*lev).toFixed(0)} @ ${fmt(live)}`);
  render();
}

function closeTrade(id, price, reason) {
  const trades = store.getTrades();
  const t = trades.find(x => x.id === id);
  if (!t || t.closed_at) return;
  t.closed_at = Date.now(); t.close_price = price; t.close_reason = reason;
  store.setTrades(trades);
  if (t.auto) localStorage.setItem("auto_last_close_" + t.coin, Date.now().toString());
  toast("SELL", `${t.coin} closed ${reason} @ ${fmt(price)}`);
}
function closeManual(id) {
  const t = store.getTrades().find(x => x.id === id);
  if (!t) return;
  closeTrade(id, parseFloat(STATE.mids[t.coin] || 0) || t.entry, "manual");
  render();
}
function checkAutoClose() {
  const trades = store.getTrades();
  let changed = false;
  for (const t of trades) {
    if (t.closed_at) continue;
    const live = parseFloat(STATE.mids[t.coin] || 0); if (!live) continue;
    const side = t.side || "LONG";
    if (side === "LONG") {
      if (live <= t.stop) { closeTrade(t.id, t.stop, "stop"); changed = true; }
      else if (t.tp2 && live >= t.tp2) { closeTrade(t.id, t.tp2, "tp2"); changed = true; }
    } else {
      if (live >= t.stop) { closeTrade(t.id, t.stop, "stop"); changed = true; }
      else if (t.tp2 && live <= t.tp2) { closeTrade(t.id, t.tp2, "tp2"); changed = true; }
    }
  }
  if (changed) setTimeout(render, 50);
}

function startAuto() {
  const m = parseFloat($("autoMargin").value);
  const l = Math.min(20, Math.max(1, parseFloat($("autoLev").value) || 3));
  if (!m || m <= 0) return toast("ERR", "enter a margin amount");
  localStorage.setItem("auto_margin", m.toString());
  localStorage.setItem("auto_lev", l.toString());
  localStorage.setItem("auto_enabled", "1");
  renderAutoPanel();
  toast("BUY", `🤖 Auto-trading ON · $${m} margin · ${l}x leverage`);
  playBeep();
}
function stopAuto() {
  localStorage.setItem("auto_enabled", "0");
  renderAutoPanel();
  toast("ERR", "Auto-trading OFF — open auto positions remain");
}
function toggleAutoFromHeader() {
  if (localStorage.getItem("auto_enabled") === "1") stopAuto();
  else {
    const panel = $("autoPanel");
    if (panel) panel.scrollIntoView({ behavior: "smooth", block: "start" });
    toast("BUY", "Configure margin/leverage below, then tap Start");
  }
}
function checkAutoTrade() {
  if (localStorage.getItem("auto_enabled") !== "1") return;
  if (STATE.status !== "live") return;
  const margin = parseFloat(localStorage.getItem("auto_margin") || "50");
  const leverage = Math.min(20, Math.max(1, parseFloat(localStorage.getItem("auto_lev") || "3")));
  if (!margin || margin <= 0) return;
  let trades = store.getTrades();
  for (const t of [...trades]) {
    if (t.closed_at || !t.auto) continue;
    const cur = STATE.coins[t.coin];
    if (!cur) continue;
    const confident = cur.confidence === "CERTAIN" || cur.confidence === "CONFIDENT";
    const flip = confident && ((t.side === "LONG" && cur.signal === "SELL") || (t.side === "SHORT" && cur.signal === "BUY"));
    if (flip) {
      const live = parseFloat(STATE.mids[t.coin] || 0) || t.entry;
      closeTrade(t.id, live, "auto_flip");
      toast(cur.signal === "SELL" ? "SELL" : "BUY", `🤖 Auto closed ${t.coin} ${t.side} (flipped to ${cur.signal})`);
    }
  }
  trades = store.getTrades();
  let autoOpenCount = trades.filter(t => !t.closed_at && t.auto).length;
  if (autoOpenCount >= AUTO_MAX_OPEN) return;
  const toOpen = [];
  for (const c of Object.values(STATE.coins)) {
    if (autoOpenCount >= AUTO_MAX_OPEN) break;
    if (!((c.signal === "BUY" || c.signal === "SELL") && (c.confidence === "CERTAIN" || c.confidence === "CONFIDENT"))) continue;
    const already = trades.find(t => !t.closed_at && t.coin === c.coin);
    if (already) continue;
    const lastClose = parseInt(localStorage.getItem("auto_last_close_" + c.coin) || "0");
    if (Date.now() - lastClose < AUTO_COOLDOWN_MS) continue;
    const live = parseFloat(STATE.mids[c.coin] || 0) || c.price;
    if (!live) continue;
    const side = c.signal === "BUY" ? "LONG" : "SHORT";
    let stop, tp2;
    if (side === "LONG") {
      stop = c.stop || live * 0.97;
      tp2 = c.tp2 || live * 1.03;
      if (stop >= live || tp2 <= live) continue;
    } else {
      stop = c.stop || live * 1.03;
      tp2 = c.tp2 || live * 0.97;
      if (stop <= live || tp2 >= live) continue;
    }
    toOpen.push({
      id: Date.now() + "-auto-" + Math.random().toString(36).slice(2, 6),
      coin: c.coin, side, entry: live, stop, tp1: (live + tp2) / 2, tp2,
      margin_usd: margin, notional_usd: margin * leverage, leverage,
      opened_at: Date.now(), closed_at: null, close_price: null, close_reason: null,
      signal_at_open: c.signal, confidence_at_open: c.confidence, score_at_open: c.score,
      why_at_open: c.why, setup_at_open: c.setup, auto: true, adjustments: []
    });
    autoOpenCount++;
  }
  if (toOpen.length) {
    trades.push(...toOpen);
    store.setTrades(trades);
    for (const t of toOpen) {
      toast(t.side === "LONG" ? "BUY" : "SELL", `🤖 Auto opened ${t.coin} ${t.side} $${(margin * leverage).toFixed(0)} @ ${fmt(t.entry)}`);
    }
    playBeep();
    if (("Notification" in window) && Notification.permission === "granted") {
      for (const t of toOpen) {
        fireNotification(`🤖 Auto ${t.side === "LONG" ? "BUY" : "SELL"} ${t.coin}`, {
          body: `${t.confidence_at_open} · entry ${fmt(t.entry)} · stop ${fmt(t.stop)} · TP2 ${fmt(t.tp2)}`,
          tag: `auto-${t.coin}`
        });
      }
    }
  }
}
function renderAutoPanel() {
  const enabled = localStorage.getItem("auto_enabled") === "1";
  const cfg = $("autoConfig"), run = $("autoRunning"), hdr = $("autoBtn");
  if (!cfg || !run) return;
  if (enabled) {
    cfg.style.display = "none";
    run.style.display = "block";
    if (hdr) { hdr.textContent = "🤖 ON"; hdr.style.background = "var(--buy)"; hdr.style.color = "#fff"; hdr.style.borderColor = "var(--buy)"; }
    const autoTrades = store.getTrades().filter(t => t.auto);
    const autoOpen = autoTrades.filter(t => !t.closed_at);
    const autoClosed = autoTrades.filter(t => t.closed_at);
    if (autoOpen.length) {
      $("autoLivePositions").innerHTML = `<div class="mu" style="font-size:11px;text-transform:uppercase;margin-bottom:6px">Open auto positions (${autoOpen.length}/${AUTO_MAX_OPEN})</div>` +
        autoOpen.map(t => {
          const live = parseFloat(STATE.mids[t.coin] || 0) || t.entry;
          const pnl = tradePnl(t, live);
          const roe = tradeMargin(t) > 0 ? pnl / tradeMargin(t) * 100 : 0;
          return `<div style="padding:8px 0;border-bottom:1px solid var(--bd);font-size:12px">
            <b>${esc(t.coin)}</b> <span class="badge ${t.side}">${t.side}</span> ${t.leverage}x<br>
            <span class="mu">entry ${fmt(t.entry)} · now ${fmt(live)} · stop ${fmt(t.stop)} · TP2 ${fmt(t.tp2)}</span><br>
            <span class="${pnl>=0?'up':'dn'}" style="font-weight:700">P/L $${pnl.toFixed(2)} (${roe.toFixed(1)}% ROE)</span>
          </div>`;
        }).join("");
    } else {
      $("autoLivePositions").innerHTML = `<div class="mu">No open auto positions. The bot will open when it sees a CERTAIN or CONFIDENT signal.</div>`;
    }
    if (autoClosed.length) {
      const stats = computeStats(autoClosed);
      if (stats) {
        $("autoStatsBox").innerHTML = `<div class="mu" style="font-size:11px;text-transform:uppercase;margin-bottom:6px">Auto-trade performance (${autoClosed.length} closed)</div>
          <div class="stat-grid">
            <div class="stat-box"><div class="k">Trades</div><div class="v">${stats.trades}</div></div>
            <div class="stat-box"><div class="k">Win rate</div><div class="v ${stats.winRate>=50?'up':'dn'}">${stats.winRate.toFixed(1)}%</div></div>
            <div class="stat-box"><div class="k">Net P/L</div><div class="v ${stats.net>=0?'up':'dn'}">$${fmt2(stats.net)}</div></div>
            <div class="stat-box"><div class="k">Profit factor</div><div class="v ${stats.pf>=1?'up':'dn'}">${isFinite(stats.pf)?stats.pf.toFixed(2):"∞"}</div></div>
            <div class="stat-box"><div class="k">W/L</div><div class="v">${stats.wins}/${stats.losses}</div></div>
            <div class="stat-box"><div class="k">Avg hold</div><div class="v">${(stats.avgHoldMs/3600000).toFixed(1)}h</div></div>
          </div>`;
      }
    } else {
      $("autoStatsBox").innerHTML = `<div class="mu">No closed auto trades yet.</div>`;
    }
  } else {
    cfg.style.display = "block";
    run.style.display = "none";
    if (hdr) { hdr.textContent = "🤖 OFF"; hdr.style.background = ""; hdr.style.color = ""; hdr.style.borderColor = ""; }
    if (!$("autoMargin").value) $("autoMargin").value = localStorage.getItem("auto_margin") || "50";
    if (!$("autoLev").value) $("autoLev").value = localStorage.getItem("auto_lev") || "3";
  }
}

function clearAllTrades() {
  if (!confirm("Clear all paper trades?")) return;
  store.setTrades([]); toast("ERR", "Cleared"); render();
}

function showTradeDetail(id) {
  const t = store.getTrades().find(x => x.id === id); if (!t) return;
  const live = parseFloat(STATE.mids[t.coin] || 0) || t.entry;
  const side = t.side || "LONG", margin = tradeMargin(t), notional = t.notional_usd;
  const pnl = tradePnl(t, live), roe = margin > 0 ? pnl / margin * 100 : 0;
  const liq = calcLiq(t.entry, t.leverage, side), distLiq = Math.abs(live - liq) / live * 100;
  const openH = (Date.now() - t.opened_at) / 3600000;
  const riskUsd = side === "LONG" ? (t.entry - t.stop) / t.entry * notional : (t.stop - t.entry) / t.entry * notional;
  const rewardUsd = side === "LONG" ? (t.tp2 - t.entry) / t.entry * notional : (t.entry - t.tp2) / t.entry * notional;
  let html = `<h3 style="margin:0 0 6px">${esc(t.coin)} <span class="badge ${side}">${side}</span>${t.auto ? ' <span class="badge" style="background:#8b93a1">🤖 AUTO</span>' : ''}</h3>
    <div class="mu" style="margin-bottom:8px">${t.leverage}x · ${openH < 1 ? (openH*60).toFixed(0)+"m" : openH.toFixed(1)+"h"} open</div>
    <div class="detail-grid">
      <div><span class="k">Margin</span><span>$${margin.toFixed(2)}</span></div>
      <div><span class="k">Size</span><span>$${notional.toFixed(2)}</span></div>
      <div><span class="k">Entry</span><span>${fmt(t.entry)}</span></div>
      <div><span class="k">Now</span><span>${fmt(live)}</span></div>
      <div><span class="k">Liquidation</span><span class="dn">${fmt(liq)}</span></div>
      <div><span class="k">From liq</span><span>${distLiq.toFixed(2)}%</span></div>
      <div><span class="k">Risk $</span><span class="dn">$${riskUsd.toFixed(2)}</span></div>
      <div><span class="k">Reward $</span><span class="up">$${rewardUsd.toFixed(2)}</span></div>
      <div><span class="k">P/L</span><span class="${pnl>=0?'up':'dn'}">$${pnl.toFixed(2)}</span></div>
      <div><span class="k">ROE</span><span class="${pnl>=0?'up':'dn'}">${roe.toFixed(1)}%</span></div>
    </div>
    <div style="margin-top:14px;padding:10px;background:var(--card2);border-radius:8px">
      <div class="mu" style="font-size:11px;text-transform:uppercase;margin-bottom:6px">Adjust stop / TP</div>
      <div class="exec-row"><label>Stop</label><input id="editStop" type="number" step="any" value="${t.stop}" style="flex:1"></div>
      <div class="exec-row"><label>TP2</label><input id="editTP2" type="number" step="any" value="${t.tp2}" style="flex:1"></div>
      <button class="btn-ghost" style="width:100%;margin-top:6px" onclick="applyEdits('${t.id}')">Apply</button>
    </div>`;
  if (t.signal_at_open) {
    html += `<div style="margin-top:14px;padding:10px;background:var(--card2);border-radius:8px">
      <div class="mu" style="font-size:11px;text-transform:uppercase;margin-bottom:6px">Signal when opened</div>
      <div style="margin-bottom:6px"><span class="badge ${t.signal_at_open}">${t.signal_at_open}</span>
        <span class="badge ${t.confidence_at_open||'LOW'}">${t.confidence_at_open||'—'}</span></div>
      <div class="mu" style="line-height:1.55">${esc(t.why_at_open||"")}</div>
    </div>`;
  }
  html += `<div style="display:flex;gap:8px;margin-top:14px">
    <button style="flex:1;padding:12px;background:var(--sell);color:#fff;border:0;border-radius:8px;font-weight:700;font-family:inherit;cursor:pointer" onclick="closeManual('${t.id}');closeModal()">Close</button>
    <button style="flex:1;padding:12px;background:var(--bd);color:var(--tx);border:0;border-radius:8px;font-weight:700;font-family:inherit;cursor:pointer" onclick="closeModal()">Dismiss</button>
  </div>`;
  $("modalContent").innerHTML = html;
  $("modal").classList.add("open");
}
function applyEdits(id) {
  const trades = store.getTrades(), t = trades.find(x => x.id === id); if (!t) return;
  const ns = parseFloat($("editStop").value), nt = parseFloat($("editTP2").value);
  const side = t.side || "LONG", errs = [];
  if (!ns || (side === "LONG" && ns >= t.entry) || (side === "SHORT" && ns <= t.entry)) errs.push("bad stop");
  if (!nt || (side === "LONG" && nt <= t.entry) || (side === "SHORT" && nt >= t.entry)) errs.push("bad TP");
  if (errs.length) return toast("ERR", errs.join(", "));
  if (ns !== t.stop) { t.adjustments = t.adjustments || []; t.adjustments.push({at:Date.now(),field:"stop",from:t.stop,to:ns}); t.stop = ns; }
  if (nt !== t.tp2) { t.adjustments = t.adjustments || []; t.adjustments.push({at:Date.now(),field:"tp2",from:t.tp2,to:nt}); t.tp2 = nt; }
  store.setTrades(trades); closeModal(); toast("BUY", `${t.coin} updated`); render();
}
function closeModal() { $("modal").classList.remove("open"); }

function computeStats(trades) {
  if (!trades.length) return null;
  const e = trades.map(t => {
    const side = t.side || "LONG", m = tradeMargin(t), n = t.notional_usd;
    const pnl = side === "LONG" ? (t.close_price - t.entry) / t.entry * n : (t.entry - t.close_price) / t.entry * n;
    return { ...t, side, pnl, margin: m, notional: n, holdMs: (t.closed_at || 0) - (t.opened_at || 0) };
  });
  const wins = e.filter(t => t.pnl > 0), losses = e.filter(t => t.pnl <= 0);
  const gw = wins.reduce((s, t) => s + t.pnl, 0), gl = losses.reduce((s, t) => s + Math.abs(t.pnl), 0);
  const net = gw - gl;
  const pf = gl > 0 ? gw / gl : (gw > 0 ? Infinity : 0);
  const wr = e.length > 0 ? wins.length / e.length * 100 : 0;
  const sorted = [...e].sort((a, b) => a.closed_at - b.closed_at);
  let cum = 0;
  const curve = sorted.map(t => { cum += t.pnl; return { t: t.closed_at, v: cum }; });
  let peak = 0, dd = 0;
  for (const p of curve) { if (p.v > peak) peak = p.v; const d = peak - p.v; if (d > dd) dd = d; }
  const rev = [...sorted].reverse();
  let streak = 0, st = null;
  for (const t of rev) { const ty = t.pnl > 0 ? "win" : "loss"; if (st === null) { st = ty; streak = 1; } else if (st === ty) streak++; else break; }
  const longs = e.filter(t => t.side === "LONG"), shorts = e.filter(t => t.side === "SHORT");
  const cert = e.filter(t => t.confidence_at_open === "CERTAIN"), conf = e.filter(t => t.confidence_at_open === "CONFIDENT");
  const pulls = e.filter(t => t.setup_at_open === "PULLBACK"), brks = e.filter(t => t.setup_at_open === "BREAKOUT");
  const tier = a => ({ count: a.length, winRate: a.length ? a.filter(t => t.pnl > 0).length / a.length * 100 : 0, net: a.reduce((s, t) => s + t.pnl, 0) });
  let vClass = "ok", vTitle = "TOO FEW TRADES", vMsg = "";
  if (e.length < 10) { vMsg = `Only ${e.length} closed trade${e.length===1?"":"s"}. Need 10+ for meaningful stats.`; }
  else if (pf >= 1.5 && wr >= 45 && net > 0) { vClass = "good"; vTitle = "GOOD"; vMsg = "Profitable. The rules are working."; }
  else if (pf >= 1.0 && net > 0) { vTitle = "OK"; vMsg = "Slightly profitable. Consider only CERTAIN signals."; }
  else { vClass = "bad"; vTitle = "NEEDS WORK"; vMsg = "Losing money. Review entries."; }
  return { trades: e.length, wins: wins.length, losses: losses.length, winRate: wr, net, pf,
    avgWin: wins.length ? gw / wins.length : 0, avgLoss: losses.length ? gl / losses.length : 0,
    best: Math.max(...e.map(t => t.pnl)), worst: Math.min(...e.map(t => t.pnl)),
    maxDD: dd, streak, streakType: st, curve, avgHoldMs: e.reduce((s, t) => s + t.holdMs, 0) / e.length,
    longCount: longs.length, shortCount: shorts.length,
    longWins: longs.filter(t => t.pnl > 0).length, shortWins: shorts.filter(t => t.pnl > 0).length,
    longNet: longs.reduce((s, t) => s + t.pnl, 0), shortNet: shorts.reduce((s, t) => s + t.pnl, 0),
    certain: tier(cert), confident: tier(conf), pullback: tier(pulls), breakout: tier(brks),
    vClass, vTitle, vMsg };
}

function svgCurve(curve, w, h) {
  if (!curve || curve.length < 2) return "";
  const vals = curve.map(p => p.v);
  const min = Math.min(...vals, 0), max = Math.max(...vals, 0), range = max - min || 1;
  const pad = 4, iw = w - pad * 2, ih = h - pad * 2, xs = iw / (vals.length - 1);
  const pts = vals.map((v, i) => `${pad + i * xs},${pad + ih - ((v - min) / range) * ih}`).join(" ");
  const color = vals[vals.length-1] >= 0 ? "#2ecc83" : "#ff5d68";
  const zy = pad + ih - ((0 - min) / range) * ih;
  return `<svg viewBox="0 0 ${w} ${h}" preserveAspectRatio="none"><line x1="${pad}" y1="${zy}" x2="${w-pad}" y2="${zy}" stroke="#262c38" stroke-width="1" stroke-dasharray="2,3"/><polyline points="${pts}" fill="none" stroke="${color}" stroke-width="2" vector-effect="non-scaling-stroke"/><circle cx="${pad+(vals.length-1)*xs}" cy="${pad+ih-((vals[vals.length-1]-min)/range)*ih}" r="3.5" fill="${color}"/></svg>`;
}

async function runBacktestOne(coin, days, margin, leverage) {
  const meta = STATE.coins[coin] || {};
  const raw = coin.includes(":") ? coin.split(":")[1] : coin;
  const dex = meta.dex || "";
  const warm = 320, bars = Math.floor(days * 24 * 60 / 5), total = warm + bars;
  const c5 = await fetchCandles(raw, "5m", total, dex);
  const c1h = await fetchCandles(raw, "1h", Math.ceil(total/12) + 50, dex);
  const c4h = await fetchCandles(raw, "4h", Math.ceil(total/48) + 50, dex);
  const c1d = await fetchCandles(raw, "1d", Math.ceil(total/288) + 50, dex);
  if (c5.length < warm + 10) throw new Error("not enough history");
  const trades = []; let open = null;
  for (let i = warm; i < c5.length - 1; i++) {
    const bar = c5[i], tClose = bar.t + IV_MS["5m"];
    const s5 = c5.slice(0, i + 1), s1h = c1h.filter(x => x.T <= tClose), s4h = c4h.filter(x => x.T <= tClose), s1d = c1d.filter(x => x.T <= tClose);
    if (!s1h.length || !s4h.length) continue;
    const cbt = { "5m": s5, "1h": s1h, "4h": s4h, "1d": s1d };
    if (s5.length >= 30) {
      const m15 = [];
      for (let j = 0; j + 2 < s5.length; j += 3) m15.push({ t: s5[j].t, T: s5[j+2].T, o: s5[j].o, h: Math.max(s5[j].h,s5[j+1].h,s5[j+2].h), l: Math.min(s5[j].l,s5[j+1].l,s5[j+2].l), c: s5[j+2].c, v: s5[j].v+s5[j+1].v+s5[j+2].v });
      cbt["15m"] = m15;
    }
    const sig = signalFrom(cbt, bar.c);
    if (sig && (sig.signal === "BUY" || sig.signal === "SELL") && (sig.confidence === "CERTAIN" || sig.confidence === "CONFIDENT") && !open) {
      const nb = c5[i + 1]; if (!nb) break;
      const side = sig.signal === "BUY" ? "LONG" : "SHORT";
      open = { id: i, coin, side, entry: nb.o, stop: sig.stop || nb.o * (side === "LONG" ? 0.97 : 1.03), tp2: sig.tp2 || nb.o * (side === "LONG" ? 1.03 : 0.97), opened_at: nb.t,
        margin_usd: margin, notional_usd: margin * leverage, leverage, confidence_at_open: sig.confidence, setup_at_open: sig.setup, closed_at: null, close_price: null, close_reason: null };
    }
    if (open) {
      const sHit = open.side === "LONG" ? bar.l <= open.stop : bar.h >= open.stop;
      const tHit = open.side === "LONG" ? bar.h >= open.tp2 : bar.l <= open.tp2;
      if (sHit) { open.closed_at = bar.t; open.close_price = open.stop; open.close_reason = "stop"; trades.push(open); open = null; }
      else if (tHit) { open.closed_at = bar.t; open.close_price = open.tp2; open.close_reason = "tp2"; trades.push(open); open = null; }
    }
  }
  if (open) { open.closed_at = c5[c5.length-1].T; open.close_price = c5[c5.length-1].c; open.close_reason = "end"; trades.push(open); }
  return { coin, windowDays: days, stats: computeStats(trades), trades };
}

function renderBacktestResult(r) {
  const el = $("btResults");
  if (!r) { el.innerHTML = ""; return; }
  const s = r.stats;
  if (!s) { el.innerHTML = `<div class="mu">No signals in the ${r.windowDays}-day window. That's the strict gates doing their job.</div>`; return; }
  let warn = "";
  if (s.trades < 20) warn = `<div class="mu" style="color:var(--wait);font-weight:700;margin-bottom:8px">⚠ Too few trades — not statistically meaningful yet</div>`;
  el.innerHTML = `${warn}
    <div class="mu" style="font-size:11px;padding:8px;background:var(--card2);border-radius:6px;margin-bottom:10px;line-height:1.5"><b>Not modeled:</b> slippage, fees, funding, liquidity. Past performance ≠ future results.</div>
    <div class="stat-grid">
      <div class="stat-box"><div class="k">Trades</div><div class="v">${s.trades}</div></div>
      <div class="stat-box"><div class="k">Win rate</div><div class="v ${s.winRate>=50?'up':'dn'}">${s.winRate.toFixed(1)}%</div></div>
      <div class="stat-box"><div class="k">Net P/L</div><div class="v ${s.net>=0?'up':'dn'}">$${fmt2(s.net)}</div></div>
      <div class="stat-box"><div class="k">Profit factor</div><div class="v ${s.pf>=1?'up':'dn'}">${isFinite(s.pf)?s.pf.toFixed(2):"∞"}</div></div>
      <div class="stat-box"><div class="k">Best</div><div class="v up">$${fmt2(s.best)}</div></div>
      <div class="stat-box"><div class="k">Worst</div><div class="v dn">$${fmt2(s.worst)}</div></div>
      <div class="stat-box"><div class="k">Max DD</div><div class="v dn">$${fmt2(s.maxDD)}</div></div>
      <div class="stat-box"><div class="k">W/L</div><div class="v">${s.wins}/${s.losses}</div></div>
    </div>
    <div style="margin-top:10px">${svgCurve(s.curve, 600, 100)}</div>
    <div class="side-row">
      <div class="side-box"><b>CERTAIN</b><br>${s.certain.count} · ${s.certain.winRate.toFixed(0)}% win<br><span class="${s.certain.net>=0?'up':'dn'}">$${fmt2(s.certain.net)}</span></div>
      <div class="side-box"><b>CONFIDENT</b><br>${s.confident.count} · ${s.confident.winRate.toFixed(0)}% win<br><span class="${s.confident.net>=0?'up':'dn'}">$${fmt2(s.confident.net)}</span></div>
    </div>`;
}

async function runBacktest() {
  const coin = $("btCoin").value;
  if (!coin) return toast("ERR", "pick an asset");
  const days = parseInt($("btWindow").value), margin = parseFloat($("btMargin").value), leverage = Math.min(20, Math.max(1, parseFloat($("btLev").value) || 3));
  $("btProgress").style.display = "block"; $("btProgressText").textContent = `Running ${coin}...`; $("btResults").innerHTML = "";
  try {
    const r = await runBacktestOne(coin, days, margin, leverage);
    store.setBtLast(r); renderBacktestResult(r);
    toast("BUY", `Backtest done: ${r.stats ? r.stats.trades + " trades" : "no signals"}`);
  } catch(e) { toast("ERR", e.message); }
  finally { $("btProgress").style.display = "none"; }
}

function toggleBacktest() {
  const b = $("backtestBody"), t = $("backtestToggle");
  const hidden = b.style.display === "none";
  b.style.display = hidden ? "block" : "none";
  t.textContent = hidden ? "▲" : "▼";
}

let swReg = null;
if ("serviceWorker" in navigator) navigator.serviceWorker.register("sw.js").then(() => navigator.serviceWorker.ready.then(r => { swReg = r; })).catch(() => {});
function requestNotifPerm() {
  if (!("Notification" in window)) return toast("ERR", "not supported");
  Notification.requestPermission().then(p => {
    if (p === "granted") { toast("BUY", "Alerts on"); $("notifBtn").textContent = "🔔 On"; }
    else toast("ERR", "Denied — enable in browser settings");
  });
}
if ("Notification" in window) {
  if (Notification.permission === "granted") { $("notifBtn").textContent = "🔔 On"; }
  else if (Notification.permission === "denied") { $("notifBtn").textContent = "🔕 Blocked"; }
  else { $("notifBtn").textContent = "🔔 Alerts"; }
} else { $("notifBtn").textContent = "🔕 N/A"; $("notifBtn").disabled = true; }

function fireNotification(title, opts) {
  try { if (swReg?.showNotification) swReg.showNotification(title, opts); else if (Notification.permission === "granted") new Notification(title, opts); } catch(e) {}
}

let audioCtx = null;
function toggleSound() {
  const on = localStorage.getItem("sound_on") === "1";
  localStorage.setItem("sound_on", on ? "0" : "1");
  updateSoundBtn();
  toast(on ? "ERR" : "BUY", on ? "Sound alerts OFF" : "Sound alerts ON");
}
function updateSoundBtn() {
  const on = localStorage.getItem("sound_on") === "1";
  const b = $("soundBtn");
  if (b) b.textContent = on ? "🔊" : "🔇";
}
function playBeep() {
  if (localStorage.getItem("sound_on") !== "1") return;
  try {
    if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    if (audioCtx.state === "suspended") audioCtx.resume();
    const osc = audioCtx.createOscillator();
    const gain = audioCtx.createGain();
    osc.connect(gain); gain.connect(audioCtx.destination);
    osc.frequency.value = 880;
    gain.gain.setValueAtTime(0.15, audioCtx.currentTime);
    gain.gain.exponentialRampToValueAtTime(0.001, audioCtx.currentTime + 0.3);
    osc.start(); osc.stop(audioCtx.currentTime + 0.35);
  } catch(e) {}
}

function applyTheme() {
  const pref = localStorage.getItem("theme_pref") || "auto";
  let theme = pref;
  if (pref === "auto") theme = window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
  document.documentElement.setAttribute("data-theme", theme);
  const btn = $("themeBtn");
  if (btn) {
    btn.textContent = pref === "auto" ? "⚙️" : (pref === "light" ? "☀️" : "🌙");
    btn.title = `Theme: ${pref === "auto" ? "follows device" : pref}`;
  }
  if (chart) {
    const card = getComputedStyle(document.documentElement).getPropertyValue("--card").trim() || "#171b24";
    const tx = getComputedStyle(document.documentElement).getPropertyValue("--tx").trim() || "#e8ebf2";
    const bd = getComputedStyle(document.documentElement).getPropertyValue("--bd").trim() || "#262c38";
    chart.applyOptions({
      layout: { background: { color: card }, textColor: tx },
      grid: { vertLines: { color: bd }, horzLines: { color: bd } },
      timeScale: { borderColor: bd },
      rightPriceScale: { borderColor: bd }
    });
  }
}
function cycleTheme() {
  const cur = localStorage.getItem("theme_pref") || "auto";
  const next = cur === "auto" ? "light" : (cur === "light" ? "dark" : "auto");
  localStorage.setItem("theme_pref", next);
  applyTheme();
  toast("BUY", `Theme: ${next === "auto" ? "auto (device)" : next}`);
}
window.matchMedia("(prefers-color-scheme: dark)").addEventListener("change", () => {
  if ((localStorage.getItem("theme_pref") || "auto") === "auto") applyTheme();
});

function toggleStats() {
  const b = $("statsBody"), t = $("statsToggle");
  const hidden = b.style.display === "none";
  b.style.display = hidden ? "block" : "none";
  t.textContent = hidden ? "▼" : "▲";
  localStorage.setItem("stats_folded", hidden ? "0" : "1");
}

function copyTradeDetails(coin) {
  const c = STATE.coins[coin];
  if (!c || c.signal !== "BUY") return toast("ERR", "No BUY signal to copy");
  const text = `${coin} LONG\nEntry: $${fmt(c.entry)}\nStop: $${fmt(c.stop)}\nTP1: $${fmt(c.tp1)}\nTP2: $${fmt(c.tp2)}\nConfidence: ${c.confidence}\nScore: ${c.score}`;
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(text).then(() => toast("BUY", "Trade details copied to clipboard"));
  } else {
    const ta = document.createElement("textarea");
    ta.value = text;
    document.body.appendChild(ta);
    ta.select();
    document.execCommand("copy");
    document.body.removeChild(ta);
    toast("BUY", "Trade details copied to clipboard");
  }
}

let signalsInit = false;
function checkSignalTransitions(coins) {
  const last = store.getLastSignals(), lastC = store.getLastConf();
  if (!signalsInit) { for (const c of coins) { last[c.coin] = c.signal; lastC[c.coin] = c.confidence; } store.setLastSignals(last); store.setLastConf(lastC); signalsInit = true; return; }
  const can = ("Notification" in window) && Notification.permission === "granted";
  const hist = store.getHistory();
  for (const c of coins) {
    const p = last[c.coin], pc = lastC[c.coin];
    if (p && p !== c.signal) {
      if (!hist[c.coin]) hist[c.coin] = [];
      hist[c.coin].unshift({ ts: Date.now(), from: p, to: c.signal, price: c.price, conf: c.confidence });
      if (hist[c.coin].length > 10) hist[c.coin].length = 10;
      if (can && c.signal === "BUY") {
        fireNotification(`🟢 BUY ${c.coin}`, { body: `${c.confidence} · entry ${fmt(c.entry)} · stop ${fmt(c.stop)} · TP2 ${fmt(c.tp2)}`, tag: `b-${c.coin}` });
        playBeep();
      } else if (can && c.signal === "SELL") {
        fireNotification(`🔴 SELL ${c.coin}`, { body: `${c.confidence} · score ${c.score}`, tag: `s-${c.coin}` });
        playBeep();
      }
    } else if (can && p === "BUY" && pc === "CONFIDENT" && c.confidence === "CERTAIN") {
      fireNotification(`⬆️ ${c.coin} now CERTAIN`, { body: "Confidence upgraded", tag: `u-${c.coin}` });
      playBeep();
    }
    last[c.coin] = c.signal; lastC[c.coin] = c.confidence;
  }
  store.setLastSignals(last); store.setLastConf(lastC); store.setHistory(hist);
}

function toast(kind, msg) {
  const d = document.createElement("div"); d.className = "t " + kind;
  d.innerHTML = "<b>" + esc(kind) + "</b> " + esc(msg);
  $("toast").appendChild(d);
  setTimeout(() => { d.style.opacity = 0; setTimeout(() => d.remove(), 300); }, 5000);
}

function renderTfTabs() { $("tfTabs").innerHTML = Object.keys(IV_MS).map(iv => `<button class="${iv===currentIv?"on":""}" onclick="switchIv('${iv}')">${iv}</button>`).join(""); }
function switchIv(iv) { currentIv = iv; renderTfTabs(); loadCandles(currentCoin, currentIv); }

function renderAssetTabs() {
  const c = { ALL: 0, CRYPTO: 0, STOCK: 0, COMMODITY: 0 };
  for (const x of Object.values(STATE.coins)) { c.ALL++; if (c[x.assetClass] != null) c[x.assetClass]++; }
  $("assetTabs").innerHTML = [
    { id: "ALL", label: `All (${c.ALL})` },
    { id: "CRYPTO", label: `Crypto (${c.CRYPTO})` },
    { id: "STOCK", label: `Stocks (${c.STOCK})` },
    { id: "COMMODITY", label: `Commodities (${c.COMMODITY})` }
  ].map(t => `<button class="${assetFilter===t.id?'on':''}" onclick="setAssetFilter('${t.id}')">${t.label}</button>`).join("");
}
function setAssetFilter(f) { assetFilter = f; renderAssetTabs(); renderWatchlist(); }

function refreshCoinSelects() {
  const coins = STATE.watchlist.map(c => STATE.coins[c]).filter(Boolean);
  const html = coins.map(c => `<option value="${esc(c.coin)}">${esc(c.coin)} — ${c.signal} (${c.score||0})</option>`).join("");
  const sel = $("execCoin"), cur = sel.value || currentCoin || "";
  if (sel.innerHTML !== html) { sel.innerHTML = html; if (Array.from(sel.options).some(o => o.value === cur)) sel.value = cur; else if (coins.length) sel.value = coins[0].coin; }
  const bt = $("btCoin"), curB = bt.value || currentCoin || "";
  if (bt.innerHTML !== html) { bt.innerHTML = html; if (Array.from(bt.options).some(o => o.value === curB)) bt.value = curB; else if (coins.length) bt.value = coins[0].coin; }
}

function updateExecPreview() {
  const m = parseFloat($("execSize").value) || 0;
  const l = Math.min(20, Math.max(1, parseFloat($("execLev").value) || 1));
  $("notionalPreview").textContent = `Notional: $${(m*l).toFixed(2)} (${l}x)`;
  const coin = $("execCoin").value;
  const live = parseFloat(STATE.mids[coin] || 0) || (STATE.coins[coin]?.price || 0);
  if (live > 0) $("liqPreview").textContent = `Liq: LONG ${fmt(calcLiq(live, l, "LONG"))} · SHORT ${fmt(calcLiq(live, l, "SHORT"))}`;
  else $("liqPreview").textContent = "—";
}

function renderSignalCard(c) {
  const el = $("signalCard");
  const live = parseFloat(STATE.mids[c.coin] || 0) || c.price;
  const sig = c.signal;
  let actClass, icon, headline;
  if (sig === "BUY") { actClass = "act-buy"; icon = "🟢"; headline = "BUY NOW"; }
  else if (sig === "SELL") { actClass = "act-sell"; icon = "🔴"; headline = "SELL NOW / STAY OUT"; }
  else if (sig === "WAIT") { actClass = "act-wait"; icon = "🟡"; headline = "DON'T BUY YET — WAIT"; }
  else { actClass = "act-neutral"; icon = "⚪"; headline = "NO ACTION — WAIT"; }
  let priceBlock = "";
  const pct = (t) => ((t - live) / live * 100).toFixed(2);
  if (sig === "BUY" && c.entry) {
    priceBlock = `<div class="action-price">Buy at $${fmt(c.entry)}</div>
      <div class="action-levels">
        <div><div class="lbl">Stop loss (auto-close)</div><div class="val dn">$${fmt(c.stop)} (${pct(c.stop)}%)</div></div>
        <div><div class="lbl">Take profit 1</div><div class="val up">$${fmt(c.tp1)} (+${pct(c.tp1)}%)</div></div>
        <div><div class="lbl">Take profit 2</div><div class="val up">$${fmt(c.tp2)} (+${pct(c.tp2)}%)</div></div>
        <div><div class="lbl">Current price</div><div class="val">$${fmt(live)}</div></div>
      </div>
      <div class="action-instruction">You make money if price rises toward TP1 or TP2. You are closed with a loss if price drops to the stop loss.</div>`;
  } else if (sig === "SELL") {
    priceBlock = `<div class="action-price">$${fmt(live)}</div>
      <div class="action-levels">
        <div><div class="lbl">Action</div><div class="val dn">Sell / stay out</div></div>
        <div><div class="lbl">Do not buy above</div><div class="val">$${fmt(live * 1.01)}</div></div>
      </div>`;
  } else if (sig === "WAIT" && c.entryZone) {
    const dist = ((c.entryZone - live) / live * 100).toFixed(2);
    const dir = dist < 0 ? "lower" : "higher";
    priceBlock = `<div class="action-price">Wait for $${fmt(c.entryZone)}</div>
      <div class="action-levels">
        <div><div class="lbl">Current price</div><div class="val">$${fmt(live)}</div></div>
        <div><div class="lbl">Wait for</div><div class="val">$${fmt(c.entryZone)} (${Math.abs(dist)}% ${dir})</div></div>
      </div>
      <div class="action-instruction">Watch the price. When it reaches $${fmt(c.entryZone)}, the bot may flip to BUY and this becomes a real entry.</div>`;
  } else {
    priceBlock = `<div class="action-price">$${fmt(live)}</div>
      <div class="action-levels">
        <div><div class="lbl">Position</div><div class="val">No trade</div></div>
        <div><div class="lbl">Wait for</div><div class="val">Clear signal</div></div>
      </div>`;
  }
  let reasonsBlock = "";
  if (c.why) {
    reasonsBlock = `<div class="action-instruction" style="margin-top:14px;padding-top:12px;border-top:1px solid var(--bd)"><b style="color:var(--tx)">Why the bot thinks this:</b><br>${esc(c.why)}</div>`;
  }
  let copyBtn = "";
  if (sig === "BUY") {
    copyBtn = `<button class="action-copy" onclick="copyTradeDetails('${esc(c.coin)}')">📋 Copy trade details</button>`;
  }
  const openPos = store.getTrades().find(t => !t.closed_at && t.coin === c.coin);
  let closeBtn = "";
  if (openPos) {
    const side = openPos.side || "LONG";
    closeBtn = `<button class="action-copy" style="margin-top:8px;background:var(--sell);color:#fff;border-color:var(--sell)" onclick="closeManual('${openPos.id}')">Close my ${side} position</button>`;
  }
  let historyBlock = "";
  const hist = store.getHistory()[c.coin] || [];
  if (hist.length) {
    historyBlock = `<div style="margin-top:14px;padding-top:12px;border-top:1px solid var(--bd)">
      <div class="mu" style="font-size:11px;text-transform:uppercase;letter-spacing:.04em;margin-bottom:6px">Recent signal changes</div>
      ${hist.slice(0,5).map(h => {
        const ago = Math.round((Date.now() - h.ts) / 60000);
        const agoStr = ago < 1 ? "just now" : (ago < 60 ? ago + "m ago" : Math.round(ago/60) + "h ago");
        return `<div style="font-size:12px;padding:3px 0;color:var(--mu)">${agoStr}: ${h.from} → <b style="color:var(--tx)">${h.to}</b> @ $${fmt(h.price)}</div>`;
      }).join("")}
    </div>`;
  }
  el.className = `card action-card ${actClass}`;
  el.innerHTML = `<div class="action-title">${icon} ${headline}</div>${priceBlock}${reasonsBlock}${copyBtn}${closeBtn}${historyBlock}`;
}

function renderPositions() {
  const open = store.getTrades().filter(t => !t.closed_at);
  const el = $("positions");
  if (!open.length) { el.innerHTML = `<div class="mu">No open positions.</div>`; return; }
  el.innerHTML = open.map(t => {
    const live = parseFloat(STATE.mids[t.coin] || 0) || t.entry;
    const side = t.side || "LONG", m = tradeMargin(t), n = t.notional_usd, pnl = tradePnl(t, live);
    const roe = m > 0 ? pnl / m * 100 : 0, liq = calcLiq(t.entry, t.leverage, side), dl = Math.abs(live - liq) / live * 100;
    return `<div class="pos-item" onclick="showTradeDetail('${t.id}')"><div><b>${esc(t.coin)}${t.auto ? ' 🤖' : ''}</b> <span class="badge ${side}">${side}</span> ${t.leverage}x · <span class="mu">$${n.toFixed(0)}</span><br><span class="mu">entry ${fmt(t.entry)} · now ${fmt(live)} · stop ${fmt(t.stop)} · TP2 ${fmt(t.tp2)}</span><br><span class="mu">liq ${fmt(liq)} (${dl.toFixed(1)}%)</span><br><span class="${pnl>=0?'up':'dn'}" style="font-weight:700">P/L $${pnl.toFixed(2)} (${roe.toFixed(1)}% ROE)</span></div><button class="x" onclick="event.stopPropagation();closeManual('${t.id}')">Close</button></div>`;
  }).join("");
}

function renderStats() {
  const closed = store.getTrades().filter(t => t.closed_at);
  const s = computeStats(closed);
  const el = $("statsWrap");
  if (!s) { el.innerHTML = `<div class="mu">No closed trades yet.</div>`; return; }
  el.innerHTML = `<div id="verdictWrap" class="${s.vClass}"><div id="verdictTitle">${esc(s.vTitle)}</div><div id="verdictMsg">${esc(s.vMsg)}</div></div>
    <div class="stat-grid">
      <div class="stat-box"><div class="k">Trades</div><div class="v">${s.trades}</div></div>
      <div class="stat-box"><div class="k">Win rate</div><div class="v ${s.winRate>=50?'up':'dn'}">${s.winRate.toFixed(1)}%</div></div>
      <div class="stat-box"><div class="k">Net P/L</div><div class="v ${s.net>=0?'up':'dn'}">$${fmt2(s.net)}</div></div>
      <div class="stat-box"><div class="k">Profit factor</div><div class="v ${s.pf>=1?'up':'dn'}">${isFinite(s.pf)?s.pf.toFixed(2):"∞"}</div></div>
      <div class="stat-box"><div class="k">Avg win</div><div class="v up">$${fmt2(s.avgWin)}</div></div>
      <div class="stat-box"><div class="k">Avg loss</div><div class="v dn">$${fmt2(s.avgLoss)}</div></div>
      <div class="stat-box"><div class="k">Best</div><div class="v up">$${fmt2(s.best)}</div></div>
      <div class="stat-box"><div class="k">Worst</div><div class="v dn">$${fmt2(s.worst)}</div></div>
      <div class="stat-box"><div class="k">Max DD</div><div class="v dn">$${fmt2(s.maxDD)}</div></div>
      <div class="stat-box"><div class="k">Streak</div><div class="v ${s.streakType==='win'?'up':'dn'}">${s.streak} ${s.streakType||""}</div></div>
      <div class="stat-box"><div class="k">Avg hold</div><div class="v">${(s.avgHoldMs/3600000).toFixed(1)}h</div></div>
      <div class="stat-box"><div class="k">W/L</div><div class="v">${s.wins}/${s.losses}</div></div>
    </div>
    <div style="margin-top:12px">${svgCurve(s.curve, 600, 100)}</div>
    <div class="side-row">
      <div class="side-box"><b>CERTAIN</b><br>${s.certain.count} · ${s.certain.winRate.toFixed(0)}% win<br><span class="${s.certain.net>=0?'up':'dn'}">$${fmt2(s.certain.net)}</span></div>
      <div class="side-box"><b>CONFIDENT</b><br>${s.confident.count} · ${s.confident.winRate.toFixed(0)}% win<br><span class="${s.confident.net>=0?'up':'dn'}">$${fmt2(s.confident.net)}</span></div>
    </div>
    <div class="side-row">
      <div class="side-box"><b>LONG</b><br>${s.longCount} · ${s.longCount?(s.longWins/s.longCount*100).toFixed(0):0}% win<br><span class="${s.longNet>=0?'up':'dn'}">$${fmt2(s.longNet)}</span></div>
      <div class="side-box"><b>SHORT</b><br>${s.shortCount} · ${s.shortCount?(s.shortWins/s.shortCount*100).toFixed(0):0}% win<br><span class="${s.shortNet>=0?'up':'dn'}">$${fmt2(s.shortNet)}</span></div>
    </div>
    <div class="side-row">
      <div class="side-box"><b>PULLBACK</b><br>${s.pullback.count} · ${s.pullback.winRate.toFixed(0)}% win<br><span class="${s.pullback.net>=0?'up':'dn'}">$${fmt2(s.pullback.net)}</span></div>
      <div class="side-box"><b>BREAKOUT</b><br>${s.breakout.count} · ${s.breakout.winRate.toFixed(0)}% win<br><span class="${s.breakout.net>=0?'up':'dn'}">$${fmt2(s.breakout.net)}</span></div>
    </div>`;
}

function renderWatchlist() {
  const q = ($("search")?.value || "").toLowerCase();
  const rows = STATE.watchlist.map(c => STATE.coins[c]).filter(Boolean)
    .filter(c => assetFilter === "ALL" || c.assetClass === assetFilter)
    .filter(c => c.coin.toLowerCase().includes(q))
    .map(c => `<tr class="clickable" onclick="selectCoin('${esc(c.coin)}')"><td><b>${esc(c.coin)}</b></td><td><span class="badge ${c.signal}">${c.signal}</span> <span class="badge ${c.confidence||'LOW'}">${c.confidence||'LOW'}</span></td><td class="n">${fmt(c.price)}</td><td class="n">${c.score||0}</td></tr>`).join("");
  $("watch").innerHTML = rows ? `<div class="table-wrap"><table><thead><tr><th>Coin</th><th>Signal</th><th class="n">Price</th><th class="n">Score</th></tr></thead><tbody>${rows}</tbody></table></div>` : `<div class="mu">No matches.</div>`;
}

function selectCoin(coin) { currentCoin = coin; $("execCoin").value = coin; loadCandles(coin, currentIv); render(); }

function render() {
  $("statusDot").className = "dot " + (STATE.status === "live" ? "" : STATE.status === "error" ? "err" : "scan");
  if (!currentCoin && STATE.watchlist.length) {
    const buy = STATE.watchlist.find(c => STATE.coins[c].signal === "BUY");
    const btc = STATE.coins["BTC"] ? "BTC" : null;
    currentCoin = buy || btc || STATE.watchlist[0];
    renderTfTabs(); initChart(); loadCandles(currentCoin, currentIv);
  }
  refreshCoinSelects(); renderAssetTabs();
  const live = parseFloat(STATE.mids[currentCoin] || 0) || (STATE.coins[currentCoin]?.price || null);
  $("livePrice").textContent = live ? "$" + fmt(live) + " " + currentCoin : "—";
  const execLive = parseFloat(STATE.mids[$("execCoin").value] || 0) || (STATE.coins[$("execCoin").value]?.price || null);
  $("execLive").textContent = execLive ? "$" + fmt(execLive) : "—";
  if (live) updateFormingBar(live);
  updateExecPreview();
  const cur = STATE.coins[currentCoin];
  if (cur) {
    $("banner").className = "banner " + (cur.signal === "BUY" ? "buy" : cur.signal === "SELL" ? "sell" : cur.signal === "WAIT" ? "wait" : "neut");
    $("banner").textContent = `${cur.signal} ${cur.coin} — ${cur.confidence||""} · ${cur.gatesPassed||0}/${cur.gatesTotal||0} checks · score ${cur.score||0}`;
    renderSignalCard(cur);
    const ec = STATE.coins[$("execCoin").value];
    if (ec) $("execHint").innerHTML = `<b>${esc(ec.coin)}:</b> ${esc(ec.signal)} ${ec.confidence||""} · ${esc((ec.why||"").slice(0,200))}`;
  }
  renderPositions(); renderStats(); renderWatchlist(); renderAutoPanel(); checkAutoClose(); drawPriceLines(currentCoin);
}

$("execCoin").addEventListener("change", function() { currentCoin = this.value; loadCandles(currentCoin, currentIv); render(); });
$("execSize").addEventListener("input", updateExecPreview);
$("execLev").addEventListener("input", updateExecPreview);
$("capital").addEventListener("change", function() { localStorage.setItem("legend_capital", this.value); });
$("search").addEventListener("input", renderWatchlist);
const savedCap = localStorage.getItem("legend_capital");
if (savedCap) $("capital").value = savedCap;

connectWS();
applyTheme();
updateSoundBtn();
if (localStorage.getItem("stats_folded") === "1") { $("statsBody").style.display = "none"; $("statsToggle").textContent = "▲"; }
renderTfTabs();
render();
setTimeout(runScan, 200);
setInterval(runScan, SCAN_INTERVAL);
setInterval(() => { if (!document.hidden) { checkAutoTrade(); render(); } }, STATE_POLL_MS);

const lastBt = store.getBtLast();
if (lastBt) renderBacktestResult(lastBt); /* C.A. Creative Bot — created and owned by Charles Amankwah */

