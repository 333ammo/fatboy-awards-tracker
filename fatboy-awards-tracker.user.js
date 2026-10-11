// ==UserScript==
// @name         Fatboy Awards Tracker
// @namespace    fatboy.torn
// @version      3.0.2
// @description  Merit honors and medals tracker for Torn PDA (iOS): merit-only filtering, verified progress, plain-text exports.
// @author       FATBOY [572123]
// @match        https://www.torn.com/awards.php*
// @match        https://www.torn.com/page.php*
// @run-at       document-end
// @grant        none
// ==/UserScript==

/*
 * Fatboy Awards Tracker v3.0.2
 * - Data: Torn API v2 only (schemas checked against the official OpenAPI spec 6.13.x).
 * - Award-to-statistic research reference: YATA awards module (GPL-3.0, Kivou).
 *   YATA was used only as a source of facts (which award ID belongs to which
 *   statistic). No YATA code is included in this script.
 * - Runs inside Torn PDA: the API key is injected by PDA, requests go through
 *   PDA_httpGet, nothing is sent anywhere except api.torn.com.
 * 2.0.1 (correctness pass): "Verified" now needs the ID, statistic and target to match a
 *   validation snapshot AND Torn's live name/wording/target; a changed target shows "Needs
 *   review"; zero circulation no longer means "future"; age medals use calendar anniversaries;
 *   Token Shop/registry/Crimes 2.0 mapping fixes; runtime registry audit in Diagnostics.
 * 2.0.2 (fixes from the first live run in Torn PDA): names from Torn's live catalogue for honors
 *   34, 40, 165 and medal 177; honors 242 (Supersonic) and 243 (Abaddon) were swapped; medals the
 *   snapshot validates by name are tracked even when Torn's type data does not mark them (the 15
 *   total-offense medals); COPY DIAGNOSTICS now includes Torn's wording, type and crimes_version.
 * 3.0.0: bachelor honors accept Torn's current "Complete all classes in [subject]" description
 *   format; catalog and data write chains (window.__FBAT_CWC__, __FBAT_DWC__) prevent stale
 *   instance overwrites; shared poison set (__FBAT_POISON__) persists across re-initializations;
 *   restoreCache busy guard; thrNote provenance; export label "snapshot-validated".
 * 3.0.1: restricted to awards.php only (@match + runtime guard + SPA navigation teardown);
 *   panel title changed to "Merit Tracker".
 * 3.0.2: Torn PDA uses page.php?sid=awards for the Awards page; added @match for page.php*
 *   and updated runtime guard to accept /page.php?sid=awards as well as /awards.php.
 */
(function () {
  'use strict';

  const VERSION = '3.0.2';
  if (window.top !== window.self) return;
  const isAwardsPage = () => /\/awards\.php/.test(location.pathname) ||
    (/\/page\.php/.test(location.pathname) && /[?&]sid=awards(?:&|$)/.test(location.search));
  if (!isAwardsPage()) return;
  const PRIOR = window.__FBAT__;
  if (PRIOR && PRIOR.version === VERSION && typeof PRIOR.isAlive === 'function' && PRIOR.isAlive()) return;
  if (PRIOR && typeof PRIOR.destroy === 'function') { try { PRIOR.destroy(); } catch (e) { /* old instance already gone */ } }

  /* ============================== 1. CONSTANTS ============================== */
  const API_KEY = (window.__FBAT_EXPOSE__ === true && typeof window.__FBAT_TEST_KEY__ === 'string'
    && /^[A-Za-z0-9]{16,}$/.test(window.__FBAT_TEST_KEY__))
    ? window.__FBAT_TEST_KEY__
    : '###PDA-APIKEY###';
  const API_BASE = 'https://api.torn.com/v2';
  const API_COMMENT = 'FBAwards2';
  const NS = 'fbat2';
  const HOUR = 3600e3;
  const CATALOG_TTL = 24 * HOUR;
  const DATA_FRESH_MS = 15 * 60e3;
  const MIN_REFRESH_GAP = 30e3;
  const REQ_GAP_MS = 250;
  const REQ_MAX_PER_MIN = 40;
  const REQ_TIMEOUT_MS = 20e3;
  const HONOR_PAGE = 100;
  const HONOR_MAX_PAGES = 25;
  const PAGE_SIZE = 40;
  const DAY_MS = 864e5;

  /* ============================== 2. UTILITIES ============================== */
  const isNum = v => typeof v === 'number' && isFinite(v);
  const str = v => (v == null ? '' : String(v));
  const keyOk = () => typeof API_KEY === 'string' && /^[A-Za-z0-9]{16,}$/.test(API_KEY);
  const sleep = ms => new Promise(r => setTimeout(r, ms));

  /* SHA-256 fingerprint of the API key (truncated to 32 hex chars = 128 bits).
   * Computed once at module init; null when Web Crypto is unavailable or key invalid.
   * Only the hash is ever stored — the key itself never leaves the module. */
  const _keyFpPromise = (function () {
    if (!keyOk()) return Promise.resolve(null);
    if (typeof crypto === 'undefined' || !crypto.subtle || typeof TextEncoder === 'undefined')
      return Promise.resolve(null);
    return crypto.subtle.digest('SHA-256', new TextEncoder().encode(API_KEY))
      .then(function (buf) {
        return Array.from(new Uint8Array(buf)).slice(0, 16)
          .map(function (b) { return b.toString(16).padStart(2, '0'); }).join('');
      })
      .catch(function () { return null; });
  }());
  function keyFingerprint() { return _keyFpPromise; }

  const NUMFMT = {};
  function fmtNum(n, dp) {
    if (!isNum(n)) return '?';
    const d = dp == null ? (Number.isInteger(n) ? 0 : 2) : dp;
    if (!NUMFMT[d]) NUMFMT[d] = new Intl.NumberFormat('en-GB', { minimumFractionDigits: 0, maximumFractionDigits: d });
    return NUMFMT[d].format(n);
  }
  function fmtVal(n, unit) {
    if (!isNum(n)) return '?';
    if (unit && unit.money) return (n < 0 ? '-$' : '$') + fmtNum(Math.abs(Math.round(n)), 0);
    return fmtNum(n, unit && unit.dp != null ? unit.dp : null);
  }
  // Percent shown with up to 2 decimals; never shows 100% unless the target is met.
  function fmtPct(p, reached) {
    if (!isNum(p)) return '';
    let v = reached ? 100 : Math.min(99.99, Math.round(p * 100) / 100);
    if (!reached && p > 0 && v === 0) v = 0.01;
    return fmtNum(v, 2) + '%';
  }
  function pad2(n) { return (n < 10 ? '0' : '') + n; }
  function fmtStamp(ms, utc) {
    const d = new Date(ms);
    if (utc) return d.getUTCFullYear() + '-' + pad2(d.getUTCMonth() + 1) + '-' + pad2(d.getUTCDate()) + ' ' + pad2(d.getUTCHours()) + ':' + pad2(d.getUTCMinutes());
    return d.getFullYear() + '-' + pad2(d.getMonth() + 1) + '-' + pad2(d.getDate()) + ' ' + pad2(d.getHours()) + ':' + pad2(d.getMinutes());
  }
  function fmtAgo(ms) {
    const s = Math.max(0, Math.round((Date.now() - ms) / 1000));
    if (s < 60) return s + 's ago';
    if (s < 3600) return Math.round(s / 60) + ' min ago';
    if (s < 86400) return Math.round(s / 3600) + ' h ago';
    return Math.round(s / 86400) + ' d ago';
  }
  function fmtDuration(min) {
    if (!isNum(min)) return '?';
    if (min < 60) return Math.max(1, Math.round(min)) + ' min';
    if (min < 48 * 60) return fmtNum(Math.round(min / 6) / 10, 1) + ' h';
    return fmtNum(Math.round(min / 144) / 10, 1) + ' days';
  }
  function getPath(obj, path) {
    let o = obj;
    const parts = path.split('.');
    for (let i = 0; i < parts.length; i++) {
      if (!o || typeof o !== 'object' || !Object.prototype.hasOwnProperty.call(o, parts[i])) return { found: false };
      o = o[parts[i]];
    }
    return { found: true, value: o };
  }
  function debounce(fn, ms) {
    let t = null;
    return function () { const a = arguments; clearTimeout(t); t = setTimeout(() => fn.apply(null, a), ms); };
  }
  function cap(s) { s = str(s); return s ? s.charAt(0).toUpperCase() + s.slice(1) : s; }

  /* ---- Numbers inside official descriptions (thresholds) ---- */
  const NUM_WORDS = {
    zero: 0, one: 1, two: 2, three: 3, four: 4, five: 5, six: 6, seven: 7, eight: 8, nine: 9, ten: 10,
    eleven: 11, twelve: 12, thirteen: 13, fourteen: 14, fifteen: 15, sixteen: 16, seventeen: 17,
    eighteen: 18, nineteen: 19, twenty: 20, thirty: 30, forty: 40, fifty: 50, sixty: 60, seventy: 70,
    eighty: 80, ninety: 90
  };
  const SCALE_WORDS = { hundred: 100, thousand: 1e3, million: 1e6, billion: 1e9, trillion: 1e12 };

  function extractNumbers(text) {
    const s = str(text);
    const out = [];
    const reDigits = /(\$\s?)?(\d{1,3}(?:,\d{3})+|\d+)(\.\d+)?(\s*(?:thousand|million|billion|trillion)\b)?(\s*%)?/gi;
    let m;
    while ((m = reDigits.exec(s))) {
      let v = Number(m[2].replace(/,/g, '') + (m[3] || ''));
      if (m[4]) v *= SCALE_WORDS[m[4].trim().toLowerCase()];
      out.push({ v, money: !!m[1], pct: !!m[5], at: m.index });
    }
    const reWord = /[A-Za-z]+/g;
    let run = null;
    const flush = () => {
      if (run && run.any) out.push({ v: run.total + run.cur, money: false, pct: false, at: run.at, word: true });
      run = null;
    };
    while ((m = reWord.exec(s))) {
      const w = m[0].toLowerCase();
      const gapOk = run && /^[\s-]*$/.test(s.slice(run.end, m.index));
      if (run && !gapOk) flush();
      if (w === 'and' && run && run.any) {
        run.end = m.index + w.length;
      } else if (NUM_WORDS[w] != null) {
        if (!run) run = { total: 0, cur: 0, at: m.index, any: false };
        run.cur += NUM_WORDS[w]; run.any = true; run.end = m.index + w.length;
      } else if (run && SCALE_WORDS[w] != null) {
        if (w === 'hundred') run.cur = (run.cur || 1) * 100;
        else { run.total += (run.cur || 1) * SCALE_WORDS[w]; run.cur = 0; }
        run.end = m.index + w.length;
      } else flush();
    }
    flush();
    return out.sort((a, b) => a.at - b.at);
  }
  // Percentages are never targets ("Achieve 100% EXP on 25 different weapons" -> 25).
  function pickNumber(all, sel) {
    const nums = all.filter(n => !n.pct);
    if (!nums.length) return null;
    if (sel === 'money') { const x = nums.find(n => n.money); return x ? x.v : null; }
    if (sel === 'last') return nums[nums.length - 1].v;
    if (sel === 'max') return Math.max.apply(null, nums.map(n => n.v));
    if (isNum(sel)) return nums[sel] ? nums[sel].v : null;
    return nums[0].v;
  }
  // Award names compared case- and punctuation-insensitively ("Web of Perks" = "Web Of Perks").
  const normName = s => str(s).toLowerCase().replace(/[^a-z0-9]+/g, '');
  function fmtDate(ms) { const d = new Date(ms); return d.getUTCFullYear() + '-' + pad2(d.getUTCMonth() + 1) + '-' + pad2(d.getUTCDate()); }
  function ordinal(n) { const s = ['th', 'st', 'nd', 'rd']; const v = n % 100; return n + (s[(v - 20) % 10] || s[v] || s[0]); }

  /* ============================== 3. STORAGE ============================== */
  /* Poisoned-key set is shared across same-window instances so a double-failure
   * recorded by one IIFE is respected by a re-initialized successor.
   * Not persistent: a full page reload creates a new JavaScript window and resets it. */
  if (!window.__FBAT_POISON__) window.__FBAT_POISON__ = new Set();
  const Store = {
    _poisoned: window.__FBAT_POISON__,
    k: k => NS + ':' + k,
    get(k, d) { try { const s = localStorage.getItem(this.k(k)); return s == null ? d : JSON.parse(s); } catch (e) { return d; } },
    set(k, v) { try { localStorage.setItem(this.k(k), JSON.stringify(v)); return true; } catch (e) { return false; } },
    del(k) { try { localStorage.removeItem(this.k(k)); } catch (e) { /* storage blocked */ } },
    native() { return typeof PDA_storage !== 'undefined' && PDA_storage && typeof PDA_storage.get === 'function'; },
    async getBig(k) {
      /* Poisoned keys have a known-failed delete: return null to fail closed rather than
       * serving stale native data whose deletion could not be confirmed. */
      if (this._poisoned.has(k)) return null;
      /* 'own:<k>' = 'l' means localStorage owns this key; skip native to avoid reading stale data. */
      const own = this.get('own:' + k, null);
      if (own === 'l') return this.get('big:' + k, null);
      if (this.native()) {
        try { const v = await PDA_storage.get(this.k(k), null); if (v != null) return v; } catch (e) { /* fall back */ }
      }
      return this.get('big:' + k, null);
    },
    async setBig(k, v) {
      if (this.native()) {
        try {
          await PDA_storage.set(this.k(k), v);
          // Clear marker FIRST: once own:k is gone, getBig routes to native even if
          // the big:k cleanup below fails silently (removeItem should not throw, but
          // clearing the marker first is the safe ordering regardless).
          this.del('own:' + k);
          this.del('big:' + k);
          this._poisoned.delete(k);
          return true;
        } catch (e) { /* fall back to localStorage */ }
      }
      const ok = this.set('big:' + k, v);
      if (ok) {
        const markerOk = this.set('own:' + k, 'l');
        if (!markerOk) { this.del('big:' + k); return false; }
        this._poisoned.delete(k);
      }
      return ok;
    },
    async delBig(k) {
      let nativeOk = true;
      if (this.native()) {
        try { await PDA_storage.delete(this.k(k)); }
        catch (e) {
          nativeOk = false;
          /* Mark localStorage as owner so getBig won't fall through to stale native data.
           * If this set() also fails (localStorage quota), own:k stays absent; poison the
           * key so getBig returns null rather than stale native data (fail-closed). */
          const markerOk = this.set('own:' + k, 'l');
          if (!markerOk) this._poisoned.add(k);
        }
      }
      this.del('big:' + k);
      if (nativeOk) {
        this._poisoned.delete(k);
        this.del('own:' + k);
      }
      return nativeOk;
    }
  };

  /* ============================== 4. API CLIENT ============================== */
  class ApiError extends Error {
    constructor(kind, message, code, path) {
      super(message);
      this.kind = kind; this.code = code == null ? null : code; this.path = path || '';
    }
  }
  const TORN_ERRORS = {
    1: 'API key missing', 2: 'Incorrect API key', 5: 'Too many requests', 8: 'IP blocked', 9: 'API disabled',
    10: 'Key owner in federal jail', 13: 'Key temporarily disabled', 14: 'Daily read limit reached',
    16: 'Key access level too low', 17: 'Torn backend error', 18: 'API key paused', 24: 'API closed temporarily'
  };

  const Api = (function () {
    const stamps = [];
    let lastAt = 0;
    let coolUntil = 0;
    let chain = Promise.resolve();
    let total = 0;

    function redact(s) {
      let t = str(s);
      if (keyOk()) t = t.split(API_KEY).join('***');
      return t.replace(/key=[^&\s"']*/gi, 'key=***');
    }
    function buildUrl(path, params) {
      const q = [];
      Object.keys(params || {}).forEach(k => {
        const v = params[k];
        if (v != null && v !== '') q.push(encodeURIComponent(k) + '=' + encodeURIComponent(String(v)).replace(/%2C/gi, ','));
      });
      q.push('comment=' + API_COMMENT);
      q.push('key=' + encodeURIComponent(API_KEY));
      return API_BASE + path + '?' + q.join('&');
    }
    function withTimeout(p, ms) {
      let t;
      const guard = new Promise((_, rej) => { t = setTimeout(() => rej(new ApiError('timeout', 'Request timed out after ' + Math.round(ms / 1000) + 's')), ms); });
      return Promise.race([p, guard]).finally(() => clearTimeout(t));
    }
    async function transport(url) {
      if (typeof PDA_httpGet === 'function') {
        const r = await withTimeout(Promise.resolve(PDA_httpGet(url, {})), REQ_TIMEOUT_MS);
        if (typeof r === 'string') return { status: 200, text: r };
        if (!r || typeof r !== 'object') throw new ApiError('network', 'Empty response from Torn PDA');
        return { status: Number(r.status) || 0, text: r.responseText == null ? '' : String(r.responseText) };
      }
      throw new ApiError('env', 'PDA_httpGet is not available - open Torn inside the Torn PDA app');
    }
    async function slot() {
      let now = Date.now();
      while (stamps.length && now - stamps[0] > 60e3) stamps.shift();
      if (stamps.length >= REQ_MAX_PER_MIN) { await sleep(60e3 - (now - stamps[0]) + 50); now = Date.now(); }
      const gap = lastAt + REQ_GAP_MS - now;
      if (gap > 0) await sleep(gap);
      lastAt = Date.now();
      stamps.push(lastAt);
      total++;
    }
    function queued(fn) {
      const run = chain.then(fn, fn);
      chain = run.then(() => undefined, () => undefined);
      return run;
    }
    function get(path, params) {
      if (!keyOk()) return Promise.reject(new ApiError('env', 'Torn PDA did not supply an API key. Open this page inside Torn PDA with your key saved.', 1, path));
      return queued(async () => {
        if (Date.now() < coolUntil) throw new ApiError('rate', 'Paused after a rate-limit warning; retry in ' + Math.ceil((coolUntil - Date.now()) / 1000) + 's', 5, path);
        await slot();
        let res;
        try { res = await transport(buildUrl(path, params)); } catch (e) {
          if (e instanceof ApiError) { e.path = path; e.message = redact(e.message); throw e; }
          throw new ApiError('network', 'Network error: ' + redact(e && e.message ? e.message : e), null, path);
        }
        if (res.status >= 400) throw new ApiError('http', 'HTTP ' + res.status + ' from Torn API', res.status, path);
        if (!res.text) throw new ApiError('parse', 'Empty response body', null, path);
        let data;
        try { data = JSON.parse(res.text); } catch (e) { throw new ApiError('parse', 'Malformed JSON from Torn API', null, path); }
        if (!data || typeof data !== 'object' || Array.isArray(data)) throw new ApiError('parse', 'Unexpected response shape', null, path);
        if (data.error) {
          const code = Number(data.error.code);
          if (code === 5) coolUntil = Date.now() + 65e3;
          const text = redact(data.error.error || data.error.message || 'API error');
          throw new ApiError('torn', (TORN_ERRORS[code] ? TORN_ERRORS[code] + ': ' : '') + text + ' (code ' + code + ')', code, path);
        }
        return data;
      });
    }
    return { get, redact, count: () => total, coolingFor: () => Math.max(0, coolUntil - Date.now()) };
  })();

  function errInfo(e) {
    if (!e) return null;
    return { kind: e.kind || 'error', code: e.code == null ? null : e.code, msg: Api.redact(e.message || String(e)), path: e.path || '' };
  }

  /* ========================= 5. RESPONSE VALIDATION ========================= */
  const HONOR_TYPES = ['attacking', 'camo', 'weapons', 'education', 'crimes', 'drugs', 'jail', 'hospital', 'travel', 'gym', 'level', 'competitions', 'money', 'items', 'commitment', 'casino', 'missions', 'misc', 'default'];
  const MEDAL_TYPES = ['combat', 'commitment', 'crime', 'level', 'miscellaneous', 'networth', 'rank'];
  const MEDAL_CODE_TITLES = { ATK: 'combat', CMT: 'commitment', CRM: 'crime', LVL: 'level', OTR: 'miscellaneous', NTW: 'networth', RNK: 'rank' };

  function normAward(raw, kind) {
    if (!raw || typeof raw !== 'object') return null;
    const id = Number(raw.id);
    if (!Number.isInteger(id) || id <= 0) return null;
    const t = raw.type && typeof raw.type === 'object' ? raw.type : {};
    let title = str(t.title).trim().toLowerCase();
    if (!title && kind === 'M' && MEDAL_CODE_TITLES[str(t.id).toUpperCase()]) title = MEDAL_CODE_TITLES[str(t.id).toUpperCase()];
    return {
      k: kind, id,
      name: str(raw.name).trim(),
      desc: str(raw.description).replace(/\s+/g, ' ').trim(),
      typeId: kind === 'H' ? (isNum(t.id) ? t.id : (/^\d+$/.test(str(t.id)) ? Number(t.id) : null)) : str(t.id).toUpperCase(),
      cat: title,
      rarity: str(raw.rarity),
      circ: isNum(raw.circulation) ? raw.circulation : null,
      cv: raw.crimes_version === 'v1' || raw.crimes_version === 'v2' ? raw.crimes_version : null
    };
  }
  function catalogArray(data, key) {
    const x = data && data[key];
    if (Array.isArray(x)) return x;
    if (x && typeof x === 'object') return Object.keys(x).map(id => Object.assign({ id: Number(id) }, x[id]));
    throw new ApiError('schema', 'Torn ' + key + ' catalogue has an unexpected format', null, '/torn/' + key);
  }
  function normCatalogList(data, key, kind, warnings) {
    const out = [];
    let bad = 0;
    catalogArray(data, key).forEach(r => { const a = normAward(r, kind); if (a) out.push(a); else bad++; });
    if (bad) warnings.push(bad + ' malformed ' + key + ' entries were skipped');
    return out;
  }
  // Earned lists: v2 returns [{id, timestamp}]; older shapes are tolerated.
  function normEarned(data, key) {
    const out = new Map();
    const x = data && data[key];
    if (Array.isArray(x)) {
      x.forEach(e => {
        if (isNum(e)) out.set(e, null);
        else if (e && Number.isInteger(Number(e.id))) out.set(Number(e.id), isNum(e.timestamp) ? e.timestamp : null);
      });
      return out;
    }
    if (x && typeof x === 'object') { Object.keys(x).forEach(k => { if (/^\d+$/.test(k)) out.set(Number(k), isNum(x[k]) ? x[k] : null); }); return out; }
    return null;
  }

  /* =========================== 6. CATALOGUE LOADER =========================== */
  async function fetchHonorPages(warnings) {
    const all = new Map();
    let offset = 0;
    let paged = true;
    for (let page = 0; page < HONOR_MAX_PAGES; page++) {
      let data;
      try { data = await Api.get('/torn/honors', paged ? { limit: HONOR_PAGE, offset } : { offset }); } catch (e) {
        // If the server rejects the paging parameters, fall back to its defaults once.
        if (page === 0 && paged && e.kind === 'torn' && [3, 4, 6, 21, 26].indexOf(e.code) !== -1) { paged = false; page--; continue; }
        throw e;
      }
      const raw = catalogArray(data, 'honors');
      const list = normCatalogList(data, 'honors', 'H', warnings);
      let added = 0;
      list.forEach(h => { if (!all.has(h.id)) { all.set(h.id, h); added++; } });
      if (!raw.length || !added) break;
      offset += raw.length;
      if (page === HONOR_MAX_PAGES - 1) warnings.push('Honor catalogue stopped at ' + HONOR_MAX_PAGES + ' pages');
    }
    return Array.from(all.values()).sort((a, b) => a.id - b.id);
  }

  async function loadCatalog(force, onStep, liveCheck) {
    const cached = await Store.getBig('catalog');
    if (!force && cached && cached.v === VERSION && Date.now() - cached.at < CATALOG_TTL && Array.isArray(cached.honors) && cached.honors.length && Array.isArray(cached.medals) && cached.medals.length) {
      return Object.assign({ fromCache: true }, cached);
    }
    const warnings = [];
    let honors;
    let medals;
    try {
      onStep && onStep('Downloading honor catalogue...');
      honors = await fetchHonorPages(warnings);
      onStep && onStep('Downloading medal catalogue...');
      medals = normCatalogList(await Api.get('/torn/medals'), 'medals', 'M', warnings);
    } catch (e) {
      // Keep working from an older catalogue rather than showing nothing.
      if (cached && cached.v === VERSION && Array.isArray(cached.honors) && cached.honors.length && Array.isArray(cached.medals) && cached.medals.length && !(e.kind === 'env' || e.code === 2)) {
        return Object.assign({ fromCache: true }, cached, { warnings: (cached.warnings || []).concat('Catalogue refresh failed (' + errInfo(e).msg + '); using the copy from ' + fmtStamp(cached.at, true) + ' TCT.') });
      }
      throw e;
    }
    let edu = null;
    try {
      onStep && onStep('Downloading education catalogue...');
      const e = await Api.get('/torn/education');
      if (Array.isArray(e.education)) {
        edu = e.education.filter(c => c && str(c.name) && Array.isArray(c.courses)).map(c => ({
          name: str(c.name), courses: c.courses.map(x => Number(x && x.id)).filter(Number.isInteger)
        }));
      }
    } catch (e) { warnings.push('Education catalogue unavailable: ' + errInfo(e).msg); }
    if (!honors.length || !medals.length) throw new ApiError('schema', 'Torn returned an empty award catalogue', null, '/torn');
    const cat = { v: VERSION, at: Date.now(), honors, medals, edu, warnings };
    if (!liveCheck || liveCheck()) {
      // Serialize catalog writes: wait for any in-progress write to complete, then
      // re-check liveness before writing. This prevents a stale instance from
      // overwriting a newer catalog written by a concurrent live instance.
      const prevChain = window.__FBAT_CWC__;
      let releaseLock;
      window.__FBAT_CWC__ = new Promise(function (r) { releaseLock = r; });
      try {
        await prevChain;
        if (liveCheck && !liveCheck()) { return Object.assign({ fromCache: false }, cat); }
        await Store.setBig('catalog', cat);
        if (liveCheck && !liveCheck()) await Store.delBig('catalog').catch(function () {});
      } finally {
        releaseLock();
      }
    }
    return Object.assign({ fromCache: false }, cat);
  }

  /* ============================ 7. USER DATA LOADER ============================ */
  // One combined call for the minimal/public selections, then personal stats and
  // battle stats separately so a low-access key only loses what it cannot see.
  const COMBINED = ['honors', 'medals', 'profile', 'faction', 'skills', 'workstats', 'education', 'merits', 'perks', 'weaponexp', 'hof', 'enlistedcars'];

  const SHAPES = { profile: 'o', workstats: 'o', merits: 'o', perks: 'o', hof: 'o', personalstats: 'o', weaponexp: 'a', enlistedcars: 'a' };
  function parseSelection(name, data) {
    const v = data[name];
    const bad = () => new ApiError('schema', name + ' missing or malformed in the API response');
    if (name === 'honors' || name === 'medals') { const m = normEarned(data, name); if (!m) throw bad(); return m; }
    if (name === 'faction') { if (!(name in data)) throw bad(); return v || null; }
    if (name === 'skills') {
      if (!Array.isArray(v)) throw bad();
      const o = {};
      v.forEach(x => { if (x && str(x.slug) && isNum(Number(x.level))) o[str(x.slug)] = Number(x.level); });
      return o;
    }
    if (name === 'education') { if (!v || !Array.isArray(v.complete)) throw bad(); return v; }
    if (name === 'battlestats') {
      if (!v || typeof v !== 'object') throw bad();
      const o = {};
      ['strength', 'defense', 'speed', 'dexterity'].forEach(k => { const x = v[k] && typeof v[k] === 'object' ? v[k].value : v[k]; if (isNum(x)) o[k] = x; });
      if (Object.keys(o).length !== 4) throw bad();
      return o;
    }
    if (SHAPES[name] === 'a' ? Array.isArray(v) : (v && typeof v === 'object' && !Array.isArray(v))) return v;
    throw bad();
  }

  async function loadUserData(onStep) {
    const D = { at: Date.now(), src: {}, sel: {} };
    const ok = (name, v) => { D.sel[name] = v; D.src[name] = { ok: true }; };
    const fail = (name, e) => { D.src[name] = { ok: false, err: errInfo(e) }; };
    const fatal = e => e && (e.kind === 'env' || e.kind === 'rate' || (e.kind === 'torn' && [1, 2, 5, 8, 9, 10, 13, 14, 18, 24].indexOf(e.code) !== -1));

    onStep && onStep('Fetching your awards and profile...');
    let combined = null;
    try { combined = await Api.get('/user', { selections: COMBINED.join(',') }); } catch (e) { if (fatal(e)) throw e; }
    for (const name of COMBINED) {
      let done = false;
      if (combined) { try { ok(name, parseSelection(name, combined)); done = true; } catch (e) { /* retry alone */ } }
      if (!done) {
        try { ok(name, parseSelection(name, await Api.get('/user/' + name))); } catch (e) {
          if (fatal(e)) throw e;
          fail(name, e);
        }
      }
    }
    onStep && onStep('Fetching personal stats...');
    try { ok('personalstats', parseSelection('personalstats', await Api.get('/user/personalstats', { cat: 'all' }))); } catch (e) { if (fatal(e)) throw e; fail('personalstats', e); }
    onStep && onStep('Fetching battle stats...');
    try { ok('battlestats', parseSelection('battlestats', await Api.get('/user/battlestats'))); } catch (e) { if (fatal(e)) throw e; fail('battlestats', e); }
    return D;
  }

  /* =========================== 8. STATISTIC REGISTRY =========================== */
  // Every statistic has one official source. src: ps=/user/personalstats?cat=all,
  // bs=/user/battlestats, sk=/user/skills, pr=/user/profile, fa=/user/faction,
  // ws=/user/workstats, ed=/user/education, me=/user/merits, pk=/user/perks,
  // we=/user/weaponexp, hf=/user/hof, cars=/user/enlistedcars.
  // kind: cum = cumulative counter, peak = best-ever value, inst = current value
  // (meeting it now does not guarantee the award), time = calendar-gated.
  const STATS = {};
  const SRC_SEL = { ps: 'personalstats', bs: 'battlestats', sk: 'skills', pr: 'profile', fa: 'faction', ws: 'workstats', ed: 'education', me: 'merits', pk: 'perks', we: 'weaponexp', hf: 'hof', cars: 'enlistedcars' };
  const PS_PRIVATE = ['battle_stats.', 'investments.', 'jobs.stats.', 'networth.wallet', 'networth.bank', 'attacking.killstreak.current'];
  function S(key, src, path, label, o) { STATS[key] = Object.assign({ key, src, path, label, kind: 'cum' }, o || {}); }

  [
    ['attWins', 'attacking.attacks.won', 'attack wins'], ['defWins', 'attacking.defends.won', 'defend wins'],
    ['stealth', 'attacking.attacks.stealth', 'stealthed attacks'], ['assists', 'attacking.attacks.assist', 'attack assists'],
    ['critHits', 'attacking.hits.critical', 'critical hits'], ['hits', 'attacking.hits.success', 'successful hits'],
    ['ohk', 'attacking.hits.one_hit_kills', 'one hit kills'], ['escapes', 'attacking.escapes.player', 'escapes'],
    ['foesEscaped', 'attacking.escapes.foes', 'enemy escapes'], ['dmgTotal', 'attacking.damage.total', 'total damage'],
    ['unarmored', 'attacking.unarmored_wins', 'unarmored wins'], ['rounds', 'attacking.ammunition.total', 'rounds fired'],
    ['ammoSpecial', 'attacking.ammunition.special', 'special rounds'], ['ammoHollow', 'attacking.ammunition.hollow_point', 'hollow point rounds'],
    ['ammoPiercing', 'attacking.ammunition.piercing', 'piercing rounds'], ['ammoIncendiary', 'attacking.ammunition.incendiary', 'incendiary rounds'],
    ['ammoTracer', 'attacking.ammunition.tracer', 'tracer rounds'], ['respect', 'attacking.faction.respect', 'faction respect'],
    ['abroadWins', 'travel.attacks_won', 'attacks won abroad'], ['bounties', 'bounties.collected.amount', 'bounties collected'],
    ['busts', 'jail.busts.success', 'successful busts'], ['bails', 'jail.bails.amount', 'bails'],
    ['jailed', 'jail.times_jailed', 'times jailed'], ['hospitalized', 'hospital.times_hospitalized', 'hospital visits'],
    ['revives', 'hospital.reviving.revives', 'revives'], ['medItems', 'hospital.medical_items_used', 'medical items'],
    ['blood', 'hospital.blood_withdrawn', 'blood bags filled'], ['cityFinds', 'items.found.city', 'city finds'],
    ['dumpFinds', 'items.found.dump', 'dump finds'], ['trashed', 'items.trashed', 'items trashed'],
    ['viruses', 'items.viruses_coded', 'viruses coded'], ['statEnh', 'items.used.stat_enhancers', 'stat enhancers'],
    ['alcohol', 'items.used.alcohol', 'bottles of alcohol'], ['candy', 'items.used.candy', 'bags of candy'],
    ['eDrinks', 'items.used.energy_drinks', 'energy drinks'], ['books', 'items.used.books', 'books'],
    ['auctions', 'trading.items.auctions.won', 'auctions won'], ['bazaarCust', 'trading.bazaar.customers', 'bazaar customers'],
    ['pointsSold', 'trading.points.sold', 'points sold'], ['travels', 'travel.total', 'trips abroad'],
    ['imports', 'travel.items_bought', 'items imported'], ['racingPts', 'racing.points', 'racing points'],
    ['racesWon', 'racing.races.won', 'races won'], ['jobPoints', 'jobs.job_points_used', 'job points'],
    ['stockPayouts', 'investments.stocks.payouts', 'stock payouts'], ['refE', 'other.refills.energy', 'energy refills'],
    ['refN', 'other.refills.nerve', 'nerve refills'], ['refT', 'other.refills.token', 'casino token refills'],
    ['donator', 'other.donator_days', 'donator days', { kind: 'time' }], ['contracts', 'missions.contracts.total', 'contracts'],
    ['credits', 'missions.credits', 'mission credits']
  ].forEach(r => S(r[0], 'ps', r[1], r[2], r[3]));
  S('streak', 'ps', 'attacking.killstreak.best', 'best kill streak', { kind: 'peak' });
  S('dmgBest', 'ps', 'attacking.damage.best', 'best single-hit damage', { kind: 'peak' });
  S('largestMug', 'ps', 'attacking.networth.largest_mug', 'largest mug', { kind: 'peak', money: true });
  S('bountyValue', 'ps', 'bounties.collected.value', 'bounty earnings', { money: true });
  S('stockProfits', 'ps', 'investments.stocks.profits', 'stock profits', { money: true });
  S('stockLosses', 'ps', 'investments.stocks.losses', 'stock losses', { money: true, abs: true });
  S('bankInvest', 'ps', 'investments.bank.current', 'current bank investment', { money: true, kind: 'inst' });
  S('networth', 'ps', 'networth.total', 'networth', { money: true, kind: 'inst' });
  S('loginStreak', 'ps', 'other.activity.streak.current', 'consecutive days online', { kind: 'time' });
  S('airDays', 'ps', 'travel.time_spent', 'days in the air', { scale: 1 / 86400, dp: 2 });
  S('activityH', 'ps', 'other.activity.time', 'hours active', { scale: 1 / 3600, dp: 1 });
  S('stalemates', 'ps', null, 'stalemates', { sum: ['attacking.attacks.stalemate', 'attacking.defends.stalemate'] });
  const FH = ['heavy_artillery', 'mechanical', 'clubbing', 'temporary', 'machine_guns', 'sub_machine_guns', 'pistols', 'rifles', 'shotguns', 'piercing', 'slashing', 'hand_to_hand'];
  FH.forEach(c => S('fh_' + c, 'ps', 'finishing_hits.' + c, c.replace(/_/g, ' ') + ' finishing hits'));
  ['cannabis', 'ecstasy', 'ketamine', 'lsd', 'opium', 'pcp', 'shrooms', 'speed', 'vicodin', 'xanax'].forEach(d => S('drug_' + d, 'ps', 'drugs.' + d, d === 'lsd' || d === 'pcp' ? d.toUpperCase() : cap(d)));
  ['mexico', 'cayman_islands', 'canada', 'hawaii', 'united_kingdom', 'argentina', 'switzerland', 'japan', 'china', 'united_arab_emirates', 'south_africa']
    .forEach(c => S('c_' + c, 'ps', 'travel.' + c, 'trips to ' + c.split('_').map(cap).join(' ')));
  ['vandalism', 'theft', 'counterfeiting', 'fraud', 'illicit_services', 'cybercrime', 'extortion', 'illegal_production', 'organized_crimes', 'total']
    .forEach(c => S('off_' + c, 'ps', 'crimes.offenses.' + c, (c === 'total' ? 'total' : c.replace(/_/g, ' ')) + ' offenses', { crimes2: true }));
  ['search_for_cash', 'bootlegging', 'graffiti', 'shoplifting', 'pickpocketing', 'card_skimming', 'burglary', 'hustling', 'disposal', 'cracking', 'forgery', 'scamming', 'arson']
    .forEach(s => S('sk_' + s, 'sk', s, s.split('_').map(cap).join(' ') + ' skill', { dp: 2, alt: ['ps', 'crimes.skills.' + s], kind: 'peak' }));
  S('huntSkill', 'sk', 'hunting', 'hunting skill', { dp: 2, alt: ['ps', 'travel.hunting.skill'], kind: 'peak' });
  S('racingSkill', 'sk', 'racing', 'racing skill', { dp: 2, alt: ['ps', 'racing.skill'], kind: 'peak' });
  [['bsStr', 'strength', 'Strength'], ['bsDef', 'defense', 'Defense'], ['bsSpd', 'speed', 'Speed'], ['bsDex', 'dexterity', 'Dexterity']]
    .forEach(r => S(r[0], 'bs', r[1], r[2], { alt: ['ps', 'battle_stats.' + r[1]], dp: 0 }));
  S('bsTotal', 'bs', null, 'total battle stats', { fn: 'bsTotal', dp: 0 });
  S('level', 'pr', 'level', 'level', { kind: 'peak' });
  S('ageDays', 'pr', 'age', 'days in Torn', { kind: 'time' });
  S('rankIdx', 'pr', null, 'rank', { fn: 'rank', kind: 'peak' });
  S('daysMarried', 'pr', null, 'days married', { fn: 'married', kind: 'time' });
  S('totalAwards', 'pr', 'awards', 'total awards', { alt: ['ps', 'other.awards'] });
  S('factionDays', 'fa', null, 'days in current faction', { fn: 'faction', kind: 'time' });
  S('workMan', 'ws', 'manual_labor', 'manual labour'); S('workInt', 'ws', 'intelligence', 'intelligence'); S('workEnd', 'ws', 'endurance', 'endurance');
  S('workMax', 'ws', null, 'highest working stat', { fn: 'workMax' });
  S('courses', 'ed', null, 'courses completed', { fn: 'courses' });
  S('meritMax', 'me', null, 'highest merit upgrade level', { fn: 'meritMax', kind: 'peak' });
  S('perks', 'pk', null, 'personal perks', { fn: 'perks', kind: 'inst' });
  S('weaponsMaxed', 'we', null, 'weapons at 100% EXP', { fn: 'weaponsMaxed' });
  S('hofBest', 'hf', null, 'best Hall of Fame rank', { fn: 'hofBest', kind: 'inst', lower: true });
  S('carWins', 'cars', null, 'most race wins with one car', { fn: 'carWins', kind: 'peak' });

  const RANKS = ['Absolute beginner', 'Beginner', 'Inexperienced', 'Rookie', 'Novice', 'Below average', 'Average', 'Reasonable', 'Above average', 'Competent', 'Highly competent', 'Veteran', 'Distinguished', 'Highly distinguished', 'Professional', 'Star', 'Master', 'Outstanding', 'Celebrity', 'Supreme', 'Idolized', 'Champion', 'Heroic', 'Legendary', 'Elite', 'Invincible'];
  function rankIndex(text) {
    const t = str(text).trim().toLowerCase();
    if (!t) return -1;
    let best = -1;
    let bestLen = 0;
    RANKS.forEach((r, i) => { const rl = r.toLowerCase(); if ((t === rl || t.indexOf(rl + ' ') === 0) && rl.length > bestLen) { best = i; bestLen = rl.length; } });
    return best;
  }

  /* ============================ 9. AWARD REGISTRY ============================ */
  // Keyed by official award ID ("H:<id>" honors, "M:<id>" medals).
  //  stat  : statistic key, or a variant list [[regex, statKey, excludeRegex]]
  //          chosen from Torn's official wording for that ID (closed vocabulary).
  //  e     : researched threshold(s) per ID (fallback when the ID is not in the snapshot).
  //  t     : fixed target for awards whose wording has no number ("Use a stat enhancer").
  //  kw    : wording guard - the live description must match or the award needs review.
  //  sel   : which number in the description is the target (first/money/last/index).
  //  ev    : evidence. Y = YATA maps this ID to this statistic; W = Torn wiki
  //          threshold; S = official schema/endpoint; T = official type metadata.
  //  sp    : special award ('cond' condition, 'act' action, 'date' calendar login).
  //  partial: why the statistic is only an approximation of Torn's rule.
  // Registry membership alone never makes progress "Verified": the ID must also match the
  // validation snapshot (section 9b) and Torn's live name, wording and target.
  const REG = new Map();
  const REG_DUPES = [];
  function put(key, v) { if (REG.has(key)) REG_DUPES.push(key); REG.set(key, v); }
  function fam(kind, ids, stat, o) { ids.forEach(id => put(kind + ':' + id, Object.assign({ kind, id, stat, ev: 'Y' }, o || {}))); }
  function special(kind, ids, sp, o) { ids.forEach(id => put(kind + ':' + id, Object.assign({ kind, id, sp, ev: 'Y' }, o || {}))); }
  const range = (a, b) => { const r = []; for (let i = a; i <= b; i++) r.push(i); return r; };

  const V_FH = [
    [/heavy artillery/i, 'fh_heavy_artillery'], [/mechanical/i, 'fh_mechanical'], [/clubbing/i, 'fh_clubbing'],
    [/temporary/i, 'fh_temporary'], [/\bsmgs?\b|sub[- ]?machine/i, 'fh_sub_machine_guns'],
    [/machine[- ]?guns?/i, 'fh_machine_guns', /sub[- ]?machine/i], [/pistols?/i, 'fh_pistols'], [/rifles?/i, 'fh_rifles'],
    [/shotguns?/i, 'fh_shotguns'], [/piercing/i, 'fh_piercing'], [/slashing/i, 'fh_slashing'],
    [/\bfists?\b|\bkicks?\b|hand[- ]to[- ]hand|unarmed/i, 'fh_hand_to_hand']
  ];
  const V_DRUG = [[/cannabis/i, 'drug_cannabis'], [/ecstasy/i, 'drug_ecstasy'], [/ketamine/i, 'drug_ketamine'], [/\blsd\b/i, 'drug_lsd'], [/opium/i, 'drug_opium'], [/\bpcp\b/i, 'drug_pcp'], [/shrooms/i, 'drug_shrooms'], [/\bspeed\b/i, 'drug_speed'], [/vicodin/i, 'drug_vicodin'], [/xanax/i, 'drug_xanax']];
  const V_COUNTRY = [[/mexico/i, 'c_mexico'], [/cayman/i, 'c_cayman_islands'], [/canada/i, 'c_canada'], [/hawaii/i, 'c_hawaii'], [/united kingdom|\buk\b|england|london|britain/i, 'c_united_kingdom'], [/argentina/i, 'c_argentina'], [/switzerland|zurich/i, 'c_switzerland'], [/japan/i, 'c_japan'], [/china/i, 'c_china'], [/united arab emirates|\buae\b|dubai/i, 'c_united_arab_emirates'], [/south africa|johannesburg/i, 'c_south_africa']];
  const V_BS = [[/strength/i, 'bsStr'], [/defen[cs]e/i, 'bsDef'], [/speed/i, 'bsSpd'], [/dexterity/i, 'bsDex'], [/\btotal\b/i, 'bsTotal']];
  const V_OFF = [[/vandalism/i, 'off_vandalism'], [/theft/i, 'off_theft'], [/counterfeit/i, 'off_counterfeiting'], [/fraud/i, 'off_fraud'], [/illicit service/i, 'off_illicit_services'], [/cyber ?crime/i, 'off_cybercrime'], [/extortion/i, 'off_extortion'], [/illegal production/i, 'off_illegal_production'], [/organi[sz]ed crime/i, 'off_organized_crimes'], [/a total of|total offen[cs]es|criminal offen[cs]es/i, 'off_total']];
  const V_SKILL = [['search for cash', 'search_for_cash'], ['bootlegging', 'bootlegging'], ['graffiti', 'graffiti'], ['shoplifting', 'shoplifting'], ['pickpocketing', 'pickpocketing'], ['card skimming', 'card_skimming'], ['burglary', 'burglary'], ['hustling', 'hustling'], ['disposal', 'disposal'], ['cracking', 'cracking'], ['forgery', 'forgery'], ['scamming', 'scamming'], ['arson', 'arson']].map(r => [new RegExp('\\b' + r[0] + '\\b', 'i'), 'sk_' + r[1]]);

  // ---- Honors: combat ----
  fam('H', range(39, 49), 'attWins', { e: { 39: 5 }, kw: /attack|win/i });
  fam('H', [28, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 515], V_FH, { e: 100, kw: /finishing/i, ev: 'YW' });
  fam('H', [611], null, { calc: 'fhAll', e: 1000, kw: /finishing/i });
  fam('H', [15, 16, 17], 'streak', { e: { 15: 10 }, kw: /streak/i });
  fam('H', [20, 227], 'critHits', { e: { 20: 25 }, kw: /critical/i });
  fam('H', [22], 'defWins', { e: 50, kw: /defend/i });
  fam('H', [228], null, { calc: 'multi', parts: [['attWins', 0], ['defWins', 1]], e: 1000, kw: /attack/i });
  fam('H', [27], 'stealth', { e: 100, kw: /stealth/i });
  fam('H', [740, 741, 786], 'dmgBest', { e: { 740: 5000, 741: 10000, 786: 15000 }, kw: /single hit/i });
  fam('H', [1001, 1002, 1003, 1004], 'dmgTotal', { e: { 1001: 1e7, 1002: 1e6, 1003: 1e8, 1004: 1e5 }, kw: /total damage/i });
  fam('H', [763], 'unarmored', { e: 250, kw: /unarmou?red/i });
  fam('H', [140, 151, 834, 836], 'rounds', { e: { 140: 1000, 151: 10000, 834: 100000, 836: 1000000 }, kw: /rounds/i, ev: 'YW' });
  fam('H', [800, 793, 791], 'ammoSpecial', { e: { 800: 100, 793: 1000, 791: 10000 }, kw: /special ammunition/i });
  fam('H', [942], 'ammoHollow', { e: 2500, kw: /hollow point/i });
  fam('H', [943], 'ammoPiercing', { e: 2500, kw: /piercing/i });
  fam('H', [944], 'ammoIncendiary', { e: 2500, kw: /incendiary/i });
  fam('H', [945], 'ammoTracer', { e: 2500, kw: /tracer/i });
  fam('H', [232], 'bounties', { e: 250, kw: /bount/i });
  fam('H', [236], 'bountyValue', { e: 1e7, kw: /bounty/i, sel: 'money' });
  fam('H', [247], 'largestMug', { e: 1e6, kw: /mug/i, sel: 'money' });
  fam('H', [270], 'stalemates', { e: 100, kw: /stalemate/i });
  fam('H', [490], 'assists', { e: 250, kw: /assist/i });
  fam('H', [517], 'ohk', { e: 100, kw: /one hit/i });
  fam('H', [254], 'ohk', { t: 1, kw: /one hit kill/i });
  fam('H', [639], 'assists', { t: 1, kw: /assist/i });
  fam('H', [601], 'hits', { e: 10000, kw: /hits/i });
  fam('H', [778], 'weaponsMaxed', { e: 25, kw: /exp/i, ev: 'YS' });
  fam('H', [846], 'abroadWins', { e: 100, kw: /abroad/i });
  // ---- Honors: travel, drugs, jail, hospital, items ----
  fam('H', [11, 165], 'travels', { e: { 11: 100 }, kw: /travel/i });
  fam('H', [549, 557, 567], 'airDays', { e: { 549: 7 }, kw: /air/i });
  fam('H', [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 272], V_COUNTRY, { e: { 130: 50 }, kw: /travel|visit|fly/i, sel: 'last' });
  fam('H', [541, 542, 543], 'imports', { e: { 541: 100 }, kw: /import|abroad/i });
  fam('H', [50, 51, 52], 'huntSkill', { e: { 50: 50, 51: 75, 52: 100 }, kw: /hunt/i });
  fam('H', range(29, 38), V_DRUG, { e: 50, ev: 'YW' });
  fam('H', [248, 249, 250], 'busts', { e: { 248: 1000 }, kw: /bust/i });
  fam('H', [252], 'bails', { e: 500, kw: /bail/i });
  fam('H', [906], 'jailed', { e: 250, kw: /jail/i });
  fam('H', [903], 'hospitalized', { e: 250, kw: /hospital/i });
  fam('H', [23, 267], 'revives', { e: { 23: 500, 267: 1000 }, kw: /reviv/i });
  fam('H', [398, 418], 'blood', { e: { 398: 1000, 418: 250 }, kw: /blood/i });
  fam('H', [7], 'medItems', { e: 5000, kw: /medical/i });
  fam('H', [1], 'cityFinds', { e: 50, kw: /city/i });
  fam('H', [238], 'dumpFinds', { e: 1000, kw: /dump/i });
  fam('H', [271], 'trashed', { e: 5000, kw: /trash/i });
  fam('H', [273], 'auctions', { e: 10, kw: /auction/i });
  fam('H', [216], 'viruses', { e: 100, kw: /virus/i });
  fam('H', [527], 'statEnh', { t: 1, kw: /stat enhancer/i });
  fam('H', [534], 'alcohol', { e: 500, kw: /alcohol/i });
  fam('H', [537], 'candy', { e: 500, kw: /candy/i });
  fam('H', [538], 'eDrinks', { e: 500, kw: /energy drink/i });
  fam('H', [539], 'books', { e: 10, kw: /book/i });
  // ---- Honors: education, work, gym ----
  fam('H', range(53, 64), null, { calc: 'bachelor', ev: 'YS', partial: true });
  fam('H', [651, 653, 656, 659], 'courses', { e: { 653: 10 }, kw: /course/i, ev: 'YS' });
  fam('H', [525], 'workEnd', { e: 100000, kw: /endurance/i });
  fam('H', [530], 'workInt', { e: 100000, kw: /intelligence/i });
  fam('H', [533], 'workMan', { e: 100000, kw: /manual/i });
  fam('H', [844], 'workMax', { e: 10000, kw: /working stat/i });
  fam('H', [4, 164, 742], 'jobPoints', { e: { 742: 10000 }, kw: /job points/i });
  // 297 is the Token Shop bar "Constellations", not a gym honor (removed in 2.0.1).
  fam('H', [240, 241, 242, 243, 497, 498, 505, 506, 550, 629, 635, 638, 640, 643, 646, 647, 679, 686, 687, 690, 694, 704, 708, 720, 721, 723], V_BS, { e: { 240: 1e6 }, kw: /gain|attain|stat|strength|defen|speed|dexterity/i });
  // ---- Honors: money, commitment, misc ----
  fam('H', [546], 'stockPayouts', { e: 100, kw: /payout/i });
  fam('H', [1005], 'stockProfits', { e: 1e9, kw: /profit/i, sel: 'money' });
  fam('H', [1006], 'stockLosses', { e: 1e9, kw: /loss/i, sel: 'money' });
  fam('H', [10], 'bankInvest', { e: 1e9, kw: /bank/i, sel: 'money', note: 'Awarded when you make the investment; holding this balance alone may not trigger it.' });
  fam('H', [239], 'bazaarCust', { e: 100, kw: /bazaar/i });
  fam('H', [268], 'pointsSold', { e: 1000, kw: /points/i });
  fam('H', [162, 163, 166], 'daysMarried', { e: { 163: 250, 162: 750, 166: 1500 }, kw: /married/i });
  fam('H', [245], 'activityH', { e: 1000, kw: /hour/i });
  fam('H', [873], 'loginStreak', { e: 100, kw: /day/i, note: 'Uses your current daily-login streak.' });
  fam('H', [13, 18, 259, 264, 265], 'level', { e: { 18: 10 }, kw: /level/i, sel: 'last' });
  fam('H', [229, 606, 614], 'totalAwards', { e: { 229: 250 }, kw: /award/i });
  fam('H', [572], 'racingSkill', { e: 10, kw: /racing skill|driver skill/i });
  fam('H', [581], 'racingPts', { e: 2500, kw: /racing points/i });
  fam('H', [571], 'racesWon', { e: 100, kw: /race/i });
  fam('H', [274], 'carWins', { e: 250, kw: /single car|same car/i, ev: 'YS' });
  fam('H', [266], 'refE', { e: 250, kw: /energy/i, sel: 'last' });
  fam('H', [566], 'refN', { e: 250, kw: /nerve/i, sel: 'last' });
  fam('H', [334], 'refT', { e: 250, kw: /token|casino/i, sel: 'last' });
  fam('H', [244, 607, 620], 'perks', { e: { 607: 50, 244: 100, 620: 150 }, kw: /perk/i, partial: 'Perk count = all perk lists returned by the API (YATA method).' });
  fam('H', [617], 'meritMax', { t: 10, kw: /merit/i, note: 'A merit upgrade maxes out at level 10.' });
  fam('H', [700], 'hofBest', { e: 250, kw: /hall of fame/i });
  fam('H', [664], 'contracts', { e: 1000, kw: /contract/i });
  fam('H', [636], 'credits', { e: 10000, kw: /credit/i });
  // ---- Honors: Crimes 2.0 skills and offenses ----
  [[1014, 'search_for_cash'], [1025, 'bootlegging'], [1029, 'shoplifting'], [1034, 'graffiti'], [1053, 'card_skimming'], [1064, 'burglary'], [1078, 'pickpocketing'], [1083, 'hustling'], [1104, 'disposal'], [1118, 'cracking'], [1130, 'forgery'], [1277, 'scamming']]
    .forEach(r => fam('H', [r[0]], 'sk_' + r[1], { e: 100, kw: new RegExp(r[1].replace(/_/g, ' '), 'i') }));
  fam('H', [552], 'off_organized_crimes', { kw: /organi[sz]ed crime/i });

  // ---- Medals ----
  fam('M', range(174, 178), 'attWins', { e: { 174: 50 }, kw: /attack/i });
  fam('M', range(179, 183), 'defWins', { e: { 179: 50 }, kw: /defend/i });
  fam('M', range(184, 186), 'escapes', { e: { 184: 50 }, kw: /escape/i });
  fam('M', range(187, 189), 'foesEscaped', { e: { 187: 50 }, kw: /escape/i });
  fam('M', range(190, 194), 'streak', { e: { 190: 25 }, kw: /streak|consecutive/i });
  fam('M', range(195, 197), 'critHits', { e: { 195: 500 }, kw: /critical/i });
  fam('M', range(198, 200), 'medItems', { e: { 198: 500 }, kw: /medical/i });
  fam('M', range(201, 203), 'bounties', { e: { 201: 25 }, kw: /bount/i });
  fam('M', range(204, 206), 'cityFinds', { e: { 204: 10 }, kw: /city|items found/i });
  fam('M', range(207, 209), 'travels', { e: { 207: 25 }, kw: /travel/i });
  fam('M', range(210, 214), 'donator', { e: { 210: 30 }, kw: /donator/i });
  fam('M', range(215, 224), 'respect', { e: { 215: 100 }, kw: /respect/i });
  fam('M', [225, 226, 227, 228, 229, 230, 231, 232, 234, 235], 'ageDays', { calc: 'years', e: { 225: 1 }, kw: /year/i });
  fam('M', [26, 27, 28, 29, 108, 109, 148, 149, 150, 151], 'factionDays', { e: { 26: 100 }, kw: /faction/i, partial: 'Uses days in your current faction; since 23/06/2016 Torn also counts earlier, non-consecutive days in the same faction (Torn wiki).' });
  fam('M', [30, 31, 32, 33, 105, 106, 107], 'busts', { kw: /bust/i });
  fam('M', range(34, 53), 'level', { e: { 34: 5 }, kw: /level/i, sel: 'last' });
  fam('M', [74, 75, 76, 77, 78, 79, 80, 110, 111, 112, 113, 114, 115, 116, 156, 157, 158, 159, 160, 161, 162], 'daysMarried', { e: { 74: 50 }, kw: /married|spouse/i });
  fam('M', [89, 90, 91, 92, 93, 94, 95, 96, 236, 237, 238, 239, 240, 241], 'networth', { e: { 89: 100000 }, kw: /networth|net worth|\$[\d,]+ for /i, sel: 'money', note: 'Torn requires the networth to be held for several days.' });
  fam('M', range(1, 25), 'rankIdx', { calc: 'rank', kw: /rank/i });

  // ---- Special-condition and action awards (no numeric tracker in the API) ----
  special('H', [1012, 1031, 1032, 1038, 1054, 1076, 1097, 1106, 1129, 1136, 1166, 1243, 1229, 1328, 1349, 1218, 1241, 1284, 1028, 1271, 1326, 328, 676], 'cond');
  special('H', [26, 828, 871, 719, 230, 481, 500, 615, 608, 627, 739, 631, 317, 781, 827, 838, 843, 670, 896, 902, 414, 955, 951, 665], 'cond');
  special('H', [253, 255, 257, 475, 476, 641, 916, 256, 477, 478, 605, 488, 14, 156, 231], 'cond');
  special('H', [367, 406, 882, 743, 699, 678, 716, 717, 853, 220, 233, 234, 235, 888], 'cond');
  special('H', [3, 19, 544, 548, 545, 1007, 869, 8, 9, 258, 237, 269, 275, 276, 326, 327, 338, 427, 431, 437, 513, 519, 520, 521, 522, 523], 'cond');
  special('H', [12, 860, 845, 316], 'act');
  special('H', [213, 222, 330, 964, 966, 969, 221, 277, 226, 280, 279, 212], 'cond', { note: 'Competition or event award - only during the event.' });
  special('H', [312, 5, 167, 217, 218, 219, 246, 839, 734, 380, 395, 288, 371, 491, 851, 322, 870, 863], 'cond');
  special('H', [21], 'cond', { note: 'Racing class is not exposed by the API.' });
  [[309, 12, 25], [443, 10, 31], [459, 11, 15], [375, 1, 1], [731, 2, 14]].forEach(r => special('H', [r[0]], 'date', { m: r[1], d: r[2] }));

  // Token Shop / Points Building bars (Torn wiki "Award" page, Token Shop table). Eight of them
  // (214, 223, 224, 225, 263, 278, 306, 311) were competition-only "legacy" honors until the
  // 19/09/22 patch made them purchasable, so they are non-merit, not retired. Matched by ID
  // AND name, in case Torn's description does not mention the shop.
  const TOKEN_SHOP = new Map([[283, 'Globule'], [308, 'Retro'], [298, 'Acute'], [313, 'Serenity'], [223, 'The Socialist'], [214, 'Jack Of All Trades'],
    [318, 'Futurity'], [297, 'Constellations'], [281, 'Parallel'], [215, 'Labyrinth'], [315, 'Glimmer'], [224, 'Proven Capacity'], [225, 'Master Of One'],
    [278, 'Globally Effective'], [321, 'Supernova'], [294, 'Pepperoni'], [284, 'Electric Dream'], [306, 'Resistance'], [311, 'Brainz'], [263, 'Survivor'],
    [730, 'Backdrop'], [729, 'Hairy']]);
  // Zero circulation alone is not evidence that an award is unreleased. An award is treated as
  // "future" only when Torn's own description says so, or when its ID is listed here together
  // with the evidence (none known as of 2026-10-10).
  const FUTURE_IDS = new Map();
  const FUTURE_RE = /\b(?:coming soon|not (?:yet )?(?:available|released|obtainable)|unreleased)\b/i;
  const REG_CONFLICTS = [];
  TOKEN_SHOP.forEach((name, id) => { if (REG.has('H:' + id)) REG_CONFLICTS.push('H:' + id + ' is the Token Shop bar "' + name + '" but has a tracker'); });

  // Rough effort models for Quick Wins (labelled estimates, minutes per unit).
  const EFFORT = {
    drug_cannabis: [75, 'avg Cannabis cooldown'], drug_ecstasy: [210, 'avg Ecstasy cooldown'], drug_ketamine: [55, 'avg Ketamine cooldown'],
    drug_lsd: [425, 'avg LSD cooldown'], drug_opium: [215, 'avg Opium cooldown'], drug_shrooms: [210, 'avg Shrooms cooldown'],
    drug_speed: [301, 'avg Speed cooldown'], drug_pcp: [330, 'avg PCP cooldown'], drug_xanax: [420, 'avg Xanax cooldown'], drug_vicodin: [300, 'avg Vicodin cooldown'],
    blood: [60, '1 bag per hour'], candy: [30, '30 min booster cooldown each'], alcohol: [60, '1 h booster cooldown each'],
    eDrinks: [120, '2 h booster cooldown each'], books: [31 * 1440, '~31 days per book'],
    attWins: [50, '25 energy per win at 720 natural energy/day'], busts: [25, '5 nerve per bust at 100% success'],
    refE: [1440, 'one refill per day'], refN: [1440, 'one refill per day'], refT: [1440, 'one refill per day'],
    donator: [1440, 'calendar days'], loginStreak: [1440, 'calendar days'], daysMarried: [1440, 'calendar days'],
    factionDays: [1440, 'calendar days'], ageDays: [1440, 'calendar days'],
    c_mexico: [52, 'round trip'], c_cayman_islands: [70, 'round trip'], c_canada: [82, 'round trip'], c_hawaii: [268, 'round trip'],
    c_united_kingdom: [318, 'round trip'], c_argentina: [334, 'round trip'], c_switzerland: [350, 'round trip'], c_japan: [450, 'round trip'],
    c_china: [484, 'round trip'], c_united_arab_emirates: [542, 'round trip'], c_south_africa: [594, 'round trip']
  };
  const QUICK_ACTIONS = { 'H:12': [5, 'invest any amount in the City Bank'], 'H:845': [5, 'read a chronicle'], 'H:860': [10, 'lease a spare property'], 'H:230': [30, 'beat someone displaying the honor'], 'H:639': [20, 'assist in an attack'] };

  /* =================== 9b. VALIDATION SNAPSHOT (generated - do not edit) =================== */
  // Built by audit/gen-valid.js (2026-10-10) from: the Torn wiki "Award" page (raw wikitext), Torn API
  // name/description copies in YATA's awards code (dated by git blame) and TornTools' explicit award
  // goals (2026-10-07). Honors are keyed by ID, medals by name (the reference tables give no medal
  // IDs). Format: "stat:record^record;..." with honor records "ID|name[~alt]|target" and medal
  // records "name|target". Progress is "Verified" only when Torn's live name, wording and target
  // also match this snapshot. Names for honors 34, 40, 165, 242, 243 and medal 177 come
  // from Torn's live catalogue (in-app diagnostics, 2026-10-10); the reference names stay accepted.
  const VALID_DATE = '2026-10-10';
  const VALID_H = new Map();
  const VALID_M = new Map();
  (function () {
    const H = "attWins:39|Woodland Camo|5^40|Desert Camo~Desert Storm Camo|20^41|Urban Camo|50^42|Arctic Camo|100^43|Fall Camo|250^44|Yellow Camo|500^45|Digital Camo" +
      "|1000^46|Red Camo|2000^47|Blue Camo|3000^48|Orange Camo|4000^49|Pink Camo|5000;fh_mechanical:28|Machinist|100;fh_heavy_artillery:141|Stumped|100;fh_cl" +
      "ubbing:142|Axe Wound|100;fh_temporary:143|Pin Puller|100;fh_machine_guns:144|Lend A Hand|100;fh_pistols:145|Yours Says Replica...|100;fh_rifles:146|28" +
      "00 Ft/S|100;fh_shotguns:147|Cartridge Packer|100;fh_sub_machine_guns:148|Act of Faith|100;fh_piercing:149|The Stabbist|100;fh_slashing:150|Slasher|100" +
      ";fh_hand_to_hand:515|Unarmed|100;:611|War Machine|1000^228|007|1000+1000^53|Biology Bachelor|^54|Business Bachelor|^55|Combat Bachelor|^56|ICT Bachelo" +
      "r|^57|Defense Bachelor|^58|General Bachelor|^59|Fitness Bachelor|^60|History Bachelor|^61|Law Bachelor|^62|Mathematics Bachelor|^63|Psychology Bachelo" +
      "r|^64|Sports Bachelor|;streak:15|Kill Streaker 1|10^16|Kill Streaker 2|100^17|Kill Streaker 3|500;critHits:20|Precision|25^227|50cal|1000;defWins:22|S" +
      "elf Defense|50;stealth:27|Night Walker|100;dmgBest:740|Devastation|5000^741|Obliteration|10000^786|Annihilation|15000;dmgTotal:1001|Boom!|10000000^100" +
      "2|Bam!|1000000^1003|Kapow!|100000000^1004|Wham!|100000;unarmored:763|Bare|250;rounds:140|Spray And Pray|1000^151|Two Halves Make A Hole|10000^834|Lead" +
      " Salad|100000^836|Peppered|1000000;ammoSpecial:800|Surplus|100^793|Bandolier|1000^791|Quartermaster|10000;ammoHollow:942|Maimed|2500;ammoPiercing:943|" +
      "Penetrated|2500;ammoIncendiary:944|Scorched|2500;ammoTracer:945|Marked|2500;bounties:232|Bounty Hunter|250;bountyValue:236|Dead Or Alive|10000000;larg" +
      "estMug:247|Blood Money|1000000;stalemates:270|Deadlock|100;assists:490|Sidekick|250^639|Double Dragon|1;ohk:517|Pressure Point|100^254|Flatline|1;hits" +
      ":601|Fury|10000;weaponsMaxed:778|Specialist|25;abroadWins:846|International|100;travels:11|Mile High Club|100^165|There And Back Again~There And Back|" +
      "1000;airDays:549|Tourist|7^557|Globetrotter|365^567|Frequent Flyer|31;c_argentina:130|Maradona|50;c_mexico:131|Cascado|50;c_united_arab_emirates:132|L" +
      "and Of Promise|50;c_hawaii:133|Hula|50;c_japan:134|The Rising Sun|50;c_united_kingdom:135|British Pride|50;c_south_africa:136|Cape Town|50;c_switzerla" +
      "nd:137|Like The Celebs|50;c_china:138|Year Of The Dragon|50;c_canada:139|Toronto|50;c_cayman_islands:272|Shark Bait|50;imports:541|Mule|100^542|Smuggl" +
      "er|1000^543|Trafficker|10000;huntSkill:50|Zebra Skin|50^51|Leopard Skin|75^52|Tiger Skin|100;drug_cannabis:29|Who's Frank?|50;drug_ecstasy:30|Party An" +
      "imal|50;drug_ketamine:31|Horse Tranquilizer|50;drug_lsd:32|Acid Dream|50;drug_opium:33|The Fields Of Opium|50;drug_shrooms:34|I See Dead People~I Thin" +
      "k I See Dead People|50;drug_speed:35|Crank It Up|50;drug_pcp:36|Angel Dust|50;drug_xanax:37|Free Energy|50;drug_vicodin:38|Painkiller|50;busts:248|Bar" +
      " Breaker|1000^249|Aiding And Abetting|2500^250|Don't Drop It|10000;bails:252|Freedom Isn't Free|500;jailed:906|Repeat Offender|250;hospitalized:903|Bo" +
      "oboo|250;revives:23|Florence Nightingale|500^267|Second Chance|1000;blood:398|Anaemic|1000^418|Transfusion|250;medItems:7|Magical Veins|5000;cityFinds" +
      ":1|I'm Watching You|50;dumpFinds:238|Optimist|1000;trashed:271|Eco Friendly|5000;auctions:273|Bargain Hunter|10;viruses:216|Silicon Valley|100;statEnh" +
      ":527|Worth It|1;alcohol:534|Alcoholic|500;candy:537|Diabetic|500;eDrinks:538|Sodaholic|500;books:539|Bibliophile|10;courses:651|Wise Guy|50^653|Smart " +
      "Alec|10^656|Whiz Kid|100^659|Clever Dick|25;workEnd:525|Tireless|100000;workInt:530|Talented|100000;workMan:533|Tough|100000;workMax:844|Worker Bee|10" +
      "000;jobPoints:4|Intern|100^164|Stuck In a Rut|1000^742|Overtime|10000;bsDef:240|Behemoth|1000000^497|Reinforced|10000000^498|Shielded|1000000000^640|B" +
      "ulletproof|100000000;bsDex:241|Draco|1000000^629|Alpinist|100000000^635|Freerunner|10000000^638|Funambulist|1000000000;bsSpd:242|Supersonic|1000000^50" +
      "5|Turbocharged|10000000^506|Lightspeed|100000000^550|Arrowshot|1000000000;bsStr:243|Abaddon|1000000^643|Powerhouse|10000000^646|Mighty Roar|100000000^" +
      "647|Well Built|1000000000;bsTotal:679|Pumped|100000000^686|Healthy|10000^687|Lean|100^690|Ripped|10000000000^694|Athletic|1000000^704|Shredded|1000000" +
      "00000^708|Conditioned|10000000^720|Fit|1000^721|Jacked|1000000000^723|Toned|100000;stockPayouts:546|Dividend|100;stockProfits:1005|Bullish|1000000000;" +
      "stockLosses:1006|Bearish|1000000000;bankInvest:10|Green Green Grass|1000000000;bazaarCust:239|Middleman|100;pointsSold:268|Wholesaler|1000;daysMarried" +
      ":162|Chasm|750^163|Fascination|250^166|Stairway To Heaven|1500;activityH:245|Couch Potato|1000;loginStreak:873|Welcome|100;level:13|The Beautiful City" +
      "|75^18|Another Brick In The Wall|10^259|Half Way There|50^264|The Whole Nine Yards|100^265|To The Limit|100;totalAwards:229|Seeker|250^606|Decorated|1" +
      "00^614|Honored|500;racingSkill:572|Motorhead|10;racingPts:581|On Track|2500;racesWon:571|Checkered Past~Chequered Past|100;carWins:274|Redline|250;ref" +
      "E:266|Energize|250;refN:566|You've Got Some Nerve|250;refT:334|Compulsive|250;perks:244|Web of Perks|100^607|Buffed|50^620|OP|150;meritMax:617|10-stac" +
      "k|10;hofBest:700|Leaderboard|250;contracts:664|Mercenary|1000;credits:636|Task Master|10000;sk_search_for_cash:1014|Pay Dirt|100;sk_bootlegging:1025|B" +
      "ox Office|100;sk_shoplifting:1029|Retail Therapy|100;sk_graffiti:1034|Let Us Spray|100;sk_card_skimming:1053|King PIN|100;sk_burglary:1064|Breaking an" +
      "d Entering|100;sk_pickpocketing:1078|Pocketeer|100;sk_hustling:1083|Crowd Teaser|100;sk_disposal:1104|Trash Bandit|100;sk_cracking:1118|Cryptographer|" +
      "100;sk_forgery:1130|Documented Success|100;sk_scamming:1277|Alpha Mail|100;off_organized_crimes:552|Mastermind|100";
    const M = "attWins:Anti Social|50^Happy Slapper|250^Scar Maker|500^Tooth and Nail|2500^Somebody Call 911|10000;defWins:Bouncer|50^Brick wall|250^Turtle|500^Solid" +
      " as a Rock|2500^Fortress|10000;escapes:Close escape|50^Blind Judgement|250^Overzealous|1000;foesEscaped:Ego Smashing|50^Underestimated|250^Run Forrest" +
      " Run|1000;streak:Strike|25^Barrage|50^Skirmish|100^Blitzkrieg|250^Onslaught|500;critHits:Boom Headshot|500^Pwned in the face|2500^Lee Harvey Oswald|10" +
      "000;medItems:Pin Cushion|500^Painkiller Abuse|5000^Attention Seeker|25000;bounties:Hired Gun|25^Bone Collector|100^The Fett|500;cityFinds:Watchful|10^" +
      "Finders Keepers|50^Eagle Eye|100;travels:Frequent Flyer|25^Jetlagged|100^Mile High Club|500;donator:Citizenship|30^Devoted|100^Diligent|250^Valiant|50" +
      "0^Patriotic|1000;respect:Recruit|100^Associate|500^Picciotto|1000^Soldier|2500^Capo|5000^Contabile|10000^Consigliere|25000^Underboss|50000^Boss|75000^" +
      "Boss Of All Bosses|100000;ageDays:One Year of Service|1^Two Years of Service|2^Three Years of Service|3^Four Years of Service|4^Five Years of Service|" +
      "5^Six Years of Service|6^Seven Years of Service|7^Eight Years of Service|8^Nine Years of Service|9^Ten Years of Service|10;factionDays:Apprentice Fact" +
      "ion Member|100^Committed Faction Member|200^Loyal Faction Member|300^Dedicated Faction Member|400^Faithful Faction Member|500^Allegiant Faction Member" +
      "|600^Devoted Faction Member|700^Dutiful Faction Member|800^Flawless Faction Member|900^Honorable Faction Member|1000;busts:Novice Buster|250^Intermedi" +
      "ate Buster|500^Advanced Buster|1000^Professional Buster|2000^Expert Buster|4000^Master Buster|6000^Guru Buster|8000;level:Level Five|5^Level Ten|10^Le" +
      "vel Fifteen|15^Level Twenty|20^Level Twenty Five|25^Level Thirty|30^Level Thirty Five|35^Level Forty|40^Level Forty Five|45^Level Fifty|50^Level Fifty" +
      " Five|55^Level Sixty|60^Level Sixty Five|65^Level Seventy|70^Level Seventy Five|75^Level Eighty|80^Level Eighty Five|85^Level Ninety|90^Level Ninety F" +
      "ive|95^Level One Hundred|100;daysMarried:Silver Anniversary|50^Ruby Anniversary|100^Sapphire Anniversary|150^Emerald Anniversary|200^Gold Anniversary|" +
      "250^Diamond Anniversary|300^Platinum Anniversary|350^Double Silver Anniversary|400^Double Ruby Anniversary|450^Double Sapphire Anniversary|500^Double " +
      "Emerald Anniversary|550^Double Gold Anniversary|600^Double Diamond Anniversary|650^Double Platinum Anniversary|700^Triple Silver Anniversary|750^Tripl" +
      "e Ruby Anniversary|800^Triple Sapphire Anniversary|850^Triple Emerald Anniversary|900^Triple Gold Anniversary|1000^Triple Diamond Anniversary|1500^Tri" +
      "ple Platinum Anniversary|2000;networth:Apprentice|100000^Entrepreneur|250000^Executive|500000^Millionaire|1000000^Multimillionaire|2500000^Capitalist|" +
      "10000000^Plutocrat|25000000^Aristocrat|100000000^Mogul|250000000^Billionaire|1000000000^Multibillionaire|2500000000^Baron|10000000000^Oligarch|2500000" +
      "0000^Tycoon|100000000000;rankIdx:Beginner|Beginner^Inexperienced|Inexperienced^Rookie|Rookie^Novice|Novice^Below Average|Below Average^Average|Average" +
      "^Reasonable|Reasonable^Above Average|Above Average^Competent|Competent^Highly Competent|Highly Competent^Veteran|Veteran^Distinguished|Distinguished^H" +
      "ighly Distinguished|Highly distinguished^Professional|Professional^Star|Star^Master|Master^Outstanding|Outstanding^Celebrity|Celebrity^Supreme|Supreme" +
      "^Idolized|Idolized^Champion|Champion^Heroic|Heroic^Legendary|Legendary^Elite|Elite^Invincible|Invincible;off_total:Trainee Troublemaker|100^Budding Ba" +
      "ndit|200^Aspiring Assailant|300^Fledgling Felon|500^Freshman Fiend|750^Despicable Deviant|1000^Conniving Culprit|1500^Sordid Sinner|2000^Polished Perp" +
      "etrator|2500^Relentless Reprobate|3000^Resolute Rogue|4000^Veteran Villain|5000^Masterful Miscreant|6000^Merciless Malefactor|7500^Legendary Lawbreake" +
      "r|10000;off_theft:Petty Pilferer|100^Crafty Crook|200^Nifty Nicker|300^Sneaky Snatcher|500^Brazen Booster|750^Stealthy Stealer|1000^Rampant Robber|150" +
      "0^Bold Burglar|2000^Invisible Intruder|2500^Lucrative Larcenist|3000^Looting Luminary|4000^Formidable Filcher|5000^Sophisticated Swiper|6000^Notorious" +
      " Nabber|7500^Prolific Plunderer|10000;off_vandalism:Sinister Scoundrel|100^Devious Delinquent|200^Rebellious Ruffian|300^Artistic Anarchist|500^Renega" +
      "de Rascal|750^Decisive Defacer|1000^Villainous Vandal|1500^Menacing Misfit|2000^Radical Rebel|2500^Urban Upsetter|3000^Malicious Maverick|4000^Reckles" +
      "s Renovator|5000^Dynamic Destructor|6000^Infernal Instigator|7500^Nefarious Nihilist|10000;off_counterfeiting:Digital Duplicator|100^Covert Copier|200" +
      "^Resourceful Replicator|300^Mimicking Maestro|500^Faux Fabricator|750^Mock Manufacturer|1000^Furtive Faker|1500^Duplicitous Designer|2000^Counterfeit " +
      "Crafter|2500^Emphatic Emulator|3000^Meticulous Maker|4000^Artificial Artisan|5000^Impeccable Imitator|6000^Bogus Buccaneer|7500^Famed Forger|10000;off" +
      "_fraud:Troublesome Trickster|100^Shameless Shyster|200^Greedy Grifter|300^Daring Deceiver|500^Provocative Persuader|750^Dexterous Defrauder|1000^Enter" +
      "prising Enticer|1500^Blackhearted Bluffer|2000^Scheming Scammer|2500^Swanky Swindler|3000^Impressive Imposter|4000^Canny Conman|5000^Frenzied Fraudste" +
      "r|6000^Bankrupting Bilker|7500^Misdirection Master|10000;off_illicit_services:Underworld Upstart|100^Murky Middleman|200^Grievous Goon|300^Heinous Hen" +
      "chman|500^Hardworking Heavy|750^Intrepid Intermediary|1000^Crooked Connector|1500^Belligerent Broker|2000^Criminal Contractor|2500^Dark Dealmaker|3000" +
      "^Lawless Liaison|4000^Clandestine Collaborator|5000^Felonious Facilitator|6000^Amoral Arbitrator|7500^Vice Vendor|10000;off_cybercrime:Web Wizard|100^" +
      "Digital Desperado|200^Tech Tinkerer|300^Virtual Virtuoso|500^Phishing Phenom|750^Network Ninja|1000^Expert Exploiter|1500^Data Dynamo|2000^Code Comman" +
      "do|2500^Online Outlaw|3000^Malware Mogul|4000^System Saboteur|5000^Heinous Hacker|6000^Backdoor Baron|7500^Byte Boss|10000;off_extortion:Budding Bully" +
      "|100^Novice Negotiator|200^Cunning Coercer|300^Professional Pressurer|500^Haughty Harasser|750^Calculating Coaxer|1000^Exceptional Extortionist|1500^P" +
      "olished Persuader|2000^Effective Enforcer|2500^Industrious Intimidator|3000^Ruthless Racketeer|4000^Ominous Oppressor|5000^Vindictive Victimizer|6000^" +
      "Master Manipulator|7500^Tyrannical Terrorizer|10000;off_illegal_production:Grass Grower|100^Dope Developer|200^Seedy Supplier|300^Blackmarket Botanist" +
      "|500^Narcotics Nurturer|750^Revered Refiner|1000^Forbidden Fabricator|1500^Back-alley Builder|2000^Contraband Creator|2500^Covert Craftsman|3000^Illic" +
      "it Innovator|4000^Prohibited Producer|5000^Workshop Wizard|6000^Synthetic Scientist|7500^Production Prodigy|10000";
    const val = s => (s === '' ? null : (s.indexOf('+') !== -1 ? s.split('+').map(Number) : (/^\d+$/.test(s) ? Number(s) : s)));
    const each = (src, fn) => src.split(';').forEach(g => { const i = g.indexOf(':'); g.slice(i + 1).split('^').forEach(r => fn(g.slice(0, i) || null, r.split('|'))); });
    each(H, (stat, f) => { const n = f[1].split('~'); VALID_H.set(Number(f[0]), { name: n[0], names: n.map(normName), t: val(f[2]), stat }); });
    each(M, (stat, f) => VALID_M.set(normName(f[0]), { name: f[0], t: val(f[1]), stat }));
  })();

  /* ============================ 10. STAT COLLECTION ============================ */
  const SEL_LABEL = { personalstats: 'Personal stats', battlestats: 'Battle stats', skills: 'Skills', profile: 'Profile', faction: 'Faction', workstats: 'Working stats', education: 'Education', merits: 'Merits', perks: 'Perks', weaponexp: 'Weapon experience', hof: 'Hall of Fame', enlistedcars: 'Enlisted cars', honors: 'Your honors', medals: 'Your medals' };
  const SEL_ACCESS = { battlestats: 'Limited', personalstats: 'Public (private stats need Limited)', honors: 'Minimal', skills: 'Minimal', workstats: 'Minimal', education: 'Minimal', merits: 'Minimal', perks: 'Minimal', weaponexp: 'Minimal', enlistedcars: 'Minimal', medals: 'Public', profile: 'Public', faction: 'Public', hof: 'Public' };

  function selFailure(sel, D) {
    const s = D.src[sel];
    if (!s) return { why: (SEL_LABEL[sel] || sel) + ' not loaded' };
    if (s.ok) return null;
    const e = s.err || {};
    if (e.code === 16) return { why: (SEL_LABEL[sel] || sel) + ' needs a ' + (SEL_ACCESS[sel] || 'higher') + ' access key', perm: true };
    return { why: (SEL_LABEL[sel] || sel) + ' request failed (' + (e.msg || 'error') + ')' };
  }
  const STAT_FNS = {
    bsTotal(d, D) {
      const b = D.sel.battlestats;
      if (b) return { ok: true, v: b.strength + b.defense + b.speed + b.dexterity };
      const ps = D.sel.personalstats;
      const parts = ['strength', 'defense', 'speed', 'dexterity'].map(k => getPath(ps || {}, 'battle_stats.' + k));
      if (parts.every(g => g.found && isNum(g.value))) return { ok: true, v: parts.reduce((s, g) => s + g.value, 0), via: 'personalstats' };
      const f = selFailure('battlestats', D);
      return { ok: false, why: f ? f.why : 'Battle stats not returned', perm: f ? f.perm : false };
    },
    rank(pr) { const i = rankIndex(pr.rank); return i < 0 ? { ok: false, why: 'Rank not recognised: ' + str(pr.rank) } : { ok: true, v: i }; },
    married(pr) {
      const sp = pr.spouse;
      if (sp == null) return { ok: true, v: 0, note: 'not married' };
      if (str(sp.status).toLowerCase() === 'engaged') return { ok: true, v: 0, note: 'engaged, not married' };
      return isNum(sp.days_married) ? { ok: true, v: sp.days_married } : { ok: false, why: 'Days married not returned' };
    },
    faction(fa) { if (fa == null) return { ok: true, v: 0, note: 'not in a faction' }; return isNum(fa.days_in_faction) ? { ok: true, v: fa.days_in_faction } : { ok: false, why: 'Days in faction not returned' }; },
    workMax(ws) { const v = ['manual_labor', 'intelligence', 'endurance'].map(k => ws[k]); return v.every(isNum) ? { ok: true, v: Math.max.apply(null, v) } : { ok: false, why: 'Working stats incomplete' }; },
    courses(ed) { return { ok: true, v: ed.complete.length }; },
    meritMax(me) { return Array.isArray(me.upgrades) ? { ok: true, v: me.upgrades.reduce((m, u) => Math.max(m, isNum(u && u.level) ? u.level : 0), 0) } : { ok: false, why: 'Merit upgrades missing' }; },
    perks(pk) { let n = 0; Object.keys(pk).forEach(k => { if (Array.isArray(pk[k])) n += pk[k].length; }); return { ok: true, v: n }; },
    weaponsMaxed(we) { return { ok: true, v: we.filter(w => w && isNum(w.exp) && w.exp >= 100).length }; },
    hofBest(hf) {
      let best = null;
      Object.keys(hf).forEach(k => { const r = hf[k] && hf[k].rank; if (isNum(r) && r > 0 && (best == null || r < best)) best = r; });
      return best == null ? { ok: false, why: 'No Hall of Fame ranks returned' } : { ok: true, v: best };
    },
    carWins(cars) { return { ok: true, v: cars.reduce((m, c) => Math.max(m, isNum(c && c.races_won) ? c.races_won : 0), 0) }; }
  };

  function readStat(def, data, D) {
    if (def.fn) return STAT_FNS[def.fn](data, D);
    if (def.crimes2) {
      const ver = data.crimes && data.crimes.version;
      if (ver && ver !== 'v2') return { ok: false, why: 'Your personal stats report Crimes ' + ver };
    }
    if (def.sum) {
      const g = def.sum.map(p => getPath(data, p));
      if (g.every(x => x.found && isNum(x.value))) return { ok: true, v: g.reduce((s, x) => s + x.value, 0) };
      return { ok: false, why: 'Part of this statistic was not returned' };
    }
    const g = getPath(data, def.path);
    const n = g.found && g.value != null && g.value !== '' ? Number(g.value) : NaN;
    if (isNum(n)) return { ok: true, v: (def.abs ? Math.abs(n) : n) * (def.scale || 1) };
    if (def.src === 'ps' && PS_PRIVATE.some(p => def.path.indexOf(p) === 0)) return { ok: false, why: 'Private stat not returned - needs a Limited or Full access key', perm: true };
    return { ok: false, why: 'Not returned by the API (' + def.path + ')' };
  }

  function statValue(key, D) {
    const def = STATS[key];
    if (!def) return { ok: false, why: 'Unknown statistic ' + key };
    const sel = SRC_SEL[def.src];
    const data = D.sel[sel];
    let r = null;
    if (data !== undefined) r = readStat(def, data, D);
    if (r && r.ok) return r;
    if (def.alt) {
      const alt = D.sel[SRC_SEL[def.alt[0]]];
      if (alt !== undefined) { const g = getPath(alt, def.alt[1]); if (g.found && isNum(g.value)) return { ok: true, v: g.value, via: SRC_SEL[def.alt[0]] }; }
    }
    if (r) return r;
    if (def.fn === 'bsTotal') return STAT_FNS.bsTotal(null, D);
    const f = selFailure(sel, D);
    return { ok: false, why: f ? f.why : 'Data not loaded', perm: f ? f.perm : false };
  }
  function crimesVersion(D) {
    const ps = D.sel.personalstats;
    const v = ps && ps.crimes && ps.crimes.version;
    return v === 'v1' || v === 'v2' ? v : null;
  }

  /* =========================== 11. PROGRESS ENGINE =========================== */
  // Progress states: verified, partial, unverified and inferred show numbers; mismatch is shown
  // as "Needs review"; special/date/unavailable/unmapped show no numbers.
  const MEASURED = ['verified', 'partial', 'inferred', 'unverified'];
  function pickVariant(list, text) {
    const hits = list.filter(v => v[0].test(text) && !(v[2] && v[2].test(text))).map(v => v[1]);
    const uniq = hits.filter((x, i) => hits.indexOf(x) === i);
    return uniq.length === 1 ? uniq[0] : null;
  }
  function expectedFor(entry, id) { return entry.e == null ? null : (isNum(entry.e) ? entry.e : (entry.e[id] != null ? entry.e[id] : null)); }
  // Target check. `exp` is the validated target from the snapshot (or, for IDs not in it, the
  // registry's research value); `live` is the number Torn's current description states. A live
  // number that disagrees is never used silently: it comes back as 'changed' and the caller marks
  // the award "Needs review".
  function resolveThreshold(entry, a, sel, exp) {
    const live = pickNumber(extractNumbers(a.desc), sel != null ? sel : entry.sel);
    if (exp === undefined || exp === null) exp = entry.t != null ? entry.t : expectedFor(entry, a.id);
    if (exp != null) {
      if (live == null) return { ok: true, t: exp, src: 'registry', exp };
      if (live === exp) return { ok: true, t: exp, src: 'confirmed', exp, live };
      return { ok: true, t: live, src: 'changed', exp, live };
    }
    if (live == null || !(live > 0)) return { ok: false, why: 'No numeric requirement in the official description' };
    return { ok: true, t: live, src: 'official', live };
  }
  const changedWhy = (thr, snap) => 'Torn\'s description now says ' + fmtNum(thr.live) + ', but the ' + (snap ? 'verified' : 'registry') + ' target is ' + fmtNum(thr.exp) + '.';
  function measure(cur, tgt, def) {
    if (def && def.lower) { const reached = cur > 0 && cur <= tgt; return { cur, tgt, rem: reached ? 0 : cur - tgt, pct: null, reached, lower: true }; }
    const reached = cur >= tgt;
    return { cur, tgt, rem: reached ? 0 : tgt - cur, pct: tgt > 0 ? Math.min(100, (cur / tgt) * 100) : 0, reached };
  }
  function thrNote(thr, hasSnap) {
    if (thr.src === 'registry') return 'Torn\'s description states no number; target taken from ' + (hasSnap ? 'the validation snapshot.' : 'the internal registry.');
    if (thr.src === 'official') return 'Target read from Torn\'s current description; not independently validated.';
    return '';
  }
  const joinNotes = function () { return Array.prototype.filter.call(arguments, Boolean).join(' '); };
  // Validation snapshot (section 9b): honors are matched by ID, medals by name (the reference
  // tables give no medal IDs).
  function snapshotFor(a) { return a.k === 'H' ? (VALID_H.get(a.id) || null) : (VALID_M.get(normName(a.name)) || null); }
  const statName = k => (STATS[k] ? STATS[k].label : k);

  function nextDate(m, d, now) {
    const n = new Date(now);
    let t = Date.UTC(n.getUTCFullYear(), m - 1, d);
    const today = Date.UTC(n.getUTCFullYear(), n.getUTCMonth(), n.getUTCDate());
    if (t < today) t = Date.UTC(n.getUTCFullYear() + 1, m - 1, d);
    return { at: t, days: Math.round((t - today) / DAY_MS) };
  }
  const MONTHS = ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec'];
  const MONTHS_LONG = ['january', 'february', 'march', 'april', 'may', 'june', 'july', 'august', 'september', 'october', 'november', 'december'];

  // Calendar anniversary of the sign-up time (UTC = Torn time). Date.UTC rolls 29 February
  // over to 1 March in non-leap years.
  function anniversary(signedUpMs, years) {
    const s = new Date(signedUpMs);
    const at = Date.UTC(s.getUTCFullYear() + years, s.getUTCMonth(), s.getUTCDate(), s.getUTCHours(), s.getUTCMinutes(), s.getUTCSeconds());
    return { at, days: Math.round((at - signedUpMs) / DAY_MS) };
  }
  // Age medals ("Live in Torn for N years"). Torn does not document whether it counts N x 365
  // elapsed days or the calendar anniversary of the sign-up date (N x 365 plus any 29 Februaries),
  // so both figures are kept and "reached" waits for the later one, the calendar anniversary.
  function ageProgress(base, years, D, now, st) {
    const def = { label: 'days in Torn', kind: 'time' };
    const pr = D.sel.profile;
    const days365 = years * 365;
    if (!pr) { const f = selFailure('profile', D); return Object.assign(base, { st: 'unavailable', why: f ? f.why : 'Profile not loaded', perm: f && f.perm, statKey: 'ageDays', tgt: days365, unit: def }); }
    const age = isNum(pr.age) ? pr.age : null;
    const su = isNum(pr.signed_up) && pr.signed_up > 0 ? pr.signed_up * 1000 : null;
    if (su == null) {
      if (age == null) return Object.assign(base, { st: 'unavailable', why: 'Account age not returned', statKey: 'ageDays', tgt: days365, unit: def });
      return Object.assign(base, measure(age, days365, def), { st, statKey: 'ageDays', unit: def, kind: 'time', years,
        note: joinNotes(base.note, 'Sign-up date not returned, so this counts ' + years + ' x 365 days; the calendar anniversary can be up to ' + Math.ceil(years / 4) + ' day(s) later.') });
    }
    const an = anniversary(su, years);
    const cur = age != null ? age : Math.floor((now - su) / DAY_MS);
    const reached = now >= an.at;
    const pct = reached ? 100 : Math.max(0, Math.min(99.99, ((now - su) / (an.at - su)) * 100));
    const left = reached ? 0 : Math.ceil((an.at - now) / DAY_MS);
    const anniv = { years, date: fmtDate(an.at), signup: fmtDate(su), days: an.days, days365, leap: an.days - days365, left365: Math.max(0, days365 - cur), feb29: new Date(su).getUTCMonth() === 1 && new Date(su).getUTCDate() === 29 };
    return Object.assign(base, { st, statKey: 'ageDays', unit: def, kind: 'time', cur, tgt: an.days, rem: left, pct, reached, anniv,
      note: joinNotes(base.note, 'Torn does not document whether it counts ' + years + ' x 365 days (' + fmtNum(days365) + ') or the calendar anniversary (' + fmtNum(an.days) + ' days); progress follows the calendar date, which is never earlier.' + (anniv.feb29 ? ' You signed up on 29 February; the anniversary is taken as 1 March in non-leap years.' : '')) });
  }

  function medalTypeRule(a) {
    if (a.cat === 'level') return { stat: 'level', kw: /level/i, sel: 'last', ev: 'T' };
    if (a.cat === 'networth') return { stat: 'networth', kw: /networth/i, sel: 'money', ev: 'T', note: 'Torn requires the networth to be held for several days.' };
    if (a.cat === 'rank') return { stat: 'rankIdx', calc: 'rank', kw: /rank/i, ev: 'T' };
    if (a.cat === 'crime' && a.cv === 'v2') return { stat: V_OFF, kw: /offen[cs]e|crime/i, ev: 'T' };
    return null;
  }
  // Medals the snapshot validates by name but neither the registry nor the type rules above match:
  // Torn's type / crimes_version data does not mark every one (the live catalogue of 2026-10-10 did
  // not mark the 15 total-offense medals). They are mapped to the snapshot's statistic; the wording
  // guard and target check still apply, and classification (crimes_version included) is unchanged.
  function snapshotRule(a) {
    const s = VALID_M.get(normName(a.name));
    if (!s || !s.stat || !STATS[s.stat]) return null;
    let tpl = null;
    REG.forEach(e => { if (!tpl && e.kind === 'M' && !e.sp && e.stat === s.stat) tpl = e; });
    if (tpl) return { stat: s.stat, calc: tpl.calc, sel: tpl.sel, kw: tpl.kw, partial: tpl.partial, note: tpl.note, ev: 'V' };
    if (s.stat.indexOf('off_') === 0) return { stat: s.stat, kw: /offen[cs]e|crime/i, ev: 'V' };
    return null;
  }
  const INFER = [
    [/^achieve a skill level of [\d,.]+ in /i, V_SKILL], [/^(?:use|take) [\d,]+ \w+$/i, V_DRUG],
    [/^(?:win|achieve) [\d,]+ attacks?$/i, 'attWins'], [/^travel to .+ [\d,]+ times$/i, V_COUNTRY, 'last'],
    [/^reach level [\d,]+$/i, 'level', 'last'], [/^achieve [\d,]+ finishing hits with /i, V_FH],
    [/^(?:gain|attain) [\d,]+ (?:strength|defen[cs]e|speed|dexterity|total stats)$/i, V_BS],
    [/^commit [\d,]+ [a-z ]*offen[cs]es$/i, V_OFF]
  ];
  const MONTH_RE = /\bon (january|february|march|april|may|june|july|august|september|october|november|december) (\d{1,2})(?:st|nd|rd|th)?\b/i;
  function inferTemplate(a) {
    for (let i = 0; i < INFER.length; i++) if (INFER[i][0].test(a.desc)) return { stat: INFER[i][1], sel: INFER[i][2], ev: 'I' };
    const md = MONTH_RE.exec(a.desc);
    if (md) return { sp: 'date', m: MONTHS_LONG.indexOf(md[1].toLowerCase()) + 1, d: Number(md[2]), ev: 'I' };
    // No number at all in Torn's wording means there is nothing to count.
    if (a.desc && !/\d/.test(a.desc)) return { sp: 'cond', ev: 'I', note: 'Not in the registry; Torn states no numeric target, so it is treated as a condition.' };
    return null;
  }

  function finalize(base, m, def, statKey, entry, extra) {
    const p = Object.assign(base, m, { statKey, unit: def, kind: def.kind });
    p.st = extra.st;
    p.note = joinNotes(base.note, entry.partial, p.st === 'unverified' ? base.vwhy : '', extra.note, def.kind === 'inst' && !entry.note ? 'Current value; reaching the target now does not guarantee the award.' : '');
    return p;
  }

  function computeProgress(a, D, cat, S, now) {
    let entry = REG.get(a.k + ':' + a.id) || null;
    let source = entry ? 'registry' : '';
    if (!entry && a.k === 'M') { entry = medalTypeRule(a); if (entry) source = 'type'; }
    if (!entry && a.k === 'M') { entry = snapshotRule(a); if (entry) source = 'snapshot'; }
    if (!entry && S.inferred) { entry = inferTemplate(a); if (entry) source = 'inferred'; }
    if (!entry) return { st: 'unmapped' };
    if (entry.sp === 'date') {
      const nd = nextDate(entry.m, entry.d, now);
      return { st: 'date', sp: 'date', ev: entry.ev, days: nd.days, note: 'Log in on ' + entry.d + ' ' + MONTHS[entry.m - 1] + ' (Torn time) - ' + (nd.days === 0 ? 'today!' : 'in ' + nd.days + ' day' + (nd.days === 1 ? '' : 's')) + '.' };
    }
    if (entry.sp) return { st: 'special', sp: entry.sp, ev: entry.ev, note: entry.note || '' };
    const review = why => ({ st: 'mismatch', ev: entry.ev, why });
    if (entry.kw && !entry.kw.test(a.desc)) return review('Torn\'s description no longer matches the statistic mapped to this award.');
    const snap = source === 'inferred' ? null : snapshotFor(a);
    // An honor ID whose live name differs from the verified one may have been reused or renamed.
    if (snap && a.k === 'H' && snap.names.indexOf(normName(a.name)) === -1) return review('Torn now names award ID ' + a.id + ' "' + a.name + '", but it was verified as "' + snap.name + '".');
    const calc = entry.calc;
    const base = { ev: entry.ev, note: entry.note || '', inferred: source === 'inferred', snap: !!snap,
      vwhy: snap || source === 'inferred' ? '' : (source === 'type' ? 'Mapped from the medal type; this medal is not in the validation snapshot.' : 'This ID is in the registry but not in the validation snapshot.') };
    // The final label never claims more than the checks above support.
    const statusFor = (def, thrs) => {
      if (source === 'inferred') return 'inferred';
      if (!snap || thrs.some(t => t.src === 'official')) return 'unverified';
      if (entry.partial || (def && def.kind === 'inst') || calc === 'rank' || calc === 'years'
          || thrs.some(t => t.src === 'registry'))
        return 'partial';
      return 'verified';
    };
    const statMismatch = k => (snap && snap.stat && k && snap.stat !== k ? review('This award was verified against ' + statName(snap.stat) + ', but the registry now reads ' + statName(k) + '.') : null);

    if (calc === 'multi' || calc === 'fhAll') {
      const spec = calc === 'fhAll' ? FH.map(c => ['fh_' + c, 0]) : entry.parts;
      if (calc === 'multi' && extractNumbers(a.desc).filter(n => !n.pct).length < spec.length) return review('Expected ' + spec.length + ' requirements in Torn\'s description.');
      const parts = [];
      const thrs = [];
      let unavailable = null;
      for (let i = 0; i < spec.length; i++) {
        const exp = snap ? (Array.isArray(snap.t) ? snap.t[i] : snap.t) : undefined;
        const thr = resolveThreshold(entry, a, spec[i][1], exp);
        if (!thr.ok) return review(thr.why);
        if (thr.src === 'changed') return review(changedWhy(thr, !!snap));
        thrs.push(thr);
        const val = statValue(spec[i][0], D);
        if (!val.ok && !unavailable) unavailable = val;
        const m = val.ok ? measure(val.v, thr.t, STATS[spec[i][0]]) : null;
        parts.push(Object.assign({ statKey: spec[i][0], label: STATS[spec[i][0]].label, tgt: thr.t, ok: val.ok, why: val.ok ? '' : val.why }, m || {}));
      }
      if (unavailable) return Object.assign(base, { st: 'unavailable', why: unavailable.why, perm: unavailable.perm, parts });
      const pct = parts.reduce((s, x) => s + Math.min(1, x.cur / x.tgt), 0) / parts.length * 100;
      const reached = parts.every(x => x.reached);
      const st = statusFor(null, thrs);
      return Object.assign(base, { st, multi: true, parts, pct: reached ? 100 : Math.min(pct, 99.99), reached, rem: null, note: joinNotes(base.note, st === 'unverified' ? base.vwhy : '', calc === 'fhAll' ? 'Every category must reach the target.' : 'All requirements must be met.') });
    }

    if (calc === 'bachelor') {
      const m = /^(\w+)/.exec(a.name) || [];
      const subj = (m[1] || '').toLowerCase();
      const BACH = { biology: /biolog/i, business: /business|commerce/i, combat: /combat|military/i, ict: /\bict\b|computer/i, defense: /defen[cs]e/i, general: /general/i, fitness: /fitness|health/i, history: /histor/i, law: /\blaw\b/i, mathematics: /math/i, psychology: /psycholog/i, sports: /sport/i };
      if (!BACH[subj]) return review('Unknown bachelor subject');
      // Validate the live description confirms both the requirement type and the expected subject.
      // Without this, a renamed or repurposed award ID would still show measurable progress.
      // Torn uses two formats: "Achieve a <Subject> Bachelor of Science" (older IDs) and
      // "Complete all classes in <Subject>" (current Torn wording as of 2026). Both are accepted.
      if (!a.desc) return Object.assign(base, { st: 'unavailable', why: 'Award description missing; cannot confirm ' + subj + ' bachelor requirement.' });
      const descHasDegree = /bachelor|degree/i.test(a.desc);
      const descHasClasses = /complete all classes in/i.test(a.desc);
      if (!descHasDegree && !descHasClasses) return review('Torn\'s description does not confirm a bachelor degree or class completion; the requirement may have changed.');
      if (!BACH[subj].test(a.desc)) return review('Torn\'s description does not confirm the expected subject (' + subj + ') for this bachelor honor; the requirement may have changed.');
      if (!Array.isArray(cat.edu) || !cat.edu.length) return Object.assign(base, { st: 'unavailable', why: 'Education catalogue not loaded' });
      const cats = cat.edu.filter(c => BACH[subj].test(c.name));
      if (cats.length !== 1 || !cats[0].courses.length) return review('Could not match the ' + subj + ' course list');
      const ed = D.sel.education;
      if (!ed) { const f = selFailure('education', D); return Object.assign(base, { st: 'unavailable', why: f ? f.why : 'Education not loaded', perm: f && f.perm }); }
      const done = new Set(ed.complete.map(Number));
      const cur = cats[0].courses.filter(id => done.has(id)).length;
      const def = { label: cats[0].name + ' courses completed', kind: 'cum' };
      return finalize(base, measure(cur, cats[0].courses.length, def), def, 'courses', entry, { st: statusFor(def, []), note: 'Course list from the official education catalogue.' });
    }

    if (calc === 'rank') {
      const q = /"([^"]+)"/.exec(a.desc) || /rank of\s+(.+?)\.?$/i.exec(a.desc);
      const tIdx = q ? rankIndex(q[1]) : -1;
      if (tIdx < 1) return review('Target rank not recognised');
      const bad = statMismatch('rankIdx');
      if (bad) return bad;
      if (snap && snap.t != null && rankIndex(String(snap.t)) !== tIdx) return review('Torn\'s description now asks for "' + RANKS[tIdx] + '", but the verified target is "' + snap.t + '".');
      const val = statValue('rankIdx', D);
      if (!val.ok) return Object.assign(base, { st: 'unavailable', why: val.why, perm: val.perm });
      const def = { label: 'rank steps', kind: 'peak', rank: true };
      return finalize(base, measure(val.v, tIdx, def), def, 'rankIdx', entry, { st: statusFor(def, []), note: 'Rank is ordinal (' + RANKS[val.v] + ' -> ' + RANKS[tIdx] + '); steps are not equal in effort.' });
    }

    if (calc === 'years') {
      const bad = statMismatch('ageDays');
      if (bad) return bad;
      const thr = resolveThreshold(entry, a, null, snap ? snap.t : undefined);
      if (!thr.ok) return review(thr.why);
      if (thr.src === 'changed') return review(changedWhy(thr, !!snap));
      return ageProgress(base, thr.t, D, now, statusFor(STATS.ageDays, [thr]));
    }

    let statKey = entry.stat;
    if (Array.isArray(statKey)) { statKey = pickVariant(statKey, a.desc); if (!statKey) return review('Could not identify the statistic from Torn\'s description.'); }
    const bad = statMismatch(statKey);
    if (bad) return bad;
    const thr = resolveThreshold(entry, a, null, snap ? snap.t : undefined);
    if (!thr.ok) return review(thr.why);
    if (thr.src === 'changed') return review(changedWhy(thr, !!snap));
    const def = STATS[statKey];
    const hold = statKey === 'networth' ? /for (?:at least )?([\d,]+) days?/i.exec(a.desc) : null;
    if (hold) base.note = 'Torn requires this networth to be held for ' + hold[1] + ' days; the API only shows today\'s value.';
    const val = statValue(statKey, D);
    if (!val.ok) return Object.assign(base, { st: 'unavailable', why: val.why, perm: val.perm, statKey, tgt: thr.t, unit: def });
    return finalize(base, measure(val.v, thr.t, def), def, statKey, entry, { st: statusFor(def, [thr]), note: joinNotes(thrNote(thr, !!snap), val.note ? '(' + val.note + ')' : '', val.via ? 'Value from ' + val.via + '.' : '') });
  }

  /* ========================= 12. CLASSIFICATION + MODEL ========================= */
  function classify(a, D, ctx) {
    const earned = a.k === 'H' ? D.sel.honors : D.sel.medals;
    if (earned && earned.has(a.id)) return { cl: 'earned', ts: earned.get(a.id) };
    if (!earned) return { cl: 'unknown', why: 'Your earned ' + (a.k === 'H' ? 'honors' : 'medals') + ' could not be loaded' };
    const key = a.k + ':' + a.id;
    if (a.k === 'H' && (a.typeId === 1 || a.cat === 'default')) return { cl: 'nonmerit', why: 'Default bar, flag or memorial (type 1)' };
    if (/token shop|points building/i.test(a.desc)) return { cl: 'nonmerit', why: 'Token Shop / Points Building bar' };
    if (/^in (?:loving )?memory of\b/i.test(a.desc)) return { cl: 'nonmerit', why: 'Memorial bar' };
    if (a.k === 'H' && TOKEN_SHOP.has(a.id) && normName(TOKEN_SHOP.get(a.id)) === normName(a.name)) return { cl: 'nonmerit', why: 'Token Shop / Points Building bar (known ID ' + a.id + ')' };
    if (a.cv) {
      const uv = ctx.crimesV;
      if (uv) {
        if (a.cv !== uv)
          return { cl: 'retired', why: 'Crimes ' + (a.cv === 'v1' ? '1.0' : '2.0') +
            ' award; your account uses Crimes ' + (uv === 'v1' ? '1.0' : '2.0') };
      } else {
        return { cl: 'unknown', why: 'Crimes ' + (a.cv === 'v1' ? '1.0' : '2.0') +
          ' award \u2014 your Crimes version could not be determined' +
          ' (personal stats unavailable or did not include crimes.version)' };
      }
    }
    if (!a.name || !a.desc) return { cl: 'unknown', why: 'Missing name or description in the catalogue' };
    if ((a.k === 'H' ? HONOR_TYPES : MEDAL_TYPES).indexOf(a.cat) === -1) return { cl: 'unknown', why: 'Unrecognised award type "' + a.cat + '"' };
    if (FUTURE_IDS.has(key)) return { cl: 'future', why: 'Listed as unreleased: ' + FUTURE_IDS.get(key) };
    if (FUTURE_RE.test(a.desc)) return { cl: 'future', why: 'Torn\'s description says it is not available yet' };
    return { cl: 'obtainable', circ0: a.circ === 0 };
  }

  function estimate(it) {
    const p = it.p;
    if (!p) return null;
    const key = it.a.k + ':' + it.a.id;
    const q = QUICK_ACTIONS[key];
    if (p.st === 'date') return { min: p.days * 1440 + 1, why: 'log in on the date', cal: true };
    if (p.st === 'special') return q ? { min: q[0], why: 'one-off action: ' + q[1] } : null;
    if (MEASURED.indexOf(p.st) === -1 || p.reached || p.multi || !isNum(p.rem)) return null;
    if (q) return { min: q[0], why: 'one-off action: ' + q[1] };
    const ef = EFFORT[p.statKey];
    if (!ef) return null;
    return { min: p.rem * ef[0], why: fmtNum(p.rem) + ' x ' + fmtDuration(ef[0]) + ' (' + ef[1] + ')' };
  }

  // Live catalogue facts for diagnostics lines: type, crimes_version (for crime awards) and Torn's
  // own wording.
  const awardTag = a => {
    const s = a.k === 'M' ? VALID_M.get(normName(a.name)) : null;
    const crime = a.cv || a.typeId === 'CRM' || a.typeId === 5 || /^crimes?$/.test(a.cat) || !!(s && s.stat && s.stat.indexOf('off_') === 0);
    return '[type ' + str(a.typeId == null || a.typeId === '' ? '?' : a.typeId) + (a.cat ? ' ' + a.cat : '') +
      (crime ? ', crimes_version ' + (a.cv || 'none') : '') + '; Torn: "' + a.desc + '"]';
  };

  // Runtime registry audit against the catalogue Torn just returned (Settings > Diagnostics).
  // Every numeric registry ID is checked, earned or not; so is every medal outside the registry
  // that the snapshot validates by name (Crimes 2.0 medals and any medal Torn's type data misses).
  function registryAudit(cat, D, S, now) {
    const byKey = new Map();
    cat.honors.concat(cat.medals).forEach(a => byKey.set(a.k + ':' + a.id, a));
    const out = { checked: 0, verified: 0, partial: 0, unavailable: 0, unverified: [], review: [], missing: [], paths: [], knownUnmapped: [], dupes: REG_DUPES.slice(), conflicts: REG_CONFLICTS.slice(),
      named: { checked: 0, verified: 0, partial: 0, unavailable: 0, unverified: [], review: [], byName: [] } };
    const S0 = Object.assign({}, S, { inferred: false });
    const tally = (o, p, key, a) => {
      if (p.st === 'mismatch') o.review.push(key + ' ' + a.name + ': ' + p.why + ' ' + awardTag(a));
      else if (p.st === 'unverified') o.unverified.push(key + ' ' + a.name + ' ' + awardTag(a));
      else if (p.st === 'unavailable') o.unavailable++;
      else if (p.st === 'partial') o.partial++;
      else if (p.st === 'verified') o.verified++;
    };
    REG.forEach((e, key) => {
      if (e.sp) return;
      const a = byKey.get(key);
      if (!a) { out.missing.push(key); return; }
      out.checked++;
      tally(out, computeProgress(a, D, cat, S0, now), key, a);
    });
    cat.medals.forEach(a => {
      const s = VALID_M.get(normName(a.name));
      if (!s || REG.has('M:' + a.id)) return;
      const how = medalTypeRule(a) ? 'type' : (snapshotRule(a) ? 'name' : '');
      if (!how) { out.knownUnmapped.push('M:' + a.id + ' ' + a.name + ' (' + statName(s.stat) + ') ' + awardTag(a)); return; }
      const n = out.named;
      n.checked++;
      if (how === 'name') n.byName.push('M:' + a.id + ' ' + a.name + ' (' + statName(s.stat) + ') ' + awardTag(a));
      tally(n, computeProgress(a, D, cat, S0, now), 'M:' + a.id, a);
    });
    const ps = D.sel.personalstats;
    if (ps) {
      Object.keys(STATS).forEach(k => {
        const d = STATS[k];
        if (d.src !== 'ps') return;
        if (d.crimes2 && !(ps.crimes && ps.crimes.version === 'v2')) return;
        (d.sum || [d.path]).forEach(p => {
          if (!p || getPath(ps, p).found || PS_PRIVATE.some(x => p.indexOf(x) === 0)) return;
          if (out.paths.indexOf(p) === -1) out.paths.push(p);
        });
      });
    }
    return out;
  }

  function buildModel(cat, D, S) {
    const now = Date.now();
    const ctx = { crimesV: crimesVersion(D) };
    const items = [];
    cat.honors.concat(cat.medals).forEach(a => {
      const c = classify(a, D, ctx);
      const it = { a, cl: c.cl, clWhy: c.why || '', circ0: !!c.circ0, ts: c.ts || null, p: null, est: null };
      if (c.cl !== 'earned' && c.cl !== 'nonmerit') it.p = computeProgress(a, D, cat, S, now);
      it.est = estimate(it);
      items.push(it);
    });
    const warnings = (cat.warnings || []).slice();
    ['honors', 'medals'].forEach(k => {
      const e = D.sel[k];
      if (!e) return;
      const known = new Set((k === 'honors' ? cat.honors : cat.medals).map(x => x.id));
      let miss = 0;
      e.forEach((ts, id) => { if (!known.has(id)) miss++; });
      if (miss) warnings.push(miss + ' of your earned ' + k + ' are not in the downloaded catalogue - it may be incomplete (tap Settings > Clear cache).');
    });
    Object.keys(D.src).forEach(sel => { const f = selFailure(sel, D); if (f) warnings.push(f.why); });
    const ob = items.filter(x => x.cl === 'obtainable');
    const meas = ob.filter(x => x.p && MEASURED.indexOf(x.p.st) !== -1);
    const count = f => items.filter(f).length;
    const st = s => ob.filter(x => x.p && x.p.st === s).length;
    const summary = {
      missingH: ob.filter(x => x.a.k === 'H').length, missingM: ob.filter(x => x.a.k === 'M').length,
      trackable: meas.length, reached: meas.filter(x => x.p.reached).length,
      nearly: meas.filter(x => isNum(x.p.pct) && x.p.pct >= S.nearPct).length,
      verified: st('verified'), partial: st('partial'), inferred: st('inferred'), unverified: st('unverified'),
      special: ob.filter(x => x.p && (x.p.st === 'special' || x.p.st === 'date')).length,
      unavailable: st('unavailable'), mismatch: st('mismatch'), unmapped: st('unmapped'), circ0: ob.filter(x => x.circ0).length,
      earned: count(x => x.cl === 'earned'), retired: count(x => x.cl === 'retired'), nonmerit: count(x => x.cl === 'nonmerit'),
      future: count(x => x.cl === 'future'), unknown: count(x => x.cl === 'unknown'),
      catH: cat.honors.length, catM: cat.medals.length, crimesV: ctx.crimesV
    };
    const audit = registryAudit(cat, D, S, now);
    const nReview = audit.review.length + audit.named.review.length;
    if (nReview) warnings.push(nReview + ' award mapping' + (nReview === 1 ? '' : 's') + ' need review against Torn\'s current catalogue (Settings > Diagnostics).');
    return { items, summary, audit, warnings: warnings.filter((w, i) => warnings.indexOf(w) === i), at: D.at, catAt: cat.at, profile: D.sel.profile || null };
  }

  /* ============================== 13. EXPORTS ============================== */
  const VIEWS = [
    ['closest', 'Closest to completion'], ['quick', 'Quick wins (estimates)'], ['nearly', 'Nearly complete'],
    ['notstarted', 'Not started (genuine 0%)'], ['all', 'All obtainable missing'], ['special', 'Untrackable / special'],
    ['recent', 'Recently earned'], ['retired', 'Reference: retired / unobtainable'], ['nonmerit', 'Reference: non-merit bars'],
    ['future', 'Reference: future / unreleased'], ['unknown', 'Reference: unknown classification']
  ];
  const MEASURABLE = MEASURED;
  const isMeas = it => !!(it.p && MEASURABLE.indexOf(it.p.st) !== -1);
  const byName = (x, y) => (x.a.name || '').localeCompare(y.a.name || '') || x.a.id - y.a.id;
  const byPct = (x, y) => (y.p.reached - x.p.reached) || ((isNum(y.p.pct) ? y.p.pct : -1) - (isNum(x.p.pct) ? x.p.pct : -1)) || byName(x, y);

  function viewItems(model, view, S) {
    const all = model.items;
    const ob = all.filter(x => x.cl === 'obtainable');
    switch (view) {
      case 'closest': return ob.filter(isMeas).sort(byPct);
      case 'nearly': return ob.filter(x => isMeas(x) && isNum(x.p.pct) && x.p.pct >= S.nearPct).sort(byPct);
      case 'quick': return ob.filter(x => x.est && x.est.min <= 7 * 1440).sort((x, y) => x.est.min - y.est.min || byName(x, y));
      case 'notstarted': return ob.filter(x => isMeas(x) && !x.p.multi && !x.p.lower && x.p.cur === 0).sort(byName);
      case 'all': return ob.slice().sort((x, y) => (isMeas(y) - isMeas(x)) || (isMeas(x) ? byPct(x, y) : byName(x, y)));
      case 'special': return ob.filter(x => x.p && ['special', 'date', 'unmapped', 'mismatch'].indexOf(x.p.st) !== -1).sort(byName);
      case 'recent': return all.filter(x => x.cl === 'earned' && isNum(x.ts)).sort((x, y) => y.ts - x.ts).slice(0, 100);
      default: return all.filter(x => x.cl === view).sort(byName);
    }
  }
  function applyFilters(list, f) {
    const q = str(f.q).trim().toLowerCase();
    return list.filter(x => (f.kind === 'all' || (f.kind === 'honors' ? x.a.k === 'H' : x.a.k === 'M')) &&
      (f.cat === 'all' || x.a.cat === f.cat) &&
      (!q || (x.a.name + ' ' + x.a.desc).toLowerCase().indexOf(q) !== -1));
  }

  function unitLabel(p) { return p && p.unit && p.unit.label ? p.unit.label : ''; }
  function valText(v, p) { return p && p.unit && p.unit.rank ? RANKS[v] + ' (step ' + (v + 1) + ' of ' + RANKS.length + ')' : fmtVal(v, p && p.unit); }
  const REACHED_Q = { partial: 'partially measurable', unverified: 'unverified mapping', inferred: 'inferred mapping' };
  function statusText(it) {
    const p = it.p;
    if (!p) return '';
    if (MEASURABLE.indexOf(p.st) !== -1 && p.reached) return 'Threshold reached' + (REACHED_Q[p.st] ? ' (' + REACHED_Q[p.st] + ')' : '') + ' \u2014 award not confirmed yet';
    switch (p.st) {
      case 'verified': return 'Trackable (snapshot-validated)';
      case 'partial': return 'Trackable (partially measurable)';
      case 'unverified': return 'Trackable (unverified \u2014 ' + (p.vwhy || 'mapping not validated') + ')';
      case 'inferred': return 'Trackable (inferred \u2014 award ID not in the registry)';
      case 'special': return p.sp === 'act' ? 'Action required \u2014 no numeric tracker' : 'Special condition \u2014 numeric progress unavailable';
      case 'date': return 'Action required \u2014 no numeric tracker';
      case 'unavailable': return 'Progress temporarily unavailable \u2014 ' + (p.why || 'missing API permission/data');
      case 'mismatch': return 'Needs review \u2014 ' + (p.why || 'Torn\'s description changed');
      default: return 'No tracker mapped for this award ID';
    }
  }
  function remText(p) {
    if (p.anniv) return fmtNum(p.rem) + ' day' + (p.rem === 1 ? '' : 's') + ' to the calendar anniversary';
    return p.unit && p.unit.rank ? fmtNum(p.rem) + ' rank steps' : fmtVal(p.rem, p.unit) + ' ' + unitLabel(p);
  }
  // Age medals: the calendar anniversary and the plain 365-day count are shown separately.
  function annivLines(p) {
    const a = p.anniv;
    if (!a) return [];
    return [
      'Calendar anniversary: ' + ordinal(a.years) + ' on ' + a.date + ' TCT (signed up ' + a.signup + '; ' + fmtNum(a.days) + ' days' + (a.leap ? ', incl. ' + a.leap + ' leap day' + (a.leap === 1 ? '' : 's') : '') + ')' + (p.reached ? ' \u2014 passed' : ''),
      'Elapsed-day count: ' + fmtNum(p.cur) + ' / ' + fmtNum(a.days365) + ' days (' + a.years + ' x 365)' + (a.left365 ? ' \u2014 ' + fmtNum(a.left365) + ' left by that count' : ' \u2014 met by that count')
    ];
  }
  function progressLines(it) {
    const p = it.p;
    const L = [];
    if (!p) return L;
    if (p.multi) {
      L.push('Progress: ' + p.parts.map(x => x.label + ' ' + (x.ok ? fmtNum(x.cur) : '?') + ' / ' + fmtNum(x.tgt) + (x.ok ? (x.reached ? ' (met)' : ' (' + fmtPct(x.pct, false) + ')') : ' (unavailable)')).join('; '));
      if (MEASURABLE.indexOf(p.st) !== -1) {
        L.push('Overall: ' + fmtPct(p.pct, p.reached) + ' (all requirements must be met)');
        const rem = p.parts.filter(x => x.ok && !x.reached).map(x => fmtNum(x.rem) + ' ' + x.label);
        if (rem.length) L.push('Remaining: ' + rem.join(' + '));
      }
      return L;
    }
    if (MEASURABLE.indexOf(p.st) !== -1) {
      if (p.lower) {
        L.push('Progress: best rank #' + fmtNum(p.cur) + ' (target: top ' + fmtNum(p.tgt) + ')');
        if (!p.reached) L.push('Remaining: climb ' + fmtNum(p.rem) + ' places');
      } else {
        L.push('Progress: ' + valText(p.cur, p) + ' / ' + valText(p.tgt, p) + ' (' + fmtPct(p.pct, p.reached) + ')');
        if (!p.reached) L.push('Remaining: ' + remText(p));
        annivLines(p).forEach(x => L.push(x));
      }
    } else if (p.st === 'unavailable' && isNum(p.tgt)) {
      L.push('Target: ' + fmtVal(p.tgt, p.unit) + ' ' + unitLabel(p));
    }
    return L;
  }

  function exportText(model, list, title, scope, S) {
    const sm = model.summary;
    const pr = model.profile;
    const who = pr && pr.name ? pr.name + ' [' + pr.id + ']' : 'Unknown account';
    const now = Date.now();
    const L = [
      who + ' \u2014 ' + title,
      'Generated: ' + fmtStamp(now) + ' (device time) / ' + fmtStamp(now, true) + ' TCT',
      'Tool: Fatboy Awards Tracker v' + VERSION + ' \u00B7 Torn API v2 \u00B7 data fetched ' + fmtStamp(model.at, true) + ' TCT',
      'Scope: ' + scope,
      'Account totals: ' + sm.missingH + ' missing merit honors, ' + sm.missingM + ' missing merit medals, ' + sm.trackable + ' measurable (' + sm.verified + ' snapshot-validated, ' + sm.partial + ' partial, ' + (sm.unverified + sm.inferred) + ' unverified/inferred; ' + sm.reached + ' at threshold), ' + sm.mismatch + ' needs review, ' + sm.special + ' special/action, ' + sm.unavailable + ' data unavailable, ' + sm.unmapped + ' without a tracker',
      'This list: ' + list.length + ' award' + (list.length === 1 ? '' : 's'),
      ''
    ];
    const block = (it, n) => {
      const a = it.a;
      const out = [(n ? n + '. ' : '') + (a.name || ('Award #' + a.id))];
      out.push('Type: ' + (a.k === 'H' ? 'Honor' : 'Medal') + ' \u00B7 Category: ' + cap(a.cat || 'unknown'));
      out.push('Requirement: ' + (a.desc || '(no description)'));
      if (it.cl === 'earned') out.push('Earned: ' + (isNum(it.ts) ? fmtStamp(it.ts * 1000, true) + ' TCT' : 'yes'));
      progressLines(it).forEach(x => out.push(x));
      if (it.cl !== 'earned' && it.cl !== 'obtainable') out.push('Classification: ' + cap(it.cl) + (it.clWhy ? ' \u2014 ' + it.clWhy : ''));
      if (it.p) out.push('Status: ' + statusText(it));
      if (it.p && it.p.note) out.push('Note: ' + it.p.note);
      if (it.circ0) out.push('Note: no player holds this yet (circulation 0); it is still listed because that alone does not prove it is unreleased.');
      if (it.est && S && S.view === 'quick') out.push('Effort estimate: ~' + fmtDuration(it.est.min) + ' \u2014 ' + it.est.why);
      return out.join('\n');
    };
    if (title.indexOf('NEAREST') !== -1) {
      list.forEach((it, i) => { L.push(block(it, i + 1)); L.push(''); });
    } else {
      [['H', 'HONORS'], ['M', 'MEDALS']].forEach(sec => {
        const part = list.filter(x => x.a.k === sec[0]);
        L.push(sec[1] + ' (' + part.length + ')');
        L.push('');
        if (!part.length) { L.push('(none)'); L.push(''); }
        part.forEach(it => { L.push(block(it)); L.push(''); });
      });
    }
    if (model.warnings.length) { L.push('DATA NOTES'); model.warnings.forEach(w => L.push('- ' + w)); L.push(''); }
    L.push('Legend: snapshot-validated = the award ID (honors) or name (medals), its statistic and its numeric target are consistent with the validation snapshot (' + VALID_DATE + ') and Torn\'s current description keyword; full requirement wording is not independently validated; partially measurable = validated, but the statistic only approximates Torn\'s rule, or the threshold came from the internal registry rather than the snapshot; unverified = mapped but not validated; needs review = Torn\'s current name, wording or target disagrees with the validated mapping, so no number is trusted; threshold reached = your statistic meets the target but Torn has not granted the award yet.');
    return Api.redact(L.join('\n'));
  }

  /* ============================ 14. APP STATE ============================ */
  const DEFAULT_SETTINGS = { view: 'closest', kind: 'all', cat: 'all', nearPct: 80, inferred: true, side: 'right', height: 'mid', autoRefresh: true };
  const HEIGHTS = { low: 76, mid: 150, high: 230 };
  /* Catalog write lock — persists across script re-initializations within the same WebView session.
   * All instances in the same page load share this chain, preventing concurrent catalog writes.
   * A page reload or separate WebView resets it; cross-session races cannot be prevented here. */
  if (!window.__FBAT_CWC__) window.__FBAT_CWC__ = Promise.resolve();
  /* Data write lock — same pattern as the catalog lock, applied to user-data cache writes.
   * Prevents a stale instance's delayed native storage write from overwriting newer data. */
  if (!window.__FBAT_DWC__) window.__FBAT_DWC__ = Promise.resolve();
  const App = { S: Object.assign({}, DEFAULT_SETTINGS, Store.get('settings', {})), catalog: null, data: null, model: null, busy: false, lastRefresh: 0, error: null, step: '', q: '', shown: PAGE_SIZE, refreshId: 0 };
  if (!VIEWS.some(v => v[0] === App.S.view)) App.S.view = 'closest';
  const saveSettings = () => Store.set('settings', App.S);

  async function serializeData(D) {
    const sel = Object.assign({}, D.sel);
    ['honors', 'medals'].forEach(k => { sel[k] = D.sel[k] ? Array.from(D.sel[k].entries()) : undefined; });
    return { v: VERSION, at: D.at, src: D.src, sel, key_fp: await keyFingerprint() };
  }
  function deserializeData(o) {
    if (!o || o.v !== VERSION || !o.sel || !isNum(o.at)) return null;
    const sel = Object.assign({}, o.sel);
    ['honors', 'medals'].forEach(k => { if (Array.isArray(sel[k])) sel[k] = new Map(sel[k]); else delete sel[k]; });
    return { at: o.at, src: o.src || {}, sel, key_fp: typeof o.key_fp === 'string' ? o.key_fp : null };
  }
  function rebuild() { App.model = App.catalog && App.data ? buildModel(App.catalog, App.data, App.S) : null; }

  async function doClearCache() {
    if (App.busy) { UI.toast('Cannot clear cache while loading'); return; }
    App.busy = true;
    App.refreshId++;
    try {
      const catOk = await Store.delBig('catalog');
      const datOk = await Store.delBig('data');
      App.catalog = null; App.data = null; App.model = null; App.lastRefresh = 0;
      UI.toast(catOk && datOk
        ? 'Cached data cleared'
        : 'Cache cleared \u2014 native storage deletion failed; data will be re-fetched on next open');
    } finally {
      App.busy = false;
      UI.render();
    }
  }

  async function refresh(opts) {
    opts = opts || {};
    if (App.busy) return;
    const since = Date.now() - App.lastRefresh;
    if (!opts.force && App.lastRefresh && since < MIN_REFRESH_GAP) { UI.toast('Please wait ' + Math.ceil((MIN_REFRESH_GAP - since) / 1000) + 's before refreshing again'); return; }
    App.busy = true; App.error = null; App.step = 'Starting...';
    const myId = ++App.refreshId;
    const live = () => App.refreshId === myId && UI.isAlive();
    UI.render();
    try {
      const step = s => { App.step = s; UI.renderStatus(); };
      App.catalog = await loadCatalog(!!opts.catalog, step, live);
      App.data = await loadUserData(step);
      App.lastRefresh = Date.now();
      if (!live()) return;
      const serialized = await serializeData(App.data);
      if (!live()) return;
      // Serialize data writes across instances sharing this JavaScript window, mirroring the
      // catalog write chain. Prevents a stale instance's delayed native write from overwriting
      // a newer write completed by a successor instance.
      {
        const prevDataChain = window.__FBAT_DWC__;
        let releaseDL;
        window.__FBAT_DWC__ = new Promise(function (r) { releaseDL = r; });
        try {
          await prevDataChain;
          if (!live()) return;
          await Store.setBig('data', serialized);
          if (!live()) { await Store.delBig('data').catch(function () {}); return; }
        } finally {
          releaseDL();
        }
      }
      rebuild();
    } catch (e) {
      App.error = errInfo(e);
    } finally {
      App.busy = false; App.step = '';
      UI.render();
    }
  }
  async function restoreCache() {
    if (App.model) return;
    // Do not invalidate an active refresh: if a refresh is already running, it will populate
    // App.model when it completes; incrementing refreshId here would make that refresh stale.
    if (App.busy) return;
    const myId = ++App.refreshId;
    try {
      const cat = await Store.getBig('catalog');
      if (App.refreshId !== myId || App.model) return;
      const raw = await Store.getBig('data');
      if (App.refreshId !== myId || App.model) return;
      const dat = deserializeData(raw);
      if (!dat) return;
      const currentFp = await keyFingerprint();
      if (App.refreshId !== myId || App.model) return;
      if (!currentFp || dat.key_fp !== currentFp) return;
      if (cat && cat.v === VERSION && Array.isArray(cat.honors) && cat.honors.length && Array.isArray(cat.medals) && cat.medals.length) {
        App.catalog = Object.assign({ fromCache: true }, cat);
        App.data = dat;
        App.lastRefresh = Math.max(App.lastRefresh, dat.at);
        rebuild();
      }
    } catch (e) { /* cache unreadable - a refresh will rebuild it */ }
  }

  /* ============================ 15. USER INTERFACE ============================ */
  const CSS = [
    ':host{all:initial}*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}',
    '.fab{position:fixed;z-index:2147483000;right:10px;bottom:calc(var(--y,150px) + env(safe-area-inset-bottom,0px));min-height:40px;padding:8px 12px;border-radius:20px;border:1px solid #c9a227;background:rgba(24,26,30,.92);color:#f2d675;font:600 14px/1.2 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Arial,sans-serif;box-shadow:0 2px 10px rgba(0,0,0,.5);touch-action:manipulation;cursor:pointer}',
    '.fab.left{left:10px;right:auto}.fab.hide{display:none}',
    '.ov{position:fixed;top:0;left:0;right:0;bottom:0;z-index:2147483001;background:rgba(0,0,0,.6);display:none}.ov.open{display:block}',
    '.pn{position:absolute;top:max(8px,env(safe-area-inset-top,0px));bottom:max(8px,env(safe-area-inset-bottom,0px));left:max(6px,env(safe-area-inset-left,0px));right:max(6px,env(safe-area-inset-right,0px));max-width:680px;margin:0 auto;display:flex;flex-direction:column;overflow:hidden;background:#16191d;color:#e7e9ec;border:1px solid #343a42;border-radius:12px;box-shadow:0 6px 30px rgba(0,0,0,.6);font:14px/1.4 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Arial,sans-serif}',
    '.hd{display:flex;align-items:center;gap:6px;padding:8px 8px 8px 12px;background:#1e2227;border-bottom:1px solid #343a42;flex:0 0 auto}',
    '.ttl{flex:1;min-width:0;font-weight:700;color:#f2d675;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.ttl small{color:#8d96a0;font-weight:400;margin-left:6px}',
    'button{font:inherit;color:inherit}',
    '.ib{width:42px;height:42px;border-radius:10px;border:1px solid #3d444d;background:#262b31;color:#e7e9ec;font-size:18px;line-height:1;cursor:pointer;touch-action:manipulation}',
    '.ib.x{background:#5a2626;border-color:#8a3a3a;color:#fff;font-weight:700}.ib:disabled{opacity:.45}',
    '.body{flex:1 1 auto;overflow-y:auto;-webkit-overflow-scrolling:touch;overscroll-behavior:contain;padding:0 10px 18px}',
    '.status{padding:8px 2px 4px;color:#9fb7a8;font-size:12.5px}.status.err{color:#ff9a8a}.status .rt{margin-left:6px}',
    'details.warn{margin:2px 0 6px;font-size:12px;color:#e8c47a}details.warn summary{cursor:pointer;padding:2px 0}details.warn li{margin:2px 0}',
    '.dash{display:grid;grid-template-columns:1fr 1fr;gap:6px;margin:6px 0 8px}@media (min-width:560px){.dash{grid-template-columns:repeat(4,1fr)}}',
    '.tile{border:1px solid #343a42;background:#1d2126;border-radius:10px;padding:8px;text-align:left;cursor:pointer;min-height:56px}.tile b{display:block;font-size:20px;color:#f2d675}.tile span{font-size:11.5px;color:#9aa3ad}',
    '.ctl{padding:6px 0;display:flex;flex-wrap:wrap;gap:6px;border-bottom:1px solid #2a2f35}',
    'select,input{font-size:16px;color:#e7e9ec;background:#22262c;border:1px solid #3d444d;border-radius:8px;padding:8px;min-height:40px;max-width:100%}',
    '.f-view{flex:1 1 100%}.f-kind,.f-cat{flex:1 1 40%;min-width:0}.f-q{flex:1 1 100%;-webkit-appearance:none;appearance:none}',
    '.cp{display:flex;flex-wrap:wrap;gap:6px;margin:8px 0 4px}.btn{flex:1 1 30%;min-height:40px;border-radius:8px;border:1px solid #4a525c;background:#2a3038;font-weight:700;font-size:12px;letter-spacing:.2px;padding:6px;cursor:pointer;touch-action:manipulation}',
    '.btn.pri{background:#3b3220;border-color:#8e7a3a;color:#f2d675}',
    '.count{font-size:12px;color:#9aa3ad;margin:6px 2px}',
    '.card{border-top:1px solid #2c3137;padding:10px 2px}.top{display:flex;gap:8px;align-items:flex-start;justify-content:space-between}',
    '.nm{font-weight:700;font-size:15px;word-break:break-word}.badges{display:flex;gap:4px;flex-wrap:wrap;justify-content:flex-end;flex:0 0 auto;max-width:48%}',
    '.badge{font-size:10.5px;padding:2px 6px;border-radius:6px;background:#2a3038;color:#b8c0c8;white-space:nowrap}.b-h{background:#26324a;color:#a9c4ff}.b-m{background:#3a2d1f;color:#f0c58a}',
    '.desc{color:#a3abb4;font-size:12.5px;margin:3px 0 4px;word-break:break-word}',
    '.bar{height:7px;background:#2c3238;border-radius:5px;overflow:hidden;margin:6px 0 4px}.bar i{display:block;height:100%;background:#57c17b;border-radius:5px}.bar.done i{background:#d4a73a}',
    '.pv{display:flex;justify-content:space-between;gap:8px;font-size:13px}.pv b{color:#7fdc9a;white-space:nowrap}.rem{font-size:12.5px;color:#c9d1d9}',
    '.part{margin:4px 0 2px;font-size:12.5px}.part .bar{height:5px;margin:3px 0}',
    '.chip{display:inline-block;margin-top:5px;font-size:11px;font-weight:700;padding:2px 7px;border-radius:6px;background:#2a3038;color:#c8d0d8}',
    '.s-verified{background:#1f3b2a;color:#7fdc9a}.s-partial{background:#3d3418;color:#ecc66b}.s-inferred{background:#1d3347;color:#8cc7f2}.s-unverified{background:#2e2b45;color:#c4b5fd}.s-reached{background:#4a3b12;color:#ffd866}',
    '.s-unavailable,.s-mismatch{background:#4a2222;color:#ff9a8a}.s-special,.s-unmapped{background:#2f3339;color:#c0c7cf}.s-date{background:#37284a;color:#d3b3ff}',
    '.note,.meta{font-size:11.5px;color:#8d96a0;margin-top:3px;word-break:break-word}.est{font-size:12px;color:#9ec3ff;margin-top:3px}',
    '.more{display:none;width:100%;margin:10px 0;min-height:42px;border-radius:8px;border:1px solid #4a525c;background:#262b31;cursor:pointer}.more.on{display:block}',
    '.empty{padding:22px 6px;color:#9aa3ad;text-align:center;font-size:13px}',
    '.sheet,.modal{position:absolute;top:58px;left:0;right:0;bottom:0;background:#16191d;display:none;flex-direction:column;z-index:5}.sheet.on,.modal.on{display:flex}',
    '.sh-body{flex:1;overflow-y:auto;-webkit-overflow-scrolling:touch;overscroll-behavior:contain;padding:10px 12px 24px}',
    '.row{display:flex;align-items:center;justify-content:space-between;gap:10px;padding:8px 0;border-bottom:1px solid #2a2f35;font-size:13.5px}.row select{min-width:110px}',
    '.row input[type=checkbox]{width:24px;height:24px;min-height:0}',
    '.sh-h{font-weight:700;color:#f2d675;margin:14px 0 4px}.diag{white-space:pre-wrap;font:11.5px/1.45 ui-monospace,Menlo,monospace;color:#b8c0c8;background:#1d2126;border-radius:8px;padding:8px;margin:6px 0}',
    '.m-title{padding:10px 12px 4px;font-weight:700}.m-help{padding:0 12px;font-size:12px;color:#9aa3ad}',
    '.m-text{flex:1;margin:8px 12px;font:12px/1.4 ui-monospace,Menlo,monospace;resize:none;min-height:0}.m-row{display:flex;gap:6px;padding:0 12px 12px}',
    '.toast{position:absolute;left:50%;bottom:16px;transform:translateX(-50%);max-width:90%;background:#2d5a3d;color:#fff;padding:9px 14px;border-radius:10px;font-size:13px;opacity:0;pointer-events:none;transition:opacity .2s;z-index:9;text-align:center}.toast.on{opacity:1}'
  ].join('\n');

  const HTML =
    '<button class="fab" data-act="open" aria-label="Open awards tracker">\u{1F3C5} Awards</button>' +
    '<div class="ov" data-act="backdrop"><div class="pn" role="dialog" aria-modal="true" aria-label="Fatboy Awards Tracker">' +
    '<div class="hd"><div class="ttl">Merit Tracker<small>v' + VERSION + '</small></div>' +
    '<button class="ib" data-act="refresh" aria-label="Refresh">\u21BB</button><button class="ib" data-act="settings" aria-label="Settings">\u2699</button>' +
    '<button class="ib x" data-act="close" aria-label="Close">\u2715</button></div>' +
    '<div class="body"><div class="status"></div><div class="warnbox"></div><div class="dash"></div>' +
    '<div class="ctl"><select class="f-view" aria-label="View"></select><select class="f-kind" aria-label="Honors or medals">' +
    '<option value="all">Honors + medals</option><option value="honors">Honors only</option><option value="medals">Medals only</option></select>' +
    '<select class="f-cat" aria-label="Category"></select><input class="f-q" type="search" placeholder="Search names and descriptions" autocomplete="off" autocapitalize="off" spellcheck="false"></div>' +
    '<div class="cp"><button class="btn pri" data-act="copy-all">COPY ALL MISSING</button><button class="btn" data-act="copy-filtered">COPY FILTERED</button><button class="btn" data-act="copy-near">COPY NEAREST 20</button></div>' +
    '<div class="count"></div><div class="list"></div><button class="more" data-act="more">Show more</button></div>' +
    '<div class="sheet"><div class="sh-body"></div></div>' +
    '<div class="modal"><div class="m-title"></div><div class="m-help">Automatic copy was blocked. Tap Select all, then choose Copy from the iOS menu.</div>' +
    '<textarea class="m-text" readonly></textarea><div class="m-row"><button class="btn pri" data-act="m-select">Select all</button><button class="btn" data-act="m-close">Close</button></div></div>' +
    '<div class="toast" role="status"></div></div></div>';

  const UI = (function () {
    let host = null;
    let root = null;
    let $ = {};
    let mo = null;
    let watch = null;
    let saved = null;
    let toastT = null;
    const mk = (tag, cls, text) => { const e = document.createElement(tag); if (cls) e.className = cls; if (text != null) e.textContent = text; return e; };
    const q = s => root.querySelector(s);
    const isOpen = () => !!($.ov && $.ov.classList.contains('open'));

    function applyCss() {
      try {
        if (root !== host && 'adoptedStyleSheets' in root && typeof CSSStyleSheet === 'function') {
          const sh = new CSSStyleSheet(); sh.replaceSync(CSS); root.adoptedStyleSheets = [sh]; return;
        }
      } catch (e) { /* fall back to a style element */ }
      const st = document.createElement('style'); st.textContent = CSS; root.appendChild(st);
    }
    function build() {
      host = document.createElement('div');
      host.id = 'fbat2-host';
      host.setAttribute('data-version', VERSION);
      host.style.cssText = 'all:initial;display:block;position:static;transform:none;filter:none;contain:none;';
      root = host.attachShadow ? host.attachShadow({ mode: 'open' }) : host;
      applyCss();
      const tpl = document.createElement('template');
      tpl.innerHTML = HTML;
      root.appendChild(tpl.content.cloneNode(true));
      $ = { fab: q('.fab'), ov: q('.ov'), pn: q('.pn'), body: q('.body'), status: q('.status'), warn: q('.warnbox'), dash: q('.dash'), view: q('.f-view'), kind: q('.f-kind'), cat: q('.f-cat'), search: q('.f-q'), count: q('.count'), list: q('.list'), more: q('.more'), sheet: q('.sheet'), shBody: q('.sh-body'), modal: q('.modal'), mTitle: q('.m-title'), mText: q('.m-text'), toast: q('.toast'), refresh: q('[data-act="refresh"]') };
      VIEWS.forEach(v => { const o = mk('option', null, v[1]); o.value = v[0]; $.view.appendChild(o); });
      bind();
      attach();
      renderFab();
      mo = new MutationObserver(() => { if (!host.isConnected) attach(); });
      mo.observe(document.documentElement, { childList: true });
      if (document.body) mo.observe(document.body, { childList: true });
      watch = setInterval(() => { if (!host.isConnected) attach(); }, 3000);
    }
    function attach() { const parent = document.body || document.documentElement; if (parent && !host.isConnected) parent.appendChild(host); }
    function destroy() {
      if (mo) mo.disconnect();
      if (watch) clearInterval(watch);
      document.removeEventListener('keydown', onKey, true);
      if (isOpen()) unlockScroll();
      if (host && host.parentNode) host.parentNode.removeChild(host);
      host = null;
    }

    function lockScroll() {
      const de = document.documentElement;
      const b = document.body;
      saved = { h: de.style.overflow, b: b ? b.style.overflow : '' };
      de.style.overflow = 'hidden';
      if (b) b.style.overflow = 'hidden';
    }
    function unlockScroll() {
      if (!saved) return;
      document.documentElement.style.overflow = saved.h;
      if (document.body) document.body.style.overflow = saved.b;
      saved = null;
    }
    function open() {
      if (isOpen()) return;
      lockScroll();
      $.ov.classList.add('open');
      $.fab.classList.add('hide');
      render();
      restoreCache().then(() => {
        render();
        const age = App.data ? Date.now() - App.data.at : Infinity;
        if (!App.busy && (!App.model || (App.S.autoRefresh && age > DATA_FRESH_MS))) refresh({ force: !App.model || age > DATA_FRESH_MS });
      });
    }
    function close() {
      $.ov.classList.remove('open');
      $.sheet.classList.remove('on');
      $.modal.classList.remove('on');
      $.fab.classList.remove('hide');
      unlockScroll();
    }
    function onKey(e) { if (e.key === 'Escape' && isOpen()) close(); }

    function bind() {
      root.addEventListener('click', onClick);
      $.view.addEventListener('change', () => { App.S.view = $.view.value; App.shown = PAGE_SIZE; saveSettings(); renderList(); });
      $.kind.addEventListener('change', () => { App.S.kind = $.kind.value; App.shown = PAGE_SIZE; saveSettings(); renderList(); });
      $.cat.addEventListener('change', () => { App.S.cat = $.cat.value; App.shown = PAGE_SIZE; saveSettings(); renderList(); });
      $.search.addEventListener('input', debounce(() => { App.q = $.search.value; App.shown = PAGE_SIZE; renderList(); }, 180));
      $.ov.addEventListener('touchmove', e => {
        const path = e.composedPath ? e.composedPath() : [];
        if (!path.some(n => n === $.body || n === $.shBody || n === $.mText)) e.preventDefault();
      }, { passive: false });
      document.addEventListener('keydown', onKey, true);
    }

    function currentList() {
      if (!App.model) return [];
      return applyFilters(viewItems(App.model, App.S.view, App.S), { kind: App.S.kind, cat: App.S.cat, q: App.q });
    }
    function viewLabel(v) { const x = VIEWS.find(r => r[0] === v); return x ? x[1] : v; }
    function onClick(e) {
      const t = e.target && e.target.closest ? e.target.closest('[data-act]') : null;
      if (!t) return;
      const act = t.getAttribute('data-act');
      if (act === 'backdrop' && e.target !== $.ov) return;
      switch (act) {
        case 'open': open(); break;
        case 'close': case 'backdrop': close(); break;
        case 'refresh': refresh({}); break;
        case 'retry': refresh({ force: true }); break;
        case 'settings': if ($.sheet.classList.toggle('on')) renderSettings(); break;
        case 'sheet-close': $.sheet.classList.remove('on'); break;
        case 'more': App.shown += PAGE_SIZE; renderList(); break;
        case 'tile': {
          const k = t.getAttribute('data-tile');
          App.S.view = k === 'h' || k === 'm' ? 'all' : (k === 'n' ? 'nearly' : 'closest');
          App.S.kind = k === 'h' ? 'honors' : (k === 'm' ? 'medals' : 'all');
          App.S.cat = 'all'; App.shown = PAGE_SIZE; saveSettings(); renderFilters(); renderList(); break;
        }
        case 'copy-all': case 'copy-filtered': case 'copy-near': doCopy(act); break;
        case 'recatalog': $.sheet.classList.remove('on'); refresh({ force: true, catalog: true }); break;
        case 'clear-cache': doClearCache(); break;
        case 'copy-diag': copyText(diagnostics(true), 'diagnostics'); break;
        case 'm-select': {
          $.mText.focus(); $.mText.select(); $.mText.setSelectionRange(0, $.mText.value.length);
          let ok = false; try { ok = document.execCommand && document.execCommand('copy'); } catch (err) { ok = false; }
          if (ok) toast('Copied');
          break;
        }
        case 'm-close': $.modal.classList.remove('on'); break;
        default: break;
      }
    }

    /* ---- clipboard (must start synchronously inside the tap) ---- */
    function legacyCopy(text) {
      const ta = document.createElement('textarea');
      ta.value = text;
      ta.setAttribute('readonly', '');
      ta.style.cssText = 'position:fixed;top:0;left:-9999px;width:1px;height:1px;opacity:0;font-size:16px;';
      (document.body || document.documentElement).appendChild(ta);
      let ok = false;
      try { ta.focus(); ta.select(); ta.setSelectionRange(0, text.length); ok = !!(document.execCommand && document.execCommand('copy')); } catch (e) { ok = false; }
      ta.parentNode.removeChild(ta);
      return ok;
    }
    function manualCopy(text, label) {
      $.mTitle.textContent = 'Copy ' + label;
      $.mText.value = text;
      $.modal.classList.add('on');
    }
    function copyText(text, label) {
      const msg = 'Copied ' + label + ' (' + fmtNum(text.length) + ' characters)';
      try {
        if (navigator.clipboard && typeof navigator.clipboard.writeText === 'function') {
          navigator.clipboard.writeText(text).then(() => toast(msg), () => { if (legacyCopy(text)) toast(msg); else manualCopy(text, label); });
          return;
        }
      } catch (e) { /* use the fallback below */ }
      if (legacyCopy(text)) toast(msg); else manualCopy(text, label);
    }
    function doCopy(act) {
      if (!App.model) { toast('Load your awards first'); return; }
      const m = App.model;
      let list;
      let title;
      let scope;
      if (act === 'copy-all') {
        list = viewItems(m, 'all', App.S);
        title = 'MISSING MERIT AWARDS';
        scope = 'every confirmed obtainable, unearned merit award (excludes earned awards, default/flag/memorial bars, Token Shop and Points Building bars, retired or Crimes 1.0 awards and unreleased awards)';
      } else if (act === 'copy-near') {
        list = viewItems(m, 'closest', App.S).filter(x => isNum(x.p.pct)).slice(0, 20);
        title = 'NEAREST 20 MEASURABLE AWARDS';
        scope = 'the 20 measurable obtainable awards closest to completion (threshold-reached awards first)';
      } else {
        list = currentList();
        title = 'FILTERED AWARDS';
        scope = 'view "' + viewLabel(App.S.view) + '"; ' + (App.S.kind === 'all' ? 'honors and medals' : App.S.kind) + '; category: ' + (App.S.cat === 'all' ? 'all' : cap(App.S.cat)) + (App.q ? '; search: "' + App.q + '"' : '');
      }
      copyText(exportText(m, list, title, scope, App.S), list.length + ' award' + (list.length === 1 ? '' : 's'));
    }
    function toast(text) {
      if (!$.toast) return;
      $.toast.textContent = text;
      $.toast.classList.add('on');
      clearTimeout(toastT);
      toastT = setTimeout(() => $.toast.classList.remove('on'), 2600);
    }

    /* ---- rendering ---- */
    function renderFab() {
      if (!$.fab) return;
      $.fab.classList.toggle('left', App.S.side === 'left');
      $.fab.style.setProperty('--y', (HEIGHTS[App.S.height] || HEIGHTS.mid) + 'px');
    }
    function render() {
      renderFab();
      if (!isOpen()) return;
      renderStatus(); renderDash(); renderFilters(); renderList();
      if ($.sheet.classList.contains('on')) renderSettings();
    }
    function renderStatus() {
      if (!$.status) return;
      $.status.textContent = '';
      $.status.className = 'status';
      $.refresh.disabled = App.busy;
      if (App.busy) { $.status.textContent = '\u23F3 ' + (App.step || 'Loading...'); return; }
      if (App.error) {
        $.status.className = 'status err';
        $.status.appendChild(document.createTextNode('\u26A0 ' + App.error.msg + (App.error.path ? ' [' + App.error.path + ']' : '')));
        const b = mk('button', 'btn rt', 'Retry'); b.setAttribute('data-act', 'retry'); $.status.appendChild(b);
        if (!App.model) return;
        $.status.appendChild(mk('div', null, 'Showing the last successful data.'));
      }
      if (App.model) {
        const c = App.catalog;
        $.status.appendChild(document.createTextNode((App.error ? '' : '\u2714 ') + 'Data ' + fmtAgo(App.model.at) + ' \u00B7 catalogue ' + (c && c.fromCache ? 'cached ' + fmtAgo(c.at) : 'fresh') + ' \u00B7 ' + Api.count() + ' API calls this session'));
      } else if (!App.error) {
        $.status.textContent = 'Tap \u21BB to load your awards.';
      }
      $.warn.textContent = '';
      const w = App.model ? App.model.warnings : [];
      if (w.length) {
        const d = mk('details', 'warn');
        d.appendChild(mk('summary', null, '\u26A0 ' + w.length + ' data note' + (w.length === 1 ? '' : 's') + ' (tap to view)'));
        const ul = mk('ul');
        w.forEach(x => ul.appendChild(mk('li', null, x)));
        d.appendChild(ul);
        $.warn.appendChild(d);
      }
    }
    function renderDash() {
      $.dash.textContent = '';
      const s = App.model ? App.model.summary : null;
      [['h', s ? s.missingH : '-', 'Missing merit honors'], ['m', s ? s.missingM : '-', 'Missing merit medals'],
        ['t', s ? s.trackable : '-', 'Trackable awards'], ['n', s ? s.nearly : '-', 'Nearly complete (\u2265' + App.S.nearPct + '%)']].forEach(r => {
        const b = mk('button', 'tile');
        b.setAttribute('data-act', 'tile'); b.setAttribute('data-tile', r[0]);
        b.appendChild(mk('b', null, String(r[1]))); b.appendChild(mk('span', null, r[2]));
        $.dash.appendChild(b);
      });
    }
    function renderFilters() {
      $.view.value = App.S.view;
      $.kind.value = App.S.kind;
      const cats = {};
      if (App.model) App.model.items.forEach(x => { if (x.a.cat) cats[x.a.cat] = true; });
      const keys = Object.keys(cats).sort();
      if (App.S.cat !== 'all' && !cats[App.S.cat]) keys.push(App.S.cat);
      $.cat.textContent = '';
      const all = mk('option', null, 'All categories'); all.value = 'all'; $.cat.appendChild(all);
      keys.forEach(k => { const o = mk('option', null, cap(k)); o.value = k; $.cat.appendChild(o); });
      $.cat.value = App.S.cat;
      if ($.search.value !== App.q) $.search.value = App.q;
    }
    function bar(pct, done) {
      const b = mk('div', 'bar' + (done ? ' done' : ''));
      const i = mk('i');
      i.style.width = Math.max(0, Math.min(100, isNum(pct) ? pct : 0)).toFixed(2) + '%';
      b.appendChild(i);
      return b;
    }
    const CHIP = { verified: 'Snapshot-validated', partial: 'Partially measurable', unverified: 'Unverified mapping', inferred: 'Inferred mapping (not in registry)', special: 'Progress unavailable \u2014 special condition', date: 'Action required \u2014 no numeric tracker', unavailable: 'Progress temporarily unavailable \u2014 missing API permission/data', mismatch: 'Needs review', unmapped: 'No tracker mapped for this award' };
    function appendProgress(c, it) {
      const p = it.p;
      const meas = MEASURABLE.indexOf(p.st) !== -1;
      const label = unitLabel(p);
      if (p.multi) {
        p.parts.forEach(x => {
          const row = mk('div', 'part');
          row.appendChild(mk('div', null, x.label + ': ' + (x.ok ? fmtNum(x.cur) : '?') + ' / ' + fmtNum(x.tgt) + (x.ok ? (x.reached ? '  \u2714' : '  (' + fmtPct(x.pct, false) + ')') : '  (unavailable)')));
          if (x.ok) row.appendChild(bar(x.pct, x.reached));
          c.appendChild(row);
        });
        if (meas) { const pv = mk('div', 'pv'); pv.appendChild(mk('span', null, 'Overall (all must be met)')); pv.appendChild(mk('b', null, fmtPct(p.pct, p.reached))); c.appendChild(pv); }
      } else if (meas) {
        if (!p.lower) c.appendChild(bar(p.pct, p.reached));
        const pv = mk('div', 'pv');
        if (p.lower) pv.appendChild(mk('span', null, 'Best rank #' + fmtNum(p.cur) + ' \u00B7 target top ' + fmtNum(p.tgt)));
        else pv.appendChild(mk('span', null, valText(p.cur, p) + ' / ' + valText(p.tgt, p) + (p.unit && p.unit.rank ? '' : ' ' + label)));
        if (!p.lower) pv.appendChild(mk('b', null, fmtPct(p.pct, p.reached)));
        c.appendChild(pv);
        if (!p.reached) c.appendChild(mk('div', 'rem', p.lower ? 'Climb ' + fmtNum(p.rem) + ' places' : remText(p) + (p.anniv ? '' : ' remaining')));
        annivLines(p).forEach(x => c.appendChild(mk('div', 'rem', x)));
      } else if (p.st === 'unavailable' && isNum(p.tgt)) {
        c.appendChild(mk('div', 'rem', 'Target: ' + fmtVal(p.tgt, p.unit) + ' ' + label));
      }
      const reached = meas && p.reached;
      c.appendChild(mk('span', 'chip ' + (reached ? 's-reached' : 's-' + p.st), reached ? 'Threshold reached' + ({ partial: ' (partial)', unverified: ' (unverified)', inferred: ' (inferred)' }[p.st] || '') + ' \u2014 award not confirmed' : (p.st === 'special' && p.sp === 'act' ? CHIP.date : CHIP[p.st] || p.st)));
      const why = p.st === 'unavailable' || p.st === 'mismatch' ? p.why : '';
      const note = [why, p.note].filter(Boolean).join(' ');
      if (note) c.appendChild(mk('div', 'note', note));
      if (it.est && App.S.view === 'quick') c.appendChild(mk('div', 'est', 'Estimate: ~' + fmtDuration(it.est.min) + ' \u2014 ' + it.est.why));
    }
    function card(it) {
      const a = it.a;
      const c = mk('div', 'card');
      const top = mk('div', 'top');
      top.appendChild(mk('div', 'nm', a.name || ('Award #' + a.id)));
      const badges = mk('div', 'badges');
      badges.appendChild(mk('span', 'badge ' + (a.k === 'H' ? 'b-h' : 'b-m'), a.k === 'H' ? 'Honor' : 'Medal'));
      badges.appendChild(mk('span', 'badge', cap(a.cat || 'unknown')));
      top.appendChild(badges);
      c.appendChild(top);
      c.appendChild(mk('div', 'desc', a.desc || '(no description)'));
      if (it.cl === 'earned') c.appendChild(mk('div', 'meta', 'Earned ' + (isNum(it.ts) ? fmtStamp(it.ts * 1000, true) + ' TCT' : '')));
      else if (it.cl !== 'obtainable') c.appendChild(mk('div', 'meta', cap(it.cl) + ': ' + it.clWhy));
      if (it.circ0) c.appendChild(mk('div', 'meta', 'No player holds this yet (circulation 0). Still listed: that alone does not prove it is unreleased.'));
      if (it.p) appendProgress(c, it);
      return c;
    }
    function renderList() {
      if (!$.list) return;
      $.list.textContent = '';
      $.more.classList.remove('on');
      if (!App.model) { $.count.textContent = ''; $.list.appendChild(mk('div', 'empty', App.busy ? 'Loading...' : 'No data yet.')); return; }
      const list = currentList();
      const shown = Math.min(App.shown, list.length);
      $.count.textContent = 'Showing ' + shown + ' of ' + list.length + ' \u00B7 ' + viewLabel(App.S.view) + (App.S.view === 'quick' ? ' \u00B7 effort figures are rough estimates' : '');
      if (!list.length) { $.list.appendChild(mk('div', 'empty', 'Nothing matches this view and filter.')); return; }
      const frag = document.createDocumentFragment();
      for (let i = 0; i < shown; i++) frag.appendChild(card(list[i]));
      $.list.appendChild(frag);
      if (list.length > shown) { $.more.textContent = 'Show ' + Math.min(PAGE_SIZE, list.length - shown) + ' more (' + (list.length - shown) + ' left)'; $.more.classList.add('on'); }
    }

    function renderSettings() {
      const b = $.shBody;
      b.textContent = '';
      const head = mk('div', 'row');
      head.appendChild(mk('b', null, 'Settings'));
      const cl = mk('button', 'btn', 'Done'); cl.setAttribute('data-act', 'sheet-close'); cl.style.flex = '0 0 90px';
      head.appendChild(cl);
      b.appendChild(head);
      const sel = (label, key, opts, after) => {
        const r = mk('div', 'row'); r.appendChild(mk('span', null, label));
        const s = mk('select');
        opts.forEach(o => { const op = mk('option', null, o[1]); op.value = String(o[0]); s.appendChild(op); });
        s.value = String(App.S[key]);
        s.addEventListener('change', () => { App.S[key] = isNum(App.S[key]) ? Number(s.value) : s.value; saveSettings(); if (after) after(); render(); });
        r.appendChild(s); b.appendChild(r);
      };
      const chk = (label, key, after) => {
        const r = mk('label', 'row'); r.appendChild(mk('span', null, label));
        const c = mk('input'); c.type = 'checkbox'; c.checked = !!App.S[key];
        c.addEventListener('change', () => { App.S[key] = c.checked; saveSettings(); if (after) after(); render(); });
        r.appendChild(c); b.appendChild(r);
      };
      sel('Nearly-complete threshold', 'nearPct', [[70, '70%'], [75, '75%'], [80, '80%'], [85, '85%'], [90, '90%'], [95, '95%']], rebuild);
      chk('Show inferred progress for awards not in the registry', 'inferred', rebuild);
      chk('Auto-refresh on open when data is older than 15 min', 'autoRefresh');
      sel('Button side', 'side', [['right', 'Right'], ['left', 'Left']]);
      sel('Button height', 'height', [['low', 'Low'], ['mid', 'Middle'], ['high', 'High']]);
      const acts = mk('div', 'cp');
      [['recatalog', 'RE-DOWNLOAD CATALOGUE'], ['clear-cache', 'CLEAR CACHE'], ['copy-diag', 'COPY DIAGNOSTICS']].forEach(r => { const x = mk('button', 'btn', r[1]); x.setAttribute('data-act', r[0]); acts.appendChild(x); });
      b.appendChild(acts);
      b.appendChild(mk('div', 'sh-h', 'Diagnostics'));
      b.appendChild(mk('div', 'diag', diagnostics()));
      b.appendChild(mk('div', 'sh-h', 'How progress is labelled'));
      b.appendChild(mk('div', 'note', 'Snapshot-validated: the award ID (honors) or name (medals), its statistic and its numeric target match the validation snapshot and Torn\'s current description keyword; full requirement wording is not independently validated. Partially measurable: validated, but the statistic only approximates Torn\'s rule, or the threshold came from the internal registry rather than the snapshot. Unverified mapping: in the registry but not validated - progress shown, treat with care. Inferred: not in the registry; Torn\'s wording matches a known statistic. Needs review: Torn\'s current name, wording or target disagrees with the validated mapping, so no progress is claimed. Special condition / action required: Torn exposes no counter. Data unavailable: the API call failed or your key cannot read it. Threshold reached: your statistic meets the target but Torn has not granted the award.'));
    }

    return { build, destroy, render, renderStatus, renderList, toast, open, close, isOpen, copyText, isAlive: () => !!(host && host.isConnected) };
  })();

  function diagnostics(full) {
    const m = App.model;
    const s = m ? m.summary : null;
    const c = App.catalog;
    const L = [
      'Fatboy Awards Tracker ' + VERSION,
      'Environment: PDA_httpGet ' + (typeof PDA_httpGet === 'function' ? 'yes' : 'NO') + ' \u00B7 PDA_storage ' + (Store.native() ? 'yes' : 'no (localStorage)') + ' \u00B7 API key supplied ' + (keyOk() ? 'yes' : 'NO'),
      'Catalogue: ' + (c ? c.honors.length + ' honors, ' + c.medals.length + ' medals, ' + (c.edu ? c.edu.length : 0) + ' education categories \u00B7 ' + fmtStamp(c.at, true) + ' TCT' : 'not loaded'),
      'API calls this session: ' + Api.count() + (Api.coolingFor() ? ' \u00B7 rate-limit pause ' + Math.ceil(Api.coolingFor() / 1000) + 's' : '')
    ];
    if (App.data) L.push('Endpoints: ' + Object.keys(App.data.src).map(k => k + ' ' + (App.data.src[k].ok ? 'OK' : 'FAILED (' + (App.data.src[k].err ? App.data.src[k].err.msg : '?') + ')')).join(' \u00B7 '));
    if (s) {
      L.push('Crimes version (personal stats): ' + (s.crimesV || 'unknown'));
      L.push('Classification: obtainable ' + (s.missingH + s.missingM) + ' \u00B7 earned ' + s.earned + ' \u00B7 non-merit ' + s.nonmerit + ' \u00B7 retired ' + s.retired + ' \u00B7 future ' + s.future + ' \u00B7 unknown ' + s.unknown);
      L.push('Progress on obtainable awards: verified ' + s.verified + ' \u00B7 partial ' + s.partial + ' \u00B7 unverified ' + s.unverified + ' \u00B7 inferred ' + s.inferred + ' \u00B7 needs review ' + s.mismatch + ' \u00B7 special/action ' + s.special + ' \u00B7 data unavailable ' + s.unavailable + ' \u00B7 no tracker ' + s.unmapped + ' \u00B7 zero circulation ' + s.circ0);
    }
    let h = 0; let md = 0; let sp = 0;
    REG.forEach(e => { if (e.sp) sp++; else if (e.kind === 'H') h++; else md++; });
    L.push('Registry: ' + h + ' honor IDs and ' + md + ' medal IDs with numeric trackers, ' + sp + ' special/action IDs, plus type rules for level, networth, rank and Crimes 2.0 medals');
    L.push('Validation snapshot (' + VALID_DATE + '): ' + VALID_H.size + ' honor IDs, ' + VALID_M.size + ' medal names');
    const au = m && m.audit;
    if (au) {
      const nm = au.named;
      L.push('Registry audit vs the live catalogue: ' + au.checked + ' numeric IDs checked \u00B7 verified ' + au.verified + ' \u00B7 partial ' + au.partial + ' \u00B7 unverified ' + au.unverified.length + ' \u00B7 data unavailable ' + au.unavailable + ' \u00B7 needs review ' + au.review.length +
        ' \u00B7 missing from catalogue ' + au.missing.length + ' \u00B7 duplicate definitions ' + au.dupes.length + ' \u00B7 conflicts ' + au.conflicts.length + ' \u00B7 personal-stat paths not returned ' + au.paths.length + ' \u00B7 validated medals without a tracker ' + au.knownUnmapped.length);
      L.push('Medals outside the registry, checked by validated name: ' + nm.checked + ' checked \u00B7 verified ' + nm.verified + ' \u00B7 partial ' + nm.partial + ' \u00B7 unverified ' + nm.unverified.length + ' \u00B7 data unavailable ' + nm.unavailable + ' \u00B7 needs review ' + nm.review.length + ' \u00B7 mapped by name only ' + nm.byName.length);
      if (full) {
        const list = (title, arr) => { if (arr.length) { L.push(title + ':'); arr.slice(0, 80).forEach(x => L.push('  - ' + x)); if (arr.length > 80) L.push('  ... ' + (arr.length - 80) + ' more'); } };
        list('Needs review', au.review.concat(nm.review)); list('Registry IDs missing from the catalogue', au.missing); list('Unverified registry IDs', au.unverified.concat(nm.unverified));
        list('Personal-stat paths not in your response', au.paths); list('Duplicate registry definitions', au.dupes); list('Registry conflicts', au.conflicts);
        list('Validated medals without a tracker', au.knownUnmapped);
        list('Mapped by validated name only (Torn\'s type data does not mark them)', nm.byName);
        // Awards that still need a decision, with Torn's own wording, so a copied report is self-contained.
        const ob = m.items.filter(x => x.cl === 'obtainable');
        const line = x => x.a.k + ':' + x.a.id + ' ' + x.a.name + ' ' + awardTag(x.a);
        list('Obtainable awards with inferred progress', ob.filter(x => x.p && x.p.st === 'inferred').map(line));
        list('Obtainable awards without a tracker', ob.filter(x => x.p && x.p.st === 'unmapped').map(line));
        list('Obtainable awards nobody holds yet (circulation 0)', ob.filter(x => x.circ0).map(x => line(x) + ' -> ' + (x.p ? x.p.st : 'no progress')));
      }
    }
    return Api.redact(L.join('\n'));
  }

  /* ================================ 16. BOOT ================================ */
  function boot() {
    if (!document.body) { document.addEventListener('DOMContentLoaded', boot, { once: true }); return; }
    if (document.getElementById('fbat2-host')) { const old = document.getElementById('fbat2-host'); old.parentNode.removeChild(old); }
    UI.build();
    window.__FBAT__ = { version: VERSION, isAlive: UI.isAlive, destroy: UI.destroy, open: UI.open, close: UI.close };
    window.addEventListener('popstate', function onNav() {
      if (!isAwardsPage()) { UI.destroy(); window.removeEventListener('popstate', onNav); }
    }, { passive: true });
    if (window.__FBAT_EXPOSE__ === true) {
      window.__FBAT_TEST__ = { App, REG, STATS, RANKS, extractNumbers, pickNumber, classify, computeProgress, buildModel, viewItems, applyFilters, exportText, statusText, progressLines, refresh, rebuild, loadCatalog, diagnostics, fmtPct, normAward, UI,
        VALID_H, VALID_M, VALID_DATE, TOKEN_SHOP, FUTURE_IDS, REG_DUPES, REG_CONFLICTS, registryAudit, anniversary, snapshotFor, normName, annivLines, resolveThreshold, snapshotRule, medalTypeRule, thrNote,
        Store, restoreCache, doClearCache, keyFingerprint, serializeData, deserializeData, VERSION };
    }
  }
  boot();
})();
