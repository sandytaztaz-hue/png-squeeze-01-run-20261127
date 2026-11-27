// PNG squeeze R8: colour forms + filter contest + binary-tree finder + optimal parse.
// Single-file encoder, deterministic, fixed budgets only. Node 22, stdlib only.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { deflateSync, inflateSync } from 'node:zlib';

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const W = 1280, H = 720;

// ---------- DEFLATE tables ----------
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
function lenSym(len) { let lo = 0, hi = 28; while (lo < hi) { const m = (lo + hi + 1) >> 1; if (LEN_BASE[m] <= len) lo = m; else hi = m - 1; } return lo; }
function distSym(d) { let lo = 0, hi = 29; while (lo < hi) { const m = (lo + hi + 1) >> 1; if (DIST_BASE[m] <= d) lo = m; else hi = m - 1; } return lo; }
const FIXED_LIT = new Uint8Array(288);
for (let i = 0; i < 288; i++) FIXED_LIT[i] = i < 144 ? 8 : i < 256 ? 9 : i < 280 ? 7 : 8;

// ---------- CRC32 / Adler32 ----------
const CRC_T = (() => { const t = new Int32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; t[n] = c; } return t; })();
function crc32(b, s, e) { let c = -1; for (let i = s; i < e; i++) c = CRC_T[(c ^ b[i]) & 255] ^ (c >>> 8); return (c ^ -1) >>> 0; }
function adler32(b) { let a = 1, c = 0; for (let i = 0; i < b.length;) { const e = Math.min(b.length, i + 5552); for (; i < e; i++) { a += b[i]; c += a; } a %= 65521; c %= 65521; } return ((c << 16) | a) >>> 0; }

// ---------- PNG decode / encode ----------
function paeth(a, b, c) { const p = a + b - c; const pa = p > a ? p - a : a - p; const pb = p > b ? p - b : b - p; const pc = p > c ? p - c : c - p; if (pa <= pb && pa <= pc) return a; return pb <= pc ? b : c; }
export function decodePng(bytes) {
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8, width = 0, height = 0, ct = 0, palette = null, trns = null; const idat = [];
  while (at < bytes.length) {
    const len = view.getUint32(at); const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    const data = bytes.subarray(at + 8, at + 8 + len); at += 12 + len;
    if (type === 'IHDR') { width = view.getUint32(at - 12 - len + 0) ; const dv = new DataView(data.buffer, data.byteOffset, 13); width = dv.getUint32(0); height = dv.getUint32(4); ct = data[9]; }
    else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
  }
  const ch = ct === 0 ? 1 : ct === 2 ? 3 : ct === 3 ? 1 : ct === 4 ? 2 : 4;
  const stride = width * ch; const expected = height * (stride + 1);
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat), { maxOutputLength: expected + 1 });
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)]; const src = y * (stride + 1) + 1; const o = y * stride; const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) { for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= ch ? samples[o + i - ch] : 0); }
    else if (ft === 2) { for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0); }
    else if (ft === 3) { for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= ch ? samples[o + i - ch] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1); }
    else { for (let i = 0; i < stride; i++) { const a = i >= ch ? samples[o + i - ch] : 0; const b = y > 0 ? samples[p + i] : 0; const c = y > 0 && i >= ch ? samples[p + i - ch] : 0; samples[o + i] = raw[src + i] + paeth(a, b, c); } }
  }
  const n = width * height; const rgba = new Uint8Array(n * 4);
  if (ct === 6) rgba.set(samples);
  else if (ct === 2) { const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5]; for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) { rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2]; rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255; } }
  else if (ct === 0) { const key = trns === null ? -1 : trns[1]; for (let i = 0, d = 0; i < n; i++, d += 4) { const g = samples[i]; rgba[d] = rgba[d + 1] = rgba[d + 2] = g; rgba[d + 3] = g === key ? 0 : 255; } }
  else if (ct === 4) { for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) { rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s]; rgba[d + 3] = samples[s + 1]; } }
  else { const lut = new Uint8Array(palette.length / 3 * 4); const en = palette.length / 3; for (let e = 0; e < en; e++) { lut[e * 4] = palette[e * 3]; lut[e * 4 + 1] = palette[e * 3 + 1]; lut[e * 4 + 2] = palette[e * 3 + 2]; lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255; } for (let i = 0, d = 0; i < n; i++, d += 4) { const e = samples[i]; rgba[d] = lut[e * 4]; rgba[d + 1] = lut[e * 4 + 1]; rgba[d + 2] = lut[e * 4 + 2]; rgba[d + 3] = lut[e * 4 + 3]; } }
  return { width, height, rgba };
}
function pngOf(chunks) {
  let size = 8; for (const [, d] of chunks) size += 12 + d.length;
  const out = new Uint8Array(size); const view = new DataView(out.buffer);
  out.set([137, 80, 78, 71, 13, 10, 26, 10], 0); let at = 8;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    for (let i = 0; i < 4; i++) out[at + 4 + i] = type.charCodeAt(i);
    out.set(data, at + 8); view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length)); at += 12 + data.length;
  }
  return out;
}
function ihdrOf(w, h, ct) { const d = new Uint8Array(13); const v = new DataView(d.buffer); v.setUint32(0, w); v.setUint32(4, h); d[8] = 8; d[9] = ct; return d; }

// ---------- PNG filtering ----------
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) { for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0); }
  else if (type === 2) { for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]); }
  else if (type === 3) { for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1); }
  else { for (let i = 0; i < n; i++) { const a = i >= bpp ? cur[i - bpp] : 0; const b = prev === null ? 0 : prev[i]; const c = prev !== null && i >= bpp ? prev[i - bpp] : 0; out[i] = cur[i] - paeth(a, b, c); } }
}
function signedSum(row) { let s = 0; for (let i = 0; i < row.length; i++) { const v = row[i]; s += v < 128 ? v : 256 - v; } return s; }
function applyFilters(samples, stride, bpp, seq) {
  const raw = new Uint8Array(H * (stride + 1));
  for (let y = 0; y < H; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    filterRow(seq[y], cur, prev, bpp, raw.subarray(y * (stride + 1) + 1, (y + 1) * (stride + 1)));
    raw[y * (stride + 1)] = seq[y];
  }
  return raw;
}

// ---------- colour forms ----------
// Returns list of {ct, bpp, samples, pal, trns} candidates (usually 1-2).
export function buildForms(rgba) {
  const n = W * H;
  const map = new Map(); const cols = []; const freq = [];
  let allOpaque = true, isGrey = true;
  for (let i = 0; i < n; i++) {
    const r = rgba[i * 4], g = rgba[i * 4 + 1], b = rgba[i * 4 + 2], a = rgba[i * 4 + 3];
    if (a !== 255) allOpaque = false;
    if (!(r === g && g === b)) isGrey = false;
    const k = (r << 24) | (g << 16) | (b << 8) | a;
    let idx = map.get(k);
    if (idx === undefined) { idx = cols.length; map.set(k, idx); cols.push(k); freq.push(0); }
    freq[idx]++;
  }
  const forms = [];
  const distinct = cols.length;
  if (distinct <= 256) {
    // Two palette orderings: frequency, and adjacency-optimised (bg pinned at 0).
    const orderings = [];
    const byFreq = cols.map((_, i) => i).sort((a, b) => freq[b] - freq[a]);
    orderings.push(byFreq);
    // adjacency matrix from horizontal + vertical neighbours
    const adj = new Uint32Array(256 * 256);
    const pixIdx = new Uint8Array(n);
    for (let i = 0; i < n; i++) pixIdx[i] = map.get((rgba[i * 4] << 24) | (rgba[i * 4 + 1] << 16) | (rgba[i * 4 + 2] << 8) | rgba[i * 4 + 3]);
    for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) {
      const i = y * W + x;
      if (x + 1 < W) { const a = pixIdx[i], b = pixIdx[i + 1]; if (a !== b) { adj[a * 256 + b]++; adj[b * 256 + a]++; } }
      if (y + 1 < H) { const a = pixIdx[i], b = pixIdx[i + W]; if (a !== b) { adj[a * 256 + b]++; adj[b * 256 + a]++; } }
    }
    const bg = byFreq[0];
    const order = [bg]; const used = new Uint8Array(256); used[bg] = 1;
    for (let s = 1; s < distinct; s++) {
      let best = -1, bestScore = -1;
      for (let c = 0; c < distinct; c++) {
        if (used[c]) continue;
        let sc = 0; for (let j = 0; j < s; j++) sc += adj[c * 256 + order[j]];
        sc += adj[c * 256 + order[s - 1]] * 2;
        if (sc > bestScore) { bestScore = sc; best = c; }
      }
      order.push(best); used[best] = 1;
    }
    // pairwise-swap local search on sum |idx[u]-idx[v]| over adjacent pairs (delta via adj rows)
    const posOf = new Int32Array(256);
    const costOf = () => { let t = 0; for (let a = 0; a < distinct; a++) for (let b = a + 1; b < distinct; b++) { const w = adj[a * 256 + b]; if (w) t += w * Math.abs(posOf[a] - posOf[b]); } return t; };
    for (let i = 0; i < distinct; i++) posOf[order[i]] = i;
    let curCost = costOf();
    for (let pass = 0; pass < 2; pass++) {
      let improved = false;
      for (let i = 0; i < distinct; i++) for (let j = i + 1; j < distinct; j++) {
        const a = order[i], b = order[j];
        let delta = 0;
        for (let c = 0; c < distinct; c++) {
          if (c === a || c === b) continue;
          const w1 = adj[a * 256 + c], w2 = adj[b * 256 + c];
          delta += w1 * (Math.abs(j - posOf[c]) - Math.abs(i - posOf[c])) + w2 * (Math.abs(i - posOf[c]) - Math.abs(j - posOf[c]));
        }
        if (delta < 0) { order[i] = b; order[j] = a; posOf[a] = j; posOf[b] = i; curCost += delta; improved = true; }
      }
      if (!improved) break;
    }
    orderings.push(order);
    for (const ord of orderings) {
      const lut = new Uint8Array(256); for (let i = 0; i < distinct; i++) lut[ord[i]] = i;
      const samples = new Uint8Array(n);
      for (let i = 0; i < n; i++) samples[i] = lut[pixIdx[i]];
      const pal = new Uint8Array(distinct * 3); const trns = new Uint8Array(distinct);
      let hasTrns = false;
      for (let i = 0; i < distinct; i++) { const k = cols[ord[i]]; pal[i * 3] = (k >>> 24) & 255; pal[i * 3 + 1] = (k >>> 16) & 255; pal[i * 3 + 2] = (k >>> 8) & 255; trns[i] = k & 255; if ((k & 255) !== 255) hasTrns = true; }
      forms.push({ ct: 3, bpp: 1, samples, pal, trns: hasTrns ? trns : null, tag: 'pal' });
    }
  }
  if (isGrey && allOpaque) {
    const samples = new Uint8Array(n);
    for (let i = 0; i < n; i++) samples[i] = rgba[i * 4];
    forms.push({ ct: 0, bpp: 1, samples, pal: null, trns: null, tag: 'grey' });
  }
  if (allOpaque && !isGrey) {
    const samples = new Uint8Array(n * 3);
    for (let i = 0, d = 0; i < n; i++, d += 3) { samples[d] = rgba[i * 4]; samples[d + 1] = rgba[i * 4 + 1]; samples[d + 2] = rgba[i * 4 + 2]; }
    forms.push({ ct: 2, bpp: 3, samples, pal: null, trns: null, tag: 'rgb' });
  }
  if (isGrey && !allOpaque) {
    const samples = new Uint8Array(n * 2);
    for (let i = 0, d = 0; i < n; i++, d += 2) { samples[d] = rgba[i * 4]; samples[d + 1] = rgba[i * 4 + 3]; }
    forms.push({ ct: 4, bpp: 2, samples, pal: null, trns: null, tag: 'ga' });
  }
  if (!allOpaque && !isGrey) {
    forms.push({ ct: 6, bpp: 4, samples: rgba, pal: null, trns: null, tag: 'rgba' });
  }
  return forms;
}

// ---------- filter candidates ----------
// Each candidate: {name, seq(Uint8Array 720), raw, z1} where z1 = deflate level-1 size (ranking).
export function filterCandidates(form) {
  const { samples, bpp } = form; const stride = W * bpp;
  const cands = [];
  const mk = (name, seq) => { const raw = applyFilters(samples, stride, bpp, seq); cands.push({ name, seq, raw, z1: deflateSync(raw, { level: 6 }).length, z6: 0 }); };
  const all = (t) => { const s = new Uint8Array(H); s.fill(t); return s; };
  mk('none', all(0)); mk('paeth', all(4));
  // SmartUp (palette / single-byte): identical row with a horizontal change -> Up, else None
  if (bpp === 1) {
    const seq = new Uint8Array(H);
    for (let y = 0; y < H; y++) {
      if (y === 0) { seq[y] = 0; continue; }
      const cur = samples.subarray(y * stride, (y + 1) * stride); const prev = samples.subarray((y - 1) * stride, y * stride);
      let same = true, change = false;
      for (let i = 0; i < stride; i++) { if (cur[i] !== prev[i]) { same = false; break; } }
      if (same) { for (let i = 1; i < stride; i++) if (cur[i] !== cur[i - 1]) { change = true; break; } seq[y] = change ? 2 : 0; }
      else seq[y] = 0;
    }
    mk('smartup', seq);
  }
  // per-row brute force: each row compressed level 6 with previous 32K filtered bytes as dictionary
  let rowCosts = null;
  {
    const seq = new Uint8Array(H); const trial = Array.from({ length: 5 }, () => new Uint8Array(stride));
    const filteredSoFar = new Uint8Array(H * (stride + 1));
    rowCosts = new Float64Array(H * 5);
    for (let y = 0; y < H; y++) {
      const cur = samples.subarray(y * stride, (y + 1) * stride); const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
      for (let t = 0; t < 5; t++) filterRow(t, cur, prev, bpp, trial[t]);
      const dictStart = Math.max(0, y * (stride + 1) - 32768);
      const dict = filteredSoFar.subarray(dictStart, y * (stride + 1));
      let best = Infinity, bt = 0;
      for (let t = 0; t < 5; t++) { const sz = deflateSync(trial[t], { level: 3, dictionary: dict }).length; rowCosts[y * 5 + t] = sz; if (sz < best) { best = sz; bt = t; } }
      seq[y] = bt;
      filteredSoFar[y * (stride + 1)] = bt;
      filteredSoFar.set(trial[bt], y * (stride + 1) + 1);
    }
    mk('brute', seq);
  }
  // Viterbi over the per-row costs with switch penalties (bytes): keeps filters stable
  // where switching costs more than it saves (brute force switches freely).
  {
    let bestSeq = null, bestTot = Infinity;
    for (const pen of [4, 12, 32, 80, 200]) {
      const dp = new Float64Array(H * 5);
      const back = new Int8Array(H * 5);
      for (let t = 0; t < 5; t++) dp[t] = rowCosts[t];
      for (let y = 1; y < H; y++) {
        for (let t = 0; t < 5; t++) {
          let bv = Infinity, bt = 0;
          for (let p = 0; p < 5; p++) { const v = dp[(y - 1) * 5 + p] + (p === t ? 0 : pen); if (v < bv) { bv = v; bt = p; } }
          dp[y * 5 + t] = bv + rowCosts[y * 5 + t]; back[y * 5 + t] = bt;
        }
      }
      let bt = 0; for (let t = 1; t < 5; t++) if (dp[(H - 1) * 5 + t] < dp[(H - 1) * 5 + bt]) bt = t;
      const tot = dp[(H - 1) * 5 + bt];
      if (tot < bestTot) {
        bestTot = tot;
        const seq = new Uint8Array(H); seq[H - 1] = bt;
        for (let y = H - 1; y > 0; y--) { bt = back[y * 5 + bt]; seq[y - 1] = bt; }
        bestSeq = seq;
      }
    }
    if (bestSeq) mk('viterbi', bestSeq);
  }
  // band16: one filter per 16-row band by level-6 compression with dict
  {
    const seq = new Uint8Array(H); const band = 16;
    const filteredSoFar = new Uint8Array(H * (stride + 1));
    for (let b0 = 0; b0 < H; b0 += band) {
      const rows = Math.min(band, H - b0);
      let best = Infinity, bt = 0;
      for (let t = 0; t < 5; t++) {
        const s = new Uint8Array(H); // dummy; build band raw directly
        const bandRaw = new Uint8Array(rows * (stride + 1));
        for (let r = 0; r < rows; r++) {
          const y = b0 + r; const cur = samples.subarray(y * stride, (y + 1) * stride); const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
          filterRow(t, cur, prev, bpp, bandRaw.subarray(r * (stride + 1) + 1, (r + 1) * (stride + 1))); bandRaw[r * (stride + 1)] = t;
        }
        const dictStart = Math.max(0, b0 * (stride + 1) - 32768);
        const dict = filteredSoFar.subarray(dictStart, b0 * (stride + 1));
        const sz = deflateSync(bandRaw, { level: 6, dictionary: dict }).length;
        if (sz < best) { best = sz; bt = t; }
      }
      for (let r = 0; r < rows; r++) seq[b0 + r] = bt;
      // materialise chosen band into filteredSoFar for later dicts
      for (let r = 0; r < rows; r++) {
        const y = b0 + r; const cur = samples.subarray(y * stride, (y + 1) * stride); const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
        filterRow(bt, cur, prev, bpp, filteredSoFar.subarray(y * (stride + 1) + 1, (y + 1) * (stride + 1))); filteredSoFar[y * (stride + 1)] = bt;
      }
    }
    mk('band16', seq);
  }
  // Rank by level-6 size (level 1 alone mis-ranks: i002 band16 beats brute at 6/9 but not at 1).
  cands.sort((a, b) => a.z1 - b.z1);
  for (const c of cands) c.z6 = c.z1;
  return cands;
}

// ---------- length-limited Huffman (optimal lengths + zlib-style overflow fix) ----------
// Returns Uint8Array of code lengths, maxLen enforced, Kraft sum exact (1, or 1/2 for a single symbol).
export function huffmanLengths(freq, maxLen) {
  const n = freq.length;
  const used = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) used.push(i);
  const out = new Uint8Array(n);
  if (used.length === 0) return out;
  if (used.length === 1) { out[used[0]] = 1; return out; }
  // Node arrays: f[], sym[] (-1 internal), left[], right[], par[].
  const f = [], sym = [], left = [], right = [], par = [];
  const addNode = (ff, ss, l, r) => { f.push(ff); sym.push(ss); left.push(l); right.push(r); par.push(-1); return f.length - 1; };
  const leafIdx = new Int32Array(n); leafIdx.fill(-1);
  for (const s of used) leafIdx[s] = addNode(freq[s], s, -1, -1);
  const q1 = used.map((s) => leafIdx[s]).sort((a, b) => f[a] - f[b] || sym[a] - sym[b]);
  const q2 = [];
  let li = 0, ii = 0;
  const take = () => {
    const lf = li < q1.length ? f[q1[li]] : Infinity;
    const inf = ii < q2.length ? f[q2[ii]] : Infinity;
    if (lf <= inf) return q1[li++];
    return q2[ii++];
  };
  while ((q1.length - li) + (q2.length - ii) > 1) {
    const a = take(), b = take();
    const nd = addNode(f[a] + f[b], -1, a, b);
    par[a] = nd; par[b] = nd; q2.push(nd);
  }
  const rawLen = new Int32Array(n);
  let maxL = 0;
  for (const s of used) { let d = 0, x = leafIdx[s]; while (par[x] !== -1) { x = par[x]; d++; } rawLen[s] = d; if (d > maxL) maxL = d; }
  if (maxL <= maxLen) { for (const s of used) out[s] = rawLen[s]; return out; }
  // Length-limit: cap at maxLen, then repair Kraft exactly by lengthening the
  // least-frequent symbols (each +1 halves that symbol's Kraft contribution).
  for (const s of used) out[s] = rawLen[s] > maxLen ? maxLen : rawLen[s];
  let S = 0;
  for (const s of used) S += 1 << (maxLen - out[s]);
  let D = S - (1 << maxLen); // > 0: must remove D units of Kraft
  const order = used.slice().sort((a, b) => freq[a] - freq[b] || a - b);
  let guard = 0;
  while (D !== 0 && guard++ < 10000) {
    if (D > 0) {
      // Lengthen a symbol: prefer the largest Kraft reduction <= D (least frequent on ties);
      // if none fits, take the smallest reduction and overshoot, then fix below by shortening.
      let pick = -1, pickRed = 0, minRed = Infinity, minPick = -1;
      for (const s of order) {
        if (out[s] >= maxLen) continue;
        const red = 1 << (maxLen - out[s] - 1);
        if (red <= D && red > pickRed) { pick = s; pickRed = red; }
        if (red < minRed) { minRed = red; minPick = s; }
      }
      if (pick === -1) { pick = minPick; pickRed = minRed; }
      out[pick]++; D -= pickRed;
    } else {
      // Shorten the longest-length, least-frequent symbol (smallest Kraft increase first).
      const cand = order.filter((s) => out[s] > 1).sort((a, b) => out[b] - out[a] || freq[a] - freq[b]);
      const s = cand[0];
      const ln = out[s] - 1; // new length after shortening
      out[s] = ln; D += 1 << (maxLen - ln - 1); // delta of shortening l -> l-1 is 2^(maxLen-l)
    }
  }
  return out;
}
function kraftOk(lengths) {
  // Exact check in 2^15 units (single-symbol alphabet: 2^14).
  let used = 0, sum = 0;
  for (let i = 0; i < lengths.length; i++) if (lengths[i] > 0) { used++; sum += 1 << (15 - lengths[i]); }
  if (used === 0) return true;
  if (used === 1) return sum === 16384;
  return sum === 32768;
}
function canonicalCodes(lengths) {
  const maxL = Math.max(0, ...lengths);
  const bl = new Int32Array(maxL + 2);
  for (const l of lengths) if (l > 0) bl[l]++;
  const next = new Int32Array(maxL + 2);
  let code = 0;
  for (let b = 1; b <= maxL; b++) { code = (code + bl[b - 1]) << 1; next[b] = code; }
  const codes = new Int32Array(lengths.length);
  for (let i = 0; i < lengths.length; i++) {
    if (lengths[i] > 0) {
      // DEFLATE packs Huffman codes MSB-first; our writer is LSB-first, so store bit-reversed codes.
      let c = next[lengths[i]]++, r = 0;
      for (let b = 0; b < lengths[i]; b++) { r = (r << 1) | (c & 1); c >>= 1; }
      codes[i] = r;
    }
  }
  return codes;
}
function revBits(v, len) { let r = 0; for (let b = 0; b < len; b++) { r = (r << 1) | (v & 1); v >>= 1; } return r; }

// ---------- bit writer (one shared writer across all blocks) ----------
class BitWriter {
  constructor(cap) { this.buf = new Uint8Array(cap); this.pos = 0; this.bitBuf = 0; this.bitCnt = 0; }
  write(v, len) {
    this.bitBuf |= (v & ((len === 32 ? 0xffffffff : (1 << len) - 1))) << this.bitCnt;
    this.bitCnt += len;
    while (this.bitCnt >= 8) { this.buf[this.pos++] = this.bitBuf & 255; this.bitBuf >>>= 8; this.bitCnt -= 8; }
  }
  align() { if (this.bitCnt > 0) { this.buf[this.pos++] = this.bitBuf & 255; this.bitBuf = 0; this.bitCnt = 0; } }
  bytes() { return this.buf.subarray(0, this.pos); }
}

// ---------- dynamic-header RLE ----------
// Returns {tokens: [[sym, extraVal, extraBits]...], clLen, hlit, hdist, hclen, headerBits}
function rleHeader(litLen, distLen) {
  let hlit = 257; while (hlit > 257 && litLen[hlit - 1] === 0) hlit--;
  hlit = 257; for (let i = 286; i > 257; i--) if (litLen[i - 1] > 0) { hlit = i; break; }
  let hdist = 1; for (let i = 30; i > 1; i--) if (distLen[i - 1] > 0) { hdist = i; break; }
  const seq = new Uint8Array(hlit + hdist);
  seq.set(litLen.subarray(0, hlit), 0); seq.set(distLen.subarray(0, hdist), hlit);
  const tokens = []; const clFreq = new Int32Array(19);
  let i = 0;
  while (i < seq.length) {
    const v = seq[i]; let run = 1; while (i + run < seq.length && seq[i + run] === v) run++;
    if (v === 0) {
      let r = run;
      while (r > 0) {
        if (r >= 11) { const c = Math.min(r, 138); tokens.push([18, c - 11, 7]); clFreq[18]++; r -= c; }
        else if (r >= 3) { const c = Math.min(r, 10); tokens.push([17, c - 3, 3]); clFreq[17]++; r -= c; }
        else { tokens.push([0, 0, 0]); clFreq[0]++; r--; }
      }
    } else {
      tokens.push([v, 0, 0]); clFreq[v]++; let r = run - 1;
      while (r > 0) {
        if (r < 3) { tokens.push([v, 0, 0]); clFreq[v]++; r--; }
        else { const c = Math.min(r, 6); tokens.push([16, c - 3, 2]); clFreq[16]++; r -= c; }
      }
    }
    i += run;
  }
  const clLen = huffmanLengths(clFreq, 7);
  let hclen = 4; for (let k = 19; k > 4; k--) if (clLen[CL_ORDER[k - 1]] > 0) { hclen = k; break; }
  let headerBits = 3 + 5 + 5 + 4 + 3 * hclen;
  for (const [s, , eb] of tokens) headerBits += clLen[s] + eb;
  return { tokens, clLen, hlit, hdist, hclen, headerBits };
}

// Precomputed per-bestLen candidate length sets (sublen expansion to length-code endpoints + 3 + bestLen).
const CAND = (() => {
  const out = new Array(259);
  for (let bl = 0; bl <= 258; bl++) {
    if (bl < 3) { out[bl] = []; continue; }
    const set = new Set([3, bl]);
    for (let s = 0; s < 29; s++) {
      const hi = Math.min(LEN_BASE[s] + ((1 << LEN_EXTRA[s]) - 1), 258);
      if (hi > 3 && hi <= bl) set.add(hi);
      const lo = LEN_BASE[s];
      if (lo > 3 && lo <= bl) set.add(lo);
    }
    let arr = [...set].sort((a, b) => a - b);
    if (arr.length > 8) arr = [3, ...arr.filter((x) => x !== 3).slice(-7)];
    out[bl] = arr;
  }
  return out;
})();
const DIST_SYM = (() => { const t = new Uint8Array(32769); for (let d = 1; d <= 32768; d++) t[d] = distSym(d); return t; })();

let CMP_SIGN = 0;
export function finderSweep(data, rowStride, bpp) {
  const n = data.length;
  const bestLen = new Uint16Array(n);
  const bestDist = new Uint16Array(n);
  const altDist3 = new Uint16Array(n);
  const dist8 = new Uint16Array(n);
  const dist32 = new Uint16Array(n);
  const dist128 = new Uint16Array(n);
  const runLen = new Uint16Array(n);
  const perLen = new Uint16Array(n);
  for (let i = n - 1; i >= 0; i--) {
    runLen[i] = i + 1 < n && data[i] === data[i + 1] ? (runLen[i + 1] >= 520 ? 520 : runLen[i + 1] + 1) : 1;
    perLen[i] = bpp > 1 && i + bpp < n && data[i] === data[i + bpp] ? (i + 1 < n && perLen[i + 1] >= 520 ? 520 : (i + 1 < n ? perLen[i + 1] : 0) + 1) : 0;
  }
  const left = new Int32Array(n).fill(-1);
  const right = new Int32Array(n).fill(-1);
  const root = new Int32Array(65536).fill(-1);
  const head = new Int32Array(65536).fill(-1);
  const prev = new Int32Array(n).fill(-1);
  let visits = 0;
  const hash3 = (p) => (Math.imul(((data[p] << 16) | (data[p + 1] << 8) | data[p + 2]), 2654435761) >>> 16) & 65535;
  const wordAt = (p) => data[p] | (data[p + 1] << 8) | (data[p + 2] << 16) | (data[p + 3] << 24);
  const matchLenAt = (p, q, cap) => {
    let l = 0; const m = Math.min(cap, n - p);
    while (l + 4 <= m && wordAt(p + l) === wordAt(q + l)) l += 4;
    while (l < m && data[p + l] === data[q + l]) l++;
    return l;
  };
  // Sets CMP_SIGN (-1/0/1: suffix p vs suffix q) and returns common prefix length.
  const cmpSuffix = (p, q, cap) => {
    let l = 0; const m = Math.min(cap, n - p, n - q);
    while (l + 4 <= m && wordAt(p + l) === wordAt(q + l)) l += 4;
    while (l < m && data[p + l] === data[q + l]) l++;
    if (l === m) { CMP_SIGN = 0; return l; }
    CMP_SIGN = data[p + l] < data[q + l] ? -1 : 1; return l;
  };
  for (let pos = 0; pos < n; pos++) {
    if (pos + 3 > n) continue;
    const rl = runLen[pos];
    let best = 0, bd = 0, a3 = 0, d8 = 0, d32 = 0, d128 = 0;
    // Record one candidate (length, dist): longest match + shortest dist per length threshold.
    const note = (l, d) => {
      if (l > best || (l === best && d < bd)) { best = l; bd = d; }
      if (l >= 3 && (a3 === 0 || d < a3)) a3 = d;
      if (l >= 8 && (d8 === 0 || d < d8)) d8 = d;
      if (l >= 32 && (d32 === 0 || d < d32)) d32 = d;
      if (l >= 128 && (d128 === 0 || d < d128)) d128 = d;
    };
    // dist-1 match: valid only inside a run (byte before pos equals byte at pos); length = runLen[pos].
    if (rl >= 3 && pos >= 1 && data[pos - 1] === data[pos]) note(Math.min(rl, 258), 1);
    // dist-bpp match: length at pos is the period run starting one period back.
    if (bpp > 1 && pos >= bpp && perLen[pos - bpp] >= 3) note(Math.min(perLen[pos - bpp], 258), bpp);
    if (rowStride > 0) {
      for (let k = 1; k <= 2; k++) {
        const q = pos - k * rowStride; if (q < 0) break;
        note(matchLenAt(pos, q, 258), pos - q);
      }
    }
    const h = hash3(pos);
    if (best < TUNE.skipBest) {
      let node = head[h], c = 0;
      while (node >= 0 && c < TUNE.chainCap) {
        if (pos - node <= 32768) {
          const l = matchLenAt(pos, node, 258);
          note(l, pos - node);
          if (l >= 258) break;
        }
        node = prev[node]; c++;
      }
      if (best < 258) {
        let node2 = root[h], depth = 0;
        while (node2 >= 0 && depth < TUNE.depthCap) {
          visits++;
          const l = cmpSuffix(pos, node2, 258);
          // Tree walk updates only the longest match (threshold dists come from run/period/row/chain).
          if (pos - node2 <= 32768 && l > best) { best = l; bd = pos - node2; }
          if (l >= 258 || CMP_SIGN === 0) break;
          node2 = CMP_SIGN < 0 ? left[node2] : right[node2]; depth++;
        }
        // Skip inserting run-interior positions (the run-start node covers the same content).
        if (rl < 258 && !(rl >= 16 && pos >= 1 && data[pos - 1] === data[pos])) {
          if (root[h] === -1) root[h] = pos;
          else {
            let cur = root[h], depth2 = 0;
            while (depth2 < TUNE.depthCap) {
              cmpSuffix(pos, cur, 258);
              if (CMP_SIGN <= 0) { if (left[cur] === -1) { left[cur] = pos; break; } cur = left[cur]; }
              else { if (right[cur] === -1) { right[cur] = pos; break; } cur = right[cur]; }
              depth2++;
            }
          }
        }
      }
    }
    prev[pos] = head[h]; head[h] = pos;
    bestLen[pos] = best; bestDist[pos] = bd; altDist3[pos] = a3; dist8[pos] = d8; dist32[pos] = d32; dist128[pos] = d128;
  }
  return { bestLen, bestDist, altDist3, dist8, dist32, dist128, visits };
}

export const TUNE = { iters: 0, blockTarget: 524288, filterSplit: 131072, depthCap: 160, skipBest: 24, chainCap: 8 };

// ---------- optimal parse + custom DEFLATE ----------
function parseBlock(data, bs, be, finder) {
  const len = be - bs;
  const cost = new Float64Array(len + 1);
  const chLen = new Uint16Array(len + 1);
  const chDist = new Int32Array(len + 1);
  let litCost = new Float64Array(256);
  for (let i = 0; i < 256; i++) litCost[i] = FIXED_LIT[i];
  let lenCost = new Float64Array(29);
  for (let s = 0; s < 29; s++) lenCost[s] = FIXED_LIT[257 + s];
  let distCost = new Float64Array(30).fill(5);
  const lenCostByLen = new Float64Array(259);
  function runDP() {
    cost.fill(Infinity); cost[0] = 0; chLen.fill(0); chDist.fill(0);
    for (let L = 3; L <= 258; L++) { const s = lenSym(L); lenCostByLen[L] = lenCost[s] + LEN_EXTRA[s]; }
    for (let i = 0; i < len; i++) {
      const base = cost[i]; if (!isFinite(base)) continue;
      const p = bs + i;
      const lc = base + litCost[data[p]];
      if (lc < cost[i + 1]) { cost[i + 1] = lc; chLen[i + 1] = 1; chDist[i + 1] = -1; }
      const bl = finder.bestLen[p];
      if (bl >= 3) {
        // Per-length best distance: shortest dist achieving >= L (threshold tables).
        for (const L of CAND[bl]) {
          if (i + L > len) continue;
          let d;
          if (L <= 3) d = finder.altDist3[p] || finder.bestDist[p];
          else if (L <= 8) d = finder.dist8[p] || finder.bestDist[p];
          else if (L <= 32) d = finder.dist32[p] || finder.bestDist[p];
          else if (L <= 128) d = finder.dist128[p] || finder.bestDist[p];
          else d = finder.bestDist[p];
          const dSym = DIST_SYM[d];
          const c = base + lenCostByLen[L] + distCost[dSym] + DIST_EXTRA[dSym];
          if (c < cost[i + L]) { cost[i + L] = c; chLen[i + L] = L; chDist[i + L] = d; }
        }
      }
    }
    const toks = []; let i = len;
    while (i > 0) { const L = chLen[i]; if (L === 1) { toks.push([data[bs + i - 1], -1]); i--; } else { toks.push([L, chDist[i]]); i -= L; } }
    toks.reverse();
    return toks;
  }
  let kraftFail = 0;
  function evalTokens(toks) {
    const lf = new Int32Array(286), df = new Int32Array(30);
    for (const [a, b] of toks) { if (b === -1) lf[a]++; else { lf[257 + lenSym(a)]++; df[distSym(b)]++; } }
    lf[256] = 1;
    const ll = huffmanLengths(lf, 15), dl = huffmanLengths(df, 15);
    if (df.every((v) => v === 0)) dl[0] = 1;
    if (!kraftOk(ll) || !kraftOk(dl)) { kraftFail++; return { tot: Infinity, useFixed: true, toks, ll, dl, hdr: null }; }
    const hdr = rleHeader(ll, dl);
    let bits = hdr.headerBits + ll[256];
    for (const [a, b] of toks) { if (b === -1) bits += ll[a]; else { const s = lenSym(a); bits += ll[257 + s] + LEN_EXTRA[s] + dl[distSym(b)] + DIST_EXTRA[distSym(b)]; } }
    let fbits = 3 + FIXED_LIT[256];
    for (const [a, b] of toks) { if (b === -1) fbits += FIXED_LIT[a]; else { const s = lenSym(a); fbits += FIXED_LIT[257 + s] + LEN_EXTRA[s] + 5 + DIST_EXTRA[distSym(b)]; } }
    return { tot: Math.min(bits, fbits), useFixed: fbits <= bits, toks, ll, dl, hdr, bits, fbits };
  }
  function derive(e, damp) {
    const nl = new Float64Array(256), nlen = new Float64Array(29), nd = new Float64Array(30);
    for (let i = 0; i < 256; i++) nl[i] = e.ll[i] > 0 ? e.ll[i] : litCost[i];
    for (let s = 0; s < 29; s++) nlen[s] = e.ll[257 + s] > 0 ? e.ll[257 + s] : lenCost[s];
    for (let s = 0; s < 30; s++) nd[s] = e.dl[s] > 0 ? e.dl[s] : distCost[s];
    if (damp) { for (let i = 0; i < 256; i++) nl[i] = (nl[i] + litCost[i]) / 2; for (let s = 0; s < 29; s++) nlen[s] = (nlen[s] + lenCost[s]) / 2; for (let s = 0; s < 30; s++) nd[s] = (nd[s] + distCost[s]) / 2; }
    litCost = nl; lenCost = nlen; distCost = nd;
  }
  let best = null;
  const keep = (toks) => { const e = evalTokens(toks); if (e.tot < (best ? best.tot : Infinity)) best = e; return e; };
  let e = keep(runDP());
  const iters = TUNE.iters > 0 ? TUNE.iters : 3;
  for (let it = 1; it < iters; it++) { derive(e, it === 2); e = keep(runDP()); }
  // Basin B (literal-friendly): only when literal-heavy and block not huge.
  if (best && best.tot / Math.max(1, len) > 5 && len < 200000) {
    const bf = new Int32Array(256);
    for (let i = 0; i < len; i++) bf[data[bs + i]]++;
    for (let i = 0; i < 256; i++) { const p = (bf[i] + 1) / (len + 256); let c = -Math.log2(p); litCost[i] = c < 1 ? 1 : c > 15 ? 15 : c; }
    lenCost = new Float64Array(29).fill(20); distCost = new Float64Array(30).fill(20);
    e = keep(runDP());
    derive(e, false); e = keep(runDP());
  }
  return { best, kraftFail };
}

export function customDeflate(data, rowStride, bpp) {
  const n = data.length;
  const finder = finderSweep(data, rowStride, bpp);
  // Block boundaries: row-aligned, ~128 KiB, also split at filter changes once >= 32 KiB.
  const rowBytes = rowStride;
  const bounds = [0];
  let acc = 0, prevF = data[0];
  for (let r = 0; r < H; r++) {
    const f = data[r * rowBytes];
    acc += rowBytes;
    if (acc >= TUNE.blockTarget || (f !== prevF && acc >= TUNE.filterSplit)) { bounds.push((r + 1) * rowBytes); acc = 0; }
    prevF = f;
  }
  if (bounds[bounds.length - 1] !== n) bounds.push(n);
  const blocks = [];
  let kraftFail = 0;
  for (let b = 0; b < bounds.length - 1; b++) {
    const r = parseBlock(data, bounds[b], bounds[b + 1], finder);
    kraftFail += r.kraftFail;
    blocks.push(r.best);
  }
  const cap = n * 2 + 65536;
  const w = new BitWriter(cap);
  for (let b = 0; b < blocks.length; b++) {
    const blk = blocks[b]; const last = b === blocks.length - 1;
    if (blk.useFixed || blk.hdr === null) {
      w.write((last ? 1 : 0) | 2, 3);
      const litC = canonicalCodes(FIXED_LIT);
      const distC = new Int32Array(30); for (let i = 0; i < 30; i++) distC[i] = i;
      for (const [a, d] of blk.toks) {
        if (d === -1) w.write(litC[a], FIXED_LIT[a]);
        else { const s = lenSym(a); w.write(litC[257 + s], FIXED_LIT[257 + s]); if (LEN_EXTRA[s]) w.write(a - LEN_BASE[s], LEN_EXTRA[s]); const ds = distSym(d); w.write(revBits(ds, 5), 5); if (DIST_EXTRA[ds]) w.write(d - DIST_BASE[ds], DIST_EXTRA[ds]); }
      }
      w.write(litC[256], FIXED_LIT[256]);
    } else {
      w.write((last ? 1 : 0) | 4, 3);
      const { hdr, ll, dl } = blk;
      w.write(hdr.hlit - 257, 5); w.write(hdr.hdist - 1, 5); w.write(hdr.hclen - 4, 4);
      for (let k = 0; k < hdr.hclen; k++) w.write(hdr.clLen[CL_ORDER[k]], 3);
      const clC = canonicalCodes(hdr.clLen);
      for (const [s, ev, eb] of hdr.tokens) { w.write(clC[s], hdr.clLen[s]); if (eb) w.write(ev, eb); }
      const litC = canonicalCodes(ll), distC = canonicalCodes(dl);
      for (const [a, d] of blk.toks) {
        if (d === -1) w.write(litC[a], ll[a]);
        else { const s = lenSym(a); w.write(litC[257 + s], ll[257 + s]); if (LEN_EXTRA[s]) w.write(a - LEN_BASE[s], LEN_EXTRA[s]); const ds = distSym(d); w.write(distC[ds], dl[ds]); if (DIST_EXTRA[ds]) w.write(d - DIST_BASE[ds], DIST_EXTRA[ds]); }
      }
      w.write(litC[256], ll[256]);
    }
  }
  w.align();
  const body = w.bytes();
  const out = new Uint8Array(2 + body.length + 4);
  out[0] = 0x78; out[1] = 0x9c; out.set(body, 2);
  const ad = adler32(data); const v = new DataView(out.buffer);
  v.setUint32(2 + body.length, ad);
  return { bytes: out, kraftFail, blocks: blocks.length, visits: finder.visits };
}

// ---------- main ----------
function main() {
  const ids = readdirSync(IN).sort();
  for (const id of ids) {
    const bytes = new Uint8Array(readFileSync(join(IN, id, 'image.png')));
    const { rgba } = decodePng(bytes);
    const forms = buildForms(rgba);
    let bestOut = null, bestInfo = null;
    // Prune duplicate palette orderings by filter-None level-1 size first.
    const pals = forms.filter((f) => f.tag === 'pal');
    if (pals.length > 1) {
      let keepPal = pals[0], keepZ = Infinity;
      for (const f of pals) {
        const stride = W; const seq = new Uint8Array(H);
        const raw = applyFilters(f.samples, stride, 1, seq);
        const z = deflateSync(raw, { level: 1 }).length;
        if (z < keepZ) { keepZ = z; keepPal = f; }
      }
      for (let i = forms.length - 1; i >= 0; i--) if (forms[i].tag === 'pal' && forms[i] !== keepPal) forms.splice(i, 1);
    }
    // Evaluate forms: rank by level-6 size of their best filter candidate; run the
    // custom parse only on forms within 8% of the best (a clearly worse form cannot win).
    const formEvals = [];
    for (const form of forms) {
      const cands = filterCandidates(form);
      formEvals.push({ form, cand: cands[0], z6: cands[0].z6 || cands[0].z1 });
    }
    formEvals.sort((a, b) => a.z6 - b.z6);
    const bestZ6 = formEvals[0].z6;
    for (const ev of formEvals) {
      const { form, cand } = ev;
      if (formEvals.length > 1 && ev.z6 > bestZ6 * 1.08) continue;
      const lib = deflateSync(cand.raw, { level: 9 });
      const custom = customDeflate(cand.raw, W * form.bpp + 1, form.bpp);
      const useCustom = custom.bytes.length <= lib.length;
      const payload = useCustom ? custom.bytes : lib;
      const chunks = [['IHDR', ihdrOf(W, H, form.ct)]];
      if (form.pal) chunks.push(['PLTE', form.pal]);
      if (form.trns) { let t = form.trns.length; while (t > 0 && form.trns[t - 1] === 255) t--; if (t > 0) chunks.push(['tRNS', form.trns.subarray(0, t)]); }
      chunks.push(['IDAT', payload]);
      chunks.push(['IEND', new Uint8Array(0)]);
      const png = pngOf(chunks);
      if (!bestOut || png.length < bestOut.length) {
        bestOut = png;
        bestInfo = { id, form: form.tag, filter: cand.name, z6: cand.z6 || cand.z1, custom: custom.bytes.length, lib: lib.length, useCustom, png: png.length, kraftFail: custom.kraftFail, blocks: custom.blocks, visitsPerPos: (custom.visits / cand.raw.length).toFixed(1) };
      }
    }
    mkdirSync(join(OUT, id), { recursive: true });
    writeFileSync(join(OUT, id, 'image.png'), bestOut);
    console.error(JSON.stringify(bestInfo));
  }
}
if (process.argv[1] && process.argv[1].endsWith('main.ts')) main();
