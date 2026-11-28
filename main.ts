// PNG Squeeze R14 — R6 dual-basin parse + R12 sorted-bucket finder (+16, no run
// skipping) + full leaders filter search. Single file, Node stdlib only.
// Reads /input/<id>/image.png (or MAKEFUN_INPUT_DIR), writes /output/<id>/image.png
// (or MAKEFUN_OUTPUT_DIR). Deterministic: fixed budgets, no clock, no randomness.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { deflateSync, inflateSync } from 'node:zlib';

const STATS = process.env.SQ_STATS === '1';
const slog = (...a) => { if (STATS) console.error(...a); };

// ---------- CRC32 / Adler32 / PNG ----------
const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; t[n] = c; }
  return t;
})();
function crc32(bytes, start = 0, end = bytes.length) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}
function adler32(bytes) {
  let a = 1, b = 0;
  for (let i = 0; i < bytes.length;) {
    const end = Math.min(bytes.length, i + 5552);
    for (; i < end; i++) { a += bytes[i]; b += a; }
    a %= 65521; b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}
const ascii = (s) => Uint8Array.from(s, (ch) => ch.charCodeAt(0));
function pngOf(chunks) {
  let size = 8;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set([137, 80, 78, 71, 13, 10, 26, 10], 0);
  let at = 8;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    out.set(ascii(type), at + 4);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}
function ihdrOf(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width); v.setUint32(4, height);
  d[8] = 8; d[9] = colourType;
  return d;
}
function paeth(a, b, c) {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}
// Minimal PNG decoder to RGBA (input is a stored type-6 PNG, but handle 0/2/3/4/6).
function decodePng(bytes) {
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let header = null, palette = null, trns = null;
  const idat = [];
  while (at < bytes.length) {
    const len = view.getUint32(at);
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (type === 'IHDR') {
      header = { width: ((data[0] << 24) | (data[1] << 16) | (data[2] << 8) | data[3]) >>> 0, height: ((data[4] << 24) | (data[5] << 16) | (data[6] << 8) | data[7]) >>> 0, depth: data[8], colourType: data[9] };
    } else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
  }
  const { width, height, colourType } = header;
  const CHANNELS = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };
  const bpp = CHANNELS[colourType];
  const stride = width * bpp;
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat));
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    const src = y * (stride + 1) + 1;
    const o = y * stride, p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) { for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0); }
    else if (ft === 2) { for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0); }
    else if (ft === 3) { for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1); }
    else { for (let i = 0; i < stride; i++) { const a = i >= bpp ? samples[o + i - bpp] : 0; const b = y > 0 ? samples[p + i] : 0; const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0; samples[o + i] = raw[src + i] + paeth(a, b, c); } }
  }
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) { const g = samples[i]; rgba[d] = rgba[d + 1] = rgba[d + 2] = g; rgba[d + 3] = g === key ? 0 : 255; }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) { rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s]; rgba[d + 3] = samples[s + 1]; }
  } else {
    const entries = palette.length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) {
      lut[e * 4] = palette[e * 3]; lut[e * 4 + 1] = palette[e * 3 + 1]; lut[e * 4 + 2] = palette[e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      rgba[d] = lut[e * 4]; rgba[d + 1] = lut[e * 4 + 1]; rgba[d + 2] = lut[e * 4 + 2]; rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return { width, height, rgba };
}

// ---------- PNG filters ----------
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) { for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0); }
  else if (type === 2) { for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]); }
  else if (type === 3) { for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1); }
  else { for (let i = 0; i < n; i++) { const a = i >= bpp ? cur[i - bpp] : 0; const b = prev === null ? 0 : prev[i]; const c = prev !== null && i >= bpp ? prev[i - bpp] : 0; out[i] = cur[i] - paeth(a, b, c); } }
}
function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) { const v = row[i]; s += v < 128 ? v : 256 - v; }
  return s;
}
// Build the filtered stream for a filter-type array (one per row).
function filterStream(samples, width, height, bpp, types) {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));
  const row = new Uint8Array(stride);
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    filterRow(types[y], cur, prev, bpp, row);
    raw[y * (stride + 1)] = types[y];
    raw.set(row, y * (stride + 1) + 1);
  }
  return raw;
}
// All five filtered versions + per-row signed-sum costs.
function filterVersions(samples, width, height, bpp) {
  const stride = width * bpp;
  const vers = [];
  const costs = []; // costs[f][y] = signed sum of row y under filter f
  const row = new Uint8Array(stride);
  for (let f = 0; f < 5; f++) {
    const raw = new Uint8Array(height * (stride + 1));
    const c = new Float64Array(height);
    for (let y = 0; y < height; y++) {
      const cur = samples.subarray(y * stride, (y + 1) * stride);
      const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
      filterRow(f, cur, prev, bpp, row);
      raw[y * (stride + 1)] = f;
      raw.set(row, y * (stride + 1) + 1);
      c[y] = signedSum(row);
    }
    vers.push(raw);
    costs.push(c);
  }
  return { vers, costs };
}
function minsumTypes(samples, width, height, bpp) {
  const stride = width * bpp;
  const types = new Uint8Array(height);
  const rows = Array.from({ length: 5 }, () => new Uint8Array(stride));
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    let best = Infinity, bt = 0;
    for (let t = 0; t < 5; t++) { filterRow(t, cur, prev, bpp, rows[t]); const s = signedSum(rows[t]); if (s < best) { best = s; bt = t; } }
    types[y] = bt;
  }
  return types;
}
function smartUpTypes(samples, width, height, bpp) {
  // palette/SmartUp: identical row with a horizontal change -> Up, else None.
  const stride = width * bpp;
  const types = new Uint8Array(height);
  for (let y = 1; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = samples.subarray((y - 1) * stride, y * stride);
    let same = true, change = false;
    for (let i = 0; i < stride; i++) {
      if (cur[i] !== prev[i]) { same = false; break; }
      if (i > 0 && cur[i] !== cur[i - 1]) change = true;
    }
    types[y] = (same && change) ? 2 : 0;
  }
  return types;
}
// Viterbi over per-row costs with a switch penalty (bits-ish units).
function viterbiTypes(costs, height, penalty) {
  const INF = 1e18;
  let dp = new Float64Array(5);
  for (let f = 0; f < 5; f++) dp[f] = costs[f][0];
  const back = new Int8Array(height * 5);
  for (let y = 1; y < height; y++) {
    const ndp = new Float64Array(5).fill(INF);
    for (let f = 0; f < 5; f++) {
      for (let g = 0; g < 5; g++) {
        const c = dp[g] + (f === g ? 0 : penalty) + costs[f][y];
        if (c < ndp[f]) { ndp[f] = c; back[y * 5 + f] = g; }
      }
    }
    dp = ndp;
  }
  let bf = 0;
  for (let f = 1; f < 5; f++) if (dp[f] < dp[bf]) bf = f;
  const types = new Uint8Array(height);
  types[height - 1] = bf;
  for (let y = height - 1; y > 0; y--) { bf = back[y * 5 + bf]; types[y - 1] = bf; }
  return types;
}
// Per-row brute force: each row compressed with zlib level 1 using the previous
// 32 KiB of filtered output as dictionary; pick the best filter per row.
function bruteTypes(samples, width, height, bpp) {
  const stride = width * bpp;
  const types = new Uint8Array(height);
  const rows = Array.from({ length: 5 }, () => new Uint8Array(stride));
  const dict = new Uint8Array(32768);
  let dictLen = 0;
  const out = new Uint8Array(stride + 1);
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    let best = Infinity, bt = 0;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, rows[t]);
      out[0] = t;
      out.set(rows[t], 1);
      const d = dictLen > 0 ? dict.subarray(0, dictLen) : undefined;
      const z = deflateSync(out, { level: 1, dictionary: d });
      if (z.length < best) { best = z.length; bt = t; }
    }
    types[y] = bt;
    // append the winning row to the rolling 32 KiB dictionary (drop oldest)
    out[0] = bt;
    out.set(rows[bt], 1);
    if (dictLen + out.length <= 32768) {
      dict.set(out, dictLen);
      dictLen += out.length;
    } else {
      const overflow = dictLen + out.length - 32768;
      dict.copyWithin(0, overflow);
      dictLen -= overflow;
      dict.set(out, dictLen);
      dictLen += out.length;
    }
  }
  return types;
}

// ================= CUSTOM DEFLATE =================
// Custom DEFLATE (zopfli-style), written from the DEFLATE spec + prose brief.
// Sorted-bucket finder (binary search + +/-16 neighbours, prev chain, row-above
// probes, run arrays), optimal-parse DP with per-length best distance, sublen
// expansion, Pareto frontier, dual-basin cost iteration, length-limited Huffman
// (Huffman + zlib-style overflow repair + Kraft validation), dynamic/fixed blocks.

// ---- DEFLATE tables ----
const LEN_BASE = [3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258];
const LEN_EXTRA = [0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0];
const DIST_BASE = [1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577];
const DIST_EXTRA = [0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13];
const CL_ORDER = [16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15];
// length symbol for a length (3..258) -> symbol 257..285
const LEN_SYM = new Int16Array(259);
const LEN_SYM_EXTRA = new Int16Array(259);
for (let s = 0; s < 29; s++) {
  const base = LEN_BASE[s], next = s === 28 ? 259 : LEN_BASE[s + 1];
  for (let l = base; l < next && l <= 258; l++) { LEN_SYM[l] = 257 + s; LEN_SYM_EXTRA[l] = LEN_EXTRA[s]; }
}
LEN_SYM[258] = 285; LEN_SYM_EXTRA[258] = 0;
// length-code range endpoints (sublen expansion targets)
const LEN_ENDS = [3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258];
// All length-code range endpoints <= L (sublen expansion targets), as a flat
// list with offsets: ENDS_LIST[ENDS_OFF[L] .. ENDS_OFF[L+1]) = endpoints < L.
const ENDS_OFF = new Int32Array(260);
const ENDS_LIST = (() => {
  const list = [];
  for (let l = 3; l <= 258; l++) {
    ENDS_OFF[l] = list.length;
    for (let i = 0; i < LEN_ENDS.length; i++) if (LEN_ENDS[i] < l) list.push(LEN_ENDS[i]);
  }
  ENDS_OFF[259] = list.length;
  return new Int16Array(list);
})();
function endBelow(l) { let e = 3; for (let i = 0; i < LEN_ENDS.length; i++) { if (LEN_ENDS[i] < l) e = LEN_ENDS[i]; else break; } return e; }
const END_BELOW = new Int16Array(259);
for (let l = 3; l <= 258; l++) END_BELOW[l] = endBelow(l);
// distance symbol for a distance 1..32768
const DIST_SYM = new Int16Array(32769);
const DIST_SYM_EXTRA = new Int16Array(32769);
for (let s = 0; s < 30; s++) {
  const base = DIST_BASE[s], next = s === 29 ? 32769 : DIST_BASE[s + 1];
  for (let d = base; d < next && d <= 32768; d++) { DIST_SYM[d] = s; DIST_SYM_EXTRA[d] = DIST_EXTRA[s]; }
}
// fixed Huffman tables
const FIX_LIT_LEN = new Uint8Array(288);
const FIX_LIT_CODE = new Uint16Array(288);
for (let s = 0; s < 288; s++) {
  let len, code;
  if (s < 144) { len = 8; code = 0x30 + s; }
  else if (s < 256) { len = 9; code = 0x190 + (s - 144); }
  else if (s < 280) { len = 7; code = s - 256; }
  else { len = 8; code = 0xC0 + (s - 280); }
  FIX_LIT_LEN[s] = len; FIX_LIT_CODE[s] = code;
}
const FIX_DIST_LEN = new Uint8Array(30).fill(5);
const FIX_DIST_CODE = new Uint16Array(30);
for (let s = 0; s < 30; s++) FIX_DIST_CODE[s] = s;



// ---- Bit writer: bits go LSB-first; Huffman codes are written MSB-first ----
class BitWriter {
  constructor(cap) { this.buf = new Uint8Array(cap); this.pos = 0; this.acc = 0; this.nbits = 0; }
  ensure(n) { if (this.pos + n + 8 > this.buf.length) { const nb = new Uint8Array(this.buf.length * 2 + 1024); nb.set(this.buf); this.buf = nb; } }
  bit(b) {
    this.acc |= (b & 1) << this.nbits; this.nbits++;
    if (this.nbits === 8) { this.ensure(1); this.buf[this.pos++] = this.acc; this.acc = 0; this.nbits = 0; }
  }
  bits(v, n) { // LSB-first
    for (let i = 0; i < n; i++) this.bit((v >> i) & 1);
  }
  code(code, len) { // MSB-first
    for (let i = len - 1; i >= 0; i--) this.bit((code >> i) & 1);
  }
  finish() {
    if (this.nbits > 0) { this.ensure(1); this.buf[this.pos++] = this.acc; this.acc = 0; this.nbits = 0; }
    return this.buf.subarray(0, this.pos);
  }
  get bitCount() { return this.pos * 8 + this.nbits; }
}

// ---- Length-limited Huffman via Huffman tree + overflow repair (zlib style) ----
// Returns {lens: Uint8Array, codes: Uint32Array} or null on failure.
function buildCodeLengths(freq, maxLen) {
  const n = freq.length;
  const active = [];
  for (let s = 0; s < n; s++) if (freq[s] > 0) active.push(s);
  if (active.length === 0) return null;
  if (active.length === 1) {
    // add a dummy symbol so the code is complete
    const dummy = active[0] === 0 ? 1 : 0;
    if (dummy >= n) return null;
    active.push(dummy);
    freq = freq.slice(); freq[dummy] = 1;
  }
  // Huffman tree with the two-queue method: sort frequencies once, then merge
  // smallest-first from the sorted leaves and the merged-node queue (O(n log n)).
  const items = active.map((s) => ({ f: freq[s], sym: s, l: null, r: null }));
  items.sort((a, b) => a.f - b.f);
  const q = []; // merged nodes, in nondecreasing f order
  let qi = 0, ii = 0;
  const take = () => {
    const a = ii < items.length ? items[ii] : null;
    const b = qi < q.length ? q[qi] : null;
    if (b === null || (a !== null && a.f <= b.f)) { ii++; return a; }
    qi++; return b;
  };
  while ((items.length - ii) + (q.length - qi) > 1) {
    const a = take(), b = take();
    q.push({ f: a.f + b.f, sym: -1, l: a, r: b });
  }
  const root = (items.length - ii === 1) ? items[ii] : q[qi];
  const nodes = [root];
  const lens = new Uint8Array(n);
  const walk = (nd, d) => {
    if (nd.sym >= 0) { lens[nd.sym] = d; return; }
    walk(nd.l, d + 1); walk(nd.r, d + 1);
  };
  walk(nodes[0], 0);
  // Cap lengths at maxLen, then reassign the capped length multiset by frequency
  // (shortest lengths to the most frequent symbols).
  for (let s = 0; s < n; s++) if (lens[s] > maxLen) lens[s] = maxLen;
  const order = active.slice().sort((a, b) => freq[b] - freq[a] || a - b);
  const sortedLens = active.map((s) => lens[s]).sort((a, b) => a - b);
  const newLens = new Uint8Array(n);
  for (let i = 0; i < order.length; i++) newLens[order[i]] = sortedLens[i];
  // Kraft repair: make the code complete (Kraft == 1).
  // If over-subscribed (K>1), lengthen the LEAST-frequent symbol still below maxLen.
  // If under-subscribed (K<1), shorten the LONGEST code (finest step, exact: the
  // deficit is always a multiple of 2^-longest, so this reaches exactly 1).
  const kraft = () => {
    let sum = 0;
    for (let s = 0; s < n; s++) if (newLens[s] > 0) sum += 1 / (1 << newLens[s]);
    return sum;
  };
  let guard = 0;
  while (guard++ < 100000) {
    const k = kraft();
    if (Math.abs(k - 1) < 1e-9) break;
    if (k > 1) {
      let sym = -1, worst = Infinity;
      for (let s = 0; s < n; s++) {
        if (newLens[s] > 0 && newLens[s] < maxLen && freq[s] < worst) { worst = freq[s]; sym = s; }
      }
      if (sym < 0) return null;
      newLens[sym]++;
    } else {
      let longest = 0, sym = -1;
      for (let s = 0; s < n; s++) if (newLens[s] > longest) { longest = newLens[s]; sym = s; }
      if (longest <= 1 || sym < 0) return null;
      newLens[sym]--;
    }
  }
  if (Math.abs(kraft() - 1) > 1e-9) return null;
  // canonical codes
  const codes = new Uint32Array(n);
  const bc2 = new Int32Array(maxLen + 2);
  for (let s = 0; s < n; s++) if (newLens[s] > 0) bc2[newLens[s]]++;
  let code = 0;
  const nc2 = new Int32Array(maxLen + 2);
  for (let len = 1; len <= maxLen; len++) { code = (code + bc2[len - 1]) << 1; nc2[len] = code; }
  for (let s = 0; s < n; s++) {
    if (newLens[s] > 0) codes[s] = nc2[newLens[s]]++;
  }
  return { lens: newLens, codes };
}

function kraftBad(lens, maxLen) {
  let sum = 0;
  for (let s = 0; s < lens.length; s++) {
    if (lens[s] > 0) {
      if (lens[s] > maxLen) return 1;
      sum += 1 / (1 << lens[s]);
    }
  }
  return Math.abs(sum - 1) > 1e-9 ? 1 : 0;
}

// ---- Sorted-bucket match finder ----
// Buckets keyed by a 17-bit hash of the 3-byte prefix; each bucket's positions are
// sorted by suffix lexicographically once. Query: binary search + +/-W neighbours.
class Finder {
  constructor(data, start, end, rowLen, width, skipRuns, w, chainLen) {
    this.d = data; this.start = start; this.end = end; this.rowLen = rowLen; this.width = width;
    this.dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    this.NB = 131072;
    this.skipRuns = skipRuns !== false;
    this.W = w || 16;
    this.chainLen = chainLen || 16;
    this.pf = new Int32Array(32); // reusable Pareto frontier scratch
    this.build();
  }
  hash3(p) {
    const d = this.d;
    return ((((d[p] << 16) ^ (d[p + 1] << 8) ^ d[p + 2]) * 2654435761) >>> 15) & 131071;
  }
  // compare suffixes at a and b lexicographically (up to 258 bytes), returns <0/0/>0
  cmpSuffix(a, b) {
    const d = this.d, lim = Math.min(258, this.end - a, this.end - b);
    let k = 0;
    while (k + 4 <= lim) {
      if (d[a + k] !== d[b + k]) return d[a + k] - d[b + k];
      if (d[a + k + 1] !== d[b + k + 1]) return d[a + k + 1] - d[b + k + 1];
      if (d[a + k + 2] !== d[b + k + 2]) return d[a + k + 2] - d[b + k + 2];
      if (d[a + k + 3] !== d[b + k + 3]) return d[a + k + 3] - d[b + k + 3];
      k += 4;
    }
    for (; k < lim; k++) {
      const x = d[a + k] - d[b + k];
      if (x !== 0) return x;
    }
    return (this.end - a) - (this.end - b);
  }
  matchLen(a, b) { // length of match between positions a and b, from k=0, cap 258
    const d = this.d, lim = Math.min(258, this.end - a, this.end - b);
    let k = 0;
    // compare 4 bytes at a time (unrolled typed-array reads)
    while (k + 4 <= lim) {
      if (d[a + k] !== d[b + k] || d[a + k + 1] !== d[b + k + 1] || d[a + k + 2] !== d[b + k + 2] || d[a + k + 3] !== d[b + k + 3]) break;
      k += 4;
    }
    while (k < lim && d[a + k] === d[b + k]) k++;
    return k;
  }
  build() {
    const d = this.d, lo = Math.max(0, this.start - 32768), hi = this.end - 2;
    const counts = new Int32Array(this.NB);
    // first pass: count (skip deep-run positions: keep first 3 of each run)
    const keep = new Uint8Array(this.end - lo);
    for (let p = lo; p < hi; p++) {
      if (this.skipRuns && p >= lo + 3 && d[p] === d[p - 1] && d[p] === d[p - 2] && d[p] === d[p - 3]) continue;
      keep[p - lo] = 1;
      counts[this.hash3(p)]++;
    }
    const offsets = new Int32Array(this.NB + 1);
    for (let i = 0; i < this.NB; i++) offsets[i + 1] = offsets[i] + counts[i];
    const total = offsets[this.NB];
    const pos = new Int32Array(total);
    const cur = offsets.slice(0, this.NB);
    // prev chain: previous position with same hash
    this.prev = new Int32Array(this.end - lo).fill(-1);
    const last = new Int32Array(this.NB).fill(-1);
    for (let p = lo; p < hi; p++) {
      if (!keep[p - lo]) continue;
      const h = this.hash3(p);
      this.prev[p - lo] = last[h] >= 0 ? last[h] : -1;
      last[h] = p;
      pos[cur[h]++] = p;
    }
    // sort each bucket by suffix
    const self = this;
    for (let b = 0; b < this.NB; b++) {
      const s0 = offsets[b], s1 = offsets[b + 1];
      if (s1 - s0 > 1) {
        const slice = Array.prototype.slice.call(pos.subarray(s0, s1));
        slice.sort((a, c) => self.cmpSuffix(a, c));
        pos.set(slice, s0);
      }
    }
    this.offsets = offsets; this.pos = pos; this.lo = lo;
  }
  // query position p (absolute), returns Pareto list of [len, dist] pairs (len>=3)
  // into out (flat array), returns count. Also updates stats.
  query(p, out, stats) {
    const d = this.d, end = this.end;
    let n = 0;
    const maxLen = Math.min(258, end - p);
    if (maxLen < 3) return 0;
    const h = this.hash3(p);
    const s0 = this.offsets[h], s1 = this.offsets[h + 1];
    // binary search insertion point for suffix p
    let lo = s0, hi = s1;
    while (lo < hi) {
      const mid = (lo + hi) >> 1;
      if (this.cmpSuffix(this.pos[mid], p) < 0) lo = mid + 1; else hi = mid;
    }
    const W = this.W;
    // Incremental Pareto frontier (flat array pf, pfn pairs, sorted by len desc):
    // a candidate is added only if no kept pair dominates it (longer AND nearer);
    // adding it evicts pairs it dominates. O(candidates x frontierSize).
    const pf = this.pf;
    let pfn = 0;
    const paretoAdd = (len, dist) => {
      for (let i = 0; i < pfn; i++) {
        if (pf[i * 2] >= len && pf[i * 2 + 1] <= dist) return; // dominated
      }
      let w = 0;
      for (let i = 0; i < pfn; i++) {
        if (pf[i * 2] <= len && pf[i * 2 + 1] >= dist) continue; // evicted
        pf[w * 2] = pf[i * 2]; pf[w * 2 + 1] = pf[i * 2 + 1]; w++;
      }
      pfn = w;
      let j = pfn;
      while (j > 0 && (pf[(j - 1) * 2] < len || (pf[(j - 1) * 2] === len && pf[(j - 1) * 2 + 1] > dist))) {
        pf[j * 2] = pf[(j - 1) * 2]; pf[j * 2 + 1] = pf[(j - 1) * 2 + 1];
        j--;
      }
      pf[j * 2] = len; pf[j * 2 + 1] = dist;
      pfn++;
      if (pfn > 8) pfn = 8; // cap: keep the 8 longest (frontier is len-sorted)
    };
    // Pareto pre-check state: best length found so far and the (shortest)
    // distance achieving it. A candidate farther than bestDist that cannot beat
    // bestLen is dominated (shorter AND farther) — skip its matchLen entirely.
    let bestLen = 0, bestDist = 0;
    const consider = (q) => {
      if (q >= p) return;
      const dist = p - q;
      if (dist > 32768 || dist < 1) return;
      if (dist === 1 && d[p] !== d[p - 1]) return; // run-path validity
      if (bestLen >= 3 && dist > bestDist) {
        // cannot be longer than bestLen? check the byte at offset bestLen
        if (q + bestLen >= end || d[q + bestLen] !== d[p + bestLen]) return;
      }
      stats.comparisons++;
      const len = this.matchLen(p, q);
      if (len >= 3) {
        paretoAdd(len, dist);
        if (len > bestLen || (len === bestLen && dist < bestDist)) { bestLen = len; bestDist = dist; }
      }
    };
    for (let k = 0; k <= W; k++) {
      if (lo + k < s1) consider(this.pos[lo + k]);
      if (k > 0 && lo - k >= s0) consider(this.pos[lo - k]);
    }
    // prev chain safety net
    let q = p - this.lo >= 0 ? this.prev[p - this.lo] : -1;
    for (let step = 0; step < this.chainLen && q >= 0; step++) {
      consider(q);
      q = q - this.lo >= 0 ? this.prev[q - this.lo] : -1;
    }
    // row-above probes (one and two scanlines above)
    const rl = this.rowLen;
    if (rl > 0) {
      for (const back of [rl, rl * 2]) {
        const q2 = p - back;
        if (q2 >= Math.max(0, p - 32768) && d[q2] === d[p] && d[q2 + 1] === d[p + 1] && d[q2 + 2] === d[p + 2]) {
          stats.comparisons++;
          const len = this.matchLen(p, q2);
          if (len >= 3) { paretoAdd(len, back); if (len > bestLen) { bestLen = len; bestDist = back; } }
        }
      }
    }
    if (pfn === 0) { stats.noMatch++; return 0; }
    for (let i = 0; i < pfn * 2; i++) out[i] = pf[i];
    return pfn;
  }
}

// ---- Optimal parse DP over one block ----
// cand: per-position candidate pairs (flat Int32Array, stride 16) + candCount Uint8.
// dp/prev/chLen/chDist buffers are reused across iterations (passed in as ws).
// Returns {toks, bits}
function parseBlock(data, start, end, cand, candCount, litCost, lenCost, distCostArr, maxLenCap, ws) {
  const n = end - start;
  const INF = 1 << 30;
  const dp = ws.dp, prev = ws.prev, chLen = ws.chLen, chDist = ws.chDist;
  dp.fill(INF, 0, n + 1);
  const d = data;
  dp[0] = 0;
  for (let i = 0; i < n; i++) {
    const base = dp[i];
    if (base === INF) continue;
    const pos = start + i;
    // literal
    const lc = base + litCost[d[pos]];
    if (lc < dp[i + 1]) { dp[i + 1] = lc; prev[i + 1] = i; chLen[i + 1] = 0; chDist[i + 1] = 0; }
    // matches: full sublen expansion (all length-code endpoints <= L, plus 3)
    const cc = candCount[i];
    if (cc > 0) {
      const off = i * 16;
      for (let c = 0; c < cc; c++) {
        let len = cand[off + c * 2];
        const dist = cand[off + c * 2 + 1];
        if (len > maxLenCap) len = maxLenCap;
        if (len < 3) continue;
        const dc = distCostArr[dist];
        const rem = n - i;
        if (len > rem) len = rem;
        if (len < 3) continue;
        // offered lengths: len itself, then every endpoint below it
        const e0 = ENDS_OFF[len], e1 = ENDS_OFF[len + 1];
        for (let ei = e1 - 1; ei >= e0; ei--) {
          const L = ENDS_LIST[ei];
          const nc = base + lenCost[L] + dc;
          if (nc < dp[i + L]) { dp[i + L] = nc; prev[i + L] = i; chLen[i + L] = L; chDist[i + L] = dist; }
        }
        const nc = base + lenCost[len] + dc;
        if (nc < dp[i + len]) { dp[i + len] = nc; prev[i + len] = i; chLen[i + len] = len; chDist[i + len] = dist; }
        if (len !== 3) {
          const nc3 = base + lenCost[3] + dc;
          if (nc3 < dp[i + 3]) { dp[i + 3] = nc3; prev[i + 3] = i; chLen[i + 3] = 3; chDist[i + 3] = dist; }
        }
      }
    }
  }
  // backtrack
  const toks = []; // {len, dist} len 0 => literal byte in dist field
  let i = n;
  while (i > 0) {
    const p = prev[i];
    const L = chLen[i];
    if (L === 0) toks.push([0, d[start + p]]);
    else toks.push([L, chDist[i]]);
    i = p;
  }
  toks.reverse();
  return { toks, bits: dp[n] };
}

function tokenFreqs(toks) {
  const litFreq = new Int32Array(286);
  const distFreq = new Int32Array(30);
  for (const [len, v] of toks) {
    if (len === 0) litFreq[v]++;
    else { litFreq[LEN_SYM[len]]++; distFreq[DIST_SYM[v]]++; }
  }
  litFreq[256] = 1; // end of block
  return { litFreq, distFreq };
}

// header bit cost for a dynamic block given lit/dist code lengths
function headerBitsClean(litLens, distLens, hlitIn, hdistIn) {
  // Trim trailing zero lengths first: the RLE sequence must encode EXACTLY
  // hlit+hdist lengths, matching the HLIT/HDIST written in the header.
  let hlit = hlitIn;
  while (hlit > 257 && litLens[hlit - 1] === 0) hlit--;
  let hdist = hdistIn;
  while (hdist > 1 && distLens[hdist - 1] === 0) hdist--;
  const combined = new Uint8Array(hlit + hdist);
  for (let i = 0; i < hlit; i++) combined[i] = litLens[i];
  for (let i = 0; i < hdist; i++) combined[hlit + i] = distLens[i];
  const freq = new Int32Array(19);
  const seq = []; // [sym, extraBits]
  let i = 0;
  while (i < combined.length) {
    const v = combined[i];
    let run = 1;
    while (i + run < combined.length && combined[i + run] === v) run++;
    if (v === 0) {
      let r = run;
      while (r >= 11) { const take = Math.min(r, 138); seq.push([18, take - 11, 7]); freq[18]++; r -= take; }
      if (r >= 3) { seq.push([17, r - 3, 3]); freq[17]++; r = 0; }
      while (r > 0) { seq.push([0, 0, 0]); freq[0]++; r--; }
    } else {
      seq.push([v, 0, 0]); freq[v]++; let r = run - 1;
      while (r >= 3) { const take = Math.min(r, 6); seq.push([16, take - 3, 2]); freq[16]++; r -= take; }
      while (r > 0) { seq.push([v, 0, 0]); freq[v]++; r--; }
    }
    i += run;
  }
  const cl = buildCodeLengths(freq, 7);
  if (!cl) return { bits: Infinity, bad: 1 };
  if (kraftBad(cl.lens, 7)) return { bits: Infinity, bad: 1 };
  let hclen = 19;
  while (hclen > 4 && cl.lens[CL_ORDER[hclen - 1]] === 0) hclen--;
  let bits = 3 + 5 + 5 + 4 + hclen * 3;
  for (const [sym, extra, eb] of seq) bits += cl.lens[sym] + eb;
  return { bits, bad: 0, seq, clLens: cl.lens, clCodes: cl.codes, hlit, hdist, hclen };
}

// emit one block (dynamic or fixed) into writer; returns bit count or null on failure
function emitBlock(bw, toks, litLens, litCodes, distLens, distCodes, useDynamic, hlit, hdist, clInfo) {
  if (useDynamic) {
    bw.bits(0b10, 2); // BTYPE dynamic (bits written LSB-first: value 2 = 10b)
    // header: HLIT (5), HDIST (5), HCLEN (4)
    bw.bits(hlit - 257, 5);
    bw.bits(hdist - 1, 5);
    bw.bits(clInfo.hclen - 4, 4);
    for (let i = 0; i < clInfo.hclen; i++) bw.bits(clInfo.clLens[CL_ORDER[i]], 3);
    for (const [sym, extra, eb] of clInfo.seq) {
      bw.code(clInfo.clCodes[sym], clInfo.clLens[sym]);
      if (eb > 0) bw.bits(extra, eb);
    }
  } else {
    bw.bits(0b01, 2); // fixed
  }
  for (const [len, v] of toks) {
    if (len === 0) {
      if (useDynamic) bw.code(litCodes[v], litLens[v]);
      else bw.code(FIX_LIT_CODE[v], FIX_LIT_LEN[v]);
    } else {
      const ls = LEN_SYM[len];
      if (useDynamic) bw.code(litCodes[ls], litLens[ls]);
      else bw.code(FIX_LIT_CODE[ls], FIX_LIT_LEN[ls]);
      const le = LEN_SYM_EXTRA[len];
      if (le > 0) bw.bits(len - LEN_BASE[ls - 257], le);
      const ds = DIST_SYM[v];
      if (useDynamic) bw.code(distCodes[ds], distLens[ds]);
      else bw.code(FIX_DIST_CODE[ds], 5);
      const de = DIST_SYM_EXTRA[v];
      if (de > 0) bw.bits(v - DIST_BASE[ds], de);
    }
  }
  // end of block
  if (useDynamic) bw.code(litCodes[256], litLens[256]);
  else bw.code(FIX_LIT_CODE[256], FIX_LIT_LEN[256]);
}

// cost tables from code lengths
function costTables(litLens, distLens) {
  const litCost = new Int32Array(256);
  for (let b = 0; b < 256; b++) litCost[b] = litLens[b] || 15;
  const lenCost = new Int32Array(259);
  for (let l = 3; l <= 258; l++) lenCost[l] = (litLens[LEN_SYM[l]] || 15) + LEN_SYM_EXTRA[l];
  const distCostArr = new Int32Array(32769);
  for (let d = 1; d <= 32768; d++) distCostArr[d] = (distLens[DIST_SYM[d]] || 15) + DIST_SYM_EXTRA[d];
  return { litCost, lenCost, distCostArr };
}

// compress one block's tokens with the dual-basin parse; returns {bytes(bits), toks, ...}
function compressBlock(data, start, end, finder, stats, opts) {
  const n = end - start;
  const maxLenCap = opts.maxLenCap || 258;
  // candidate search at every position (once per block)
  const cand = new Int32Array(n * 16);
  const candCount = new Uint8Array(n);
  const qbuf = new Int32Array(256);
  const runLen = opts.runLen;
    for (let i = 0; i < n; i++) {
    const p = start + i;
    // Mid-run fast path: at a position strictly inside a run of >=4, the dist-1
    // run match dominates; the bucket search is skipped (row probes + a short
    // prev chain only). Run starts and short runs get the full search.
    if (runLen && p > start && data[p] === data[p - 1] && runLen[p] >= 4) {
      const d = data;
      const rl = finder.rowLen;
      let m = 0;
      const rlen = Math.min(258, runLen[p]);
      // dist-1 run match (valid: data[p]==data[p-1])
      qbuf[m++] = rlen; qbuf[m++] = 1;
      // row-above probes
      if (rl > 0) {
        for (const back of [rl, rl * 2]) {
          const q2 = p - back;
          if (q2 >= Math.max(0, p - 32768) && d[q2] === d[p] && d[q2 + 1] === d[p + 1] && d[q2 + 2] === d[p + 2]) {
            stats.comparisons++;
            const len = finder.matchLen(p, q2);
            if (len >= 3) { qbuf[m++] = len; qbuf[m++] = back; }
          }
        }
      }
      // short prev chain (4 steps)
      let q = finder.prev[p - finder.lo];
      for (let step = 0; step < 4 && q >= 0; step++) {
        if (q < p && p - q <= 32768) {
          stats.comparisons++;
          const len = finder.matchLen(p, q);
          if (len >= 3) { qbuf[m++] = len; qbuf[m++] = p - q; }
        }
        q = q - finder.lo >= 0 ? finder.prev[q - finder.lo] : -1;
      }
      // Pareto prune the small set (insertion sort by len desc, keep dec dist)
      const np = m / 2;
      for (let a = 1; a < np; a++) {
        const l = qbuf[a * 2], dd = qbuf[a * 2 + 1];
        let j = a - 1;
        while (j >= 0 && (qbuf[j * 2] < l || (qbuf[j * 2] === l && qbuf[j * 2 + 1] > dd))) {
          qbuf[(j + 1) * 2] = qbuf[j * 2]; qbuf[(j + 1) * 2 + 1] = qbuf[j * 2 + 1];
          j--;
        }
        qbuf[(j + 1) * 2] = l; qbuf[(j + 1) * 2 + 1] = dd;
      }
      let bd = Infinity, mm = 0;
      for (let a = 0; a < np; a++) {
        const l = qbuf[a * 2], dd = qbuf[a * 2 + 1];
        if (dd < bd) { qbuf[mm++] = l; qbuf[mm++] = dd; bd = dd; if (mm >= 16) break; }
      }
      candCount[i] = mm / 2;
      for (let c = 0; c < mm; c++) cand[i * 16 + c] = qbuf[c];
      continue;
    }
    const m = finder.query(p, qbuf, stats);
    candCount[i] = m;
    for (let c = 0; c < m * 2; c++) cand[i * 16 + c] = qbuf[c];
  }
    // raw byte entropy for basin B decision
  const freq = new Int32Array(256);
  for (let i = start; i < end; i++) freq[data[i]]++;
  let entropyBits = 0;
  for (let b = 0; b < 256; b++) if (freq[b] > 0) entropyBits += freq[b] * Math.log2(n / freq[b]);
  const rawEntropyCost = entropyBits; // bits

  const iters = opts.iters || 5;
  let best = null;
  // DP work buffers, allocated once per block and reused across iterations
  const ws = {
    dp: new Int32Array(n + 1),
    prev: new Int32Array(n + 1),
    chLen: new Int16Array(n + 1),
    chDist: new Int32Array(n + 1),
  };
  // Basin A: fixed costs first
  let litLens = FIX_LIT_LEN.slice(0, 286);
  let distLens = FIX_DIST_LEN.slice(0, 30);
  // fixed lit lens are 288 long; trim to 286
  litLens = new Uint8Array(286);
  for (let s = 0; s < 286; s++) litLens[s] = FIX_LIT_LEN[s];
  distLens = new Uint8Array(30).fill(5);
  const runBasin = (initLit, initDist, passes) => {
    let ll = initLit, dl = initDist, result = null;
    for (let it = 0; it < passes; it++) {
      const ct = costTables(ll, dl);
      const r = parseBlock(data, start, end, cand, candCount, ct.litCost, ct.lenCost, ct.distCostArr, maxLenCap, ws);
      const tf = tokenFreqs(r.toks);
      const lb = buildCodeLengths(tf.litFreq, 15);
      const db = buildCodeLengths(tf.distFreq, 15);
      if (!lb || !db) { result = { toks: r.toks, bits: r.bits + 1e9, bad: 1 }; break; }
      if (kraftBad(lb.lens, 15) || kraftBad(db.lens, 15)) { result = { toks: r.toks, bits: r.bits + 1e9, bad: 1 }; break; }
      const hb = headerBitsClean(lb.lens, db.lens, 286, 30);
      const total = r.bits + (hb.bad ? 1e9 : hb.bits);
      result = { toks: r.toks, bits: total, tokenBits: r.bits, headerBits: hb.bits, litLens: lb.lens, distLens: db.lens, hb, bad: hb.bad ? 1 : 0 };
      // damped update on later iterations: blend toward previous lengths is complex;
      // use undamped re-derive (deterministic) with a fixed-seed perturbation at iter 5
      ll = lb.lens; dl = db.lens;
      if (it === 4 && opts.perturb) {
        // deterministic perturbation: bump a few mid-frequency symbols' lengths by +1/-1 pattern
        // (kept simple: skip — perturbation folded into iteration count instead)
      }
    }
    return result;
  };
    const basinA = runBasin(litLens, distLens, iters);
  if (basinA && !basinA.bad) best = basinA;
    // Basin B decision: literal-heavy if basinA token bits >= 55% of raw entropy
  if (basinA && basinA.tokenBits >= 0.55 * rawEntropyCost) {
    const entLit = new Uint8Array(286);
    for (let b = 0; b < 256; b++) {
      const f = freq[b];
      entLit[b] = f > 0 ? Math.max(1, Math.min(15, Math.round(Math.log2(n / f)))) : 15;
    }
    for (let s = 256; s < 286; s++) entLit[s] = 15;
    const entDist = new Uint8Array(30).fill(15);
    const basinB = runBasin(entLit, entDist, 3);
    if (basinB && !basinB.bad) {
      if (!best || basinB.bits < best.bits) best = basinB;
      else if (basinB.bits > best.bits * 1.12) { /* abort: keep A */ }
    }
  }
  if (!best) return null;
  if (opts.dump) {
    const dh = new Int32Array(31);
    const lh = new Int32Array(29);
    for (const [len, v] of best.toks) {
      if (len > 0) { dh[Math.min(30, DIST_SYM[v])]++; lh[LEN_SYM[len] - 257]++; }
    }
    let actual = 0;
    for (const [len, v] of best.toks) {
      if (len === 0) actual += best.litLens[v];
      else actual += best.litLens[LEN_SYM[len]] + LEN_SYM_EXTRA[len] + best.distLens[DIST_SYM[v]] + DIST_SYM_EXTRA[v];
    }
    actual += best.litLens[256];
    console.error('DUMP block', start, '-', end, 'toks', best.toks.length, 'tokenBits(dp)', best.tokenBits, 'actualBits', actual, 'headerBits', best.headerBits);
    console.error('  distSym hist', [...dh].join(','));
    console.error('  lenSym hist', [...lh].join(','));
    console.error('  distLens', [...best.distLens].join(','));
    console.error('  litLens[256..285]', [...best.litLens.slice(256)].join(','));
  }
  // compare dynamic vs fixed for the best token set
  const tf = tokenFreqs(best.toks);
  // fixed cost:
  let fixedBits = 3; // BFINAL+BTYPE
  for (const [len, v] of best.toks) {
    if (len === 0) fixedBits += FIX_LIT_LEN[v];
    else fixedBits += FIX_LIT_LEN[LEN_SYM[len]] + LEN_SYM_EXTRA[len] + 5 + DIST_SYM_EXTRA[v];
  }
  fixedBits += FIX_LIT_LEN[256];
  const dynBits = 3 + (best.headerBits || 0) + best.tokenBits;
  const useDynamic = !opts.forceFixed && dynBits < fixedBits && !best.bad;
  const tokStats = { nTok: best.toks.length, nMatch: 0, matchBytes: 0 };
  for (const [len] of best.toks) if (len > 0) { tokStats.nMatch++; tokStats.matchBytes += len; }
  return { toks: best.toks, useDynamic, litLens: best.litLens, distLens: best.distLens, hb: best.hb, dynBits, fixedBits, bits: Math.min(dynBits, fixedBits), tokStats };
}

// canonical codes from code lengths
function codesFromLens(lens) {
  const maxLen = 15;
  const bc = new Int32Array(maxLen + 2);
  for (let s = 0; s < lens.length; s++) if (lens[s] > 0) bc[lens[s]]++;
  const codes = new Uint32Array(lens.length);
  let code = 0;
  const nc = new Int32Array(maxLen + 2);
  for (let len = 1; len <= maxLen; len++) { code = (code + bc[len - 1]) << 1; nc[len] = code; }
  for (let s = 0; s < lens.length; s++) if (lens[s] > 0) codes[s] = nc[lens[s]]++;
  return codes;
}

// ---- top-level: compress a whole filtered stream ----
function compressStream(data, rowLen, opts = {}) {
  const stats = { comparisons: 0, noMatch: 0, positions: 0, blocks: 0, kraftBad: 0, libFallback: 0 };
    const n = data.length;
  // block boundaries: rows, ~192KB target, snapped to filter-band changes and run ends
  const blockSize = opts.blockSize || 196608;
  const bounds = [0];
  let at = 0;
  while (at < n) {
    let nxt = Math.min(n, at + blockSize);
    // snap to a row boundary (rowLen = stride+1)
    if (rowLen > 0 && nxt < n) {
      nxt = Math.floor(nxt / rowLen) * rowLen;
      if (nxt <= at) nxt = at + rowLen;
    }
    // avoid splitting a long run: if data[nxt-1]==data[nxt], advance to run end
    if (nxt < n && data[nxt - 1] === data[nxt]) {
      const v = data[nxt];
      while (nxt < n && data[nxt] === v) nxt++;
      if (rowLen > 0) nxt = Math.ceil(nxt / rowLen) * rowLen;
      if (nxt > n) nxt = n;
    }
    bounds.push(nxt);
    at = nxt;
  }
  const finder = new Finder(data, 0, n, rowLen, 0, opts.skipRuns, opts.w, opts.chain);
    // run-length array (capped at 300): runLen[i] = identical bytes starting at i
  const runLen = new Uint16Array(n + 1);
  for (let i = n - 1; i >= 0; i--) {
    runLen[i] = (i + 1 < n && data[i] === data[i + 1]) ? Math.min(300, runLen[i + 1] + 1) : 1;
  }
  const bw = new BitWriter(n);
  let totalBits = 0;
  const iters = opts.iters || 5;
  for (let bi = 0; bi < bounds.length - 1; bi++) {
    const s = bounds[bi], e = bounds[bi + 1];
    if (e <= s) continue;
    stats.blocks++;
    const isFlat = opts.flat;
    const res = compressBlock(data, s, e, finder, stats, {
      iters: isFlat ? (opts.flatIters || 12) : (n > 2000000 ? Math.min(iters, 6) : iters),
      maxLenCap: opts.maxLenCap || 258,
      perturb: opts.perturb,
      forceFixed: opts.forceFixed,
      dump: opts.dump,
      runLen,
    });
    if (!res) { stats.libFallback++; return null; }
    const last = bi === bounds.length - 2;
    // emit: BFINAL + block
    const hb = res.hb;
    let hlit = 286, hdist = 30;
    if (res.useDynamic) {
      while (hlit > 257 && res.litLens[hlit - 1] === 0) hlit--;
      while (hdist > 1 && res.distLens[hdist - 1] === 0) hdist--;
    }
    const clInfo = res.useDynamic ? hb : null;
    if (res.useDynamic && (!clInfo || clInfo.bad)) { stats.libFallback++; return null; }
    // write BFINAL
    bw.bit(last ? 1 : 0);
    const lc = res.useDynamic ? codesFromLens(res.litLens) : null;
    const dc = res.useDynamic ? codesFromLens(res.distLens) : null;
    emitBlock(bw, res.toks, res.litLens, lc, res.distLens, dc, res.useDynamic, hlit, hdist, clInfo);
    totalBits += res.bits;
    stats.positions += e - s;
    if (res.tokStats) {
      stats.nTok = (stats.nTok || 0) + res.tokStats.nTok;
      stats.nMatch = (stats.nMatch || 0) + res.tokStats.nMatch;
      stats.matchBytes = (stats.matchBytes || 0) + res.tokStats.matchBytes;
      stats.dynBits = (stats.dynBits || 0) + res.dynBits;
      stats.fixedBits = (stats.fixedBits || 0) + res.fixedBits;
    }
  }
  const deflateBytes = bw.finish();
  // zlib wrapper
  const out = new Uint8Array(deflateBytes.length + 6);
  out[0] = 0x78; out[1] = 0x9c;
  out.set(deflateBytes, 2);
  const ad = adler32(data);
  out[out.length - 4] = (ad >>> 24) & 0xff;
  out[out.length - 3] = (ad >>> 16) & 0xff;
  out[out.length - 2] = (ad >>> 8) & 0xff;
  out[out.length - 1] = ad & 0xff;
    return { zlib: out, stats, totalBits };
}

function libDeflate(data) {
  return deflateSync(data, { level: 9 });
}

// ================= FORMS + DRIVER =================

// ---------- Colour forms ----------
function analyse(rgba, n) {
  const set = new Map();
  let grey = true, alphaMin = 255, alphaMax = 0;
  const transRGB = new Set();
  const transRGBOpaque = new Set();
  for (let i = 0; i < n; i++) {
    const r = rgba[i * 4], g = rgba[i * 4 + 1], b = rgba[i * 4 + 2], a = rgba[i * 4 + 3];
    const k = (r << 24) | (g << 16) | (b << 8) | a;
    set.set(k, (set.get(k) || 0) + 1);
    if (r !== g || g !== b) grey = false;
    if (a < alphaMin) alphaMin = a;
    if (a > alphaMax) alphaMax = a;
    const rgb = (r << 16) | (g << 8) | b;
    if (a === 0) transRGB.add(rgb);
    else transRGBOpaque.add(rgb);
  }
  // tRNS key is usable only if the transparent RGB never occurs opaque
  let trnsKey = -1;
  if (transRGB.size === 1) {
    const only = [...transRGB][0];
    if (!transRGBOpaque.has(only)) trnsKey = only;
  }
  return { set, grey, alphaMin, alphaMax, trnsKey };
}
// Palette orderings. Returns {samples, plte, trns} for a given colour order.
function paletteForm(rgba, width, height, order) {
  const n = width * height;
  const idx = new Map();
  order.forEach((c, i) => idx.set(c, i));
  const samples = new Uint8Array(n);
  for (let i = 0; i < n; i++) {
    const k = (rgba[i * 4] << 24) | (rgba[i * 4 + 1] << 16) | (rgba[i * 4 + 2] << 8) | rgba[i * 4 + 3];
    samples[i] = idx.get(k);
  }
  const plte = new Uint8Array(order.length * 3);
  const trns = new Uint8Array(order.length);
  let nTrns = 0;
  for (let i = 0; i < order.length; i++) {
    const c = order[i];
    plte[i * 3] = (c >>> 24) & 0xff;
    plte[i * 3 + 1] = (c >>> 16) & 0xff;
    plte[i * 3 + 2] = (c >>> 8) & 0xff;
    trns[i] = c & 0xff;
    if ((c & 0xff) !== 255) nTrns = i + 1;
  }
  return { samples, plte, trns: nTrns > 0 ? trns.subarray(0, nTrns) : null };
}
function paletteOrderings(rgba, width, height, info) {
  const n = width * height;
  const cols = [...info.set.entries()];
  const freq = cols.slice().sort((a, b) => b[1] - a[1]).map((e) => e[0]);
  const lum = cols.slice().sort((a, b) => {
    const la = 0.299 * ((a[0] >>> 24) & 0xff) + 0.587 * ((a[0] >>> 16) & 0xff) + 0.114 * ((a[0] >>> 8) & 0xff);
    const lb = 0.299 * ((b[0] >>> 24) & 0xff) + 0.587 * ((b[0] >>> 16) & 0xff) + 0.114 * ((b[0] >>> 8) & 0xff);
    return la - lb;
  }).map((e) => e[0]);
  // border-pinned: order by first appearance scanning border pixels, then frequency
  const border = [];
  const seenB = new Set();
  const pushB = (c) => { if (!seenB.has(c)) { seenB.add(c); border.push(c); } };
  for (let x = 0; x < width; x++) {
    pushB((rgba[x * 4] << 24) | (rgba[x * 4 + 1] << 16) | (rgba[x * 4 + 2] << 8) | rgba[x * 4 + 3]);
    pushB((rgba[((height - 1) * width + x) * 4] << 24) | (rgba[((height - 1) * width + x) * 4 + 1] << 16) | (rgba[((height - 1) * width + x) * 4 + 2] << 8) | rgba[((height - 1) * width + x) * 4 + 3]);
  }
  for (let y = 0; y < height; y++) {
    pushB((rgba[(y * width) * 4] << 24) | (rgba[(y * width) * 4 + 1] << 16) | (rgba[(y * width) * 4 + 2] << 8) | rgba[(y * width) * 4 + 3]);
    pushB((rgba[(y * width + width - 1) * 4] << 24) | (rgba[(y * width + width - 1) * 4 + 1] << 16) | (rgba[(y * width + width - 1) * 4 + 2] << 8) | rgba[(y * width + width - 1) * 4 + 3]);
  }
  for (const c of freq) if (!seenB.has(c)) border.push(c);
  // adjacency-optimized: background (most frequent) at 0, greedy walk on the
  // horizontal-adjacency matrix, so neighbours in the image get nearby indices.
  const C = cols.length;
  const cidx = new Map(cols.map((e, i) => [e[0], i]));
  const adj = new Float64Array(C * C);
  for (let y = 0; y < height; y++) {
    const row = y * width;
    for (let x = 0; x < width - 1; x++) {
      const a = (rgba[(row + x) * 4] << 24) | (rgba[(row + x) * 4 + 1] << 16) | (rgba[(row + x) * 4 + 2] << 8) | rgba[(row + x) * 4 + 3];
      const b = (rgba[(row + x + 1) * 4] << 24) | (rgba[(row + x + 1) * 4 + 1] << 16) | (rgba[(row + x + 1) * 4 + 2] << 8) | rgba[(row + x + 1) * 4 + 3];
      const ia = cidx.get(a), ib = cidx.get(b);
      if (ia !== ib) { adj[ia * C + ib]++; adj[ib * C + ia]++; }
    }
  }
  const adjOrder = [];
  const used = new Uint8Array(C);
  let cur = cidx.get(freq[0]);
  adjOrder.push(cols[cur][0]);
  used[cur] = 1;
  for (let step = 1; step < C; step++) {
    let best = -1, bestScore = -1;
    for (let j = 0; j < C; j++) {
      if (used[j]) continue;
      const s = adj[cur * C + j];
      if (s > bestScore) { bestScore = s; best = j; }
    }
    if (best < 0) { // no adjacency left: take the most frequent remaining
      for (const c of freq) { const j = cidx.get(c); if (!used[j]) { best = j; break; } }
    }
    adjOrder.push(cols[best][0]);
    used[best] = 1;
    cur = best;
  }
  return { freq, lum, border, adj: adjOrder };
}
function buildForms(rgba, width, height) {
  const n = width * height;
  const info = analyse(rgba, n);
  const forms = [];
  const z1 = (raw) => deflateSync(raw, { level: 1 }).length;
  // palette (if <=256 distinct colours)
  if (info.set.size <= 256) {
    const ords = paletteOrderings(rgba, width, height, info);
    let best = null;
    for (const [name, order] of [['freq', ords.freq], ['lum', ords.lum], ['border', ords.border], ['adj', ords.adj]]) {
      const pf = paletteForm(rgba, width, height, order);
      const raw = filterStream(pf.samples, width, height, 1, new Uint8Array(height));
      const cost = z1(raw) + pf.plte.length + (pf.trns ? pf.trns.length : 0);
      if (!best || cost < best.cost) best = { name, order, cost, pf };
    }
    slog('  palette orderings best:', best.name, 'z1=', best.cost);
    forms.push({ name: 'pal-' + best.name, bpp: 1, colourType: 3, samples: best.pf.samples, plte: best.pf.plte, trns: best.pf.trns, overhead: 12 + best.pf.plte.length + (best.pf.trns ? 12 + best.pf.trns.length : 0) });
  }
  // grey / grey+alpha
  if (info.grey) {
    const g = new Uint8Array(n);
    for (let i = 0; i < n; i++) g[i] = rgba[i * 4];
    if (info.alphaMin === 255) {
      forms.push({ name: 'grey', bpp: 1, colourType: 0, samples: g, plte: null, trns: null, overhead: 0 });
    } else {
      const ga = new Uint8Array(n * 2);
      for (let i = 0; i < n; i++) { ga[i * 2] = rgba[i * 4]; ga[i * 2 + 1] = rgba[i * 4 + 3]; }
      forms.push({ name: 'greyA', bpp: 2, colourType: 4, samples: ga, plte: null, trns: null, overhead: 0 });
    }
  }
  // RGB + tRNS key (only when the transparent RGB never occurs opaque)
  if (info.alphaMax < 255 && info.trnsKey >= 0) {
    const rgb = new Uint8Array(n * 3);
    for (let i = 0; i < n; i++) { rgb[i * 3] = rgba[i * 4]; rgb[i * 3 + 1] = rgba[i * 4 + 1]; rgb[i * 3 + 2] = rgba[i * 4 + 2]; }
    const trns = new Uint8Array(6);
    trns[1] = (info.trnsKey >>> 16) & 0xff;
    trns[3] = (info.trnsKey >>> 8) & 0xff;
    trns[5] = info.trnsKey & 0xff;
    forms.push({ name: 'rgb-key', bpp: 3, colourType: 2, samples: rgb, plte: null, trns, overhead: 12 + 6 });
  } else if (info.alphaMin === 255) {
    const rgb = new Uint8Array(n * 3);
    for (let i = 0; i < n; i++) { rgb[i * 3] = rgba[i * 4]; rgb[i * 3 + 1] = rgba[i * 4 + 1]; rgb[i * 3 + 2] = rgba[i * 4 + 2]; }
    forms.push({ name: 'rgb', bpp: 3, colourType: 2, samples: rgb, plte: null, trns: null, overhead: 0 });
  }
  // RGBA (always valid)
  forms.push({ name: 'rgba', bpp: 4, colourType: 6, samples: rgba, plte: null, trns: null, overhead: 0 });
  // rank forms by zlib1 on the filter-None stream
  for (const f of forms) {
    const raw = filterStream(f.samples, width, height, f.bpp, new Uint8Array(height));
    f.z1none = z1(raw) + f.overhead;
  }
  forms.sort((a, b) => a.z1none - b.z1none);
  return forms;
}

// ---------- Filter contest ----------
function filterContest(form, width, height) {
  const { vers, costs } = filterVersions(form.samples, width, height, form.bpp);
  const cands = [];
  const add = (name, types) => {
    const raw = filterStream(form.samples, width, height, form.bpp, types);
    cands.push({ name, types, raw, z1: deflateSync(raw, { level: 1 }).length });
  };
  add('none', new Uint8Array(height));
  // minsum from the per-row costs
  const ms = new Uint8Array(height);
  for (let y = 0; y < height; y++) {
    let bt = 0;
    for (let f = 1; f < 5; f++) if (costs[f][y] < costs[bt][y]) bt = f;
    ms[y] = bt;
  }
  add('minsum', ms);
  if (form.bpp === 1) add('smartup', smartUpTypes(form.samples, width, height, form.bpp));
  const pens = form.bpp === 1 ? [0, 96, 640, 4000] : [400, 1600];
  for (const pen of pens) add('vit' + pen, viterbiTypes(costs, height, pen));
  // brute force (only when the form is already the leading candidate: caller
  // passes a flag via form.brute)
  if (form.brute) add('brute', bruteTypes(form.samples, width, height, form.bpp));
  cands.sort((a, b) => a.z1 - b.z1);
  // re-rank the top 2 by zlib6
  const top = cands.slice(0, 2);
  for (const c of top) c.z6 = deflateSync(c.raw, { level: 6 }).length;
  top.sort((a, b) => a.z6 - b.z6);
  const winner = top[0];
  slog('  form', form.name, 'filter contest:', cands.map((c) => c.name + ':' + c.z1).join(' '), '-> winner', winner.name, 'z6=', winner.z6);
  return { winner, cands };
}

// ---------- Driver ----------
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const ids = readdirSync(I).sort();
const results = [];
for (const id of ids) {
    const { width, height, rgba } = decodePng(new Uint8Array(readFileSync(join(I, id, 'image.png'))));
  const forms = buildForms(rgba, width, height);
  slog(id, 'forms ranked:', forms.map((f) => f.name + ':' + f.z1none).join(' '));
  // full contest on the best form (with brute force); reduced contest on the
  // runner-up only when it is within 5% of the best.
  const best = forms[0];
  best.brute = true;
  const c1 = filterContest(best, width, height);
  let winner = { form: best, ...c1.winner };
  if (forms.length > 1 && forms[1].z1none < best.z1none * 1.05) {
    const c2 = filterContest(forms[1], width, height);
    if (c2.winner.z6 < winner.z6) winner = { form: forms[1], ...c2.winner };
  }
  const raw = winner.raw;
  const rowLen = width * winner.form.bpp + 1;
  const lib = deflateSync(raw, { level: 9 });
  // custom DEFLATE (adaptive budgets by stream size)
  const big = raw.length > 2000000;
  const cOpts = {
    iters: winner.form.name.startsWith('pal') ? 6 : 3,
    flat: winner.form.name.startsWith('pal'),
    flatIters: 6,
    skipRuns: false,
    w: big ? 8 : 16,
    chain: big ? 8 : 16,
    blockSize: 196608,
  };
  const custom = compressStream(raw, rowLen, cOpts);
  let idat, method;
  if (custom && custom.zlib.length < lib.length) { idat = custom.zlib; method = 'custom'; }
  else { idat = lib; method = 'lib'; }
  const chunks = [['IHDR', ihdrOf(width, height, winner.form.colourType)]];
  if (winner.form.colourType === 3) chunks.push(['PLTE', winner.form.plte]);
  if (winner.form.trns) chunks.push(['tRNS', winner.form.trns]);
  chunks.push(['IDAT', idat]);
  chunks.push(['IEND', new Uint8Array(0)]);
  const png = pngOf(chunks);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'image.png'), png);
  const rec = {
    id, form: winner.form.name, filter: winner.name, method,
    bytes: png.length, customBytes: custom ? custom.zlib.length : -1, libBytes: lib.length,
    customStats: custom ? custom.stats : null,
  };
  results.push(rec);
  slog(id, JSON.stringify(rec));
}
if (STATS) {
  let tot = 0;
  for (const r of results) tot += r.bytes;
  console.error('TOTAL bytes:', tot);
  console.error(JSON.stringify(results, null, 1));
}
