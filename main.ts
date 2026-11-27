// PNG squeeze R7 — own encoder written from the R5/R6/R7 prose briefs.
// Dual-indexed binary-tree match finder (3-byte hash tree is primary; every
// position is inserted into it) + optimal-parse DEFLATE + filter contest.
import { readFileSync, writeFileSync, mkdirSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { inflateSync, deflateRawSync, deflateSync } from 'node:zlib';

const NODE = process.argv[2] === '--diag' ? 'diag' : 'run';
const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const W = 1280, H = 720, NPIX = W * H;

// ---- DEFLATE length / distance tables ----
const LEN_BASE = [3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258];
const LEN_EXT = [0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0];
const DIST_BASE = [1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577];
const DIST_EXT = [0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13];
function lenSymIdx(len) { let i = 0; while (i < 28 && LEN_BASE[i + 1] <= len) i++; return i; }
function distSymIdx(d) { let i = 0; while (i < 29 && DIST_BASE[i + 1] <= d) i++; return i; }
const LEN_SYM = (() => { const t = new Uint8Array(259); for (let l = 3; l <= 258; l++) t[l] = lenSymIdx(l); return t; })();
const DIST_SYM = (() => { const t = new Uint8Array(32769); for (let d = 1; d <= 32768; d++) t[d] = distSymIdx(d); return t; })();
function lenRangeEnds(len) { const i = lenSymIdx(len); const s = LEN_BASE[i]; const e = i === 28 ? 258 : LEN_BASE[i + 1] - 1; return [s, Math.min(e, len)]; }

// ---- CRC32 / Adler32 ----
const CRC_T = (() => { const t = new Int32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; t[n] = c; } return t; })();
function crc32(b, s = 0, e = b.length) { let c = -1; for (let i = s; i < e; i++) c = CRC_T[(c ^ b[i]) & 255] ^ (c >>> 8); return (c ^ -1) >>> 0; }
function adler32(b) { let a = 1, c = 0; for (let i = 0; i < b.length;) { const e = Math.min(b.length, i + 5552); for (; i < e; i++) { a += b[i]; c += a; } a %= 65521; c %= 65521; } return ((c << 16) | a) >>> 0; }
function chunk(type, data) { const o = new Uint8Array(12 + data.length); const v = new DataView(o.buffer); v.setUint32(0, data.length); for (let i = 0; i < 4; i++) o[4 + i] = type.charCodeAt(i); o.set(data, 8); v.setUint32(8 + data.length, crc32(o, 4, 8 + data.length)); return o; }
function pngOf(chunks) { let s = 8; for (const c of chunks) s += c.length; const o = new Uint8Array(s); o.set([137,80,78,71,13,10,26,10]); let at = 8; for (const c of chunks) { o.set(c, at); at += c.length; } return o; }
function ihdr(ct) { const d = new Uint8Array(13); const v = new DataView(d.buffer); v.setUint32(0, W); v.setUint32(4, H); d[8] = 8; d[9] = ct; return d; }

// ---- PNG decode to RGBA (input is type 6, but decode generically) ----
function paeth(a, b, c) { const p = a + b - c; const pa = p > a ? p - a : a - p; const pb = p > b ? p - b : b - p; const pc = p > c ? p - c : c - p; if (pa <= pb && pa <= pc) return a; return pb <= pc ? b : c; }
function decodePng(bytes) {
  const v = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8, ct = 0, palette = null, trns = null; const idat = [];
  while (at < bytes.length) {
    const len = v.getUint32(at); const type = String.fromCharCode(bytes[at+4], bytes[at+5], bytes[at+6], bytes[at+7]);
    const data = bytes.subarray(at + 8, at + 8 + len); at += 12 + len;
    if (type === 'IHDR') ct = data[9];
    else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
  }
  const ch = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 }[ct];
  const stride = W * ch;
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat));
  const samples = new Uint8Array(H * stride);
  for (let y = 0; y < H; y++) {
    const ft = raw[y * (stride + 1)], src = y * (stride + 1) + 1, o = y * stride, p = o - stride;
    for (let i = 0; i < stride; i++) {
      const rv = raw[src + i];
      if (ft === 0) samples[o + i] = rv;
      else if (ft === 1) samples[o + i] = rv + (i >= ch ? samples[o + i - ch] : 0);
      else if (ft === 2) samples[o + i] = rv + (y > 0 ? samples[p + i] : 0);
      else if (ft === 3) samples[o + i] = rv + (((i >= ch ? samples[o + i - ch] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
      else { const a = i >= ch ? samples[o + i - ch] : 0, b = y > 0 ? samples[p + i] : 0, c = y > 0 && i >= ch ? samples[p + i - ch] : 0; samples[o + i] = rv + paeth(a, b, c); }
    }
  }
  const rgba = new Uint8Array(NPIX * 4);
  if (ct === 6) rgba.set(samples);
  else if (ct === 2) { const key = trns ? (trns[1] << 16) | (trns[3] << 8) | trns[5] : -1; for (let i = 0, s = 0, d = 0; i < NPIX; i++, s += 3, d += 4) { rgba[d] = samples[s]; rgba[d+1] = samples[s+1]; rgba[d+2] = samples[s+2]; rgba[d+3] = ((samples[s] << 16) | (samples[s+1] << 8) | samples[s+2]) === key ? 0 : 255; } }
  else if (ct === 0) { const key = trns ? trns[1] : -1; for (let i = 0, d = 0; i < NPIX; i++, d += 4) { const g = samples[i]; rgba[d] = rgba[d+1] = rgba[d+2] = g; rgba[d+3] = g === key ? 0 : 255; } }
  else if (ct === 4) { for (let i = 0, s = 0, d = 0; i < NPIX; i++, s += 2, d += 4) { rgba[d] = rgba[d+1] = rgba[d+2] = samples[s]; rgba[d+3] = samples[s+1]; } }
  else { const e = palette.length / 3; for (let i = 0, d = 0; i < NPIX; i++, d += 4) { const k = samples[i] * 3; rgba[d] = palette[k]; rgba[d+1] = palette[k+1]; rgba[d+2] = palette[k+2]; rgba[d+3] = trns && samples[i] < trns.length ? trns[samples[i]] : 255; } }
  return rgba;
}

// ---- PNG filters ----
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) { for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0); }
  else if (type === 2) { for (let i = 0; i < n; i++) out[i] = cur[i] - (prev ? prev[i] : 0); }
  else if (type === 3) { for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev ? prev[i] : 0)) >> 1); }
  else { for (let i = 0; i < n; i++) { const a = i >= bpp ? cur[i - bpp] : 0, b = prev ? prev[i] : 0, c = prev && i >= bpp ? prev[i - bpp] : 0; out[i] = cur[i] - paeth(a, b, c); } }
}
function buildFiltered(samples, bpp, seq) {
  const stride = W * bpp, raw = new Uint8Array(H * (stride + 1));
  for (let y = 0; y < H; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride), prev = y ? samples.subarray((y - 1) * stride, y * stride) : null;
    raw[y * (stride + 1)] = seq[y];
    filterRow(seq[y], cur, prev, bpp, raw.subarray(y * (stride + 1) + 1, (y + 1) * (stride + 1)));
  }
  return raw;
}
// Per-row, per-filter cheap cost + the five filtered streams (cached so
// candidate streams can be assembled by row copies instead of re-filtering).
function rowCosts(samples, bpp) {
  const stride = W * bpp, cost = new Float64Array(H * 5);
  const filtered = Array.from({ length: 5 }, () => new Uint8Array(H * (stride + 1)));
  const trial = new Uint8Array(stride);
  for (let y = 0; y < H; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride), prev = y ? samples.subarray((y - 1) * stride, y * stride) : null;
    for (let f = 0; f < 5; f++) {
      filterRow(f, cur, prev, bpp, trial);
      filtered[f][y * (stride + 1)] = f;
      filtered[f].set(trial, y * (stride + 1) + 1);
      let s = 0;
      for (let i = 0; i < stride; i++) { const v = trial[i]; if (v) { const a = v < 128 ? v : 256 - v; s += a < 2 ? 1 : a < 8 ? 2 : a < 32 ? 3 : a < 128 ? 4 : 5; } }
      cost[y * 5 + f] = s;
    }
  }
  return { cost, filtered };
}
function buildFromCache(filtered, seq) {
  const stride = filtered[0].length / H - 1, raw = new Uint8Array(H * (stride + 1));
  for (let y = 0; y < H; y++) raw.set(filtered[seq[y]].subarray(y * (stride + 1), (y + 1) * (stride + 1)), y * (stride + 1));
  return raw;
}
function viterbi(cost, penalty) {
  const dp = new Float64Array(5), ndp = new Float64Array(5), back = new Int8Array(H * 5);
  for (let f = 0; f < 5; f++) dp[f] = cost[f];
  for (let y = 1; y < H; y++) {
    for (let f = 0; f < 5; f++) { let best = Infinity, bf = 0; for (let g = 0; g < 5; g++) { const c = dp[g] + (g === f ? 0 : penalty); if (c < best) { best = c; bf = g; } } ndp[f] = best + cost[y * 5 + f]; back[y * 5 + f] = bf; }
    dp.set(ndp);
  }
  let f = 0; for (let g = 1; g < 5; g++) if (dp[g] < dp[f]) f = g;
  const seq = new Uint8Array(H); seq[H - 1] = f;
  for (let y = H - 1; y > 0; y--) { f = back[y * 5 + f]; seq[y - 1] = f; }
  return seq;
}
function bandSeq(cost, band) {
  const seq = new Uint8Array(H);
  for (let y0 = 0; y0 < H; y0 += band) {
    let bf = 0, bs = Infinity;
    for (let f = 0; f < 5; f++) { let s = 0; for (let y = y0; y < Math.min(H, y0 + band); y++) s += cost[y * 5 + f]; if (s < bs) { bs = s; bf = f; } }
    for (let y = y0; y < Math.min(H, y0 + band); y++) seq[y] = bf;
  }
  return seq;
}
function minsumSeq(cost) { const seq = new Uint8Array(H); for (let y = 0; y < H; y++) { let bf = 0; for (let f = 1; f < 5; f++) if (cost[y * 5 + f] < cost[y * 5 + bf]) bf = f; seq[y] = bf; } return seq; }
function constSeq(f) { const s = new Uint8Array(H); s.fill(f); return s; }
function smartUp(samples) { // palette: Up on rows identical to above with a horizontal change, else None
  const stride = W, seq = new Uint8Array(H);
  for (let y = 1; y < H; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride), prev = samples.subarray((y - 1) * stride, y * stride);
    let same = true, change = false;
    for (let i = 0; i < stride; i++) { if (cur[i] !== prev[i]) { same = false; break; } if (i && cur[i] !== cur[i - 1]) change = true; }
    seq[y] = same && change ? 2 : 0;
  }
  return seq;
}

// ---- Huffman lengths (heap build + limit to `limit` bits, Kraft repair) ----
function huffLengths(freq, limit) {
  const n = freq.length, len = new Uint8Array(n);
  let syms = 0; for (let i = 0; i < n; i++) if (freq[i] > 0) syms++;
  if (syms === 0) return len;
  if (syms === 1) { for (let i = 0; i < n; i++) if (freq[i] > 0) len[i] = 1; return len; }
  // heap of [freq, id]; id<0 means internal node index into nodes[]
  const nodes = []; // {f, l, r, sym}
  const heap = [];
  const push = (f, id) => { heap.push([f, id]); let i = heap.length - 1; while (i > 0) { const p = (i - 1) >> 1; if (heap[p][0] <= heap[i][0]) break; const t = heap[p]; heap[p] = heap[i]; heap[i] = t; i = p; } };
  const pop = () => { const top = heap[0], last = heap.pop(); if (heap.length) { heap[0] = last; let i = 0; for (;;) { const l = i * 2 + 1, r = l + 1; let m = i; if (l < heap.length && heap[l][0] < heap[m][0]) m = l; if (r < heap.length && heap[r][0] < heap[m][0]) m = r; if (m === i) break; const t = heap[m]; heap[m] = heap[i]; heap[i] = t; i = m; } } return top; };
  for (let i = 0; i < n; i++) if (freq[i] > 0) push(freq[i], i);
  while (heap.length > 1) { const a = pop(), b = pop(); const id = -1 - nodes.length; nodes.push({ f: a[0] + b[0], l: a[1], r: b[1] }); push(a[0] + b[0], id); }
  const root = pop()[1];
  const walk = (id, d) => { if (id >= 0) { len[id] = d; return; } const nd = nodes[-1 - id]; walk(nd.l, d + 1); walk(nd.r, d + 1); };
  walk(root, 0);
  let over = false; for (let i = 0; i < n; i++) if (len[i] > limit) { len[i] = limit; over = true; }
  if (over) { // repair Kraft: while sum 2^-len > 1, deepen the rarest shallow symbol
    for (;;) {
      let kraft = 0; for (let i = 0; i < n; i++) if (len[i]) kraft += 1 / (1 << len[i]);
      if (kraft <= 1.0000001) break;
      let bi = -1, bf = Infinity; for (let i = 0; i < n; i++) if (len[i] && len[i] < limit && freq[i] < bf) { bf = freq[i]; bi = i; }
      if (bi < 0) break; len[bi]++;
    }
  }
  return len;
}
// Exact Kraft check in integer units: sum 2^(limit-len) over used symbols
// must equal 2^limit (a complete prefix code). huffLengths' clamp-and-repair
// can overshoot below 1 (e.g. 0.9922), which zlib rejects as
// "invalid code lengths set" for the code-length alphabet.
function kraftOk(len, limit) {
  const T = 1 << limit; let k = 0;
  for (let i = 0; i < len.length; i++) if (len[i]) k += 1 << (limit - len[i]);
  return k === T;
}
function lengthsValid(ll, dl) {
  if (!kraftOk(ll, 15) || !kraftOk(dl, 15)) return false;
  const hb = headerBits(ll, dl);
  return kraftOk(hb.clLen, 7);
}
function codesFromLengths(len) {
  const n = len.length, bl = new Uint16Array(16), codes = new Uint16Array(n);
  for (let i = 0; i < n; i++) bl[len[i]]++;
  bl[0] = 0; let code = 0;
  const next = new Uint16Array(16);
  for (let b = 1; b < 16; b++) { code = (code + bl[b - 1]) << 1; next[b] = code; }
  for (let i = 0; i < n; i++) if (len[i]) { codes[i] = next[len[i]]; next[len[i]]++; }
  // reverse bits (DEFLATE codes are packed MSB-first)
  for (let i = 0; i < n; i++) if (len[i]) { let c = codes[i], r = 0; for (let k = 0; k < len[i]; k++) { r = (r << 1) | (c & 1); c >>= 1; } codes[i] = r; }
  return codes;
}
const FIXED_LIT_LEN = (() => { const l = new Uint8Array(288); for (let i = 0; i < 288; i++) l[i] = i < 144 ? 8 : i < 256 ? 9 : i < 280 ? 7 : 8; return l; })();
const FIXED_DIST_LEN = new Uint8Array(30).fill(5);

// ---- Bit writer ----
class BW {
  constructor(cap) { this.b = new Uint8Array(cap); this.p = 0; this.acc = 0; this.nbits = 0; }
  w(v, n) { this.acc |= (v & ((1 << n) - 1)) << this.nbits; this.nbits += n; while (this.nbits >= 8) { if (this.p >= this.b.length) { const nb = new Uint8Array(this.b.length * 2); nb.set(this.b); this.b = nb; } this.b[this.p++] = this.acc & 255; this.acc >>>= 8; this.nbits -= 8; } }
  sym(code, len) { this.w(code, len); }
  finish() { if (this.nbits) { this.b[this.p++] = this.acc & 255; this.acc = 0; this.nbits = 0; } return this.b.subarray(0, this.p); }
}

// ---- Binary-tree match finder (R7 fix: 3-byte hash tree is PRIMARY) ----
// The tree is a TREAP per 3-byte hash bucket: a binary search tree ordered by
// suffix, heap-ordered by a deterministic priority of the position, so depth
// stays O(log n) and EVERY position stays in the tree (no cap, no eviction,
// no dropped positions). Any two positions sharing a 3-byte prefix can find
// each other through it. Supplementary fast paths (most-recent maximal run
// per first byte, last-16 ring per hash, row-above probes) are consulted
// first but never hide the tree walk.
class Finder {
  constructor(w, depth, maxLen, rowStride) {
    this.w = w; this.m = w.length; this.depth = depth; this.maxLen = maxLen; this.rowStride = rowStride;
    this.head = new Int32Array(65536).fill(-1);
    this.left = new Int32Array(this.m).fill(-1); this.right = new Int32Array(this.m).fill(-1);
    this.prio = new Uint32Array(this.m);
    for (let i = 0; i < this.m; i++) { let x = (i * 2654435761 + 0x9e3779b9) >>> 0; x = (x ^ (x >>> 16)) * 0x7feb352d >>> 0; x = (x ^ (x >>> 15)) * 0x846ca68b >>> 0; x ^= x >>> 16; this.prio[i] = x >>> 0; }
    this.run = new Int32Array(this.m);
    for (let i = this.m - 1; i >= 0; i--) this.run[i] = (i + 1 < this.m && w[i + 1] === w[i]) ? Math.min(520, this.run[i + 1] + 1) : 1;
    this.maxRun = new Int32Array(256).fill(-1); // most recent pos starting a 258+ run, per first byte
    this.ring = new Int32Array(65536 * 16).fill(-1); // per 3-byte hash, last 16 positions (supplementary)
    this.ringIdx = new Uint8Array(65536);
    this.scr = new Int32Array(64); this.scrN = 0; this.cC = 0; this.cL = 0;
    this.path = new Int32Array(512); this.pathDir = new Int8Array(512);
    this.ins = 0; this.visits = 0;
  }
  hash3(p) { const w = this.w; return (((w[p] << 16) ^ (w[p + 1] << 8) ^ w[p + 2]) * 2654435761 >>> 16) & 65535; }
  mlen(a, b, cap) {
    const w = this.w;
    if (w[a] !== w[b]) return 0;
    let l = 0;
    const r = Math.min(this.run[a], this.run[b], cap);
    if (r >= 3) { l = r; if (l >= cap) return cap; }
    // compare remaining bytes (after the identical-byte run prefix)
    while (l < cap && a + l < this.m && b + l < this.m && w[a + l] === w[b + l]) l++;
    return l;
  }
  // Iterative treap insert with inlined match-length (no per-node calls).
  // `collect` records (len,dist) candidates into this.scr during the walk.
  // Returns the (possibly rotated) subtree root. `h` is the hash bucket.
  insRec(root, p, collect) {
    if (root < 0) return p;
    const w = this.w, m = this.m, run = this.run, left = this.left, right = this.right, prio = this.prio;
    const path = this.path, pdir = this.pathDir;
    let node = root, depth = 0;
    for (;;) {
      this.visits++;
      // inline mlen(p, node)
      let l = 0, dir;
      if (w[p] === w[node]) {
        const cap = Math.min(258, m - p, m - node);
        let r = run[p]; if (run[node] < r) r = run[node]; if (cap < r) r = cap;
        if (r >= 3) { l = r; if (l < cap) { while (l < cap && w[p + l] === w[node + l]) l++; } }
        else { while (l < cap && w[p + l] === w[node + l]) l++; }
        if (l < cap) dir = w[p + l] < w[node + l] ? 0 : 1;
        else if (m - p !== m - node) dir = m - p < m - node ? 0 : 1;
        else dir = p < node ? 0 : 1;
        if (l >= 3 && collect && this.scrN < 64 && p - node <= 32768) this.scr[this.scrN++] = (l << 15) | (32768 - (p - node));
      } else { dir = w[p] < w[node] ? 0 : 1; l = 0; }
      path[depth] = node; pdir[depth] = dir; depth++;
      const child = dir ? right[node] : left[node];
      if (child < 0) { if (dir) right[node] = p; else left[node] = p; break; }
      node = child;
      if (depth >= 512) return root; // safety: treap depth is O(log n); drop this insert
    }
    // rotate back up the path
    let sub = p;
    for (let k = depth - 1; k >= 0; k--) {
      const a = path[k];
      const childOnPath = k === depth - 1 ? p : path[k + 1];
      void childOnPath;
      // the child of a on the path is now `sub`'s subtree root after any rotation below;
      // link a's child pointer to sub first
      if (pdir[k]) right[a] = sub; else left[a] = sub;
      // rotate if the child has higher priority (smaller prio value)
      if (prio[sub] < prio[a]) {
        if (pdir[k]) { // left rotation at a
          const y = sub; right[a] = left[y]; left[y] = a; sub = y;
        } else { // right rotation at a
          const x = sub; left[a] = right[x]; right[x] = a; sub = x;
        }
      } else sub = a;
      if (k === 0) return sub;
    }
    return root;
  }
  record(p) {
    const w = this.w;
    if (this.run[p] >= 258) this.maxRun[w[p]] = p;
    const h = (p + 2 < this.m) ? this.hash3(p) : 0;
    this.ring[h * 16 + this.ringIdx[h]] = p; this.ringIdx[h] = (this.ringIdx[h] + 1) & 15;
  }
  insert(p) { // plain insert (history positions): no candidate collection
    this.record(p);
    const h = (p + 2 < this.m) ? this.hash3(p) : 0;
    this.head[h] = this.insRec(this.head[h], p, false);
  }
  // Find candidates for p AND insert p, in one treap walk (the walk visits
  // exactly the nodes a search would; rotations happen on the way back up,
  // after the candidates are recorded). Candidates are packed ints
  // (len<<15)|(32768-dist) in this.scr; returns the count after Pareto filtering.
  // Supplementary probes run first but never hide the tree walk.
  find(p) {
    const w = this.w; this.scrN = 0;
    const mr = this.maxRun[w[p]];
    if (mr >= 0 && mr < p && p - mr <= 32768) { const l = this.mlen(p, mr, Math.min(this.maxLen, this.m - p)); if (l >= 3 && this.scrN < 64) this.scr[this.scrN++] = (l << 15) | (32768 - (p - mr)); }
    for (let k = 1; k <= 2; k++) { const q = p - k * this.rowStride; if (q >= 0) { const l = this.mlen(p, q, Math.min(this.maxLen, this.m - p)); if (l >= 3 && this.scrN < 64) this.scr[this.scrN++] = (l << 15) | (32768 - (p - q)); } }
    if (p + 2 < this.m) {
      const h = this.hash3(p);
      for (let k = 0; k < 2; k++) { const q = this.ring[h * 16 + k]; if (q >= 0 && q < p && p - q <= 32768) { const l = this.mlen(p, q, Math.min(this.maxLen, this.m - p)); if (l >= 3 && this.scrN < 64) this.scr[this.scrN++] = (l << 15) | (32768 - (p - q)); } }
      this.record(p);
      this.head[h] = this.insRec(this.head[h], p, true);
    } else this.record(p);
    // Pareto-filter in place: sort ascending numerically (native, no
    // comparator), then scan from the largest down, keeping strictly nearer
    // distances as len falls.
    const s = this.scr.subarray(0, this.scrN);
    s.sort();
    let n = 0, mind = Infinity;
    for (let k = this.scrN - 1; k >= 0; k--) { const pk = s[k]; const d = 32768 - (pk & 32767); if (d < mind) { s[n++] = pk; mind = d; } }
    this.scrN = n;
    return n;
  }
}

// ---- Optimal parse of one block (data = filtered stream slice, hist = preceding bytes) ----
const MAXC = 6;
function parseBlock(data, hist, rowStride, iters, depth, maxLen, flat) {
  const n = data.length;
  const w = new Uint8Array(hist.length + n); w.set(hist); w.set(data, hist.length);
  const base = hist.length;
  const finder = new Finder(w, depth, maxLen, rowStride);
  for (let h = 0; h < base; h++) finder.insert(h); // history positions in first
  // candidate cache, filled lazily during iteration 0
  const candLen = new Uint16Array(n * MAXC), candDist = new Uint32Array(n * MAXC);
  const expScr = new Int32Array(128);
  // We compute candidates for position i on first use and store count+1 (0 = unknown)
  const cntArr = new Uint8Array(n); // stored count, 0 = not yet computed
  const computeCands = (i) => {
    if (cntArr[i]) return cntArr[i] - 1;
    const rn = finder.find(base + i); // packed (len<<15)|(32768-dist) in finder.scr
    // expand: each candidate also offers length-code range endpoints + len 3
    let en = 0;
    for (let k = 0; k < rn; k++) {
      const pk = finder.scr[k], L = pk >>> 15, cd = pk & 32767;
      expScr[en++] = pk;
      const li = LEN_SYM[L], s = LEN_BASE[li], e0 = li === 28 ? 258 : LEN_BASE[li + 1] - 1, e = e0 > L ? L : e0;
      if (s !== L && s >= 3 && en < 128) expScr[en++] = (s << 15) | cd;
      if (e !== L && e >= 3 && en < 128) expScr[en++] = (e << 15) | cd;
      if (L > 3 && en < 128) expScr[en++] = (3 << 15) | cd;
    }
    const es = expScr.subarray(0, en);
    es.sort(); // ascending numeric; scan from the largest down
    let keep = 0, mind = Infinity;
    for (let k = en - 1; k >= 0; k--) {
      const pk = es[k], L = pk >>> 15, D = 32768 - (pk & 32767);
      if (D < mind) { candLen[i * MAXC + keep] = L; candDist[i * MAXC + keep] = D; mind = D; keep++; if (keep >= MAXC) break; }
    }
    cntArr[i] = keep + 1;
    return keep;
  };
  const dp = new Float64Array(n + 1), prev = new Int32Array(n + 1), plen = new Uint16Array(n + 1), pdist = new Uint32Array(n + 1);
  let litCost = new Float64Array(288), distCost = new Float64Array(30);
  const setCostsFromLengths = (ll, dl) => {
    for (let s = 0; s < 288; s++) litCost[s] = ll[s];
    for (let s = 0; s < 30; s++) distCost[s] = dl[s];
  };
  let bestTokens = null, bestBits = Infinity, bestLL = null, bestDL = null;
  // cost tables start at fixed Huffman
  setCostsFromLengths(FIXED_LIT_LEN, FIXED_DIST_LEN);
  for (let it = 0; it < iters; it++) {
    dp.fill(Infinity); dp[0] = 0; prev[0] = -1;
    for (let i = 0; i < n; i++) {
      const di = dp[i]; if (!isFinite(di)) continue;
      // literal
      const lc = di + litCost[data[i]];
      if (lc < dp[i + 1]) { dp[i + 1] = lc; prev[i + 1] = i; plen[i + 1] = 1; pdist[i + 1] = 0; }
      const nc = computeCands(i);
      for (let k = 0; k < nc; k++) {
        const L = candLen[i * MAXC + k], D = candDist[i * MAXC + k];
        if (D > 32768 || i + L > n) continue;
        const li = LEN_SYM[L], dci = DIST_SYM[D];
        const c = di + litCost[257 + li] + LEN_EXT[li] + distCost[dci] + DIST_EXT[dci];
        if (c < dp[i + L]) { dp[i + L] = c; prev[i + L] = i; plen[i + L] = L; pdist[i + L] = D; }
      }
    }
    const bits = dp[n];
    void bits;
    // walk back to tokens + frequencies
    const freqL = new Uint32Array(288), freqD = new Uint32Array(30);
    const toks = [];
    let pos = n;
    while (pos > 0) { const pr = prev[pos], L = plen[pos], D = pdist[pos]; toks.push([pr, L, D]); if (L === 1) freqL[data[pr]]++; else { freqL[257 + LEN_SYM[L]]++; freqD[DIST_SYM[D]]++; } pos = pr; }
    toks.reverse();
    freqL[256] = 1; // end-of-block must always have a code
    let dSum = 0; for (let s = 0; s < 30; s++) dSum += freqD[s];
    if (dSum === 0) freqD[0] = 1; // at least one distance code
    // Judge iterations by ACTUAL encoded bits (dynamic or fixed, whichever is smaller),
    // never by the cost-table dp value: a cost table that prices unused symbols
    // at 0 bits would otherwise fake a tiny dp and win with a literal-heavy parse.
    const itLL = huffLengths(freqL, 15), itDL = huffLengths(freqD, 15);
    const dynBits = dataBits(toks, data, itLL, itDL) + headerBits(itLL, itDL).bits + 3;
    const fixBits = dataBits(toks, data, FIXED_LIT_LEN, FIXED_DIST_LEN) + 3;
    const actual = Math.min(dynBits, fixBits);
    if (actual < bestBits) { bestBits = actual; bestTokens = toks; if (dynBits <= fixBits) { bestLL = itLL; bestDL = itDL; } else { bestLL = FIXED_LIT_LEN; bestDL = FIXED_DIST_LEN; } }
    if (it === iters - 1) break;
    // re-derive costs; an unused symbol keeps its FIXED length as its price
    // (a 0-bit price would make the DP think that symbol is free).
    const nLLf = new Float64Array(288), nDLf = new Float64Array(30);
    for (let s = 0; s < 288; s++) nLLf[s] = itLL[s] > 0 ? itLL[s] : FIXED_LIT_LEN[s];
    for (let s = 0; s < 30; s++) nDLf[s] = itDL[s] > 0 ? itDL[s] : FIXED_DIST_LEN[s];
    if (it % 2 === 1) {
      for (let s = 0; s < 288; s++) litCost[s] = litCost[s] * 0.5 + nLLf[s] * 0.5;
      for (let s = 0; s < 30; s++) distCost[s] = distCost[s] * 0.5 + nDLf[s] * 0.5;
    } else { litCost.set(nLLf); distCost.set(nDLf); }
  }
  return { tokens: bestTokens, bits: bestBits, ll: bestLL, dl: bestDL, finder, n };
}
// ---- Dynamic header cost + encoding helpers ----
const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
function clRle(lengths) {
  // returns {seq: [sym...], freq}
  const seq = []; const freq = new Uint32Array(19);
  let i = 0; const n = lengths.length;
  while (i < n) {
    const v = lengths[i]; let run = 1; while (i + run < n && lengths[i + run] === v) run++;
    if (v === 0) {
      let r = run;
      while (r >= 11) { const t = Math.min(r, 138); seq.push([18, t - 11]); freq[18]++; r -= t; }
      while (r >= 3) { const t = Math.min(r, 10); seq.push([17, t - 3]); freq[17]++; r -= t; }
      while (r > 0) { seq.push([0]); freq[0]++; r--; }
    } else {
      seq.push([v]); freq[v]++;
      let r = run - 1;
      while (r >= 3) { const t = Math.min(r, 6); seq.push([16, t - 3]); freq[16]++; r -= t; }
      while (r > 0) { seq.push([v]); freq[v]++; r--; }
    }
    i += run;
  }
  return { seq, freq };
}
function headerBits(ll, dl) {
  let hlit = 288; while (hlit > 257 && ll[hlit - 1] === 0) hlit--;
  let hdist = 30; while (hdist > 1 && dl[hdist - 1] === 0) hdist--;
  const all = new Uint8Array(hlit + hdist); all.set(ll.subarray(0, hlit)); all.set(dl.subarray(0, hdist), hlit);
  const { seq, freq } = clRle(all);
  const clLen = huffLengths(freq, 7);
  let ncl = 19; while (ncl > 4 && clLen[CL_ORDER[ncl - 1]] === 0) ncl--;
  let bits = 5 + 5 + 4 + ncl * 3;
  for (const [s, x] of seq) { bits += clLen[s]; if (s === 16) bits += 2; else if (s === 17) bits += 3; else if (s === 18) bits += 7; void x; }
  return { bits, hlit, hdist, clLen, ncl, seq };
}
// Encode one block's tokens into the SHARED bit writer (never finish() here:
// DEFLATE blocks are concatenated at the bit level, not byte-aligned).
function encodeBlock(tokens, data, ll, dl, useFixed, last, bw) {
  const litL = useFixed ? FIXED_LIT_LEN : ll, distL = useFixed ? FIXED_DIST_LEN : dl;
  const litC = codesFromLengths(litL), distC = codesFromLengths(distL);
  let hb = null;
  if (!useFixed) hb = headerBits(ll, dl);
  bw.w(last ? 1 : 0, 1); bw.w(useFixed ? 1 : 2, 2);
  if (!useFixed) {
    const { hlit, hdist, clLen, ncl, seq } = hb;
    bw.w(hlit - 257, 5); bw.w(hdist - 1, 5); bw.w(ncl - 4, 4);
    for (let k = 0; k < ncl; k++) bw.w(clLen[CL_ORDER[k]], 3);
    const clC = codesFromLengths(clLen);
    for (const [s, x] of seq) {
      bw.sym(clC[s], clLen[s]);
      if (s === 16) bw.w(x, 2); else if (s === 17) bw.w(x, 3); else if (s === 18) bw.w(x, 7);
    }
  }
  for (const [pr, L, D] of tokens) {
    if (L === 1) bw.sym(litC[data[pr]], litL[data[pr]]);
    else {
      const li = LEN_SYM[L], di = DIST_SYM[D];
      bw.sym(litC[257 + li], litL[257 + li]); if (LEN_EXT[li]) bw.w(L - LEN_BASE[li], LEN_EXT[li]);
      bw.sym(distC[di], distL[di]); if (DIST_EXT[di]) bw.w(D - DIST_BASE[di], DIST_EXT[di]);
    }
  }
  bw.sym(litC[256], litL[256]);
}
function dataBits(tokens, data, ll, dl) {
  let b = 0;
  for (const [pr, L, D] of tokens) { if (L === 1) b += ll[data[pr]]; else { const li = LEN_SYM[L], di = DIST_SYM[D]; b += ll[257 + li] + LEN_EXT[li] + dl[di] + DIST_EXT[di]; } }
  return b + ll[256];
}
// Compress one filtered stream with custom DEFLATE; returns {raw, customBytes, libBytes, blocks}
function customDeflate(stream, rowStride, flat) {
  // block boundaries: at filter-change rows, cap ~200 KB, run-aware
  const bounds = [0];
  let acc = 0, lastF = stream[0];
  for (let y = 0; y < H; y++) {
    const rs = y * rowStride;
    if (y > 0 && stream[rs] !== lastF) { if (acc >= 250000) { bounds.push(rs); acc = 0; } }
    lastF = stream[rs]; acc += rowStride;
    if (acc >= 450000) { bounds.push((y + 1) * rowStride); acc = 0; }
  }
  if (bounds[bounds.length - 1] !== stream.length) bounds.push(stream.length);
  // run-aware adjustment: never cut inside an identical-byte run
  for (let b = 1; b < bounds.length - 1; b++) {
    const p = bounds[b];
    if (p > 0 && p < stream.length && stream[p] === stream[p - 1]) {
      let q = p; while (q < stream.length && stream[q] === stream[p - 1] && q - p < 4096) q++;
      if (q < stream.length && q - p < 4096) bounds[b] = q;
    }
  }
  let totalVisits = 0, totalPos = 0;
  const lib = deflateRawSync(stream, { level: 9 });
  // Sampled decision: parse one middle block and run the full custom parse
  // only if it beats the library by >3% on the sample. The custom parse costs
  // ~10x the library on big streams; spending it where it wins <3% (or loses)
  // is what blows the wall budget.
  const nb = bounds.length - 1;
  let sampleCustom = 0, sampleLib = 0;
  if (nb > 2) {
    const b = Math.floor((nb - 1) / 2);
    const from = bounds[b], to = bounds[b + 1];
    const data = stream.subarray(from, to);
    const histStart = Math.max(0, from - 32768);
    const hist = stream.subarray(histStart, from);
    const nn = data.length;
    const itersS = flat ? 4 : 3;
    const rS = parseBlock(data, hist, rowStride, itersS, flat ? 192 : 128, nn > 500000 ? 128 : 258, flat);
    const dynBits = dataBits(rS.tokens, data, rS.ll, rS.dl) + headerBits(rS.ll, rS.dl).bits + 3;
    const fixBits = dataBits(rS.tokens, data, FIXED_LIT_LEN, FIXED_DIST_LEN) + 3;
    sampleCustom += Math.min(dynBits, fixBits) / 8;
    sampleLib += deflateRawSync(data, { level: 9 }).length;
    if (sampleCustom >= sampleLib * 0.97) {
      return { raw: lib, customBytes: -1, libBytes: lib.length + 6, visits: 0, positions: 0, blocks: nb, skipped: true, sampleCustom: Math.round(sampleCustom), sampleLib };
    }
  }
  const bw = new BW(Math.max(1024, stream.length + 65536));
  for (let b = 0; b < bounds.length - 1; b++) {
    const from = bounds[b], to = bounds[b + 1];
    const data = stream.subarray(from, to);
    const histStart = Math.max(0, from - 32768);
    const hist = stream.subarray(histStart, from);
    const n = data.length;
    const iters = flat ? 4 : 3;
    const depth = flat ? 192 : 128;
    const maxLen = n > 500000 ? 128 : 258;
    const r = parseBlock(data, hist, rowStride, iters, depth, maxLen, flat);
    totalVisits += r.finder.visits; totalPos += n;
    const dynBits = dataBits(r.tokens, data, r.ll, r.dl) + headerBits(r.ll, r.dl).bits + 3;
    const fixBits = dataBits(r.tokens, data, FIXED_LIT_LEN, FIXED_DIST_LEN) + 3;
    const useFixed = fixBits <= dynBits || !lengthsValid(r.ll, r.dl);
    const last = b === bounds.length - 2;
    encodeBlock(r.tokens, data, r.ll, r.dl, useFixed, last, bw);
  }
  const raw = bw.finish();
  return { raw, customBytes: raw.length + 6, libBytes: lib.length + 6, visits: totalVisits, positions: totalPos, blocks: bounds.length - 1 };
}

// ---- Image analysis + colour forms ----
function analyze(rgba) {
  const map = new Map(); let grey = true, alphaVar = false, allOpaque = true, transpKey = -1, transpCount = 0;
  const freq = new Map();
  for (let i = 0; i < NPIX; i++) {
    const r = rgba[i*4], g = rgba[i*4+1], b = rgba[i*4+2], a = rgba[i*4+3];
    if (r !== g || g !== b) grey = false;
    if (a !== 255) { allOpaque = false; alphaVar = true; }
    const k = (r << 24) | (g << 16) | (b << 8) | a;
    const c = (freq.get(k) || 0) + 1; freq.set(k, c);
    if (a === 0) { transpCount++; if (transpKey === -1) transpKey = k; }
  }
  return { distinct: freq.size, freq, grey, alphaVar, allOpaque, transpKey, transpCount };
}
// Palette orderings. Returns list of {name, samples, palette: Uint8Array RGB, trns: Uint8Array|null}
function paletteForms(rgba, an) {
  const entries = [...an.freq.entries()].sort((a, b) => b[1] - a[1]);
  const cols = entries.map(([k]) => [(k >>> 24) & 255, (k >>> 16) & 255, (k >>> 8) & 255, k & 255]);
  const idxOf = new Map(entries.map(([k], i) => [k, i]));
  const lum = (c) => 0.299 * c[0] + 0.587 * c[1] + 0.114 * c[2];
  const orders = [];
  orders.push({ name: 'freq', order: entries.map((_, i) => i) });
  orders.push({ name: 'lum', order: entries.map((_, i) => i).sort((a, b) => lum(cols[a]) - lum(cols[b])) });
  // border-pinned: most frequent colour on the border first, then freq
  const borderFreq = new Map();
  for (let x = 0; x < W; x++) for (const y of [0, H - 1]) { const k = (rgba[(y*W+x)*4] << 24) | (rgba[(y*W+x)*4+1] << 16) | (rgba[(y*W+x)*4+2] << 8) | rgba[(y*W+x)*4+3]; borderFreq.set(k, (borderFreq.get(k) || 0) + 1); }
  for (let y = 0; y < H; y++) for (const x of [0, W - 1]) { const k = (rgba[(y*W+x)*4] << 24) | (rgba[(y*W+x)*4+1] << 16) | (rgba[(y*W+x)*4+2] << 8) | rgba[(y*W+x)*4+3]; borderFreq.set(k, (borderFreq.get(k) || 0) + 1); }
  let borderBest = -1, borderBestN = -1; for (const [k, n] of borderFreq) if (n > borderBestN) { borderBestN = n; borderBest = k; }
  const borderOrder = [idxOf.get(borderBest), ...entries.map((_, i) => i).filter((i) => i !== idxOf.get(borderBest))];
  orders.push({ name: 'border', order: borderOrder });
  // adjacency greedy: background (most frequent) at 0, then nearest neighbour by co-occurrence
  const adj = new Map(); // key a*n+b -> count (horizontal neighbours, sampled every pixel)
  const nC = cols.length;
  const pixIdx = new Uint8Array(NPIX);
  for (let i = 0; i < NPIX; i++) pixIdx[i] = idxOf.get((rgba[i*4] << 24) | (rgba[i*4+1] << 16) | (rgba[i*4+2] << 8) | rgba[i*4+3]);
  for (let y = 0; y < H; y++) for (let x = 0; x + 1 < W; x++) { const a = pixIdx[y*W+x], b = pixIdx[y*W+x+1]; if (a !== b) { const k = a * nC + b; adj.set(k, (adj.get(k) || 0) + 1); const k2 = b * nC + a; adj.set(k2, (adj.get(k2) || 0) + 1); } }
  const used = new Uint8Array(nC); const adjOrder = [0]; used[0] = 1;
  for (let t = 1; t < nC; t++) {
    const last = adjOrder[adjOrder.length - 1]; let bi = -1, bs = -1, bf = -1;
    for (let c = 0; c < nC; c++) if (!used[c]) { const s = adj.get(last * nC + c) || 0; if (s > bs || (s === bs && an.freq.get(entries[c][0]) > bf)) { bs = s; bf = an.freq.get(entries[c][0]); bi = c; } }
    adjOrder.push(bi); used[bi] = 1;
  }
  orders.push({ name: 'adj', order: adjOrder });
  const out = [];
  for (const { name, order } of orders) {
    const remap = new Uint8Array(nC); // old idx -> new idx
    order.forEach((oldI, newI) => { remap[oldI] = newI; });
    const samples = new Uint8Array(NPIX);
    for (let i = 0; i < NPIX; i++) samples[i] = remap[pixIdx[i]];
    const pal = new Uint8Array(nC * 3), trns = new Uint8Array(nC); let hasTrns = false;
    order.forEach((oldI, newI) => { const c = cols[oldI]; pal[newI*3] = c[0]; pal[newI*3+1] = c[1]; pal[newI*3+2] = c[2]; trns[newI] = c[3]; if (c[3] !== 255) hasTrns = true; });
    let trnsTrim = null;
    if (hasTrns) { let e = nC; while (e > 0 && trns[e - 1] === 255) e--; trnsTrim = trns.subarray(0, e); }
    out.push({ name: 'pal-' + name, samples, bpp: 1, ct: 3, pal, trns: trnsTrim, flat: true });
  }
  return out;
}
function otherForms(rgba, an) {
  const forms = [];
  if (an.grey) {
    const g = new Uint8Array(NPIX); for (let i = 0; i < NPIX; i++) g[i] = rgba[i * 4];
    if (an.allOpaque) forms.push({ name: 'grey', samples: g, bpp: 1, ct: 0, pal: null, trns: null, flat: false });
    else if (!an.alphaVar) forms.push({ name: 'grey', samples: g, bpp: 1, ct: 0, pal: null, trns: null, flat: false });
    else {
      // single transparent grey value -> type 0 + tRNS, else grey+alpha
      const transGreys = new Set();
      for (let i = 0; i < NPIX; i++) if (rgba[i*4+3] === 0) transGreys.add(rgba[i*4]);
      const alphas = new Set(); for (let i = 0; i < NPIX; i += 7) alphas.add(rgba[i*4+3]);
      if (transGreys.size === 1 && [...alphas].every((a) => a === 0 || a === 255)) {
        const tv = [...transGreys][0]; forms.push({ name: 'grey-key', samples: g, bpp: 1, ct: 0, pal: null, trns: new Uint8Array([0, tv]), flat: false });
      }
      const ga = new Uint8Array(NPIX * 2); for (let i = 0; i < NPIX; i++) { ga[i*2] = rgba[i*4]; ga[i*2+1] = rgba[i*4+3]; }
      forms.push({ name: 'greyalpha', samples: ga, bpp: 2, ct: 4, pal: null, trns: null, flat: false });
    }
  }
  if (an.allOpaque) {
    const rgb = new Uint8Array(NPIX * 3); for (let i = 0; i < NPIX; i++) { rgb[i*3] = rgba[i*4]; rgb[i*3+1] = rgba[i*4+1]; rgb[i*3+2] = rgba[i*4+2]; }
    forms.push({ name: 'rgb', samples: rgb, bpp: 3, ct: 2, pal: null, trns: null, flat: false });
  } else {
    // one transparent RGB colour, rest opaque -> RGB + tRNS key
    const transCols = new Set();
    for (let i = 0; i < NPIX; i++) if (rgba[i*4+3] === 0) transCols.add((rgba[i*4] << 16) | (rgba[i*4+1] << 8) | rgba[i*4+2]);
    let partial = false; for (let i = 0; i < NPIX; i += 3) if (rgba[i*4+3] !== 0 && rgba[i*4+3] !== 255) { partial = true; break; }
    if (transCols.size === 1 && !partial) {
      const tc = [...transCols][0];
      const rgb = new Uint8Array(NPIX * 3); for (let i = 0; i < NPIX; i++) { rgb[i*3] = rgba[i*4]; rgb[i*3+1] = rgba[i*4+1]; rgb[i*3+2] = rgba[i*4+2]; }
      forms.push({ name: 'rgb-key', samples: rgb, bpp: 3, ct: 2, pal: null, trns: new Uint8Array([0, (tc >> 16) & 255, 0, (tc >> 8) & 255, 0, tc & 255]), flat: false });
    }
  }
  forms.push({ name: 'rgba', samples: rgba, bpp: 4, ct: 6, pal: null, trns: null, flat: false });
  return forms;
}
// Brute-force per-row filter choice (zlib level 6, previous 32 KiB as dictionary)
function bruteForceSeq(samples, bpp) {
  const stride = W * bpp, seq = new Uint8Array(H);
  const out = new Uint8Array(H * (stride + 1));
  const trial = new Uint8Array(stride);
  for (let y = 0; y < H; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride), prev = y ? samples.subarray((y - 1) * stride, y * stride) : null;
    const dict = out.subarray(Math.max(0, y * (stride + 1) - 32768), y * (stride + 1));
    let bf = 0, bs = Infinity;
    for (let f = 0; f < 5; f++) {
      filterRow(f, cur, prev, bpp, trial);
      const row = new Uint8Array(stride + 1); row[0] = f; row.set(trial, 1);
      const c = deflateSync(row, { level: 6, dictionary: dict.length ? dict : undefined }).length;
      if (c < bs) { bs = c; bf = f; }
    }
    seq[y] = bf;
    out[y * (stride + 1)] = bf;
    filterRow(bf, cur, prev, bpp, out.subarray(y * (stride + 1) + 1, (y + 1) * (stride + 1)));
  }
  return seq;
}
// Choose best form + filter sequence for one image.
function chooseForm(rgba, an) {
  let forms = [];
  if (an.distinct <= 256) forms = forms.concat(paletteForms(rgba, an));
  forms = forms.concat(otherForms(rgba, an));
  // quick screen: filter-0 stream, zlib level 6
  const screened = [];
  for (const f of forms) {
    const s0 = buildFiltered(f.samples, f.bpp, constSeq(0));
    const z = deflateRawSync(s0, { level: 6 }).length + (f.pal ? f.pal.length : 0) + (f.trns ? f.trns.length : 0);
    screened.push({ f, z0: z });
  }
  screened.sort((a, b) => a.z0 - b.z0);
  // If the best form wins the screen by >10%, search only it: the second
  // form's full filter search costs ~40% of chooseForm and never wins then.
  const top = screened.length > 1 && screened[0].z0 < screened[1].z0 * 0.9 ? screened.slice(0, 1) : screened.slice(0, 2);
  let best = null;
  for (const { f } of top) {
    const { cost, filtered } = rowCosts(f.samples, f.bpp);
    const cands = [];
    const add = (name, seq) => cands.push({ name, seq });
    add('f0', constSeq(0)); add('f4', constSeq(4)); add('f2', constSeq(2));
    add('minsum', minsumSeq(cost));
    add('vit0', viterbi(cost, 0)); add('vit200', viterbi(cost, 200)); add('vit800', viterbi(cost, 800));
    add('band16', bandSeq(cost, 16)); add('band32', bandSeq(cost, 32));
    if (f.ct === 3) add('smartup', smartUp(f.samples));
    // palette/flat forms: only the candidates that ever win there (f0, smartup,
    // minsum, one Viterbi, one band) — the full set costs more than it saves.
    const useCands = f.ct === 3 ? cands.filter((c) => ['f0', 'smartup', 'minsum', 'vit0', 'band16'].includes(c.name)) : cands;
    // rank ALL candidates by true level-1 compression; level-1 mis-ranks
    // run-heavy streams, so the finalists (top 3 by level 1 PLUS f0 and
    // minsum, always) are re-ranked by level 6, a much better proxy for level 9.
    const ranked = [];
    for (const c of useCands) {
      const stream = buildFromCache(filtered, c.seq);
      ranked.push({ c, stream, z1: deflateRawSync(stream, { level: 1 }).length });
    }
    ranked.sort((a, b) => a.z1 - b.z1);
    const fin = [];
    const seen = new Set();
    for (const r of ranked.slice(0, 3)) { fin.push(r); seen.add(r.c.name); }
    for (const r of ranked) if (r.c.name === 'f0' && !seen.has(r.c.name)) { fin.push(r); seen.add(r.c.name); }
    for (const { c, stream } of fin) {
      const z = deflateRawSync(stream, { level: 6 }).length;
      const tot = z + (f.pal ? f.pal.length : 0) + (f.trns ? f.trns.length : 0) + 12;
      if (!best || tot < best.tot) best = { form: f, name: c.name, seq: c.seq, stream, tot, z6: z };
    }
    // keep this form's cache for the brute-force step if it wins
    if (best && best.form === f) best.filtered = filtered;
  }
  // brute force on the winning form (skipped for palette: SmartUp/filter-0 win there);
  // keep it only if it wins at level 6
  if (best.form.ct !== 3) {
    const bfSeq = bruteForceSeq(best.form.samples, best.form.bpp);
    const bfStream = buildFiltered(best.form.samples, best.form.bpp, bfSeq);
    const bfZ6 = deflateRawSync(bfStream, { level: 6 }).length;
    if (bfZ6 < best.z6) best = { form: best.form, name: 'brute', seq: bfSeq, stream: bfStream, tot: bfZ6, z6: bfZ6 };
  }
  return best;
}
function writePng(form, deflateRaw) {
  const chunks = [chunk('IHDR', ihdr(form.ct))];
  if (form.pal) chunks.push(chunk('PLTE', form.pal));
  if (form.trns) chunks.push(chunk('tRNS', form.trns));
  const zl = new Uint8Array(2 + deflateRaw.length + 4);
  zl[0] = 0x78; zl[1] = 0x9c; zl.set(deflateRaw, 2);
  new DataView(zl.buffer).setUint32(2 + deflateRaw.length, adler32(form.streamForAdler));
  chunks.push(chunk('IDAT', zl));
  chunks.push(chunk('IEND', new Uint8Array(0)));
  return pngOf(chunks);
}
function processImage(id) {
  const rgba = decodePng(new Uint8Array(readFileSync(join(IN_DIR, id, 'image.png'))));
  const an = analyze(rgba);
  const best = chooseForm(rgba, an);
  const rowStride = W * best.form.bpp + 1;
  const r = customDeflate(best.stream, rowStride, best.form.flat);
  const useCustom = !r.skipped && r.customBytes <= r.libBytes;
  const deflateRaw = useCustom ? r.raw : deflateRawSync(best.stream, { level: 9 });
  best.form.streamForAdler = best.stream;
  const png = writePng(best.form, deflateRaw);
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'image.png'), png);
  const overhead = png.length - deflateRaw.length - 6; // chunks + zlib wrapper beyond raw deflate
  void overhead;
  const rep = { id, form: best.form.name, filter: best.name, custom: r.skipped ? ('sampled ' + r.sampleCustom + '/' + r.sampleLib) : r.customBytes, lib: r.libBytes, chosen: useCustom ? 'custom' : 'lib', bytes: png.length, blocks: r.blocks, visitsPerPos: (r.visits / Math.max(1, r.positions)).toFixed(2) };
  console.error(JSON.stringify(rep));
  return rep;
}
function main() {
  const ids = readdirSync(IN_DIR).sort().filter((d) => /^i\d{3}$/.test(d));
  const reps = [];
  for (const id of ids) reps.push(processImage(id));
  return reps;
}
// ---- Tree-finder diagnostic (node main.ts --diag) ----
function diag() {
  const ids = readdirSync(IN_DIR).sort().filter((d) => /^i\d{3}$/.test(d));
  let totMiss = 0, totSamp = 0, totVisits = 0;
  for (const id of ids) {
    const rgba = decodePng(new Uint8Array(readFileSync(join(IN_DIR, id, 'image.png'))));
    const an = analyze(rgba);
    const best = chooseForm(rgba, an);
    const stream = best.stream, rowStride = W * best.form.bpp + 1;
    const n = stream.length;
    // sampled positions: every ~n/50 plus positions inside long runs
    const samp = new Set();
    for (let i = 0; i < 60; i++) samp.add(Math.floor((i + 0.5) * n / 60));
    for (let i = 100; i < n - 300; i += 9973) { // run interiors
      if (stream[i] === stream[i - 1] && stream[i] === stream[i + 1]) samp.add(i);
    }
    const positions = [...samp].filter((p) => p + 32 < n).sort((a, b) => a - b);
    const finder = new Finder(stream, 128, 258, rowStride);
    let miss = 0, visits = 0, checked = 0;
    const sampSet = new Set(positions);
    for (let p = 0; p < n; p++) {
      if (!sampSet.has(p)) { finder.insert(p); continue; }
      // brute force: best match length in previous 32768 bytes
      let brute = 0;
      const lo = Math.max(0, p - 32768);
      for (let q = lo; q < p; q++) {
        if (stream[q] !== stream[p] || stream[q + 1] !== stream[p + 1] || stream[q + 2] !== stream[p + 2]) continue;
        let l = 3; while (l < 258 && p + l < n && stream[q + l] === stream[p + l]) l++;
        if (l > brute) brute = l;
        if (brute >= 258) break;
      }
      const before = finder.visits;
      const rn = finder.find(p);
      visits += finder.visits - before;
      if (brute < 32) continue;
      checked++;
      const treeBest = rn ? finder.scr[0] >>> 15 : 0;
      if (treeBest < brute - 3) miss++;
    }
    totMiss += miss; totSamp += checked; totVisits += visits;
    console.error(JSON.stringify({ id, form: best.form.name, filter: best.name, sampled: checked, miss, missRate: checked ? (miss / checked).toFixed(4) : 'n/a', avgVisits: checked ? (visits / checked).toFixed(1) : 'n/a' }));
  }
  console.error(JSON.stringify({ totalSampled: totSamp, totalMiss: totMiss, overallMissRate: totSamp ? (totMiss / totSamp).toFixed(4) : 'n/a', avgVisits: totSamp ? (totVisits / totSamp).toFixed(1) : 'n/a' }));
}
if (NODE === 'diag') diag(); else main();
