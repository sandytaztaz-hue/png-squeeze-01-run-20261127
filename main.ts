// PNG squeeze R10: forms + filter contest + custom DEFLATE (dual-index tree finder,
// optimal-parse DP with cost-table refinement, package-merge Huffman).
// Written from the R5-R10 briefs alone. Deterministic: fixed budgets, no clock/random.
import { readFileSync, writeFileSync, mkdirSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { inflateSync, deflateSync } from 'node:zlib';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DIAG = false;
const W = 1280, H = 720, N = W * H;
const ITERS_FLAT = 12, ITERS_RICH = 12, DEPTH_FLAT = 48, DEPTH_RICH = 32;

const CRC = (() => { const t = new Int32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; t[n] = c; } return t; })();
function crc32(b: Uint8Array, s: number, e: number): number { let c = -1; for (let i = s; i < e; i++) c = CRC[(c ^ b[i]) & 255] ^ (c >>> 8); return (c ^ -1) >>> 0; }
function adler32(b: Uint8Array): number { let a = 1, c = 0; for (let i = 0; i < b.length;) { const end = Math.min(b.length, i + 5552); for (; i < end; i++) { a += b[i]; c += a; } a %= 65521; c %= 65521; } return ((c << 16) | a) >>> 0; }
function chunk(type: string, data: Uint8Array): Uint8Array {
  const out = new Uint8Array(12 + data.length); const v = new DataView(out.buffer);
  v.setUint32(0, data.length);
  for (let i = 0; i < 4; i++) out[4 + i] = type.charCodeAt(i);
  out.set(data, 8); v.setUint32(8 + data.length, crc32(out, 4, 8 + data.length)); return out;
}
function ihdr(ct: number): Uint8Array { const d = new Uint8Array(13); const v = new DataView(d.buffer); v.setUint32(0, W); v.setUint32(4, H); d[8] = 8; d[9] = ct; return d; }
function pngOf(parts: Uint8Array[]): Uint8Array {
  const sig = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
  let sz = sig.length; for (const p of parts) sz += p.length;
  const out = new Uint8Array(sz); out.set(sig); let at = sig.length;
  for (const p of parts) { out.set(p, at); at += p.length; } return out;
}
function paeth(a: number, b: number, c: number): number { const p = a + b - c; const pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c); if (pa <= pb && pa <= pc) return a; return pb <= pc ? b : c; }

function decode(buf: Uint8Array): Uint8Array {
  const view = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
  let at = 8; const idat: Uint8Array[] = []; let ct = 6;
  while (at < buf.length) {
    const len = view.getUint32(at); const type = String.fromCharCode(buf[at + 4], buf[at + 5], buf[at + 6], buf[at + 7]);
    const data = buf.subarray(at + 8, at + 8 + len); at += 12 + len;
    if (type === 'IHDR') ct = data[9];
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
  }
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat));
  const bpp = ct === 6 ? 4 : ct === 2 ? 3 : ct === 0 ? 1 : ct === 4 ? 2 : 1;
  const stride = W * bpp; const samples = new Uint8Array(N * bpp);
  for (let y = 0; y < H; y++) {
    const ft = raw[y * (stride + 1)]; const src = y * (stride + 1) + 1; const o = y * stride; const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) { for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0); }
    else if (ft === 2) { for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0); }
    else if (ft === 3) { for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1); }
    else { for (let i = 0; i < stride; i++) { const a = i >= bpp ? samples[o + i - bpp] : 0; const b = y > 0 ? samples[p + i] : 0; const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0; samples[o + i] = raw[src + i] + paeth(a, b, c); } }
  }
  if (ct === 6) return samples;
  const rgba = new Uint8Array(N * 4);
  if (ct === 2) { for (let i = 0, s = 0, d = 0; i < N; i++, s += 3, d += 4) { rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2]; rgba[d + 3] = 255; } }
  else if (ct === 0) { for (let i = 0, d = 0; i < N; i++, d += 4) { const g = samples[i]; rgba[d] = rgba[d + 1] = rgba[d + 2] = g; rgba[d + 3] = 255; } }
  else { for (let i = 0, s = 0, d = 0; i < N; i++, s += 2, d += 4) { const g = samples[s]; rgba[d] = rgba[d + 1] = rgba[d + 2] = g; rgba[d + 3] = samples[s + 1]; } }
  return rgba;
}

function filterRow(type: number, cur: Uint8Array, prev: Uint8Array | null, bpp: number, out: Uint8Array): void {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) { for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0); }
  else if (type === 2) { for (let i = 0; i < n; i++) out[i] = cur[i] - (prev ? prev[i] : 0); }
  else if (type === 3) { for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev ? prev[i] : 0)) >> 1); }
  else { for (let i = 0; i < n; i++) { const a = i >= bpp ? cur[i - bpp] : 0; const b = prev ? prev[i] : 0; const c = prev && i >= bpp ? prev[i - bpp] : 0; out[i] = cur[i] - paeth(a, b, c); } }
}
function signedSum(row: Uint8Array): number { let s = 0; for (let i = 0; i < row.length; i++) { const v = row[i]; s += v < 128 ? v : 256 - v; } return s; }

// ---------- DEFLATE tables ----------
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const LEN_SYM = new Int32Array(259); const LEN_EB = new Int32Array(259); const LEN_B = new Int32Array(259);
for (let s = 0; s < 29; s++) { const lo = LEN_BASE[s]; const hi = s === 28 ? 258 : LEN_BASE[s + 1] - 1; for (let l = lo; l <= hi; l++) { LEN_SYM[l] = 257 + s; LEN_EB[l] = LEN_EXTRA[s]; LEN_B[l] = lo; } }
const DIST_SYM = new Int32Array(32769); const DIST_EB = new Int32Array(32769); const DIST_B = new Int32Array(32769);
for (let s = 0; s < 30; s++) { const lo = DIST_BASE[s]; const hi = s === 29 ? 32768 : DIST_BASE[s + 1] - 1; for (let d = lo; d <= hi; d++) { DIST_SYM[d] = s; DIST_EB[d] = DIST_EXTRA[s]; DIST_B[d] = lo; } }
// length-code range starts (for sublen expansion)
const LEN_RANGE_START = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227];
// bit-reverse table for 15 bits
const REV15 = new Uint16Array(32768);
for (let i = 0; i < 32768; i++) { let r = 0, x = i; for (let k = 0; k < 15; k++) { r = (r << 1) | (x & 1); x >>= 1; } REV15[i] = r; }

// ---------- Huffman lengths: heap Huffman + length limit with exact Kraft fix ----------
function buildLengths(freq: Int32Array, maxLen: number): Int32Array | null {
  const n = freq.length;
  let used = 0; let onlySym = -1;
  for (let i = 0; i < n; i++) if (freq[i] > 0) { used++; onlySym = i; }
  if (used === 0) return new Int32Array(n);
  if (used === 1) { const l = new Int32Array(n); l[onlySym] = 1; return l; }
  // heap of nodes: [weight, sym(-1 internal), left, right] in arrays
  const w: number[] = []; const sym: number[] = []; const left: number[] = []; const right: number[] = [];
  const heap: number[] = [];
  const push = (id: number) => { heap.push(id); let i = heap.length - 1; while (i > 0) { const p = (i - 1) >> 1; if (w[heap[p]] <= w[heap[i]]) break; const t = heap[p]; heap[p] = heap[i]; heap[i] = t; i = p; } };
  const pop = (): number => { const top = heap[0]; const last = heap.pop()!; if (heap.length) { heap[0] = last; let i = 0; for (;;) { const l = i * 2 + 1, r = l + 1; let m = i; if (l < heap.length && w[heap[l]] < w[heap[m]]) m = l; if (r < heap.length && w[heap[r]] < w[heap[m]]) m = r; if (m === i) break; const t = heap[m]; heap[m] = heap[i]; heap[i] = t; i = m; } } return top; };
  for (let i = 0; i < n; i++) if (freq[i] > 0) { const id = w.length; w.push(freq[i]); sym.push(i); left.push(-1); right.push(-1); push(id); }
  while (heap.length > 1) {
    const a = pop(); const b = pop();
    const id = w.length; w.push(w[a] + w[b]); sym.push(-1); left.push(a); right.push(b); push(id);
  }
  const root = heap[0];
  const len = new Int32Array(n);
  const stack: number[] = [root]; const dstack: number[] = [0];
  while (stack.length) { const id = stack.pop()!; const d = dstack.pop()!; if (sym[id] >= 0) len[sym[id]] = d; else { stack.push(left[id]); dstack.push(d + 1); stack.push(right[id]); dstack.push(d + 1); } }
  let mx = 0; for (let i = 0; i < n; i++) if (len[i] > mx) mx = len[i];
  if (mx <= maxLen) {
    // Kraft must be exactly 2^maxLen units for completeness (heap Huffman is complete)
    return len;
  }
  // cap + fix: work in units of 2^-maxLen
  const full = 1 << maxLen;
  for (let i = 0; i < n; i++) if (len[i] > maxLen) len[i] = maxLen;
  let sum = 0; for (let i = 0; i < n; i++) if (len[i] > 0) sum += 1 << (maxLen - len[i]);
  let guard = 0;
  while (sum > full && guard++ < 100000) {
    const need = sum - full;
    // lengthen the rarest symbol whose step fits, else the one with the smallest step
    let best = -1, bestF = Infinity, bestStep = Infinity;
    for (let i = 0; i < n; i++) if (len[i] > 0 && len[i] < maxLen) {
      const step = 1 << (maxLen - len[i] - 1);
      if (step <= need && freq[i] < bestF) { bestF = freq[i]; best = i; bestStep = step; }
    }
    if (best < 0) {
      for (let i = 0; i < n; i++) if (len[i] > 0 && len[i] < maxLen) { const step = 1 << (maxLen - len[i] - 1); if (step < bestStep) { bestStep = step; best = i; } }
    }
    if (best < 0) break;
    sum -= bestStep; len[best]++;
  }
  guard = 0;
  while (sum < full && guard++ < 100000) {
    const need = full - sum;
    // shorten the most frequent symbol whose add fits exactly
    let best = -1, bestF = -1, bestAdd = 0;
    for (let i = 0; i < n; i++) if (len[i] > 1) {
      const add = 1 << (maxLen - len[i]);
      if (add <= need && freq[i] > bestF) { bestF = freq[i]; best = i; bestAdd = add; }
    }
    if (best < 0) break;
    sum += bestAdd; len[best]--;
  }
  if (sum !== full) return null;
  return len;
}
function kraftOk(len: Int32Array, maxLen: number): boolean {
  let sum = 0; let used = 0;
  for (let i = 0; i < len.length; i++) if (len[i] > 0) { used++; sum += 1 << (maxLen - len[i]); }
  if (used === 1) return len.some ? true : true; // single symbol: length 1 accepted by inflate
  return sum === (1 << maxLen);
}
function canonicalCodes(len: Int32Array): { code: Int32Array; } {
  const maxL = Math.max(0, ...len);
  const blCount = new Int32Array(maxL + 1);
  for (let i = 0; i < len.length; i++) if (len[i] > 0) blCount[len[i]]++;
  const code = new Int32Array(len.length);
  let next = 0;
  const nextCode = new Int32Array(maxL + 1);
  for (let b = 1; b <= maxL; b++) { next = (next + blCount[b - 1]) << 1; nextCode[b] = next; }
  for (let i = 0; i < len.length; i++) if (len[i] > 0) code[i] = nextCode[len[i]]++;
  return { code };
}

// ---------- Bit writer (single shared writer across blocks) ----------
class BitWriter {
  buf: number[] = []; bitbuf = 0; bitcnt = 0;
  write(v: number, n: number): void {
    this.bitbuf |= (v & ((1 << n) - 1)) << this.bitcnt; this.bitcnt += n;
    while (this.bitcnt >= 8) { this.buf.push(this.bitbuf & 255); this.bitbuf >>>= 8; this.bitcnt -= 8; }
  }
  // write a Huffman code (value `code` of `n` bits, MSB first into the stream)
  writeCode(code: number, n: number): void {
    const rev = REV15[code] >> (15 - n); // bit-reverse the n-bit code so MSB goes first
    this.write(rev, n);
  }
  finish(): Uint8Array {
    if (this.bitcnt > 0) { this.buf.push(this.bitbuf & 255); this.bitbuf = 0; this.bitcnt = 0; }
    return Uint8Array.from(this.buf);
  }
}

// ---------- Match finder: 3-byte hash tree (binary search tree per hash bucket) ----------
// Every position is inserted into the 3-byte-prefix tree (primary index). Run-keyed
// records are a supplementary fast path only; the tree walk is what the parse trusts.
interface Finder { candLen: Uint16Array; candDist: Uint16Array; candCnt: Uint8Array; bestLen: Uint16Array; visits: number; positions: number; }
const KCAND = 4;
function matchLen(d: Uint8Array, a: number, b: number, limit: number): number {
  const max = Math.min(limit, d.length - b);
  let i = 0;
  while (i < max && d[a + i] === d[b + i]) i++;
  return i;
}
// Match length, but only pay the full compare when the match can beat `best`:
// if it cannot, the returned length is exact and <= best.
function matchLenBest(d: Uint8Array, a: number, b: number, limit: number, best: number): number {
  const max = Math.min(limit, d.length - b);
  const cap = Math.min(max, best + 1);
  let i = 0;
  while (i < cap && d[a + i] === d[b + i]) i++;
  if (i < cap || cap >= max) return i;
  while (i < max && d[a + i] === d[b + i]) i++;
  return i;
}
function buildFinder(data: Uint8Array, rowStride: number, maxDepth: number, period: number): Finder {
  const n = data.length;
  const runLen = new Uint16Array(n + 1);
  for (let i = n - 1; i >= 0; i--) runLen[i] = data[i] === data[i + 1] ? Math.min(runLen[i + 1] + 1, 520) : 1;
  // pixel-period run: q[i] = length of the run repeating with the pixel period
  // (data[i+k] == data[i+k-period] for k = 0..q[i]-1), capped at 520
  const perRun = new Uint16Array(n + 1);
  if (period > 1) {
    for (let i = n - 1; i >= 0; i--) perRun[i] = i >= period && data[i] === data[i - period] ? Math.min(perRun[i + 1] + 1, 520) : 0;
  }
  const candLen = new Uint16Array(n * KCAND); const candDist = new Uint16Array(n * KCAND);
  const candCnt = new Uint8Array(n); const bestLen = new Uint16Array(n);
  // BST per 3-byte hash: root[65536], left/right child slots per position (pre-allocated).
  const root = new Int32Array(65536).fill(-1);
  const left = new Int32Array(n).fill(-1); const right = new Int32Array(n).fill(-1);
  // Recency chain per 3-byte hash (head/prev): the BST alone degenerates on periodic
  // data (equal suffixes form a position-ordered chain whose nodes fall out of the
  // 32K window), so the chain guarantees the nearest occurrences stay reachable.
  const head = new Int32Array(65536).fill(-1);
  const prev = new Int32Array(n).fill(-1);
  const bstDepth = Math.max(8, maxDepth >> 1);
  let visits = 0;
  const tmpLen = new Int32Array(8); const tmpDist = new Int32Array(8);
  for (let i = 0; i < n; i++) {
    const rl = runLen[i];
    let tc = 0;
    // add() keeps tmpLen/tmpDist sorted by length desc (distance asc within a
    // length), so the Pareto scan below is linear and no sort pass is needed.
    const add = (len: number, dist: number) => {
      if (len < 3 || dist <= 0 || dist > 32768 || dist > i) return;
      let p = 0;
      while (p < tc && tmpLen[p] > len) p++;
      if (p < tc && tmpLen[p] === len) { if (tmpDist[p] > dist) tmpDist[p] = dist; return; }
      if (tc < 8) {
        for (let k = tc; k > p; k--) { tmpLen[k] = tmpLen[k - 1]; tmpDist[k] = tmpDist[k - 1]; }
        tmpLen[p] = len; tmpDist[p] = dist; tc++;
      } else if (p < 8) {
        for (let k = 7; k > p; k--) { tmpLen[k] = tmpLen[k - 1]; tmpDist[k] = tmpDist[k - 1]; }
        tmpLen[p] = len; tmpDist[p] = dist;
      }
    };
    // run-length fast path: must return the FULL run length (up to 258) before any early break.
    // A distance-1 match copies the byte BEFORE the match first, so it is only
    // valid when data[i] == data[i-1] (inside a run, not at its start); at a run
    // start the run's bytes cannot be produced from the previous (different) byte.
    const runOk = i > 0 && data[i] === data[i - 1];
    const rlV = runOk ? rl : 0;
    if (rl >= 3 && runOk) add(Math.min(rl, 258), 1);
    let bestSoFar = rl >= 3 && runOk ? Math.min(rl, 258) : 0;
    // pixel-period fast path: a repeated pixel gives a match at distance = period
    const pr = period > 1 ? perRun[i] : 0;
    if (pr >= 3) { add(Math.min(pr, 258), period); if (Math.min(pr, 258) > bestSoFar) bestSoFar = Math.min(pr, 258); }
    // row-above probe (one scanline above; the two-scanline probe cost more
    // CPU than the bytes it ever won)
    if (rowStride > 0) {
      for (let k = 1; k <= 1; k++) { const p = i - k * rowStride; if (p >= 0) { const ml = matchLenBest(data, p, i, 258, bestSoFar); if (ml >= 3) { add(ml, k * rowStride); if (ml > bestSoFar) bestSoFar = ml; } } }
    }
    // hash + walks, unless a long run (byte run or pixel-period run) already dominates.
    // (A 258 match from the row above must NOT skip the walks: a nearer shorter
    // match can still be cheaper for the DP, so only byte/period runs skip.)
    let insNode = -1, insCmp = 1;
    const h = i + 3 <= n ? ((((data[i] << 16) ^ (data[i + 1] << 8) ^ data[i + 2]) * 2654435761) >>> 16 & 65535) : -1;
    if (rlV < 16 && pr < 16 && i + 3 <= n) {
      // recency chain walk (nearest occurrences first; break on out-of-window: prev is older)
      {
        let node = head[h]; let depth = 0; let best = 0;
        while (node >= 0 && depth < maxDepth) {
          visits++; depth++;
          const d = i - node;
          if (d > 32768) break;
          const ml = matchLenBest(data, node, i, 258, Math.max(best, bestSoFar));
          if (ml >= 3) { add(ml, d); if (ml > bestSoFar) bestSoFar = ml; }
          if (ml > best) best = ml;
          if (best >= 258) break; // nearest 258 cannot be beaten
          node = prev[node];
        }
      }
      // tree walk (diverse suffixes); out-of-window nodes are skipped, not a break:
      // their children were inserted later and are nearer.
      {
        let node = root[h]; let depth = 0; let best = 0;
        while (node >= 0 && depth < bstDepth) {
          visits++; depth++;
          const d = i - node;
          let ml = -1;
          if (d <= 32768) {
            ml = matchLenBest(data, node, i, 258, Math.max(best, bestSoFar));
            if (ml >= 3) { add(ml, d); if (ml > bestSoFar) bestSoFar = ml; }
            if (ml > best) best = ml;
            if (best >= 258) { insNode = node; insCmp = 1; break; }
          }
          // walk direction from the first differing byte (ml is its offset when known)
          const lim = Math.min(258, n - i, n - node);
          let cmp: number;
          if (ml >= 0) { if (ml >= lim) cmp = 1; else cmp = data[i + ml] < data[node + ml] ? -1 : 1; }
          else { let j = 0; while (j < lim && data[node + j] === data[i + j]) j++; if (j >= lim) cmp = 1; else cmp = data[i + j] < data[node + j] ? -1 : 1; }
          insNode = node; insCmp = cmp;
          node = cmp < 0 ? left[node] : right[node];
        }
      }
    }
    // keep Pareto candidates: tmp is already sorted by length desc (add() maintains
    // it), so this is a single linear scan keeping a new minimum distance each time
    let kept = 0; let minDist = 1 << 30;
    for (let k = 0; k < tc && kept < KCAND; k++) {
      if (tmpDist[k] >= minDist && k > 0) continue; // dominated: shorter and not nearer
      candLen[i * KCAND + kept] = tmpLen[k]; candDist[i * KCAND + kept] = tmpDist[k]; kept++;
      if (tmpDist[k] < minDist) minDist = tmpDist[k];
    }
    candCnt[i] = kept;
    bestLen[i] = kept > 0 ? candLen[i * KCAND] : 0;
    // insert into both indexes (chain: every position, O(1); tree: search-path insert,
    // skipping positions inside long runs — their suffix is the run's suffix).
    if (i + 3 <= n) {
      prev[i] = head[h]; head[h] = i;
      if (rlV < 8) {
        if (root[h] < 0) { root[h] = i; }
        else if (insNode >= 0) {
          if (insCmp < 0) { if (left[insNode] < 0) left[insNode] = i; }
          else { if (right[insNode] < 0) right[insNode] = i; }
        }
      }
    }
  }
  return { candLen, candDist, candCnt, bestLen, visits, positions: n };
}

// ---------- Optimal parse (shortest path DP, cost-table refinement) ----------
const FIX_LIT_LEN = new Int32Array(286); const FIX_DIST_LEN = new Int32Array(30);
for (let i = 0; i < 286; i++) FIX_LIT_LEN[i] = i < 144 ? 8 : i < 256 ? 9 : i < 280 ? 7 : 8;
for (let i = 0; i < 30; i++) FIX_DIST_LEN[i] = 5;
const FIX_LIT_CODE = new Int32Array(286);
for (let i = 0; i < 286; i++) FIX_LIT_CODE[i] = i < 144 ? 0x30 + i : i < 256 ? 0x190 + i - 144 : i < 280 ? i - 256 : 0xc0 + i - 280;

interface BlockResult { tokSym: Int32Array; tokDist: Int32Array; tokLen: Int32Array; ntok: number; dynBits: number; fixBits: number; litLen: Int32Array; distLen: Int32Array; useDyn: boolean; }
function parseBlock(data: Uint8Array, finder: Finder, bs: number, be: number, iters: number, maxCand: number): BlockResult {
  const m = be - bs;
  const dp = new Float64Array(m + 1);
  const choiceLen = new Int32Array(m + 1); const choiceDist = new Int32Array(m + 1);
  const litC = new Float64Array(286); const distC = new Float64Array(30);
  for (let i = 0; i < 286; i++) litC[i] = FIX_LIT_LEN[i];
  for (let i = 0; i < 30; i++) distC[i] = 5;
  const lenCost = new Float64Array(259); const distCost = new Float64Array(32769);
  // token buffers (reused across iterations; best is copied out)
  const tSym = new Int32Array(m + 1); const tDist = new Int32Array(m + 1); const tLen = new Int32Array(m + 1);
  let best: BlockResult | null = null;
  let lcg = 0x12345678;
  const nextRand = () => { lcg = (lcg * 1103515245 + 12345) & 0x7fffffff; return lcg / 0x7fffffff; };
  for (let iter = 0; iter < iters; iter++) {
    for (let l = 3; l <= 258; l++) lenCost[l] = litC[LEN_SYM[l]] + LEN_EB[l];
    for (let d = 1; d <= 32768; d++) distCost[d] = distC[DIST_SYM[d]] + DIST_EB[d];
    dp[m] = 0; choiceLen[m] = 0; choiceDist[m] = 0;
    for (let i = m - 1; i >= 0; i--) {
      const pos = bs + i;
      let bestCost = dp[i + 1] + litC[data[pos]];
      let bl = 0, bd = 0;
      const cnt = finder.candCnt[pos] < maxCand ? finder.candCnt[pos] : maxCand;
      const base = pos * KCAND;
      for (let c = 0; c < cnt; c++) {
        const L = finder.candLen[base + c]; const D = finder.candDist[base + c];
        if (D > pos || D > 32768) continue;
        const dc = distCost[D];
        // try L, then the range start of L's length code (landing on a cheap
        // length code is the sublen value; the length-3 trial is dropped: the
        // DP already searches matches at every interior position)
        const rs = LEN_RANGE_START[LEN_SYM[L] - 257];
        const l0 = L; const l1 = rs;
        if (l0 >= 3 && i + l0 <= m) { const cost = dp[i + l0] + lenCost[l0] + dc; if (cost < bestCost) { bestCost = cost; bl = l0; bd = D; } }
        if (l1 !== l0 && l1 >= 3 && i + l1 <= m) { const cost = dp[i + l1] + lenCost[l1] + dc; if (cost < bestCost) { bestCost = cost; bl = l1; bd = D; } }
      }
      dp[i] = bestCost; choiceLen[i] = bl; choiceDist[i] = bd;
    }
    // extract tokens + frequencies
    const litFreq = new Int32Array(286); const distFreq = new Int32Array(30);
    let ntok = 0; let i = 0;
    while (i < m) {
      const pos = bs + i;
      if (choiceLen[i] === 0) { tSym[ntok] = data[pos]; tDist[ntok] = 0; tLen[ntok] = 0; litFreq[data[pos]]++; ntok++; i++; }
      else { const L = choiceLen[i]; const D = choiceDist[i]; const s = LEN_SYM[L]; tSym[ntok] = s; tDist[ntok] = D; tLen[ntok] = L; litFreq[s]++; distFreq[DIST_SYM[D]]++; ntok++; i += L; }
    }
    litFreq[256]++; // end-of-block
    const litLen = buildLengths(litFreq, 15); const distLen = buildLengths(distFreq, 7);
    const litLenU = litLen ?? FIX_LIT_LEN; const distLenU = distLen ?? FIX_DIST_LEN;
    // exact token bits under dynamic and fixed trees
    let dynBits = 0, fixBits = 0;
    for (let k = 0; k < ntok; k++) {
      if (tLen[k] === 0) { dynBits += litLenU[tSym[k]]; fixBits += FIX_LIT_LEN[tSym[k]]; }
      else { const s = tSym[k]; dynBits += litLenU[s] + LEN_EB[tLen[k]] + distLenU[DIST_SYM[tDist[k]]] + DIST_EB[tDist[k]]; fixBits += FIX_LIT_LEN[s] + LEN_EB[tLen[k]] + 5 + DIST_EB[tDist[k]]; }
    }
    dynBits += litLenU[256]; fixBits += 7;
    const hb = headerBits(litLenU, distLenU);
    const totalDyn = (litLen && distLen && hb !== Infinity) ? dynBits + hb : Infinity;
    const total = Math.min(totalDyn, fixBits);
    if (!best || total < Math.min(best.dynBits, best.fixBits)) {
      best = {
        tokSym: tSym.slice(0, ntok), tokDist: tDist.slice(0, ntok), tokLen: tLen.slice(0, ntok), ntok,
        dynBits: totalDyn, fixBits, litLen: litLenU.slice(), distLen: distLenU.slice(),
        useDyn: totalDyn <= fixBits,
      };
    }
    if (iter === iters - 1) break;
    // re-derive costs; damped on every 3rd iteration; one deterministic perturbation late
    const damped = iter % 3 === 2;
    for (let s = 0; s < 286; s++) {
      const target = litLenU[s] > 0 ? litLenU[s] : (s < 256 ? 9 : 15);
      litC[s] = damped ? (litC[s] + target) / 2 : target;
    }
    for (let s = 0; s < 30; s++) {
      const target = distLenU[s] > 0 ? distLenU[s] : 15;
      distC[s] = damped ? (distC[s] + target) / 2 : target;
    }
    if ((iter === iters - 2 || iter === 5) && iters >= 6) {
      const mag = iter === iters - 2 ? 0.05 : 0.10;
      for (let s = 0; s < 286; s++) if (litFreq[s] > 0) litC[s] *= 1 + (nextRand() - 0.5) * 2 * mag;
      for (let s = 0; s < 30; s++) if (distFreq[s] > 0) distC[s] *= 1 + (nextRand() - 0.5) * 2 * mag;
    }
  }
  return best!;
}

// ---------- Dynamic header: RLE + code-length code ----------
const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
function rleOf(litLen: Int32Array, distLen: Int32Array, litCount: number, distCount: number): { sym: Int32Array; extra: Int32Array; ebits: Int32Array; clFreq: Int32Array; } {
  const arr = new Int32Array(litCount + distCount);
  arr.set(litLen.subarray(0, litCount)); arr.set(distLen.subarray(0, distCount), litCount);
  const sym: number[] = []; const extra: number[] = []; const ebits: number[] = []; const clFreq = new Int32Array(19);
  const push = (s: number, e: number, b: number) => { sym.push(s); extra.push(e); ebits.push(b); clFreq[s]++; };
  let i = 0;
  while (i < arr.length) {
    const v = arr[i];
    if (v === 0) {
      let j = i; while (j < arr.length && arr[j] === 0) j++;
      let run = j - i;
      while (run >= 11) { const t = Math.min(run, 138); push(18, t - 11, 7); run -= t; }
      if (run >= 3) { push(17, run - 3, 3); run = 0; }
      while (run > 0) { push(0, 0, 0); run--; }
      i = j;
    } else {
      push(v, 0, 0);
      let j = i + 1; while (j < arr.length && arr[j] === v) j++;
      let run = j - i - 1;
      while (run >= 3) { const t = Math.min(run, 6); push(16, t - 3, 2); run -= t; }
      while (run > 0) { push(v, 0, 0); run--; }
      i = j;
    }
  }
  return { sym: Int32Array.from(sym), extra: Int32Array.from(extra), ebits: Int32Array.from(ebits), clFreq };
}
function trimCounts(litLen: Int32Array, distLen: Int32Array): { litCount: number; distCount: number; } {
  let litCount = 286; while (litCount > 257 && litLen[litCount - 1] === 0) litCount--;
  let distCount = 30; while (distCount > 1 && distLen[distCount - 1] === 0) distCount--;
  return { litCount, distCount };
}
function headerBits(litLen: Int32Array, distLen: Int32Array): number {
  const { litCount, distCount } = trimCounts(litLen, distLen);
  const r = rleOf(litLen, distLen, litCount, distCount);
  const clLen = buildLengths(r.clFreq, 7);
  if (!clLen) return Infinity;
  let clCount = 19; while (clCount > 4 && clLen[CL_ORDER[clCount - 1]] === 0) clCount--;
  let bits = 3 + 5 + 5 + 4 + 3 * clCount;
  for (let k = 0; k < r.sym.length; k++) bits += clLen[r.sym[k]] + r.ebits[k];
  return bits;
}
function emitBlock(bw: BitWriter, blk: BlockResult, isLast: boolean, kraftFail: { n: number }): void {
  // a dynamic block whose code-length code cannot be built must fall back to fixed
  if (blk.useDyn) {
    const tc = trimCounts(blk.litLen, blk.distLen);
    const r0 = rleOf(blk.litLen, blk.distLen, tc.litCount, tc.distCount);
    if (!buildLengths(r0.clFreq, 7)) blk = { ...blk, useDyn: false };
  }
  bw.write(isLast ? 1 : 0, 1);
  if (!blk.useDyn) {
    bw.write(1, 2); // fixed
    const litCode = FIX_LIT_CODE;
    for (let k = 0; k < blk.ntok; k++) {
      if (blk.tokLen[k] === 0) { const s = blk.tokSym[k]; bw.writeCode(litCode[s], FIX_LIT_LEN[s]); }
      else {
        const s = blk.tokSym[k]; const L = blk.tokLen[k]; const D = blk.tokDist[k];
        bw.writeCode(litCode[s], FIX_LIT_LEN[s]);
        if (LEN_EB[L] > 0) bw.write(L - LEN_B[L], LEN_EB[L]);
        bw.writeCode(DIST_SYM[D], 5);
        if (DIST_EB[D] > 0) bw.write(D - DIST_B[D], DIST_EB[D]);
      }
    }
    bw.writeCode(litCode[256], 7);
    return;
  }
  // dynamic
  if (!kraftOk(blk.litLen, 15) || !kraftOk(blk.distLen, 7)) { kraftFail.n++; }
  bw.write(2, 2);
  const { litCount, distCount } = trimCounts(blk.litLen, blk.distLen);
  const r = rleOf(blk.litLen, blk.distLen, litCount, distCount);
  const clLen = buildLengths(r.clFreq, 7) ?? new Int32Array(19);
  if (!kraftOk(clLen, 7)) kraftFail.n++;
  let clCount = 19; while (clCount > 4 && clLen[CL_ORDER[clCount - 1]] === 0) clCount--;
  bw.write(litCount - 257, 5); bw.write(distCount - 1, 5); bw.write(clCount - 4, 4);
  for (let k = 0; k < clCount; k++) bw.write(clLen[CL_ORDER[k]], 3);
  const clCode = canonicalCodes(clLen).code;
  for (let k = 0; k < r.sym.length; k++) {
    const s = r.sym[k]; bw.writeCode(clCode[s], clLen[s]);
    if (r.ebits[k] > 0) bw.write(r.extra[k], r.ebits[k]);
  }
  const litCode = canonicalCodes(blk.litLen).code;
  const distCode = canonicalCodes(blk.distLen).code;
  for (let k = 0; k < blk.ntok; k++) {
    if (blk.tokLen[k] === 0) { const s = blk.tokSym[k]; bw.writeCode(litCode[s], blk.litLen[s]); }
    else {
      const s = blk.tokSym[k]; const L = blk.tokLen[k]; const D = blk.tokDist[k];
      bw.writeCode(litCode[s], blk.litLen[s]);
      if (LEN_EB[L] > 0) bw.write(L - LEN_B[L], LEN_EB[L]);
      const ds = DIST_SYM[D]; bw.writeCode(distCode[ds], blk.distLen[ds]);
      if (DIST_EB[D] > 0) bw.write(D - DIST_B[D], DIST_EB[D]);
    }
  }
  bw.writeCode(litCode[256], blk.litLen[256]);
}

// ---------- Compress one filtered stream with the custom DEFLATE ----------
function compressCustom(data: Uint8Array, rowStride: number, iters: number, maxDepth: number, diag: any, period: number, dpCand: number): { zlib: Uint8Array; kraftFail: number; blocks: number; finder: Finder; } {
  const finder = buildFinder(data, rowStride, maxDepth, period);
  const rowLen = rowStride;
  let blockBytes = 262144;
  if (rowLen > 0) blockBytes = Math.max(rowLen, Math.floor(262144 / rowLen) * rowLen);
  const bw = new BitWriter();
  let kraftFail = 0; let blocks = 0;
  const kf = { n: 0 };
  for (let bs = 0; bs < data.length; bs += blockBytes) {
    const be = Math.min(data.length, bs + blockBytes);
    const blk = parseBlock(data, finder, bs, be, iters, dpCand);
    emitBlock(bw, blk, be >= data.length, kf);
    blocks++;
  }
  kraftFail = kf.n;
  const def = bw.finish();
  const out = new Uint8Array(2 + def.length + 4);
  out[0] = 0x78; out[1] = 0x9c; out.set(def, 2);
  const v = new DataView(out.buffer); v.setUint32(2 + def.length, adler32(data));
  if (diag) { diag.finderVisits = finder.visits; diag.finderPositions = finder.positions; diag.kraftFail = kraftFail; diag.blocks = blocks; diag.finder = finder; diag.data = data; }
  return { zlib: out, kraftFail, blocks, finder };
}

// ---------- Colour forms ----------
interface Form { ct: number; bpp: number; samples: Uint8Array; plte: Uint8Array | null; trns: Uint8Array | null; name: string; }
function buildForms(rgba: Uint8Array): Form[] {
  const forms: Form[] = [];
  const cmap = new Map<number, number>();
  let allGrey = true, allOpaque = true, alpha01 = true;
  const transRGB = new Set<number>(); let transGrey = -1; let greyKeyOk = true;
  for (let i = 0; i < N; i++) {
    const r = rgba[i * 4], g = rgba[i * 4 + 1], b = rgba[i * 4 + 2], a = rgba[i * 4 + 3];
    if (r !== g || g !== b) allGrey = false;
    if (a !== 255) allOpaque = false;
    if (a !== 0 && a !== 255) alpha01 = false;
    if (a === 0) { transRGB.add((r << 16) | (g << 8) | b); if (transGrey === -1) transGrey = r; else if (r !== transGrey) greyKeyOk = false; }
    const key = (r << 24) | (g << 16) | (b << 8) | a;
    cmap.set(key, (cmap.get(key) ?? 0) + 1);
  }
  forms.push({ ct: 6, bpp: 4, samples: rgba, plte: null, trns: null, name: 'rgba' });
  if (allOpaque || (alpha01 && transRGB.size === 1)) {
    const s = new Uint8Array(N * 3);
    for (let i = 0; i < N; i++) { s[i * 3] = rgba[i * 4]; s[i * 3 + 1] = rgba[i * 4 + 1]; s[i * 3 + 2] = rgba[i * 4 + 2]; }
    let trns: Uint8Array | null = null;
    if (!allOpaque) { const k = [...transRGB][0]; trns = new Uint8Array([0, (k >> 16) & 255, 0, (k >> 8) & 255, 0, k & 255]); }
    forms.push({ ct: 2, bpp: 3, samples: s, plte: null, trns, name: 'rgb' });
  }
  if (allGrey) {
    if (allOpaque) {
      const s = new Uint8Array(N); for (let i = 0; i < N; i++) s[i] = rgba[i * 4];
      forms.push({ ct: 0, bpp: 1, samples: s, plte: null, trns: null, name: 'grey' });
    } else if (alpha01 && greyKeyOk) {
      const s = new Uint8Array(N); for (let i = 0; i < N; i++) s[i] = rgba[i * 4];
      forms.push({ ct: 0, bpp: 1, samples: s, plte: null, trns: new Uint8Array([0, transGrey]), name: 'grey-key' });
    } else {
      const s = new Uint8Array(N * 2); for (let i = 0; i < N; i++) { s[i * 2] = rgba[i * 4]; s[i * 2 + 1] = rgba[i * 4 + 3]; }
      forms.push({ ct: 4, bpp: 2, samples: s, plte: null, trns: null, name: 'greyalpha' });
    }
  }
  if (cmap.size <= 256) {
    const cols = [...cmap.entries()];
    const orderings: { name: string; ord: number[] }[] = [];
    orderings.push({ name: 'freq', ord: cols.slice().sort((a, b) => b[1] - a[1]).map(e => e[0]) });
    orderings.push({ name: 'lum', ord: cols.slice().sort((a, b) => { const la = 0.299 * ((a[0] >> 24) & 255) + 0.587 * ((a[0] >> 16) & 255) + 0.114 * ((a[0] >> 8) & 255); const lb = 0.299 * ((b[0] >> 24) & 255) + 0.587 * ((b[0] >> 16) & 255) + 0.114 * ((b[0] >> 8) & 255); return la - lb; }).map(e => e[0]) });
    if (cmap.size <= 64) {
      const pair = new Map<number, number>();
      for (let y = 0; y < H; y++) for (let x = 0; x < W - 1; x++) {
        const a = (rgba[(y * W + x) * 4] << 24) | (rgba[(y * W + x) * 4 + 1] << 16) | (rgba[(y * W + x) * 4 + 2] << 8) | rgba[(y * W + x) * 4 + 3];
        const b = (rgba[(y * W + x + 1) * 4] << 24) | (rgba[(y * W + x + 1) * 4 + 1] << 16) | (rgba[(y * W + x + 1) * 4 + 2] << 8) | rgba[(y * W + x + 1) * 4 + 3];
        if (a !== b) { const k = a * 4294967296 + (b >>> 0); pair.set(k, (pair.get(k) ?? 0) + 1); }
      }
      const freq = new Map(cols);
      const remaining = new Set(cols.map(e => e[0]));
      const ord: number[] = [];
      let cur = cols.slice().sort((a, b) => b[1] - a[1])[0][0];
      ord.push(cur); remaining.delete(cur);
      while (remaining.size) {
        let bestK = -1, bestV = -1;
        for (const k of remaining) {
          const v = (pair.get(cur * 4294967296 + (k >>> 0)) ?? 0) + (pair.get(k * 4294967296 + (cur >>> 0)) ?? 0);
          const score = v * 1000 + (freq.get(k) ?? 0);
          if (score > bestV) { bestV = score; bestK = k; }
        }
        ord.push(bestK); remaining.delete(bestK); cur = bestK;
      }
      orderings.push({ name: 'adj', ord });
    }
    // rank orderings by filter-None zlib level-1 size; keep the best two
    const scored: { o: { name: string; ord: number[] }; s: Uint8Array; plte: Uint8Array; trns: Uint8Array | null; l1: number }[] = [];
    for (const o of orderings) {
      const idx = new Map<number, number>(); o.ord.forEach((k, i) => idx.set(k, i));
      const s = new Uint8Array(N);
      for (let i = 0; i < N; i++) { const k = (rgba[i * 4] << 24) | (rgba[i * 4 + 1] << 16) | (rgba[i * 4 + 2] << 8) | rgba[i * 4 + 3]; s[i] = idx.get(k)!; }
      const plte = new Uint8Array(o.ord.length * 3); const trnsFull = new Uint8Array(o.ord.length);
      o.ord.forEach((k, i) => { plte[i * 3] = (k >> 24) & 255; plte[i * 3 + 1] = (k >> 16) & 255; plte[i * 3 + 2] = (k >> 8) & 255; trnsFull[i] = k & 255; });
      let trns: Uint8Array | null = null; let last = trnsFull.length - 1; while (last >= 0 && trnsFull[last] === 255) last--;
      if (last >= 0) trns = trnsFull.subarray(0, last + 1);
      const raw0 = applyFilters(s, 1, new Uint8Array(H).fill(0));
      scored.push({ o, s, plte, trns, l1: deflateSync(raw0, { level: 1 }).length });
    }
    scored.sort((a, b) => a.l1 - b.l1);
    for (const sc of scored.slice(0, 2)) forms.push({ ct: 3, bpp: 1, samples: sc.s, plte: sc.plte, trns: sc.trns, name: 'pal-' + sc.o.name });
  }
  return forms;
}

function applyFilters(samples: Uint8Array, bpp: number, choice: Uint8Array): Uint8Array {
  const stride = W * bpp; const raw = new Uint8Array(H * (stride + 1));
  const tmp = new Uint8Array(stride);
  for (let y = 0; y < H; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    filterRow(choice[y], cur, prev, bpp, tmp);
    raw[y * (stride + 1)] = choice[y]; raw.set(tmp, y * (stride + 1) + 1);
  }
  return raw;
}
function applyFiltersFrom(filt: Uint8Array[], bpp: number, choice: Uint8Array): Uint8Array {
  const stride = W * bpp; const raw = new Uint8Array(H * (stride + 1));
  for (let y = 0; y < H; y++) {
    const t = choice[y];
    raw[y * (stride + 1)] = t;
    raw.set(filt[t].subarray(y * stride, (y + 1) * stride), y * (stride + 1) + 1);
  }
  return raw;
}
function viterbi(costs: Float64Array, penalty: number): Uint8Array {
  const dp = new Float64Array(5); const back = new Uint8Array(H * 5);
  for (let t = 0; t < 5; t++) dp[t] = costs[t];
  for (let y = 1; y < H; y++) {
    const ndp = new Float64Array(5).fill(Infinity);
    for (let t = 0; t < 5; t++) for (let p = 0; p < 5; p++) { const c = dp[p] + (p === t ? 0 : penalty) + costs[y * 5 + t]; if (c < ndp[t]) { ndp[t] = c; back[y * 5 + t] = p; } }
    dp.set(ndp);
  }
  let best = 0; for (let t = 1; t < 5; t++) if (dp[t] < dp[best]) best = t;
  const choice = new Uint8Array(H);
  for (let y = H - 1; y >= 0; y--) { choice[y] = best; best = back[y * 5 + best]; }
  return choice;
}

// Filter contest for one form (cheap candidates). Returns candidates ranked by zlib
// level-1 size, plus the filtered streams so the brute candidate can be added later.
function filterContest(form: Form): { ranked: { cand: { name: string; choice: Uint8Array }; raw: Uint8Array; l1: number }[]; filt: Uint8Array[]; stride: number } {
  const { samples, bpp } = form; const stride = W * bpp;
  const filt: Uint8Array[] = [];
  for (let t = 0; t < 5; t++) {
    const f = new Uint8Array(N * bpp); const tmp = new Uint8Array(stride);
    for (let y = 0; y < H; y++) {
      const cur = samples.subarray(y * stride, (y + 1) * stride);
      const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
      filterRow(t, cur, prev, bpp, tmp); f.set(tmp, y * stride);
    }
    filt.push(f);
  }
  const entCosts = new Float64Array(H * 5); const rowSum = new Float64Array(H * 5);
  const hist = new Int32Array(256);
  for (let y = 0; y < H; y++) for (let t = 0; t < 5; t++) {
    const row = filt[t].subarray(y * stride, (y + 1) * stride);
    hist.fill(0); let ss = 0;
    for (let i = 0; i < stride; i++) { hist[row[i]]++; const v = row[i]; ss += v < 128 ? v : 256 - v; }
    rowSum[y * 5 + t] = ss;
    let bits = 0; for (let v = 0; v < 256; v++) { const c = hist[v]; if (c) bits += c * (Math.log2(stride) - Math.log2(c)); }
    entCosts[y * 5 + t] = bits;
  }
  const cands: { name: string; choice: Uint8Array }[] = [];
  const push = (name: string, choice: Uint8Array) => {
    if (!cands.some(c => { for (let y = 0; y < H; y++) if (c.choice[y] !== choice[y]) return false; return true; })) cands.push({ name, choice });
  };
  push('f0', new Uint8Array(H).fill(0));
  push('f2', new Uint8Array(H).fill(2));
  push('f4', new Uint8Array(H).fill(4));
  { const choice = new Uint8Array(H); for (let y = 0; y < H; y++) { let best = 0; for (let t = 1; t < 5; t++) if (rowSum[y * 5 + t] < rowSum[y * 5 + best]) best = t; choice[y] = best; } push('minsum', choice); }
  if (form.ct === 3) {
    const choice = new Uint8Array(H);
    for (let y = 0; y < H; y++) {
      if (y === 0) { choice[y] = 0; continue; }
      const cur = samples.subarray(y * stride, (y + 1) * stride); const prev = samples.subarray((y - 1) * stride, y * stride);
      let same = true, change = false;
      for (let i = 0; i < stride; i++) { if (cur[i] !== prev[i]) { same = false; break; } if (i > 0 && cur[i] !== cur[i - 1]) change = true; }
      choice[y] = same && change ? 2 : 0;
    }
    push('smartup', choice);
  }
  push('vit0', viterbi(entCosts, 0));
  push('vit256', viterbi(entCosts, 256));
  const ranked = cands.map(cand => { const raw = applyFiltersFrom(filt, bpp, cand.choice); return { cand, raw, l1: deflateSync(raw, { level: 1 }).length }; });
  ranked.sort((a, b) => a.l1 - b.l1);
  return { ranked, filt, stride };
}
// Per-row brute force (R3's method), added only for forms near the lead: each row
// compressed with a mid-level compressor using the previous 32 KiB of chosen
// filtered output as dictionary.
function addBrute(form: Form, contest: { ranked: { cand: { name: string; choice: Uint8Array }; raw: Uint8Array; l1: number }[]; filt: Uint8Array[]; stride: number }): void {
  const { filt, stride } = contest; const bpp = form.bpp;
  const choice = new Uint8Array(H);
  const dictBuf = new Uint8Array(H * (stride + 1));
  let dictLen = 0;
  const rowBuf = new Uint8Array(stride + 1);
  for (let y = 0; y < H; y++) {
    let bestT = 0, bestLen = Infinity;
    const dict = dictBuf.subarray(Math.max(0, dictLen - 32768), dictLen);
    for (let t = 0; t < 5; t++) {
      rowBuf[0] = t; rowBuf.set(filt[t].subarray(y * stride, (y + 1) * stride), 1);
      const len = deflateSync(rowBuf, { level: 6, dictionary: dict }).length;
      if (len < bestLen) { bestLen = len; bestT = t; }
    }
    choice[y] = bestT;
    rowBuf[0] = bestT; rowBuf.set(filt[bestT].subarray(y * stride, (y + 1) * stride), 1);
    dictBuf.set(rowBuf, dictLen); dictLen += stride + 1;
  }
  const cand = { name: 'brute', choice };
  const raw = applyFiltersFrom(filt, bpp, choice);
  contest.ranked.push({ cand, raw, l1: deflateSync(raw, { level: 1 }).length });
  contest.ranked.sort((a, b) => a.l1 - b.l1);
}

// ---------- Finder diagnostic (brute force, sampled) ----------
function finderDiag(data: Uint8Array, finder: Finder): { sampled: number; noMatch: number; strict: number; visitsPerPos: number } {
  const n = data.length; const nsamp = 150; const step = Math.max(1, Math.floor(n / nsamp));
  let sampled = 0, noMatch = 0, strict = 0;
  for (let k = 0; k < nsamp; k++) {
    const pos = Math.min(n - 4, k * step + 7);
    if (pos < 4) continue;
    const lim = Math.min(pos, 32768);
    let brute = 0;
    for (let d = 1; d <= lim; d++) {
      const p = pos - d;
      if (data[p] !== data[pos] || data[p + 1] !== data[pos + 1] || data[p + 2] !== data[pos + 2]) continue;
      const ml = matchLen(data, p, pos, 258);
      if (ml > brute) brute = ml;
      if (brute >= 258) break;
    }
    if (brute < 32) continue;
    sampled++;
    const fb = finder.bestLen[pos];
    if (fb < 3) noMatch++;
    if (fb < brute - 3) strict++;
  }
  return { sampled, noMatch, strict, visitsPerPos: finder.visits / Math.max(1, finder.positions) };
}

// ---------- Encode one instance ----------
const SCALE: Record<string, number> = { i001: 13547, i002: 55063, i003: 107892, i004: 110521, i005: 18669, i006: 185295, i007: 64285, i008: 26807 };
function cpuMs(u: NodeJS.CpuUsage): number { return (u.user + u.system) / 1000; }
function encodeOne(id: string): any {
  const diag: any = { id };
  const t0 = DIAG ? process.cpuUsage() : null;
  const rgba = decode(readFileSync(join(I, id, 'image.png')));
  const forms = buildForms(rgba);
  const t1 = DIAG ? process.cpuUsage() : null;
  if (DIAG) diag.formsMs = t0 ? cpuMs(process.cpuUsage(t0)) : 0;
  // per-form contest (cheap candidates first), ranked by zlib L1
  const perForm: { form: Form; contest: { ranked: { cand: { name: string; choice: Uint8Array }; raw: Uint8Array; l1: number }[]; filt: Uint8Array[]; stride: number } }[] = [];
  for (const form of forms) perForm.push({ form, contest: filterContest(form) });
  perForm.sort((a, b) => a.contest.ranked[0].l1 - b.contest.ranked[0].l1);
  // brute-force filter candidate only for the lead form
  const leadL1 = perForm[0].contest.ranked[0].l1;
  addBrute(perForm[0].form, perForm[0].contest);
  perForm.sort((a, b) => a.contest.ranked[0].l1 - b.contest.ranked[0].l1);
  const t2 = DIAG ? process.cpuUsage() : null;
  if (DIAG) diag.filterMs = t1 ? cpuMs(process.cpuUsage(t1)) : 0;
  let best: { total: number; form: Form; def: Uint8Array; candName: string; customLen: number; libLen: number; diagFinder: any; iters: number } | null = null;
  const tParse0 = DIAG ? process.cpuUsage() : null;
  const evalForms = perForm.slice(0, 2);
  for (let fi = 0; fi < evalForms.length; fi++) {
    const pf = evalForms[fi];
    const form = pf.form;
    const overhead = (form.plte ? form.plte.length + 12 : 0) + (form.trns ? form.trns.length + 12 : 0) + 57;
    // best form gets full budgets; a second form gets a lib-first gate (custom beats
    // the library by ~10% on multi-byte streams and up to ~16% on 1-byte streams,
    // so skip it only when even the library cannot reach the lead) and reduced
    // iterations.
    const isBestForm = fi === 0;
    const itersFull = form.bpp === 1 ? ITERS_FLAT : ITERS_RICH;
    const depth = form.bpp === 1 ? DEPTH_FLAT : DEPTH_RICH;
    const dpCand = 4;
    const rowStride = W * form.bpp + 1;
    const candList = pf.contest.ranked.slice(0, 1);
    for (const top of candList) {
      const lib = deflateSync(top.raw, { level: 9 });
      // gate every candidate by its own library size: a candidate whose library
      // encoding cannot reach the current best (allowing for custom beating the
      // library by ~10% multi-byte / ~18% 1-byte) is not worth a custom parse
      const gate = form.bpp === 1 ? 1.05 : 1.12;
      if (best && lib.length + overhead > best.total * gate) {
        if (DIAG) diag['form_' + form.name + '_' + top.cand.name] = { cand: top.cand.name, skipped: 'lib-gate', lib: lib.length };
        continue;
      }
      const iters = isBestForm ? itersFull : (form.bpp === 1 ? 6 : 2);
      const d2: any = {};
      const custom = compressCustom(top.raw, rowStride, iters, depth, DIAG ? d2 : null, form.bpp, dpCand);
      const useCustom = custom.zlib.length <= lib.length;
      const def = useCustom ? custom.zlib : lib;
      const total = def.length + overhead;
      let fd: any = null;
      if (DIAG) fd = finderDiag(top.raw, custom.finder);
      if (!best || total < best.total) best = { total, form, def, candName: top.cand.name, customLen: custom.zlib.length, libLen: lib.length, diagFinder: fd, iters };
      if (DIAG) diag['form_' + form.name + '_' + top.cand.name] = { cand: top.cand.name, custom: custom.zlib.length, lib: lib.length, kraftFail: custom.kraftFail, blocks: custom.blocks, visitsPerPos: custom.finder.visits / Math.max(1, custom.finder.positions), finderDiag: fd };
    }
  }
  if (DIAG) diag.parseMs = tParse0 ? cpuMs(process.cpuUsage(tParse0)) : 0;
  const f = best!;
  diag.form = f.form.name; diag.filter = f.candName; diag.customLen = f.customLen; diag.libLen = f.libLen;
  diag.bytes = f.total; diag.points = Math.round(1000 * (2 * SCALE[id] - f.total) / (2 * SCALE[id] - SCALE[id] / 2) * 1000) / 1000;
  const parts: Uint8Array[] = [chunk('IHDR', ihdr(f.form.ct))];
  if (f.form.plte) parts.push(chunk('PLTE', f.form.plte));
  if (f.form.trns) parts.push(chunk('tRNS', f.form.trns));
  parts.push(chunk('IDAT', f.def));
  parts.push(chunk('IEND', new Uint8Array(0)));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'image.png'), pngOf(parts));
  return diag;
}

const diags: any[] = [];
for (const id of readdirSync(I).sort()) {
  const d = encodeOne(id);
  if (DIAG) { diags.push(d); console.error(JSON.stringify(d)); }
}
if (DIAG) {
  const tot = diags.reduce((a, d) => a + d.points, 0) / diags.length;
  console.error('SCORE_EST ' + Math.round(tot * 1000));
}
