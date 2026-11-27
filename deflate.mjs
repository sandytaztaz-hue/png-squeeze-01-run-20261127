// deflate.mjs — a from-scratch optimal-parse DEFLATE compressor (zlib wrapper).
// Written fresh for the png-squeeze entry. Pure Node standard library.
// Design: hash-chain match search with a Pareto frontier of candidates and
// sub-length expansion, an optimal-parse dynamic program with true bit costs
// and cost-table refinement, package-merge length-limited Huffman codes,
// adaptive multi-block output with per-block tables, and a zlib-9 fallback.
// Deterministic: fixed budgets only, no clock, no randomness.

import { deflateSync } from 'node:zlib';

// ---- DEFLATE tables (RFC 1951) -------------------------------------------

export const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
export const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
export const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
export const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
// Length symbol (257..285) for every match length 3..258.
export const LEN_SYM = (() => {
  const t = new Int16Array(259);
  for (let s = 0; s < 29; s++) {
    const base = LEN_BASE[s];
    const next = s === 28 ? 259 : LEN_BASE[s + 1];
    for (let l = base; l < next; l++) t[l] = 257 + s;
  }
  return t;
})();
// Distance symbol (0..29) for every distance 1..32768.
export const DIST_SYM = (() => {
  const t = new Int16Array(32769);
  for (let s = 0; s < 30; s++) {
    const base = DIST_BASE[s];
    const next = s === 29 ? 32769 : DIST_BASE[s + 1];
    for (let d = base; d < next; d++) t[d] = s;
  }
  return t;
})();
// Fixed Huffman lengths.
export const FIXED_LIT_LEN = (() => {
  const t = new Int16Array(288);
  for (let s = 0; s < 144; s++) t[s] = 8;
  for (let s = 144; s < 256; s++) t[s] = 9;
  for (let s = 256; s < 280; s++) t[s] = 7;
  for (let s = 280; s < 288; s++) t[s] = 8;
  return t;
})();
export const FIXED_DIST_LEN = (() => {
  const t = new Int16Array(32);
  for (let s = 0; s < 32; s++) t[s] = 5;
  return t;
})();

// ---- checksums ------------------------------------------------------------

export function adler32(data) {
  let a = 1;
  let b = 0;
  const n = data.length;
  let i = 0;
  while (i < n) {
    const end = Math.min(n, i + 5552);
    for (; i < end; i++) {
      a += data[i];
      b += a;
    }
    a %= 65521;
    b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

// ---- bit writer -----------------------------------------------------------

export class BitWriter {
  constructor(capacity) {
    this.buf = new Uint8Array(Math.max(1024, capacity));
    this.pos = 0; // bytes written
    this.acc = 0; // pending bits, LSB first
    this.nbits = 0;
  }
  grow(need) {
    if (this.pos + need + 8 > this.buf.length) {
      const next = new Uint8Array(Math.max(this.buf.length * 2, this.pos + need + 1024));
      next.set(this.buf.subarray(0, this.pos));
      this.buf = next;
    }
  }
  put(code, len) {
    this.acc |= code << this.nbits;
    this.nbits += len;
    while (this.nbits >= 8) {
      this.grow(1);
      this.buf[this.pos++] = this.acc & 0xff;
      this.acc >>>= 8;
      this.nbits -= 8;
    }
  }
  putReversed(code, len) {
    // Put `len` bits of `code`, most-significant bit first (Huffman codes).
    let rev = 0;
    for (let i = 0; i < len; i++) rev = (rev << 1) | ((code >>> i) & 1);
    this.put(rev, len);
  }
  align() {
    if (this.nbits > 0) {
      this.grow(1);
      this.buf[this.pos++] = this.acc & 0xff;
      this.acc = 0;
      this.nbits = 0;
    }
  }
  bytes() {
    this.align();
    return this.buf.subarray(0, this.pos);
  }
  get length() {
    return this.pos + (this.nbits > 0 ? 1 : 0);
  }
}

// ---- Huffman codes --------------------------------------------------------

/** Length-limited code lengths from symbol frequencies (package-merge).
 * Lists are built level by level: each level merges the two lightest items
 * of the current list, pair by pair, into the next list, then the singletons
 * join it; after maxBits levels the n-1 lightest items of the last list are
 * kept, and a symbol's code length is how many of them contain it. */
export function packageMerge(freqs, maxBits) {
  const n = freqs.length;
  const lengths = new Int16Array(n);
  const live = [];
  for (let s = 0; s < n; s++) if (freqs[s] > 0) live.push(s);
  if (live.length === 0) return lengths;
  if (live.length === 1) {
    lengths[live[0]] = 1;
    return lengths;
  }
  if (live.length === 2) {
    lengths[live[0]] = 1;
    lengths[live[1]] = 1;
    return lengths;
  }
  const singletons = live
    .map((s) => ({ w: freqs[s], syms: [s] }))
    .sort((a, b) => a.w - b.w);
  const L = Math.min(maxBits, live.length - 1);
  let cur = singletons;
  for (let level = 0; level < L; level++) {
    // Pair adjacent items of the sorted list into the next list.
    const next = [];
    for (let i = 0; i + 1 < cur.length; i += 2) {
      next.push({ w: cur[i].w + cur[i + 1].w, syms: cur[i].syms.concat(cur[i + 1].syms) });
    }
    if (level + 1 < L) {
      // The singletons join the next list; keep it sorted by weight.
      const merged = [];
      let a = 0;
      let b = 0;
      while (a < singletons.length || b < next.length) {
        if (b >= next.length || (a < singletons.length && singletons[a].w <= next[b].w)) merged.push(singletons[a++]);
        else merged.push(next[b++]);
      }
      cur = merged;
    } else {
      cur = next;
    }
  }
  const selected = cur.slice(0, live.length - 1);
  for (const item of selected) for (const s of item.syms) lengths[s]++;
  return lengths;
}

/** Canonical Huffman codes from code lengths: { codes, lengths }. */
export function canonicalCodes(lengths) {
  const n = lengths.length;
  const codes = new Int32Array(n);
  const blCount = new Int32Array(16);
  for (let s = 0; s < n; s++) if (lengths[s] > 0) blCount[lengths[s]]++;
  let code = 0;
  const next = new Int32Array(16);
  for (let b = 1; b < 16; b++) {
    code = (code + blCount[b - 1]) << 1;
    next[b] = code;
  }
  for (let s = 0; s < n; s++) {
    const len = lengths[s];
    if (len > 0) codes[s] = next[len]++;
  }
  return { codes, lengths };
}

/** Bit cost of every literal/length symbol under a code-length table. */
export function symbolCosts(lengths) {
  const c = new Float64Array(lengths.length);
  for (let s = 0; s < lengths.length; s++) c[s] = lengths[s] === 0 ? 1e9 : lengths[s];
  return c;
}

// ---- zlib fallback ----------------------------------------------------------

/** zlib level-9 stream of raw bytes (used as a fallback / yardstick). */
export function zlib9(data) {
  const out = deflateSync(data, { level: 9, memLevel: 9 });
  return new Uint8Array(out.buffer, out.byteOffset, out.length);
}

// ---- match search ---------------------------------------------------------

// Length of the match between data[a..] and data[b..], at most maxLen.
// Word-at-a-time via u32 when the offsets are congruent mod 4.
function matchLength(data, a, b, maxLen, u32) {
  let l = 0;
  if (u32 !== null && ((a - b) & 3) === 0 && maxLen >= 4) {
    while (l < maxLen && ((a + l) & 3) !== 0) {
      if (data[a + l] !== data[b + l]) return l;
      l++;
    }
    const aw = (a + l) >> 2;
    const bw = (b + l) >> 2;
    const words = (maxLen - l) >> 2;
    let w = 0;
    while (w < words && u32[aw + w] === u32[bw + w]) w++;
    l += w * 4;
  }
  while (l < maxLen && data[a + l] === data[b + l]) l++;
  return l;
}

// Insert one (len, dist) pair into a Pareto frontier list (at most 32 pairs):
// a pair is kept only when no other pair is both at least as long and at
// least as near; pairs it dominates are dropped.
function addPair(list, len, dist) {
  for (let i = 0; i < list.length; i++) {
    if (list[i][0] >= len && list[i][1] <= dist) return;
  }
  for (let i = list.length - 1; i >= 0; i--) {
    if (list[i][0] <= len && list[i][1] >= dist) list.splice(i, 1);
  }
  list.push([len, dist]);
  if (list.length > 32) {
    let worst = 0;
    for (let i = 1; i < list.length; i++) {
      const l = list[i][0];
      const d = list[i][1];
      const wl = list[worst][0];
      const wd = list[worst][1];
      if (l < wl || (l === wl && d > wd)) worst = i;
    }
    list.splice(worst, 1);
  }
}

// Find match candidates at every position of `data`, with two hash chains:
// a 3-byte chain (16-bit table) walked only a short way — length-3 matches
// pay only up close — and a 4-byte chain (18-bit table) walked far, which
// stays cheap because 4-byte patterns collide far less. The 3-byte walk runs
// first so near short matches are recorded before a long match raises the
// bar. `chainCap` bounds the 4-byte walk, `cap3` the 3-byte walk.
//   rowStride: distance of the row directly above (0 = unknown); a vertical
//     candidate from the previous row is added at every position.
// Returns { off, lens, dists }: for position p, the expanded (len, dist)
// candidates are lens[off[p]..off[p+1]], dists[off[p]..off[p+1]]. Expansion
// turns each frontier pair (L, D) into the lengths L, 3 and the base of L's
// length-code range, so the DP can also start shorter matches at that distance.
export function findMatches(data, chainCap, rowStride = 0, stallLimit = 1000000, cap3 = 32) {
  const n = data.length;
  const u32 = data.byteOffset % 4 === 0 ? new Uint32Array(data.buffer, data.byteOffset, n >> 2) : null;
  const head3 = new Int32Array(1 << 16).fill(-1);
  const prev3 = new Int32Array(n).fill(-1);
  const head4 = new Int32Array(1 << 18).fill(-1);
  const prev4 = new Int32Array(n).fill(-1);
  // Raw Pareto frontier pairs per position; expansion into (len, dist)
  // candidates happens later in expandCands (cheap everywhere, rich at
  // chosen positions), so the match search runs only once.
  const pairOff = new Int32Array(n + 1);
  let cap = 1 << 20;
  let pairLens = new Uint16Array(cap);
  let pairDists = new Uint16Array(cap);
  let count = 0;
  const pushPair = (len, dist) => {
    if (count >= cap) {
      cap *= 2;
      const nl = new Uint16Array(cap);
      nl.set(pairLens);
      pairLens = nl;
      const nd = new Uint16Array(cap);
      nd.set(pairDists);
      pairDists = nd;
    }
    pairLens[count] = len;
    pairDists[count] = dist;
    count++;
  };
  const frontier = [];
  // Walk one hash chain from its head, collecting Pareto pairs into the
  // shared frontier. Chains run newest-first, so a later entry is always
  // farther: once a length is beaten, only longer matches can still help,
  // which the byte-at-best check enforces. `best` / `bestDist` are shared
  // across the two walks at one position.
  let best = 2;
  let bestDist = 0;
  const walk = (headArr, prevArr, h, cap, maxLen, oldest, p) => {
    let cur = headArr[h];
    let steps = 0;
    let sinceImprove = 0;
    while (cur >= oldest && cur >= 0 && steps < cap) {
      steps++;
      const dist = p - cur;
      if (best < maxLen && data[cur + best] === data[p + best] && (best < 8 || data[cur + best - 8] === data[p + best - 8])) {
        const len = matchLength(data, p, cur, maxLen, u32);
        if (len > best) {
          best = len;
          bestDist = dist;
          sinceImprove = 0;
          addPair(frontier, len, dist);
          if (len >= maxLen) break;
        } else {
          sinceImprove++;
        }
      } else if (best === 2) {
        // No long match yet: still measure short ones (length 3 matters).
        const len = matchLength(data, p, cur, Math.min(4, maxLen), u32);
        if (len >= 3) {
          best = len;
          bestDist = dist;
          sinceImprove = 0;
          addPair(frontier, len, dist);
        } else {
          sinceImprove++;
        }
      } else {
        sinceImprove++;
      }
      if (sinceImprove >= stallLimit) break;
      cur = prevArr[cur];
    }
  };
  for (let p = 0; p < n; p++) {
    if (p + 3 <= n) {
      const maxLen = Math.min(258, n - p);
      const oldest = p - 32768;
      best = 2;
      bestDist = 0;
      frontier.length = 0;
      const h3 = ((data[p] << 10) ^ (data[p + 1] << 5) ^ data[p + 2]) & 0xffff;
      // Short walk: only length-3 matches live here (anything longer shares
      // 4 bytes and the 4-byte walk measures it), so three inline byte
      // checks replace matchLength entirely.
      let cur3 = head3[h3];
      let steps3 = 0;
      while (cur3 >= oldest && cur3 >= 0 && steps3 < cap3) {
        steps3++;
        const dist = p - cur3;
        if (data[cur3] === data[p] && data[cur3 + 1] === data[p + 1] && data[cur3 + 2] === data[p + 2]) {
          const longer = p + 4 <= n && data[cur3 + 3] === data[p + 3];
          if (!longer && best < 3) {
            best = 3;
            bestDist = dist;
            addPair(frontier, 3, dist);
          }
        }
        cur3 = prev3[cur3];
      }
      if (p + 4 <= n && best < maxLen) {
        const h4 = ((((data[p] * 31 + data[p + 1]) * 31 + data[p + 2]) * 31 + data[p + 3]) & 0x3ffff);
        walk(head4, prev4, h4, chainCap, maxLen, oldest, p);
      }
      // Vertical candidate: the same column one row up.
      if (rowStride > 0 && p >= rowStride) {
        const len = matchLength(data, p, p - rowStride, maxLen, u32);
        if (len >= 3) {
          addPair(frontier, len, rowStride);
          if (len > best) {
            best = len;
            bestDist = rowStride;
          }
        }
      }
      // Store the raw frontier pairs; expansion is expandCands' job.
      for (let i = 0; i < frontier.length; i++) pushPair(frontier[i][0], frontier[i][1]);
      prev3[p] = head3[h3];
      head3[h3] = p;
      if (p + 4 <= n) {
        const h4 = ((((data[p] * 31 + data[p + 1]) * 31 + data[p + 2]) * 31 + data[p + 3]) & 0x3ffff);
        prev4[p] = head4[h4];
        head4[h4] = p;
      }
    }
    pairOff[p + 1] = count;
  }
  return { pairOff, pairLens: pairLens.subarray(0, count), pairDists: pairDists.subarray(0, count) };
}

// Length-code range tops: the longest length in each range. A match of
// length L at distance D can be truncated to any top <= L at the same
// distance, letting the DP stop a long match early to start a better one.
const TOPS = [3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 22, 26, 30, 34, 42, 50, 58, 66, 82, 98, 114, 130, 162, 194, 226, 257, 258];

// Expand raw frontier pairs into (len, dist) candidates. Every pair
// contributes its length L, length 3, and the base of L's length-code
// range. At positions where `rich` is set, the longest pair additionally
// contributes every range top <= L (the truncation options).
export function expandCands(pairs, rich) {
  const n = pairs.pairOff.length - 1;
  const off = new Int32Array(n + 1);
  let cap = 1 << 20;
  let lens = new Uint16Array(cap);
  let dists = new Uint16Array(cap);
  let count = 0;
  const push = (len, dist) => {
    if (count >= cap) {
      cap *= 2;
      const nl = new Uint16Array(cap);
      nl.set(lens);
      lens = nl;
      const nd = new Uint16Array(cap);
      nd.set(dists);
      dists = nd;
    }
    lens[count] = len;
    dists[count] = dist;
    count++;
  };
  for (let p = 0; p < n; p++) {
    const s = pairs.pairOff[p];
    const e = pairs.pairOff[p + 1];
    if (e > s && rich !== null && rich[p]) {
      let maxL = 0;
      for (let i = s; i < e; i++) if (pairs.pairLens[i] > maxL) maxL = pairs.pairLens[i];
      for (let i = s; i < e; i++) {
        const L = pairs.pairLens[i];
        const D = pairs.pairDists[i];
        push(L, D);
        if (L !== 3) {
          push(3, D);
          if (L === maxL) {
            for (let t = 0; t < TOPS.length; t++) {
              const top = TOPS[t];
              if (top >= L) break;
              if (top > 3) push(top, D);
            }
          } else {
            const base = LEN_BASE[LEN_SYM[L] - 257];
            if (base !== 3 && base !== L) push(base, D);
          }
        }
      }
    } else {
      for (let i = s; i < e; i++) {
        const L = pairs.pairLens[i];
        const D = pairs.pairDists[i];
        push(L, D);
        if (L !== 3) {
          push(3, D);
          const base = LEN_BASE[LEN_SYM[L] - 257];
          if (base !== 3 && base !== L) push(base, D);
        }
      }
    }
    off[p + 1] = count;
  }
  return { off, lens: lens.subarray(0, count), dists: dists.subarray(0, count) };
}

// ---- optimal parse --------------------------------------------------------

// Cost tables from code lengths: literal costs, per-length match costs and
// per-distance match costs (symbol cost plus extra bits).
function costTables(litLen, distLen) {
  const litCost = new Float64Array(288);
  for (let s = 0; s < 288; s++) litCost[s] = litLen[s] === 0 ? 1e9 : litLen[s];
  const lenCost = new Float64Array(259);
  for (let l = 3; l <= 258; l++) {
    const sym = LEN_SYM[l];
    lenCost[l] = litCost[sym] + LEN_EXTRA[sym - 257];
  }
  const distCost = new Float64Array(32769);
  for (let d = 1; d <= 32768; d++) {
    const sym = DIST_SYM[d];
    distCost[d] = (distLen[sym] === 0 ? 1e9 : distLen[sym]) + DIST_EXTRA[sym];
  }
  return { litCost, lenCost, distCost };
}

// One forward DP pass over [from, to): fills costBuf and the back-pointers,
// then backtracks into op arrays. Returns { len, dist, pos, count, bits }.
export function dpParse(data, cands, from, to, litCost, lenCost, distCost, scratch) {
  const { cost, prevLen, prevDist } = scratch;
  cost.fill(Infinity, from, to + 1);
  cost[from] = 0;
  for (let p = from; p < to; p++) {
    const c = cost[p];
    if (c === Infinity) continue;
    const lc = c + litCost[data[p]];
    if (lc < cost[p + 1]) {
      cost[p + 1] = lc;
      prevLen[p + 1] = 1;
      prevDist[p + 1] = 0;
    }
    const s = cands.off[p];
    const e = cands.off[p + 1];
    for (let i = s; i < e; i++) {
      const len = cands.lens[i];
      const end = p + len;
      if (end > to) continue;
      const mc = c + lenCost[len] + distCost[cands.dists[i]];
      if (mc < cost[end]) {
        cost[end] = mc;
        prevLen[end] = len;
        prevDist[end] = cands.dists[i];
      }
    }
  }
  const bits = cost[to];
  // Backtrack.
  const lenArr = new Int32Array(to - from + 1);
  const distArr = new Int32Array(to - from + 1);
  const posArr = new Int32Array(to - from + 1);
  let count = 0;
  let p = to;
  while (p > from) {
    const len = prevLen[p];
    const dist = prevDist[p];
    lenArr[count] = len;
    distArr[count] = dist;
    posArr[count] = p - len;
    count++;
    p -= len;
  }
  // Reverse into forward order.
  const opsLen = new Int32Array(count);
  const opsDist = new Int32Array(count);
  const opsPos = new Int32Array(count);
  for (let i = 0; i < count; i++) {
    opsLen[i] = lenArr[count - 1 - i];
    opsDist[i] = distArr[count - 1 - i];
    opsPos[i] = posArr[count - 1 - i];
  }
  return { opsLen, opsDist, opsPos, count, bits };
}

// Symbol frequencies of a parse: literal/length symbols 0..285 and distance
// symbols 0..29 (a match of length 3..258 also counts its length symbol).
export function parseFreqs(data, ops, litFreq, distFreq) {
  litFreq.fill(0);
  distFreq.fill(0);
  const { opsLen, opsDist, opsPos, count } = ops;
  for (let i = 0; i < count; i++) {
    const len = opsLen[i];
    if (len === 1) {
      litFreq[data[opsPos[i]]]++;
    } else {
      litFreq[LEN_SYM[len]]++;
      distFreq[DIST_SYM[opsDist[i]]]++;
    }
  }
  litFreq[256]++; // end of block
}

// Run the DP `iterations` times, rebuilding the Huffman tables from each
// parse's frequencies. Starts from `initLitLen` / `initDistLen` (fixed
// tables when omitted). Returns the final parse plus its code lengths.
export function refineParse(data, cands, from, to, iterations, scratch, initLitLen = null, initDistLen = null) {
  let litLen = initLitLen === null ? FIXED_LIT_LEN : initLitLen;
  let distLen = initDistLen === null ? FIXED_DIST_LEN : initDistLen;
  let ops = null;
  const litFreq = new Int32Array(288);
  const distFreq = new Int32Array(32);
  for (let it = 0; it < iterations; it++) {
    const { litCost, lenCost, distCost } = costTables(litLen, distLen);
    ops = dpParse(data, cands, from, to, litCost, lenCost, distCost, scratch);
    parseFreqs(data, ops, litFreq, distFreq);
    litLen = packageMerge(litFreq, 15);
    distLen = packageMerge(distFreq, 15);
  }
  return { ops, litLen, distLen };
}

// ---- block splitting ------------------------------------------------------

// f * log2(f), tabulated so the split search never calls Math.log2 per op.
const LOGMUL = (() => {
  const t = new Float64Array(1 << 20);
  for (let i = 2; i < t.length; i++) t[i] = i * Math.log2(i);
  return t;
})();
const flog = (f) => (f < LOGMUL.length ? LOGMUL[f] : f * Math.log2(f));

// Choose block boundaries for a parse, by a DP over a coarse grid of op
// starts (every `gridBytes` input bytes, snapped to op starts). The cost of
// a segment is its Shannon entropy under its own symbol frequencies, plus
// the match extra bits, plus a dynamic-header estimate — so a boundary pays
// only where the local statistics actually change. Returns input offsets
// (op starts) of the chosen splits, between 0 and n exclusive.
export function chooseSplits(data, ops, gridBytes, maxBlocks, headerBits = 240) {
  const { opsLen, opsDist, opsPos, count } = ops;
  if (count < 2) return [];
  // Candidate boundary op indices: 0, count, and the first op at or after
  // each grid multiple.
  const bnd = [0];
  let next = gridBytes;
  for (let i = 1; i < count; i++) {
    if (opsPos[i] >= next) {
      bnd.push(i);
      next += gridBytes;
    }
  }
  bnd.push(count);
  const B = bnd.length;
  const isBnd = new Int32Array(count + 1).fill(-1);
  for (let j = 0; j < B; j++) isBnd[bnd[j]] = j;
  const dp = new Float64Array(B).fill(Infinity);
  const prev = new Int32Array(B).fill(-1);
  dp[0] = 0;
  const litFreq = new Int32Array(288);
  const distFreq = new Int32Array(32);
  const litFl = new Float64Array(288);
  const distFl = new Float64Array(32);
  for (let i = 0; i < B - 1; i++) {
    if (dp[i] === Infinity) continue;
    litFreq.fill(0);
    distFreq.fill(0);
    litFl.fill(0);
    distFl.fill(0);
    let sumLit = 0;
    let sumDist = 0;
    let totLit = 0;
    let totDist = 0;
    let distinctLit = 0;
    let distinctDist = 0;
    let extra = 0;
    const start = bnd[i];
    for (let k = start; k < count; k++) {
      const len = opsLen[k];
      if (len === 1) {
        const s = data[opsPos[k]];
        const f = litFreq[s];
        if (f === 0) distinctLit++;
        const nf = flog(f + 1);
        sumLit += nf - litFl[s];
        litFl[s] = nf;
        litFreq[s] = f + 1;
        totLit++;
      } else {
        const s = LEN_SYM[len];
        const f = litFreq[s];
        if (f === 0) distinctLit++;
        const nf = flog(f + 1);
        sumLit += nf - litFl[s];
        litFl[s] = nf;
        litFreq[s] = f + 1;
        totLit++;
        const ds = DIST_SYM[opsDist[k]];
        const df = distFreq[ds];
        if (df === 0) distinctDist++;
        const ndf = flog(df + 1);
        sumDist += ndf - distFl[ds];
        distFl[ds] = ndf;
        distFreq[ds] = df + 1;
        totDist++;
        extra += LEN_EXTRA[s - 257] + DIST_EXTRA[ds];
      }
      const j = isBnd[k + 1];
      if (j > 0) {
        const litBits = totLit > 0 ? totLit * Math.log2(totLit) - sumLit : 0;
        const distBits = totDist > 0 ? totDist * Math.log2(totDist) - sumDist : 0;
        const seg = litBits + distBits + extra + headerBits + 4 * (distinctLit + distinctDist);
        const tot = dp[i] + seg;
        if (tot < dp[j]) {
          dp[j] = tot;
          prev[j] = i;
        }
      }
    }
  }
  // Backtrack into split op indices, then input offsets.
  const splits = [];
  let j = B - 1;
  while (j > 0) {
    const i = prev[j];
    if (i < 0) break;
    if (i > 0) splits.push(bnd[i]);
    j = i;
  }
  splits.reverse();
  let offsets = splits.map((oi) => opsPos[oi]);
  if (offsets.length > maxBlocks - 1) {
    // Too many blocks: keep an evenly spaced subset of the chosen splits.
    const keep = [];
    const step = offsets.length / (maxBlocks - 1);
    for (let t = 0; t < maxBlocks - 1; t++) keep.push(offsets[Math.floor(t * step)]);
    offsets = [...new Set(keep)].sort((a, b) => a - b);
  }
  return offsets;
}

// ---- emission -------------------------------------------------------------

const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

// Run-length encoding of a code-length sequence into [symbol, extra, bits].
function rleLengths(lens) {
  const out = [];
  let i = 0;
  const n = lens.length;
  while (i < n) {
    const v = lens[i];
    let run = 1;
    while (i + run < n && lens[i + run] === v) run++;
    if (v === 0) {
      let r = run;
      while (r >= 11) {
        const t = Math.min(r, 138);
        out.push([18, t - 11, 7]);
        r -= t;
      }
      if (r >= 3) {
        out.push([17, r - 3, 3]);
        r = 0;
      }
      while (r > 0) {
        out.push([0, 0, 0]);
        r--;
      }
    } else {
      out.push([v, 0, 0]);
      let r = run - 1;
      while (r >= 3) {
        const t = Math.min(r, 6);
        out.push([16, t - 3, 2]);
        r -= t;
      }
      while (r > 0) {
        out.push([v, 0, 0]);
        r--;
      }
    }
    i += run;
  }
  return out;
}

// Write a dynamic Huffman header for litLen/distLen into bw.
function writeDynamicHeader(bw, litLen, distLen) {
  let nLit = 257;
  for (let s = 287; s >= 257; s--) {
    if (litLen[s] > 0) {
      nLit = s + 1;
      break;
    }
  }
  let nDist = 1;
  for (let s = 31; s >= 1; s--) {
    if (distLen[s] > 0) {
      nDist = s + 1;
      break;
    }
  }
  const all = new Int16Array(nLit + nDist);
  all.set(litLen.subarray(0, nLit), 0);
  all.set(distLen.subarray(0, nDist), nLit);
  const rle = rleLengths(all);
  const clFreq = new Int32Array(19);
  for (let i = 0; i < rle.length; i++) clFreq[rle[i][0]]++;
  const clLen = packageMerge(clFreq, 7);
  let nCl = 4;
  for (let i = 18; i >= 4; i--) {
    if (clLen[CL_ORDER[i]] > 0) {
      nCl = i + 1;
      break;
    }
  }
  bw.put(nLit - 257, 5);
  bw.put(nDist - 1, 5);
  bw.put(nCl - 4, 4);
  for (let i = 0; i < nCl; i++) bw.put(clLen[CL_ORDER[i]], 3);
  const clCodes = canonicalCodes(clLen).codes;
  for (let i = 0; i < rle.length; i++) {
    const [sym, extra, ebits] = rle[i];
    bw.putReversed(clCodes[sym], clLen[sym]);
    if (ebits > 0) bw.put(extra, ebits);
  }
}

// Exact bit length of a dynamic header (measured by writing it to scratch).
function dynamicHeaderBits(litLen, distLen) {
  const scratch = new BitWriter(1024);
  writeDynamicHeader(scratch, litLen, distLen);
  return scratch.pos * 8 + scratch.nbits;
}

// Exact body bits of a parse under a code-length pair (ops + end-of-block).
function bodyBits(data, ops, litLen, distLen) {
  const { opsLen, opsDist, opsPos, count } = ops;
  let bits = litLen[256];
  for (let i = 0; i < count; i++) {
    const len = opsLen[i];
    if (len === 1) {
      bits += litLen[data[opsPos[i]]];
    } else {
      const lsym = LEN_SYM[len];
      bits += litLen[lsym] + LEN_EXTRA[lsym - 257];
      const dsym = DIST_SYM[opsDist[i]];
      bits += distLen[dsym] + DIST_EXTRA[dsym];
    }
  }
  return bits;
}

// Write a parse's ops into bw under the given codes.
function writeOps(bw, data, ops, litCodes, litLen, distCodes, distLen) {
  const { opsLen, opsDist, opsPos, count } = ops;
  for (let i = 0; i < count; i++) {
    const len = opsLen[i];
    if (len === 1) {
      const s = data[opsPos[i]];
      bw.putReversed(litCodes[s], litLen[s]);
    } else {
      const lsym = LEN_SYM[len];
      bw.putReversed(litCodes[lsym], litLen[lsym]);
      const le = LEN_EXTRA[lsym - 257];
      if (le > 0) bw.put(len - LEN_BASE[lsym - 257], le);
      const dsym = DIST_SYM[opsDist[i]];
      bw.putReversed(distCodes[dsym], distLen[dsym]);
      const de = DIST_EXTRA[dsym];
      if (de > 0) bw.put(opsDist[i] - DIST_BASE[dsym], de);
    }
  }
  bw.putReversed(litCodes[256], litLen[256]);
}

// ---- top level ------------------------------------------------------------

// Compress `data` into a zlib stream: optimal-parse DEFLATE with adaptive
// multi-block output and per-block tables, or zlib level 9, whichever is
// smaller. opts: { chainCap, rowStride, globalIters, blockIters, maxBlocks }.
export function compressZlib(data, opts = {}) {
  const n = data.length;
  const z9 = zlib9(data);
  if (n < 1024) return z9;
  const chainCap = opts.chainCap ?? (n > 1000000 ? 128 : n > 200000 ? 256 : n > 50000 ? 512 : 1024);
  const rowStride = opts.rowStride ?? 0;
  const pairs = findMatches(data, chainCap, rowStride, opts.stallLimit ?? 1000000, opts.cap3 ?? 32);
  const scratch = {
    cost: new Float64Array(n + 1),
    prevLen: new Uint16Array(n + 1),
    prevDist: new Uint16Array(n + 1),
  };
  const globalIters = opts.globalIters ?? 2;
  const blockIters = opts.blockIters ?? 3;
  // Phase 1: cheap expansion, global parse. Its match starts are the
  // positions where a long match may want truncating, so phase 2 expands
  // richly only there and cheaply everywhere else.
  const cands = expandCands(pairs, null);
  const g = refineParse(data, cands, 0, n, globalIters, scratch);
  const gridBytes = rowStride > 0 ? rowStride * 16 : 32768;
  const splits = chooseSplits(data, g.ops, gridBytes, opts.maxBlocks ?? 16);
  const rich = new Uint8Array(n);
  for (let i = 0; i < g.ops.count; i++) {
    if (g.ops.opsLen[i] >= 3) rich[g.ops.opsPos[i]] = 1;
  }
  const candsRich = expandCands(pairs, rich);
  const bounds = [0, ...splits, n];
  const bw = new BitWriter(n);
  const fixedLitCodes = canonicalCodes(FIXED_LIT_LEN).codes;
  const fixedDistCodes = canonicalCodes(FIXED_DIST_LEN).codes;
  for (let b = 0; b < bounds.length - 1; b++) {
    const from = bounds[b];
    const to = bounds[b + 1];
    const last = b === bounds.length - 2;
    const r = refineParse(data, candsRich, from, to, blockIters, scratch, g.litLen, g.distLen);
    const dynBits = 3 + dynamicHeaderBits(r.litLen, r.distLen) + bodyBits(data, r.ops, r.litLen, r.distLen);
    const fixBits = 3 + bodyBits(data, r.ops, FIXED_LIT_LEN, FIXED_DIST_LEN);
    bw.put(last ? 1 : 0, 1);
    if (dynBits <= fixBits) {
      bw.put(2, 2);
      writeDynamicHeader(bw, r.litLen, r.distLen);
      const dc = canonicalCodes(r.litLen).codes;
      const dd = canonicalCodes(r.distLen).codes;
      writeOps(bw, data, r.ops, dc, r.litLen, dd, r.distLen);
    } else {
      bw.put(1, 2);
      writeOps(bw, data, r.ops, fixedLitCodes, FIXED_LIT_LEN, fixedDistCodes, FIXED_DIST_LEN);
    }
  }
  const raw = bw.bytes();
  const out = new Uint8Array(raw.length + 6);
  out[0] = 0x78;
  out[1] = 0xda;
  out.set(raw, 2);
  const ad = adler32(data);
  out[out.length - 4] = (ad >>> 24) & 0xff;
  out[out.length - 3] = (ad >>> 16) & 0xff;
  out[out.length - 2] = (ad >>> 8) & 0xff;
  out[out.length - 1] = ad & 0xff;
  return out.length < z9.length ? out : z9;
}
