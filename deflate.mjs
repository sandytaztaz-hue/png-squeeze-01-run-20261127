// deflate.mjs — a from-scratch optimal-parse DEFLATE encoder (RFC 1951) plus the
// small helpers the PNG writer needs. Pure Node standard library, no clock, no
// randomness, no I/O: the same input bytes always produce the same output bytes.
//
// The encoder works in three passes over the input:
//   1. a hash-chain walk finds, at every position, the longest match and the
//      closest match (smallest distance with length >= 3). The result is cached,
//      so later passes never walk a chain again;
//   2. a dynamic-programming parse picks literals and matches by true bit cost,
//      using a cost model (Huffman bit lengths) that is refined over a few
//      iterations from the previous parse's symbol frequencies;
//   3. the best parse seen is written as one block, dynamic or fixed Huffman,
//      whichever is smaller in bytes, and wrapped in a zlib stream.
//
// Length and distance code tables are the fixed tables of the DEFLATE format.

// Length codes 257..285: base length and extra bits for each.
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
// Distance codes 0..29: base distance and extra bits for each.
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
// The order the dynamic header writes the code-length code's lengths in.
const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
// Fixed Huffman bit lengths (RFC 1951 section 3.2.6).
const FIXED_LIT_LEN = new Uint8Array(288);
for (let s = 0; s < 144; s++) FIXED_LIT_LEN[s] = 8;
for (let s = 144; s < 256; s++) FIXED_LIT_LEN[s] = 9;
for (let s = 256; s < 280; s++) FIXED_LIT_LEN[s] = 7;
for (let s = 280; s < 288; s++) FIXED_LIT_LEN[s] = 8;
const FIXED_DIST_LEN = new Uint8Array(32).fill(5);

// Lookup: match length (3..258) -> length symbol, and the extra-bits value/count.
// (16-bit: length symbols run 257..285, past a byte's range.)
const LEN_SYM = new Uint16Array(259);
const LEN_EXT_VAL = new Uint8Array(259);
const LEN_EXT_BITS = new Uint8Array(259);
for (let k = 0; k < 29; k++) {
  for (let v = 0; v < (1 << LEN_EXTRA[k]); v++) {
    const len = LEN_BASE[k] + v;
    if (len < 259) { LEN_SYM[len] = 257 + k; LEN_EXT_VAL[len] = v; LEN_EXT_BITS[len] = LEN_EXTRA[k]; }
  }
}
LEN_SYM[258] = 285; LEN_EXT_VAL[258] = 0; LEN_EXT_BITS[258] = 0;
// Lookup: distance (1..32768) -> distance symbol, extra-bits value/count.
const DIST_SYM = new Uint8Array(32769);
const DIST_EXT_VAL = new Uint16Array(32769);
const DIST_EXT_BITS = new Uint8Array(32769);
for (let k = 0; k < 30; k++) {
  for (let v = 0; v < (1 << DIST_EXTRA[k]); v++) {
    const d = DIST_BASE[k] + v;
    if (d <= 32768) { DIST_SYM[d] = k; DIST_EXT_VAL[d] = v; DIST_EXT_BITS[d] = DIST_EXTRA[k]; }
  }
}

/** Adler-32 of bytes (zlib's checksum), as an unsigned 32-bit number. */
export function adler32(bytes) {
  let a = 1, b = 0;
  for (let i = 0; i < bytes.length;) {
    const end = Math.min(bytes.length, i + 5552);
    for (; i < end; i++) { a += bytes[i]; b += a; }
    a %= 65521; b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

/** Reverse the low `len` bits of `code` (DEFLATE writes Huffman codes starting with their most significant bit). */
function reverseBits(code, len) {
  let r = 0;
  for (let i = 0; i < len; i++) { r = (r << 1) | (code & 1); code >>>= 1; }
  return r;
}

/** A bit writer: bits go out least-significant-bit first within each byte. */
class BitWriter {
  constructor(capacity) {
    this.buf = new Uint8Array(capacity);
    this.pos = 0;
    this.bitBuf = 0;
    this.bitCnt = 0;
  }
  writeBits(value, count) {
    if (count === 0) return;
    this.bitBuf |= (value & ((1 << count) - 1)) << this.bitCnt;
    this.bitCnt += count;
    while (this.bitCnt >= 8) {
      this.buf[this.pos++] = this.bitBuf & 0xff;
      this.bitBuf >>>= 8;
      this.bitCnt -= 8;
    }
  }
  /** Write a Huffman code of `len` bits, most significant bit first. */
  writeCode(reversedCode, len) { this.writeBits(reversedCode, len); }
  align() {
    if (this.bitCnt > 0) { this.buf[this.pos++] = this.bitBuf & 0xff; this.bitBuf = 0; this.bitCnt = 0; }
  }
  bytes() { return this.buf.subarray(0, this.pos); }
}

/**
 * Canonical Huffman codes from bit lengths: returns { codes, rev } where codes[s]
 * is the code value and rev[s] is the same code with its bits reversed, ready for
 * the bit writer. Lengths of 0 mean the symbol is unused.
 */
function canonicalCodes(lengths) {
  const n = lengths.length;
  let maxLen = 0;
  for (let s = 0; s < n; s++) if (lengths[s] > maxLen) maxLen = lengths[s];
  const blCount = new Int32Array(maxLen + 1);
  for (let s = 0; s < n; s++) if (lengths[s] > 0) blCount[lengths[s]]++;
  const nextCode = new Int32Array(maxLen + 1);
  let code = 0;
  for (let bits = 1; bits <= maxLen; bits++) { code = (code + blCount[bits - 1]) << 1; nextCode[bits] = code; }
  const codes = new Int32Array(n);
  const rev = new Int32Array(n);
  for (let s = 0; s < n; s++) {
    const l = lengths[s];
    if (l > 0) { codes[s] = nextCode[l]; nextCode[l]++; rev[s] = reverseBits(codes[s], l); }
  }
  return { codes, rev, maxLen };
}

/**
 * Length-limited Huffman code lengths by package-merge (Moffat-Turpin): the
 * optimal code with every length at most `maxBits`, for the given symbol
 * frequencies. `freq` is an array of counts; the result is a Uint8Array of the
 * same length, 0 for symbols with count 0. Deterministic: ties break by symbol.
 *
 * How it works: the symbols are sorted by weight; list 0 holds one item per
 * symbol. Each later list is made by packaging the previous list (pairing
 * adjacent items, summing weights, joining their symbol sets; a leftover odd
 * item is dropped) and merging the packages back with list 0. After maxBits-1
 * rounds, a symbol's code length is the number of items in the final list
 * whose symbol set holds it.
 */
export function huffmanLengths(freq, maxBits) {
  const n = freq.length;
  const lengths = new Uint8Array(n);
  const syms = [];
  for (let s = 0; s < n; s++) if (freq[s] > 0) syms.push(s);
  if (syms.length === 0) return lengths;
  if (syms.length === 1) { lengths[syms[0]] = 1; return lengths; }
  // Sort symbols by frequency, then by symbol, so every tie is settled the same way.
  syms.sort((a, b) => (freq[a] - freq[b]) || (a - b));
  // One list, each item { w, set } with set the symbols the item covers. Every
  // list is kept to its smallest 2n-2 items, which is what makes the final
  // list's counts the code lengths.
  const keep = 2 * syms.length - 2;
  let list = syms.map((s) => ({ w: freq[s], set: [s] }));
  const byWeight = (x, y) => (x.w - y.w) || (x.set[0] - y.set[0]);
  for (let round = 1; round < maxBits; round++) {
    // Package: pair adjacent items of the previous list.
    const packed = [];
    for (let i = 0; i + 1 < list.length; i += 2) {
      packed.push({ w: list[i].w + list[i + 1].w, set: list[i].set.concat(list[i + 1].set) });
    }
    if (packed.length === 0) break;
    // Merge the packages with list 0 (the singletons), keeping weight order.
    const singles = syms.map((s) => ({ w: freq[s], set: [s] }));
    const merged = [];
    let a = 0, b = 0;
    while (a < packed.length && b < singles.length) {
      if (byWeight(packed[a], singles[b]) <= 0) merged.push(packed[a++]);
      else merged.push(singles[b++]);
    }
    while (a < packed.length) merged.push(packed[a++]);
    while (b < singles.length) merged.push(singles[b++]);
    list = merged.length > keep ? merged.slice(0, keep) : merged;
    if (list.length <= 2) break;
  }
  for (const item of list) for (const s of item.set) lengths[s]++;
  return lengths;
}

/** Cost model from bit lengths: a symbol's cost is its length, or 15 bits when unused (never free, never infinite). */
function costFromLengths(lengths, fallback) {
  const cost = new Float64Array(lengths.length);
  for (let s = 0; s < lengths.length; s++) cost[s] = lengths[s] > 0 ? lengths[s] : fallback;
  return cost;
}

/**
 * Hash-chain match search over the whole stream, once. For every position it
 * records the longest match (length, distance) and the closest match (the
 * smallest distance whose length is at least 3). The chains hold the most
 * recent position first, so the first candidate with a real length is the
 * closest match. Candidates are rejected cheaply: a candidate can only beat
 * the best length found so far when its byte at that length matches, so most
 * chain steps cost a single comparison. A match that reaches the longest
 * possible length stops the walk at once, and a good match shortens the
 * remaining walk, which is what keeps long runs of equal bytes cheap.
 *
 * `chainCap` bounds the walk at each position; `niceLen` (default 258) is the
 * length at which the walk stops early.
 */
export function findMatches(data, chainCap, niceLen = 258) {
  const n = data.length;
  const head = new Int32Array(32768).fill(-1);
  const prev = new Int32Array(n);
  const longLen = new Uint16Array(n);
  const longDist = new Uint16Array(n);
  const closeLen = new Uint16Array(n);
  const closeDist = new Uint16Array(n);
  // The Pareto frontier of (length, distance) at each position: every time the
  // walk finds a longer match than any nearer candidate, that (length,
  // distance) is a frontier point — a shorter match at a nearer distance can
  // be cheaper than the longest match at a far one. Up to four points, kept
  // in walk order (increasing distance and length); the first is the closest
  // match and the last the longest, so the middle points are the useful new
  // ones. Recording them is free: they are exactly the candidates whose full
  // length the walk already measures.
  const NF = 4;
  const fLen = new Uint16Array(n * NF);
  const fDist = new Uint16Array(n * NF);
  const last = n - 3; // positions past this hold no 3-byte hash
  for (let pos = 0; pos <= last; pos++) {
    const h = ((data[pos] << 10) ^ (data[pos + 1] << 5) ^ data[pos + 2]) & 0x7fff;
    let cand = head[h];
    const maxLen = Math.min(258, n - pos);
    let bestLen = 2;
    let bestDist = 0;
    let cLen = 0;
    let cDist = 0;
    let fCount = 0;
    let tries = 0;
    let limit = chainCap;
    while (cand >= 0 && pos - cand <= 32768 && tries < limit) {
      tries++;
      const dist = pos - cand;
      // A candidate is only measured when it can beat the longest match, and
      // the closest match still needs its true length even when it cannot.
      if ((bestLen < maxLen && data[cand + bestLen] === data[pos + bestLen]) || cLen === 0) {
        let len = 0;
        while (len < maxLen && data[pos + len] === data[cand + len]) len++;
        if (len >= 3 && cLen === 0) { cLen = len; cDist = dist; }
        if (len > bestLen) {
          bestLen = len;
          bestDist = dist;
          // A new record: a frontier point.
          if (fCount < NF) {
            fLen[pos * NF + fCount] = len;
            fDist[pos * NF + fCount] = dist;
            fCount++;
          } else {
            // Keep the closest point and the three most recent records.
            fLen[pos * NF + 1] = fLen[pos * NF + 2];
            fDist[pos * NF + 1] = fDist[pos * NF + 2];
            fLen[pos * NF + 2] = fLen[pos * NF + 3];
            fDist[pos * NF + 2] = fDist[pos * NF + 3];
            fLen[pos * NF + 3] = len;
            fDist[pos * NF + 3] = dist;
          }
          if (len >= niceLen || len >= maxLen) break;
          if (len >= 32) limit = Math.min(limit, tries + 16);
        }
      }
      cand = prev[cand];
    }
    if (bestLen >= 3) { longLen[pos] = bestLen; longDist[pos] = bestDist; }
    if (cLen >= 3) { closeLen[pos] = cLen; closeDist[pos] = cDist; }
    // Insert this position for later positions to find.
    prev[pos] = head[h];
    head[h] = pos;
  }
  // nextGood[i]: the smallest j >= i whose longest match is at least GOOD
  // bytes, or -1; prevGood[i]: the largest j <= i with that property, or -1.
  // The parse uses them to end a match where a good match starts.
  const GOOD = 8;
  const nextGood = new Int32Array(n + 2).fill(-1);
  for (let i = n - 1; i >= 0; i--) nextGood[i] = longLen[i] >= GOOD ? i : nextGood[i + 1];
  const prevGood = new Int32Array(n + 2).fill(-1);
  for (let i = 0; i < n; i++) prevGood[i] = longLen[i] >= GOOD ? i : (i > 0 ? prevGood[i - 1] : -1);
  return { longLen, longDist, closeLen, closeDist, nextGood, prevGood, fLen, fDist, NF };
}

/**
 * The cost model for one dynamic-programming pass: the bit cost of every match
 * length and every distance, from the current literal/length and distance bit
 * lengths. `lenCost[l]` is the cost of the length symbol for length l plus its
 * extra bits; `distCost[d]` the same for distance d.
 */
function buildMatchCosts(litCost, distCost) {
  const lenCost = new Float64Array(259);
  for (let l = 3; l <= 258; l++) lenCost[l] = litCost[LEN_SYM[l]] + LEN_EXT_BITS[l];
  const distCostArr = new Float64Array(32769);
  for (let d = 1; d <= 32768; d++) distCostArr[d] = distCost[DIST_SYM[d]] + DIST_EXT_BITS[d];
  return { lenCost, distCost: distCostArr };
}

/**
 * The dynamic-programming parse: the cheapest way to encode `data` with the
 * given cost model, walking every position (including positions inside a long
 * match, so a match can start there). From each position the transitions are
 * the literal, the longest match (at its full length and the two lengths below
 * it, same distance) and the closest match (at its length and the one below
 * it, when its distance differs). Symbols are stored as two parallel arrays:
 * `symLen` (1 for a literal, otherwise the match length) and `symVal` (the
 * literal byte, or the match distance). Returns the symbols, their
 * frequencies, and the parse's bit cost under this model, without the
 * end-of-block symbol.
 */
export function optimalParse(data, m, litCost, distCost, mode = 'short') {
  const n = data.length;
  const { lenCost, distCost: distPart } = buildMatchCosts(litCost, distCost);
  const cost = new Float64Array(n + 1);
  cost.fill(Infinity);
  cost[0] = 0;
  const choiceLen = new Uint16Array(n + 1);
  const choiceDist = new Uint16Array(n + 1);
  const { longLen, longDist, closeLen, closeDist, nextGood, prevGood, fLen, fDist, NF } = m;
  for (let i = 0; i < n; i++) {
    const ci = cost[i];
    if (ci === Infinity) continue;
    const litC = ci + litCost[data[i]];
    if (litC < cost[i + 1]) { cost[i + 1] = litC; choiceLen[i + 1] = 1; choiceDist[i + 1] = 0; }
    const L = longLen[i];
    if (L >= 3) {
      const D = longDist[i];
      const base = ci + distPart[D];
      const low = mode === 'all' ? 3 : (L - 2 < 3 ? 3 : L - 2);
      for (let l = L; l >= low; l--) {
        const c = base + lenCost[l];
        const j = i + l;
        if (c < cost[j]) { cost[j] = c; choiceLen[j] = l; choiceDist[j] = D; }
      }
      if (mode === 'good') {
        // Lengths ending where a good match starts, so the next match can
        // begin there: the first few good starts after this match begins, and
        // the last few before it ends. Bounded, so a long run of good starts
        // does not turn this into the all-lengths walk.
        const end = i + L;
        let j = nextGood[i + 3];
        for (let k = 0; k < 4 && j !== -1 && j <= end; k++) {
          const l = j - i;
          if (l < L - 2 && l >= 3) {
            const c = base + lenCost[l];
            if (c < cost[j]) { cost[j] = c; choiceLen[j] = l; choiceDist[j] = D; }
          }
          j = nextGood[j + 1];
        }
        j = prevGood[end];
        for (let k = 0; k < 4 && j !== -1 && j > i + 2; k++) {
          const l = j - i;
          if (l < L - 2 && l >= 3) {
            const c = base + lenCost[l];
            if (c < cost[j]) { cost[j] = c; choiceLen[j] = l; choiceDist[j] = D; }
          }
          j = prevGood[j - 1];
        }
      }
    }
    const Cl = closeLen[i];
    const Cd = closeDist[i];
    if (Cl >= 3 && Cd !== longDist[i]) {
      const base = ci + distPart[Cd];
      const low = mode === 'all' ? 3 : (Cl - 1 < 3 ? 3 : Cl - 1);
      for (let l = Cl; l >= low; l--) {
        const c = base + lenCost[l];
        const j = i + l;
        if (c < cost[j]) { cost[j] = c; choiceLen[j] = l; choiceDist[j] = Cd; }
      }
    }
    // The Pareto frontier: a shorter match at a nearer distance can be
    // cheaper than the longest match at a far one. Full length only, so this
    // adds a few transitions per position.
    const fi = i * NF;
    for (let f = 0; f < NF; f++) {
      const fl = fLen[fi + f];
      const fd = fDist[fi + f];
      if (fl >= 3 && fd !== longDist[i] && fd !== Cd) {
        const c = ci + distPart[fd] + lenCost[fl];
        const j = i + fl;
        if (c < cost[j]) { cost[j] = c; choiceLen[j] = fl; choiceDist[j] = fd; }
      }
    }
  }
  // Backtrack from the end, filling the symbol lists in order.
  let count = 0;
  for (let j = n; j > 0;) { count++; j -= choiceLen[j]; }
  const symLen = new Uint16Array(count);
  const symVal = new Uint16Array(count);
  let k = count;
  for (let j = n; j > 0;) {
    const l = choiceLen[j];
    k--;
    symLen[k] = l;
    symVal[k] = l === 1 ? data[j - 1] : choiceDist[j];
    j -= l;
  }
  const freqLit = new Int32Array(288);
  const freqDist = new Int32Array(32);
  for (let s = 0; s < count; s++) {
    const l = symLen[s];
    if (l === 1) freqLit[symVal[s]]++;
    else { freqLit[LEN_SYM[l]]++; freqDist[DIST_SYM[symVal[s]]]++; }
  }
  freqLit[256]++; // end of block
  return { symLen, symVal, count, freqLit, freqDist, bits: cost[n] + litCost[256] };
}

/**
 * The RLE of the literal/length and distance bit lengths for a dynamic block
 * header. Returns the trimmed counts (hlit literal lengths, hdist distance
 * lengths), the RLE entries as [symbol, extra value, extra bit count] triples,
 * and the frequencies of the code-length symbols the entries use.
 */
function rleLengths(litLengths, distLengths) {
  let hlit = 287;
  while (hlit > 257 && litLengths[hlit - 1] === 0) hlit--;
  let hdist = 30;
  while (hdist > 1 && distLengths[hdist - 1] === 0) hdist--;
  const lens = new Uint8Array(hlit + hdist);
  lens.set(litLengths.subarray(0, hlit));
  lens.set(distLengths.subarray(0, hdist), hlit);
  const entries = [];
  const freq = new Int32Array(19);
  let i = 0;
  while (i < lens.length) {
    const v = lens[i];
    let run = 1;
    while (i + run < lens.length && lens[i + run] === v) run++;
    if (v === 0) {
      let r = run;
      while (r >= 11) { const take = Math.min(r, 138); entries.push([18, take - 11, 7]); freq[18]++; r -= take; }
      if (r >= 3) { entries.push([17, r - 3, 3]); freq[17]++; r = 0; }
      while (r > 0) { entries.push([0, 0, 0]); freq[0]++; r--; }
    } else {
      entries.push([v, 0, 0]); freq[v]++;
      let r = run - 1;
      while (r >= 3) { const take = Math.min(r, 6); entries.push([16, take - 3, 2]); freq[16]++; r -= take; }
      while (r > 0) { entries.push([v, 0, 0]); freq[v]++; r--; }
    }
    i += run;
  }
  return { hlit, hdist, entries, freq };
}

/**
 * The exact bit size of one dynamic block and of one fixed block holding
 * `parse` with the given bit lengths, plus everything the emitter needs for
 * the dynamic header. The dynamic size includes the whole header.
 */
function blockSizes(parse, litLengths, distLengths) {
  const { symLen, symVal, count } = parse;
  const rle = rleLengths(litLengths, distLengths);
  let clLengths = huffmanLengths(rle.freq, 7);
  // The code-length code needs at least two symbols to be a complete code.
  let used = 0;
  for (let s = 0; s < 19; s++) if (clLengths[s] > 0) used++;
  if (used === 1) {
    for (const s of CL_ORDER) {
      if (clLengths[s] === 0) { clLengths[s] = 1; break; }
    }
  }
  let hclen = 4;
  for (let k = 4; k < 19; k++) if (clLengths[CL_ORDER[k]] > 0) hclen = k + 1;
  let dynBits = 3 + 5 + 5 + 4 + hclen * 3;
  for (const [sym, , extraBits] of rle.entries) dynBits += clLengths[sym] + extraBits;
  let fixedBits = 3;
  for (let s = 0; s < count; s++) {
    const l = symLen[s];
    if (l === 1) {
      dynBits += litLengths[symVal[s]];
      fixedBits += FIXED_LIT_LEN[symVal[s]];
    } else {
      dynBits += litLengths[LEN_SYM[l]] + LEN_EXT_BITS[l] + distLengths[DIST_SYM[symVal[s]]] + DIST_EXT_BITS[symVal[s]];
      fixedBits += FIXED_LIT_LEN[LEN_SYM[l]] + LEN_EXT_BITS[l] + 5 + DIST_EXT_BITS[symVal[s]];
    }
  }
  dynBits += litLengths[256];
  fixedBits += FIXED_LIT_LEN[256];
  return { dynBits, fixedBits, dynBytes: (dynBits + 7) >> 3, fixedBytes: (fixedBits + 7) >> 3, rle, clLengths, hclen };
}

/** Write one block (dynamic or fixed) holding `parse` into the bit writer.
 * `final` marks the last block of the DEFLATE stream; only the last block is
 * byte-aligned, since blocks are bit-packed back to back. */
function emitBlock(w, parse, litLengths, distLengths, sizes, dynamic, final) {
  const { symLen, symVal, count } = parse;
  if (dynamic) {
    const litCodes = canonicalCodes(litLengths);
    const distCodes = canonicalCodes(distLengths);
    const clCodes = canonicalCodes(sizes.clLengths);
    const { hlit, hdist, entries } = sizes.rle;
    w.writeBits(final ? 1 : 0, 1);
    w.writeBits(2, 2); // BTYPE 10, dynamic
    w.writeBits(hlit - 257, 5);
    w.writeBits(hdist - 1, 5);
    w.writeBits(sizes.hclen - 4, 4);
    for (let k = 0; k < sizes.hclen; k++) w.writeBits(sizes.clLengths[CL_ORDER[k]], 3);
    for (const [sym, extra, extraBits] of entries) {
      w.writeCode(clCodes.rev[sym], sizes.clLengths[sym]);
      if (extraBits > 0) w.writeBits(extra, extraBits);
    }
    for (let s = 0; s < count; s++) {
      const l = symLen[s];
      if (l === 1) {
        w.writeCode(litCodes.rev[symVal[s]], litLengths[symVal[s]]);
      } else {
        w.writeCode(litCodes.rev[LEN_SYM[l]], litLengths[LEN_SYM[l]]);
        if (LEN_EXT_BITS[l] > 0) w.writeBits(LEN_EXT_VAL[l], LEN_EXT_BITS[l]);
        w.writeCode(distCodes.rev[DIST_SYM[symVal[s]]], distLengths[DIST_SYM[symVal[s]]]);
        if (DIST_EXT_BITS[symVal[s]] > 0) w.writeBits(DIST_EXT_VAL[symVal[s]], DIST_EXT_BITS[symVal[s]]);
      }
    }
    w.writeCode(litCodes.rev[256], litLengths[256]);
  } else {
    const fixedLit = canonicalCodes(FIXED_LIT_LEN);
    const fixedDist = canonicalCodes(FIXED_DIST_LEN);
    w.writeBits(final ? 1 : 0, 1);
    w.writeBits(1, 2); // BTYPE 01, fixed
    for (let s = 0; s < count; s++) {
      const l = symLen[s];
      if (l === 1) {
        w.writeCode(fixedLit.rev[symVal[s]], FIXED_LIT_LEN[symVal[s]]);
      } else {
        w.writeCode(fixedLit.rev[LEN_SYM[l]], FIXED_LIT_LEN[LEN_SYM[l]]);
        if (LEN_EXT_BITS[l] > 0) w.writeBits(LEN_EXT_VAL[l], LEN_EXT_BITS[l]);
        w.writeCode(fixedDist.rev[DIST_SYM[symVal[s]]], 5);
        if (DIST_EXT_BITS[symVal[s]] > 0) w.writeBits(DIST_EXT_VAL[symVal[s]], DIST_EXT_BITS[symVal[s]]);
      }
    }
    w.writeCode(fixedLit.rev[256], FIXED_LIT_LEN[256]);
  }
  if (final) w.align();
}

/**
 * The best parse of `data`: the match search runs once, then the
 * dynamic-programming parse is refined over `iterations` cost-model rounds,
 * keeping the parse whose emitted block (dynamic or fixed, whichever is
 * smaller) is smallest. Returns the parse, its Huffman lengths, the block
 * sizes and the block size in bytes.
 */
export function bestParse(data, { chainCap = 256, iterations = 3, mode = 'short' } = {}) {
  const m = findMatches(data, chainCap);
  let litCost = new Float64Array(FIXED_LIT_LEN);
  let distCost = new Float64Array(32).fill(5);
  let best = null;
  for (let it = 0; it < iterations; it++) {
    const parse = optimalParse(data, m, litCost, distCost, mode);
    const litLengths = huffmanLengths(parse.freqLit, 15);
    const distLengths = huffmanLengths(parse.freqDist, 15);
    if (parse.freqDist.every((f) => f === 0)) distLengths[0] = 1; // no matches: one dummy distance code
    const sizes = blockSizes(parse, litLengths, distLengths);
    const bytes = Math.min(sizes.dynBytes, sizes.fixedBytes);
    if (best === null || bytes < best.bytes) best = { parse, litLengths, distLengths, sizes, bytes };
    litCost = costFromLengths(litLengths, 15);
    distCost = costFromLengths(distLengths, 15);
  }
  best.dynamic = best.sizes.dynBytes <= best.sizes.fixedBytes;
  return best;
}

/** The best DEFLATE stream of `data` as a single block. */
export function deflateBest(data, opts = {}) {
  const best = bestParse(data, opts);
  const w = new BitWriter(best.bytes + 16);
  emitBlock(w, best.parse, best.litLengths, best.distLengths, best.sizes, best.dynamic, true);
  return { raw: w.bytes(), bytes: best.bytes, dynamic: best.dynamic, litLengths: best.litLengths, distLengths: best.distLengths };
}

/**
 * The best DEFLATE stream of `data` split into `parts` equal blocks, each
 * with its own Huffman tree, bit-packed into one stream. A split only helps
 * when the stream's statistics change along its length; callers choose the
 * part count per stream.
 */
export function deflateBestSplit(data, parts, opts = {}) {
  const n = data.length;
  const segs = [];
  const chunk = Math.ceil(n / parts);
  for (let s = 0; s < parts; s++) {
    const start = s * chunk;
    if (start >= n) break;
    segs.push(data.subarray(start, Math.min(n, start + chunk)));
  }
  const bests = segs.map((seg) => bestParse(seg, opts));
  const total = bests.reduce((a, b) => a + b.bytes, 0);
  const w = new BitWriter(total + 16);
  bests.forEach((b, i) => {
    emitBlock(w, b.parse, b.litLengths, b.distLengths, b.sizes, b.dynamic, i === bests.length - 1);
  });
  const raw = w.bytes();
  return { raw, bytes: raw.length, parts: bests.length };
}

/** The zlib stream of `data` (header 0x78 0x9C, DEFLATE, Adler-32). */
export function deflateZlib(data, opts = {}) {
  const { raw, bytes, litLengths, distLengths } = deflateBest(data, opts);
  const out = new Uint8Array(bytes + 6);
  out[0] = 0x78;
  out[1] = 0x9c;
  out.set(raw, 2);
  const adler = adler32(data);
  out[bytes + 2] = (adler >>> 24) & 0xff;
  out[bytes + 3] = (adler >>> 16) & 0xff;
  out[bytes + 4] = (adler >>> 8) & 0xff;
  out[bytes + 5] = adler & 0xff;
  return { zlib: out, bytes: bytes + 6, litLengths, distLengths };
}

/** The zlib stream of `data`, split into `parts` DEFLATE blocks. */
export function deflateZlibSplit(data, parts, opts = {}) {
  const { raw, bytes } = deflateBestSplit(data, parts, opts);
  const out = new Uint8Array(bytes + 6);
  out[0] = 0x78;
  out[1] = 0x9c;
  out.set(raw, 2);
  const adler = adler32(data);
  out[bytes + 2] = (adler >>> 24) & 0xff;
  out[bytes + 3] = (adler >>> 16) & 0xff;
  out[bytes + 4] = (adler >>> 8) & 0xff;
  out[bytes + 5] = adler & 0xff;
  return { zlib: out, bytes: bytes + 6 };
}
