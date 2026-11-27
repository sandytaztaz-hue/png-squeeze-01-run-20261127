// deflate.mjs — a from-scratch DEFLATE encoder (optimal-parse, zopfli-style).
// Pure Node standard library. Deterministic: fixed budgets only, no clock,
// no randomness. Written for the png-squeeze entry: it takes filtered PNG
// row data and returns a zlib stream.
//
// Design:
//   1. Match search: one left-to-right pass over the data with a hash table
//      of 3-byte sequences and chains of previous positions. At each position
//      the walk records the Pareto frontier of (length, distance) pairs:
//      distances grow as the chain is walked (positions strictly decrease),
//      so a candidate only matters when its length beats every length seen
//      at a nearer distance. The frontier is cached and reused by every
//      dynamic-programming pass.
//   2. Optimal parse: a shortest-path DP over the data with true bit costs
//      (literal / length / distance symbol costs from the current Huffman
//      tables). Iterated: start from fixed-Huffman costs, re-parse, rebuild
//      the Huffman tables from the parse's frequencies, re-parse again.
//   3. Block splitting: the data is cut into a fixed number of uniform
//      blocks; each block gets its own Huffman tables, and each block is
//      emitted either as a dynamic-Huffman block or a fixed-Huffman block,
//      whichever is exactly smaller in bits.
//   4. Huffman lengths are built with a heap and then length-limited to 15
//      with the classic overflow redistribution.

const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];

// Length code (257..285) and extra-bit count for every match length 3..258.
const LEN_CODE = new Uint16Array(259);
// Right endpoint of each length code's range (lengths 3..258).
const RANGE_END = LEN_BASE.map((b, c) => (c === 28 ? 258 : LEN_BASE[c + 1] - 1));
const LEN_EXT = new Uint8Array(259);
for (let c = 0; c < 29; c++) {
  const span = c === 28 ? 1 : LEN_BASE[c + 1] - LEN_BASE[c];
  for (let k = 0; k < span; k++) {
    LEN_CODE[LEN_BASE[c] + k] = 257 + c;
    LEN_EXT[LEN_BASE[c] + k] = LEN_EXTRA[c];
  }
}
// Distance code (0..29) and extra-bit count for every distance 1..32768.
const DIST_CODE = new Uint8Array(32769);
const DIST_EXT = new Uint8Array(32769);
for (let c = 0; c < 30; c++) {
  const span = c === 29 ? 32768 - DIST_BASE[c] + 1 : DIST_BASE[c + 1] - DIST_BASE[c];
  for (let k = 0; k < span; k++) {
    DIST_CODE[DIST_BASE[c] + k] = c;
    DIST_EXT[DIST_BASE[c] + k] = DIST_EXTRA[c];
  }
}
// Fixed-Huffman code lengths (DEFLATE spec).
const FIXED_LIT_LEN = new Uint8Array(288);
for (let i = 0; i < 144; i++) FIXED_LIT_LEN[i] = 8;
for (let i = 144; i < 256; i++) FIXED_LIT_LEN[i] = 9;
for (let i = 256; i < 280; i++) FIXED_LIT_LEN[i] = 7;
for (let i = 280; i < 288; i++) FIXED_LIT_LEN[i] = 8;
const FIXED_DIST_LEN = new Uint8Array(30).fill(5);

const MAX_MATCH = 258;
const MIN_MATCH = 3;
const WINDOW = 32768;
const HASH_BITS = 20;
const HASH_SIZE = 1 << HASH_BITS;
const HASH_MASK = HASH_SIZE - 1;

function hash3(a, b, c) {
  // A cheap 3-byte mix; collisions only cost a wasted comparison.
  return (((a << 10) ^ (b << 5) ^ c) * 2654435761) >>> (32 - HASH_BITS) & HASH_MASK;
}

// Length of the match between data[i..] and data[j..], at most maxLen.
// The caller guarantees data[i + best] and data[j + best] were already
// compared when best > 0, so this only runs when a longer match is possible.
// When i and j share their alignment mod 4, the bulk of the comparison
// runs four bytes at a time through a 32-bit view; otherwise it falls
// back to the byte loop.
function matchLength(data, u32, i, j, maxLen) {
  let l = 0;
  if (u32 !== null && (i & 3) === (j & 3)) {
    const align = (4 - (i & 3)) & 3;
    while (l < align && l < maxLen && data[i + l] === data[j + l]) l++;
    if (l < align) return l;
    while (l + 4 <= maxLen) {
      if (u32[(i + l) >>> 2] !== u32[(j + l) >>> 2]) break;
      l += 4;
    }
    while (l < maxLen && data[i + l] === data[j + l]) l++;
    return l;
  }
  while (l < maxLen && data[i + l] === data[j + l]) l++;
  return l;
}

// One pass over the data: build the Pareto frontier of matches at every
// position. Returns { lens, dists, counts } with at most MAXF pairs per
// position, lens stored as length, dists as distance.
const MAXF = 32;
function findFrontiers(data, chainCap) {
  const n = data.length;
  const head = new Int32Array(HASH_SIZE).fill(-1);
  const prev = new Int32Array(n);
  const u32 = data.byteOffset % 4 === 0 ? new Uint32Array(data.buffer, data.byteOffset, data.length >>> 2) : null;
  const lens = new Uint16Array(n * MAXF);
  const dists = new Uint16Array(n * MAXF);
  const counts = new Uint8Array(n);
  const fLen = new Uint16Array(MAXF);
  const fDist = new Uint16Array(MAXF);
  for (let i = 0; i < n; i++) {
    if (i + MIN_MATCH > n) break;
    const h = hash3(data[i], data[i + 1], data[i + 2]);
    let j = head[h];
    head[h] = i;
    prev[i] = j;
    const maxLen = Math.min(MAX_MATCH, n - i);
    const minJ = i - WINDOW;
    let best = MIN_MATCH - 1; // best length found so far
    let f = 0;
    let walked = 0;
    // Loop-invariant reads, refreshed only when `best` grows.
    let targetByte = data[i + best];
    let targetByteM1 = data[i + best - 1];
    while (j >= 0 && j >= minJ && walked < chainCap) {
      walked++;
      const dist = i - j;
      if (best < maxLen && data[j + best] === targetByte && (best === 0 || data[j + best - 1] === targetByteM1)) {
        const l = matchLength(data, u32, i, j, maxLen);
        if (l > best) {
          best = l;
          targetByte = data[i + best];
          targetByteM1 = data[i + best - 1];
          if (f < MAXF) {
            fLen[f] = l;
            fDist[f] = dist;
            f++;
          }
          if (l >= MAX_MATCH) break;
        }
      }
      j = prev[j];
    }
    if (f > 0) {
      counts[i] = f;
      const base = i * MAXF;
      for (let k = 0; k < f; k++) {
        lens[base + k] = fLen[k];
        dists[base + k] = fDist[k];
      }
    }
  }
  return { lens, dists, counts };
}

// ---- Huffman lengths -------------------------------------------------------

// Build length-limited Huffman code lengths (max 15) from frequencies.
// Heap-based tree build, then the overflow redistribution: lengths over the
// cap are folded back down, and lengths are reassigned by frequency rank.
function buildLengths(freq, maxLen) {
  const n = freq.length;
  const lengths = new Uint8Array(n);
  let used = 0;
  for (let i = 0; i < n; i++) if (freq[i] > 0) used++;
  if (used === 0) return lengths;
  if (used === 1) {
    for (let i = 0; i < n; i++) if (freq[i] > 0) lengths[i] = 1;
    return lengths;
  }
  // Heap of node indices; leaves 0..n-1, internal nodes n.. .
  const weight = new Float64Array(2 * n);
  const depth = new Uint8Array(2 * n);
  const left = new Int32Array(2 * n).fill(-1);
  const right = new Int32Array(2 * n).fill(-1);
  for (let i = 0; i < n; i++) weight[i] = freq[i];
  const heap = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) heap.push(i);
  const less = (a, b) => weight[a] < weight[b] || (weight[a] === weight[b] && a < b);
  const push = (x) => {
    heap.push(x);
    let k = heap.length - 1;
    while (k > 0) {
      const p = (k - 1) >> 1;
      if (less(heap[k], heap[p])) {
        const t = heap[k]; heap[k] = heap[p]; heap[p] = t;
        k = p;
      } else break;
    }
  };
  const pop = () => {
    const top = heap[0];
    const last = heap.pop();
    if (heap.length > 0) {
      heap[0] = last;
      let k = 0;
      for (;;) {
        const l = k * 2 + 1, r = l + 1;
        let s = k;
        if (l < heap.length && less(heap[l], heap[s])) s = l;
        if (r < heap.length && less(heap[r], heap[s])) s = r;
        if (s === k) break;
        const t = heap[k]; heap[k] = heap[s]; heap[s] = t;
        k = s;
      }
    }
    return top;
  };
  // Heapify the initial leaves.
  for (let k = (heap.length >> 1) - 1; k >= 0; k--) {
    let p = k;
    for (;;) {
      const l = p * 2 + 1, r = l + 1;
      let s = p;
      if (l < heap.length && less(heap[l], heap[s])) s = l;
      if (r < heap.length && less(heap[r], heap[s])) s = r;
      if (s === p) break;
      const t = heap[p]; heap[p] = heap[s]; heap[s] = t;
      p = s;
    }
  }
  let next = n;
  while (heap.length > 1) {
    const a = pop();
    const b = pop();
    weight[next] = weight[a] + weight[b];
    left[next] = a;
    right[next] = b;
    depth[next] = 0;
    push(next);
    next++;
  }
  const root = heap[0];
  // Depths by walking the tree.
  const stack = [root];
  const dstack = [0];
  while (stack.length > 0) {
    const node = stack.pop();
    const d = dstack.pop();
    if (node < n) {
      lengths[node] = d;
    } else {
      stack.push(left[node]); dstack.push(d + 1);
      stack.push(right[node]); dstack.push(d + 1);
    }
  }
  // Length limiting: cap the over-long lengths, then repair the Kraft sum
  // back to exactly 1. Capping only raises the sum, so the repair only
  // ever needs to lower it. One repair step — split a code of length
  // m < maxLen into two of length m+1, and drop one code of length
  // maxLen — lowers the sum (in units of 2^-maxLen) by exactly 1, so
  // looping until the sum is 2^maxLen always terminates with a complete
  // code (a code shorter than maxLen always exists to split while the sum
  // is above 1, since at most 2^maxLen codes fit at length maxLen).
  const blCount = new Int32Array(maxLen + 1);
  for (let i = 0; i < n; i++) {
    if (lengths[i] > maxLen) lengths[i] = maxLen;
    if (lengths[i] > 0) blCount[lengths[i]]++;
  }
  const target = 1 << maxLen;
  let total = 0;
  for (let l = 1; l <= maxLen; l++) total += blCount[l] * (1 << (maxLen - l));
  while (total > target) {
    let m = maxLen - 1;
    while (m > 0 && blCount[m] === 0) m--;
    if (m === 0) break; // cannot happen for a feasible alphabet
    blCount[m]--;
    blCount[m + 1] += 2;
    blCount[maxLen]--;
    total -= 1;
  }
  // Reassign lengths by frequency rank: most frequent gets shortest.
  const order = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) order.push(i);
  order.sort((a, b) => freq[b] - freq[a] || a - b);
  let oi = 0;
  for (let l = 1; l <= maxLen; l++) {
    for (let k = 0; k < blCount[l]; k++) {
      lengths[order[oi++]] = l;
    }
  }
  return lengths;
}

// Canonical Huffman codes from lengths: returns { codes, lengths } with
// codes bit-reversed for LSB-first DEFLATE emission.
function canonicalCodes(lengths) {
  const n = lengths.length;
  const maxLen = Math.max(1, ...lengths);
  const blCount = new Int32Array(maxLen + 1);
  for (let i = 0; i < n; i++) if (lengths[i] > 0) blCount[lengths[i]]++;
  const nextCode = new Int32Array(maxLen + 1);
  let code = 0;
  for (let l = 1; l <= maxLen; l++) {
    code = (code + blCount[l - 1]) << 1;
    nextCode[l] = code;
  }
  const codes = new Uint32Array(n);
  for (let i = 0; i < n; i++) {
    const l = lengths[i];
    if (l === 0) continue;
    let c = nextCode[l]++;
    // Reverse l bits for LSB-first output.
    let r = 0;
    for (let k = 0; k < l; k++) {
      r = (r << 1) | (c & 1);
      c >>= 1;
    }
    codes[i] = r;
  }
  return { codes, lengths };
}

// ---- Bit writer -------------------------------------------------------------

class BitWriter {
  constructor(capacity) {
    this.out = new Uint8Array(capacity);
    this.pos = 0;
    this.bitBuf = 0;
    this.bitCnt = 0;
    this.bitLen = 0;
  }
  write(code, len) {
    this.bitLen += len;
    this.bitBuf |= code << this.bitCnt;
    this.bitCnt += len;
    while (this.bitCnt >= 8) {
      this.out[this.pos++] = this.bitBuf & 0xff;
      this.bitBuf >>>= 8;
      this.bitCnt -= 8;
    }
  }
  // Append another writer's bits (LSB-first packing) into this one.
  append(other) {
    const nBytes = Math.ceil(other.bitLen / 8);
    let remaining = other.bitLen;
    for (let i = 0; i < nBytes; i++) {
      const take = Math.min(8, remaining);
      this.writeBits(other.out[i], take);
      remaining -= take;
    }
  }
  writeBits(value, len) {
    // value's low `len` bits, LSB first.
    this.write(value & ((1 << len) - 1), len);
  }
  finish() {
    if (this.bitCnt > 0) {
      this.out[this.pos++] = this.bitBuf & 0xff;
      this.bitBuf = 0;
      this.bitCnt = 0;
    }
    return this.out.subarray(0, this.pos);
  }
}

// ---- Optimal parse ----------------------------------------------------------

// Per-symbol cost tables for one DP run, from Huffman lengths.
function costTables(litLen, distLen) {
  const litCost = new Float64Array(288);
  for (let i = 0; i < 288; i++) litCost[i] = litLen[i];
  const lenCost = new Float64Array(259);
  for (let l = 3; l <= 258; l++) lenCost[l] = litLen[LEN_CODE[l]] + LEN_EXT[l];
  const distCost = new Float64Array(32769);
  for (let d = 1; d <= 32768; d++) distCost[d] = distLen[DIST_CODE[d]] + DIST_EXT[d];
  return { litCost, lenCost, distCost };
}

// DP parse of data[start..end) using cached frontiers. Returns symbol
// arrays: lit[i] = literal byte (0..255) or -1; len[i] / dist[i] for a match.
// When `expand` is set, each frontier pair (length L0, distance D) also
// offers every shorter length that ends a length-code range (plus length
// 3): a match of length L0 at distance D contains every shorter length
// at the same distance, and within a length-code range the bit cost is
// constant, so the range's right endpoint dominates the rest of the range
// — except that the DP may need to end the match early to align with the
// next match, which is what the range endpoints give it.
function parseBlock(data, start, end, frontiers, tables, expand = false) {
  const len = end - start;
  const cost = new Float64Array(len + 1).fill(Infinity);
  const prevLen = new Uint16Array(len + 1);
  const prevDist = new Uint32Array(len + 1);
  cost[0] = 0;
  const { litCost, lenCost, distCost } = tables;
  const { lens, dists, counts } = frontiers;
  for (let i = 0; i < len; i++) {
    const base = cost[i];
    if (base === Infinity) continue;
    const pos = start + i;
    const remain = len - i;
    // Literal edge.
    const lc = base + litCost[data[pos]];
    if (lc < cost[i + 1]) {
      cost[i + 1] = lc;
      prevLen[i + 1] = 0;
      prevDist[i + 1] = 0;
    }
    // Match edges from the frontier.
    const fc = counts[pos];
    if (fc > 0 && remain >= 3) {
      const fb = pos * MAXF;
      for (let k = 0; k < fc; k++) {
        const L0 = lens[fb + k];
        const D = dists[fb + k];
        const dc = distCost[D];
        if (!expand) {
          let L = L0 > remain ? remain : L0;
          if (L >= 3) {
            const mc = base + lenCost[L] + dc;
            if (mc < cost[i + L]) {
              cost[i + L] = mc;
              prevLen[i + L] = L;
              prevDist[i + L] = D;
            }
          }
          continue;
        }
        let prevL = -1;
        for (let c = 0; c < 29; c++) {
          const lo = LEN_BASE[c];
          if (lo > L0) break;
          let L = RANGE_END[c];
          if (L > L0) L = L0;
          if (L > remain) L = remain;
          if (L < 3 || L === prevL) continue;
          prevL = L;
          const mc = base + lenCost[L] + dc;
          if (mc < cost[i + L]) {
            cost[i + L] = mc;
            prevLen[i + L] = L;
            prevDist[i + L] = D;
          }
        }
        // Length 3 itself, for alignment when the range endpoints overshoot.
        if (L0 >= 3 && prevL !== 3) {
          const mc = base + lenCost[3] + dc;
          if (mc < cost[i + 3]) {
            cost[i + 3] = mc;
            prevLen[i + 3] = 3;
            prevDist[i + 3] = D;
          }
        }
      }
    }
  }
  // Backtrack: count symbols, then fill arrays forward.
  let nSym = 0;
  let p = len;
  while (p > 0) {
    nSym++;
    p -= prevLen[p] === 0 ? 1 : prevLen[p];
  }
  const symLit = new Int16Array(nSym);
  const symLen = new Uint16Array(nSym);
  const symDist = new Uint16Array(nSym);
  let s = nSym - 1;
  p = len;
  while (p > 0) {
    const L = prevLen[p];
    if (L === 0) {
      symLit[s] = data[start + p - 1];
      symLen[s] = 0;
      symDist[s] = 0;
      p -= 1;
    } else {
      symLit[s] = -1;
      symLen[s] = L;
      symDist[s] = prevDist[p];
      p -= L;
    }
    s--;
  }
  return { symLit, symLen, symDist, nSym, cost: cost[len] + litCost[256] };
}

function frequencies(symLit, symLen, symDist, nSym) {
  const litFreq = new Float64Array(288);
  const distFreq = new Float64Array(30);
  for (let s = 0; s < nSym; s++) {
    if (symLit[s] >= 0) litFreq[symLit[s]]++;
    else {
      litFreq[LEN_CODE[symLen[s]]]++;
      distFreq[DIST_CODE[symDist[s]]]++;
    }
  }
  litFreq[256]++; // end of block
  return { litFreq, distFreq };
}

// Emit one block's symbols with the given tables into a BitWriter.
function emitBlock(bw, symLit, symLen, symDist, nSym, litCode, distCode, isLast) {
  bw.writeBits(isLast ? 1 : 0, 1);
  bw.writeBits(2, 2); // dynamic Huffman block
  // Build the code-length sequence over lit (trimmed) + dist (trimmed) lengths.
  const litLen = litCode.lengths;
  const distLen = distCode.lengths;
  let hlit = 286;
  while (hlit > 257 && litLen[hlit - 1] === 0) hlit--;
  let hdist = 30;
  while (hdist > 1 && distLen[hdist - 1] === 0) hdist--;
  const seq = new Uint8Array(hlit + hdist);
  seq.set(litLen.subarray(0, hlit));
  seq.set(distLen.subarray(0, hdist), hlit);
  // RLE the sequence with symbols 16/17/18.
  const clSyms = [];
  const clExtra = [];
  let i = 0;
  while (i < seq.length) {
    const v = seq[i];
    let run = 1;
    while (i + run < seq.length && seq[i + run] === v) run++;
    if (v === 0) {
      let left = run;
      while (left >= 11) {
        const take = Math.min(left, 138);
        clSyms.push(18); clExtra.push(take - 11);
        left -= take;
      }
      if (left >= 3) {
        clSyms.push(17); clExtra.push(left - 3);
        left = 0;
      }
      while (left-- > 0) { clSyms.push(0); clExtra.push(0); }
    } else {
      clSyms.push(v); clExtra.push(0);
      let left = run - 1;
      while (left >= 3) {
        const take = Math.min(left, 6);
        clSyms.push(16); clExtra.push(take - 3);
        left -= take;
      }
      while (left-- > 0) { clSyms.push(v); clExtra.push(0); }
    }
    i += run;
  }
  const clFreq = new Float64Array(19);
  for (const s of clSyms) clFreq[s]++;
  const clLen = buildLengths(clFreq, 7);
  const clCode = canonicalCodes(clLen);
  const ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
  let hclen = 19;
  while (hclen > 4 && clLen[ORDER[hclen - 1]] === 0) hclen--;
  bw.writeBits(hlit - 257, 5);
  bw.writeBits(hdist - 1, 5);
  bw.writeBits(hclen - 4, 4);
  for (let k = 0; k < hclen; k++) bw.writeBits(clLen[ORDER[k]], 3);
  const CL_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 7];
  for (let k = 0; k < clSyms.length; k++) {
    const s = clSyms[k];
    bw.write(clCode.codes[s], clCode.lengths[s]);
    if (CL_EXTRA[s] > 0) bw.writeBits(clExtra[k], CL_EXTRA[s]);
  }
  // Symbols.
  for (let s = 0; s < nSym; s++) {
    if (symLit[s] >= 0) {
      const v = symLit[s];
      bw.write(litCode.codes[v], litCode.lengths[v]);
    } else {
      const L = symLen[s];
      const D = symDist[s];
      const lc = LEN_CODE[L];
      bw.write(litCode.codes[lc], litCode.lengths[lc]);
      if (LEN_EXT[L] > 0) bw.writeBits(L - LEN_BASE[lc - 257], LEN_EXT[L]);
      const dc = DIST_CODE[D];
      bw.write(distCode.codes[dc], distCode.lengths[dc]);
      if (DIST_EXT[D] > 0) bw.writeBits(D - DIST_BASE[dc], DIST_EXT[D]);
    }
  }
  bw.write(litCode.codes[256], litCode.lengths[256]);
}

// Emit the same symbols as a fixed-Huffman block.
function emitFixedBlock(bw, symLit, symLen, symDist, nSym, isLast) {
  const litCode = canonicalCodes(FIXED_LIT_LEN);
  const distCode = canonicalCodes(FIXED_DIST_LEN);
  bw.writeBits(isLast ? 1 : 0, 1);
  bw.writeBits(1, 2); // fixed Huffman block
  for (let s = 0; s < nSym; s++) {
    if (symLit[s] >= 0) {
      const v = symLit[s];
      bw.write(litCode.codes[v], litCode.lengths[v]);
    } else {
      const L = symLen[s];
      const D = symDist[s];
      const lc = LEN_CODE[L];
      bw.write(litCode.codes[lc], litCode.lengths[lc]);
      if (LEN_EXT[L] > 0) bw.writeBits(L - LEN_BASE[lc - 257], LEN_EXT[L]);
      const dc = DIST_CODE[D];
      bw.write(distCode.codes[dc], distCode.lengths[dc]);
      if (DIST_EXT[D] > 0) bw.writeBits(D - DIST_BASE[dc], DIST_EXT[D]);
    }
  }
  bw.write(litCode.codes[256], litCode.lengths[256]);
}


// A copy of `freq` with every zero-frequency symbol raised to 1. The
// DP cost tables are built from these: a symbol the previous parse never
// used must still cost something, or the DP treats it as free and the
// parse collapses into literals that cost nothing on paper but plenty in
// the emitted stream. Emission still uses the raw frequencies.
function smoothed(freq) {
  const out = new Float64Array(freq.length);
  for (let i = 0; i < freq.length; i++) out[i] = freq[i] === 0 ? 1 : freq[i];
  return out;
}

function adler32(data) {
  let a = 1, b = 0;
  for (let i = 0; i < data.length;) {
    const end = Math.min(data.length, i + 5552);
    for (; i < end; i++) {
      a += data[i];
      b += a;
    }
    a %= 65521;
    b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

// The main entry: deflate `data` into a zlib stream.
// opts: { chainCap, blocks, iterations }
export function deflateZlib(data, opts = {}) {
  const chainCap = opts.chainCap ?? 1024;
  const nBlocks = opts.blocks ?? 8;
  const iterations = opts.iterations ?? 3;
  const n = data.length;
  if (n === 0) {
    return new Uint8Array([0x78, 0x01, 0x01, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01]);
  }
  const frontiers = findFrontiers(data, chainCap);
  const blockLen = Math.ceil(n / nBlocks);
  const mainBw = new BitWriter(n * 2 + 8192);
  for (let b = 0; b < nBlocks; b++) {
    const start = b * blockLen;
    if (start >= n) break;
    const end = Math.min(n, start + blockLen);
    const isLast = end >= n;
    // Iterate: fixed costs, then rebuild tables from each parse. The
    // final pass expands matches to length-code range endpoints so the
    // parse can end a match early for alignment.
    let litLen = FIXED_LIT_LEN;
    let distLen = FIXED_DIST_LEN;
    let parsed = null;
    for (let it = 0; it < iterations; it++) {
      const tables = costTables(litLen, distLen);
      parsed = parseBlock(data, start, end, frontiers, tables, it === iterations - 1);
      if (it === iterations - 1) break;
      const { litFreq, distFreq } = frequencies(parsed.symLit, parsed.symLen, parsed.symDist, parsed.nSym);
      litLen = buildLengths(smoothed(litFreq), 15);
      distLen = buildLengths(smoothed(distFreq), 15);
      // A dynamic block needs at least two lit codes and one dist code;
      // buildLengths already guarantees this for used alphabets, but an
      // all-literal block has a single dist symbol (code 0) with freq 0:
      // give it a second code so the header stays valid.
      let dl = 0;
      for (let k = 0; k < 30; k++) if (distLen[k] > 0) dl++;
      if (dl === 0) distLen[0] = 1;
      if (dl === 1) {
        let other = -1;
        for (let k = 1; k < 30; k++) if (distLen[k] === 0) { other = k; break; }
        if (other >= 0) distLen[other] = 1;
      }
      let ll = 0;
      for (let k = 0; k < 288; k++) if (litLen[k] > 0) ll++;
      if (ll === 1) {
        for (let k = 0; k < 288; k++) if (litLen[k] === 0) { litLen[k] = 1; break; }
      }
    }
    const { litFreq, distFreq } = frequencies(parsed.symLit, parsed.symLen, parsed.symDist, parsed.nSym);
    const finLitLen = buildLengths(litFreq, 15);
    const finDistLen = buildLengths(distFreq, 15);
    let dl = 0;
    for (let k = 0; k < 30; k++) if (finDistLen[k] > 0) dl++;
    if (dl === 0) finDistLen[0] = 1;
    if (dl === 1) {
      for (let k = 1; k < 30; k++) if (finDistLen[k] === 0) { finDistLen[k] = 1; break; }
    }
    let ll = 0;
    for (let k = 0; k < 288; k++) if (finLitLen[k] > 0) ll++;
    if (ll === 1) {
      for (let k = 0; k < 288; k++) if (finLitLen[k] === 0) { finLitLen[k] = 1; break; }
    }
    const litCode = canonicalCodes(finLitLen);
    const distCode = canonicalCodes(finDistLen);
    // Emit dynamic and fixed into trial writers, keep the smaller by bits.
    // finish() flushes each trial writer's pending partial byte into its
    // buffer before append() reads it.
    const cap = (end - start) * 2 + 8192;
    const bwDyn = new BitWriter(cap);
    emitBlock(bwDyn, parsed.symLit, parsed.symLen, parsed.symDist, parsed.nSym, litCode, distCode, isLast);
    bwDyn.finish();
    const bwFix = new BitWriter(cap);
    emitFixedBlock(bwFix, parsed.symLit, parsed.symLen, parsed.symDist, parsed.nSym, isLast);
    bwFix.finish();
    mainBw.append(bwDyn.bitLen <= bwFix.bitLen ? bwDyn : bwFix);
  }
  const deflated = mainBw.finish();
  const total = 2 + deflated.length + 4;
  const out = new Uint8Array(total);
  out[0] = 0x78;
  out[1] = 0x9c;
  out.set(deflated, 2);
  const ad = adler32(data);
  out[2 + deflated.length] = (ad >>> 24) & 0xff;
  out[3 + deflated.length] = (ad >>> 16) & 0xff;
  out[4 + deflated.length] = (ad >>> 8) & 0xff;
  out[5 + deflated.length] = ad & 0xff;
  return out;
}
