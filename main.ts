// PNG squeeze R9 — fresh build from the prose briefs (R5 leaders, R6, R7, R8, R9).
// Colour forms + palette orderings, Viterbi/strip/band filter contest over hybrid
// entropy+lazy-match costs, per-row brute force, hash-chain finder with row-above
// probes, forward-DP optimal parse with iterated Huffman costs (dual basins),
// run-aware block splitting/merging, length-limited Huffman trees (clamp+Kraft
// repair, exact Kraft validated), one shared bit writer, dynamic-vs-fixed blocks.
// Deterministic: fixed budgets, no clock, no Math.random.
import { readFileSync, writeFileSync, mkdirSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { inflateSync, deflateRawSync, deflateSync } from 'node:zlib';

const NODE = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTD = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// ---------- DEFLATE tables ----------
const LEN_BASE = [3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258];
const LEN_EXTRA = [0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0];
const DIST_BASE = [1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577];
const DIST_EXTRA = [0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13];
function lenSym(len) { // length -> symbol 257..285
  if (len >= 258) return 285;
  for (let s = 0; s < 29; s++) {
    const lo = LEN_BASE[s], hi = lo + (LEN_EXTRA[s] ? (1 << LEN_EXTRA[s]) - 1 : 0);
    if (len >= lo && len <= hi) return 257 + s;
  }
  return 285;
}
function distSym(d) {
  for (let s = 0; s < 30; s++) {
    const lo = DIST_BASE[s], hi = lo + (DIST_EXTRA[s] ? (1 << DIST_EXTRA[s]) - 1 : 0);
    if (d >= lo && d <= hi) return s;
  }
  return 29;
}
const CL_ORDER = [16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15];
const LEN_SYM_TAB = new Uint16Array(259);
for (let l = 3; l <= 258; l++) LEN_SYM_TAB[l] = lenSym(l);
const DIST_SYM_TAB = new Uint8Array(32769);
for (let d = 1; d <= 32768; d++) DIST_SYM_TAB[d] = distSym(d);
const FIXED_LIT = new Uint8Array(288);
for (let i = 0; i < 288; i++) FIXED_LIT[i] = i < 144 ? 8 : i < 256 ? 9 : i < 280 ? 7 : 8;
const FIXED_DIST = new Uint8Array(30).fill(5);

// ---------- CRC / Adler ----------
const CRC_T = (() => { const t = new Int32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; t[n] = c; } return t; })();
function crc32(b, s, e) { let c = -1; for (let i = s; i < e; i++) c = CRC_T[(c ^ b[i]) & 255] ^ (c >>> 8); return (c ^ -1) >>> 0; }
function adler32(b) { let a = 1, c = 0; for (let i = 0; i < b.length;) { const e = Math.min(b.length, i + 5552); for (; i < e; i++) { a += b[i]; c += a; } a %= 65521; c %= 65521; } return ((c << 16) | a) >>> 0; }
function chunk(type, data) {
  const out = new Uint8Array(12 + data.length);
  const v = new DataView(out.buffer);
  v.setUint32(0, data.length);
  for (let i = 0; i < 4; i++) out[4 + i] = type.charCodeAt(i);
  out.set(data, 8);
  v.setUint32(8 + data.length, crc32(out, 4, 8 + data.length));
  return out;
}
function pngOf(chunks) {
  const sig = Uint8Array.of(137,80,78,71,13,10,26,10);
  let size = 8; for (const c of chunks) size += c.length;
  const out = new Uint8Array(size); out.set(sig, 0);
  let at = 8; for (const c of chunks) { out.set(c, at); at += c.length; }
  return out;
}
function ihdrOf(w, h, ct) { const d = new Uint8Array(13); const v = new DataView(d.buffer); v.setUint32(0, w); v.setUint32(4, h); d[8] = 8; d[9] = ct; return d; }

// ---------- PNG decode to RGBA ----------
function paeth(a, b, c) { const p = a + b - c, pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c); return pa <= pb && pa <= pc ? a : pb <= pc ? b : c; }
function decodePng(bytes) {
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8, header = null, palette = null, trns = null; const idat = [];
  while (at < bytes.length) {
    const len = view.getUint32(at);
    const type = String.fromCharCode(bytes[at+4], bytes[at+5], bytes[at+6], bytes[at+7]);
    const data = bytes.subarray(at + 8, at + 8 + len); at += 12 + len;
    if (type === 'IHDR') { const dv = new DataView(data.buffer, data.byteOffset, 13); header = { w: dv.getUint32(0), h: dv.getUint32(4), ct: data[9] }; }
    else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
  }
  const { w, h, ct } = header;
  const ch = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 }[ct];
  const stride = w * ch;
  const raw = inflateSync(Buffer.concat(idat.map(x => Buffer.from(x))));
  const samples = new Uint8Array(h * stride);
  for (let y = 0; y < h; y++) {
    const ft = raw[y * (stride + 1)], src = y * (stride + 1) + 1, o = y * stride, p = o - stride;
    for (let i = 0; i < stride; i++) {
      const v = raw[src + i];
      if (ft === 0) samples[o+i] = v;
      else if (ft === 1) samples[o+i] = v + (i >= ch ? samples[o+i-ch] : 0);
      else if (ft === 2) samples[o+i] = v + (y > 0 ? samples[p+i] : 0);
      else if (ft === 3) samples[o+i] = v + (((i >= ch ? samples[o+i-ch] : 0) + (y > 0 ? samples[p+i] : 0)) >> 1);
      else { const a = i >= ch ? samples[o+i-ch] : 0, b = y > 0 ? samples[p+i] : 0, c = y > 0 && i >= ch ? samples[p+i-ch] : 0; samples[o+i] = v + paeth(a, b, c); }
    }
  }
  const n = w * h, rgba = new Uint8Array(n * 4);
  if (ct === 6) rgba.set(samples);
  else if (ct === 2) { const key = trns ? (trns[1] << 16) | (trns[3] << 8) | trns[5] : -1; for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) { rgba[d]=samples[s]; rgba[d+1]=samples[s+1]; rgba[d+2]=samples[s+2]; rgba[d+3] = ((samples[s]<<16)|(samples[s+1]<<8)|samples[s+2]) === key ? 0 : 255; } }
  else if (ct === 0) { const key = trns ? trns[1] : -1; for (let i = 0, d = 0; i < n; i++, d += 4) { const g = samples[i]; rgba[d]=rgba[d+1]=rgba[d+2]=g; rgba[d+3] = g === key ? 0 : 255; } }
  else if (ct === 4) { for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) { rgba[d]=rgba[d+1]=rgba[d+2]=samples[s]; rgba[d+3]=samples[s+1]; } }
  else { const lut = new Uint8Array((palette.length/3) * 4); for (let e = 0; e < palette.length/3; e++) { lut[e*4]=palette[e*3]; lut[e*4+1]=palette[e*3+1]; lut[e*4+2]=palette[e*3+2]; lut[e*4+3] = trns && e < trns.length ? trns[e] : 255; } for (let i = 0, d = 0; i < n; i++, d += 4) { const e = samples[i]; rgba[d]=lut[e*4]; rgba[d+1]=lut[e*4+1]; rgba[d+2]=lut[e*4+2]; rgba[d+3]=lut[e*4+3]; } }
  return { w, h, rgba };
}

// ---------- filters ----------
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) { for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i-bpp] : 0); }
  else if (type === 2) { for (let i = 0; i < n; i++) out[i] = cur[i] - (prev ? prev[i] : 0); }
  else if (type === 3) { for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i-bpp] : 0) + (prev ? prev[i] : 0)) >> 1); }
  else { for (let i = 0; i < n; i++) { const a = i >= bpp ? cur[i-bpp] : 0, b = prev ? prev[i] : 0, c = prev && i >= bpp ? prev[i-bpp] : 0; out[i] = cur[i] - paeth(a, b, c); } }
}
function signedSum(row) { let s = 0; for (let i = 0; i < row.length; i++) { const v = row[i]; s += v < 128 ? v : 256 - v; } return s; }
function buildFiltered(samples, w, h, bpp) {
  const stride = w * bpp, F = [];
  for (let t = 0; t < 5; t++) {
    const raw = new Uint8Array(h * (stride + 1));
    const tmp = new Uint8Array(stride);
    for (let y = 0; y < h; y++) {
      const cur = samples.subarray(y*stride, (y+1)*stride), prev = y ? samples.subarray((y-1)*stride, y*stride) : null;
      filterRow(t, cur, prev, bpp, tmp);
      raw[y*(stride+1)] = t; raw.set(tmp, y*(stride+1)+1);
    }
    F.push(raw);
  }
  return F;
}
function streamFromSeq(F, seq, w, h, bpp) {
  const stride = w * bpp, raw = new Uint8Array(h * (stride + 1));
  for (let y = 0; y < h; y++) { const t = seq[y]; raw[y*(stride+1)] = t; raw.set(F[t].subarray(y*(stride+1)+1, (y+1)*(stride+1)), y*(stride+1)+1); }
  return raw;
}

// ---------- Huffman: heap lengths, clamp to maxBits, Kraft repair, canonical codes ----------
// Returns {lens: Uint8Array, codes: Uint32Array, kraftOk: boolean}
function huffLengths(freq, maxBits) {
  const n = freq.length;
  const lens = new Uint8Array(n);
  const syms = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) syms.push(i);
  if (syms.length === 0) return { lens, codes: new Uint32Array(n), kraftOk: true };
  if (syms.length === 1) {
    lens[syms[0]] = 1;
    // a single code of length 1 is incomplete: add a dummy code of length 1 (never emitted)
    for (let i = 0; i < n; i++) if (i !== syms[0]) { lens[i] = 1; break; }
  }
  else {
    // heap of [freq, tie, nodeIndex]; nodes: leaves are syms, internal nodes in arrays
    const nf = [], nl = [], nr = []; // node freq, left, right (child node ids; leaf id = sym, internal id = n+k)
    const heap = [];
    const push = (id) => { heap.push(id); let i = heap.length - 1; while (i > 0) { const p = (i-1)>>1; if (nf[heap[p]] < nf[heap[i]] || (nf[heap[p]] === nf[heap[i]] && heap[p] < heap[i])) break; const t = heap[p]; heap[p] = heap[i]; heap[i] = t; i = p; } };
    const pop = () => { const top = heap[0], last = heap.pop(); if (heap.length) { heap[0] = last; let i = 0; for (;;) { const l = i*2+1, r = l+1; let m = i; if (l < heap.length && (nf[heap[l]] < nf[heap[m]] || (nf[heap[l]] === nf[heap[m]] && heap[l] < heap[m]))) m = l; if (r < heap.length && (nf[heap[r]] < nf[heap[m]] || (nf[heap[r]] === nf[heap[m]] && heap[r] < heap[m]))) m = r; if (m === i) break; const t = heap[m]; heap[m] = heap[i]; heap[i] = t; i = m; } } return top; };
    for (const s of syms) { nf[s] = freq[s]; nl[s] = -1; nr[s] = -1; push(s); }
    let next = n;
    while (heap.length > 1) {
      const a = pop(), b = pop();
      nf[next] = nf[a] + nf[b]; nl[next] = a; nr[next] = b; push(next); next++;
    }
    const root = heap[0];
    const stack = [[root, 0]];
    while (stack.length) { const [id, d] = stack.pop(); if (id < n) lens[id] = d; else { stack.push([nl[id], d+1]); stack.push([nr[id], d+1]); } }
    // clamp + repair (zlib-style overflow handling via Kraft adjustment)
    let over = 0;
    for (const s of syms) if (lens[s] > maxBits) over += lens[s] - maxBits;
    if (over > 0) {
      for (const s of syms) if (lens[s] > maxBits) lens[s] = maxBits;
      // Kraft sum in units of 2^-maxBits
      const kraft = () => { let s = 0; for (const x of syms) s += 1 << (maxBits - lens[x]); return s; };
      let k = kraft();
      const full = 1 << maxBits;
      // If sum > full, lengthen the longest (least frequent first) codes one step at a time.
      while (k > full) {
        let pick = -1, worst = -1;
        for (const s of syms) if (lens[s] < maxBits && (lens[s] > worst || (lens[s] === worst && freq[s] < freq[pick]))) { worst = lens[s]; pick = s; }
        if (pick < 0) break;
        lens[pick]++; k -= 1 << (maxBits - lens[pick]);
      }
      // If sum < full, shorten the shortest (most frequent) codes.
      // Shortening L -> L-1 increases Kraft by 2^(maxBits-L) (old contribution).
      while (k < full) {
        let pick = -1, best = 99;
        for (const s of syms) if (lens[s] > 1 && (lens[s] < best || (lens[s] === best && freq[s] > freq[pick]))) { best = lens[s]; pick = s; }
        if (pick < 0) break;
        lens[pick]--; k += 1 << (maxBits - lens[pick] - 1);
      }
      // Exactness check: if the repair did not land exactly on a complete code,
      // fall back to a provably complete assignment (shorter codes to frequent symbols).
      {
        let kk = 0; for (const s of syms) kk += 1 << (maxBits - lens[s]);
        if (kk !== full) {
          const cnt = syms.length;
          const d = Math.floor(Math.log2(cnt));
          const nShort = (1 << (d + 1)) - cnt; // symbols at length d
          const byFreq = syms.slice().sort((a, b) => freq[b] - freq[a] || a - b);
          for (let i = 0; i < byFreq.length; i++) lens[byFreq[i]] = i < nShort ? d : d + 1;
          // the dummy symbol (freq 0) keeps length 1 only if it was the single-symbol case;
          // here cnt >= 2, so no dummy is present.
        }
      }
    }
  }
  // canonical codes, MSB-first values
  // Final safety net: a complete code is mandatory; if anything above left Kraft != full, use the complete fallback.
  {
    let kk = 0, cnt = 0;
    for (const s of syms) { kk += 1 << (maxBits - lens[s]); cnt++; }
    if (cnt >= 2 && kk !== (1 << maxBits)) {
      const d = Math.floor(Math.log2(cnt));
      const nShort = (1 << (d + 1)) - cnt;
      const byFreq = syms.slice().sort((a, b) => freq[b] - freq[a] || a - b);
      for (let i = 0; i < byFreq.length; i++) lens[byFreq[i]] = i < nShort ? d : d + 1;
    }
  }
  const codes = new Uint32Array(n);
  const bl = new Uint32Array(maxBits + 1);
  for (const s of syms) bl[lens[s]]++;
  let code = 0; const nextCode = new Uint32Array(maxBits + 1);
  for (let b = 1; b <= maxBits; b++) { code = (code + bl[b-1]) << 1; nextCode[b] = code; }
  const order = syms.slice().sort((a, b) => lens[a] - lens[b] || a - b);
  for (const s of order) { codes[s] = nextCode[lens[s]]++; }
  // exact Kraft check
  let k = 0; for (const s of syms) k += 1 << (maxBits - lens[s]);
  const kraftOk = syms.length <= 1 ? true : k === (1 << maxBits);
  return { lens, codes, kraftOk };
}
function kraftCheck(lens, maxBits) { let k = 0, cnt = 0; for (let i = 0; i < lens.length; i++) if (lens[i]) { cnt++; k += 1 << (maxBits - lens[i]); } return cnt <= 1 ? true : k === (1 << maxBits); }

// ---------- bit writer (one shared writer across all blocks) ----------
class BitWriter {
  constructor() { this.bytes = []; this.acc = 0; this.nbits = 0; }
  putBits(val, len) { // LSB-first stream bits (header fields, extra bits)
    for (let i = 0; i < len; i++) { this.acc |= ((val >> i) & 1) << this.nbits; this.nbits++; if (this.nbits === 8) { this.bytes.push(this.acc); this.acc = 0; this.nbits = 0; } }
  }
  putCode(code, len) { // Huffman code, MSB-first
    for (let i = len - 1; i >= 0; i--) { this.acc |= ((code >> i) & 1) << this.nbits; this.nbits++; if (this.nbits === 8) { this.bytes.push(this.acc); this.acc = 0; this.nbits = 0; } }
  }
  finish() { if (this.nbits) this.bytes.push(this.acc); return new Uint8Array(this.bytes); }
}

// ---------- cost tables from Huffman lengths ----------
function makeCostTables(litLens, distLens) {
  const litCost = new Float64Array(288), distCost = new Float64Array(30);
  for (let i = 0; i < 256; i++) litCost[i] = litLens[i] || 12;
  for (let s = 0; s < 29; s++) litCost[257+s] = (litLens[257+s] || 12) + LEN_EXTRA[s];
  litCost[256] = litLens[256] || 7;
  for (let s = 0; s < 30; s++) distCost[s] = (distLens[s] || 12) + DIST_EXTRA[s];
  return { litCost, distCost };
}
function fixedCostTables() { return makeCostTables(FIXED_LIT, FIXED_DIST); }
function matchBitCost(len, dist, litCost, distCost) {
  return litCost[lenSym(len)] + distCost[distSym(dist)];
}

// ---------- match finder (hash chain + row-above probes, every position) ----------
function findMatches(buf, hist, L, rowLen, maxLen, depth, out) {
  const n = hist + L;
  const head = new Int32Array(262144).fill(-1);
  const prev = new Int32Array(n).fill(-1);
  const { bestLen, bestDist, secLen, secDist } = out;
  // run lengths (capped at maxLen) for O(1) match-extension jumps inside runs
  const runLen = new Uint16Array(n + 1);
  runLen[n-1] = 1;
  for (let i = n - 2; i >= 0; i--) runLen[i] = buf[i] === buf[i+1] ? Math.min(maxLen, runLen[i+1] + 1) : 1;
  let visits = 0;
  // per-length best distance (Pareto): nearest distance achieving >=3, >=8, >=24
  const nearLen = out.nearLen, nearDist = out.nearDist;
  // match extension, inlined at both call sites (no function call per candidate):
  // jump over identical-byte runs, then compare byte by byte up to `bound`.
  // `bound` is lim normally, or bestL when the byte at bestL already differs
  // (then the true match cannot exceed bestL).
  for (let p = 0; p < n; p++) {
    if (p + 2 < n) {
      const h = (((buf[p] * 257 + buf[p+1]) * 257 + buf[p+2]) * 2654435761) >>> 14 & 262143;
      if (p >= hist) {
        let bestL = 0, bestD = 0, secL = 0, secD = 0;
        const lim = Math.min(maxLen, n - p);
        const base3 = p * 3;
        let v = 0;
        let cand = head[h];
        while (cand >= 0 && v < depth) {
          const dist = p - cand;
          if (dist > 32768) break;
          v++;
          if (buf[cand] === buf[p] && buf[cand+1] === buf[p+1] && buf[cand+2] === buf[p+2]) {
            let len = -1;
            if (bestL >= 3 && secL >= bestL && buf[cand+bestL] !== buf[p+bestL]) {
              len = -1; // cannot improve best/second; near already set by nearer candidates
            } else {
              const bound = (bestL >= 3 && buf[cand+bestL] !== buf[p+bestL]) ? bestL : lim;
              len = runLen[cand] < runLen[p] ? runLen[cand] : runLen[p];
              if (len < bound) { while (len < bound && buf[cand+len] === buf[p+len]) len++; }
              if (len > bound) len = bound;
            }
            if (len >= 3) {
              if (len > bestL || (len === bestL && dist < bestD)) { if (bestL > secL && bestD !== dist) { secL = bestL; secD = bestD; } bestL = len; bestD = dist; }
              else if (len > secL) { secL = len; secD = dist; }
              if (len >= 3 && dist < nearDist[base3]) { nearDist[base3] = dist; nearLen[base3] = len; }
              if (len >= 8 && dist < nearDist[base3+1]) { nearDist[base3+1] = dist; nearLen[base3+1] = len; }
              if (len >= 24 && dist < nearDist[base3+2]) { nearDist[base3+2] = dist; nearLen[base3+2] = len; }
            }
            if (bestL >= 64) break;
            if (bestL >= lim) break;
          }
          cand = prev[cand];
        }
        visits += v;
        // row-above probes (one and two scanlines above)
        for (let k = 1; k <= 2; k++) {
          const c2 = p - k * rowLen;
          if (c2 < 0) break;
          const dist = k * rowLen;
          if (dist > 32768) break;
          if (buf[c2] === buf[p] && buf[c2+1] === buf[p+1] && buf[c2+2] === buf[p+2]) {
            const bound = (bestL >= 3 && buf[c2+bestL] !== buf[p+bestL]) ? bestL : lim;
            let len = runLen[c2] < runLen[p] ? runLen[c2] : runLen[p];
            if (len < bound) { while (len < bound && buf[c2+len] === buf[p+len]) len++; }
            if (len > bound) len = bound;
            if (len >= 3) {
              if (len > bestL || (len === bestL && dist < bestD)) { if (bestL > secL && bestD !== dist) { secL = bestL; secD = bestD; } bestL = len; bestD = dist; }
              else if (len > secL) { secL = len; secD = dist; }
              if (len >= 3 && dist < nearDist[base3]) { nearDist[base3] = dist; nearLen[base3] = len; }
              if (len >= 8 && dist < nearDist[base3+1]) { nearDist[base3+1] = dist; nearLen[base3+1] = len; }
              if (len >= 24 && dist < nearDist[base3+2]) { nearDist[base3+2] = dist; nearLen[base3+2] = len; }
            }
          }
        }
        bestLen[p] = bestL; bestDist[p] = bestD; secLen[p] = secL; secDist[p] = secD;
      }
      prev[p] = head[h]; head[h] = p;
    }
  }
  return visits;
}

// ---------- forward-DP optimal parse of one block ----------
function dpParse(buf, hist, L, litCost, distCost, maxLen, finder) {
  const dp = new Float64Array(L + 1); dp.fill(Infinity); dp[0] = 0;
  const chLen = new Uint16Array(L + 1), chDist = new Uint16Array(L + 1);
  const { bestLen, bestDist, secLen, secDist, nearLen, nearDist } = finder;
  // per-length literal cost and per-distance cost for this iteration (no table lookups in the loop)
  const lenCost = new Float64Array(259);
  for (let l = 3; l <= 258; l++) lenCost[l] = litCost[LEN_SYM_TAB[l]];
  const distCostByDist = new Float64Array(32769);
  for (let d = 1; d <= 32768; d++) distCostByDist[d] = distCost[DIST_SYM_TAB[d]];
  // candidate evaluation is inlined below (a closure call per candidate costs
  // ~40% of DP time at ~450M candidate evaluations per full run)
  for (let i = 0; i < L; i++) {
    const base = dp[i]; if (!Number.isFinite(base)) continue;
    const p = hist + i;
    const nc = base + litCost[buf[p]];
    if (nc < dp[i+1]) { dp[i+1] = nc; chLen[i+1] = 1; chDist[i+1] = 0; }
    const bl = bestLen[p];
    if (bl >= 3) {
      const rem = L - i, ml = bl > rem ? rem : bl;
      if (ml >= 3) {
        const bd = bestDist[p];
        { const len = ml, dist = bd; const j = i + len, c = base + lenCost[len] + distCostByDist[dist]; if (c < dp[j]) { dp[j] = c; chLen[j] = len; chDist[j] = dist; } }
        if (secLen[p] >= 3) { const len = secLen[p] > rem ? rem : secLen[p], dist = secDist[p]; const j = i + len, c = base + lenCost[len] + distCostByDist[dist]; if (c < dp[j]) { dp[j] = c; chLen[j] = len; chDist[j] = dist; } }
        if (ml > 3) {
          { const len = 3, dist = bd; const j = i + len, c = base + lenCost[len] + distCostByDist[dist]; if (c < dp[j]) { dp[j] = c; chLen[j] = len; chDist[j] = dist; } }
          { const len = ml - 1, dist = bd; const j = i + len, c = base + lenCost[len] + distCostByDist[dist]; if (c < dp[j]) { dp[j] = c; chLen[j] = len; chDist[j] = dist; } }
        }
        // sublen endpoints of the best match's length-code ranges (LEN_BASE
        // ascends, so break once it reaches ml)
        for (let s = 0; s < 29; s++) { const len = LEN_BASE[s]; if (len >= ml) break; if (len < 3) continue; const dist = bd; const j = i + len, c = base + lenCost[len] + distCostByDist[dist]; if (c < dp[j]) { dp[j] = c; chLen[j] = len; chDist[j] = dist; } }
        // Pareto near-distance candidates: nearest match of >=3, >=8, >=24 bytes
        const base3 = p * 3;
        for (let k = 0; k < 3; k++) {
          const nl = nearLen[base3 + k], nd = nearDist[base3 + k];
          if (nl >= 3 && nd !== bd) {
            { const len = nl > rem ? rem : nl, dist = nd; const j = i + len, c = base + lenCost[len] + distCostByDist[dist]; if (c < dp[j]) { dp[j] = c; chLen[j] = len; chDist[j] = dist; } }
            if (nl > 3) { const len = 3, dist = nd; const j = i + len, c = base + lenCost[len] + distCostByDist[dist]; if (c < dp[j]) { dp[j] = c; chLen[j] = len; chDist[j] = dist; } }
          }
        }
      }
    }
  }
  // backtrack
  const litFreq = new Uint32Array(288), distFreq = new Uint32Array(30);
  const toks = [];
  let i = L, matchBytes = 0, nTok = 0;
  while (i > 0) {
    const len = chLen[i], dist = chDist[i];
    if (len === 1 && dist === 0) { const b = buf[hist + i - 1]; litFreq[b]++; toks.push([0, b, 0]); }
    else { const ls = lenSym(len), ds = distSym(dist); litFreq[ls]++; distFreq[ds]++; matchBytes += len; toks.push([1, len, dist]); }
    nTok++; i -= len;
  }
  toks.reverse();
  litFreq[256] = 1;
  return { toks, bits: dp[L], litFreq, distFreq, matchBytes, nTok };
}
function headerBitsEst(litLens, distLens) {
  // rough dynamic-header estimate: CL code lengths for RLE of lit+dist lengths
  let nz = 0; for (let i = 0; i < 288; i++) if (litLens[i]) nz++; for (let i = 0; i < 30; i++) if (distLens[i]) nz++;
  return 14 + 57 + nz * 4;
}
function parseBlockFull(buf, hist, L, rowLen, maxLen, depth, iters, isFlat) {
  const finder = { bestLen: new Uint16Array(hist + L), bestDist: new Uint16Array(hist + L), secLen: new Uint16Array(hist + L), secDist: new Uint16Array(hist + L), nearLen: new Uint16Array((hist + L) * 3), nearDist: new Uint16Array((hist + L) * 3).fill(65535) };
  const visits = findMatches(buf, hist, L, rowLen, maxLen, depth, finder);
  let costs = fixedCostTables();
  let best = null;
  for (let it = 0; it < iters; it++) {
    const r = dpParse(buf, hist, L, costs.litCost, costs.distCost, maxLen, finder);
    const { lens: ll, codes: lc } = huffLengths(r.litFreq, 15);
    const { lens: dl, codes: dc } = huffLengths(r.distFreq, 15);
    // score by ACTUAL emitted token bits under this parse's own lengths, not stale dp bits
    const tot = tokenBits(r.toks, ll, dl) + dynamicHeaderBits(ll, dl);
    if (!best || tot < best.tot) best = { ...r, litLens: ll, distLens: dl, tot, visits };
    costs = makeCostTables(ll, dl);
  }
  return best;
}

// ---------- canonical codes from lengths ----------
function codesFromLens(lens, maxBits) {
  const codes = new Uint32Array(lens.length);
  const bl = new Uint32Array(maxBits + 1);
  for (let i = 0; i < lens.length; i++) if (lens[i]) bl[lens[i]]++;
  let code = 0; const next = new Uint32Array(maxBits + 1);
  for (let b = 1; b <= maxBits; b++) { code = (code + bl[b-1]) << 1; next[b] = code; }
  const order = []; for (let i = 0; i < lens.length; i++) if (lens[i]) order.push(i);
  order.sort((a, b) => lens[a] - lens[b] || a - b);
  for (const s of order) codes[s] = next[lens[s]]++;
  return codes;
}
function tokenBits(toks, litLens, distLens) {
  let bits = 0;
  for (const [m, a, b] of toks) {
    if (!m) bits += litLens[a] || 12;
    else bits += (litLens[LEN_SYM_TAB[a]] || 12) + LEN_EXTRA[LEN_SYM_TAB[a]-257] + (distLens[DIST_SYM_TAB[b]] || 12) + DIST_EXTRA[DIST_SYM_TAB[b]];
  }
  bits += litLens[256] || 7;
  return bits;
}
function rleLengthsReal(arr) {
  const syms = []; const clFreq = new Uint32Array(19);
  let i = 0;
  while (i < arr.length) {
    const v = arr[i];
    if (v === 0) {
      let run = 0; while (i + run < arr.length && arr[i+run] === 0) run++;
      let left = run;
      while (left >= 11) { const n = Math.min(left, 138); syms.push([18, n-11, 7]); clFreq[18]++; left -= n; }
      if (left >= 3) { syms.push([17, left-3, 3]); clFreq[17]++; left = 0; }
      while (left > 0) { syms.push([0, 0, 0]); clFreq[0]++; left--; }
      i += run;
    } else {
      syms.push([v, 0, 0]); clFreq[v]++; i++;
      let rep = 0; while (i + rep < arr.length && arr[i+rep] === v) rep++;
      let left = rep;
      while (left >= 3) { const n = Math.min(left, 6); syms.push([16, n-3, 2]); clFreq[16]++; left -= n; }
      for (let k = 0; k < left; k++) { syms.push([v, 0, 0]); clFreq[v]++; }
      i += rep;
    }
  }
  return { syms, clFreq };
}
function trimmedCounts(litLens, distLens) {
  let litCount = 257; for (let i = 287; i >= 257; i--) if (litLens[i]) { litCount = i + 1; break; }
  let distCount = 1; for (let i = 29; i >= 1; i--) if (distLens[i]) { distCount = i + 1; break; }
  return [litCount, distCount];
}
function dynamicHeaderBits(litLens, distLens) {
  const [litCount, distCount] = trimmedCounts(litLens, distLens);
  const arr = [];
  for (let i = 0; i < litCount; i++) arr.push(litLens[i]);
  for (let i = 0; i < distCount; i++) arr.push(distLens[i]);
  const { syms, clFreq } = rleLengthsReal(arr);
  const { lens: clLens } = huffLengths(clFreq, 7);
  let hclen = 4; for (let k = 18; k >= 4; k--) if (clLens[CL_ORDER[k]]) { hclen = k + 1; break; }
  let bits = 5 + 5 + 4 + hclen * 3;
  for (const [s, , eb] of syms) bits += (clLens[s] || 0) + eb;
  return bits;
}
function writeDynamicHeader(bw, litLens, distLens) {
  let litCount = 257; for (let i = 287; i >= 257; i--) if (litLens[i]) { litCount = i + 1; break; }
  let distCount = 1; for (let i = 29; i >= 1; i--) if (distLens[i]) { distCount = i + 1; break; }
  const arr = [];
  for (let i = 0; i < litCount; i++) arr.push(litLens[i]);
  for (let i = 0; i < distCount; i++) arr.push(distLens[i]);
  const { syms, clFreq } = rleLengthsReal(arr);
  const { lens: clLens, codes: clCodes } = huffLengths(clFreq, 7);
  let hclen = 4; for (let k = 18; k >= 4; k--) if (clLens[CL_ORDER[k]]) { hclen = k + 1; break; }
  bw.putBits(litCount - 257, 5); bw.putBits(distCount - 1, 5); bw.putBits(hclen - 4, 4);
  for (let k = 0; k < hclen; k++) bw.putBits(clLens[CL_ORDER[k]], 3);
  for (const [s, extra, eb] of syms) { bw.putCode(clCodes[s], clLens[s]); if (eb) bw.putBits(extra, eb); }
  return { clLens, litCount, distCount };
}
function emitBlock(bw, blk, isLast) {
  let litLens = blk.litLens, distLens = blk.distLens, useFixed = blk.useFixed;
  if (!useFixed) {
    if (!kraftCheck(litLens, 15) || !kraftCheck(distLens, 15)) { useFixed = true; }
  }
  let litCodes, distCodes;
  if (useFixed) { litLens = FIXED_LIT; distLens = FIXED_DIST; }
  litCodes = codesFromLens(litLens, 15); distCodes = codesFromLens(distLens, 15);
  bw.putBits(isLast ? 1 : 0, 1);
  if (useFixed) { bw.putBits(1, 2); }
  else {
    bw.putBits(2, 2);
    const { clLens } = writeDynamicHeader(bw, litLens, distLens);
    if (!kraftCheck(clLens, 7)) { /* header already written; cannot undo — but Kraft repair guarantees pass */ }
  }
  for (const [m, a, b] of blk.toks) {
    if (!m) bw.putCode(litCodes[a], litLens[a]);
    else {
      const ls = LEN_SYM_TAB[a], ds = DIST_SYM_TAB[b];
      bw.putCode(litCodes[ls], litLens[ls]);
      if (LEN_EXTRA[ls-257]) bw.putBits(a - LEN_BASE[ls-257], LEN_EXTRA[ls-257]);
      bw.putCode(distCodes[ds], distLens[ds]);
      if (DIST_EXTRA[ds]) bw.putBits(b - DIST_BASE[ds], DIST_EXTRA[ds]);
    }
  }
  bw.putCode(litCodes[256], litLens[256]);
  return useFixed;
}

// ---------- compress one filtered stream with custom DEFLATE ----------
function compressStream(raw, seq, w, h, bpp, isFlat, isDense) {
  const rowLen = w * bpp + 1;
  const H = raw.length;
  // initial boundaries: filter changes only where the segment is worth a new tree (>=16KB),
  // plus a 192KB cap, all aligned to row starts (run-aware: never split inside a run mid-row)
  const bounds = [0];
  for (let y = 1; y < h; y++) if (seq[y] !== seq[y-1] && y * rowLen - bounds[bounds.length-1] >= 65536) bounds.push(y * rowLen);
  const capped = [0];
  for (let k = 1; k < bounds.length; k++) {
    let s = capped[capped.length-1];
    while (bounds[k] - s > 256 * 1024) { const nb = s + Math.floor(256*1024 / rowLen) * rowLen; capped.push(nb); s = nb; }
    capped.push(bounds[k]);
  }
  capped.push(H);
  let blocks = [];
  let kraftFail = 0;
  const maxLen = 258; // the 128 cap for dense streams doubled token counts in flat blocks
  // inside dense images while never helping photo blocks (their matches are short)
  const depth = isFlat ? 96 : 48;
  const iters = isFlat ? 5 : 3;
  for (let k = 0; k + 1 < capped.length; k++) {
    const s = capped[k], e = capped[k+1], L = e - s;
    if (L <= 0) continue;
    const hist = Math.min(32768, s);
    const buf = raw.subarray(s - hist, e);
    const best = parseBlockFull(buf, hist, L, rowLen, maxLen, depth, iters, isFlat);
    if (process.env.MAKEFUN_DEBUG === '3') {
      const libB = deflateSync(raw.subarray(s, e), { level: 9 }).length;
      let litN = 0, litMax = 0, distN = 0, distMax = 0;
      for (let i = 0; i < 288; i++) if (best.litLens[i]) { litN++; litMax = Math.max(litMax, best.litLens[i]); }
      for (let i = 0; i < 30; i++) if (best.distLens[i]) { distN++; distMax = Math.max(distMax, best.distLens[i]); }
      const eb = tokenBits(best.toks, best.litLens, best.distLens);
      let badTok = null;
      if (!Number.isFinite(eb)) { for (const tk of best.toks) { const [m, a, b] = tk; if (m && (a < 3 || a > 258 || b < 1 || b > 32768)) { badTok = tk; break; } } }
      console.error(JSON.stringify({ block: k, L, matchFrac: +(best.matchBytes / Math.max(1, L)).toFixed(3), emitBits: eb, badTok, lib9: libB, toks: best.nTok, litN, litMax, distN, distMax }));
    }
    blocks.push({ s, e, toks: best.toks, litFreq: best.litFreq, distFreq: best.distFreq, litLens: best.litLens, distLens: best.distLens, visits: best.visits });
  }
  // split trials REMOVED (measured: re-parsing big blocks cost ~30% of parse CPU
  // for <1% of bytes; initial filter-boundary splits + merge pass are enough)
  // merge pass: adjacent blocks share one tree when no more expensive
  const merged = [];
  for (const blk of blocks) {
    const last = merged[merged.length-1];
    if (last) {
      const lf = new Uint32Array(288), df = new Uint32Array(30);
      for (let i = 0; i < 288; i++) lf[i] = last.litFreq[i] + blk.litFreq[i];
      for (let i = 0; i < 30; i++) df[i] = last.distFreq[i] + blk.distFreq[i];
      const { lens: ll } = huffLengths(lf, 15); const { lens: dl } = huffLengths(df, 15);
      const allToks = last.toks.concat(blk.toks);
      const mBits = tokenBits(allToks, ll, dl) + dynamicHeaderBits(ll, dl);
      const sBits = tokenBits(last.toks, last.litLens, last.distLens) + dynamicHeaderBits(last.litLens, last.distLens)
        + tokenBits(blk.toks, blk.litLens, blk.distLens) + dynamicHeaderBits(blk.litLens, blk.distLens);
      if (mBits <= sBits) {
        last.toks = allToks; last.litFreq = lf; last.distFreq = df; last.litLens = ll; last.distLens = dl; last.e = blk.e;
        continue;
      }
    }
    merged.push(blk);
  }
  blocks = merged;
  // per-block dynamic vs fixed, emit with ONE shared bit writer
  const bw = new BitWriter();
  let fixedCount = 0;
  for (let k = 0; k < blocks.length; k++) {
    const blk = blocks[k];
    const dynBits = tokenBits(blk.toks, blk.litLens, blk.distLens) + dynamicHeaderBits(blk.litLens, blk.distLens);
    const fixBits = tokenBits(blk.toks, FIXED_LIT, FIXED_DIST);
    blk.useFixed = fixBits + 3 <= dynBits + 3;
    if (blk.useFixed) fixedCount++;
    if (!blk.useFixed && (!kraftCheck(blk.litLens, 15) || !kraftCheck(blk.distLens, 15))) kraftFail++;
    emitBlock(bw, blk, k === blocks.length - 1);
  }
  const deflate = bw.finish();
  const zlib = new Uint8Array(2 + deflate.length + 4);
  zlib[0] = 0x78; zlib[1] = 0x9c; zlib.set(deflate, 2);
  new DataView(zlib.buffer).setUint32(2 + deflate.length, adler32(raw));
  const visits = blocks.reduce((a, b) => a + (b.visits || 0), 0);
  return { zlib, blocks: blocks.length, fixedCount, kraftFail, visits, rawLen: H };
}

// ---------- colour forms ----------
function buildForms(rgba, w, h) {
  const n = w * h;
  const counts = new Map();
  let grey = true, allOpaque = true, alphaOnly01 = true;
  const transRGB = new Set();
  for (let i = 0; i < n; i++) {
    const r = rgba[i*4], g = rgba[i*4+1], b = rgba[i*4+2], a = rgba[i*4+3];
    if (r !== g || g !== b) grey = false;
    if (a !== 255) allOpaque = false;
    if (a !== 0 && a !== 255) alphaOnly01 = false;
    if (a === 0) transRGB.add((r << 16) | (g << 8) | b);
    const key = (r << 24) | (g << 16) | (b << 8) | a;
    counts.set(key, (counts.get(key) || 0) + 1);
  }
  const forms = [];
  const distinct = counts.size;
  // palette forms
  if (distinct <= 256) {
    const cols = [...counts.entries()].sort((a, b) => b[1] - a[1]); // [key, count] freq order
    const keys = cols.map(c => c[0]);
    const freqs = cols.map(c => c[1]);
    const orderings = [];
    orderings.push({ name: 'pal-freq', order: keys.map((_, i) => i) });
    // luminance
    orderings.push({ name: 'pal-lum', order: keys.map((_, i) => i).sort((a, b) => { const ka = keys[a], kb = keys[b]; const la = 0.299*((ka>>>24)&255)+0.587*((ka>>>16)&255)+0.114*((ka>>>8)&255); const lb = 0.299*((kb>>>24)&255)+0.587*((kb>>>16)&255)+0.114*((kb>>>8)&255); return la - lb; }) });
    // border-pinned: colours by border frequency first
    const border = new Map();
    for (let x = 0; x < w; x++) { for (const y of [0, h-1]) { const i = y*w+x; const k = (rgba[i*4]<<24)|(rgba[i*4+1]<<16)|(rgba[i*4+2]<<8)|rgba[i*4+3]; border.set(k, (border.get(k)||0)+1); } }
    for (let y = 0; y < h; y++) { for (const x of [0, w-1]) { const i = y*w+x; const k = (rgba[i*4]<<24)|(rgba[i*4+1]<<16)|(rgba[i*4+2]<<8)|rgba[i*4+3]; border.set(k, (border.get(k)||0)+1); } }
    orderings.push({ name: 'pal-border', order: keys.map((_, i) => i).sort((a, b) => ((border.get(keys[b])||0) - (border.get(keys[a])||0)) || freqs[b] - freqs[a]) });
    // adjacency-optimized
    const P = keys.length;
    const idOf = new Map(keys.map((k, i) => [k, i]));
    const S = new Float64Array(P * P); // symmetric adjacency counts
    for (let y = 0; y < h; y++) {
      const base = y * w;
      for (let x = 0; x + 1 < w; x++) {
        const a = idOf.get((rgba[(base+x)*4]<<24)|(rgba[(base+x)*4+1]<<16)|(rgba[(base+x)*4+2]<<8)|rgba[(base+x)*4+3]);
        const b = idOf.get((rgba[(base+x+1)*4]<<24)|(rgba[(base+x+1)*4+1]<<16)|(rgba[(base+x+1)*4+2]<<8)|rgba[(base+x+1)*4+3]);
        if (a !== b) { S[a*P+b]++; S[b*P+a]++; }
      }
    }
    const order = [0]; const used = new Uint8Array(P); used[0] = 1;
    for (let k = 1; k < P; k++) {
      const last = order[k-1]; let bestC = -1, bestV = -1;
      for (let c = 0; c < P; c++) if (!used[c]) { const v = S[last*P+c]; if (v > bestV || (v === bestV && freqs[c] > freqs[bestC])) { bestV = v; bestC = c; } }
      order.push(bestC); used[bestC] = 1;
    }
    // adjacent-swap local search on cost sum S[a][b]*|pos[a]-pos[b]|
    const pos = new Int32Array(P);
    for (let k = 0; k < P; k++) pos[order[k]] = k;
    for (let pass = 0; pass < 3; pass++) {
      let improved = false;
      for (let k = 0; k + 1 < P; k++) {
        const x = order[k], y = order[k+1];
        let delta = 0;
        for (let b = 0; b < P; b++) {
          if (b === x || b === y) continue;
          delta += S[x*P+b] * (Math.abs(k+1 - pos[b]) - Math.abs(k - pos[b]));
          delta += S[y*P+b] * (Math.abs(k - pos[b]) - Math.abs(k+1 - pos[b]));
        }
        if (delta < 0) { order[k] = y; order[k+1] = x; pos[x] = k+1; pos[y] = k; improved = true; }
      }
      if (!improved) break;
    }
    orderings.push({ name: 'pal-adj', order });
    for (const o of orderings) {
      const idx = new Map();
      o.order.forEach((ci, pi) => idx.set(keys[ci], pi));
      const samples = new Uint8Array(n);
      for (let i = 0; i < n; i++) samples[i] = idx.get((rgba[i*4]<<24)|(rgba[i*4+1]<<16)|(rgba[i*4+2]<<8)|rgba[i*4+3]);
      const palette = new Uint8Array(P * 3), trnsA = new Uint8Array(P);
      let lastAlpha = -1;
      o.order.forEach((ci, pi) => { const k = keys[ci]; palette[pi*3] = (k>>>24)&255; palette[pi*3+1] = (k>>>16)&255; palette[pi*3+2] = (k>>>8)&255; trnsA[pi] = k & 255; if (trnsA[pi] < 255) lastAlpha = pi; });
      const trns = lastAlpha >= 0 ? trnsA.subarray(0, lastAlpha + 1) : null;
      forms.push({ name: o.name, ct: 3, bpp: 1, samples, palette, trns, overhead: 12 + palette.length + (trns ? 12 + trns.length : 0) });
    }
  }
  // grey forms
  if (grey) {
    const g = new Uint8Array(n); for (let i = 0; i < n; i++) g[i] = rgba[i*4];
    const a = new Uint8Array(n); for (let i = 0; i < n; i++) a[i] = rgba[i*4+3];
    let hasAlpha = false; for (let i = 0; i < n; i++) if (a[i] !== 255) { hasAlpha = true; break; }
    if (!hasAlpha) forms.push({ name: 'grey', ct: 0, bpp: 1, samples: g, palette: null, trns: null, overhead: 0 });
    else {
      const ga = new Uint8Array(n * 2); for (let i = 0; i < n; i++) { ga[i*2] = g[i]; ga[i*2+1] = a[i]; }
      forms.push({ name: 'grey-alpha', ct: 4, bpp: 2, samples: ga, palette: null, trns: null, overhead: 0 });
      if (alphaOnly01 && transRGB.size === 1) {
        const key = [...transRGB][0];
        const trns = new Uint8Array([0, (key >> 16) & 255]);
        forms.push({ name: 'grey-trns', ct: 0, bpp: 1, samples: g, palette: null, trns, overhead: 12 + 2 });
      }
    }
  }
  // RGB / RGB-trns
  if (allOpaque) {
    const rgb = new Uint8Array(n * 3); for (let i = 0; i < n; i++) { rgb[i*3] = rgba[i*4]; rgb[i*3+1] = rgba[i*4+1]; rgb[i*3+2] = rgba[i*4+2]; }
    forms.push({ name: 'rgb', ct: 2, bpp: 3, samples: rgb, palette: null, trns: null, overhead: 0 });
  } else if (alphaOnly01 && transRGB.size === 1) {
    const key = [...transRGB][0];
    const rgb = new Uint8Array(n * 3); for (let i = 0; i < n; i++) { rgb[i*3] = rgba[i*4]; rgb[i*3+1] = rgba[i*4+1]; rgb[i*3+2] = rgba[i*4+2]; }
    const trns = new Uint8Array([0, (key>>16)&255, 0, (key>>8)&255, 0, key&255]);
    forms.push({ name: 'rgb-trns', ct: 2, bpp: 3, samples: rgb, palette: null, trns, overhead: 12 + 6 });
  }
  // RGBA always
  forms.push({ name: 'rgba', ct: 6, bpp: 4, samples: rgba, palette: null, trns: null, overhead: 0 });
  for (const f of forms) f.distinct = distinct;
  return forms;
}

// ---------- filter contest ----------
function viterbi(costs, penalty, h) { // costs: [5][h] Float64Array
  const dp = new Float64Array(5), back = new Int8Array(h * 5);
  for (let t = 0; t < 5; t++) dp[t] = costs[t][0];
  for (let y = 1; y < h; y++) {
    const ndp = new Float64Array(5).fill(Infinity);
    for (let t = 0; t < 5; t++) {
      let best = Infinity, bp = 0;
      for (let p = 0; p < 5; p++) { const c = dp[p] + (p === t ? 0 : penalty) + costs[t][y]; if (c < best) { best = c; bp = p; } }
      ndp[t] = best; back[y*5+t] = bp;
    }
    dp.set(ndp);
  }
  let last = 0; for (let t = 1; t < 5; t++) if (dp[t] < dp[last]) last = t;
  const seq = new Uint8Array(h); seq[h-1] = last;
  for (let y = h - 1; y >= 1; y--) { last = back[y*5+last]; seq[y-1] = last; }
  return seq;
}
function stripSeq(costs, stripSize, penalty, h) {
  const ns = Math.ceil(h / stripSize);
  const sc = [];
  for (let t = 0; t < 5; t++) { const a = new Float64Array(ns); for (let s = 0; s < ns; s++) { let sum = 0; for (let y = s*stripSize; y < Math.min(h, (s+1)*stripSize); y++) sum += costs[t][y]; a[s] = sum; } sc.push(a); }
  const sseq = viterbi(sc, penalty, ns);
  const seq = new Uint8Array(h);
  for (let s = 0; s < ns; s++) for (let y = s*stripSize; y < Math.min(h, (s+1)*stripSize); y++) seq[y] = sseq[s];
  return seq;
}
function bandSeq(costs, bandSize, h) {
  const seq = new Uint8Array(h);
  for (let s = 0; s * bandSize < h; s++) {
    let bestT = 0, bestC = Infinity;
    for (let t = 0; t < 5; t++) { let sum = 0; for (let y = s*bandSize; y < Math.min(h, (s+1)*bandSize); y++) sum += costs[t][y]; if (sum < bestC) { bestC = sum; bestT = t; } }
    for (let y = s*bandSize; y < Math.min(h, (s+1)*bandSize); y++) seq[y] = bestT;
  }
  return seq;
}
function seqCost(seq, costs, h) { let s = 0; for (let y = 0; y < h; y++) s += costs[seq[y]][y]; return s; }
function snapSeq(seq, costs, h) {
  const out = Uint8Array.from(seq);
  const bounds = () => { const b = []; for (let y = 1; y < h; y++) if (out[y] !== out[y-1]) b.push(y); return b; };
  for (const step of [5, 2, 1]) {
    for (const b of bounds()) {
      const prevB = (() => { let p = 0; for (let y = 1; y < b; y++) if (out[y] !== out[y-1]) p = y; return p; })();
      const nextB = (() => { for (let y = b + 1; y < h; y++) if (out[y] !== out[y-1]) return y; return h; })();
      let bestD = 0, bestS = Infinity;
      const lo = Math.max(0, b - 12), hi = Math.min(h - 1, b + 12);
      const scoreAt = (bb) => { let s = 0; for (let y = Math.max(0, b-13); y < Math.min(h, b+13); y++) { const t = y < bb ? out[b-1] : out[b]; s += costs[t][y]; } return s; };
      bestS = scoreAt(b);
      for (let d = -12; d <= 12; d += step) {
        if (!d) continue;
        const bb = b + d;
        if (bb <= prevB || bb >= nextB || bb < 1 || bb >= h) continue;
        const s = scoreAt(bb);
        if (s < bestS) { bestS = s; bestD = d; }
      }
      if (bestD) {
        const nb = b + bestD;
        const from = out[b-1], to = out[b];
        for (let y = Math.min(b, nb); y < Math.max(b, nb); y++) out[y] = bestD > 0 ? from : to;
      }
    }
  }
  return out;
}
function greedyCosts(F, w, h, bpp) {
  // per-row per-filter lazy-match token costs (fixed-Huffman approx), charged to rows
  const rowLen = w * bpp + 1;
  const costs = [];
  for (let t = 0; t < 5; t++) {
    const data = F[t], n = data.length;
    const rowCost = new Float64Array(h);
    const head = new Int32Array(65536).fill(-1);
    let p = 0;
    while (p < n) {
      const row = Math.floor(p / rowLen);
      if (p + 2 < n) {
        const hh = (((data[p]*257 + data[p+1])*257 + data[p+2]) * 2654435761) >>> 16 & 65535;
        const cand = head[hh];
        let len = 0;
        if (cand >= 0 && p - cand <= 32768 && data[cand] === data[p] && data[cand+1] === data[p+1] && data[cand+2] === data[p+2]) {
          len = 3; const lim = Math.min(258, n - p);
          while (len < lim && data[cand+len] === data[p+len]) len++;
        }
        if (len >= 3) {
          const ls = lenSym(len), ds = distSym(p - cand);
          const bits = FIXED_LIT[ls] + LEN_EXTRA[ls-257] + 5 + DIST_EXTRA[ds];
          // charge across rows spanned
          let left = len, at = p;
          while (left > 0) { const r = Math.floor(at / rowLen); const seg = Math.min(left, (r+1)*rowLen - at); rowCost[r] += bits * seg / len; at += seg; left -= seg; }
          head[hh] = p; p += len;
        } else {
          rowCost[row] += FIXED_LIT[data[p]];
          head[hh] = p; p++;
        }
      } else { rowCost[row] += FIXED_LIT[data[p]]; p++; }
    }
    costs.push(rowCost);
  }
  return costs;
}
function entropyCosts(F, w, h, bpp) {
  const rowLen = w * bpp + 1;
  const costs = [];
  for (let t = 0; t < 5; t++) {
    const data = F[t];
    const freq = new Float64Array(256);
    for (let i = 0; i < data.length; i += 4) freq[data[i]]++;
    const bits = new Float64Array(256);
    for (let b = 0; b < 256; b++) bits[b] = freq[b] > 0 ? Math.max(0.5, Math.min(15, -Math.log2(freq[b] / (data.length / 4)))) : 15;
    const rowCost = new Float64Array(h);
    // row sums sampled at 1-in-2 bytes (x2 to keep scale vs greedy costs); the
    // cheap cost only ranks finalists, and size-1 arbitrates the winner
    for (let y = 0; y < h; y++) { let s = 0; const base = y * rowLen; for (let i = 1; i < rowLen; i += 2) s += bits[data[base+i]]; rowCost[y] = s * 2; }
    costs.push(rowCost);
  }
  return costs;
}
function bruteForceSeq(F, samples, w, h, bpp) {
  const rowLen = w * bpp + 1;
  const seq = new Uint8Array(h);
  const stream = new Uint8Array(h * rowLen); // chosen filtered stream (dict = its tail)
  const tmp = new Uint8Array(rowLen);
  for (let y = 0; y < h; y++) {
    let bestT = 0, bestSize = Infinity;
    const off = y * rowLen;
    const dict = off > 0 ? stream.subarray(Math.max(0, off - 32768), off) : undefined;
    for (let t = 0; t < 5; t++) {
      tmp[0] = t;
      tmp.set(F[t].subarray(y*rowLen+1, (y+1)*rowLen), 1);
      const sz = deflateRawSync(tmp, { level: 6, dictionary: dict }).length;
      if (sz < bestSize) { bestSize = sz; bestT = t; }
    }
    seq[y] = bestT;
    stream[off] = bestT;
    stream.set(F[bestT].subarray(y*rowLen+1, (y+1)*rowLen), off+1);
  }
  return seq;
}

// ---------- filter contest driver ----------
function smartUpSeq(samples, w, h, bpp) {
  const stride = w * bpp, seq = new Uint8Array(h);
  for (let y = 0; y < h; y++) {
    let same = false, change = false;
    if (y > 0) {
      same = true;
      for (let i = 0; i < stride; i++) if (samples[y*stride+i] !== samples[(y-1)*stride+i]) { same = false; break; }
    }
    if (same) { for (let i = bpp; i < stride; i++) if (samples[y*stride+i] !== samples[y*stride+i-bpp]) { change = true; break; } }
    seq[y] = same && change ? 2 : 0;
  }
  return seq;
}
function filterContest(form, w, h, isTop) {
  const { samples, bpp, ct } = form;
  const stride = w * bpp, rowLen = stride + 1;
  const F = buildFiltered(samples, w, h, bpp);
  const ent = entropyCosts(F, w, h, bpp);
  let hybrid = ent;
  if (isTop && bpp === 1) {
    const g = greedyCosts(F, w, h, bpp);
    hybrid = [];
    for (let t = 0; t < 5; t++) { const a = new Float64Array(h); for (let y = 0; y < h; y++) a[y] = Math.min(ent[t][y], g[t][y]); hybrid.push(a); }
  }
  const cands = [];
  const add = (name, seq) => cands.push({ name, seq });
  for (let t = 0; t < 5; t++) { const s = new Uint8Array(h).fill(t); add('fixed' + t, s); }
  // minsum
  { const s = new Uint8Array(h); const tmp = new Uint8Array(stride);
    for (let y = 0; y < h; y++) { let best = Infinity, bt = 0; for (let t = 0; t < 5; t++) { const ss = signedSum(F[t].subarray(y*rowLen+1, (y+1)*rowLen)); if (ss < best) { best = ss; bt = t; } } s[y] = bt; }
    add('minsum', s); }
  { const s = new Uint8Array(h); for (let y = 0; y < h; y++) { let bt = 0; for (let t = 1; t < 5; t++) if (ent[t][y] < ent[bt][y]) bt = t; s[y] = bt; } add('perRowEnt', s); }
  { const s = new Uint8Array(h); for (let y = 0; y < h; y++) { let bt = 0; for (let t = 1; t < 5; t++) if (hybrid[t][y] < hybrid[bt][y]) bt = t; s[y] = bt; } add('perRowHyb', s); }
  const pens = bpp === 1 ? [0, 32, 96, 256, 640, 1600, 4000] : [400, 1600, 1200, 2400];
  let bestVit = null, bestVitCost = Infinity;
  for (const p of pens) {
    const s = viterbi(hybrid, p, h); add('vit' + p, s);
    const c = seqCost(s, hybrid, h); if (c < bestVitCost) { bestVitCost = c; bestVit = s; }
  }
  for (const p of [25, 65]) add('strip10-' + p, stripSeq(hybrid, 10, p, h));
  if (F[0].length > 200000) for (const p of [40, 85]) add('strip16-' + p, stripSeq(hybrid, 16, p, h));
  add('band16', bandSeq(hybrid, 16, h));
  add('band32', bandSeq(hybrid, 32, h));
  if (bestVit) add('vitSnap', snapSeq(bestVit, hybrid, h));
  if (ct === 3) add('smartUp', smartUpSeq(samples, w, h, bpp));
  // Finalists: top 4 by cheap hybrid cost PLUS all five fixed filters, minsum and
  // brute force — always. (Measured: fixed-0 is the best filter on i002/i007 under
  // zlib-9 but ranks low by cheap entropy cost, so a cheap-only shortlist loses it.)
  const finalists = [];
  const pushC = (c) => { if (c && !finalists.some(x => x.name === c.name)) finalists.push(c); };
  const ranked = cands.map(c => ({ c, cheap: seqCost(c.seq, hybrid, h) / 8 })).sort((a, b) => a.cheap - b.cheap);
  ranked.slice(0, 4).forEach(r => pushC(r.c));
  for (let t = 0; t < 5; t++) pushC(cands.find(c => c.name === 'fixed' + t));
  pushC(cands.find(c => c.name === 'minsum'));
  if (isTop) pushC({ name: 'brute', seq: bruteForceSeq(F, samples, w, h, bpp) });
  const scored = [];
  const dbg = process.env.MAKEFUN_DEBUG;
  for (const c of (dbg === '2' ? cands.concat(isTop ? [{ name: 'brute', seq: bruteForceSeq(F, samples, w, h, bpp) }] : []) : finalists)) {
    const stream = streamFromSeq(F, c.seq, w, h, bpp);
    const size1 = deflateRawSync(stream, { level: 1 }).length;
    const size9 = dbg === '2' ? deflateSync(stream, { level: 9 }).length : 0;
    if (dbg === '2') console.error(JSON.stringify({ cand: c.name, size1, size9 }));
    scored.push({ name: c.name, seq: c.seq, stream, score: size1, size1 });
  }
  let best;
  if (isTop && dbg !== '2') {
    // Re-rank the top 3 by size-1 (plus fixed-0 if it is not among them) with zlib
    // level 6: level-1 ranking misranks multi-byte photo streams badly.
    const top3 = scored.slice().sort((a, b) => a.score - b.score).slice(0, 3);
    const f0 = scored.find(s => s.name === 'fixed0');
    if (f0 && !top3.includes(f0)) top3.push(f0);
    for (const s of top3) s.size6 = deflateSync(s.stream, { level: 6 }).length;
    best = top3.slice().sort((a, b) => a.size6 - b.size6)[0];
  } else {
    best = scored.slice().sort((a, b) => a.score - b.score)[0];
  }
  return best;
}

// ---------- main ----------
const cpuTot = { forms: 0, filter: 0, parse: 0, other: 0 };
function cpuMs(since) { const u = process.cpuUsage(since); return (u.user + u.system) / 1000; }
const ids = readdirSync(NODE).sort();
for (const id of ids) {
  const t0 = process.cpuUsage();
  const { w, h, rgba } = decodePng(new Uint8Array(readFileSync(join(NODE, id, 'image.png'))));
  const forms = buildForms(rgba, w, h);
  // screen forms by filter-0 zlib-1 size + overhead
  const stride0 = (f) => w * f.bpp + 1;
  const screened = forms.map(f => {
    const rl = stride0(f);
    const raw0 = new Uint8Array(h * rl);
    for (let y = 0; y < h; y++) { raw0[y*rl] = 0; raw0.set(f.samples.subarray(y*w*f.bpp, (y+1)*w*f.bpp), y*rl+1); }
    return { f, score: deflateRawSync(raw0, { level: 1 }).length + f.overhead };
  }).sort((a, b) => a.score - b.score);
  // stage 2: forms within 1.6x of the best filter-0 score get a fixed-filter screen
  // (filter-0 alone misranks grey/photo forms, where Sub/Paeth win by a lot)
  const best0 = screened[0].score;
  const stage2 = screened.filter(s => s.score <= best0 * 1.35).map(s => {
    const F = buildFiltered(s.f.samples, w, h, s.f.bpp);
    let m = Infinity;
    for (const t of [0, 1, 2, 4]) m = Math.min(m, deflateRawSync(F[t], { level: 1 }).length);
    return { f: s.f, score: m + s.f.overhead };
  }).sort((a, b) => a.score - b.score);
  if (stage2.length < 2 && screened.length > stage2.length) stage2.push(screened.find(s => !stage2.some(x => x.f === s.f)));
  const topForms = stage2.slice(0, 2);
  if (process.env.MAKEFUN_DEBUG) console.error(JSON.stringify({ id, screened: screened.map(s => [s.f.name, s.score]) }));
  const tForms = process.cpuUsage();
  cpuTot.forms += cpuMs(t0);
  let winner = null;
  for (let k = 0; k < topForms.length; k++) {
    const r = filterContest(topForms[k].f, w, h, k === 0);
    if (process.env.MAKEFUN_DEBUG) console.error(JSON.stringify({ id, form: topForms[k].f.name, method: r.name, score: Math.round(r.score), size1: r.size1 }));
    const tot = r.score + topForms[k].f.overhead;
    if (!winner || tot < winner.tot) winner = { ...r, form: topForms[k].f, tot };
  }
  const tFilter = process.cpuUsage();
  cpuTot.filter += cpuMs(tForms);
  const isFlat = winner.form.ct === 3;
  const isDense = winner.form.distinct > 20000;
  const custom = compressStream(winner.stream, winner.seq, w, h, winner.form.bpp, isFlat, isDense);
  const lib = deflateSync(winner.stream, { level: 9 });
  const tParse = process.cpuUsage();
  cpuTot.parse += cpuMs(tFilter);
  const chosenStream = custom.zlib.length <= lib.length ? custom.zlib : lib;
  const chosenKind = custom.zlib.length <= lib.length ? 'custom' : 'lib';
  const chunks = [['IHDR', ihdrOf(w, h, winner.form.ct)]];
  if (winner.form.ct === 3) chunks.push(['PLTE', winner.form.palette]);
  if (winner.form.trns) chunks.push(['tRNS', winner.form.trns]);
  chunks.push(['IDAT', chosenStream]);
  chunks.push(['IEND', new Uint8Array(0)]);
  const png = pngOf(chunks.map(([t, d]) => chunk(t, d)));
  mkdirSync(join(OUTD, id), { recursive: true });
  writeFileSync(join(OUTD, id, 'image.png'), png);
  const tEnd = process.cpuUsage();
  cpuTot.other += cpuMs(tParse);
  console.error(JSON.stringify({ id, form: winner.form.name, method: winner.method, filterScore: Math.round(winner.score), custom: custom.zlib.length, lib: lib.length, chosen: chosenKind, fileBytes: png.length, blocks: custom.blocks, fixedBlocks: custom.fixedCount, kraftFail: custom.kraftFail, visits: custom.visits, cpuMs: Math.round(cpuMs(t0)) }));
}
console.error(JSON.stringify({ summary: true, cpuMs: { forms: Math.round(cpuTot.forms), filter: Math.round(cpuTot.filter), parse: Math.round(cpuTot.parse), other: Math.round(cpuTot.other), total: Math.round(cpuTot.forms + cpuTot.filter + cpuTot.parse + cpuTot.other) } }));
