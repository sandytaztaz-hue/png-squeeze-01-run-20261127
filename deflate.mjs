// deflate.mjs — from-scratch optimal-parse DEFLATE (zopfli-style), Node stdlib only.
// API: deflateOpt(data: Uint8Array, opts) -> Uint8Array raw deflate stream.
const LB = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LE = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DB = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DE = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const LS = new Int32Array(259), DS = new Int32Array(32769);
for (let s = 0; s < 29; s++) for (let l = LB[s]; l < (s === 28 ? 259 : LB[s + 1]); l++) LS[l] = 257 + s;
for (let s = 0; s < 30; s++) for (let d = DB[s]; d < (s === 29 ? 32769 : DB[s + 1]); d++) DS[d] = s;
const CAND = [];
for (let L = 3; L <= 258; L++) { const t = new Set(); for (let l = 3; l <= Math.min(L, 10); l++) t.add(l); for (const b of LB) if (b <= L && b > 10) t.add(b); t.add(L); CAND[L] = [...t].sort((a, b) => a - b); }
const CLO = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
// Length-limited Huffman (package-merge), maxBits 15 (7 for code-length code).
function ll(freq, maxBits) {
  const n = freq.length, len = new Int32Array(n), syms = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) syms.push(i);
  const m = syms.length;
  if (m === 0) return len;
  if (m === 1) { len[syms[0]] = 1; return len; }
  let cur = syms.map(s => ({ w: freq[s], s: [s] })).sort((a, b) => a.w - b.w);
  const first = cur;
  for (let lvl = 1; lvl < maxBits; lvl++) {
    const pkg = [];
    for (let k = 0; k + 1 < cur.length; k += 2) pkg.push({ w: cur[k].w + cur[k + 1].w, s: cur[k].s.concat(cur[k + 1].s) });
    if (cur.length % 2 === 1) pkg.push(cur[cur.length - 1]);
    const mg = []; let i = 0, j = 0;
    while (i < pkg.length && j < first.length) { if (pkg[i].w <= first[j].w) mg.push(pkg[i++]); else mg.push(first[j++]); }
    while (i < pkg.length) mg.push(pkg[i++]);
    while (j < first.length) mg.push(first[j++]);
    cur = mg;
  }
  const take = 2 * m - 2;
  for (let i = 0; i < take && i < cur.length; i++) for (const s of cur[i].s) len[s]++;
  return len;
}
function canon(lengths) {
  const n = lengths.length, codes = new Int32Array(n);
  let mx = 0; for (let i = 0; i < n; i++) if (lengths[i] > mx) mx = lengths[i];
  const bc = new Int32Array(mx + 1);
  for (let i = 0; i < n; i++) if (lengths[i] > 0) bc[lengths[i]]++;
  const nc = new Int32Array(mx + 1); let c = 0;
  for (let b = 1; b <= mx; b++) { c = (c + bc[b - 1]) << 1; nc[b] = c; }
  for (let i = 0; i < n; i++) if (lengths[i] > 0) codes[i] = nc[lengths[i]]++;
  return { codes, mx };
}
function costsFromLengths(litLen, distLen) {
  const litCost = new Float64Array(256);
  for (let b = 0; b < 256; b++) litCost[b] = litLen[b];
  const lenCost = new Float64Array(259);
  for (let l = 3; l <= 258; l++) lenCost[l] = litLen[LS[l]] + LE[LS[l] - 257];
  const distCost = new Float64Array(32769);
  for (let d = 1; d <= 32768; d++) distCost[d] = distLen[DS[d]] + DE[DS[d]];
  return { litCost, lenCost, distCost };
}
function fixedCosts() {
  const litLen = new Int32Array(288);
  for (let i = 0; i < 144; i++) litLen[i] = 8;
  for (let i = 144; i < 256; i++) litLen[i] = 9;
  for (let i = 256; i < 280; i++) litLen[i] = 7;
  for (let i = 280; i < 288; i++) litLen[i] = 8;
  return costsFromLengths(litLen, new Int32Array(30).fill(5));
}
class BW {
  constructor() { this.bytes = []; this.acc = 0; this.nbits = 0; }
  put(code, len) { this.acc |= code << this.nbits; this.nbits += len; while (this.nbits >= 8) { this.bytes.push(this.acc & 0xff); this.acc >>>= 8; this.nbits -= 8; } }
  putRev(code, len) { let r = 0; for (let i = 0; i < len; i++) r = (r << 1) | ((code >> i) & 1); this.put(r, len); }
  flush() { if (this.nbits > 0) { this.bytes.push(this.acc & 0xff); this.acc = 0; this.nbits = 0; } }
  result() { return new Uint8Array(this.bytes); }
}
function rleLengths(litLen, distLen) {
  let hlit = litLen.length;
  while (hlit > 257 && litLen[hlit - 1] === 0) hlit--;
  let hdist = distLen.length;
  while (hdist > 1 && distLen[hdist - 1] === 0) hdist--;
  const all = [];
  for (let i = 0; i < hlit; i++) all.push(litLen[i]);
  for (let i = 0; i < hdist; i++) all.push(distLen[i]);
  const end = all.length, seq = [];
  let i = 0;
  while (i < end) {
    const v = all[i]; let run = 1;
    while (i + run < end && all[i + run] === v) run++;
    if (v === 0) {
      let r = run;
      while (r >= 11) { const t = Math.min(r, 138); seq.push([18, t - 11]); r -= t; }
      if (r >= 3) { seq.push([17, r - 3]); r = 0; }
      while (r > 0) { seq.push([0, 0]); r--; }
    } else {
      seq.push([v, 0]);
      let r = run - 1;
      while (r >= 3) { const t = Math.min(r, 6); seq.push([16, t - 3]); r -= t; }
      while (r > 0) { seq.push([v, 0]); r--; }
    }
    i += run;
  }
  return { seq, hlit, hdist };
}
function headerBits(litLen, distLen) {
  const { seq, hlit, hdist } = rleLengths(litLen, distLen);
  const cf = new Int32Array(19);
  for (const [s] of seq) cf[s]++;
  const clLen = ll(cf, 7);
  let nCl = 19;
  while (nCl > 4 && clLen[CLO[nCl - 1]] === 0) nCl--;
  let bits = 5 + 5 + 4 + 3 * nCl;
  for (const [s] of seq) { bits += clLen[s]; if (s === 16) bits += 2; else if (s === 17) bits += 3; else if (s === 18) bits += 7; }
  return { bits, seq, hlit, hdist, clLen, nCl };
}
function emitDynHeader(w, litLen, distLen) {
  const { seq, hlit, hdist, clLen, nCl } = headerBits(litLen, distLen);
  const { codes: clCodes } = canon(clLen);
  w.put(hlit - 257, 5); w.put(hdist - 1, 5); w.put(nCl - 4, 4);
  for (let i = 0; i < nCl; i++) w.put(clLen[CLO[i]], 3);
  for (const [s, e] of seq) {
    w.putRev(clCodes[s], clLen[s]);
    if (s === 16) w.put(e, 2); else if (s === 17) w.put(e, 3); else if (s === 18) w.put(e, 7);
  }
}
// Lazy match search; records the best match at each visited position.
function lazyParse(data, chainCap, recLen, recDist, nice = 128, interior = null) {
  const n = data.length;
  const head = new Int32Array(32768).fill(-1), prev = new Int32Array(n);
  const hashAt = (i) => (Math.imul((data[i] << 16) | (data[i + 1] << 8) | data[i + 2], 2654435761) >>> 17) & 32767;
  const insert = (i) => { if (i + 2 < n) { const h = hashAt(i); prev[i] = head[h]; head[h] = i; } };
  // Chain search at an arbitrary position (hash table already complete there).
  const searchIn = (pos, cap) => {
    const maxLen = Math.min(258, n - pos);
    if (maxLen < 3) return [0, 0];
    const h = hashAt(pos);
    let cand = head[h], bestLen = 2, bestDist = 0, chain = 0;
    while (cand >= 0 && chain < cap) {
      const dist = pos - cand;
      if (dist < 1) { cand = prev[cand]; chain++; continue; }
      if (dist > 32768) break;
      if (data[cand + bestLen] === data[pos + bestLen]) {
        let l = 0;
        while (l < maxLen && data[cand + l] === data[pos + l]) l++;
        if (l > bestLen) { bestLen = l; bestDist = dist; if (l === maxLen) break; }
      }
      cand = prev[cand]; chain++;
    }
    return bestLen >= 3 ? [bestLen, bestDist] : [0, 0];
  };
  const search = (pos) => {
    const maxLen = Math.min(258, n - pos);
    if (maxLen < 3) return [0, 0];
    const h = hashAt(pos);
    let cand = head[h], bestLen = 2, bestDist = 0, chain = 0, cap = chainCap;
    while (cand >= 0 && chain < cap) {
      const dist = pos - cand;
      if (dist < 1) { cand = prev[cand]; chain++; continue; }
      if (dist > 32768) break;
      if (data[cand + bestLen] === data[pos + bestLen]) {
        let l = 0;
        while (l < maxLen && data[cand + l] === data[pos + l]) l++;
        if (l > bestLen) {
          bestLen = l; bestDist = dist;
          if (l >= nice) break;
          if (l >= 32) cap = Math.max(4, chainCap >> 2);
          if (l === maxLen) break;
        }
      }
      cand = prev[cand]; chain++;
    }
    return bestLen >= 3 ? [bestLen, bestDist] : [0, 0];
  };
  const tLen = [], tVal = [];
  let pos = 0, prevLen = 0, prevDist = 0, avail = false;
  while (pos < n) {
    let curLen = 0, curDist = 0;
    if (pos + 3 <= n) { const r = search(pos); curLen = r[0]; curDist = r[1]; }
    recLen[pos] = curLen; recDist[pos] = curDist;
    if (avail) {
      if (curLen <= prevLen) {
        tLen.push(prevLen); tVal.push(prevDist);
        const s0 = pos - 1, L0 = prevLen;
        const np = pos - 1 + prevLen;
        for (let k = pos; k < np; k++) insert(k);
        // Interior search: the DP can also start a match inside this match
        // (e.g. the row-above match); record the best match at interior
        // positions so the DP can use them.
        if (interior && L0 >= interior.minLen) {
          const end = Math.min(np - 1, s0 + interior.span);
          for (let q = s0 + 1; q <= end; q++) {
            const r = searchIn(q, interior.chain);
            if (r[0] >= 3 && (r[0] > recLen[q] || (r[0] === recLen[q] && r[1] < recDist[q]))) { recLen[q] = r[0]; recDist[q] = r[1]; }
          }
        }
        pos = np; avail = false; prevLen = 0; continue;
      }
      tLen.push(0); tVal.push(data[pos - 1]);
      prevLen = curLen; prevDist = curDist; insert(pos); pos++;
    } else {
      if (curLen >= 3) { avail = true; prevLen = curLen; prevDist = curDist; insert(pos); pos++; }
      else { tLen.push(0); tVal.push(data[pos]); insert(pos); pos++; }
    }
  }
  if (avail) { tLen.push(prevLen); tVal.push(prevDist); }
  return { tLen, tVal };
}
// DP optimal parse over the recorded matches (true bit costs).
function dpParse(data, recLen, recDist, costs) {
  const n = data.length, { litCost, lenCost, distCost } = costs;
  const cost = new Float64Array(n + 1).fill(Infinity), prev = new Int32Array(n + 1);
  const tlen = new Uint16Array(n + 1), tdist = new Uint16Array(n + 1);
  cost[0] = 0;
  for (let i = 0; i < n; i++) {
    const c = cost[i], nc = c + litCost[data[i]];
    if (nc < cost[i + 1]) { cost[i + 1] = nc; prev[i + 1] = i; tlen[i + 1] = 0; }
    const L = recLen[i];
    if (L >= 3) {
      const dc = distCost[recDist[i]], cands = CAND[L];
      for (let k = 0; k < cands.length; k++) {
        const l = cands[k], j = i + l, nc2 = c + dc + lenCost[l];
        if (nc2 < cost[j]) { cost[j] = nc2; prev[j] = i; tlen[j] = l; tdist[j] = recDist[i]; }
      }
    }
  }
  const tLen = [], tVal = [];
  let j = n;
  while (j > 0) { const p = prev[j], l = tlen[j]; if (l === 0) { tLen.push(0); tVal.push(data[p]); } else { tLen.push(l); tVal.push(tdist[j]); } j = p; }
  tLen.reverse(); tVal.reverse();
  return { tLen, tVal, bits: cost[n] };
}
function freqs(tLen, tVal) {
  const lf = new Int32Array(286), df = new Int32Array(30);
  for (let i = 0; i < tLen.length; i++) { if (tLen[i] === 0) lf[tVal[i]]++; else { lf[LS[tLen[i]]]++; df[DS[tVal[i]]]++; } }
  lf[256]++;
  return { lf, df };
}
function emitBlock(w, tLen, tVal, lo, hi, isLast) {
  const lf = new Int32Array(286), df = new Int32Array(30);
  for (let i = lo; i < hi; i++) { if (tLen[i] === 0) lf[tVal[i]]++; else { lf[LS[tLen[i]]]++; df[DS[tVal[i]]]++; } }
  lf[256]++;
  const litLen = ll(lf, 15);
  let ndist = 30;
  while (ndist > 1 && df[ndist - 1] === 0) ndist--;
  const distLen = ll(df, 15).slice(0, ndist);
  if (ndist === 1 && distLen[0] === 0) distLen[0] = 1;
  let fixedBits = 3 + 7;
  for (let i = lo; i < hi; i++) {
    if (tLen[i] === 0) fixedBits += tVal[i] < 144 ? 8 : 9;
    else fixedBits += (LS[tLen[i]] <= 279 ? 7 : 8) + LE[LS[tLen[i]] - 257] + 5 + DE[DS[tVal[i]]];
  }
  const hb = headerBits(litLen, distLen);
  let dynBits = 3 + hb.bits;
  for (let i = lo; i < hi; i++) {
    if (tLen[i] === 0) dynBits += litLen[tVal[i]];
    else dynBits += litLen[LS[tLen[i]]] + LE[LS[tLen[i]] - 257] + distLen[DS[tVal[i]]] + DE[DS[tVal[i]]];
  }
  dynBits += litLen[256];
  if (fixedBits <= dynBits) {
    w.put(isLast ? 1 : 0, 1); w.put(1, 2);
    for (let i = lo; i < hi; i++) {
      if (tLen[i] === 0) { const v = tVal[i]; w.putRev(v < 144 ? (0x30 + v) : (0x190 + (v - 144)), v < 144 ? 8 : 9); }
      else {
        const s = LS[tLen[i]];
        w.putRev(s < 280 ? s - 256 : 0xC0 + (s - 280), s < 280 ? 7 : 8);
        w.put(tLen[i] - LB[s - 257], LE[s - 257]);
        const d = DS[tVal[i]];
        w.putRev(d, 5);
        w.put(tVal[i] - DB[d], DE[d]);
      }
    }
    w.putRev(0, 7);
  } else {
    w.put(isLast ? 1 : 0, 1); w.put(2, 2);
    emitDynHeader(w, litLen, distLen);
    const { codes: litCodes } = canon(litLen), { codes: distCodes } = canon(distLen);
    for (let i = lo; i < hi; i++) {
      if (tLen[i] === 0) w.putRev(litCodes[tVal[i]], litLen[tVal[i]]);
      else {
        const s = LS[tLen[i]];
        w.putRev(litCodes[s], litLen[s]);
        w.put(tLen[i] - LB[s - 257], LE[s - 257]);
        const d = DS[tVal[i]];
        w.putRev(distCodes[d], distLen[d]);
        w.put(tVal[i] - DB[d], DE[d]);
      }
    }
    w.putRev(litCodes[256], litLen[256]);
  }
}
function encodeTokens(tLen, tVal) {
  let n = 0;
  for (let i = 0; i < tLen.length; i++) n += tLen[i] === 0 ? 1 : tLen[i];
  const posOf = new Int32Array(tLen.length + 1);
  for (let i = 0; i < tLen.length; i++) posOf[i + 1] = posOf[i] + (tLen[i] === 0 ? 1 : tLen[i]);
  const blockCost = (lo, hi) => {
    const lf = new Int32Array(286), df = new Int32Array(30);
    for (let i = lo; i < hi; i++) { if (tLen[i] === 0) lf[tVal[i]]++; else { lf[LS[tLen[i]]]++; df[DS[tVal[i]]]++; } }
    lf[256]++;
    const litLen = ll(lf, 15);
    let ndist = 30;
    while (ndist > 1 && df[ndist - 1] === 0) ndist--;
    const distLen = ll(df, 15).slice(0, ndist);
    if (ndist === 1 && distLen[0] === 0) distLen[0] = 1;
    const hb = headerBits(litLen, distLen);
    let dyn = 3 + hb.bits;
    for (let i = lo; i < hi; i++) {
      if (tLen[i] === 0) dyn += litLen[tVal[i]];
      else dyn += litLen[LS[tLen[i]]] + LE[LS[tLen[i]] - 257] + distLen[DS[tVal[i]]] + DE[DS[tVal[i]]];
    }
    dyn += litLen[256];
    let fix = 3 + 7;
    for (let i = lo; i < hi; i++) {
      if (tLen[i] === 0) fix += tVal[i] < 144 ? 8 : 9;
      else fix += (LS[tLen[i]] <= 279 ? 7 : 8) + LE[LS[tLen[i]] - 257] + 5 + DE[DS[tVal[i]]];
    }
    return Math.min(dyn, fix);
  };
  let bestSplit = [0, tLen.length], bestCost = blockCost(0, tLen.length);
  for (const k of [2, 4, 8, 16, 32]) {
    const bounds = [0];
    for (let b = 1; b < k; b++) {
      const target = Math.floor(n * b / k);
      let lo = bounds[b - 1], hi = tLen.length;
      while (lo < hi) { const mid = (lo + hi) >> 1; if (posOf[mid + 1] < target) lo = mid + 1; else hi = mid; }
      bounds.push(lo + 1);
    }
    bounds.push(tLen.length);
    let c = 0;
    for (let b = 0; b < k; b++) c += blockCost(bounds[b], bounds[b + 1]);
    if (c < bestCost) { bestCost = c; bestSplit = bounds; }
  }
  const w = new BW();
  for (let b = 0; b + 1 < bestSplit.length; b++) emitBlock(w, tLen, tVal, bestSplit[b], bestSplit[b + 1], b === bestSplit.length - 2);
  w.flush();
  return w.result();
}
export function deflateOpt(data, opts = {}) {
  const n = data.length;
  const chainCap = opts.chain ?? (n <= 1048576 ? 128 : 64);
  const nice = opts.nice ?? 128, dpPasses = opts.dpPasses ?? 2;
  const recLen = new Uint16Array(n), recDist = new Uint16Array(n);
  lazyParse(data, chainCap, recLen, recDist, nice, opts.interior ?? null);
  let costs = fixedCosts(), toks = null;
  for (let p = 0; p < dpPasses; p++) {
    toks = dpParse(data, recLen, recDist, costs);
    const { lf, df } = freqs(toks.tLen, toks.tVal);
    const litLen = ll(lf, 15);
    let ndist = 30;
    while (ndist > 1 && df[ndist - 1] === 0) ndist--;
    const distLen = new Int32Array(30), dl = ll(df, 15);
    for (let i = 0; i < ndist; i++) distLen[i] = dl[i];
    if (ndist === 1 && distLen[0] === 0) distLen[0] = 1;
    costs = costsFromLengths(litLen, distLen);
  }
  toks = dpParse(data, recLen, recDist, costs);
  return encodeTokens(toks.tLen, toks.tVal);
}
export function zlibWrap(raw, data) {
  const out = new Uint8Array(2 + raw.length + 4);
  out[0] = 0x78; out[1] = 0x9c; out.set(raw, 2);
  let a = 1, b = 0;
  for (let i = 0; i < data.length;) {
    const end = Math.min(data.length, i + 5552);
    for (; i < end; i++) { a += data[i]; b += a; }
    a %= 65521; b %= 65521;
  }
  const ad = ((b << 16) | a) >>> 0;
  out[out.length - 4] = (ad >>> 24) & 0xff; out[out.length - 3] = (ad >>> 16) & 0xff;
  out[out.length - 2] = (ad >>> 8) & 0xff; out[out.length - 1] = ad & 0xff;
  return out;
}
