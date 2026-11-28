// PNG squeeze R12 — sort-once neighbourhood finder + optimal-parse DEFLATE.
// Written from the R5-R12 prose briefs. Node 22, stdlib only, deterministic.
import { readFileSync, writeFileSync, mkdirSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { inflateSync, deflateRawSync } from 'node:zlib';

const STATS = process.env.SQUEEZE_STATS === '1';
const stat = (s) => { if (STATS) process.stderr.write(s + '\n'); };
const cpuMs = () => { const u = process.cpuUsage(); return (u.user + u.system) / 1000; };

// ---------- CRC / Adler ----------
const CRC_T = (() => { const t = new Int32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; t[n] = c; } return t; })();
function crc32(b, s = 0, e = b.length) { let c = -1; for (let i = s; i < e; i++) c = CRC_T[(c ^ b[i]) & 255] ^ (c >>> 8); return (c ^ -1) >>> 0; }
function adler32(b) { let a = 1, c = 0; for (let i = 0; i < b.length;) { const e = Math.min(b.length, i + 5552); for (; i < e; i++) { a += b[i]; c += a; } a %= 65521; c %= 65521; } return ((c << 16) | a) >>> 0; }
function paeth(a, b, c) { const p = a + b - c, pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c); if (pa <= pb && pa <= pc) return a; return pb <= pc ? b : c; }

// ---------- PNG decode (own, per kit png.mjs spec) ----------
const CH = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };
function decodePng(bytes) {
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8, header = null, palette = null, trns = null; const idat = [];
  while (at < bytes.length) {
    const len = view.getUint32(at); const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    const data = bytes.subarray(at + 8, at + 8 + len); at += 12 + len;
    if (type === 'IHDR') { const dv = new DataView(data.buffer, data.byteOffset, 13); header = { w: dv.getUint32(0), h: dv.getUint32(4), ct: data[9] }; }
    else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
  }
  const bpp = CH[header.ct], stride = header.w * bpp, expected = header.h * (stride + 1);
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat), { maxOutputLength: expected + 1 });
  const samples = new Uint8Array(header.h * stride);
  for (let y = 0; y < header.h; y++) {
    const ft = raw[y * (stride + 1)], src = y * (stride + 1) + 1, o = y * stride, p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    else if (ft === 2) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    else if (ft === 3) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    else for (let i = 0; i < stride; i++) { const a = i >= bpp ? samples[o + i - bpp] : 0, bb = y > 0 ? samples[p + i] : 0, cc = y > 0 && i >= bpp ? samples[p + i - bpp] : 0; samples[o + i] = raw[src + i] + paeth(a, bb, cc); }
  }
  const n = header.w * header.h, rgba = new Uint8Array(n * 4);
  if (header.ct === 6) rgba.set(samples);
  else if (header.ct === 2) { const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5]; for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) { rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2]; rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255; } }
  else if (header.ct === 0) { const key = trns === null ? -1 : trns[1]; for (let i = 0, d = 0; i < n; i++, d += 4) { const g = samples[i]; rgba[d] = rgba[d + 1] = rgba[d + 2] = g; rgba[d + 3] = g === key ? 0 : 255; } }
  else if (header.ct === 4) { for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) { rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s]; rgba[d + 3] = samples[s + 1]; } }
  else { const en = palette.length / 3; for (let i = 0, d = 0; i < n; i++, d += 4) { const e = samples[i]; rgba[d] = palette[e * 3]; rgba[d + 1] = palette[e * 3 + 1]; rgba[d + 2] = palette[e * 3 + 2]; rgba[d + 3] = trns !== null && e < trns.length ? trns[e] : 255; } }
  return { w: header.w, h: header.h, rgba };
}
function pngOf(chunks, w, h, ct) {
  const ihdr = new Uint8Array(13); const v = new DataView(ihdr.buffer); v.setUint32(0, w); v.setUint32(4, h); ihdr[8] = 8; ihdr[9] = ct;
  const all = [['IHDR', ihdr], ...chunks, ['IEND', new Uint8Array(0)]];
  let size = 8; for (const [, d] of all) size += 12 + d.length;
  const out = new Uint8Array(size); const ov = new DataView(out.buffer);
  out.set([137, 80, 78, 71, 13, 10, 26, 10], 0); let at = 8;
  for (const [type, data] of all) { ov.setUint32(at, data.length); for (let i = 0; i < 4; i++) out[at + 4 + i] = type.charCodeAt(i); out.set(data, at + 8); ov.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length)); at += 12 + data.length; }
  return out;
}

// ---------- DEFLATE tables ----------
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXT = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXT = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const LEN_ENDS = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
function lenSymFor(len) { return LEN_SYM[len]; }
function distSymFor(d) { return DIST_SYM[d]; }
const LEN_SYM = (() => { const t = new Int8Array(259); for (let L = 3; L <= 258; L++) { if (L === 258) { t[L] = 28; continue; } let s = 28; for (let i = 0; i < 28; i++) if (L <= LEN_BASE[i] + (LEN_EXT[i] ? (1 << LEN_EXT[i]) - 1 : 0)) { s = i; break; } t[L] = s; } return t; })();
const DIST_SYM = (() => { const t = new Int8Array(32769); for (let d = 1; d <= 32768; d++) { let s = 29; for (let i = 0; i < 30; i++) if (d <= DIST_BASE[i] + (DIST_EXT[i] ? (1 << DIST_EXT[i]) - 1 : 0)) { s = i; break; } t[d] = s; } return t; })();
const EP_FOR = (() => { const t = new Int8Array(259); for (let L = 3; L <= 258; L++) { let ep = 3; for (const e of LEN_ENDS) if (e < L && e > ep) ep = e; t[L] = ep; } return t; })();

// ---------- Huffman lengths: heap-free merge + clamp + exact Kraft repair ----------
function huffLengths(freq, maxLen, nSym) {
  const len = new Uint8Array(nSym);
  const syms = []; for (let s = 0; s < nSym; s++) if (freq[s] > 0) syms.push(s);
  if (syms.length === 0) return len;
  if (syms.length === 1) { len[syms[0]] = 1; return len; }
  const m = syms.length, tot = 2 * m - 1;
  const fArr = new Float64Array(tot), parent = new Int32Array(tot).fill(-1);
  for (let i = 0; i < m; i++) fArr[i] = freq[syms[i]];
  const heap = new Int32Array(tot); let hs = 0;
  const push = (x) => { let i = hs++; heap[i] = x; while (i > 0) { const p = (i - 1) >> 1; if (fArr[heap[p]] <= fArr[heap[i]]) break; const t = heap[p]; heap[p] = heap[i]; heap[i] = t; i = p; } };
  const pop = () => { const top = heap[0]; heap[0] = heap[--hs]; let i = 0; for (;;) { const l = i * 2 + 1, r = l + 1; let s = i; if (l < hs && fArr[heap[l]] < fArr[heap[s]]) s = l; if (r < hs && fArr[heap[r]] < fArr[heap[s]]) s = r; if (s === i) break; const t = heap[s]; heap[s] = heap[i]; heap[i] = t; i = s; } return top; };
  for (let i = 0; i < m; i++) push(i);
  let next = m;
  while (hs > 1) { const a = pop(), b = pop(); parent[a] = next; parent[b] = next; fArr[next] = fArr[a] + fArr[b]; push(next); next++; }
  for (let i = 0; i < m; i++) { let d = 0, x = i; while (parent[x] >= 0) { d++; x = parent[x]; } len[syms[i]] = d; }
  let mx = 0; for (const s of syms) if (len[s] > mx) mx = len[s];
  if (mx > maxLen) { for (const s of syms) if (len[s] > maxLen) len[s] = maxLen; }
  // exact Kraft repair in units of 2^(maxLen-len), target 2^maxLen.
  // Use the finest step available: lengthen the LONGEST code (smallest Kraft step)
  // when oversubscribed, shorten the LONGEST code above 1 when undersubscribed.
  const target = 1 << maxLen;
  const kraft = () => { let s = 0; for (const x of syms) s += 1 << (maxLen - len[x]); return s; };
  let guard = 0;
  while (kraft() < target && guard++ < 100000) {
    let best = -1, bl = -1, bf = -1; for (const s of syms) if (len[s] > 1 && (len[s] > bl || (len[s] === bl && freq[s] > bf))) { bl = len[s]; bf = freq[s]; best = s; }
    if (best < 0) break; len[best]--;
  }
  guard = 0;
  while (kraft() > target && guard++ < 100000) {
    let best = -1, bl = -1, bf = Infinity; for (const s of syms) if (len[s] < maxLen && (len[s] > bl || (len[s] === bl && freq[s] < bf))) { bl = len[s]; bf = freq[s]; best = s; }
    if (best < 0) break; len[best]++;
  }
  return len;
}
function kraftOk(len, maxLen) { let s = 0; for (let i = 0; i < len.length; i++) if (len[i] > 0) s += 1 << (maxLen - len[i]); return s === (1 << maxLen); }
function canonCodes(len) {
  const n = len.length, code = new Uint16Array(n); const cnt = new Int32Array(16);
  for (let i = 0; i < n; i++) if (len[i]) cnt[len[i]]++;
  let next = 0; const nc = new Int32Array(16);
  for (let l = 1; l < 16; l++) { next = (next + cnt[l - 1]) << 1; nc[l] = next; }
  for (let i = 0; i < n; i++) if (len[i]) code[i] = nc[len[i]]++;
  return code;
}
function revBits(c, l) { let r = 0; for (let i = 0; i < l; i++) { r = (r << 1) | ((c >> i) & 1); } return r; }

// ---------- Bit writer (MSB-first Huffman codes via reversed writeBits) ----------
class BW {
  constructor(cap) { this.buf = new Uint8Array(cap); this.at = 0; this.bit = 0; this.acc = 0; }
  bits(v, n) { this.acc |= (v & ((1 << n) - 1)) << this.bit; this.bit += n; while (this.bit >= 8) { this.buf[this.at++] = this.acc & 255; this.acc >>>= 8; this.bit -= 8; } }
  code(c, l) { this.bits(revBits(c, l), l); }
  align() { if (this.bit > 0) { this.buf[this.at++] = this.acc & 255; this.acc = 0; this.bit = 0; } }
  bytes() { return this.buf.subarray(0, this.at); }
}

// ---------- CL header encoding ----------
const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
function encodeLengthsRLE(lens, n) {
  // returns array of (sym, extra, extraBits) items
  const out = []; let i = 0;
  while (i < n) {
    const v = lens[i];
    if (v === 0) { let j = i; while (j < n && lens[j] === 0) j++; let run = j - i; i = j;
      while (run >= 11) { const t = Math.min(run, 138); out.push([18, t - 11, 7]); run -= t; }
      if (run >= 3) out.push([17, run - 3, 3]); else while (run-- > 0) out.push([0, 0, 0]);
    } else { let j = i + 1; while (j < n && lens[j] === v) j++; let run = j - i; i = j;
      out.push([v, 0, 0]); run--;
      while (run >= 3) { const t = Math.min(run, 6); out.push([16, t - 3, 2]); run -= t; }
      while (run-- > 0) out.push([v, 0, 0]);
    }
  }
  return out;
}
function headerBits(litLen, distLen) {
  let hlit = 286; while (hlit > 257 && litLen[hlit - 1] === 0) hlit--;
  let hdist = 30; while (hdist > 1 && distLen[hdist - 1] === 0) hdist--;
  const items = encodeLengthsRLE(litLen, hlit).concat(encodeLengthsRLE(distLen, hdist));
  const cf = new Int32Array(19); for (const [s] of items) cf[s]++;
  if (cf.filter(x => x > 0).length < 2) cf[0] = 1, cf[1] = 1;
  const cl = huffLengths(cf, 7, 19);
  if (!kraftOk(cl, 7)) {
    // Balanced-tree fallback: a complete prefix code always exists for n<=128 symbols.
    // Lengths L-1 (a symbols) and L (b symbols) with 2a+b=2^L, L=ceil(log2 n); shortest to most frequent.
    const used = []; for (let s = 0; s < 19; s++) if (cf[s] > 0) used.push(s);
    used.sort((a, b) => cf[b] - cf[a]);
    const n = used.length; const L = Math.max(1, Math.ceil(Math.log2(n)));
    const a = (1 << L) - n, b = 2 * n - (1 << L);
    cl.fill(0);
    for (let i = 0; i < n; i++) cl[used[i]] = i < a ? L - 1 : L;
    void b;
  }
  let hclen = 19; while (hclen > 4 && cl[CL_ORDER[hclen - 1]] === 0) hclen--;
  let bits = 5 + 5 + 4 + hclen * 3;
  for (const [s, e, eb] of items) bits += cl[s] + eb;
  return { bits, hlit, hdist, hclen, cl, items };
}

// ---------- Sorted-bucket neighbourhood finder (R12 MANDATORY 1) ----------
function buildFinder(data, bpp, rowLen) {
  const N = data.length;
  const run = new Uint16Array(N + 1);
  for (let i = N - 1; i >= 0; i--) run[i] = (i + 1 < N && data[i] === data[i + 1]) ? Math.min(258, run[i + 1] + 1) : 1;
  const per = new Uint16Array(N + 1);
  if (bpp > 1) for (let i = N - 1; i >= 0; i--) per[i] = (i >= bpp && data[i] === data[i - bpp]) ? Math.min(258, per[i + 1] + 1) : 0;
  const hashOf = (i) => (((data[i] << 16) | (data[i + 1] << 8) | data[i + 2]) * 2654435761 >>> 16) & 65535;
  // previous-occurrence chain per 3-byte hash: the near-distance (cheap) matches live here,
  // not among the suffix-sorted neighbours — a len-10 match at dist 20 beats a len-200 match at dist 5121
  const prevPos = new Int32Array(N).fill(-1);
  { const last = new Int32Array(65536).fill(-1); for (let i = 0; i + 2 < N; i++) { const h = hashOf(i); prevPos[i] = last[h]; last[h] = i; } }
  const cnt = new Uint32Array(65536);
  for (let i = 0; i + 2 < N; i++) cnt[hashOf(i)]++;
  const start = new Uint32Array(65537); for (let h = 0; h < 65536; h++) start[h + 1] = start[h] + cnt[h];
  const pos = new Int32Array(N); const cur = start.slice(0, 65536);
  for (let i = 0; i + 2 < N; i++) pos[cur[hashOf(i)]++] = i;
  const rank = new Int32Array(N).fill(-1);
  let capped = 0, sortedBuckets = 0;
  const tmp = [];
  for (let h = 0; h < 65536; h++) {
    const s = start[h], e = start[h + 1], sz = e - s;
    if (sz <= 1) { if (sz === 1) rank[pos[s]] = 0; continue; }
    if (sz > 4096) { capped++; for (let k = 0; k < sz; k++) rank[pos[s + k]] = k; continue; }
    sortedBuckets++;
    tmp.length = 0; for (let k = s; k < e; k++) tmp.push(pos[k]);
    tmp.sort((a, b) => {
      let k = 3; const lim = Math.min(258, N - a, N - b);
      while (k < lim && data[a + k] === data[b + k]) k++;
      if (k >= lim) { if (N - a === N - b) return a - b; return (N - a) - (N - b); }
      return data[a + k] - data[b + k];
    });
    for (let k = 0; k < sz; k++) { pos[s + k] = tmp[k]; rank[tmp[k]] = k; }
  }
  const bestLen = new Uint16Array(N), bestDist = new Int32Array(N);
  const candCnt = new Uint8Array(N), candLen = new Int32Array(N * 4), candDist = new Int32Array(N * 4);
  let comparisons = 0;
  const distCost = (d) => 5 + DIST_EXT[DIST_SYM[d]];
  const tmpL = new Int32Array(16), tmpD = new Int32Array(16);
  const addCand = (nc, l, d) => {
    if (l < 3) return nc;
    for (let j = 0; j < nc; j++) if (tmpD[j] === d) { if (l > tmpL[j]) tmpL[j] = l; return nc; }
    if (nc < 16) { tmpL[nc] = l; tmpD[nc] = d; nc++; }
    return nc;
  };
  for (let i = 0; i < N; i++) {
    let nc = 0;
    // run fast path — MANDATORY 0: dist-1 valid ONLY when data[i]==data[i-1]
    if (i > 0 && data[i] === data[i - 1] && run[i] >= 3) nc = addCand(nc, Math.min(run[i], N - i), 1);
    if (bpp > 1 && per[i] >= 3) nc = addCand(nc, Math.min(per[i], N - i), bpp);
    let bl = 0; for (let j = 0; j < nc; j++) if (tmpL[j] > bl) bl = tmpL[j];
    // row-above probes (1 and 2 scanlines) — only while no long match yet
    if (bl < 200) for (let r = 1; r <= 2; r++) {
      const q = i - r * rowLen; if (q < 0) break;
      let k = 0; const lim = Math.min(258, N - i);
      while (k < lim && data[i + k] === data[q + k]) k++;
      if (k >= 3) nc = addCand(nc, k, r * rowLen);
      if (k > bl) bl = k;
    }
    if (i + 2 < N && bl < 200) {
      const h = hashOf(i), s = start[h], e = start[h + 1], rk = rank[i];
      for (let d = 1; d <= 8; d++) {
        for (let side = 0; side < 2; side++) {
          const rr = side === 0 ? rk - d : rk + d;
          if (rr < 0 || rr >= e - s) continue;
          const q = pos[s + rr]; if (q >= i || i - q > 32768) continue;
          comparisons++;
          let k = 0; const lim = Math.min(258, N - i);
          while (k < lim && data[i + k] === data[q + k]) k++;
          if (k >= 3) nc = addCand(nc, k, i - q);
          if (k > bl) bl = k;
        }
      }
    }
    // previous-occurrence chain: near (cheap) matches, up to 4 back — run even when bl is long,
    // because a short cheap match can still be Pareto-optimal against a long expensive one;
    // skip it when a >=128 match already exists (the chain's value there is ~0, its cost is not)
    if (i + 2 < N && bl < 128) {
      let q = prevPos[i];
      for (let step = 0; step < 12 && q >= 0; step++) {
        if (i - q <= 32768) {
          comparisons++;
          let k = 0; const lim = Math.min(258, N - i);
          while (k < lim && data[i + k] === data[q + k]) k++;
          if (k >= 3) nc = addCand(nc, k, i - q);
        }
        q = prevPos[q];
      }
    }
    // insertion sort tmp by len desc, dist asc
    for (let a = 1; a < nc; a++) { const l = tmpL[a], d = tmpD[a]; let b = a - 1; while (b >= 0 && (tmpL[b] < l || (tmpL[b] === l && tmpD[b] > d))) { tmpL[b + 1] = tmpL[b]; tmpD[b + 1] = tmpD[b]; b--; } tmpL[b + 1] = l; tmpD[b + 1] = d; }
    // Pareto prune: a shorter candidate survives only if its distance is cheaper than
    // every longer kept candidate's distance. Cap 4.
    let kept = 0;
    for (let a = 0; a < nc && kept < 4; a++) {
      const l = tmpL[a], d = tmpD[a];
      let dominated = false;
      for (let j = 0; j < kept; j++) if (distCost(candDist[i * 4 + j]) <= distCost(d)) { dominated = true; break; }
      if (!dominated) { candLen[i * 4 + kept] = l; candDist[i * 4 + kept] = d; kept++; }
    }
    bestLen[i] = kept ? candLen[i * 4] : 0; bestDist[i] = kept ? candDist[i * 4] : 0;
    candCnt[i] = kept;
  }
  return { bestLen, bestDist, candCnt, candLen, candDist, comparisons, capped, sortedBuckets, pos, start, rank, run, per };
}
// finder diagnostic vs brute force over the same-hash bucket
function finderDiag(data, f, rowLen, bpp) {
  const N = data.length; const step = Math.max(1, Math.floor(N / 1200));
  let n = 0, noMatch = 0, strict = 0; const perInst = { n: 0, noMatch: 0, strict: 0 };
  for (let i = 0; i + 2 < N; i += step) {
    // brute best over same-hash positions + run + row probes
    let brute = 0;
    if (i > 0 && data[i] === data[i - 1]) brute = Math.max(brute, Math.min(f.run[i], N - i));
    if (bpp > 1) brute = Math.max(brute, Math.min(f.per[i], N - i));
    for (let r = 1; r <= 2; r++) { const q = i - r * rowLen; if (q < 0) break; let k = 0; const lim = Math.min(258, N - i); while (k < lim && data[i + k] === data[q + k]) k++; brute = Math.max(brute, k); }
    const h = (((data[i] << 16) | (data[i + 1] << 8) | data[i + 2]) * 2654435761 >>> 16) & 65535;
    const s = f.start[h], e = f.start[h + 1];
    let scanned = 0;
    for (let k = s; k < e && scanned < 400; k++) { const q = f.pos[k]; if (q >= i || i - q > 32768) continue; scanned++; let m = 0; const lim = Math.min(258, N - i); while (m < lim && data[i + m] === data[q + m]) m++; if (m > brute) brute = m; }
    if (brute >= 32) {
      n++; const got = f.bestLen[i];
      if (got < 3) noMatch++;
      if (got < brute - 3) strict++;
    }
  }
  perInst.n = n; perInst.noMatch = noMatch; perInst.strict = strict;
  return perInst;
}

// ---------- Optimal-parse DP per block ----------
function parseBlock(data, f, bs, be, iters, flat) {
  const n = be - bs;
  const dp = new Int32Array(n + 1), chLen = new Int32Array(n + 1), chDist = new Int32Array(n + 1);
  let litCost = new Int32Array(256), lenCost = new Int32Array(259), distCost = new Int32Array(32769);
  const fixedLit = new Int32Array(256); for (let i = 0; i < 144; i++) fixedLit[i] = 8 * 16; for (let i = 144; i < 256; i++) fixedLit[i] = 9 * 16; fixedLit[256] = 7 * 16;
  // fixed literal/length costs (lit 0..255 above; 256..285: 7/8 bits)
  const setFixed = () => {
    litCost.set(fixedLit);
    for (let L = 3; L <= 258; L++) { const s = lenSymFor(L); litCost[257 + s] = 0; lenCost[L] = ((s < 23 ? 7 : 8) + LEN_EXT[s]) * 16; }
    for (let d = 1; d <= 32768; d++) distCost[d] = (5 + DIST_EXT[distSymFor(d)]) * 16;
    // litCost entries 257..285 hold length-symbol costs separately in lenCost; store also in litCost for freq calc convenience
    for (let s = 0; s < 29; s++) litCost[257 + s] = (s < 23 ? 7 : 8) * 16;
  };
  setFixed();
  let best = null, bestBits = Infinity, prevBits = Infinity, stall = 0;
  for (let iter = 0; iter < iters; iter++) {
    dp.fill(2000000000); dp[0] = 0; chLen[0] = 0;
    const lc = litCost, ln = lenCost, dc = distCost;
    for (let i = 0; i < n; i++) {
      const di = dp[i]; if (di >= 2000000000) continue; const gi = bs + i;
      const rem = n - i;
      // literal
      const nl = di + lc[data[gi]];
      if (nl < dp[i + 1]) { dp[i + 1] = nl; chLen[i + 1] = 0; chDist[i + 1] = 0; }
      const cc = f.candCnt[gi];
      for (let ci = 0; ci < cc; ci++) {
        const L0 = Math.min(f.candLen[gi * 4 + ci], rem), bd = f.candDist[gi * 4 + ci];
        if (L0 < 3 || bd <= 0) continue;
        const ep = EP_FOR[L0];
        for (let oi = 0; oi < 3; oi++) {
          let L = -1;
          if (oi === 0) L = L0;
          else if (oi === 1) { if (L0 > 3) L = 3; }
          else if (ci === 0 && ep > 3) L = ep;
          if (L < 3 || L > rem) continue;
          let c = di + ln[L] + dc[bd];
          if (iter === 5) c = di + Math.floor(ln[L] * 0.9) + Math.floor(dc[bd] * 0.9);
          if (c < dp[i + L]) { dp[i + L] = c; chLen[i + L] = L; chDist[i + L] = bd; }
        }
      }
    }
    // backtrack
    const toks = []; let j = n;
    const litFreq = new Int32Array(286), distFreq = new Int32Array(30);
    litFreq[256] = 1;
    while (j > 0) { const L = chLen[j]; if (L === 0) { const b = data[bs + j - 1]; toks.push([0, b, 0]); litFreq[b]++; j--; } else { const d = chDist[j]; toks.push([1, L, d]); const s = lenSymFor(L); litFreq[257 + s]++; distFreq[distSymFor(d)]++; j -= L; } }
    toks.reverse();
    // a single-symbol distance alphabet needs a dummy symbol for a complete Kraft tree
    let ndist = 0; for (let s = 0; s < 30; s++) if (distFreq[s] > 0) ndist++;
    if (ndist === 1) distFreq[distFreq[0] > 0 ? 1 : 0]++;
    // header bits + total
    const ll = huffLengths(litFreq, 15, 286), dl = huffLengths(distFreq, 15, 30);
    // ensure dist has >=2 symbols for Kraft: huffLengths handles single via len 1; force dummy if needed
    let dynBits = dp[n];
    for (let s = 0; s < 286; s++) dynBits += litFreq[s] * 0; // dp already in scaled units; recompute exact data bits below
    let dataBits = 0; for (let s = 0; s < 286; s++) dataBits += litFreq[s] * ll[s]; for (let s = 0; s < 30; s++) dataBits += distFreq[s] * dl[s];
    for (const t of toks) if (t[0] === 1) dataBits += LEN_EXT[lenSymFor(t[1])] + DIST_EXT[distSymFor(t[2])];
    const hb = headerBits(ll, dl);
    const totalBits = dataBits + hb.bits;
    // fixed-block data bits
    let fixedBits = 0; for (let s = 0; s < 256; s++) fixedBits += litFreq[s] * fixedLit[s]; for (let s = 0; s < 29; s++) fixedBits += litFreq[257 + s] * (s < 23 ? 7 : 8); fixedBits += litFreq[256] * 7;
    for (let s = 0; s < 30; s++) fixedBits += distFreq[s] * 5;
    for (const t of toks) if (t[0] === 1) fixedBits += LEN_EXT[lenSymFor(t[1])] + DIST_EXT[distSymFor(t[2])];
    const useFixed = fixedBits + 3 <= totalBits;
    const bits = useFixed ? fixedBits + 3 : totalBits;
    if (bits < bestBits) { bestBits = bits; best = { toks, litFreq, distFreq, ll, dl, hb, useFixed, fixedBits, totalBits }; }
    if (iter >= 2) { if (prevBits - bits < Math.max(16, prevBits * 0.0005)) { if (++stall >= 2 && iter >= 4) break; } else stall = 0; }
    prevBits = bits;
    if (iter === iters - 1) break;
    // re-derive costs from this parse's frequencies
    const nll = huffLengths(litFreq, 15, 286), ndl = huffLengths(distFreq, 15, 30);
    for (let s = 0; s < 256; s++) litCost[s] = (nll[s] || 8) * 16;
    for (let s = 0; s < 29; s++) litCost[257 + s] = (nll[257 + s] || 8) * 16;
    litCost[256] = (nll[256] || 7) * 16;
    for (let L = 3; L <= 258; L++) { const s = lenSymFor(L); lenCost[L] = (nll[257 + s] * 16) + LEN_EXT[s] * 16; }
    for (let d = 1; d <= 32768; d++) { const s = distSymFor(d); distCost[d] = (ndl[s] || 5) * 16 + DIST_EXT[s] * 16; }
  }
  return best;
}
function emitBlock(bw, parse, isFinal) {
  const { toks, litFreq, distFreq, ll, dl, hb, useFixed } = parse;
  bw.bits(isFinal ? 1 : 0, 1);
  let litLen, distLen, litCode, distCode;
  if (useFixed) {
    bw.bits(1, 2);
    litLen = new Uint8Array(288); for (let i = 0; i < 144; i++) litLen[i] = 8; for (let i = 144; i < 256; i++) litLen[i] = 9; for (let i = 256; i < 280; i++) litLen[i] = 7; for (let i = 280; i < 288; i++) litLen[i] = 8;
    distLen = new Uint8Array(30).fill(5);
  } else {
    bw.bits(2, 2);
    litLen = ll; distLen = dl;
    bw.bits(hb.hlit - 257, 5); bw.bits(hb.hdist - 1, 5); bw.bits(hb.hclen - 4, 4);
    for (let k = 0; k < hb.hclen; k++) bw.bits(hb.cl[CL_ORDER[k]], 3);
    const clCode = canonCodes(hb.cl);
    // encode items with RLE using CL codes (need to regenerate items deterministically)
    const items = encodeLengthsRLE(litLen, hb.hlit).concat(encodeLengthsRLE(distLen, hb.hdist));
    for (const [s, e, eb] of items) { bw.code(clCode[s], hb.cl[s]); if (eb) bw.bits(e, eb); }
  }
  litCode = canonCodes(litLen); distCode = canonCodes(distLen);
  for (const t of toks) {
    if (t[0] === 0) bw.code(litCode[t[1]], litLen[t[1]]);
    else { const s = lenSymFor(t[1]); bw.code(litCode[257 + s], litLen[257 + s]); if (LEN_EXT[s]) bw.bits(t[1] - LEN_BASE[s], LEN_EXT[s]); const ds = distSymFor(t[2]); bw.code(distCode[ds], distLen[ds]); if (DIST_EXT[ds]) bw.bits(t[2] - DIST_BASE[ds], DIST_EXT[ds]); }
  }
  bw.code(litCode[256], litLen[256]);
  return { litLen, distLen };
}
// compress one filtered stream; returns zlib-wrapped bytes, custom size, lib size, kraft status
function compressStream(data, bpp, rowLen, iters) {
  const t0 = cpuMs();
  const f = buildFinder(data, bpp, rowLen);
  const finderMs = cpuMs() - t0;
  const lib = deflateRawSync(data, { level: 9, memLevel: 9 });
  const libBytes = lib.length + 6;
  const diag = STATS ? finderDiag(data, f, rowLen, bpp) : { n: 0, noMatch: 0, strict: 0 };
  const rowBytes = rowLen;
  const blockCap = bpp === 1 ? 131072 : 524288;
  const blockSize = Math.max(rowBytes * 8, Math.min(blockCap, Math.ceil(data.length / 4 / rowBytes) * rowBytes || rowBytes));
  const bounds = []; let bs = 0;
  while (bs < data.length) { let be = Math.min(data.length, bs + blockSize); be = Math.ceil(be / rowBytes) * rowBytes; if (be > data.length) be = data.length; bounds.push([bs, be]); bs = be; }
  const cap = data.length + 1024;
  const bw = new BW(cap);
  let kraftBad = 0, kraftChecked = 0, kraftBadLit = 0, kraftBadDist = 0;
  const t1 = cpuMs();
  for (let bi = 0; bi < bounds.length; bi++) {
    const [s, e] = bounds[bi];
    const parse = parseBlock(data, f, s, e, iters, bpp === 1);
    const r = emitBlock(bw, parse, bi === bounds.length - 1);
    kraftChecked += 2;
    if (!parse.useFixed) {
      if (!kraftOk(r.litLen, 15)) { kraftBad++; kraftBadLit++; }
      if (!kraftOk(r.distLen, 15)) { kraftBad++; kraftBadDist++; }
      if (parse.hb && !kraftOk(parse.hb.cl, 7)) kraftBad++;
    }
  }
  bw.align();
  const defBytes = bw.bytes();
  const parseMs = cpuMs() - t1;
  // zlib wrapper
  const out = new Uint8Array(defBytes.length + 6);
  out[0] = 0x78; out[1] = 0x9c; out.set(defBytes, 2);
  new DataView(out.buffer).setUint32(2 + defBytes.length, adler32(data));
  return { bytes: out, customBytes: out.length, libBytes, finderMs, parseMs, diag, comparisons: f.comparisons, capped: f.capped, kraftBad, kraftBadLit, kraftBadDist, kraftChecked, blocks: bounds.length };
}

// ---------- Filtering ----------
function filterRowInto(type, cur, prev, bpp, out) {
  const n = cur.length; let s = 0;
  const ss = (v) => { s += v < 128 ? v : 256 - v; };
  if (type === 0) { out.set(cur); for (let i = 0; i < n; i++) ss(cur[i]); }
  else if (type === 1) for (let i = 0; i < n; i++) { const v = cur[i] - (i >= bpp ? cur[i - bpp] : 0); out[i] = v; ss(v); }
  else if (type === 2) for (let i = 0; i < n; i++) { const v = cur[i] - (prev === null ? 0 : prev[i]); out[i] = v; ss(v); }
  else if (type === 3) for (let i = 0; i < n; i++) { const v = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1); out[i] = v; ss(v); }
  else for (let i = 0; i < n; i++) {
    const a = i >= bpp ? cur[i - bpp] : 0, b = prev === null ? 0 : prev[i], c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
    const p = a + b - c, pa = p > a ? p - a : a - p, pb = p > b ? p - b : b - p, pc = p > c ? p - c : c - p;
    const pr = pa <= pb && pa <= pc ? a : pb <= pc ? b : c;
    const v = cur[i] - pr; out[i] = v; ss(v);
  }
  return s;
}
function buildFiltered(samples, w, h, bpp) {
  const stride = w * bpp, rowLen = stride + 1;
  const filt = []; const minsum = new Uint8Array(h); const rowCost = []; // rowCost[f][y] signed sum
  for (let f = 0; f < 5; f++) { filt.push(new Uint8Array(h * rowLen)); rowCost.push(new Float64Array(h)); }
  const trial = new Uint8Array(stride);
  for (let y = 0; y < h; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    let best = Infinity, bt = 0;
    for (let f = 0; f < 5; f++) {
      const s = filterRowInto(f, cur, prev, bpp, trial);
      filt[f][y * rowLen] = f; filt[f].set(trial, y * rowLen + 1);
      rowCost[f][y] = s;
      if (s < best) { best = s; bt = f; }
    }
    minsum[y] = bt;
  }
  return { filt, minsum, rowCost, rowLen, stride };
}
function viterbi(costs, h, penalty) {
  const dp = new Float64Array(5), ndp = new Float64Array(5);
  const back = new Int8Array(h * 5);
  for (let f = 0; f < 5; f++) dp[f] = costs[f][0];
  for (let y = 1; y < h; y++) {
    for (let f = 0; f < 5; f++) { let best = Infinity, bf = 0; for (let g = 0; g < 5; g++) { const c = dp[g] + (g === f ? 0 : penalty); if (c < best) { best = c; bf = g; } } ndp[f] = best + costs[f][y]; back[y * 5 + f] = bf; }
    dp.set(ndp);
  }
  let bf = 0; for (let f = 1; f < 5; f++) if (dp[f] < dp[bf]) bf = f;
  const seq = new Uint8Array(h); seq[h - 1] = bf;
  for (let y = h - 1; y >= 1; y--) { bf = back[y * 5 + bf]; seq[y - 1] = bf; }
  return seq;
}
function assemble(filt, seq, h, rowLen) {
  const out = new Uint8Array(h * rowLen);
  for (let y = 0; y < h; y++) out.set(filt[seq[y]].subarray(y * rowLen, (y + 1) * rowLen), y * rowLen);
  return out;
}
function bandSeq(costs, h, band) {
  const seq = new Uint8Array(h);
  for (let y0 = 0; y0 < h; y0 += band) {
    let bf = 0, bc = Infinity;
    for (let f = 0; f < 5; f++) { let s = 0; for (let y = y0; y < Math.min(h, y0 + band); y++) s += costs[f][y]; if (s < bc) { bc = s; bf = f; } }
    for (let y = y0; y < Math.min(h, y0 + band); y++) seq[y] = bf;
  }
  return seq;
}

// ---------- Colour forms ----------
function analyse(rgba, w, h) {
  const n = w * h; const map = new Map(); let grey = true, allOpaque = true; const alphas = new Set();
  let distinct = 0;
  for (let i = 0; i < n; i++) {
    const r = rgba[i * 4], g = rgba[i * 4 + 1], b = rgba[i * 4 + 2], a = rgba[i * 4 + 3];
    if (r !== g || g !== b) grey = false;
    if (a !== 255) allOpaque = false;
    alphas.add(a);
    const key = (r << 24) | (g << 16) | (b << 8) | a;
    if (!map.has(key)) { map.set(key, (map.get(key) || 0) + 1); distinct++; if (distinct > 256 && !grey) { /* keep counting cheaply via map size */ } }
    else map.set(key, map.get(key) + 1);
  }
  return { grey, allOpaque, alphas, map, distinct: map.size };
}
function paletteOrderings(map) {
  // entries: {r,g,b,a,count}
  const ents = [];
  for (const [key, count] of map) ents.push({ r: (key >> 24) & 255, g: (key >> 16) & 255, b: (key >> 8) & 255, a: key & 255, count });
  const byFreq = ents.slice().sort((a, b) => b.count - a.count);
  const orders = [];
  orders.push({ name: 'freq', list: byFreq });
  // freq with background (most frequent) pinned at 0 is same as freq (most frequent is first) — skip duplicate
  const byLum = ents.slice().sort((a, b) => (0.299 * a.r + 0.587 * a.g + 0.114 * a.b) - (0.299 * b.r + 0.587 * b.g + 0.114 * b.b));
  orders.push({ name: 'lum', list: byLum });
  return orders;
}
// adjacency ordering needs pixel scan; built by caller with adjacency matrix
function adjacencyOrder(ents, adj, bgIdx) {
  const n = ents.length; const used = new Uint8Array(n); const order = [];
  let cur = bgIdx; used[cur] = 1; order.push(cur);
  while (order.length < n) {
    let best = -1, bc = -1;
    for (let i = 0; i < n; i++) if (!used[i]) { const c = adj[cur * n + i] + adj[i * n + cur]; if (c > bc) { bc = c; best = i; } }
    if (best < 0) { for (let i = 0; i < n; i++) if (!used[i]) { best = i; break; } }
    used[best] = 1; order.push(best); cur = best;
  }
  return order.map(i => ents[i]);
}

// ---------- Per-instance encode ----------
function encodeInstance(id, rgba, w, h) {
  const tStart = cpuMs(); const phase = { forms: 0, filter: 0, finder: 0, parse: 0 };
  const an = analyse(rgba, w, h); const n = w * h;
  const forms = [];
  const mkSamples = (bpp, fn) => { const s = new Uint8Array(n * bpp); fn(s); return s; };
  if (an.grey) {
    forms.push({ name: 'grey', ct: 0, bpp: 1, samples: mkSamples(1, s => { for (let i = 0; i < n; i++) s[i] = rgba[i * 4]; }), plte: null, trns: null });
    if (!an.allOpaque) forms.push({ name: 'greyalpha', ct: 4, bpp: 2, samples: mkSamples(2, s => { for (let i = 0; i < n; i++) { s[i * 2] = rgba[i * 4]; s[i * 2 + 1] = rgba[i * 4 + 3]; } }), plte: null, trns: null });
  }
  if (an.allOpaque && !an.grey && an.distinct > 256) {
    forms.push({ name: 'rgb', ct: 2, bpp: 3, samples: mkSamples(3, s => { for (let i = 0; i < n; i++) { s[i * 3] = rgba[i * 4]; s[i * 3 + 1] = rgba[i * 4 + 1]; s[i * 3 + 2] = rgba[i * 4 + 2]; } }), plte: null, trns: null });
  }
  if (!an.allOpaque) {
    // RGB + transparency key if transparent pixels share one RGB and the rest are opaque
    let trnsKey = null, ok = true;
    for (let i = 0; i < n; i++) { const a = rgba[i * 4 + 3]; if (a === 0) { const k = (rgba[i * 4] << 16) | (rgba[i * 4 + 1] << 8) | rgba[i * 4 + 2]; if (trnsKey === null) trnsKey = k; else if (trnsKey !== k) { ok = false; break; } } else if (a !== 255) { ok = false; break; } }
    if (ok && trnsKey !== null) {
      const tr = new Uint8Array(6); tr[1] = (trnsKey >> 16) & 255; tr[3] = (trnsKey >> 8) & 255; tr[5] = trnsKey & 255;
      forms.push({ name: 'rgbtrns', ct: 2, bpp: 3, samples: mkSamples(3, s => { for (let i = 0; i < n; i++) { s[i * 3] = rgba[i * 4]; s[i * 3 + 1] = rgba[i * 4 + 1]; s[i * 3 + 2] = rgba[i * 4 + 2]; } }), plte: null, trns: tr });
    }
    forms.push({ name: 'rgba', ct: 6, bpp: 4, samples: mkSamples(4, s => s.set(rgba)), plte: null, trns: null });
    if (an.grey && an.distinct > 256) forms.push({ name: 'greyalpha2', ct: 4, bpp: 2, samples: mkSamples(2, s => { for (let i = 0; i < n; i++) { s[i * 2] = rgba[i * 4]; s[i * 2 + 1] = rgba[i * 4 + 3]; } }), plte: null, trns: null });
  }
  if (an.distinct <= 256 && !an.grey) {
    const orders = paletteOrderings(an.map);
    // adjacency ordering
    const ents = orders[0].list;
    const idxOf = new Map(); ents.forEach((e, i) => idxOf.set((e.r << 24) | (e.g << 16) | (e.b << 8) | e.a, i));
    const nn = ents.length; const adj = new Int32Array(nn * nn);
    for (let y = 0; y < h; y++) for (let x = 0; x + 1 < w; x++) {
      const i0 = y * w + x, k0 = (rgba[i0 * 4] << 24) | (rgba[i0 * 4 + 1] << 16) | (rgba[i0 * 4 + 2] << 8) | rgba[i0 * 4 + 3];
      const i1 = i0 + 1, k1 = (rgba[i1 * 4] << 24) | (rgba[i1 * 4 + 1] << 16) | (rgba[i1 * 4 + 2] << 8) | rgba[i1 * 4 + 3];
      const a = idxOf.get(k0), b = idxOf.get(k1); if (a !== b) { adj[a * nn + b]++; adj[b * nn + a]++; }
    }
    let bg = 0; for (let i = 1; i < nn; i++) if (ents[i].count > ents[bg].count) bg = i;
    orders.push({ name: 'adj', list: adjacencyOrder(ents, adj, bg) });
    for (const ord of orders) {
      const lut = new Map(); ord.list.forEach((e, i) => lut.set((e.r << 24) | (e.g << 16) | (e.b << 8) | e.a, i));
      const plte = new Uint8Array(nn * 3); const trnsArr = new Uint8Array(nn); let maxTrns = -1;
      ord.list.forEach((e, i) => { plte[i * 3] = e.r; plte[i * 3 + 1] = e.g; plte[i * 3 + 2] = e.b; trnsArr[i] = e.a; if (e.a < 255) maxTrns = i; });
      const trns = maxTrns >= 0 ? trnsArr.subarray(0, maxTrns + 1) : null;
      forms.push({ name: 'pal-' + ord.name, ct: 3, bpp: 1, samples: mkSamples(1, s => { for (let i = 0; i < n; i++) s[i] = lut.get((rgba[i * 4] << 24) | (rgba[i * 4 + 1] << 16) | (rgba[i * 4 + 2] << 8) | rgba[i * 4 + 3]); }), plte, trns });
    }
  }
  phase.forms = cpuMs() - tStart;
  // filter contest per form, ranked by zlib9
  let bestForm = null, bestStream = null, bestLib = Infinity, bestFilterName = '', bestFilterBytes = 0;
  const tF = cpuMs();
  for (const form of forms) {
    const { filt, minsum, rowLen, rowCost } = buildFiltered(form.samples, w, h, form.bpp);
    const costs = rowCost;
    const cands = [];
    const full = form.name === 'pal-freq' || !form.name.startsWith('pal-');
    for (const f of [0, 2, 4]) { const s = new Uint8Array(h).fill(f); cands.push(['f' + f, s]); }
    cands.push(['minsum', minsum]);
    cands.push(['vit0', viterbi(costs, h, 0)]);
    if (full) cands.push(['vit10240', viterbi(costs, h, 10240)]);
    cands.push(['band16', bandSeq(costs, h, 16)]);
    if (form.ct === 3) {
      // SmartUp: identical row with a horizontal change -> Up, else None
      const su = new Uint8Array(h);
      for (let y = 0; y < h; y++) {
        let same = y > 0, change = false; const stride = w * form.bpp;
        if (y > 0) { const cur = form.samples.subarray(y * stride, (y + 1) * stride), prev = form.samples.subarray((y - 1) * stride, y * stride); for (let i = 0; i < stride; i++) if (cur[i] !== prev[i]) { same = false; break; } for (let i = 1; i < stride; i++) if (cur[i] !== cur[i - 1]) { change = true; break; } }
        su[y] = (same && change) ? 2 : 0;
      }
      cands.push(['smartup', su]);
    }
    // per-row brute force (R3's method): each row compressed with level-1 zlib using the
    // previous 32 KiB of the already-chosen stream as dictionary; cheapest filter wins the row.
    // Skipped for palette forms: f0/SmartUp always win there, and brute costs ~0.4 s per form.
    if (form.ct !== 3) {
      const brute = new Uint8Array(h);
      const chosen = new Uint8Array(h * rowLen); let chosenLen = 0;
      for (let y = 0; y < h; y++) {
        let bestF = 0, bestSize = Infinity;
        for (let f = 0; f < 5; f++) {
          const row = filt[f].subarray(y * rowLen, (y + 1) * rowLen);
          const dict = chosen.subarray(Math.max(0, chosenLen - 32768), chosenLen);
          const sz = deflateRawSync(row, { level: 1, dictionary: dict }).length;
          if (sz < bestSize) { bestSize = sz; bestF = f; }
        }
        brute[y] = bestF;
        chosen.set(filt[bestF].subarray(y * rowLen, (y + 1) * rowLen), chosenLen); chosenLen += rowLen;
      }
      cands.push(['brute', brute]);
    }
    const ranked = full ? cands : cands.filter(([n]) => n === 'f0' || n === 'minsum' || n === 'brute' || n === 'smartup');
    // rank candidates by level-6 first (cheap), then level-9 only for the top 2 per form
    const scored = [];
    for (const [name, seq] of ranked) {
      const stream = assemble(filt, seq, h, rowLen);
      scored.push({ name, stream, z6: deflateRawSync(stream, { level: 6, memLevel: 9 }).length });
    }
    scored.sort((a, b) => a.z6 - b.z6);
    const overhead = (form.plte ? 12 + form.plte.length : 0) + (form.trns ? 12 + form.trns.length : 0);
    for (const cand of scored.slice(0, 2)) {
      const z = deflateRawSync(cand.stream, { level: 9, memLevel: 9 });
      const tot = z.length + overhead;
      if (tot < bestLib) { bestLib = tot; bestForm = form; bestStream = cand.stream; bestFilterName = form.name + '/' + cand.name; bestFilterBytes = z.length; }
    }
  }
  phase.filter = cpuMs() - tF;
  // custom DEFLATE on the winning stream
  const iters = bestForm.bpp === 1 ? 12 : 12;
  const rowLen = w * bestForm.bpp + 1;
  const cs = compressStream(bestStream, bestForm.bpp, rowLen, iters);
  phase.finder = cs.finderMs; phase.parse = cs.parseMs;
  let idat, method;
  if (cs.kraftBad === 0 && cs.customBytes < cs.libBytes) { idat = cs.bytes; method = 'custom'; }
  else { const lib = deflateRawSync(bestStream, { level: 9, memLevel: 9 }); const o = new Uint8Array(lib.length + 6); o[0] = 0x78; o[1] = 0x9c; o.set(lib, 2); new DataView(o.buffer).setUint32(2 + lib.length, adler32(bestStream)); idat = o; method = 'lib'; }
  const chunks = [];
  if (bestForm.plte) chunks.push(['PLTE', bestForm.plte]);
  if (bestForm.trns) chunks.push(['tRNS', bestForm.trns]);
  chunks.push(['IDAT', idat]);
  const png = pngOf(chunks, w, h, bestForm.ct);
  const totalMs = cpuMs() - tStart;
  stat(`${id} form=${bestForm.name} filter=${bestFilterName} filterZ=${bestFilterBytes} custom=${cs.customBytes} lib=${cs.libBytes} method=${method} png=${png.length} kraftBad=${cs.kraftBad}/${cs.kraftChecked} lit=${cs.kraftBadLit} dist=${cs.kraftBadDist} blocks=${cs.blocks} cmp/query=${(cs.comparisons / bestStream.length).toFixed(2)} cappedBuckets=${cs.capped} diag n=${cs.diag.n} noMatch=${cs.diag.noMatch} strict=${cs.diag.strict} cpuTotal=${totalMs.toFixed(0)}ms forms=${phase.forms.toFixed(0)} filter=${phase.filter.toFixed(0)} finder=${phase.finder.toFixed(0)} parse=${phase.parse.toFixed(0)} iters=${iters}`);
  return { png, info: { form: bestForm.name, filter: bestFilterName, filterZ: bestFilterBytes, custom: cs.customBytes, lib: cs.libBytes, method, kraftBad: cs.kraftBad, kraftChecked: cs.kraftChecked, blocks: cs.blocks, diag: cs.diag, comparisons: cs.comparisons, capped: cs.capped, cpu: totalMs, phase } };
}

// ---------- main ----------
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const ids = readdirSync(I).sort();
for (const id of ids) {
  const { w, h, rgba } = decodePng(new Uint8Array(readFileSync(join(I, id, 'image.png'))));
  const { png } = encodeInstance(id, rgba, w, h);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'image.png'), png);
}
