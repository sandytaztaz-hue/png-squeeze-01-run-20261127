// R11 PNG squeeze — written from the R5/R6/R7/R8/R9/R10/R11 prose briefs.
// Lexicographic-suffix BST finder, optimal-parse DP with cost refinement,
// exact package-merge Huffman, Viterbi filter search, palette orderings.
import { readFileSync, writeFileSync, mkdirSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { inflateSync, deflateSync } from 'node:zlib';

const NODE22 = true;
const DIAG = process.env.DEV11_REPORT === '1';

// ---------- CRC32 / Adler ----------
const CRC_T = (() => { const t = new Int32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; t[n] = c; } return t; })();
function crc32(b: Uint8Array, s = 0, e = b.length): number { let c = -1; for (let i = s; i < e; i++) c = CRC_T[(c ^ b[i]) & 255] ^ (c >>> 8); return (c ^ -1) >>> 0; }
function adler32(b: Uint8Array): number { let a = 1, bb = 0; for (let i = 0; i < b.length;) { const e = Math.min(b.length, i + 5552); for (; i < e; i++) { a += b[i]; bb += a; } a %= 65521; bb %= 65521; } return ((bb << 16) | a) >>> 0; }

// ---------- PNG decode to RGBA ----------
function paeth(a: number, b: number, c: number): number { const p = a + b - c; const pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c); if (pa <= pb && pa <= pc) return a; return pb <= pc ? b : c; }
function decodePng(bytes: Uint8Array): { w: number; h: number; rgba: Uint8Array } {
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8, w = 0, h = 0, ct = 6; const idat: Uint8Array[] = []; let pal: Uint8Array | null = null; let trns: Uint8Array | null = null;
  while (at < bytes.length) {
    const len = view.getUint32(at); const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    const data = bytes.subarray(at + 8, at + 8 + len); at += 12 + len;
    if (type === 'IHDR') { const dv = new DataView(data.buffer, data.byteOffset, 13); w = dv.getUint32(0); h = dv.getUint32(4); ct = data[9]; }
    else if (type === 'PLTE') pal = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
  }
  const ch = ct === 0 ? 1 : ct === 2 ? 3 : ct === 3 ? 1 : ct === 4 ? 2 : 4;
  const stride = w * ch;
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat));
  const samples = new Uint8Array(h * stride);
  for (let y = 0; y < h; y++) {
    const ft = raw[y * (stride + 1)]; const src = y * (stride + 1) + 1; const o = y * stride; const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= ch ? samples[o + i - ch] : 0);
    else if (ft === 2) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    else if (ft === 3) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= ch ? samples[o + i - ch] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    else for (let i = 0; i < stride; i++) { const a = i >= ch ? samples[o + i - ch] : 0; const b = y > 0 ? samples[p + i] : 0; const c = y > 0 && i >= ch ? samples[p + i - ch] : 0; samples[o + i] = raw[src + i] + paeth(a, b, c); }
  }
  const rgba = new Uint8Array(w * h * 4);
  if (ct === 6) rgba.set(samples);
  else if (ct === 2) { const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5]; for (let i = 0, s = 0, d = 0; i < w * h; i++, s += 3, d += 4) { rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2]; rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255; } }
  else if (ct === 0) { const key = trns === null ? -1 : trns[1]; for (let i = 0, d = 0; i < w * h; i++, d += 4) { const g = samples[i]; rgba[d] = rgba[d + 1] = rgba[d + 2] = g; rgba[d + 3] = g === key ? 0 : 255; } }
  else if (ct === 4) { for (let i = 0, s = 0, d = 0; i < w * h; i++, s += 2, d += 4) { rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s]; rgba[d + 3] = samples[s + 1]; } }
  else { const n = (pal as Uint8Array).length / 3; for (let i = 0, d = 0; i < w * h; i++, d += 4) { const e = samples[i]; rgba[d] = (pal as Uint8Array)[e * 3]; rgba[d + 1] = (pal as Uint8Array)[e * 3 + 1]; rgba[d + 2] = (pal as Uint8Array)[e * 3 + 2]; rgba[d + 3] = trns !== null && e < trns.length ? trns[e] : 255; } }
  return { w, h, rgba };
}

// ---------- PNG encode ----------
function pngOf(chunks: [string, Uint8Array][]): Uint8Array {
  let size = 8; for (const [, d] of chunks) size += 12 + d.length;
  const out = new Uint8Array(size); const v = new DataView(out.buffer);
  out.set([137, 80, 78, 71, 13, 10, 26, 10], 0); let at = 8;
  for (const [t, d] of chunks) { v.setUint32(at, d.length); for (let i = 0; i < 4; i++) out[at + 4 + i] = t.charCodeAt(i); out.set(d, at + 8); v.setUint32(at + 8 + d.length, crc32(out, at + 4, at + 8 + d.length)); at += 12 + d.length; }
  return out;
}
function ihdrOf(w: number, h: number, ct: number): Uint8Array { const d = new Uint8Array(13); const v = new DataView(d.buffer); v.setUint32(0, w); v.setUint32(4, h); d[8] = 8; d[9] = ct; return d; }

// ---------- PNG row filters ----------
function filterRow(type: number, cur: Uint8Array, prev: Uint8Array | null, bpp: number, out: Uint8Array): void {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  else if (type === 2) for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  else if (type === 3) for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  else for (let i = 0; i < n; i++) { const a = i >= bpp ? cur[i - bpp] : 0; const b = prev === null ? 0 : prev[i]; const c = prev !== null && i >= bpp ? prev[i - bpp] : 0; out[i] = cur[i] - paeth(a, b, c); }
}
function signedSum(row: Uint8Array): number { let s = 0; for (let i = 0; i < row.length; i++) { const v = row[i]; s += v < 128 ? v : 256 - v; } return s; }
// Build the filtered stream for a sample array given a per-row filter choice.
function buildFiltered(samples: Uint8Array, w: number, h: number, bpp: number, choice: Uint8Array): Uint8Array {
  const stride = w * bpp; const raw = new Uint8Array(h * (stride + 1));
  for (let y = 0; y < h; y++) { raw[y * (stride + 1)] = choice[y]; filterRow(choice[y], samples.subarray(y * stride, (y + 1) * stride), y === 0 ? null : samples.subarray((y - 1) * stride, y * stride), bpp, raw.subarray(y * (stride + 1) + 1, (y + 1) * (stride + 1))); }
  return raw;
}
function minsumChoice(samples: Uint8Array, w: number, h: number, bpp: number): Uint8Array {
  const stride = w * bpp; const ch = new Uint8Array(h); const trial = new Uint8Array(stride);
  for (let y = 0; y < h; y++) {
    let best = Infinity, bt = 0;
    for (let t = 0; t < 5; t++) { filterRow(t, samples.subarray(y * stride, (y + 1) * stride), y === 0 ? null : samples.subarray((y - 1) * stride, y * stride), bpp, trial); const s = signedSum(trial); if (s < best) { best = s; bt = t; } }
    ch[y] = bt;
  }
  return ch;
}

// ---------- Colour forms ----------
type Form = { ct: number; bpp: number; samples: Uint8Array; pal: Uint8Array | null; trns: Uint8Array | null; name: string };
function buildForms(rgba: Uint8Array, w: number, h: number): Form[] {
  const n = w * h;
  let allGrey = true, allOpaque = true, nAlpha = 0; const alphaSet = new Set<number>();
  const cmap = new Map<number, number>(); const colours: number[] = []; const freq = new Map<number, number>();
  for (let i = 0; i < n; i++) {
    const r = rgba[i * 4], g = rgba[i * 4 + 1], b = rgba[i * 4 + 2], a = rgba[i * 4 + 3];
    if (r !== g || g !== b) allGrey = false;
    if (a !== 255) { allOpaque = false; nAlpha++; alphaSet.add(a); }
    const k = (r << 24) | (g << 16) | (b << 8) | a;
    let idx = cmap.get(k); if (idx === undefined) { idx = colours.length; cmap.set(k, idx); colours.push(k); freq.set(k, 0); }
    freq.set(k, (freq.get(k) as number) + 1);
  }
  const forms: Form[] = [];
  // Palette forms (several orderings)
  if (colours.length <= 256) {
    const orderings: number[][] = [];
    const byFreq = colours.slice().sort((a, b) => (freq.get(b) as number) - (freq.get(a) as number));
    orderings.push(byFreq);
    const byLum = colours.slice().sort((a, b) => ((a >>> 24) * 299 + ((a >> 16) & 255) * 587 + ((a >> 8) & 255) * 114) - ((b >>> 24) * 299 + ((b >> 16) & 255) * 587 + ((b >> 8) & 255) * 114));
    orderings.push(byLum);
    // Adjacency greedy: background (most frequent) at 0, then most-adjacent unplaced colour.
    const adj = new Map<number, number>(); // key a*256+b-ish via colour index pair
    const idOf = new Map<number, number>(); colours.forEach((c, i) => idOf.set(c, i));
    for (let y = 0; y < h; y++) for (let x = 0; x + 1 < w; x++) {
      const a = idOf.get((rgba[(y * w + x) * 4] << 24) | (rgba[(y * w + x) * 4 + 1] << 16) | (rgba[(y * w + x) * 4 + 2] << 8) | rgba[(y * w + x) * 4 + 3]) as number;
      const b2 = idOf.get((rgba[(y * w + x + 1) * 4] << 24) | (rgba[(y * w + x + 1) * 4 + 1] << 16) | (rgba[(y * w + x + 1) * 4 + 2] << 8) | rgba[(y * w + x + 1) * 4 + 3]) as number;
      if (a !== b2) { const k1 = a * 512 + b2, k2 = b2 * 512 + a; adj.set(k1, (adj.get(k1) || 0) + 1); adj.set(k2, (adj.get(k2) || 0) + 1); }
    }
    const placed: number[] = []; const used = new Set<number>();
    let cur = byFreq[0]; placed.push(cur); used.add(cur);
    while (placed.length < colours.length) {
      let bestC = -1, bestS = -1;
      for (const c of colours) { if (used.has(c)) continue; const s = adj.get((idOf.get(cur) as number) * 512 + (idOf.get(c) as number)) || 0; const sc = s * 1000 + (freq.get(c) as number); if (sc > bestS) { bestS = sc; bestC = c; } }
      placed.push(bestC); used.add(bestC); cur = bestC;
    }
    orderings.push(placed);
    // Keep orderings distinct; evaluate each by zlib1 size of filter-0 stream, keep best 2.
    const scored: { o: number[]; s: number }[] = [];
    for (const o of orderings) {
      const lut = new Map<number, number>(); o.forEach((c, i) => lut.set(c, i));
      const samples = new Uint8Array(n);
      for (let i = 0; i < n; i++) samples[i] = lut.get((rgba[i * 4] << 24) | (rgba[i * 4 + 1] << 16) | (rgba[i * 4 + 2] << 8) | rgba[i * 4 + 3]) as number;
      const raw = buildFiltered(samples, w, h, 1, new Uint8Array(h));
      scored.push({ o, s: deflateSync(raw, { level: 1 }).length });
    }
    scored.sort((a, b) => a.s - b.s);
    const seen = new Set<string>();
    for (const { o } of scored) {
      const key = o.join(',');
      if (seen.has(key)) continue; seen.add(key);
      const lut = new Map<number, number>(); o.forEach((c, i) => lut.set(c, i));
      const samples = new Uint8Array(n);
      for (let i = 0; i < n; i++) samples[i] = lut.get((rgba[i * 4] << 24) | (rgba[i * 4 + 1] << 16) | (rgba[i * 4 + 2] << 8) | rgba[i * 4 + 3]) as number;
      const pal = new Uint8Array(o.length * 3); const trns = new Uint8Array(o.length);
      let needTrns = false;
      o.forEach((c, i) => { pal[i * 3] = (c >>> 24) & 255; pal[i * 3 + 1] = (c >> 16) & 255; pal[i * 3 + 2] = (c >> 8) & 255; trns[i] = c & 255; if ((c & 255) !== 255) needTrns = true; });
      // Trim trailing opaque tRNS entries.
      let tlen = o.length; while (tlen > 0 && trns[tlen - 1] === 255) tlen--;
      forms.push({ ct: 3, bpp: 1, samples, pal, trns: needTrns ? trns.subarray(0, Math.max(tlen, 1)) : null, name: 'pal' });
      if (forms.filter(f => f.ct === 3).length >= 2) break;
    }
  }
  if (allGrey) {
    if (allOpaque) { const s = new Uint8Array(n); for (let i = 0; i < n; i++) s[i] = rgba[i * 4]; forms.push({ ct: 0, bpp: 1, samples: s, pal: null, trns: null, name: 'grey' }); }
    else { const s = new Uint8Array(n * 2); for (let i = 0; i < n; i++) { s[i * 2] = rgba[i * 4]; s[i * 2 + 1] = rgba[i * 4 + 3]; } forms.push({ ct: 4, bpp: 2, samples: s, pal: null, trns: null, name: 'greyA' }); }
  }
  if (allOpaque) {
    const s = new Uint8Array(n * 3); for (let i = 0; i < n; i++) { s[i * 3] = rgba[i * 4]; s[i * 3 + 1] = rgba[i * 4 + 1]; s[i * 3 + 2] = rgba[i * 4 + 2]; }
    forms.push({ ct: 2, bpp: 3, samples: s, pal: null, trns: null, name: 'rgb' });
    // RGB + transparency key: exactly one RGB value is transparent everywhere it occurs.
    const transp = new Map<number, number>(); const tot = new Map<number, number>();
    for (let i = 0; i < n; i++) { const k = (rgba[i * 4] << 16) | (rgba[i * 4 + 1] << 8) | rgba[i * 4 + 2]; tot.set(k, (tot.get(k) || 0) + 1); if (rgba[i * 4 + 3] === 0) transp.set(k, (transp.get(k) || 0) + 1); }
    // (only meaningful when not all opaque; skipped here since allOpaque)
    void transp; void tot;
  } else {
    // RGB with trns key if a single RGB value accounts for all transparent pixels and never appears opaque.
    const transp = new Map<number, number>(); const tot = new Map<number, number>();
    for (let i = 0; i < n; i++) { const k = (rgba[i * 4] << 16) | (rgba[i * 4 + 1] << 8) | rgba[i * 4 + 2]; tot.set(k, (tot.get(k) || 0) + 1); if (rgba[i * 4 + 3] === 0) transp.set(k, (transp.get(k) || 0) + 1); }
    let keyC = -1;
    if (transp.size === 1) { const [k, v] = [...transp.entries()][0]; if (v === tot.get(k) && nAlpha === v) keyC = k; }
    if (keyC >= 0) {
      const s = new Uint8Array(n * 3); for (let i = 0; i < n; i++) { s[i * 3] = rgba[i * 4]; s[i * 3 + 1] = rgba[i * 4 + 1]; s[i * 3 + 2] = rgba[i * 4 + 2]; }
      const tr = new Uint8Array(6); tr[1] = (keyC >> 16) & 255; tr[3] = (keyC >> 8) & 255; tr[5] = keyC & 255;
      forms.push({ ct: 2, bpp: 3, samples: s, pal: null, trns: tr, name: 'rgbKey' });
    }
    forms.push({ ct: 6, bpp: 4, samples: rgba.slice(), pal: null, trns: null, name: 'rgba' });
  }
  return forms;
}

// ---------- Filter contest ----------
// Fast greedy LZ cost table: per row per filter, bit cost (fixed-cost approx) from a
// hash-table greedy parse of the whole filtered stream, plus 0-order entropy cost.
// Returns rowCost[y*5+f] in bits (float).
function lazyRowCosts(filtered: Uint8Array[], w: number, h: number, bpp: number): Float64Array {
  const stride = w * bpp; const rowCost = new Float64Array(h * 5);
  const HASH_BITS = 15; const HSIZE = 1 << HASH_BITS;
  for (let f = 0; f < 5; f++) {
    const data = filtered[f];
    // entropy cost per row
    const cnt = new Int32Array(256);
    for (let y = 0; y < h; y++) {
      cnt.fill(0);
      const base = y * (stride + 1) + 1;
      for (let i = 0; i < stride; i++) cnt[data[base + i]]++;
      let e = 0; for (let c = 0; c < 256; c++) if (cnt[c] > 0) { const p = cnt[c] / stride; e -= cnt[c] * Math.log2(p); }
      rowCost[y * 5 + f] = e;
    }
    // (lazy LZ costs are accumulated in the second pass below)
  }
  for (let f = 0; f < 5; f++) {
    const data = filtered[f];
    const lazy = new Float64Array(h);
    const head = new Int32Array(HSIZE).fill(-1); const prev = new Int32Array(data.length).fill(-1);
    let i = 0; const n = data.length;
    while (i < n) {
      let bestLen = 0;
      if (i + 2 < n) {
        const hh = ((((data[i] << 8) ^ data[i + 1]) * 2654435761) ^ data[i + 2]) >>> (32 - HASH_BITS);
        let q = head[hh]; let tries = 0;
        while (q >= 0 && tries < 8) {
          if (i - q <= 32768) { const l = matchLenAt(data, i, q, 258); if (l >= 3 && l > bestLen) { bestLen = l; if (l >= 258) break; } }
          q = prev[q]; tries++;
        }
        prev[i] = head[hh]; head[hh] = i;
      }
      const y0 = Math.floor(i / (stride + 1));
      if (bestLen >= 3) { const y1 = Math.floor((i + bestLen - 1) / (stride + 1)); const per = 14 / (y1 - y0 + 1); for (let y = y0; y <= y1; y++) lazy[y] += per; i += bestLen; }
      else { lazy[y0] += 8.5; i += 1; }
    }
    for (let y = 0; y < h; y++) rowCost[y * 5 + f] = Math.min(rowCost[y * 5 + f], lazy[y]);
  }
  return rowCost;
}
function viterbi(rowCost: Float64Array, h: number, penalty: number): Uint8Array {
  const INF = 1e18; let dp = new Float64Array(5).fill(0); const back = new Int8Array(h * 5);
  for (let y = 0; y < h; y++) {
    const ndp = new Float64Array(5).fill(INF);
    for (let f = 0; f < 5; f++) { let best = INF, bf = 0; for (let pf = 0; pf < 5; pf++) { const c = dp[pf] + (pf === f ? 0 : penalty) + rowCost[y * 5 + f]; if (c < best) { best = c; bf = pf; } } ndp[f] = best; back[y * 5 + f] = bf; }
    dp = ndp;
  }
  let bf = 0; for (let f = 1; f < 5; f++) if (dp[f] < dp[bf]) bf = f;
  const ch = new Uint8Array(h);
  for (let y = h - 1; y >= 0; y--) { ch[y] = bf; bf = back[y * 5 + bf]; }
  return ch;
}
function smartUp(samples: Uint8Array, w: number, h: number, bpp: number): Uint8Array {
  const stride = w * bpp; const ch = new Uint8Array(h);
  for (let y = 0; y < h; y++) {
    if (y === 0) { ch[y] = 0; continue; }
    const cur = samples.subarray(y * stride, (y + 1) * stride); const prv = samples.subarray((y - 1) * stride, y * stride);
    let same = true, change = false;
    for (let i = 0; i < stride; i++) if (cur[i] !== prv[i]) { same = false; break; }
    if (same) { for (let i = 1; i < stride; i++) if (cur[i] !== cur[i - 1]) { change = true; break; } ch[y] = change ? 2 : 0; }
    else ch[y] = 0;
  }
  return ch;
}
// Greedy per-row brute force: choose each row's filter by greedy LZ cost given history.
function bruteGreedy(samples: Uint8Array, w: number, h: number, bpp: number): Uint8Array {
  const stride = w * bpp; const ch = new Uint8Array(h);
  const HASH_BITS = 15; const HSIZE = 1 << HASH_BITS;
  const head = new Int32Array(HSIZE).fill(-1); const prev = new Int32Array(h * (stride + 1)).fill(-1);
  const trial = new Uint8Array(stride); const built = new Uint8Array(h * (stride + 1));
  // insert row 0 filter 0 as history seed is handled row by row below
  for (let y = 0; y < h; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride); const prv = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    let bestF = 0, bestC = Infinity;
    const base = y * (stride + 1);
    for (let f = 0; f < 5; f++) {
      filterRow(f, cur, prv, bpp, trial);
      // greedy cost of this row's bytes (filter byte + row) against history hash table
      let cost = 8.5; let i = 0;
      // simulate positions in the assembled stream: filter byte at base, then row bytes
      // For speed, cost the row bytes against head/prev built from previous rows only.
      const rowBytes = trial;
      while (i < stride) {
        let bl = 0;
        if (i + 2 < stride) {
          const hh = ((((rowBytes[i] << 8) ^ rowBytes[i + 1]) * 2654435761) ^ rowBytes[i + 2]) >>> (32 - HASH_BITS);
          let q = head[hh]; let tries = 0;
          while (q >= 0 && tries < 4) {
            const qp = q; // q is absolute position in built stream
            if (base + 1 + i - qp <= 32768) {
              // compare built[qp..] with rowBytes[i..]; built covers only previous rows
              let l = 0; const maxL = Math.min(258, stride - i);
              while (l < maxL && qp + l < base && built[qp + l] === rowBytes[i + l]) l++;
              if (l >= 3 && l > bl) { bl = l; if (l >= 258) break; }
            }
            q = prev[qp]; tries++;
          }
        }
        if (bl >= 3) { cost += 14; i += bl; } else { cost += 8.5; i += 1; }
      }
      if (cost < bestC) { bestC = cost; bestF = f; }
    }
    ch[y] = bestF;
    filterRow(bestF, cur, prv, bpp, trial);
    built[base] = bestF; built.set(trial, base + 1);
    // insert this row's positions into hash table
    for (let i = 0; i + 2 < stride + 1; i++) {
      const p = base + i;
      const b0 = built[p], b1 = built[p + 1], b2 = built[p + 2];
      const hh = ((((b0 << 8) ^ b1) * 2654435761) ^ b2) >>> (32 - HASH_BITS);
      prev[p] = head[hh]; head[hh] = p;
    }
  }
  return ch;
}

// ---------- DEFLATE tables ----------
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
function lenSym(len: number): number { for (let s = 0; s < 29; s++) { const lo = LEN_BASE[s]; const hi = s === 28 ? 258 : LEN_BASE[s + 1] - 1; if (len >= lo && len <= hi) return s; } return 28; }
function distSym(d: number): number { for (let s = 0; s < 30; s++) { const lo = DIST_BASE[s]; const hi = s === 29 ? 32768 : DIST_BASE[s + 1] - 1; if (d >= lo && d <= hi) return s; } return 29; }
const LEN_SYM_LUT = new Uint8Array(259); { for (let l = 0; l <= 258; l++) LEN_SYM_LUT[l] = l < 3 ? 0 : lenSym(l); }
const DIST_SYM_LUT = new Uint8Array(32769); { for (let d = 1; d <= 32768; d++) DIST_SYM_LUT[d] = distSym(d); }
const FIXED_LIT_LEN = new Int32Array(288); { for (let i = 0; i < 144; i++) FIXED_LIT_LEN[i] = 8; for (let i = 144; i < 256; i++) FIXED_LIT_LEN[i] = 9; for (let i = 256; i < 280; i++) FIXED_LIT_LEN[i] = 7; for (let i = 280; i < 288; i++) FIXED_LIT_LEN[i] = 8; }

// ---------- Package-merge length-limited Huffman ----------
function packageMerge(freq: Int32Array | number[], maxLen: number): Int32Array {
  const n = freq.length; const lens = new Int32Array(n);
  const idx: number[] = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) idx.push(i);
  if (idx.length === 0) return lens;
  if (idx.length === 1) { lens[idx[0]] = 1; return lens; }
  idx.sort((a, b) => freq[a] - freq[b]);
  type El = { w: number; s: number[] };
  const orig: El[] = idx.map(i => ({ w: freq[i], s: [i] }));
  let lists: El[][] = [orig];
  let cur: El[] = orig;
  for (let l = 1; l <= maxLen; l++) {
    const packaged: El[] = [];
    for (let i = 0; i + 1 < cur.length; i += 2) packaged.push({ w: cur[i].w + cur[i + 1].w, s: cur[i].s.concat(cur[i + 1].s) });
    if (cur.length % 2 === 1) packaged.push(cur[cur.length - 1]); // unpaired largest carried over
    // merge packaged + orig, sorted by w
    const merged: El[] = []; let a = 0, b = 0;
    while (a < packaged.length && b < orig.length) { if (packaged[a].w <= orig[b].w) merged.push(packaged[a++]); else merged.push(orig[b++]); }
    while (a < packaged.length) merged.push(packaged[a++]);
    while (b < orig.length) merged.push(orig[b++]);
    cur = merged; lists.push(cur);
  }
  void lists;
  const take = Math.min(2 * idx.length - 2, cur.length);
  for (let i = 0; i < take; i++) for (const s of cur[i].s) lens[s]++;
  // Clamp any length over maxLen (package-merge can count one over), then
  // complete-ify only when it cannot overshoot: Kraft sum must stay <= 2^maxLen.
  // An incomplete code (sum < 2^maxLen) is still a valid DEFLATE code.
  for (let i = 0; i < n; i++) if (lens[i] > maxLen) lens[i] = maxLen;
  const T = 1 << maxLen;
  let sum = 0; for (let i = 0; i < n; i++) if (lens[i] > 0) sum += 1 << (maxLen - lens[i]);
  // If oversubscribed (should not happen after clamping), lengthen the least
  // frequent symbols until it fits.
  let guard = 0;
  while (sum > T && guard++ < 10000) {
    let worst = -1, worstF = Infinity;
    for (let i = 0; i < n; i++) if (lens[i] > 0 && lens[i] < maxLen && freq[i] < worstF) { worstF = freq[i]; worst = i; }
    if (worst < 0) break;
    sum -= 1 << (maxLen - lens[worst]);
    lens[worst]++;
    sum += 1 << (maxLen - lens[worst]);
  }
  guard = 0;
  while (sum < T && guard++ < 10000) {
    let worst = -1, worstLen = -1;
    for (let i = 0; i < n; i++) if (lens[i] > 1 && lens[i] > worstLen) { worstLen = lens[i]; worst = i; }
    if (worst < 0) break;
    const delta = 1 << (maxLen - worstLen);
    if (sum + delta > T) break; // never overshoot; incomplete is valid
    sum += delta;
    lens[worst]--;
  }
  return lens;
}
function canonicalCodes(lens: Int32Array): { codes: Int32Array; lens: Int32Array } {
  const maxL = Math.max(0, ...lens); const bl = new Int32Array(maxL + 1);
  for (let i = 0; i < lens.length; i++) if (lens[i] > 0) bl[lens[i]]++;
  const next = new Int32Array(maxL + 1); let code = 0;
  for (let b = 1; b <= maxL; b++) { code = (code + bl[b - 1]) << 1; next[b] = code; }
  const codes = new Int32Array(lens.length);
  for (let i = 0; i < lens.length; i++) if (lens[i] > 0) codes[i] = next[lens[i]]++;
  return { codes, lens };
}
function kraftOk(lens: Int32Array, maxLen: number): boolean {
  let sum = 0; for (let i = 0; i < lens.length; i++) if (lens[i] > 0) { if (lens[i] > maxLen) return false; sum += 1 << (maxLen - lens[i]); }
  return sum <= (1 << maxLen);
}

// ---------- Bit writer (single shared writer; Huffman codes MSB-first) ----------
class BitWriter {
  bytes: number[] = []; bitBuf = 0; bitCnt = 0;
  writeBits(v: number, n: number): void { // LSB-first (header fields, extra bits)
    for (let i = 0; i < n; i++) { this.bitBuf |= ((v >> i) & 1) << this.bitCnt; this.bitCnt++; if (this.bitCnt === 8) { this.bytes.push(this.bitBuf); this.bitBuf = 0; this.bitCnt = 0; } }
  }
  writeCode(code: number, n: number): void { // MSB-first (Huffman codes)
    for (let i = n - 1; i >= 0; i--) { this.bitBuf |= ((code >> i) & 1) << this.bitCnt; this.bitCnt++; if (this.bitCnt === 8) { this.bytes.push(this.bitBuf); this.bitBuf = 0; this.bitCnt = 0; } }
  }
  finish(): Uint8Array { if (this.bitCnt > 0) this.bytes.push(this.bitBuf); return new Uint8Array(this.bytes); }
}

// ---------- Lexicographic-suffix BST finder ----------
type Cand = { bLen: Uint16Array; bDist: Int32Array; aLen: Uint16Array; aDist: Int32Array; rLen: Uint16Array; rDist: Int32Array; pLen: Uint16Array; pDist: Int32Array; pCnt: Uint8Array; runLen: Uint16Array; visits: number };
let _dv: DataView | null = null; let _dvBuf: ArrayBuffer | null = null; let _dvOff = -1; let _dvLen = -1;
function matchLenAt(d: Uint8Array, p: number, q: number, cap: number): number {
  let l = 0; const maxL = Math.min(cap, d.length - p, d.length - q);
  if (_dv === null || _dvBuf !== d.buffer || _dvOff !== d.byteOffset || _dvLen !== d.byteLength) { _dv = new DataView(d.buffer, d.byteOffset, d.byteLength); _dvBuf = d.buffer; _dvOff = d.byteOffset; _dvLen = d.byteLength; }
  const dv = _dv;
  while (l + 4 <= maxL && dv.getUint32(p + l) === dv.getUint32(q + l)) l += 4;
  while (l < maxL && d[p + l] === d[q + l]) l++;
  return l;
}
// Fast (unlimited) Huffman code lengths — used ONLY as DP cost estimates, never for emitted trees.
function huffLengths(freq: Int32Array | number[], maxLen: number): Int32Array {
  const n = freq.length; const lens = new Int32Array(n);
  const idx: number[] = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) idx.push(i);
  if (idx.length === 0) return lens;
  if (idx.length === 1) { lens[idx[0]] = 1; return lens; }
  // Binary heap of node ids; node weights in w[].
  const maxNodes = 2 * idx.length;
  const w = new Float64Array(maxNodes); const lc = new Int32Array(maxNodes).fill(-1); const rc = new Int32Array(maxNodes).fill(-1);
  let nn = 0;
  for (const i of idx) { w[nn] = freq[i]; lc[nn] = i; nn++; } // lc holds symbol for leaves (rc=-1, lc>=0 leaf marker via sym array)
  const sym = new Int32Array(maxNodes).fill(-1);
  for (let k = 0; k < idx.length; k++) sym[k] = idx[k];
  const heap: number[] = [];
  for (let k = 0; k < idx.length; k++) heap.push(k);
  const hpush = (x: number) => { heap.push(x); let c = heap.length - 1; while (c > 0) { const p = (c - 1) >> 1; if (w[heap[p]] <= w[heap[c]]) break; const t = heap[p]; heap[p] = heap[c]; heap[c] = t; c = p; } };
  const hpop = (): number => { const top = heap[0]; const last = heap.pop() as number; if (heap.length > 0) { heap[0] = last; let p = 0; for (;;) { const l = p * 2 + 1, r = l + 1; let m = p; if (l < heap.length && w[heap[l]] < w[heap[m]]) m = l; if (r < heap.length && w[heap[r]] < w[heap[m]]) m = r; if (m === p) break; const t = heap[p]; heap[p] = heap[m]; heap[m] = t; p = m; } } return top; };
  // Rebuild heap properly (heapify)
  for (let k = (heap.length >> 1) - 1; k >= 0; k--) { let p = k; for (;;) { const l = p * 2 + 1, r = l + 1; let m = p; if (l < heap.length && w[heap[l]] < w[heap[m]]) m = l; if (r < heap.length && w[heap[r]] < w[heap[m]]) m = r; if (m === p) break; const t = heap[p]; heap[p] = heap[m]; heap[m] = t; p = m; } }
  void hpush;
  let root = -1;
  while (heap.length > 1) {
    const a = hpop(); const b = hpop();
    const nd = nn++;
    w[nd] = w[a] + w[b]; lc[nd] = a; rc[nd] = b; sym[nd] = -1;
    // push nd
    heap.push(nd); let c = heap.length - 1; while (c > 0) { const p = (c - 1) >> 1; if (w[heap[p]] <= w[heap[c]]) break; const t = heap[p]; heap[p] = heap[c]; heap[c] = t; c = p; }
    root = nd;
  }
  if (heap.length === 1) root = heap[0];
  // Depths via stack.
  const stack: [number, number][] = [[root, 0]];
  while (stack.length > 0) {
    const [nd, dep] = stack.pop() as [number, number];
    if (sym[nd] >= 0) lens[sym[nd]] = Math.max(1, Math.min(maxLen, dep));
    else { if (lc[nd] >= 0) stack.push([lc[nd], dep + 1]); if (rc[nd] >= 0) stack.push([rc[nd], dep + 1]); }
  }
  return lens;
}
function findMatches(d: Uint8Array, rowBytes: number, diag: { visits: number; positions: number }, depthCap = 64, paretoCap = 4): Cand {
  const n = d.length;
  const runLen = new Uint16Array(n + 1);
  for (let i = n - 1; i >= 0; i--) runLen[i] = d[i] === d[i + 1] ? Math.min(258, runLen[i + 1] + 1) : 1;
  const bLen = new Uint16Array(n), bDist = new Int32Array(n), aLen = new Uint16Array(n), aDist = new Int32Array(n), rLen = new Uint16Array(n), rDist = new Int32Array(n);
  const pLen = new Uint16Array(n * 4), pDist = new Int32Array(n * 4), pCnt = new Uint8Array(n);
  const _cl = new Int32Array(16), _cd = new Int32Array(16);
  const roots = new Int32Array(65536).fill(-1);
  const left = new Int32Array(n).fill(-1); const right = new Int32Array(n).fill(-1);
  const prio = new Uint32Array(n);
  for (let k = 0; k < n; k++) { let x = ((k + 1) * 2654435761) >>> 0; x ^= x >>> 15; x = (x * 2246822519) >>> 0; x ^= x >>> 13; prio[k] = x; }
  const cmpSuffix = (p: number, q: number): number => {
    const maxL = Math.min(258, n - p, n - q);
    const l = matchLenAt(d, p, q, maxL);
    if (l < maxL) return d[p + l] < d[q + l] ? -1 : 1;
    if (n - p < n - q) return -1;
    if (n - p > n - q) return 1;
    return 0;
  };
  const treapInsert = (root: number, x: number): number => {
    if (root < 0) return x;
    const c = cmpSuffix(x, root);
    if (c < 0) {
      left[root] = treapInsert(left[root], x);
      if (left[root] >= 0 && prio[left[root]] > prio[root]) { const L = left[root]; left[root] = right[L]; right[L] = root; return L; }
    } else {
      right[root] = treapInsert(right[root], x);
      if (right[root] >= 0 && prio[right[root]] > prio[root]) { const R = right[root]; right[root] = left[R]; left[R] = root; return R; }
    }
    return root;
  };
  const maxRun = new Int32Array(256).fill(-1);
  let visits = 0;
  const hash3 = (i: number) => ((((d[i] << 16) ^ (d[i + 1] << 8) ^ d[i + 2]) * 2654435761) >>> 16) & 0xffff;
  for (let i = 0; i < n; i++) {
    let bl = 0, bd = 0, al = 0, ad = 0;
    // MANDATORY 0: distance-1 run match valid ONLY when data[i]==data[i-1].
    let nc = 0;
    const addCand = (L: number, dist: number) => { if (L >= 3 && dist >= 1 && dist <= 32768 && nc < 16) { _cl[nc] = L; _cd[nc] = dist; nc++; } };
    if (i > 0 && d[i] === d[i - 1]) { const L = Math.min(258, runLen[i - 1] - 1, n - i); if (L >= 3) { bl = L; bd = 1; addCand(L, 1); } }
    // O(1) side record: most recent maximal-length (258) run start per first byte.
    const mr = maxRun[d[i]];
    if (mr >= 0 && i - mr <= 32768 && mr < i) { const L = matchLenAt(d, i, mr, 258); addCand(L, i - mr); if (L >= 3 && L > bl) { bl = L; bd = i - mr; } }
    // Row-above probes (one and two scanlines above).
    for (const dr of [rowBytes, rowBytes * 2]) {
      if (dr > 0 && i - dr >= 0) { const L = matchLenAt(d, i, i - dr, 258); addCand(L, dr); if (L >= 3 && L > rLen[i]) { rLen[i] = L; rDist[i] = dr; } if (L >= 3 && L > bl) { bl = L; bd = dr; } }
    }
    // Lexicographic treap walk within the 3-byte-prefix hash bucket.
    // The treap is a BST by suffix (lexicographic) and a heap by a fixed
    // pseudo-random priority, so its expected depth is O(log n): the descent
    // moves toward suffixes sharing a long prefix with the query.
    if (i + 2 < n) {
      const h = hash3(i);
      let q = roots[h]; let depth = 0;
      while (q >= 0 && depth < depthCap) {
        visits++;
        const maxL = Math.min(258, n - i, n - q);
        const l = matchLenAt(d, i, q, maxL);
        let cmp = 0;
        if (l < maxL) cmp = d[i + l] < d[q + l] ? -1 : 1;
        else if (n - i < n - q) cmp = -1; else if (n - i > n - q) cmp = 1;
        if (l >= 3 && i - q <= 32768) {
          addCand(l, i - q);
          if (l > bl || (l === bl && bd > i - q)) { bl = l; bd = i - q; }
          if (ad === 0 || i - q < ad) { al = l; ad = i - q; }
        }
        if (cmp === 0 || (bl >= 258 && nc >= 2)) break;
        q = cmp < 0 ? left[q] : right[q];
        depth++;
      }
      // Insert i into the treap (maximal-run starts skipped — side record covers them).
      if (runLen[i] < 258) roots[h] = treapInsert(roots[h], i);
    }
    if (runLen[i] >= 258) maxRun[d[i]] = i;
    bLen[i] = bl; bDist[i] = bd; aLen[i] = al; aDist[i] = ad;
    // Pareto frontier: sort scratch by length desc, keep pairs whose distance
    // is strictly better than every longer pair's distance (up to 4).
    for (let a = 1; a < nc; a++) { const tl = _cl[a], td = _cd[a]; let b = a - 1; while (b >= 0 && _cl[b] < tl) { _cl[b + 1] = _cl[b]; _cd[b + 1] = _cd[b]; b--; } _cl[b + 1] = tl; _cd[b + 1] = td; }
    let pc = 0, minD = 1 << 30;
    for (let a = 0; a < nc && pc < paretoCap; a++) { if (_cd[a] < minD) { minD = _cd[a]; pLen[i * 4 + pc] = _cl[a]; pDist[i * 4 + pc] = _cd[a]; pc++; } }
    pCnt[i] = pc;
  }
  diag.visits = visits; diag.positions = n;
  return { bLen, bDist, aLen, aDist, rLen, rDist, pLen, pDist, pCnt, runLen, visits };
}

// ---------- Optimal-parse DP over one block, iterated cost refinement ----------
// Returns tokens: arrays kind (0 lit / 1 match), lit byte or len/dist.
function parseBlock(d: Uint8Array, bs: number, be: number, cand: Cand, iters: number, isFlat: boolean): { toks: { k: number; v: number; d: number }[]; litFreq: Int32Array; distFreq: Int32Array; dpCost: number } {
  const m = be - bs;
  const dp = new Int32Array(m + 1); const chKind = new Int8Array(m + 1); const chLen = new Uint16Array(m + 1); const chDist = new Uint16Array(m + 1);
  let litCost = new Int32Array(288); let lenCost = new Int32Array(29); let distCost = new Int32Array(30);
  for (let i = 0; i < 288; i++) litCost[i] = FIXED_LIT_LEN[i] * 16;
  for (let s = 0; s < 29; s++) lenCost[s] = 8 * 16;
  for (let s = 0; s < 30; s++) distCost[s] = 5 * 16;
  const litFreq = new Int32Array(288); const distFreq = new Int32Array(30);
  let toks: { k: number; v: number; d: number }[] = [];
  let seed = 123456789;
  const lcg = () => { seed = (seed * 1103515245 + 12345) >>> 0; return seed / 4294967296; };
  for (let it = 0; it < iters; it++) {
    const INF = 1 << 29;
    dp.fill(INF); dp[0] = 0; chKind.fill(-1);
    // Deterministic perturbation at iteration 5 (±10%), second perturbation per brief.
    let lc = litCost, ec = lenCost, dc = distCost;
    if (it === 5) {
      lc = litCost.slice(); ec = lenCost.slice(); dc = distCost.slice();
      for (let i = 0; i < 288; i++) lc[i] = Math.max(16, Math.round(lc[i] * (0.9 + 0.2 * lcg())));
      for (let i = 0; i < 29; i++) ec[i] = Math.max(16, Math.round(ec[i] * (0.9 + 0.2 * lcg())));
      for (let i = 0; i < 30; i++) dc[i] = Math.max(16, Math.round(dc[i] * (0.9 + 0.2 * lcg())));
    }
    for (let i = 0; i < m; i++) {
      const base = dp[i]; if (base >= INF) continue;
      const pos = bs + i;
      // literal
      let j = i + 1; let c = base + lc[d[pos]];
      if (c < dp[j]) { dp[j] = c; chKind[j] = 0; }
      // Pareto match candidates (per-length best distance), plus sublen
      // endpoints (length 3 and the top of the range below the longest) for pair 0.
      const pc = cand.pCnt[pos];
      for (let k = 0; k < pc; k++) {
        const L = cand.pLen[pos * 4 + k], D = cand.pDist[pos * 4 + k];
        if (L < 3 || D < 1 || D > 32768 || L > m - i) continue;
        const s = lenSym(L); const ds = distSym(D);
        const cc = base + ec[s] + LEN_EXTRA[s] * 16 + dc[ds] + DIST_EXTRA[ds] * 16;
        j = i + L; if (cc < dp[j]) { dp[j] = cc; chKind[j] = 1; chLen[j] = L; chDist[j] = D; }
        if (k === 0) {
          if (L > 3) { const c3 = base + ec[0] + dc[ds] + DIST_EXTRA[ds] * 16; j = i + 3; if (c3 < dp[j]) { dp[j] = c3; chKind[j] = 1; chLen[j] = 3; chDist[j] = D; } }
          const hi = s > 0 ? LEN_BASE[s] - 1 : 0;
          if (hi >= 3 && hi < L) { const sh = lenSym(hi); const ch2 = base + ec[sh] + LEN_EXTRA[sh] * 16 + dc[ds] + DIST_EXTRA[ds] * 16; j = i + hi; if (hi <= m - i && ch2 < dp[j]) { dp[j] = ch2; chKind[j] = 1; chLen[j] = hi; chDist[j] = D; } }
        }
      }
    }
    // Backtrack, count frequencies.
    litFreq.fill(0); distFreq.fill(0); toks = [];
    let p = m;
    while (p > 0) {
      if (chKind[p] === 1) { const L = chLen[p], D = chDist[p]; toks.push({ k: 1, v: L, d: D }); litFreq[257 + lenSym(L)]++; distFreq[distSym(D)]++; p -= L; }
      else { toks.push({ k: 0, v: d[bs + p - 1], d: 0 }); litFreq[d[bs + p - 1]]++; p -= 1; }
    }
    toks.reverse();
    litFreq[256]++; // end-of-block
    // Re-derive costs from token frequencies (fast Huffman lengths as DP cost
    // estimates; the emitted trees use exact package-merge in emitBlock).
    const ll = huffLengths(litFreq, 15); const dl = huffLengths(distFreq, 15);
    litCost = new Int32Array(288); lenCost = new Int32Array(29); distCost = new Int32Array(30);
    for (let i = 0; i < 256; i++) litCost[i] = (ll[i] > 0 ? ll[i] : 15) * 16;
    for (let s = 0; s < 29; s++) { const sym = 257 + s; litCost[sym] = (ll[sym] > 0 ? ll[sym] : 15) * 16; lenCost[s] = litCost[sym]; }
    litCost[256] = (ll[256] > 0 ? ll[256] : 7) * 16;
    for (let s = 0; s < 30; s++) distCost[s] = (dl[s] > 0 ? dl[s] : 15) * 16;
    void isFlat;
  }
  return { toks, litFreq, distFreq, dpCost: dp[m] };
}

// Emit one block's tokens; returns bits used (approx, for dynamic-vs-fixed choice done by caller via freq costs).
function emitBlock(bw: BitWriter, toks: { k: number; v: number; d: number }[], litFreq: Int32Array, distFreq: Int32Array, last: boolean): { kraftOk: boolean; dynamic: boolean } {
  // Build dynamic trees.
  const ll = packageMerge(litFreq, 15); const dl = packageMerge(distFreq, 15);
  // Trim trailing zero dist lengths (keep at least 1).
  let nDist = 30; while (nDist > 1 && dl[nDist - 1] === 0) nDist--;
  let nLit = 288; while (nLit > 257 && ll[nLit - 1] === 0) nLit--;
  // Code-length alphabet: RLE-encode lit+dist lengths.
  const seq: number[] = []; for (let i = 0; i < nLit; i++) seq.push(ll[i]); for (let i = 0; i < nDist; i++) seq.push(dl[i]);
  const rleSyms: number[] = []; const rleExtra: number[] = [];
  let i = 0;
  while (i < seq.length) {
    const v = seq[i]; let run = 1; while (i + run < seq.length && seq[i + run] === v) run++;
    if (v === 0) {
      let r = run;
      while (r >= 11) { const take = Math.min(138, r); rleSyms.push(18); rleExtra.push(take - 11); r -= take; }
      if (r >= 3) { rleSyms.push(17); rleExtra.push(r - 3); r = 0; }
      while (r-- > 0) { rleSyms.push(0); rleExtra.push(0); }
    } else {
      rleSyms.push(v); rleExtra.push(0);
      let r = run - 1;
      while (r >= 3) { const take = Math.min(6, r); rleSyms.push(16); rleExtra.push(take - 3); r -= take; }
      while (r-- > 0) { rleSyms.push(v); rleExtra.push(0); }
    }
    i += run;
  }
  const clFreq = new Int32Array(19); for (const s of rleSyms) clFreq[s]++;
  let clLens = packageMerge(clFreq, 7);
  // Code-length code needs >=2 nonzero lengths for a complete code; add a dummy if needed.
  let nz = 0; for (let k = 0; k < 19; k++) if (clLens[k] > 0) nz++;
  if (nz === 1) { for (let k = 0; k < 19; k++) if (clLens[k] === 0) { clLens[k] = 1; break; } }
  if (nz === 0) { clLens[0] = 1; clLens[1] = 1; }
  const clOrder = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
  let nCl = 19; while (nCl > 4 && clLens[clOrder[nCl - 1]] === 0) nCl--;
  // Header bit cost of dynamic.
  let dynHdrBits = 5 + 5 + 4 + 3 * nCl;
  const clC = canonicalCodes(clLens);
  for (let k = 0; k < rleSyms.length; k++) { const s = rleSyms[k]; dynHdrBits += clLens[s]; if (s === 16) dynHdrBits += 2; else if (s === 17) dynHdrBits += 3; else if (s === 18) dynHdrBits += 7; }
  let dynDataBits = 0;
  for (let k = 0; k < 256; k++) dynDataBits += litFreq[k] * (ll[k] > 0 ? ll[k] : 0);
  for (let s = 0; s < 29; s++) dynDataBits += litFreq[257 + s] * (ll[257 + s] > 0 ? ll[257 + s] : 0);
  dynDataBits += litFreq[256] * (ll[256] > 0 ? ll[256] : 0);
  for (let s = 0; s < 30; s++) dynDataBits += distFreq[s] * (dl[s] > 0 ? dl[s] : 0);
  // Extra bits for matches.
  let extraBits = 0; for (const t of toks) if (t.k === 1) extraBits += LEN_EXTRA[lenSym(t.v)] + DIST_EXTRA[distSym(t.d)];
  const dynTotal = 3 + dynHdrBits + dynDataBits + extraBits;
  // Fixed block cost.
  let fixDataBits = 0;
  for (let k = 0; k < 256; k++) fixDataBits += litFreq[k] * FIXED_LIT_LEN[k];
  for (let s = 0; s < 29; s++) fixDataBits += litFreq[257 + s] * FIXED_LIT_LEN[257 + s];
  fixDataBits += litFreq[256] * FIXED_LIT_LEN[256];
  for (let s = 0; s < 30; s++) fixDataBits += distFreq[s] * 5;
  const fixTotal = 3 + fixDataBits + extraBits;
  const useDyn = dynTotal < fixTotal;
  const ok = kraftOk(ll, 15) && kraftOk(dl, 15) && kraftOk(clLens, 7);
  if (useDyn) {
    const litC = canonicalCodes(ll); const distC = canonicalCodes(dl);
    bw.writeBits(last ? 1 : 0, 1); bw.writeBits(2, 2);
    bw.writeBits(nLit - 257, 5); bw.writeBits(nDist - 1, 5); bw.writeBits(nCl - 4, 4);
    for (let k = 0; k < nCl; k++) bw.writeBits(clLens[clOrder[k]], 3);
    for (let k = 0; k < rleSyms.length; k++) {
      const s = rleSyms[k];
      bw.writeCode(clC.codes[s], clLens[s]);
      if (s === 16) bw.writeBits(rleExtra[k], 2); else if (s === 17) bw.writeBits(rleExtra[k], 3); else if (s === 18) bw.writeBits(rleExtra[k], 7);
    }
    for (const t of toks) {
      if (t.k === 0) bw.writeCode(litC.codes[t.v], ll[t.v]);
      else { const s = lenSym(t.v); bw.writeCode(litC.codes[257 + s], ll[257 + s]); if (LEN_EXTRA[s]) bw.writeBits(t.v - LEN_BASE[s], LEN_EXTRA[s]); const ds = distSym(t.d); bw.writeCode(distC.codes[ds], dl[ds]); if (DIST_EXTRA[ds]) bw.writeBits(t.d - DIST_BASE[ds], DIST_EXTRA[ds]); }
    }
    bw.writeCode(litC.codes[256], ll[256]);
  } else {
    const litC = canonicalCodes(FIXED_LIT_LEN); const distLens = new Int32Array(30).fill(5); const distC = canonicalCodes(distLens);
    bw.writeBits(last ? 1 : 0, 1); bw.writeBits(1, 2);
    for (const t of toks) {
      if (t.k === 0) bw.writeCode(litC.codes[t.v], FIXED_LIT_LEN[t.v]);
      else { const s = lenSym(t.v); bw.writeCode(litC.codes[257 + s], FIXED_LIT_LEN[257 + s]); if (LEN_EXTRA[s]) bw.writeBits(t.v - LEN_BASE[s], LEN_EXTRA[s]); const ds = distSym(t.d); bw.writeCode(distC.codes[ds], 5); if (DIST_EXTRA[ds]) bw.writeBits(t.d - DIST_BASE[ds], DIST_EXTRA[ds]); }
    }
    bw.writeCode(litC.codes[256], FIXED_LIT_LEN[256]);
  }
  return { kraftOk: ok, dynamic: useDyn };
}

// ---------- Custom DEFLATE over a whole filtered stream ----------
function deflateCustom(data: Uint8Array, rowBytes: number, bandEnds: number[], iters: number, isFlat: boolean, depthCap = 64, paretoCap = 4): { out: Uint8Array; kraftBad: number; blocks: number } {
  const t0 = process.hrtime.bigint();
  const diag = { visits: 0, positions: 0 };
  const cand = findMatches(data, rowBytes, diag, depthCap, paretoCap);
  if (DIAG) console.error('  finder ms=' + (Number(process.hrtime.bigint() - t0) / 1e6).toFixed(0) + ' visits=' + diag.visits + ' vis/pos=' + (diag.visits / Math.max(1, diag.positions)).toFixed(2));
  const n = data.length;
  // Block boundaries: at filter-band ends, cap 200KB, min 32KB; run-aware (don't split inside a run).
  const bounds: number[] = [0];
  let start = 0;
  while (start < n) {
    let end = Math.min(n, start + 131072);
    if (end < n) {
      // prefer a band end in (start+32k, end]
      let be2 = -1;
      for (const b of bandEnds) if (b > start + 32768 && b <= end) be2 = b;
      if (be2 > 0) end = be2;
      // run-aware: if end falls inside a run, move to the run's end (max +258).
      if (end > 0 && end < n && data[end] === data[end - 1]) { let e2 = end; while (e2 < n && e2 < end + 258 && data[e2] === data[e2 - 1]) e2++; end = Math.min(n, e2); }
    }
    bounds.push(end); start = end;
  }
  const bw = new BitWriter();
  let kraftBad = 0; const tP = process.hrtime.bigint();
  for (let b = 0; b + 1 < bounds.length; b++) {
    const { toks, litFreq, distFreq } = parseBlock(data, bounds[b], bounds[b + 1], cand, iters, isFlat);
    const r = emitBlock(bw, toks, litFreq, distFreq, b + 2 === bounds.length);
    if (!r.kraftOk) kraftBad++;
  }
  if (DIAG) console.error('  parse ms=' + (Number(process.hrtime.bigint() - tP) / 1e6).toFixed(0));
  const def = bw.finish();
  const out = new Uint8Array(def.length + 6);
  out[0] = 0x78; out[1] = 0x9c; out.set(def, 2);
  new DataView(out.buffer).setUint32(out.length - 4, adler32(data));
  return { out, kraftBad, blocks: bounds.length - 1 };
}

// ---------- Per-instance encode ----------
function pngOverhead(f: Form): number { let o = 8 + 25 + 12 + 12; if (f.pal) o += 12 + f.pal.length; if (f.trns) o += 12 + f.trns.length; return o; }
function bandCandidates(samples: Uint8Array, w: number, h: number, bpp: number, size: number): Uint8Array {
  const stride = w * bpp; const ch = new Uint8Array(h); const trial = new Uint8Array(stride);
  const sums: number[][] = [];
  for (let y = 0; y < h; y++) { const row: number[] = []; for (let t = 0; t < 5; t++) { filterRow(t, samples.subarray(y * stride, (y + 1) * stride), y === 0 ? null : samples.subarray((y - 1) * stride, y * stride), bpp, trial); row.push(signedSum(trial)); } sums.push(row); }
  for (let y0 = 0; y0 < h; y0 += size) {
    let bestF = 0, bestS = Infinity;
    for (let f = 0; f < 5; f++) { let s = 0; for (let y = y0; y < Math.min(h, y0 + size); y++) s += sums[y][f]; if (s < bestS) { bestS = s; bestF = f; } }
    for (let y = y0; y < Math.min(h, y0 + size); y++) ch[y] = bestF;
  }
  return ch;
}
function filterContest(f: Form, w: number, h: number): { name: string; choice: Uint8Array; raw: Uint8Array; z1: number } {
  const stride = w * f.bpp;
  const filtered: Uint8Array[] = [];
  for (let t = 0; t < 5; t++) { const ch = new Uint8Array(h).fill(t); filtered.push(buildFiltered(f.samples, w, h, f.bpp, ch)); }
  const cands: { name: string; choice: Uint8Array }[] = [];
  const push = (name: string, choice: Uint8Array) => cands.push({ name, choice });
  for (let t = 0; t < 5; t++) push('f' + t, new Uint8Array(h).fill(t));
  push('minsum', minsumChoice(f.samples, w, h, f.bpp));
  if (f.ct === 3) push('smartup', smartUp(f.samples, w, h, f.bpp));
  push('band16', bandCandidates(f.samples, w, h, f.bpp, 16));
  push('band32', bandCandidates(f.samples, w, h, f.bpp, 32));
  // Viterbi over hybrid lazy+entropy costs.
  const rc = lazyRowCosts(filtered, w, h, f.bpp);
  const pens = f.bpp === 1 ? [0, 96, 640] : [400, 1600];
  for (const p of pens) push('vit' + p, viterbi(rc, h, p));
  if (w * f.bpp * h <= 2000000) push('brute', bruteGreedy(f.samples, w, h, f.bpp));
  // Dedupe + rank by zlib level 1; re-rank the top 3 by zlib level 9
  // (z1 misranks: on i007 vit1600 wins z1 but f0 wins z9 by ~1k).
  const seen = new Set<string>(); const scored: { name: string; choice: Uint8Array; raw: Uint8Array; z1: number }[] = [];
  for (const c of cands) {
    const k = c.choice.join(',');
    if (seen.has(k)) continue; seen.add(k);
    const raw = buildFiltered(f.samples, w, h, f.bpp, c.choice);
    const z1 = deflateSync(raw, { level: 1 }).length;
    scored.push({ name: c.name, choice: c.choice, raw, z1 });
  }
  scored.sort((a, b) => a.z1 - b.z1);
  let best = scored[0]; let bestZ9 = deflateSync(best.raw, { level: 9 }).length;
  for (const c of scored.slice(1, 3)) { const z9 = deflateSync(c.raw, { level: 9 }).length; if (z9 < bestZ9) { best = c; bestZ9 = z9; } }
  return best;
}
function quickRank(f: Form, w: number, h: number): number {
  const cands: Uint8Array[] = [new Uint8Array(h).fill(0), minsumChoice(f.samples, w, h, f.bpp)];
  if (f.ct === 3) cands.push(smartUp(f.samples, w, h, f.bpp));
  let best = Infinity;
  for (const c of cands) { const raw = buildFiltered(f.samples, w, h, f.bpp, c); const s = deflateSync(raw, { level: 1 }).length; if (s < best) best = s; }
  return best;
}
function encodeInstance(rgba: Uint8Array, w: number, h: number): { png: Uint8Array; info: string } {
  const t0 = process.hrtime.bigint();
  const ph = (label: string) => { if (DIAG) console.error('  phase ' + label + ' ms=' + (Number(process.hrtime.bigint() - t0) / 1e6).toFixed(0)); };
  const forms = buildForms(rgba, w, h);
  ph('forms');
  const ranked = forms.map(f => ({ f, q: quickRank(f, w, h) + pngOverhead(f) })).sort((a, b) => a.q - b.q);
  ph('quickRank');
  const top = ranked.slice(0, 2);
  // Contest both top forms first (cheap), then run the expensive custom parse
  // only where it can plausibly win: skip a form whose zlib9 is >5% worse.
  const contested: { f: Form; win: { name: string; choice: Uint8Array; raw: Uint8Array; z1: number }; z9: Uint8Array; bandEnds: number[] }[] = [];
  for (const { f } of top) {
    const win = filterContest(f, w, h);
    ph('contest-' + f.name);
    const z9 = deflateSync(win.raw, { level: 9 });
    const bandEnds: number[] = []; const stride = w * f.bpp;
    for (let y = 1; y < h; y++) if (win.choice[y] !== win.choice[y - 1]) bandEnds.push(y * (stride + 1));
    contested.push({ f, win, z9, bandEnds });
  }
  // Custom parse runs on ONE form only (best zlib9 after the contest): the
  // second form's custom run costs as much as the first and rarely wins.
  // Budgets by stream size: small streams get full budgets (12 iters, Pareto 4,
  // depth 64); big streams get reduced budgets (6 iters, Pareto 2, depth 32).
  const bestZ9 = Math.min(...contested.map(c => c.z9.length));
  const chosen = contested.find(c => c.z9.length === bestZ9) as { f: Form; win: { name: string; choice: Uint8Array; raw: Uint8Array; z1: number }; z9: Uint8Array; bandEnds: number[] };
  let bestPng: Uint8Array | null = null; let bestInfo = '';
  for (const { f, win, z9, bandEnds } of [chosen]) {
    const stride = w * f.bpp;
    const big = win.raw.length > 2000000;
    const iters = big ? 6 : 12;
    const custom = deflateCustom(win.raw, stride + 1, bandEnds, iters, f.bpp === 1, big ? 32 : 64, big ? 2 : 4);
    ph('custom-' + f.name);
    const useCustom = custom.out.length <= z9.length;
    const def = useCustom ? custom.out : z9;
    const chunks: [string, Uint8Array][] = [['IHDR', ihdrOf(w, h, f.ct)]];
    if (f.pal) chunks.push(['PLTE', f.pal]);
    if (f.trns) chunks.push(['tRNS', f.trns]);
    chunks.push(['IDAT', def]);
    chunks.push(['IEND', new Uint8Array(0)]);
    const png = pngOf(chunks);
    const ms = Number(process.hrtime.bigint() - t0) / 1e6;
    const info = `${f.name} ct${f.ct} filter=${win.name} z1=${win.z1} z9=${z9.length} custom=${custom.out.length} ${useCustom ? 'CUSTOM' : 'ZLIB9'} kraftBad=${custom.kraftBad} blocks=${custom.blocks} png=${png.length} ms=${ms.toFixed(0)}`;
    if (!bestPng || png.length < bestPng.length) { bestPng = png; bestInfo = info; }
  }
  return { png: bestPng as Uint8Array, info: bestInfo };
}

function main(): void {
  const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
  const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
  const t0 = process.hrtime.bigint();
  for (const id of readdirSync(I).sort()) {
    const bytes = new Uint8Array(readFileSync(join(I, id, 'image.png')));
    const { w, h, rgba } = decodePng(bytes);
    const { png, info } = encodeInstance(rgba, w, h);
    mkdirSync(join(O, id), { recursive: true });
    writeFileSync(join(O, id, 'image.png'), png);
    if (DIAG) console.error(id + ' ' + info);
  }
  if (DIAG) console.error('TOTAL ms=' + (Number(process.hrtime.bigint() - t0) / 1e6).toFixed(0));
}

if (process.argv[1] && process.argv[1].endsWith('main.ts')) main();
export { decodePng, encodeInstance, findMatches, matchLenAt, deflateCustom, packageMerge, kraftOk, buildForms, buildFiltered, filterContest, quickRank, minsumChoice, smartUp, bruteGreedy, bandCandidates, lazyRowCosts, viterbi, parseBlock, huffLengths, emitBlock, BitWriter, lenSym, distSym, LEN_EXTRA, DIST_EXTRA, LEN_BASE, DIST_BASE, canonicalCodes };
export type { Form };
