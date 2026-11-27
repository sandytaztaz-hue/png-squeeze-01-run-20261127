// PNG squeeze R6 — own encoder written from the R6/R5 prose briefs + kit starter.
// Colour forms + palette orderings, Viterbi/strip/band/brute-force filter search,
// hash-chain match finder, dual-basin optimal parse, package-merge Huffman.
// Deterministic: fixed budgets only, no clock, no randomness.
import { readFileSync, writeFileSync, mkdirSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { inflateSync, deflateSync } from 'node:zlib';

const NODE = process.env.MAKEFUN_DEBUG === '1';
const log = (...a) => { if (NODE) console.error(...a); };

// ---------- CRC32 / Adler ----------
const CRC_T = (() => { const t = new Int32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = (c & 1) ? 0xedb88320 ^ (c >>> 1) : c >>> 1; t[n] = c; } return t; })();
function crc32(b, s = 0, e = b.length) { let c = -1; for (let i = s; i < e; i++) c = CRC_T[(c ^ b[i]) & 255] ^ (c >>> 8); return (c ^ -1) >>> 0; }
function adler32(b) { let a = 1, c = 0; for (let i = 0; i < b.length;) { const e = Math.min(b.length, i + 5552); for (; i < e; i++) { a += b[i]; c += a; } a %= 65521; c %= 65521; } return ((c << 16) | a) >>> 0; }

// ---------- PNG decode (to RGBA) ----------
const CH = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };
function paeth(a, b, c) { const p = a + b - c, pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c); return pa <= pb && pa <= pc ? a : pb <= pc ? b : c; }
function decodePng(bytes) {
  const v = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8, header = null, pal = null, trns = null; const idat = [];
  while (at < bytes.length) {
    const len = v.getUint32(at); const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    const data = bytes.subarray(at + 8, at + 8 + len); at += 12 + len;
    if (type === 'IHDR') { const d = new DataView(data.buffer, data.byteOffset, 13); header = { w: d.getUint32(0), h: d.getUint32(4), ct: data[9] }; }
    else if (type === 'PLTE') pal = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
  }
  const { w, h, ct } = header; const bpp = CH[ct]; const stride = w * bpp;
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat));
  const samples = new Uint8Array(h * stride);
  for (let y = 0; y < h; y++) {
    const ft = raw[y * (stride + 1)], src = y * (stride + 1) + 1, o = y * stride, p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    else if (ft === 2) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    else if (ft === 3) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    else for (let i = 0; i < stride; i++) { const a = i >= bpp ? samples[o + i - bpp] : 0, b = y > 0 ? samples[p + i] : 0, c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0; samples[o + i] = raw[src + i] + paeth(a, b, c); }
  }
  const n = w * h, rgba = new Uint8Array(n * 4);
  if (ct === 6) rgba.set(samples);
  else if (ct === 2) { const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5]; for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) { rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2]; rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255; } }
  else if (ct === 0) { const key = trns === null ? -1 : trns[1]; for (let i = 0, d = 0; i < n; i++, d += 4) { const g = samples[i]; rgba[d] = rgba[d + 1] = rgba[d + 2] = g; rgba[d + 3] = g === key ? 0 : 255; } }
  else if (ct === 4) { for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) { rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s]; rgba[d + 3] = samples[s + 1]; } }
  else { const e = pal.length / 3, lut = new Uint8Array(e * 4); for (let k = 0; k < e; k++) { lut[k * 4] = pal[k * 3]; lut[k * 4 + 1] = pal[k * 3 + 1]; lut[k * 4 + 2] = pal[k * 3 + 2]; lut[k * 4 + 3] = trns !== null && k < trns.length ? trns[k] : 255; } for (let i = 0, d = 0; i < n; i++, d += 4) { const q = samples[i] * 4; rgba[d] = lut[q]; rgba[d + 1] = lut[q + 1]; rgba[d + 2] = lut[q + 2]; rgba[d + 3] = lut[q + 3]; } }
  return { w, h, rgba };
}

// ---------- PNG write ----------
function pngOf(chunks) {
  let size = 8; for (const [, d] of chunks) size += 12 + d.length;
  const out = new Uint8Array(size); const v = new DataView(out.buffer);
  out.set([137, 80, 78, 71, 13, 10, 26, 10], 0); let at = 8;
  for (const [t, d] of chunks) {
    v.setUint32(at, d.length); out[at + 4] = t.charCodeAt(0); out[at + 5] = t.charCodeAt(1); out[at + 6] = t.charCodeAt(2); out[at + 7] = t.charCodeAt(3);
    out.set(d, at + 8); v.setUint32(at + 8 + d.length, crc32(out, at + 4, at + 8 + d.length)); at += 12 + d.length;
  }
  return out;
}
function ihdrOf(w, h, ct) { const d = new Uint8Array(13); const v = new DataView(d.buffer); v.setUint32(0, w); v.setUint32(4, h); d[8] = 8; d[9] = ct; return d; }
function zlibWrap(rawDef, rawData) {
  const out = new Uint8Array(2 + rawDef.length + 4);
  out[0] = 0x78; out[1] = 0x9c; out.set(rawDef, 2);
  new DataView(out.buffer).setUint32(2 + rawDef.length, adler32(rawData));
  return out;
}

// ---------- filters ----------
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  else if (type === 2) for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  else if (type === 3) for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  else for (let i = 0; i < n; i++) { const a = i >= bpp ? cur[i - bpp] : 0, b = prev === null ? 0 : prev[i], c = prev !== null && i >= bpp ? prev[i - bpp] : 0; out[i] = cur[i] - paeth(a, b, c); }
}
function signedSum(row) { let s = 0; for (let i = 0; i < row.length; i++) { const v = row[i]; s += v < 128 ? v : 256 - v; } return s; }
// Build the filtered stream for a filter-type array (Uint8Array H) over samples.
function buildRaw(samples, w, h, bpp, ftypes) {
  const stride = w * bpp, rs = stride + 1, raw = new Uint8Array(h * rs);
  const tmp = new Uint8Array(stride);
  for (let y = 0; y < h; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride), prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const t = ftypes[y]; raw[y * rs] = t;
    filterRow(t, cur, prev, bpp, tmp); raw.set(tmp, y * rs + 1);
  }
  return raw;
}
// All five filtered versions of every row: filt[t][y*stride .. ] (no filter byte).
function allFilters(samples, w, h, bpp) {
  const stride = w * bpp;
  const out = [];
  for (let t = 0; t < 5; t++) out.push(new Uint8Array(h * stride));
  const tmp = new Uint8Array(stride);
  for (let y = 0; y < h; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride), prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    for (let t = 0; t < 5; t++) { filterRow(t, cur, prev, bpp, tmp); out[t].set(tmp, y * stride); }
  }
  return out;
}

// ---------- colour forms ----------
// A form: {ct, bpp, samples, pal (Uint8Array rgb), trns (Uint8Array|null), name, overhead}
function buildForms(rgba, w, h) {
  const n = w * h;
  const cmap = new Map(); const cols = []; const cnt = [];
  let allGrey = true; const alphaSet = new Set(); const transCols = new Map();
  for (let i = 0; i < n; i++) {
    const r = rgba[i * 4], g = rgba[i * 4 + 1], b = rgba[i * 4 + 2], a = rgba[i * 4 + 3];
    if (r !== g || g !== b) allGrey = false;
    alphaSet.add(a);
    const key = ((r * 256 + g) * 256 + b) * 256 + a;
    let ix = cmap.get(key);
    if (ix === undefined) { ix = cols.length; cmap.set(key, ix); cols.push([r, g, b, a]); cnt.push(0); }
    cnt[ix]++;
    if (a === 0) transCols.set((r << 16) | (g << 8) | b, (transCols.get((r << 16) | (g << 8) | b) || 0) + 1);
  }
  const forms = [];
  const idxOf = new Map(); for (let i = 0; i < cols.length; i++) idxOf.set(((cols[i][0] * 256 + cols[i][1]) * 256 + cols[i][2]) * 256 + cols[i][3], i);
  // RGBA (always possible)
  forms.push({ ct: 6, bpp: 4, samples: rgba, pal: null, trns: null, name: 'rgba', overhead: 0 });
  // Palette
  if (cols.length <= 256) {
    const orderings = paletteOrderings(cols, cnt, rgba, w, h, idxOf);
    for (const o of orderings) {
      const samples = new Uint8Array(n);
      const remap = new Int32Array(cols.length);
      for (let p = 0; p < o.length; p++) remap[o[p]] = p;
      for (let i = 0; i < n; i++) samples[i] = remap[idxOf.get(((rgba[i * 4] * 256 + rgba[i * 4 + 1]) * 256 + rgba[i * 4 + 2]) * 256 + rgba[i * 4 + 3])];
      const pal = new Uint8Array(o.length * 3); const trns = new Uint8Array(o.length);
      let lastOp = -1;
      for (let p = 0; p < o.length; p++) { const c = cols[o[p]]; pal[p * 3] = c[0]; pal[p * 3 + 1] = c[1]; pal[p * 3 + 2] = c[2]; trns[p] = c[3]; if (c[3] !== 255) lastOp = p; }
      const tr = lastOp >= 0 ? trns.subarray(0, lastOp + 1) : null;
      forms.push({ ct: 3, bpp: 1, samples, pal, trns: tr, name: 'pal-' + o.tag, overhead: 12 + pal.length + (tr ? 12 + tr.length : 0) });
    }
  }
  // Grey
  if (allGrey) {
    const g = new Uint8Array(n); for (let i = 0; i < n; i++) g[i] = rgba[i * 4];
    if (alphaSet.size === 1 && alphaSet.has(255)) forms.push({ ct: 0, bpp: 1, samples: g, pal: null, trns: null, name: 'grey', overhead: 0 });
    else if ([...alphaSet].every(a => a === 0 || a === 255)) {
      // one transparent grey value?
      const tg = new Set(); for (let i = 0; i < n; i++) if (rgba[i * 4 + 3] === 0) tg.add(rgba[i * 4]);
      if (tg.size === 1) { const tr = new Uint8Array(2); tr[1] = [...tg][0]; forms.push({ ct: 0, bpp: 1, samples: g, pal: null, trns: tr, name: 'grey-trns', overhead: 14 }); }
      else { const ga = new Uint8Array(n * 2); for (let i = 0; i < n; i++) { ga[i * 2] = rgba[i * 4]; ga[i * 2 + 1] = rgba[i * 4 + 3]; } forms.push({ ct: 4, bpp: 2, samples: ga, pal: null, trns: null, name: 'grey-alpha', overhead: 0 }); }
    } else { const ga = new Uint8Array(n * 2); for (let i = 0; i < n; i++) { ga[i * 2] = rgba[i * 4]; ga[i * 2 + 1] = rgba[i * 4 + 3]; } forms.push({ ct: 4, bpp: 2, samples: ga, pal: null, trns: null, name: 'grey-alpha', overhead: 0 }); }
  }
  // RGB (+ transparency key)
  if ([...alphaSet].every(a => a === 0 || a === 255)) {
    const rgb = new Uint8Array(n * 3); for (let i = 0; i < n; i++) { rgb[i * 3] = rgba[i * 4]; rgb[i * 3 + 1] = rgba[i * 4 + 1]; rgb[i * 3 + 2] = rgba[i * 4 + 2]; }
    if (alphaSet.size === 1 && alphaSet.has(255)) forms.push({ ct: 2, bpp: 3, samples: rgb, pal: null, trns: null, name: 'rgb', overhead: 0 });
    else if (transCols.size === 1) { const k = [...transCols.keys()][0]; const tr = new Uint8Array(6); tr[1] = (k >> 16) & 255; tr[3] = (k >> 8) & 255; tr[5] = k & 255; forms.push({ ct: 2, bpp: 3, samples: rgb, pal: null, trns: tr, name: 'rgb-trns', overhead: 18 }); }
  }
  return forms;
}
// Palette orderings: frequency, luminance, border-pinned, adjacency-greedy. Each returned order has .tag.
function paletteOrderings(cols, cnt, rgba, w, h, idxOf) {
  const n = cols.length;
  const byFreq = [...Array(n).keys()].sort((a, b) => cnt[b] - cnt[a]);
  const lum = c => 0.299 * cols[c][0] + 0.587 * cols[c][1] + 0.114 * cols[c][2];
  const byLum = [...Array(n).keys()].sort((a, b) => lum(a) - lum(b));
  // border-pinned: colours on the image border first (by freq), then the rest by freq
  const border = new Set();
  for (let x = 0; x < w; x++) { border.add(idxOf.get(((rgba[x * 4] * 256 + rgba[x * 4 + 1]) * 256 + rgba[x * 4 + 2]) * 256 + rgba[x * 4 + 3])); border.add(idxOf.get(((rgba[((h - 1) * w + x) * 4] * 256 + rgba[((h - 1) * w + x) * 4 + 1]) * 256 + rgba[((h - 1) * w + x) * 4 + 2]) * 256 + rgba[((h - 1) * w + x) * 4 + 3])); }
  for (let y = 0; y < h; y++) { border.add(idxOf.get(((rgba[(y * w) * 4] * 256 + rgba[(y * w) * 4 + 1]) * 256 + rgba[(y * w) * 4 + 2]) * 256 + rgba[(y * w) * 4 + 3])); border.add(idxOf.get(((rgba[(y * w + w - 1) * 4] * 256 + rgba[(y * w + w - 1) * 4 + 1]) * 256 + rgba[(y * w + w - 1) * 4 + 2]) * 256 + rgba[(y * w + w - 1) * 4 + 3])); }
  const byBorder = [...border].sort((a, b) => cnt[b] - cnt[a]).concat(byFreq.filter(c => !border.has(c)));
  // adjacency-greedy: background (most frequent) at 0, then walk to the colour most adjacent to the last placed
  const adj = new Map(); // key a*n+b -> pair count (horizontal + vertical neighbours)
  const pix = new Int32Array(w * h);
  for (let i = 0; i < w * h; i++) pix[i] = idxOf.get(((rgba[i * 4] * 256 + rgba[i * 4 + 1]) * 256 + rgba[i * 4 + 2]) * 256 + rgba[i * 4 + 3]);
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    const c = pix[y * w + x];
    if (x + 1 < w) { const d = pix[y * w + x + 1]; if (d !== c) { const k = c * n + d; adj.set(k, (adj.get(k) || 0) + 1); const k2 = d * n + c; adj.set(k2, (adj.get(k2) || 0) + 1); } }
    if (y + 1 < h) { const d = pix[(y + 1) * w + x]; if (d !== c) { const k = c * n + d; adj.set(k, (adj.get(k) || 0) + 1); const k2 = d * n + c; adj.set(k2, (adj.get(k2) || 0) + 1); } }
  }
  const byAdj = [];
  const rem = new Set(byFreq);
  let cur = byFreq[0]; byAdj.push(cur); rem.delete(cur);
  while (rem.size) {
    let best = -1, bestW = -1;
    for (const c of rem) { const ww = adj.get(cur * n + c) || 0; const score = ww * 1000000 + cnt[c]; if (score > bestW) { bestW = score; best = c; } }
    byAdj.push(best); rem.delete(best); cur = best;
  }
  const tag = (arr, t) => { arr.tag = t; return arr; };
  const out = [tag(byFreq, 'freq'), tag(byLum, 'lum'), tag(byBorder, 'border'), tag(byAdj, 'adj')];
  // de-dup identical orderings
  const seen = new Set(); return out.filter(o => { const k = o.join(','); if (seen.has(k)) return false; seen.add(k); return true; });
}

// ---------- filter search ----------
const z6 = (buf, dict) => deflateSync(buf, dict ? { level: 6, dictionary: dict } : { level: 6 });
const z1 = (buf, dict) => deflateSync(buf, dict ? { level: 1, dictionary: dict } : { level: 1 });
const z9 = buf => deflateSync(buf, { level: 9 });
function rowCostMatrix(filt, raw0, w, h, bpp) {
  const stride = w * bpp, rs = stride + 1, H = h;
  const cost = new Float64Array(H * 5);
  const chunk = new Uint8Array(rs);
  for (let y = 0; y < H; y++) {
    const dict = raw0.subarray(Math.max(0, y * rs - 32768), y * rs);
    for (let t = 0; t < 5; t++) {
      chunk[0] = t; chunk.set(filt[t].subarray(y * stride, (y + 1) * stride), 1);
      cost[y * 5 + t] = z6(chunk, dict.length ? dict : undefined).length;
    }
  }
  return cost;
}
function viterbiRows(cost, H, penalty) {
  const dp = new Float64Array(H * 5), back = new Int8Array(H * 5);
  for (let t = 0; t < 5; t++) dp[t] = cost[t];
  for (let y = 1; y < H; y++) for (let t = 0; t < 5; t++) {
    let best = Infinity, bt = 0;
    for (let p = 0; p < 5; p++) { const c = dp[(y - 1) * 5 + p] + (p === t ? 0 : penalty); if (c < best) { best = c; bt = p; } }
    dp[y * 5 + t] = best + cost[y * 5 + t]; back[y * 5 + t] = bt;
  }
  const out = new Uint8Array(H); let t = 0; for (let k = 1; k < 5; k++) if (dp[(H - 1) * 5 + k] < dp[(H - 1) * 5 + t]) t = k;
  for (let y = H - 1; y >= 0; y--) { out[y] = t; t = back[y * 5 + t]; }
  return out;
}
function bruteForce(filt, w, h, bpp) {
  const stride = w * bpp, rs = stride + 1, H = h;
  const out = new Uint8Array(H), raw = new Uint8Array(H * rs);
  const chunk = new Uint8Array(rs);
  for (let y = 0; y < H; y++) {
    const dict = raw.subarray(Math.max(0, y * rs - 32768), y * rs);
    let best = Infinity, bt = 0;
    for (let t = 0; t < 5; t++) {
      chunk[0] = t; chunk.set(filt[t].subarray(y * stride, (y + 1) * stride), 1);
      const s = z1(chunk, dict.length ? dict : undefined).length;
      if (s < best) { best = s; bt = t; }
    }
    out[y] = bt; raw[y * rs] = bt; raw.set(filt[bt].subarray(y * stride, (y + 1) * stride), y * rs + 1);
  }
  return out;
}
function minsumTypes(filt, samples, w, h, bpp) {
  const stride = w * bpp, out = new Uint8Array(h);
  for (let y = 0; y < h; y++) { let best = Infinity, bt = 0; for (let t = 0; t < 5; t++) { const s = signedSum(filt[t].subarray(y * stride, (y + 1) * stride)); if (s < best) { best = s; bt = t; } } out[y] = bt; }
  return out;
}
function smartUp(samples, w, h, bpp) {
  const stride = w * bpp, out = new Uint8Array(h);
  for (let y = 0; y < h; y++) {
    if (y === 0) { out[y] = 0; continue; }
    const cur = samples.subarray(y * stride, (y + 1) * stride), prev = samples.subarray((y - 1) * stride, y * stride);
    let same = true, change = false;
    for (let i = 0; i < stride; i++) if (cur[i] !== prev[i]) { same = false; break; }
    if (same) { for (let i = 1; i < stride; i++) if (cur[i] !== cur[i - 1]) { change = true; break; } out[y] = change ? 2 : 0; }
    else out[y] = 0;
  }
  return out;
}
function stripViterbi(cost, H, band, penalty) {
  const nb = Math.ceil(H / band);
  const bc = new Float64Array(nb * 5);
  for (let b = 0; b < nb; b++) { const y0 = b * band, y1 = Math.min(H, y0 + band); for (let t = 0; t < 5; t++) { let s = 0; for (let y = y0; y < y1; y++) s += cost[y * 5 + t]; bc[b * 5 + t] = s; } }
  const seq = viterbiRows(bc, nb, penalty);
  const out = new Uint8Array(H);
  for (let b = 0; b < nb; b++) { const y0 = b * band, y1 = Math.min(H, y0 + band); for (let y = y0; y < y1; y++) out[y] = seq[b]; }
  return out;
}
function bandFixed(cost, H, band) {
  const out = new Uint8Array(H);
  for (let y0 = 0; y0 < H; y0 += band) { const y1 = Math.min(H, y0 + band); let bt = 0, bs = Infinity; for (let t = 0; t < 5; t++) { let s = 0; for (let y = y0; y < y1; y++) s += cost[y * 5 + t]; if (s < bs) { bs = s; bt = t; } } for (let y = y0; y < y1; y++) out[y] = bt; }
  return out;
}
// Snap filter-change boundaries ±12 rows, coarse-to-fine, scored by real mid-level compression of the region.
function snapReal(ftypes, samples, w, h, bpp, rawRef) {
  const stride = w * bpp, rs = stride + 1, H = h;
  const f = Uint8Array.from(ftypes);
  const bounds = [];
  for (let y = 1; y < H; y++) if (f[y] !== f[y - 1]) bounds.push(y);
  if (bounds.length > 24) return f;
  const regionScore = (y0, y1, ft) => {
    const buf = new Uint8Array((y1 - y0) * rs);
    const tmp = new Uint8Array(stride);
    for (let y = y0; y < y1; y++) {
      const cur = samples.subarray(y * stride, (y + 1) * stride), prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
      buf[(y - y0) * rs] = ft[y]; filterRow(ft[y], cur, prev, bpp, tmp); buf.set(tmp, (y - y0) * rs + 1);
    }
    const dict = rawRef.subarray(Math.max(0, y0 * rs - 32768), y0 * rs);
    return z6(buf, dict.length ? dict : undefined).length;
  };
  for (const b0 of bounds) {
    let curB = b0;
    for (const step of [5, 2, 1]) {
      let bestB = curB, bestS = regionScore(Math.max(0, curB - 20), Math.min(H, curB + 20), f);
      for (let d = -12; d <= 12; d += step) {
        if (d === 0) continue;
        const nb = curB + d; if (nb <= 1 || nb >= H) continue;
        const trial = Uint8Array.from(f);
        const oldT = f[curB], newT = f[curB - 1];
        for (let y = Math.min(curB, nb); y < Math.max(curB, nb); y++) trial[y] = nb > curB ? oldT : newT;
        const s = regionScore(Math.max(0, nb - 20), Math.min(H, nb + 20), trial);
        if (s < bestS) { bestS = s; bestB = nb; }
      }
      if (bestB !== curB) {
        const oldT = f[curB], newT = f[curB - 1];
        for (let y = Math.min(curB, bestB); y < Math.max(curB, bestB); y++) f[y] = bestB > curB ? oldT : newT;
        curB = bestB;
      }
    }
  }
  return f;
}
// Full filter search for one form. Returns candidates sorted by proxy cost, each {ftypes, method}.
function filterSearch(form, w, h) {
  const { samples, bpp } = form; const H = h, stride = w * bpp;
  const filt = allFilters(samples, w, h, bpp);
  const zero = new Uint8Array(H);
  const raw0 = buildRaw(samples, w, h, bpp, zero);
  const cost = rowCostMatrix(filt, raw0, w, h, bpp);
  const proxy = ftypes => { let s = 0; for (let y = 0; y < H; y++) s += cost[y * 5 + ftypes[y]]; return s; };
  const cands = [];
  const add = (ftypes, method) => cands.push({ ftypes, method, proxy: proxy(ftypes) });
  for (let t = 0; t < 5; t++) { const f = new Uint8Array(H).fill(t); add(f, 'fixed-' + t); }
  add(minsumTypes(filt, samples, w, h, bpp), 'minsum');
  if (form.ct === 3) add(smartUp(samples, w, h, bpp), 'smartup');
  add(bruteForce(filt, w, h, bpp), 'brute');
  const pens = bpp === 1 ? [0, 32, 96, 256, 640, 1600, 4000] : [400, 1600, 1200, 2400];
  let bestVit = null;
  for (const p of pens) { const v = viterbiRows(cost, H, p); add(v, 'viterbi-' + p); if (!bestVit || proxy(v) < proxy(bestVit)) bestVit = v; }
  const band = raw0.length > 200000 ? 16 : 10;
  for (const p of [25, 65]) add(stripViterbi(cost, H, band, p), 'strip-' + band + '-' + p);
  add(bandFixed(cost, H, 16), 'band-16');
  add(bandFixed(cost, H, 32), 'band-32');
  // snap the best viterbi + best strip candidates
  const snapped = snapReal(bestVit, samples, w, h, bpp, raw0);
  add(snapped, 'viterbi-snap');
  cands.sort((a, b) => a.proxy - b.proxy);
  // de-dup identical sequences
  const seen = new Set(), out = [];
  for (const c of cands) { const k = c.ftypes.join(','); if (seen.has(k)) continue; seen.add(k); out.push(c); }
  return { cands: out, filt };
}
// Rank the top few candidates by true compression: dual-band 50/50 blend for multi-byte, whole-stream z6 for single-byte.
function rankCandidates(cands, form, w, h) {
  const { samples, bpp } = form; const H = h, stride = w * bpp, rs = stride + 1;
  const top = cands.slice(0, 3);
  for (const c of top) {
    const raw = buildRaw(samples, w, h, bpp, c.ftypes);
    c.raw = raw;
    if (bpp > 1) {
      // runs of equal filter, short runs (<8 rows) folded into neighbours
      const runs = [];
      let y = 0;
      while (y < H) { let y1 = y + 1; while (y1 < H && c.ftypes[y1] === c.ftypes[y]) y1++; runs.push([y, y1]); y = y1; }
      const merged = [];
      for (const r of runs) { if (merged.length && r[1] - r[0] < 8) merged[merged.length - 1][1] = r[1]; else merged.push([r[0], r[1]]); }
      let sum = 0;
      for (const [y0, y1] of merged) {
        const buf = raw.subarray(y0 * rs, y1 * rs);
        const dict = raw.subarray(Math.max(0, y0 * rs - 32768), y0 * rs);
        sum += z6(buf, dict.length ? dict : undefined).length - 10;
      }
      const whole = z6(raw).length;
      c.score = (sum + whole) / 2;
    } else {
      c.score = z9(raw).length;
    }
  }
  top.sort((a, b) => a.score - b.score);
  return top[0];
}

// ---------- DEFLATE tables ----------
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
function lenSymOf(len) { for (let s = 0; s < 29; s++) { const lo = LEN_BASE[s], hi = s === 28 ? 258 : LEN_BASE[s + 1] - 1; if (len >= lo && len <= hi) return s; } return 28; }
function distSymOf(d) { for (let s = 0; s < 30; s++) { const lo = DIST_BASE[s], hi = s === 29 ? 32768 : DIST_BASE[s + 1] - 1; if (d >= lo && d <= hi) return s; } return 29; }
const FIXED_LIT_LEN = new Uint8Array(288); const FIXED_DIST_LEN = new Uint8Array(32);
for (let i = 0; i < 288; i++) FIXED_LIT_LEN[i] = i < 144 ? 8 : i < 256 ? 9 : i < 280 ? 7 : 8;
FIXED_DIST_LEN.fill(5);

// ---------- package-merge length-limited Huffman ----------
// Returns Uint8Array lengths (0 = unused), max length <= maxBits, complete code.
function codeLengths(freq, maxBits) {
  const n = freq.length;
  const lens = new Uint8Array(n);
  const syms = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) syms.push(i);
  if (syms.length === 0) return lens;
  if (syms.length === 1) {
    // a one-symbol code of length 1 is incomplete (Kraft 0.5) and zlib rejects it:
    // give a second (unused) symbol length 1 so the code is complete.
    lens[syms[0]] = 1;
    for (let i = 0; i < n; i++) if (i !== syms[0]) { lens[i] = 1; break; }
    return lens;
  }
  // lists of nodes {f, s:[symbols]}
  let cur = syms.map(s => ({ f: freq[s], s: [s] })).sort((a, b) => a.f - b.f);
  const first = cur;
  const cap = 2 * syms.length - 2;
  for (let b = 1; b <= maxBits; b++) {
    const packaged = [];
    for (let i = 0; i + 1 < cur.length; i += 2) packaged.push({ f: cur[i].f + cur[i + 1].f, s: cur[i].s.concat(cur[i + 1].s) });
    // merge packaged + first, sorted by f
    const merged = [];
    let i = 0, j = 0;
    while (i < packaged.length && j < first.length) { if (packaged[i].f <= first[j].f) merged.push(packaged[i++]); else merged.push(first[j++]); }
    while (i < packaged.length) merged.push(packaged[i++]);
    while (j < first.length) merged.push(first[j++]);
    cur = merged.length > cap ? merged.slice(0, cap) : merged;
  }
  // count occurrences in the first (2n-2) nodes of the final list
  const take = cur.slice(0, cap);
  for (const node of take) for (const s of node.s) lens[s]++;
  // fix-up: any symbol with 0 length (should not happen) gets 1
  for (const s of syms) if (lens[s] === 0) lens[s] = 1;
  return repairLens(lens, freq, maxBits);
}
// The package-merge counts always form a complete code (Kraft 1) but can yield a
// length of maxBits+1 (its count is then necessarily even). Repair: clamp those to
// maxBits (each adds 1 unit of 2^-(maxBits+1)) and remove the excess units in pairs
// by lengthening low-frequency codes. Falls back to a flat complete code if invalid.
function repairLens(lens, freq, L) {
  const n = lens.length;
  let over = 0;
  for (let i = 0; i < n; i++) if (lens[i] > L) { lens[i] = L; over++; }
  if (over === 0) {
    if (validLens(lens, L)) return lens;
    return flatLengths(freq, L);
  }
  let need = over; // units of 2^-(L+1) to remove; even when Kraft was exactly 1
  let guard = 0;
  while (need > 0 && guard++ < 10000) {
    // lengthen a lowest-frequency length-(L-1) code to L: removes exactly 2 units
    let best = -1;
    for (let i = 0; i < n; i++) if (lens[i] === L - 1 && (best < 0 || freq[i] < freq[best])) best = i;
    if (best >= 0) { lens[best] = L; need -= 2; continue; }
    // no (L-1) code: lengthen the lowest-frequency code at the largest length < L-1
    let bl = -1, bb = -1;
    for (let i = 0; i < n; i++) if (lens[i] > 0 && lens[i] < L - 1 && (bl < 0 || lens[i] > bl || (lens[i] === bl && freq[i] < freq[bb]))) { bl = lens[i]; bb = i; }
    if (bb < 0) break;
    const removed = 1 << (L - bl);
    lens[bb] = bl + 1; need -= removed;
    // if we removed too much, add units back by shortening high-frequency codes
    while (need < 0) {
      let add = -need, step = 1;
      while (step * 2 <= add) step *= 2;
      let lg = 0; while ((1 << lg) < step) lg++;
      const targetLen = L + 1 - lg; // shortening a length-targetLen code adds `step` units
      let cand = -1;
      for (let i = 0; i < n; i++) if (lens[i] === targetLen && (cand < 0 || freq[i] > freq[cand])) cand = i;
      if (cand < 0) { if (step <= 2) break; step /= 2; continue; }
      lens[cand] = targetLen - 1; need += step;
    }
  }
  if (validLens(lens, L)) return lens;
  return flatLengths(freq, L);
}
function validLens(lens, L) {
  let k = 0, mx = 0;
  for (const l of lens) { if (l) { k += 2 ** -l; if (l > mx) mx = l; } }
  return mx <= L && Math.abs(k - 1) < 1e-9;
}
// A complete prefix code with max length L: all used symbols start at
// ceil(log2(nsym)), then the highest-frequency codes are shortened until Kraft is 1.
function flatLengths(freq, L) {
  const n = freq.length, lens = new Uint8Array(n);
  const syms = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) syms.push(i);
  if (syms.length === 0) return lens;
  if (syms.length === 1) { lens[syms[0]] = 1; for (let i = 0; i < n; i++) if (i !== syms[0]) { lens[i] = 1; break; } return lens; }
  let m = 1; while ((1 << m) < syms.length) m++;
  if (m > L) m = L;
  for (const s of syms) lens[s] = m;
  syms.sort((a, b) => freq[b] - freq[a]);
  // Kraft is syms.length / 2^m <= 1; shorten highest-frequency codes (m -> m-1, ...) until Kraft == 1
  let kraftNum = syms.length; // in units of 2^-m
  const target = 1 << m;
  let idx = 0;
  while (kraftNum < target && idx < syms.length) {
    const s = syms[idx++];
    if (lens[s] <= 1) continue;
    const inc = 1 << (m - lens[s]); // shortening length l adds 2^(m-l) units
    lens[s]--; kraftNum += inc;
  }
  return lens;
}
// Canonical codes from lengths: returns {codes: Uint16Array, lens}
function canonicalCodes(lens) {
  const n = lens.length; const codes = new Uint16Array(n);
  let maxL = 0; for (let i = 0; i < n; i++) if (lens[i] > maxL) maxL = lens[i];
  const bl = new Uint16Array(maxL + 2);
  for (let i = 0; i < n; i++) bl[lens[i]]++;
  bl[0] = 0;
  const next = new Uint16Array(maxL + 2); let code = 0;
  for (let b = 1; b <= maxL; b++) { code = (code + bl[b - 1]) << 1; next[b] = code; }
  for (let i = 0; i < n; i++) if (lens[i]) { codes[i] = next[lens[i]]; next[lens[i]]++; }
  return { codes, maxL };
}
function revBits(code, len) { let r = 0; for (let i = 0; i < len; i++) { r = (r << 1) | (code & 1); code >>>= 1; } return r; }

// ---------- bit writer ----------
class BitWriter {
  constructor() { this.bytes = []; this.acc = 0; this.nbits = 0; }
  put(value, len) { // len bits, LSB first
    this.acc |= (value & ((1 << len) - 1)) << this.nbits; this.nbits += len;
    while (this.nbits >= 8) { this.bytes.push(this.acc & 255); this.acc >>>= 8; this.nbits -= 8; }
  }
  putHuff(code, len) { this.put(revBits(code, len), len); }
  flush() { if (this.nbits > 0) { this.bytes.push(this.acc & 255); this.acc = 0; this.nbits = 0; } }
  result() { this.flush(); return Uint8Array.from(this.bytes); }
  get length() { return this.bytes.length + (this.nbits > 0 ? 1 : 0); }
}

// ---------- block emission ----------
// tokens: {sym: Int32Array (0-255 literal, 257+lenSym match), len: Uint16Array, dist: Uint16Array}, count n
function emitBlock(w, tok, n, litLens, distLens, isFinal, fixed) {
  w.put(isFinal ? 1 : 0, 1);
  let ll, dl, lc, dc;
  if (fixed) { w.put(1, 2); ll = FIXED_LIT_LEN; dl = FIXED_DIST_LEN; }
  else {
    w.put(2, 2);
    // trim trailing zero lengths
    let nLit = 288; while (nLit > 257 && litLens[nLit - 1] === 0) nLit--;
    let nDist = 32; while (nDist > 1 && distLens[nDist - 1] === 0) nDist--;
    // RLE-encode combined lengths
    const all = new Uint8Array(nLit + nDist); all.set(litLens.subarray(0, nLit), 0); all.set(distLens.subarray(0, nDist), nLit);
    const rsym = [], rextra = [], rbits = [];
    let i = 0;
    while (i < all.length) {
      const v = all[i];
      if (v === 0) {
        let run = 0; while (i + run < all.length && all[i + run] === 0) run++;
        i += run;
        while (run > 0) { if (run >= 11) { const c = Math.min(run, 138); rsym.push(18); rextra.push(c - 11); rbits.push(7); run -= c; } else if (run >= 3) { const c = Math.min(run, 10); rsym.push(17); rextra.push(c - 3); rbits.push(3); run -= c; } else { rsym.push(0); rextra.push(0); rbits.push(0); run--; } }
      } else {
        rsym.push(v); rextra.push(0); rbits.push(0); i++;
        let run = 0; while (i + run < all.length && all[i + run] === v) run++;
        i += run;
        while (run >= 3) { const c = Math.min(run, 6); rsym.push(16); rextra.push(c - 3); rbits.push(2); run -= c; }
        for (let k = 0; k < run; k++) { rsym.push(v); rextra.push(0); rbits.push(0); }
      }
    }
    const cfreq = new Uint32Array(19); for (const s of rsym) cfreq[s]++;
    const clLens = codeLengths(cfreq, 7);
    const ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
    let nCl = 19; while (nCl > 4 && clLens[ORDER[nCl - 1]] === 0) nCl--;
    w.put(nLit - 257, 5); w.put(nDist - 1, 5); w.put(nCl - 4, 4);
    for (let k = 0; k < nCl; k++) w.put(clLens[ORDER[k]], 3);
    const cc = canonicalCodes(clLens);
    for (let k = 0; k < rsym.length; k++) { w.putHuff(cc.codes[rsym[k]], clLens[rsym[k]]); if (rbits[k]) w.put(rextra[k], rbits[k]); }
    ll = litLens; dl = distLens;
  }
  const lcc = canonicalCodes(ll), dcc = canonicalCodes(dl);
  for (let k = 0; k < n; k++) {
    const s = tok.sym[k];
    if (s < 256) { w.putHuff(lcc.codes[s], ll[s]); }
    else {
      const ls = s - 257, L = tok.len[k], D = tok.dist[k];
      w.putHuff(lcc.codes[s], ll[s]);
      if (LEN_EXTRA[ls]) w.put(L - LEN_BASE[ls], LEN_EXTRA[ls]);
      const ds = distSymOf(D);
      w.putHuff(dcc.codes[ds], dl[ds]);
      if (DIST_EXTRA[ds]) w.put(D - DIST_BASE[ds], DIST_EXTRA[ds]);
    }
  }
  w.putHuff(lcc.codes[256], ll[256]); // end of block
}

// ---------- hash-chain match finder ----------
// Match length between suffixes at a and b, capped at lim (4-byte chunks, then bytes).
function mlen(win, a, b, lim) {
  let k = 0;
  let la = win.length - a, lb = win.length - b;
  if (lim > la) lim = la; if (lim > lb) lim = lb;
  while (k + 4 <= lim) {
    const x = win[a + k] | (win[a + k + 1] << 8) | (win[a + k + 2] << 16) | (win[a + k + 3] << 24);
    const y = win[b + k] | (win[b + k + 1] << 8) | (win[b + k + 2] << 16) | (win[b + k + 3] << 24);
    if (x !== y) break;
    k += 4;
  }
  while (k < lim && win[a + k] === win[b + k]) k++;
  return k;
}
// A plain binary search tree over suffixes degenerates on repetitive screenshot data
// (insert aborts at its depth cap, so most positions are never inserted and later
// searches find nothing). A hash chain with O(1) insertion, most-recent-first walk,
// early exit on a long match, and run / row-above / periodic probes finds the same
// matches reliably. For every block position it returns up to 4 Pareto (len, dist) pairs.
function findMatches(win, bpp, stride, bStart, bLen, maxDepth, maxLen, opts) {
  const W = win.length;
  const paretoMax = (opts && opts.pareto) || 4;
  const goodEnough = (opts && opts.goodEnough) || 48;
  const run = new Uint16Array(W);
  for (let i = W - 2; i >= 0; i--) run[i] = win[i] === win[i + 1] ? (run[i + 1] >= 520 ? 520 : run[i + 1] + 1) : 1;
  run[W - 1] = 1;
  // prun[i]: length of the forward periodic match (distance bpp) starting at i
  const prun = new Uint16Array(W);
  if (bpp > 1) for (let i = W - 1; i >= 0; i--) { const nx = i + 1 < W ? prun[i + 1] : 0; prun[i] = i >= bpp && win[i] === win[i - bpp] ? Math.min(520, nx + 1) : 0; }
  const HEADN = 65536;
  const head = new Int32Array(HEADN).fill(-1);
  const prev = new Int32Array(W).fill(-1);
  const maxRunPos = new Int32Array(256).fill(-1);
  const hashOf = p => {
    if (p + 2 < W) { const h = (((win[p] << 16) ^ (win[p + 1] << 8) ^ win[p + 2]) * 2654435761) >>> 0; return (h >>> 16) & 65535; }
    return win[p];
  };
  const insert = p => {
    if (run[p] >= 258) return;
    const h = hashOf(p);
    prev[p] = head[h]; head[h] = p;
  };
  for (let p = 0; p < bStart; p++) { insert(p); if (run[p] >= 258) maxRunPos[win[p]] = p; }
  const mCnt = new Uint8Array(bLen), mLen = new Uint16Array(bLen * paretoMax), mDist = new Uint16Array(bLen * paretoMax);
  const cand = [];
  const addCand = (len, dist) => {
    if (len < 3 || dist < 1 || dist > 32768) return;
    for (let i = 0; i < cand.length; i++) if (cand[i][0] === len) { if (dist < cand[i][1]) cand[i][1] = dist; return; }
    cand.push([len, dist]);
  };
  const rowDist = stride + 1;
  const chainCap = maxDepth;
  for (let q = 0; q < bLen; q++) {
    const p = bStart + q;
    cand.length = 0;
    if (run[p] >= 3 && p > 0 && win[p] === win[p - 1]) addCand(Math.min(run[p], maxLen), 1);
    if (bpp > 1 && prun[p] >= 3) addCand(Math.min(prun[p], maxLen), bpp);
    if (p - rowDist >= 0) { const l = mlen(win, p, p - rowDist, maxLen); if (l >= 3) addCand(l, rowDist); }
    if (p - 2 * rowDist >= 0) { const l = mlen(win, p, p - 2 * rowDist, maxLen); if (l >= 3) addCand(l, 2 * rowDist); }
    if (run[p] >= 258 && maxRunPos[win[p]] >= 0) addCand(maxLen, p - maxRunPos[win[p]]);
    // chain walk, most recent first; skip it deep inside a long identical run
    if (run[p] < 32) {
      let node = head[hashOf(p)];
      let steps = 0, bestLen = 0;
      while (node >= 0 && steps < chainCap) {
        steps++;
        // Cheap pre-check: a node can only beat bestLen if its byte at offset
        // bestLen matches (later nodes are farther, so a tie is never useful).
        // This skips ~all full compares for nodes that mismatch early.
        let len = 0;
        if (bestLen >= 3 && p + bestLen < W && node + bestLen < W && win[node + bestLen] !== win[p + bestLen]) len = 0;
        else len = mlen(win, p, node, maxLen);
        if (len >= 3) { addCand(len, p - node); if (len > bestLen) bestLen = len; }
        if (bestLen >= goodEnough) break;
        node = prev[node];
      }
    }
    cand.sort((a, b) => b[0] - a[0]);
    let bestDist = 32769, cnt = 0;
    for (const [l, d] of cand) {
      if (d < bestDist) { bestDist = d; mLen[q * paretoMax + cnt] = l; mDist[q * paretoMax + cnt] = d; cnt++; if (cnt === paretoMax) break; }
    }
    mCnt[q] = cnt;
    if (run[p] >= 258) maxRunPos[win[p]] = p;
    insert(p);
  }
  return { mCnt, mLen, mDist };
}

// ---------- optimal parse ----------
// Precomputed length-code range endpoints.
const LEN_LO = new Uint16Array(259), LEN_HI = new Uint16Array(259);
for (let l = 3; l <= 258; l++) { const s = lenSymOf(l); LEN_LO[l] = LEN_BASE[s]; LEN_HI[l] = s === 28 ? 258 : LEN_BASE[s + 1] - 1; }
function parseBlock(win, bStart, bLen, bpp, stride, opts) {
  const { maxDepth, maxLen, iters, dense } = opts;
  const PM = opts.pareto || 4;
  const N = bLen;
  const { mCnt, mLen, mDist } = findMatches(win, bpp, stride, bStart, bLen, maxDepth, maxLen, opts);
  const cost = new Float64Array(N + 1);
  const chLen = new Uint16Array(N + 1), chDist = new Int32Array(N + 1);
  const litCost = new Float64Array(256), lenCost = new Float64Array(259), distCost = new Float64Array(32769);
  // DP with given cost tables; returns {bits, tok} where tok = {sym, len, dist, n}
  const dpRun = () => {
    cost.fill(Infinity); cost[0] = 0;
    for (let i = 0; i < N; i++) {
      const ci = cost[i];
      if (!Number.isFinite(ci)) continue;
      const v0 = ci + litCost[win[bStart + i]];
      if (v0 < cost[i + 1]) { cost[i + 1] = v0; chLen[i + 1] = 0; chDist[i + 1] = 0; }
      const cnt = mCnt[i];
      for (let k = 0; k < cnt; k++) {
        const len = mLen[i * PM + k], dist = mDist[i * PM + k];
        const dc = distCost[dist];
        // expand to length-code endpoints + 3 + len
        const candL = [len, LEN_LO[len], LEN_HI[len], 3];
        for (let q = 0; q < 4; q++) {
          const L = candL[q];
          if (L < 3 || L > len) continue;
          if (q > 0 && (L === len || L === candL[q - 1])) continue;
          const j = i + L, v = ci + lenCost[L] + dc;
          if (v < cost[j]) { cost[j] = v; chLen[j] = L; chDist[j] = dist; }
        }
      }
    }
    // reconstruct tokens
    const sym = [], lenA = [], distA = [];
    let j = N;
    while (j > 0) {
      const L = chLen[j];
      if (L === 0) { sym.push(win[bStart + j - 1]); lenA.push(0); distA.push(0); j--; }
      else { const D = chDist[j]; sym.push(257 + lenSymOf(L)); lenA.push(L); distA.push(D); j -= L; }
    }
    sym.reverse(); lenA.reverse(); distA.reverse();
    return { bits: cost[N], sym: Int32Array.from(sym), len: Uint16Array.from(lenA), dist: Uint16Array.from(distA), n: sym.length };
  };
  const freqsOf = tok => {
    const lf = new Uint32Array(288), df = new Uint32Array(32);
    for (let k = 0; k < tok.n; k++) {
      const s = tok.sym[k];
      if (s < 256) lf[s]++; else { lf[s]++; df[distSymOf(tok.dist[k])]++; }
    }
    lf[256] = 1;
    if (!tok.n || df.every(x => x === 0)) df[0] = 1;
    return { lf, df };
  };
  const emitEval = (tok, ll, dl) => {
    const w1 = new BitWriter(); emitBlock(w1, tok, tok.n, ll, dl, false, false);
    const dyn = w1.length;
    const w2 = new BitWriter(); emitBlock(w2, tok, tok.n, ll, dl, false, true);
    const fix = w2.length;
    return fix < dyn ? { bytes: fix, fixed: true } : { bytes: dyn, fixed: false };
  };
  // Track the best parse by DP bit cost; emit only once at the end of the basin
  // (emitting every iteration costs more than the DP itself on big streams).
  const setCostsFromLens = (ll, dl) => {
    for (let b = 0; b < 256; b++) litCost[b] = ll[b] || 15;
    for (let l = 3; l <= 258; l++) { const s = lenSymOf(l); lenCost[l] = (ll[257 + s] || 15) + LEN_EXTRA[s]; }
    for (let d = 1; d <= 32768; d++) { const s = distSymOf(d); distCost[d] = (dl[s] || 15) + DIST_EXTRA[s]; }
  };
  // one basin: initLens {ll, dl} or entropy init; returns best {tok, ll, dl, fixed, bytes}
  const runBasin = (init, nIter, damped) => {
    let ll, dl;
    if (init.entropy) {
      // literal entropy costs, matches flat high
      const freq = new Uint32Array(256);
      for (let i = 0; i < N; i++) freq[win[bStart + i]]++;
      for (let b = 0; b < 256; b++) { const p = (freq[b] + 1) / (N + 256); litCost[b] = Math.max(0.5, Math.min(15, -Math.log2(p))); }
      for (let l = 3; l <= 258; l++) lenCost[l] = 12 + LEN_EXTRA[lenSymOf(l)];
      for (let d = 1; d <= 32768; d++) distCost[d] = 12 + DIST_EXTRA[distSymOf(d)];
      ll = FIXED_LIT_LEN; dl = FIXED_DIST_LEN;
    } else { ll = init.ll; dl = init.dl; setCostsFromLens(ll, dl); }
    let best = null; // {tok, ll, dl, bits} — best by DP bit cost; emitted once at the end
    const consider = tok => { if (!best || tok.bits < best.bits) best = { tok, ll, dl, bits: tok.bits }; };
    let prevLit = null, prevLen = null, prevDist = null;
    for (let it = 0; it < nIter; it++) {
      if (it > 0) {
        // re-derive lens from previous parse
        const f = freqsOf(best.tok);
        ll = codeLengths(f.lf, 15); dl = codeLengths(f.df, 15);
        if (ll[256] === 0) ll[256] = 1;
        if (damped && it % 3 === 2 && prevLit) {
          // damped costs: average of new and previous cost tables
          setCostsFromLens(ll, dl);
          for (let b = 0; b < 256; b++) litCost[b] = (litCost[b] + prevLit[b]) / 2;
          for (let l = 3; l <= 258; l++) lenCost[l] = (lenCost[l] + prevLen[l]) / 2;
          for (let d = 1; d <= 32768; d++) distCost[d] = (distCost[d] + prevDist[d]) / 2;
          prevLit = Float64Array.from(litCost); prevLen = Float64Array.from(lenCost); prevDist = Float64Array.from(distCost);
          consider(dpRun());
          continue;
        }
        setCostsFromLens(ll, dl);
        prevLit = Float64Array.from(litCost); prevLen = Float64Array.from(lenCost); prevDist = Float64Array.from(distCost);
      }
      consider(dpRun());
    }
    if (!best) return null;
    // The lens that scored the winning parse may give length 0 to a symbol the
    // parse actually uses (the DP costs such symbols at 15, so it can pick them).
    // Emitting with a 0-length code writes zero bits for that symbol and corrupts
    // the stream. Re-derive the lens from the winning token set so every used
    // symbol (plus EOB) has a real length, then emit once with those lens.
    const ff = freqsOf(best.tok);
    const ll2 = codeLengths(ff.lf, 15), dl2 = codeLengths(ff.df, 15);
    if (ll2[256] === 0) ll2[256] = 1;
    const ev = emitEval(best.tok, ll2, dl2);
    return { tok: best.tok, ll: ll2, dl: dl2, fixed: ev.fixed, bytes: ev.bytes };
  };
  // Basin A (match-friendly, fixed-Huffman warm start)
  const basinA = runBasin({ ll: FIXED_LIT_LEN, dl: FIXED_DIST_LEN }, iters, true);
  let best = basinA;
  // Basin B (literal-friendly) when literal-heavy
  const byteFreq = new Uint32Array(256);
  for (let i = 0; i < N; i++) byteFreq[win[bStart + i]]++;
  let entBits = 0;
  for (let b = 0; b < 256; b++) if (byteFreq[b]) { const p = byteFreq[b] / N; entBits -= byteFreq[b] * Math.log2(p); }
  const aBits = basinA.bytes * 8;
  if (aBits >= 0.55 * entBits) {
    const basinB = runBasin({ entropy: true }, 3, false);
    if (basinB && basinB.bytes < best.bytes) best = basinB;
    else if (basinB && basinB.bytes > best.bytes * 1.12) { /* clearly worse, ignore */ }
  }
  return best;
}

// ---------- whole-stream encode ----------
// Splits raw at filter-band boundaries (run-aware), cap per block. Returns {def: Uint8Array raw deflate bytes, customBytes, libBytes}
function encodeStream(raw, bpp, stride, ftypes, opts) {
  const H = ftypes.length, rs = stride + 1;
  const cap = raw.length > 2000000 ? 384 * 1024 : 512 * 1024;
  // boundaries: filter changes + size cap, nudged off long runs
  const minBlock = opts.minBlock || 16384;
  const bounds = [0];
  let last = 0;
  for (let y = 1; y < H; y++) {
    if (ftypes[y] !== ftypes[y - 1]) {
      const pos = y * rs;
      if (pos - last >= minBlock) { bounds.push(pos); last = pos; }
    }
  }
  // size-cap splits
  const withCap = [0];
  for (let i = 1; i < bounds.length; i++) {
    let p = bounds[i];
    while (p - withCap[withCap.length - 1] > cap) {
      let q = withCap[withCap.length - 1] + cap;
      // run-aware: if inside a run of >=64 identical bytes, move to run end,
      // but never past the next boundary p (that would double-cover bytes)
      let r = 0; while (q + r < raw.length && raw[q + r] === raw[q]) r++;
      if (r >= 64) q = Math.min(p, q + r);
      withCap.push(q);
    }
    withCap.push(p);
  }
  let tail = withCap[withCap.length - 1];
  while (raw.length - tail > cap) { let q = tail + cap; let r = 0; while (q + r < raw.length && raw[q + r] === raw[q]) r++; if (r >= 64) q = Math.min(raw.length, q + r); withCap.push(q); tail = q; }
  withCap.push(raw.length);
  // guard: boundaries must be strictly increasing (a non-monotonic split would double-cover bytes)
  const bounds2 = [withCap[0]];
  for (let i = 1; i < withCap.length; i++) if (withCap[i] > bounds2[bounds2.length - 1]) bounds2.push(withCap[i]);
  if (bounds2[bounds2.length - 1] !== raw.length) bounds2.push(raw.length);
  const w = new BitWriter();
  let customBytes = 0;
  for (let b = 0; b + 1 < bounds2.length; b++) {
    const s = bounds2[b], e = bounds2[b + 1];
    if (e - s <= 0) continue;
    const hs = Math.max(0, s - 32768);
    const win = raw.subarray(hs, e);
    const bs = s - hs, bl = e - s;
    const isLast = b + 2 >= bounds2.length;
    const best = parseBlock(win, bs, bl, bpp, stride, opts);
    // re-emit best into the shared writer
    const before = w.length;
    emitBlock(w, best.tok, best.tok.n, best.ll, best.dl, isLast, best.fixed);
    customBytes += w.length - before;
  }
  const def = w.result();
  const libBytes = z9(raw).length;
  return { def, customBytes: def.length, libBytes, nBlocks: bounds2.length - 1 };
}

// ---------- driver ----------
function optsFor(raw, form) {
  if (form.ct === 3) return { maxDepth: 128, maxLen: 258, iters: 5, dense: false, goodEnough: 128, minBlock: 131072 };
  if (form.bpp === 1) return { maxDepth: 512, maxLen: 258, iters: 6, dense: false, goodEnough: 128, minBlock: 16384 };
  return { maxDepth: 128, maxLen: 258, iters: 2, dense: false, goodEnough: 128, minBlock: 16384 };
}
// Cheap candidates for a form (fixed filters, minsum, smartup) ranked by whole-stream z6.
function cheapCandidates(form, w, h) {
  const { samples, bpp } = form; const H = h;
  const filt = allFilters(samples, w, h, bpp);
  const out = [];
  for (let t = 0; t < 5; t++) { const f = new Uint8Array(H).fill(t); out.push({ ftypes: f, method: 'fixed-' + t, score: z6(buildRaw(samples, w, h, bpp, f)).length }); }
  const ms = minsumTypes(filt, samples, w, h, bpp);
  out.push({ ftypes: ms, method: 'minsum', score: z6(buildRaw(samples, w, h, bpp, ms)).length });
  if (form.ct === 3) { const su = smartUp(samples, w, h, bpp); out.push({ ftypes: su, method: 'smartup', score: z6(buildRaw(samples, w, h, bpp, su)).length }); }
  out.sort((a, b) => a.score - b.score);
  const win = out[0];
  win.raw = buildRaw(samples, w, h, bpp, win.ftypes);
  return win;
}
function processImage(rgba, w, h) {
  const forms = buildForms(rgba, w, h);
  // screen forms by filter-0 zlib-6 size + chunk overhead
  const screened = [];
  const zero = new Uint8Array(h);
  for (const f of forms) {
    const raw0 = buildRaw(f.samples, w, h, f.bpp, zero);
    screened.push({ f, quick: z6(raw0).length + f.overhead });
  }
  screened.sort((a, b) => a.quick - b.quick);
  // full filter search on the best-screened form only
  const { f: f0 } = screened[0];
  const { cands } = filterSearch(f0, w, h);
  const win0 = rankCandidates(cands, f0, w, h);
  let best = { f: f0, win: win0, total: win0.score + f0.overhead };
  // second form: cheap candidates first; full search only if it can win
  if (screened.length > 1) {
    const { f: f1 } = screened[1];
    const cheap = cheapCandidates(f1, w, h);
    if (cheap.score + f1.overhead < best.total) {
      const { cands: c1 } = filterSearch(f1, w, h);
      const win1 = rankCandidates(c1, f1, w, h);
      const total1 = win1.score + f1.overhead;
      if (total1 < best.total) best = { f: f1, win: win1, total: total1 };
    }
  }
  const { f, win } = best;
  const raw = win.raw;
  const opts = optsFor(raw, f);
  const enc = encodeStream(raw, f.bpp, w * f.bpp, win.ftypes, opts);
  const customZ = enc.def.length + 6;
  let zlibStream, used;
  if (customZ <= enc.libBytes) { zlibStream = zlibWrap(enc.def, raw); used = 'custom'; }
  else { zlibStream = deflateSync(raw, { level: 9 }); used = 'zlib9'; }
  const chunks = [['IHDR', ihdrOf(w, h, f.ct)]];
  if (f.ct === 3) chunks.push(['PLTE', f.pal]);
  if (f.trns) chunks.push(['tRNS', f.trns]);
  chunks.push(['IDAT', zlibStream]);
  chunks.push(['IEND', new Uint8Array(0)]);
  const png = pngOf(chunks);
  log(`form=${f.name} filter=${win.method} raw=${raw.length} customZ=${customZ} libZ=${enc.libBytes} used=${used} blocks=${enc.nBlocks} file=${png.length}`);
  return { png, form: f.name, filter: win.method, customZ, libZ: enc.libBytes, used, fileBytes: png.length };
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const { w, h, rgba } = decodePng(readFileSync(join(I, id, 'image.png')));
  log(`--- ${id} ${w}x${h}`);
  const r = processImage(rgba, w, h);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'image.png'), r.png);
}
log('done');
