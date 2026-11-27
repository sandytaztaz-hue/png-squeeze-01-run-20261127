// PNG squeeze R5: palette/grey/RGB(A) forms, filter Viterbi + strip DP + SmartUp,
// hash-chain match finder with row-above probes, dual-basin-ish optimal parse
// (fixed-cost start, then cost-refinement passes), package-merge Huffman,
// block split at filter boundaries. Deterministic, fixed budgets.
import { readFileSync, writeFileSync, mkdirSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { inflateSync, inflateRawSync, deflateRawSync } from 'node:zlib';

const NODE = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTD = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const W = 1280, H = 720;

// ---------- CRC / Adler ----------
const CRC_T = (() => { const t = new Int32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; t[n] = c; } return t; })();
function crc32(b: Uint8Array, s = 0, e = b.length): number { let c = -1; for (let i = s; i < e; i++) c = CRC_T[(c ^ b[i]) & 255] ^ (c >>> 8); return (c ^ -1) >>> 0; }
function adler(b: Uint8Array): number { let a = 1, c = 0; for (let i = 0; i < b.length;) { const e = Math.min(b.length, i + 5552); for (; i < e; i++) { a += b[i]; c += a; } a %= 65521; c %= 65521; } return ((c << 16) | a) >>> 0; }
function chunk(type: string, data: Uint8Array): Uint8Array { const o = new Uint8Array(12 + data.length); const v = new DataView(o.buffer); v.setUint32(0, data.length); for (let i = 0; i < 4; i++) o[4 + i] = type.charCodeAt(i); o.set(data, 8); v.setUint32(8 + data.length, crc32(o, 4, 8 + data.length)); return o; }
function pngFile(ct: number, plte: Uint8Array | null, trns: Uint8Array | null, idat: Uint8Array): Uint8Array {
  const ih = new Uint8Array(13); const v = new DataView(ih.buffer); v.setUint32(0, W); v.setUint32(4, H); ih[8] = 8; ih[9] = ct;
  const parts: Uint8Array[] = [new Uint8Array([137, 80, 78, 71, 13, 10, 26, 10]), chunk('IHDR', ih)];
  if (plte) parts.push(chunk('PLTE', plte));
  if (trns) parts.push(chunk('tRNS', trns));
  parts.push(chunk('IDAT', idat)); parts.push(chunk('IEND', new Uint8Array(0)));
  let n = 0; for (const p of parts) n += p.length; const o = new Uint8Array(n); let a = 0; for (const p of parts) { o.set(p, a); a += p.length; } return o;
}
function zlibWrap(def: Uint8Array, orig: Uint8Array): Uint8Array { const o = new Uint8Array(def.length + 6); o[0] = 0x78; o[1] = 0x9c; o.set(def, 2); new DataView(o.buffer).setUint32(2 + def.length, adler(orig)); return o; }

// ---------- PNG decode to RGBA ----------
function decodePng(bytes: Uint8Array): Uint8Array {
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8, ct = 6, pal: Uint8Array | null = null, tr: Uint8Array | null = null; const idat: Uint8Array[] = [];
  while (at < bytes.length) { const len = view.getUint32(at); const ty = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]); const d = bytes.subarray(at + 8, at + 8 + len); at += 12 + len;
    if (ty === 'IHDR') ct = d[9]; else if (ty === 'PLTE') pal = d; else if (ty === 'tRNS') tr = d; else if (ty === 'IDAT') idat.push(d); else if (ty === 'IEND') break; }
  const id = idat.length === 1 ? idat[0] : Buffer.concat(idat);
  const raw = inflateSync(id);
  const bpp = ct === 6 ? 4 : ct === 2 ? 3 : ct === 4 ? 2 : ct === 0 ? 1 : 1;
  const stride = W * bpp, samples = new Uint8Array(H * stride);
  for (let y = 0; y < H; y++) { const ft = raw[y * (stride + 1)]; const src = y * (stride + 1) + 1, o = y * stride, p = o - stride;
    for (let i = 0; i < stride; i++) { const x = raw[src + i]; let val: number;
      if (ft === 0) val = x; else if (ft === 1) val = x + (i >= bpp ? samples[o + i - bpp] : 0);
      else if (ft === 2) val = x + (y > 0 ? samples[p + i] : 0);
      else if (ft === 3) val = x + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
      else { const a = i >= bpp ? samples[o + i - bpp] : 0, bb = y > 0 ? samples[p + i] : 0, cc = y > 0 && i >= bpp ? samples[p + i - bpp] : 0; const pp = a + bb - cc; const pa = pp > a ? pp - a : a - pp, pb = pp > bb ? pp - bb : bb - pp, pc = pp > cc ? pp - cc : cc - pp; val = x + (pa <= pb && pa <= pc ? a : pb <= pc ? bb : cc); }
      samples[o + i] = val & 255; } }
  if (ct === 6) return samples;
  const rgba = new Uint8Array(W * H * 4);
  if (ct === 2) { const key = tr ? (tr[1] << 16) | (tr[3] << 8) | tr[5] : -1; for (let i = 0, s = 0, d = 0; i < W * H; i++, s += 3, d += 4) { rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2]; rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255; } }
  else if (ct === 0) { const key = tr ? tr[1] : -1; for (let i = 0, d = 0; i < W * H; i++, d += 4) { const g = samples[i]; rgba[d] = rgba[d + 1] = rgba[d + 2] = g; rgba[d + 3] = g === key ? 0 : 255; } }
  else if (ct === 4) { for (let i = 0, s = 0, d = 0; i < W * H; i++, s += 2, d += 4) { rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s]; rgba[d + 3] = samples[s + 1]; } }
  else { const lut = new Uint8Array((pal!.length / 3) * 4); for (let e = 0; e < pal!.length / 3; e++) { lut[e * 4] = pal![e * 3]; lut[e * 4 + 1] = pal![e * 3 + 1]; lut[e * 4 + 2] = pal![e * 3 + 2]; lut[e * 4 + 3] = tr && e < tr.length ? tr[e] : 255; } for (let i = 0, d = 0; i < W * H; i++, d += 4) { const e = samples[i] * 4; rgba[d] = lut[e]; rgba[d + 1] = lut[e + 1]; rgba[d + 2] = lut[e + 2]; rgba[d + 3] = lut[e + 3]; } }
  return rgba;
}

// ---------- PNG filtering ----------
function paeth(a: number, b: number, c: number): number { const p = a + b - c; const pa = p > a ? p - a : a - p, pb = p > b ? p - b : b - p, pc = p > c ? p - c : c - p; return pa <= pb && pa <= pc ? a : pb <= pc ? b : c; }
// Build filtered versions for the given types (each H rows of stride+1), plus
// per-row entropy + minsum costs over those types.
function filterSubset(samples: Uint8Array, bpp: number, types: number[]): { filt: (Uint8Array | null)[]; ent: Float64Array; minsum: Uint8Array } {
  const stride = W * bpp, rs = stride + 1;
  const filt: (Uint8Array | null)[] = [null, null, null, null, null]; for (const t of types) filt[t] = new Uint8Array(H * rs);
  const ent = new Float64Array(H * 5); const minsum = new Uint8Array(H);
  const freq = new Int32Array(256); const lg = new Float64Array(65536); for (let i = 1; i < 65536; i++) lg[i] = Math.log2(i);
  for (let y = 0; y < H; y++) { const cur = y * stride, prev = cur - stride;
    let bestS = Infinity, bestT = types[0];
    for (const t of types) { const out = filt[t]!; const o = y * rs; out[o] = t; let s = 0; freq.fill(0);
      for (let i = 0; i < stride; i++) { const c = samples[cur + i]; let v: number;
        if (t === 0) v = c; else if (t === 1) v = c - (i >= bpp ? samples[cur + i - bpp] : 0);
        else if (t === 2) v = c - (y > 0 ? samples[prev + i] : 0);
        else if (t === 3) v = c - (((i >= bpp ? samples[cur + i - bpp] : 0) + (y > 0 ? samples[prev + i] : 0)) >> 1);
        else v = c - paeth(i >= bpp ? samples[cur + i - bpp] : 0, y > 0 ? samples[prev + i] : 0, y > 0 && i >= bpp ? samples[prev + i - bpp] : 0);
        v &= 255; out[o + 1 + i] = v; freq[v]++; const sv = v < 128 ? v : 256 - v; s += sv; }
      // entropy bits of this filtered row (filter byte included as one extra byte of value t)
      let e = 0; const n = stride + 1; for (let v = 0; v < 256; v++) { const c = freq[v] + (v === t ? 1 : 0); if (c) e += c * (lg[n] - lg[c]); }
      ent[y * 5 + t] = e;
      if (s < bestS) { bestS = s; bestT = t; } }
    minsum[y] = bestT; }
  return { filt, ent, minsum };
}
function filterAll(samples: Uint8Array, bpp: number): { filt: (Uint8Array | null)[]; ent: Float64Array; minsum: Uint8Array } { return filterSubset(samples, bpp, [0, 1, 2, 3, 4]); }
function assemble(filt: (Uint8Array | null)[], choice: Uint8Array): Uint8Array { const rs = filt[0].length / H; const out = new Uint8Array(H * rs); for (let y = 0; y < H; y++) out.set(filt[choice[y]]!.subarray(y * rs, (y + 1) * rs), y * rs); return out; }
function viterbi(ent: Float64Array, penalty: number): Uint8Array {
  const dp = new Float64Array(5); const back = new Uint8Array(H * 5);
  for (let t = 0; t < 5; t++) dp[t] = ent[t];
  for (let y = 1; y < H; y++) { const nd = new Float64Array(5).fill(Infinity);
    for (let t = 0; t < 5; t++) { let best = Infinity, bt = 0; for (let p = 0; p < 5; p++) { const c = dp[p] + (p === t ? 0 : penalty); if (c < best) { best = c; bt = p; } } nd[t] = best + ent[y * 5 + t]; back[y * 5 + t] = bt; }
    dp.set(nd); }
  let t = 0; for (let k = 1; k < 5; k++) if (dp[k] < dp[t]) t = k;
  const ch = new Uint8Array(H); for (let y = H - 1; y >= 0; y--) { ch[y] = t; if (y > 0) t = back[y * 5 + t]; } return ch;
}
// Greedy per-row filter: each row scored by real level-1 deflate with the chosen
// prefix (last 32 KiB) as dictionary — captures cross-row matches exactly.
function greedyFilter(filt: (Uint8Array | null)[]): Uint8Array {
  const rs = filt[0].length / H; const raw = new Uint8Array(H * rs); const ch = new Uint8Array(H);
  for (let y = 0; y < H; y++) { const dict = y === 0 ? undefined : raw.subarray(Math.max(0, y * rs - 32768), y * rs);
    let best = Infinity, bt = 0;
    for (let t = 0; t < 5; t++) { const seg = filt[t]!.subarray(y * rs, (y + 1) * rs);
      const l = deflateRawSync(seg, { level: 6, dictionary: dict }).length; if (l < best) { best = l; bt = t; } }
    ch[y] = bt; raw.set(filt[bt]!.subarray(y * rs, (y + 1) * rs), y * rs); }
  return ch;
}
function smartUp(samples: Uint8Array, bpp: number): Uint8Array {
  const stride = W * bpp, ch = new Uint8Array(H);
  for (let y = 0; y < H; y++) { if (y === 0) { ch[y] = 0; continue; }
    let same = true, change = false; const cur = y * stride, prev = cur - stride;
    for (let i = 0; i < stride; i++) { if (samples[cur + i] !== samples[prev + i]) { same = false; break; } }
    if (same) { for (let i = bpp; i < stride; i++) if (samples[cur + i] !== samples[cur + i - bpp]) { change = true; break; } }
    ch[y] = same && change ? 2 : 0; }
  return ch;
}

// ---------- colour forms ----------
interface Form { ct: number; bpp: number; samples: Uint8Array; plte: Uint8Array | null; trns: Uint8Array | null; overhead: number; name: string; }
function buildForms(rgba: Uint8Array): Form[] {
  const n = W * H; const map = new Map<number, number>(); const cols: number[] = []; const freq: number[] = [];
  let grey = true, allA255 = true;
  for (let i = 0; i < n; i++) { const r = rgba[i * 4], g = rgba[i * 4 + 1], b = rgba[i * 4 + 2], a = rgba[i * 4 + 3];
    if (r !== g || g !== b) grey = false; if (a !== 255) allA255 = false;
    const key = (r << 24) | (g << 16) | (b << 8) | a; let idx = map.get(key); if (idx === undefined) { idx = cols.length; map.set(key, idx); cols.push(key); freq.push(0); } freq[idx]++; }
  const forms: Form[] = [];
  // palette forms (several orderings), if <=256 colours
  if (cols.length <= 256) {
    const orderings: number[][] = [];
    const byFreq = cols.map((_, i) => i).sort((a, b) => freq[b] - freq[a] || a - b); orderings.push(byFreq);
    // luminance
    orderings.push(cols.map((_, i) => i).sort((a, b) => { const la = ((cols[a] >>> 24) * 299 + ((cols[a] >> 16) & 255) * 587 + ((cols[a] >> 8) & 255) * 114); const lb = ((cols[b] >>> 24) * 299 + ((cols[b] >> 16) & 255) * 587 + ((cols[b] >> 8) & 255) * 114); return la - lb; }));
    // background-pinned adjacency greedy: adjacency weights from neighbour pairs
    const N = cols.length; const wgt = new Float64Array(N * N);
    const idxOf = (key: number) => map.get(key)!;
    for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) { const i = y * W + x; const k = (rgba[i * 4] << 24) | (rgba[i * 4 + 1] << 16) | (rgba[i * 4 + 2] << 8) | rgba[i * 4 + 3]; const a = idxOf(k);
      if (x + 1 < W) { const j = i + 1; const k2 = (rgba[j * 4] << 24) | (rgba[j * 4 + 1] << 16) | (rgba[j * 4 + 2] << 8) | rgba[j * 4 + 3]; const bb = idxOf(k2); if (bb !== a) { wgt[a * N + bb]++; wgt[bb * N + a]++; } }
      if (y + 1 < H) { const j = i + W; const k2 = (rgba[j * 4] << 24) | (rgba[j * 4 + 1] << 16) | (rgba[j * 4 + 2] << 8) | rgba[j * 4 + 3]; const bb = idxOf(k2); if (bb !== a) { wgt[a * N + bb]++; wgt[bb * N + a]++; } } }
    const bg = byFreq[0]; const used = new Uint8Array(N); const adj: number[] = [bg]; used[bg] = 1;
    const scoreTo = new Float64Array(N);
    for (let step = 1; step < N; step++) { const last = adj[adj.length - 1]; for (let i = 0; i < N; i++) if (!used[i]) scoreTo[i] += wgt[last * N + i];
      let best = -1, bs = -1; for (let i = 0; i < N; i++) if (!used[i]) { const s = scoreTo[i] * 1000 + freq[i]; if (s > bs) { bs = s; best = i; } }
      adj.push(best); used[best] = 1; }
    orderings.push(adj);
    for (const ord of orderings) {
      const inv = new Uint8Array(N); for (let p = 0; p < N; p++) inv[ord[p]] = p;
      const samples = new Uint8Array(n);
      for (let i = 0; i < n; i++) { const k = (rgba[i * 4] << 24) | (rgba[i * 4 + 1] << 16) | (rgba[i * 4 + 2] << 8) | rgba[i * 4 + 3]; samples[i] = inv[map.get(k)!]; }
      const plte = new Uint8Array(N * 3); const trns = new Uint8Array(N); let hasA = false;
      for (let p = 0; p < N; p++) { const c = cols[ord[p]]; plte[p * 3] = (c >>> 24) & 255; plte[p * 3 + 1] = (c >> 16) & 255; plte[p * 3 + 2] = (c >> 8) & 255; trns[p] = c & 255; if ((c & 255) !== 255) hasA = true; }
      let tlen = N; while (tlen > 0 && trns[tlen - 1] === 255) tlen--;
      forms.push({ ct: 3, bpp: 1, samples, plte, trns: hasA ? trns.subarray(0, tlen) : null, overhead: 12 + N * 3 + (hasA ? 12 + tlen : 0), name: 'pal' });
    }
  }
  if (grey) {
    if (allA255) { const s = new Uint8Array(n); for (let i = 0; i < n; i++) s[i] = rgba[i * 4]; forms.push({ ct: 0, bpp: 1, samples: s, plte: null, trns: null, overhead: 0, name: 'grey' }); }
    else { const s = new Uint8Array(n * 2); for (let i = 0; i < n; i++) { s[i * 2] = rgba[i * 4]; s[i * 2 + 1] = rgba[i * 4 + 3]; } forms.push({ ct: 4, bpp: 2, samples: s, plte: null, trns: null, overhead: 0, name: 'greyA' }); }
  }
  if (allA255) { const s = new Uint8Array(n * 3); for (let i = 0; i < n; i++) { s[i * 3] = rgba[i * 4]; s[i * 3 + 1] = rgba[i * 4 + 1]; s[i * 3 + 2] = rgba[i * 4 + 2]; } forms.push({ ct: 2, bpp: 3, samples: s, plte: null, trns: null, overhead: 0, name: 'rgb' }); }
  forms.push({ ct: 6, bpp: 4, samples: rgba, plte: null, trns: null, overhead: 0, name: 'rgba' });
  return forms;
}
// Choose best filter sequence for a form by zlib level-1 ranking.
function bestFilter(form: Form, fa?: ReturnType<typeof filterAll>, light = false): { raw: Uint8Array; z1: number } {
  if (light) { const { filt } = filterSubset(form.samples, form.bpp, [0]); const ch = new Uint8Array(H).fill(0); const raw = assemble(filt, ch); return { raw, z1: deflateRawSync(raw, { level: 1 }).length }; }
  const { filt, ent, minsum } = fa ?? filterAll(form.samples, form.bpp);
  const cands: { ch: Uint8Array; tag: string }[] = [];
  const fixed: Uint8Array[] = [];
  for (let t = 0; t < 5; t++) { const c = new Uint8Array(H).fill(t); fixed.push(c); if (!light || t === 0) cands.push({ ch: c, tag: 'fixed' + t }); }
  cands.push({ ch: minsum, tag: 'minsum' });
  if (form.bpp < 3) cands.push({ ch: greedyFilter(filt), tag: 'greedy' });
  if (form.ct === 3) cands.push({ ch: smartUp(form.samples, form.bpp), tag: 'smart' });
  if (!light) for (const p of [0, 256, 1024]) cands.push({ ch: viterbi(ent, p), tag: 'vit' + p });
  const scored: { raw: Uint8Array; z1: number; tag: string }[] = [];
  for (const c of cands) { const raw = assemble(filt, c.ch); scored.push({ raw, z1: deflateRawSync(raw, { level: 1 }).length, tag: c.tag }); }
  scored.sort((a, b) => a.z1 - b.z1);
  if (form.bpp >= 3) {
    // Multi-byte forms: level 1 and level 4 both misrank fixed-None. Re-rank the
    // level-1 winner against fixed-None by level 9 on the first 240 rows.
    // Strided sample: every 3rd row across the whole image (a top-only sample
    // misranks: screenshots are flat at the top and photo-like below).
    const rs = scored[0].raw.length / H;
    const sample = (raw: Uint8Array): Uint8Array => { const o = new Uint8Array(240 * rs); const starts = [0, 180, 360, 540]; for (let b = 0; b < 4; b++) for (let k = 0; k < 60; k++) { const y = starts[b] + k; o.set(raw.subarray(y * rs, (y + 1) * rs), (b * 60 + k) * rs); } return o; };
    const pool = [scored[0]]; const f0 = scored.find(y => y.tag === 'fixed0'); if (f0 && f0 !== scored[0]) pool.push(f0);
    let best = pool[0]; let bestZ = deflateRawSync(sample(best.raw), { level: 9 }).length;
    for (let k = 1; k < pool.length; k++) { const z = deflateRawSync(sample(pool[k].raw), { level: 9 }).length; if (z < bestZ) { bestZ = z; best = pool[k]; } }
    return { raw: best.raw, z1: best.z1 };
  }
  // Single-byte forms: re-rank by level 4 the top 2 by level 1 plus fixed-None/Paeth.
  const pool: typeof scored = [];
  for (const x of scored) if (pool.length < 2) pool.push(x);
  for (const tag of ['fixed0', 'fixed4']) { const x = scored.find(y => y.tag === tag); if (x && !pool.includes(x)) pool.push(x); }
  let best = pool[0]; let bestZ = deflateRawSync(best.raw, { level: 4 }).length;
  for (let k = 1; k < pool.length; k++) { const z4 = deflateRawSync(pool[k].raw, { level: 4 }).length; if (z4 < bestZ) { bestZ = z4; best = pool[k]; } }
  return { raw: best.raw, z1: best.z1 };
}

// ---------- DEFLATE: length tables ----------
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const LEN_SYM = new Int32Array(259); { let s = 0; for (let i = 0; i < 29; i++) { const mx = i === 28 ? 258 : LEN_BASE[i + 1] - 1; for (let l = LEN_BASE[i]; l <= mx; l++) LEN_SYM[l] = 257 + i; } }
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
function distSym(d: number): number { let s = 0; while (s < 29 && DIST_BASE[s + 1] <= d) s++; return s; }
// Package-merge: code lengths (max `maxLen`) for frequencies.
function codeLengths(freq: Int32Array, maxLen: number): Uint8Array {
  const n = freq.length; const len = new Uint8Array(n);
  let nz = 0, only = -1; for (let i = 0; i < n; i++) if (freq[i] > 0) { nz++; only = i; }
  if (nz === 0) return len; if (nz === 1) { len[only] = 1; return len; }
  // items: [freq, symbol] lists per level; package-merge
  type Item = { f: number; syms: number[] };
  let lists: Item[][] = [];
  let cur: Item[] = []; for (let i = 0; i < n; i++) if (freq[i] > 0) cur.push({ f: freq[i], syms: [i] });
  cur.sort((a, b) => a.f - b.f); lists.push(cur);
  for (let lvl = 1; lvl < maxLen; lvl++) { const prev = lists[lvl - 1]; const pk: Item[] = [];
    for (let i = 0; i + 1 < prev.length; i += 2) pk.push({ f: prev[i].f + prev[i + 1].f, syms: prev[i].syms.concat(prev[i + 1].syms) });
    const merged = pk.concat(cur).sort((a, b) => a.f - b.f); lists.push(merged); }
  // count: take 2*nz-2 items from top levels
  const counts = new Int32Array(n); let need = 2 * nz - 2;
  for (let lvl = maxLen - 1; lvl >= 0 && need > 0; lvl--) { const list = lists[lvl]; const take = Math.min(need, list.length); for (let i = 0; i < take; i++) for (const s of list[i].syms) counts[s]++; need -= take; }
  // lengths: symbol appearing in k packages gets length... standard: len = number of levels it was selected in? Use counts as depths via Kraft check fallback:
  for (let i = 0; i < n; i++) if (freq[i] > 0) len[i] = Math.max(1, counts[i]);
  // Fix Kraft overflow by shortening longest / lengthening shortest iteratively (simple, deterministic)
  for (let iter = 0; iter < 64; iter++) { let kraft = 0; for (let i = 0; i < n; i++) if (len[i]) kraft += 1 << (maxLen - len[i]); const target = 1 << maxLen;
    if (kraft === target) break;
    if (kraft > target) { let worst = -1, wl = -1; for (let i = 0; i < n; i++) if (len[i] > wl && freq[i] > 0) { wl = len[i]; worst = i; } if (worst < 0 || wl >= maxLen) break; len[worst]++; }
    else { let best = -1, bl = 99; for (let i = 0; i < n; i++) if (len[i] > 0 && len[i] < bl) { bl = len[i]; best = i; } if (best < 0) break; len[best]--; } }
  return len;
}
function canonicalCodes(len: Uint8Array): { code: Int32Array; } {
  const code = new Int32Array(len.length); let cur = 0, prev = 0;
  const maxL = Math.max(0, ...len);
  const cnt = new Int32Array(maxL + 2); for (const l of len) if (l) cnt[l]++;
  const next = new Int32Array(maxL + 2); for (let l = 1; l <= maxL; l++) { cur = (cur + cnt[l - 1]) << 1; next[l] = cur; }
  for (let i = 0; i < len.length; i++) if (len[i]) { code[i] = next[len[i]]; next[len[i]]++; }
  return { code };
}
function revBits(code: number, len: number): number { let r = 0; for (let i = 0; i < len; i++) { r = (r << 1) | (code & 1); code >>>= 1; } return r; }

class BitWriter {
  out: number[] = []; acc = 0; nbits = 0;
  bits(v: number, n: number) { this.acc |= (v & ((1 << n) - 1)) << this.nbits; this.nbits += n; while (this.nbits >= 8) { this.out.push(this.acc & 255); this.acc >>>= 8; this.nbits -= 8; } }
  flush() { if (this.nbits > 0) { this.out.push(this.acc & 255); this.acc = 0; this.nbits = 0; } }
  bytes(): Uint8Array { return new Uint8Array(this.out); }
}

// ---------- match finder (hash chain + row-above probes) ----------
// Per position up to 4 Pareto-optimal (length, distance) candidates: a candidate is kept
// only if no kept candidate with a smaller-or-equal distance is at least as long.
// Distances are capped at the DEFLATE window 32768.
function findMatches(data: Uint8Array, rowDist: number, chainCap: number): { clen: Uint16Array; cdist: Int32Array; ccnt: Uint8Array } {
  const n = data.length; const KC = 4;
  const clen = new Uint16Array(n * KC); const cdist = new Int32Array(n * KC); const ccnt = new Uint8Array(n);
  const HS = 1 << 15; const head = new Int32Array(HS).fill(-1); const prev = new Int32Array(n);
  const hash = (i: number) => (((data[i] << 16) ^ (data[i + 1] << 8) ^ data[i + 2]) * 2654435761 >>> 17) & (HS - 1);
  const matchLen = (a: number, b: number, cap: number): number => { let l = 0; const mx = Math.min(cap, n - a); while (l < mx && data[a + l] === data[b + l]) l++; return l; };
  const candL = new Int32Array(8); const candD = new Int32Array(8);
  for (let i = 0; i + 2 < n; i++) {
    let nc = 0; let bl = 0;
    const add = (l: number, d: number) => { if (l < 3) return; for (let k = 0; k < nc; k++) if (candD[k] <= d && candL[k] >= l) return;
      let w = 0; for (let k = 0; k < nc; k++) if (!(candD[k] >= d && candL[k] <= l)) { candL[w] = candL[k]; candD[w] = candD[k]; w++; } nc = w;
      if (nc < 8) { candL[nc] = l; candD[nc] = d; nc++; } else { let worst = 0; for (let k = 1; k < nc; k++) if (candL[k] < candL[worst] || (candL[k] === candL[worst] && candD[k] > candD[worst])) worst = k; if (l > candL[worst] || (l === candL[worst] && d < candD[worst])) { candL[worst] = l; candD[worst] = d; } } };
    const probe = (d: number) => { if (d <= 0 || d > 32768 || i - d < 0) return; if (data[i] !== data[i - d] || data[i + 1] !== data[i - d + 1] || data[i + 2] !== data[i - d + 2]) return; const l = matchLen(i, i - d, 258); add(l, d); if (l > bl) bl = l; };
    probe(rowDist); probe(rowDist * 2);
    const h = hash(i); let cand = head[h]; let tries = 0;
    while (cand >= i - 32768 && cand >= 0 && tries < chainCap) { tries++;
      if (data[cand + bl] === data[i + bl] || bl < 3) { const l = matchLen(i, cand, 258); if (l >= 3) { add(l, i - cand); if (l > bl) bl = l; if (l >= 258) break; if (l >= 64) break; } }
      cand = prev[cand]; }
    // keep at most KC: longest first, then nearest
    const order = [0, 1, 2, 3, 4, 5, 6, 7].slice(0, nc).sort((a, b) => candL[b] - candL[a] || candD[a] - candD[b]);
    let c = 0; for (const k of order) { if (c >= KC) break; clen[i * KC + c] = candL[k]; cdist[i * KC + c] = candD[k]; c++; }
    ccnt[i] = c;
    prev[i] = head[h]; head[h] = i;
  }
  return { clen, cdist, ccnt };
}
// ---------- optimal parse + encode one block ----------
const FIXED_LIT_LEN = new Uint8Array(288); { for (let i = 0; i < 144; i++) FIXED_LIT_LEN[i] = 8; for (let i = 144; i < 256; i++) FIXED_LIT_LEN[i] = 9; for (let i = 256; i < 280; i++) FIXED_LIT_LEN[i] = 7; for (let i = 280; i < 288; i++) FIXED_LIT_LEN[i] = 8; }
const FIXED_DIST_LEN = new Uint8Array(32).fill(5);
const LEN_ENDS = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
interface Tok { lit: number; len: number; dist: number; } // lit>=0: literal; len>=3: match
// Exact bit cost of a token stream (min of fixed / dynamic, header included).
function exactBits(toks: Tok[]): number {
  const lf = new Int32Array(288); const df = new Int32Array(32);
  for (const t of toks) if (t.len === 0) lf[t.lit]++; else { lf[LEN_SYM[t.len]]++; df[distSym(t.dist)]++; }
  lf[256] = 1; if (toks.every(t => t.len === 0)) df[0] = 1;
  const ll = codeLengths(lf, 15); const dl = codeLengths(df, 15);
  let fixedBits = 0; for (const t of toks) fixedBits += t.len === 0 ? FIXED_LIT_LEN[t.lit] : FIXED_LIT_LEN[LEN_SYM[t.len]] + LEN_EXTRA[LEN_SYM[t.len] - 257] + 5 + DIST_EXTRA[distSym(t.dist)];
  fixedBits += FIXED_LIT_LEN[256] + 3;
  let hlit = 288; while (hlit > 257 && ll[hlit - 1] === 0) hlit--;
  let hdist = 32; while (hdist > 1 && dl[hdist - 1] === 0) hdist--;
  const allLen = new Uint8Array(hlit + hdist); allLen.set(ll.subarray(0, hlit)); allLen.set(dl.subarray(0, hdist), hlit);
  const rle: [number, number][] = []; let i = 0;
  while (i < allLen.length) { const v = allLen[i]; let j = i; while (j < allLen.length && allLen[j] === v) j++; const run = j - i;
    if (v === 0) { let r = run; while (r >= 11) { const take = Math.min(r, 138); rle.push([18, take]); r -= take; } if (r >= 3) rle.push([17, r]); else for (let k = 0; k < r; k++) rle.push([0, 0]); }
    else { rle.push([v, 0]); let r = run - 1; while (r >= 3) { const take = Math.min(r, 6); rle.push([16, take]); r -= take; } for (let k = 0; k < r; k++) rle.push([v, 0]); }
    i = j; }
  const clf = new Int32Array(19); for (const [s2] of rle) clf[s2]++;
  const clLen = codeLengths(clf, 7);
  let hclen = 19; while (hclen > 4 && clLen[CL_ORDER[hclen - 1]] === 0) hclen--;
  let dynBits = 5 + 5 + 4 + hclen * 3; for (const [s2] of rle) dynBits += clLen[s2]; for (const [s2] of rle) dynBits += s2 === 16 ? 2 : s2 === 17 ? 3 : s2 === 18 ? 7 : 0;
  for (const t of toks) dynBits += t.len === 0 ? ll[t.lit] : ll[LEN_SYM[t.len]] + LEN_EXTRA[LEN_SYM[t.len] - 257] + dl[distSym(t.dist)] + DIST_EXTRA[distSym(t.dist)];
  dynBits += ll[256] + 3;
  return Math.min(fixedBits, dynBits);
}
function parseBlockInner(data: Uint8Array, s: number, e: number, clen: Uint16Array, cdist: Int32Array, ccnt: Uint8Array, iters: number, litCost: Float64Array, distCost: Float64Array): Tok[] {
  const n = e - s;
  let toks: Tok[] = [];
  for (let it = 0; it < iters; it++) {
    const dp = new Float64Array(n + 1).fill(Infinity); const chLen = new Int16Array(n + 1); const chDist = new Int32Array(n + 1);
    dp[0] = 0;
    for (let i = 0; i < n; i++) { const base = dp[i]; if (!isFinite(base)) continue;
      const lit = data[s + i];
      const cLit = base + litCost[lit]; if (cLit < dp[i + 1]) { dp[i + 1] = cLit; chLen[i + 1] = 0; }
      const nc = ccnt[s + i];
      for (let ci = 0; ci < nc; ci++) { const L = clen[(s + i) * 4 + ci]; if (L < 3) continue; const d = cdist[(s + i) * 4 + ci]; const ds = distSym(d); const dc = distCost[ds] + DIST_EXTRA[ds];
        // Lengths where the cost can change: L, its code base, and the boundary below L.
        const symL = LEN_SYM[L]; const candLens: number[] = [L, LEN_BASE[symL - 257]];
        for (let e = LEN_ENDS.length - 1; e >= 0; e--) if (LEN_ENDS[e] < L) { candLens.push(LEN_ENDS[e]); break; }
        for (const l of candLens) { if (l < 3 || l > L || i + l > n) continue; const sym = LEN_SYM[l]; const c = base + litCost[sym] + LEN_EXTRA[sym - 257] + dc; if (c < dp[i + l]) { dp[i + l] = c; chLen[i + l] = l; chDist[i + l] = d; } } } }
    // reconstruct
    toks = []; let i = n; while (i > 0) { const l = chLen[i]; if (l === 0) { toks.push({ lit: data[s + i - 1], len: 0, dist: 0 }); i--; } else { toks.push({ lit: -1, len: l, dist: chDist[i] }); i -= l; } }
    toks.reverse();
    if (it === iters - 1) break;
    const lf = new Int32Array(288); const df = new Int32Array(32);
    for (const t of toks) if (t.len === 0) lf[t.lit]++; else { lf[LEN_SYM[t.len]]++; df[distSym(t.dist)]++; }
    lf[256] = 1; if (toks.every(t => t.len === 0)) df[0] = 1;
    const ll = codeLengths(lf, 15); const dl = codeLengths(df, 15);
    litCost = new Float64Array(288); distCost = new Float64Array(32);
    for (let k = 0; k < 288; k++) litCost[k] = ll[k] || 15; for (let k = 0; k < 32; k++) distCost[k] = dl[k] || 15;
  }
  return toks;
}
function parseBlock(data: Uint8Array, s: number, e: number, clen: Uint16Array, cdist: Int32Array, ccnt: Uint8Array, iters: number): Tok[] {
  const litA = new Float64Array(288); const distA = new Float64Array(32);
  for (let i = 0; i < 288; i++) litA[i] = FIXED_LIT_LEN[i]; for (let i = 0; i < 32; i++) distA[i] = 5;
  const toksA = parseBlockInner(data, s, e, clen, cdist, ccnt, iters, litA, distA);
  // Literal-heavy blocks: try a literal-friendly basin (entropy literal costs,
  // flat high match costs) and keep whichever token stream encodes smaller.
  const n = e - s; const freq = new Int32Array(256); for (let i = s; i < e; i++) freq[data[i]]++;
  let entBits = 0; for (let v = 0; v < 256; v++) if (freq[v]) entBits += freq[v] * Math.log2(n / freq[v]);
  const costA = exactBits(toksA);
  if (costA >= 0.55 * entBits) {
    const litB = new Float64Array(288).fill(20); const distB = new Float64Array(32).fill(20);
    for (let v = 0; v < 256; v++) litB[v] = freq[v] ? Math.max(1, Math.min(15, -Math.log2(freq[v] / n))) : 15;
    litB[256] = 7;
    const toksB = parseBlockInner(data, s, e, clen, cdist, ccnt, 2, litB, distB);
    if (exactBits(toksB) < costA) return toksB;
  }
  return toksA;
}
const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
function encodeBlock(w: BitWriter, toks: Tok[], last: boolean) {
  const lf = new Int32Array(288); const df = new Int32Array(32);
  for (const t of toks) if (t.len === 0) lf[t.lit]++; else { lf[LEN_SYM[t.len]]++; df[distSym(t.dist)]++; }
  lf[256] = 1; if (toks.every(t => t.len === 0)) df[0] = 1;
  const ll = codeLengths(lf, 15); const dl = codeLengths(df, 15);
  // fixed cost
  let fixedBits = 0; for (const t of toks) fixedBits += t.len === 0 ? FIXED_LIT_LEN[t.lit] : FIXED_LIT_LEN[LEN_SYM[t.len]] + LEN_EXTRA[LEN_SYM[t.len] - 257] + 5 + DIST_EXTRA[distSym(t.dist)];
  fixedBits += FIXED_LIT_LEN[256];
  // dynamic header cost: build CL lengths
  let hlit = 288; while (hlit > 257 && ll[hlit - 1] === 0) hlit--;
  let hdist = 32; while (hdist > 1 && dl[hdist - 1] === 0) hdist--;
  const allLen = new Uint8Array(hlit + hdist); allLen.set(ll.subarray(0, hlit)); allLen.set(dl.subarray(0, hdist), hlit);
  // RLE the code lengths
  const rle: [number, number][] = []; // [sym, extra-count or value]
  let i = 0; while (i < allLen.length) { const v = allLen[i]; let j = i; while (j < allLen.length && allLen[j] === v) j++; const run = j - i;
    if (v === 0) { let r = run; while (r >= 11) { const take = Math.min(r, 138); rle.push([18, take]); r -= take; } if (r >= 3) rle.push([17, r]); else for (let k = 0; k < r; k++) rle.push([0, 0]); }
    else { rle.push([v, 0]); let r = run - 1; while (r >= 3) { const take = Math.min(r, 6); rle.push([16, take]); r -= take; } for (let k = 0; k < r; k++) rle.push([v, 0]); }
    i = j; }
  const clf = new Int32Array(19); for (const [s] of rle) clf[s]++;
  const clLen = codeLengths(clf, 7);
  let hclen = 19; while (hclen > 4 && clLen[CL_ORDER[hclen - 1]] === 0) hclen--;
  let dynHeader = 5 + 5 + 4 + hclen * 3; for (let k = 0; k < hclen; k++) dynHeader += 0; // placeholder
  dynHeader = 5 + 5 + 4 + hclen * 3; for (const [s] of rle) dynHeader += clLen[s]; for (const [s, x] of rle) dynHeader += s === 16 ? 2 : s === 17 ? 3 : s === 18 ? 7 : 0;
  let dynBits = dynHeader; for (const t of toks) dynBits += t.len === 0 ? ll[t.lit] : ll[LEN_SYM[t.len]] + LEN_EXTRA[LEN_SYM[t.len] - 257] + dl[distSym(t.dist)] + DIST_EXTRA[distSym(t.dist)];
  dynBits += ll[256];
  const useFixed = fixedBits + 3 <= dynBits;
  w.bits(last ? 1 : 0, 1);
  if (useFixed) { w.bits(1, 2); const { code: lc } = canonicalCodes(FIXED_LIT_LEN); const { code: dc } = canonicalCodes(FIXED_DIST_LEN);
    for (const t of toks) { if (t.len === 0) w.bits(revBits(lc[t.lit], FIXED_LIT_LEN[t.lit]), FIXED_LIT_LEN[t.lit]);
      else { const sym = LEN_SYM[t.len]; w.bits(revBits(lc[sym], FIXED_LIT_LEN[sym]), FIXED_LIT_LEN[sym]); w.bits(t.len - LEN_BASE[sym - 257], LEN_EXTRA[sym - 257]); const ds = distSym(t.dist); w.bits(revBits(dc[ds], 5), 5); w.bits(t.dist - DIST_BASE[ds], DIST_EXTRA[ds]); } }
    w.bits(revBits(lc[256], 7), 7);
  } else { w.bits(2, 2); w.bits(hlit - 257, 5); w.bits(hdist - 1, 5); w.bits(hclen - 4, 4);
    for (let k = 0; k < hclen; k++) w.bits(clLen[CL_ORDER[k]], 3);
    const { code: clc } = canonicalCodes(clLen);
    for (const [s, x] of rle) { w.bits(revBits(clc[s], clLen[s]), clLen[s]); if (s === 16) w.bits(x - 3, 2); else if (s === 17) w.bits(x - 3, 3); else if (s === 18) w.bits(x - 11, 7); }
    const { code: lc } = canonicalCodes(ll); const { code: dc } = canonicalCodes(dl);
    for (const t of toks) { if (t.len === 0) w.bits(revBits(lc[t.lit], ll[t.lit]), ll[t.lit]);
      else { const sym = LEN_SYM[t.len]; w.bits(revBits(lc[sym], ll[sym]), ll[sym]); w.bits(t.len - LEN_BASE[sym - 257], LEN_EXTRA[sym - 257]); const ds = distSym(t.dist); w.bits(revBits(dc[ds], dl[ds]), dl[ds]); w.bits(t.dist - DIST_BASE[ds], DIST_EXTRA[ds]); } }
    w.bits(revBits(lc[256], ll[256]), ll[256]); }
}
function customDeflate(raw: Uint8Array, rowBytes: number, blockKB = 128): Uint8Array {
  const n = raw.length; const rs = rowBytes + 1;
  const big = n > 2000000; const chainCap = n > 1500000 ? 32 : n > 600000 ? 64 : 128;
  const { clen, cdist, ccnt } = findMatches(raw, rs, chainCap);
  // block boundaries at row starts, ~blockKB
  const bs = blockKB * 1024;
  const bounds: number[] = [0]; let at = 0; while (at < n) { let nxt = Math.min(n, at + bs); if (nxt < n) nxt = Math.ceil(nxt / rs) * rs; if (nxt <= at) nxt = at + rs; bounds.push(Math.min(n, nxt)); at = nxt; }
  const iters = 3;
  const w = new BitWriter();
  for (let b = 0; b + 1 < bounds.length; b++) { const toks = parseBlock(raw, bounds[b], bounds[b + 1], clen, cdist, ccnt, iters); encodeBlock(w, toks, b + 2 === bounds.length); }
  w.flush(); return w.bytes();
}

// ---------- main ----------
for (const id of readdirSync(NODE).sort()) {
  const rgba = decodePng(new Uint8Array(readFileSync(join(NODE, id, 'image.png'))));
  const forms = buildForms(rgba);
  let bestForm: Form | null = null, bestRaw: Uint8Array | null = null, bestScore = Infinity;
  // Rank palette orderings cheaply (minsum stream only), keep the best ordering.
  const pals = forms.filter(f => f.ct === 3);
  const palFa = new Map<Form, ReturnType<typeof filterAll>>();
  if (pals.length > 1) { let bp: Form | null = null, bz = Infinity, bfa: ReturnType<typeof filterAll> | null = null;
    for (const f of pals) { const fa = filterSubset(f.samples, f.bpp, [0, 2, 4]); const z = deflateRawSync(assemble(fa.filt, fa.minsum), { level: 1 }).length; if (z < bz) { bz = z; bp = f; bfa = null; } }
    for (const f of pals) if (f !== bp) forms.splice(forms.indexOf(f), 1);
    if (bp && bfa) palFa.set(bp, bfa); }
  const hasRgb = forms.some(f => f.name === 'rgb'); const hasPal = forms.some(f => f.ct === 3);
  for (const f of forms) { if (f.name === 'rgba' && hasRgb) continue;
    const { raw, z1 } = bestFilter(f, palFa.get(f), f.name === 'rgb' && hasPal); const tot = z1 + f.overhead + 6; if (tot < bestScore) { bestScore = tot; bestForm = f; bestRaw = raw; } }
  const raw = bestRaw!; const form = bestForm!;
  const z9 = deflateRawSync(raw, { level: 9 });
  let def: Uint8Array;
  // Sample gate: if custom deflate clearly loses on the first 256 KB block, skip it.
  let skipCustom = false;
  try { const rs = W * form.bpp + 1; const bend = Math.min(raw.length, Math.ceil(262144 / rs) * rs);
    const sCd = customDeflate(raw.subarray(0, bend), W * form.bpp, 256);
    const sZ9 = deflateRawSync(raw.subarray(0, bend), { level: 9 }).length;
    skipCustom = sCd.length > sZ9 * 1.01; } catch { skipCustom = false; }
  if (skipCustom) def = z9;
  else try { const cd = customDeflate(raw, W * form.bpp, 256); const back = inflateRawSync(cd); let ok = back.length === raw.length; if (ok) for (let i = 0; i < raw.length; i++) if (back[i] !== raw[i]) { ok = false; break; } def = ok && cd.length <= z9.length ? cd : z9; } catch { def = z9; }
  const png = pngFile(form.ct, form.plte, form.trns, zlibWrap(def, raw));
  mkdirSync(join(OUTD, id), { recursive: true });
  writeFileSync(join(OUTD, id, 'image.png'), png);
  console.log(id, form.name, 'ct' + form.ct, 'raw', raw.length, 'z9', z9.length, 'def', def.length, 'png', png.length);
}
