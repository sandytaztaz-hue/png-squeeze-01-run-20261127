// main.ts — PNG squeeze entry (png-squeeze-01-run-20261127).
// Lossless PNG recompression: colour-form reduction, per-row filter screen
// (incl. brute force with a 32 KiB context dictionary), optimal-parse DEFLATE.
// Node built-ins only + ./deflate.mjs (from-scratch optimal-parse DEFLATE).
import * as fs from 'node:fs';
import * as path from 'node:path';
import * as zlib from 'node:zlib';
import { deflateOpt, zlibWrap } from './deflate.mjs';

// ---- CRC-32 ----
const CT = new Int32Array(256);
for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1); CT[n] = c; }
function crc32(b) { let c = 0xFFFFFFFF; for (let i = 0; i < b.length; i++) c = CT[(c ^ b[i]) & 255] ^ (c >>> 8); return (c ^ 0xFFFFFFFF) >>> 0; }
function chunk(t, d) {
  const o = new Uint8Array(12 + d.length), v = new DataView(o.buffer);
  v.setUint32(0, d.length);
  o[4] = t.charCodeAt(0); o[5] = t.charCodeAt(1); o[6] = t.charCodeAt(2); o[7] = t.charCodeAt(3);
  o.set(d, 8); v.setUint32(8 + d.length, crc32(o.subarray(4, 8 + d.length)));
  return o;
}

// ---- PNG decode (input is colour type 6, bit depth 8) ----
function decodePng(file) {
  const b = fs.readFileSync(file);
  if (b[0] !== 137 || b[1] !== 80 || b[2] !== 78 || b[3] !== 71) throw new Error('not PNG');
  let off = 8, w = 0, h = 0, ct = 0;
  const idat = [];
  while (off < b.length) {
    const len = b.readUInt32BE(off), ty = b.toString('ascii', off + 4, off + 8);
    if (ty === 'IHDR') { w = b.readUInt32BE(off + 8); h = b.readUInt32BE(off + 12); ct = b[off + 17]; }
    else if (ty === 'IDAT') idat.push(b.subarray(off + 8, off + 8 + len));
    else if (ty === 'IEND') break;
    off += 12 + len;
  }
  if (ct !== 6) throw new Error('expected colour type 6, got ' + ct);
  const raw = zlib.inflateSync(Buffer.concat(idat));
  const st = w * 4, px = new Uint8Array(w * h * 4), prev = new Uint8Array(st);
  for (let y = 0; y < h; y++) {
    const f = raw[y * (st + 1)], row = raw.subarray(y * (st + 1) + 1, (y + 1) * (st + 1));
    const cur = px.subarray(y * st, (y + 1) * st);
    for (let x = 0; x < st; x++) {
      const a = x >= 4 ? cur[x - 4] : 0, up = prev[x], ul = x >= 4 ? prev[x - 4] : 0;
      let v = row[x];
      if (f === 1) v = (v + a) & 255;
      else if (f === 2) v = (v + up) & 255;
      else if (f === 3) v = (v + ((a + up) >> 1)) & 255;
      else if (f === 4) { const p = a + up - ul, pa = Math.abs(p - a), pb = Math.abs(p - up), pc = Math.abs(p - ul); v = (v + (pa <= pb && pa <= pc ? a : (pb <= pc ? up : ul))) & 255; }
      cur[x] = v;
    }
    prev.set(cur);
  }
  return { width: w, height: h, px };
}

// ---- analysis: distinct colours (cap 257), grey, opaque, single transparent key ----
function analyse(px, n) {
  const counts = new Map();
  let grey = true, opaque = true, over = false;
  for (let i = 0; i < n; i++) {
    const r = px[i * 4], g = px[i * 4 + 1], b = px[i * 4 + 2], a = px[i * 4 + 3];
    if (r !== g || g !== b) grey = false;
    if (a !== 255) opaque = false;
    if (!over) { const k = ((r * 256 + g) * 256 + b) * 256 + a; counts.set(k, (counts.get(k) || 0) + 1); if (counts.size > 256) { over = true; counts.clear(); } }
  }
  let key = -1;
  if (!opaque) {
    let k0 = -1, ok = true;
    for (let i = 0; i < n; i++) {
      const a = px[i * 4 + 3];
      if (a === 0) { const k = (px[i * 4] << 16) | (px[i * 4 + 1] << 8) | px[i * 4 + 2]; if (k0 < 0) k0 = k; else if (k0 !== k) { ok = false; break; } }
      else if (a !== 255) { ok = false; break; }
    }
    if (ok && k0 >= 0) {
      for (let i = 0; i < n; i++) if (px[i * 4 + 3] === 255 && ((px[i * 4] << 16) | (px[i * 4 + 1] << 8) | px[i * 4 + 2]) === k0) { ok = false; break; }
    }
    if (ok && k0 >= 0) key = k0;
  }
  return { distinct: over ? 257 : counts.size, counts, grey, opaque, key };
}

// ---- forms: {colourType, bpp, raw, plte, trns, overhead, filters} ----
function buildForms(img, an) {
  const { width, height, px } = img, n = width * height, forms = [];
  const add = (ct, bpp, raw, plte, trns, filters) => {
    let oh = 0; if (plte) oh += plte.length + 12; if (trns) oh += trns.length + 12;
    forms.push({ colourType: ct, bpp, raw, plte, trns, overhead: oh, filters });
  };
  if (an.distinct <= 256) {
    const entries = [];
    for (const [k, c] of an.counts) entries.push({ r: (k >>> 24) & 255, g: (k >>> 16) & 255, b: (k >>> 8) & 255, a: k & 255, count: c });
    const orders = [
      { name: 'count', list: [...entries].sort((x, y) => y.count - x.count) },
      { name: 'lum', list: [...entries].sort((x, y) => (299 * x.r + 587 * x.g + 114 * x.b) - (299 * y.r + 587 * y.g + 114 * y.b)) },
    ];
    for (const { name, list } of orders) {
      const trans = list.filter((e) => e.a !== 255).sort((x, y) => x.a - y.a);
      const opaq = list.filter((e) => e.a === 255);
      const fin = trans.concat(opaq);
      const idx = new Map(), plte = new Uint8Array(fin.length * 3), al = new Uint8Array(fin.length);
      for (let i = 0; i < fin.length; i++) { const e = fin[i]; idx.set(((e.r * 256 + e.g) * 256 + e.b) * 256 + e.a, i); plte[i * 3] = e.r; plte[i * 3 + 1] = e.g; plte[i * 3 + 2] = e.b; al[i] = e.a; }
      let trns = null;
      if (trans.length > 0) { let last = 0; for (let i = 0; i < fin.length; i++) if (fin[i].a !== 255) last = i; trns = al.subarray(0, last + 1); }
      const raw = new Uint8Array(n);
      for (let i = 0; i < n; i++) raw[i] = idx.get(((px[i * 4] * 256 + px[i * 4 + 1]) * 256 + px[i * 4 + 2]) * 256 + px[i * 4 + 3]);
      add(3, 1, raw, plte, trns, name === 'count' ? [0] : [0, 'minsum', 'brute']);
    }
    if (!an.grey) return forms;
  }
  if (an.grey) {
    if (an.opaque) { const raw = new Uint8Array(n); for (let i = 0; i < n; i++) raw[i] = px[i * 4]; add(0, 1, raw, null, null, [0, 1, 2, 4, 'minsum', 'pairs', 'brute']); }
    else if (an.key >= 0) { const raw = new Uint8Array(n); for (let i = 0; i < n; i++) raw[i] = px[i * 4]; add(0, 1, raw, null, new Uint8Array([0, an.key & 255]), [0, 1, 2, 4, 'minsum', 'pairs', 'brute']); }
    else { const raw = new Uint8Array(n * 2); for (let i = 0; i < n; i++) { raw[i * 2] = px[i * 4]; raw[i * 2 + 1] = px[i * 4 + 3]; } add(4, 2, raw, null, null, [0, 1, 2, 4, 'minsum', 'pairs', 'brute']); }
    return forms;
  }
  if (an.opaque) { const raw = new Uint8Array(n * 3); for (let i = 0; i < n; i++) { raw[i * 3] = px[i * 4]; raw[i * 3 + 1] = px[i * 4 + 1]; raw[i * 3 + 2] = px[i * 4 + 2]; } add(2, 3, raw, null, null, [0, 1, 2, 4, 'minsum', 'pairs', 'brute']); }
  else if (an.key >= 0) {
    const raw = new Uint8Array(n * 3);
    for (let i = 0; i < n; i++) { raw[i * 3] = px[i * 4]; raw[i * 3 + 1] = px[i * 4 + 1]; raw[i * 3 + 2] = px[i * 4 + 2]; }
    add(2, 3, raw, null, new Uint8Array([0, (an.key >> 16) & 255, 0, (an.key >> 8) & 255, 0, an.key & 255]), [0, 1, 2, 4, 'minsum', 'pairs', 'brute']);
  } else add(6, 4, px, null, null, [0, 1, 2, 4, 'minsum', 'pairs', 'brute']);
  return forms;
}

// ---- one row, all five filters, into tmp[0..4] ----
function filterRowInto(row, prevRow, bpp, tmp) {
  const L = row.length;
  for (let x = 0; x < L; x++) {
    const v = row[x], a = x >= bpp ? row[x - bpp] : 0, up = prevRow[x], ul = x >= bpp ? prevRow[x - bpp] : 0;
    const p = a + up - ul, pa = Math.abs(p - a), pb = Math.abs(p - up), pc = Math.abs(p - ul);
    const pr = pa <= pb && pa <= pc ? a : (pb <= pc ? up : ul);
    tmp[0][x] = v; tmp[1][x] = (v - a) & 255; tmp[2][x] = (v - up) & 255; tmp[3][x] = (v - ((a + up) >> 1)) & 255; tmp[4][x] = (v - pr) & 255;
  }
}

// Fixed/minsum/pairs candidates in one pass; brute candidate separately.
function filterCandidates(form, width, height) {
  const bpp = form.bpp, rb = width * bpp, stride = rb + 1, raw = form.raw;
  const out = {};
  const fixed = [];
  for (let k = 0; k < 5; k++) fixed.push(new Uint8Array(stride * height));
  const minsum = new Uint8Array(stride * height), pairs = new Uint8Array(stride * height);
  const tmp = [];
  for (let f = 0; f < 5; f++) tmp.push(new Uint8Array(rb));
  const prevRow = new Uint8Array(rb);
  const seen = new Uint32Array(65536);
  let gen = 0;
  for (let y = 0; y < height; y++) {
    const row = raw.subarray(y * rb, (y + 1) * rb);
    filterRowInto(row, prevRow, bpp, tmp);
    const sums = [0, 0, 0, 0, 0], pc = [0, 0, 0, 0, 0], pb = [-1, -1, -1, -1, -1];
    const gs = [++gen, ++gen, ++gen, ++gen, ++gen];
    for (let x = 0; x < rb; x++) for (let f = 0; f < 5; f++) {
      const fv = tmp[f][x], sv = fv >= 128 ? fv - 256 : fv;
      sums[f] += sv < 0 ? -sv : sv;
      const pair = (pb[f] << 8) | fv;
      if (pb[f] >= 0 && seen[pair] !== gs[f]) { seen[pair] = gs[f]; pc[f]++; }
      pb[f] = fv;
    }
    let bs = 0, bp = 0;
    for (let f = 1; f < 5; f++) { if (sums[f] < sums[bs]) bs = f; if (pc[f] < pc[bp]) bp = f; }
    const base = y * stride;
    for (let f = 0; f < 5; f++) { fixed[f][base] = f; fixed[f].set(tmp[f], base + 1); }
    minsum[base] = bs; minsum.set(tmp[bs], base + 1);
    pairs[base] = bp; pairs.set(tmp[bp], base + 1);
    prevRow.set(row);
  }
  for (let f = 0; f < 5; f++) out[f] = fixed[f];
  out['minsum'] = minsum; out['pairs'] = pairs;
  return out;
}

// Brute force: per row, the filter whose trial compresses smallest at zlib
// level 4 with the previous 32 KiB of filtered output as dictionary.
function bruteFiltered(form, width, height) {
  const bpp = form.bpp, rb = width * bpp, stride = rb + 1, raw = form.raw;
  const out = new Uint8Array(stride * height);
  const trial = [];
  for (let f = 0; f < 5; f++) { const t = new Uint8Array(stride); t[0] = f; trial.push(t); }
  const tmp = [];
  for (let f = 0; f < 5; f++) tmp.push(new Uint8Array(rb));
  const prevRow = new Uint8Array(rb);
  for (let y = 0; y < height; y++) {
    const row = raw.subarray(y * rb, (y + 1) * rb);
    filterRowInto(row, prevRow, bpp, tmp);
    for (let f = 0; f < 5; f++) trial[f].set(tmp[f], 1);
    const at = y * stride;
    const before = out.subarray(Math.max(0, at - 32768), at);
    let bt = 0, best = Infinity;
    for (let f = 0; f < 5; f++) {
      const cost = zlib.deflateSync(trial[f], before.length === 0 ? { level: 4, memLevel: 9 } : { level: 4, memLevel: 9, dictionary: before }).length;
      if (cost < best) { best = cost; bt = f; }
    }
    out[at] = bt; out.set(tmp[bt], at + 1);
    prevRow.set(row);
  }
  return out;
}

function encodePng(img, form, stream) {
  const ihdr = new Uint8Array(13), dv = new DataView(ihdr.buffer);
  dv.setUint32(0, img.width); dv.setUint32(4, img.height);
  ihdr[8] = 8; ihdr[9] = form.colourType;
  const parts = [new Uint8Array([137, 80, 78, 71, 13, 10, 26, 10]), chunk('IHDR', ihdr)];
  if (form.plte) parts.push(chunk('PLTE', form.plte));
  if (form.trns) parts.push(chunk('tRNS', form.trns));
  parts.push(chunk('IDAT', stream));
  parts.push(chunk('IEND', new Uint8Array(0)));
  let total = 0; for (const p of parts) total += p.length;
  const o = new Uint8Array(total); let n = 0;
  for (const p of parts) { o.set(p, n); n += p.length; }
  return o;
}

function processImage(inFile, outFile) {
  const img = decodePng(inFile), nPix = img.width * img.height;
  const an = analyse(img.px, nPix), forms = buildForms(img, an);
  let best = null;
  for (const form of forms) {
    const cands = filterCandidates(form, img.width, img.height);
    for (const choice of form.filters) {
      let filtered;
      if (choice === 'brute') filtered = bruteFiltered(form, img.width, img.height);
      else filtered = cands[choice];
      const z = zlib.deflateSync(filtered, { level: 6, memLevel: 8 });
      const weight = z.length + form.overhead;
      if (best === null || weight < best.weight) best = { weight, form, filtered, choice, z6len: z.length };
    }
  }
  const n = best.filtered.length;
  const cfg = n <= 1048576 ? { chain: 8192, interior: { chain: 256, span: 100000, minLen: 8 } }
    : n <= 3145728 ? { chain: 8192, interior: { chain: 128, span: 100000, minLen: 8 } }
    : { chain: 4096, interior: { chain: 128, span: 100000, minLen: 12 } };
  const custom = zlibWrap(deflateOpt(best.filtered, { chain: cfg.chain, nice: 258, interior: cfg.interior }), best.filtered);
  const z9 = zlib.deflateSync(best.filtered, { level: 9 });
  const stream = custom.length <= z9.length ? custom : z9;
  const png = encodePng(img, best.form, stream);
  fs.mkdirSync(path.dirname(outFile), { recursive: true });
  fs.writeFileSync(outFile, png);
  return { distinct: an.distinct, grey: an.grey, opaque: an.opaque, key: an.key, ct: best.form.colourType, choice: best.choice, z6: best.z6len, custom: custom.length, z9: z9.length, bytes: png.length, overhead: best.form.overhead };
}

function main() {
  const inputDir = process.env.MAKEFUN_INPUT_DIR || '/input';
  const outputDir = process.env.MAKEFUN_OUTPUT_DIR || '/output';
  const ids = fs.readdirSync(inputDir).filter((d) => { try { return fs.statSync(path.join(inputDir, d)).isDirectory(); } catch { return false; } }).sort();
  for (const id of ids) {
    const inFile = path.join(inputDir, id, 'image.png'), outFile = path.join(outputDir, id, 'image.png');
    if (!fs.existsSync(inFile)) { console.log(id + ' SKIP no input'); continue; }
    const r = processImage(inFile, outFile);
    console.log(id + ' distinct=' + r.distinct + ' grey=' + r.grey + ' opaque=' + r.opaque + ' key=' + r.key + ' ct=' + r.ct + ' filter=' + r.choice + ' z6=' + r.z6 + ' custom=' + r.custom + ' z9=' + r.z9 + ' bytes=' + r.bytes);
  }
}
main();
