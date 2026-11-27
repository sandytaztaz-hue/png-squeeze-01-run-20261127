// main.ts — lossless PNG recompression for screenshots (make.fun png-squeeze).
// Reads /input/<id>/image.png for each instance, writes /output/<id>/image.png.
//
// The pipeline, per image: decode to RGBA; pick the colour form the pixels
// allow (palette with two orderings, grey, grey+alpha, RGB, RGB with a tRNS
// key, RGBA); screen the forms with zlib level 6 over minimum-sum filtered
// rows; then refine the winner: an optimal-parse DEFLATE (see deflate.mjs)
// gives a true cost model, the per-row filters are re-chosen by that model,
// and the parse is refined again. The smaller of the result and a zlib level 9
// stream wins. Pure Node standard library, deterministic: fixed work budgets
// only, no clock, no randomness, no network.

import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { deflateSync, inflateSync } from 'node:zlib';
import { pathToFileURL } from 'node:url';
import { deflateZlib, deflateZlibSplit } from './deflate.mjs';

const WIDTH = 1280;
const HEIGHT = 720;

const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();

/** CRC-32 (PNG's) of bytes[start, end). */
function crc32(bytes, start = 0, end = bytes.length) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

/** A PNG file of `chunks`, each [type, data]. */
function pngOf(chunks) {
  let size = 8;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set([137, 80, 78, 71, 13, 10, 26, 10], 0);
  let at = 8;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    for (let i = 0; i < 4; i++) out[at + 4 + i] = type.charCodeAt(i);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}

/** IHDR's data: width, height, bit depth 8, the colour type, no interlace. */
function ihdrOf(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}

/** The Paeth predictor of PNG's filter 4. */
function paeth(a, b, c) {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}

/**
 * Row `cur` (stride samples, bpp a pixel, `prev` the row above or null)
 * filtered by `type` into out[0, stride).
 */
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) { out.set(cur); return; }
  if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paeth(a, b, c);
    }
  }
}

/** The sum of a filtered row's bytes read as signed (-128 to 127), absolute. */
function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

const CHANNELS = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };

/**
 * Decode a PNG to RGBA (4 bytes a pixel, rows top to bottom). Reads the
 * colour types the contest accepts; anything else throws.
 */
export function decodePng(bytes) {
  if (bytes.length < 8) throw new Error('not a PNG');
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let width = 0, height = 0, colourType = 6;
  let palette = null, trns = null;
  const idat = [];
  while (at + 12 <= bytes.length) {
    const len = view.getUint32(at);
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (type === 'IHDR') {
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      width = dv.getUint32(0); height = dv.getUint32(4);
      if (data[8] !== 8 || data[12] !== 0) throw new Error('unsupported PNG');
      colourType = data[9];
    } else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
  }
  const bpp = CHANNELS[colourType];
  const stride = width * bpp;
  const raw = inflateSync(Buffer.concat(idat));
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    } else {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
        samples[o + i] = raw[src + i] + paeth(a, b, c);
      }
    }
  }
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    const entries = palette.length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) {
      lut[e * 4] = palette[e * 3];
      lut[e * 4 + 1] = palette[e * 3 + 1];
      lut[e * 4 + 2] = palette[e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      rgba[d] = lut[e * 4]; rgba[d + 1] = lut[e * 4 + 1]; rgba[d + 2] = lut[e * 4 + 2]; rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return { rgba, width, height };
}

/**
 * What the image holds: whether every pixel is opaque, whether every pixel is
 * grey, and its colours (at most 256) with their counts. A colour's key is
 * built from its bytes, so it is the same on every platform.
 */
export function analyse(rgba) {
  const n = rgba.length >>> 2;
  let opaque = true;
  let grey = true;
  const colours = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    const r = rgba[d], g = rgba[d + 1], b = rgba[d + 2], a = rgba[d + 3];
    if (a !== 255) opaque = false;
    if (r !== g || r !== b) grey = false;
    if (!many) {
      const key = (r << 24) | (g << 16) | (b << 8) | a;
      const c = colours.get(key);
      if (c === undefined) {
        if (colours.size === 256) many = true;
        else colours.set(key, { r, g, b, a, key, count: 1 });
      } else c.count++;
    }
  }
  return { opaque, grey, colours: many ? null : [...colours.values()] };
}

/**
 * The one fully transparent value (grey or RGB) the image may key by tRNS
 * instead of an alpha channel: every pixel is opaque or that exact value at
 * alpha 0, and no opaque pixel holds that value. Null when there is none.
 */
function transparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}

/** The image's samples in colour type `ct` (0, 2, 4 or 6) from its RGBA. */
function samplesOf(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) { out[s] = rgba[d]; out[s + 1] = rgba[d + 3]; }
    else { out[s] = rgba[d]; out[s + 1] = rgba[d + 1]; out[s + 2] = rgba[d + 2]; }
  }
  return out;
}

/** A palette's entries in trial order: transparent ones first (by alpha), then by `order`. */
function paletteOrder(colours, order) {
  const lum = (c) => 299 * c.r + 587 * c.g + 114 * c.b;
  return [...colours].sort((x, y) => {
    const ta = x.a === 255 ? 1 : 0;
    const tb = y.a === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.a !== y.a) return x.a - y.a;
    if (order === 'luminance') return lum(x) - lum(y) || x.key - y.key;
    return y.count - x.count || x.key - y.key;
  });
}

/** The palette form: { plte, trns, indices }. */
function paletteForm(rgba, colours, order) {
  const entries = paletteOrder(colours, order);
  const index = new Map(entries.map((c, i) => [c.key, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.r;
    plte[i * 3 + 1] = c.g;
    plte[i * 3 + 2] = c.b;
    if (c.a !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.a);
  const n = rgba.length >>> 2;
  const indices = new Uint8Array(n);
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    indices[i] = index.get((rgba[d] << 24) | (rgba[d + 1] << 16) | (rgba[d + 2] << 8) | rgba[d + 3]);
  }
  return { plte, trns, indices };
}

/** The bytes a form's PLTE and tRNS chunks take in its file. */
const chunkBytes = (form) => (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);

/**
 * The forms the image can be written in, each { colourType, bpp, samples,
 * plte, trns }: a palette (two orderings) when it holds at most 256 colours,
 * then a channel form when it is grey or holds more colours.
 */
export function formsOf(rgba) {
  const { opaque, grey, colours } = analyse(rgba);
  const forms = [];
  if (colours !== null) {
    for (const order of ['count', 'luminance']) {
      const p = paletteForm(rgba, colours, order);
      forms.push({ colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns });
    }
    if (!grey) return forms;
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct;
  let trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct];
  forms.push({ colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns });
  return forms;
}

/**
 * The five filtered variants of every row, in one buffer: variants[(t * height
 * + y) * rowBytes] is the filter byte t, followed by the row filtered by t.
 * Building it once lets the filter choice be re-run under several cost models
 * without re-filtering.
 */
export function buildFilterCache(samples, width, height, bpp) {
  const stride = width * bpp;
  const rowBytes = stride + 1;
  const variants = new Uint8Array(5 * height * rowBytes);
  const cur = new Uint8Array(stride);
  const prev = new Uint8Array(stride);
  for (let y = 0; y < height; y++) {
    const row = samples.subarray(y * stride, (y + 1) * stride);
    const up = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    for (let t = 0; t < 5; t++) {
      const at = (t * height + y) * rowBytes;
      variants[at] = t;
      filterRow(t, row, up, bpp, variants.subarray(at + 1, at + rowBytes));
    }
  }
  return { variants, rowBytes, stride, height };
}

/** The minimum-sum filtered stream of a form, from its filter cache. */
export function minsumStream(cache) {
  const { variants, rowBytes, stride, height } = cache;
  const out = new Uint8Array(height * rowBytes);
  const sums = new Float64Array(5);
  for (let y = 0; y < height; y++) {
    let bestT = 0, bestS = Infinity;
    for (let t = 0; t < 5; t++) {
      const at = (t * height + y) * rowBytes + 1;
      let s = 0;
      for (let i = 0; i < stride; i++) { const v = variants[at + i]; s += v < 128 ? v : 256 - v; }
      if (s < bestS) { bestS = s; bestT = t; }
    }
    const src = (bestT * height + y) * rowBytes;
    out.set(variants.subarray(src, src + rowBytes), y * rowBytes);
  }
  return out;
}

/** The stream of one fixed filter for every row, from a filter cache. */
export function fixedStream(cache, t) {
  const { variants, rowBytes, height } = cache;
  const out = new Uint8Array(height * rowBytes);
  for (let y = 0; y < height; y++) {
    const src = (t * height + y) * rowBytes;
    out.set(variants.subarray(src, src + rowBytes), y * rowBytes);
  }
  return out;
}

/** Fixed work budgets by filtered-stream size: no clock, so the run is deterministic. */
export function settingsFor(n) {
  if (n <= 1500000) return { cap: 1024, iters: 3, mode: 'all', top2gap: 1.015 };
  return { cap: 256, iters: 3, mode: 'good', top2gap: 0 };
}

/**
 * How many DEFLATE blocks to split `stream` into: zlib level 6 is run on the
 * whole stream and on eight equal parts, and eight parts win only when their
 * total is smaller. The proxy predicts the optimal-parse split decision on
 * every practice image, and costs about one extra level-6 pass.
 */
export function splitParts(stream) {
  const whole = deflateSync(stream, { level: 6, memLevel: 8 }).length;
  const chunk = Math.ceil(stream.length / 8);
  let split = 0;
  for (let p = 0; p < 8; p++) {
    split += deflateSync(stream.subarray(p * chunk, Math.min(stream.length, (p + 1) * chunk)), { level: 6, memLevel: 8 }).length;
  }
  return split < whole ? 8 : 1;
}

/**
 * Refine one form: three filterings (every row unfiltered, brute force, and
 * minimum-sum) are screened by zlib level 6, and the best two are written by
 * the optimal-parse DEFLATE, each split into blocks when the proxy says the
 * stream's statistics change along its length; the smaller wins, against a
 * zlib level 9 stream of the same filtered data as fallback.
 */
export function refine(form, cache, minsum, width, height) {
  const n = height * (width * form.bpp + 1);
  const s = settingsFor(n);
  const cands = [
    fixedStream(cache, 0),
    bruteStream(cache),
    minsum,
  ].map((stream) => ({ stream, z6: deflateSync(stream, { level: 6, memLevel: 8 }).length, parts: undefined }));
  cands.sort((a, b) => a.z6 - b.z6);
  // The split decision is only computed for a candidate that is actually
  // written, so the third candidate costs just its level-6 screen.
  const partsOf = (cand) => {
    if (cand.parts === undefined) cand.parts = splitParts(cand.stream);
    return cand.parts;
  };
  const write = (cand) => {
    const parts = partsOf(cand);
    const r = parts === 1
      ? deflateZlib(cand.stream, { chainCap: s.cap, iterations: s.iters, mode: s.mode })
      : deflateZlibSplit(cand.stream, parts, { chainCap: s.cap, iterations: s.iters, mode: s.mode });
    return { zlib: r.zlib, bytes: r.bytes };
  };
  let best = write(cands[0]);
  let bestStream = cands[0].stream;
  // A second candidate is written when it can plausibly win. On the small
  // streams, whenever it is close by the level-6 screen. On the large
  // streams, when the two candidates are close and disagree about splitting,
  // since the split gain differs per stream and the screen's ranking can flip
  // there; the screen's ranking otherwise already matches the optimal-parse
  // ranking, so the second pass buys nothing.
  const closeSmall = s.top2gap > 0 && cands[1].z6 < cands[0].z6 * s.top2gap;
  const splitDiffers = s.top2gap === 0 && cands[1].z6 < cands[0].z6 * 1.05
    ? partsOf(cands[0]) !== partsOf(cands[1])
    : false;
  if (closeSmall || splitDiffers) {
    const second = write(cands[1]);
    if (second.bytes < best.bytes) { best = second; bestStream = cands[1].stream; }
  }
  const z9 = deflateSync(bestStream, { level: 9, memLevel: 9 });
  if (z9.length < best.bytes) return z9;
  return best.zlib;
}

/** Screen one form: its minimum-sum stream, weighed by zlib level 6 plus its chunk overhead. */
export function screenForm(form, width, height) {
  const cache = buildFilterCache(form.samples, width, height, form.bpp);
  const stream = minsumStream(cache);
  const z = deflateSync(stream, { level: 6, memLevel: 8 });
  return { cache, stream, score: z.length + chunkBytes(form) };
}

/** The answer PNG for one image. */
export function processImage(rgba, width, height) {
  const forms = formsOf(rgba);
  let best = null;
  for (const form of forms) {
    const s = screenForm(form, width, height);
    if (best === null || s.score < best.score) best = { form, cache: s.cache, stream: s.stream, score: s.score };
  }
  const zlib = refine(best.form, best.cache, best.stream, width, height);  const chunks = [['IHDR', ihdrOf(width, height, best.form.colourType)]];
  if (best.form.plte !== null) chunks.push(['PLTE', best.form.plte]);
  if (best.form.trns !== null) chunks.push(['tRNS', best.form.trns]);
  chunks.push(['IDAT', zlib]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngOf(chunks);
}

function main() {
  const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
  const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
  for (const id of readdirSync(I).sort()) {
    const { rgba, width, height } = decodePng(readFileSync(join(I, id, 'image.png')));
    const png = processImage(rgba, width, height);
    mkdirSync(join(O, id), { recursive: true });
    writeFileSync(join(O, id, 'image.png'), png);
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();

/**
 * The brute-force filtered stream: each row is tried under all five filters,
 * each compressed by zlib at level 4 after the 32 KiB written before it, and
 * the smallest is kept. This is the filter choice that matters most for
 * rich, alpha and grey images, where a filter's value is in the matches it
 * creates, not in its byte distribution.
 */
export function bruteStream(cache) {
  const { variants, rowBytes, height } = cache;
  const out = new Uint8Array(height * rowBytes);
  const CONTEXT = 32768;
  for (let y = 0; y < height; y++) {
    const at = y * rowBytes;
    const before = out.subarray(Math.max(0, at - CONTEXT), at);
    let bestT = 0, bestLen = Infinity;
    for (let t = 0; t < 5; t++) {
      const src = (t * height + y) * rowBytes;
      const trial = variants.subarray(src, src + rowBytes);
      const len = deflateSync(trial, before.length === 0
        ? { level: 4, memLevel: 9 }
        : { level: 4, memLevel: 9, dictionary: before }).length;
      if (len < bestLen) { bestLen = len; bestT = t; }
    }
    const src = (bestT * height + y) * rowBytes;
    out.set(variants.subarray(src, src + rowBytes), at);
  }
  return out;
}
