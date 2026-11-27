// main.ts — PNG squeeze entry (round 3, fresh rewrite).
// Node 22 runs this directly (erasable syntax only; this file is plain JS).
// Reads /input/<id>/image.png for i001..i008, writes /output/<id>/image.png.
// Pure Node standard library. Deterministic: fixed work budgets only.
//
// Pipeline per image:
//   decode -> analyse (grey / opaque / colour count / transparent key)
//   -> colour forms (palette by count, palette by luminance, grey/RGB/RGBA
//      with a tRNS key where one exists) -> per-form filter choices
//      (filter 0, minimum-sum, brute force per row at zlib level 4)
//      -> screen every choice with zlib level 6 -> run the from-scratch
//      optimal-parse DEFLATE (deflate.mjs) on the best candidate (and the
//      second when the ranking can flip) -> zlib level 9 fallback -> the
//      smallest total file wins.

import { readFileSync, writeFileSync, mkdirSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { inflateSync, deflateSync, constants } from 'node:zlib';
import { deflateZlib } from './deflate.mjs';


// ---- PNG codec (reader + writer) --------------------------------------------

const SIGNATURE = [137, 80, 78, 71, 13, 10, 26, 10];
const CHANNELS = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };

const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();

function crc32(bytes, start = 0, end = bytes.length) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

function paeth(a, b, c) {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}

// Decode a PNG into RGBA bytes. Supports colour types 0, 2, 3, 4, 6.
function decodePng(bytes) {
  for (let i = 0; i < 8; i++) if (bytes[i] !== SIGNATURE[i]) throw new Error('bad PNG signature');
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let width = 0, height = 0, colourType = 6;
  let palette = null, trns = null;
  const idat = [];
  while (at < bytes.length) {
    const len = view.getUint32(at);
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    const data = bytes.subarray(at + 8, at + 8 + len);
    if (type === 'IHDR') {
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      width = dv.getUint32(0);
      height = dv.getUint32(4);
      if (data[8] !== 8) throw new Error('bit depth is not 8');
      colourType = data[9];
      if (data[12] !== 0) throw new Error('interlaced');
    } else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
    at += 12 + len;
  }
  const bpp = CHANNELS[colourType];
  const stride = width * bpp;
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat));
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
      rgba[d] = samples[s];
      rgba[d + 1] = samples[s + 1];
      rgba[d + 2] = samples[s + 2];
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
      rgba[d] = lut[e * 4];
      rgba[d + 1] = lut[e * 4 + 1];
      rgba[d + 2] = lut[e * 4 + 2];
      rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return { rgba, width, height };
}

function pngOf(chunks) {
  let size = 8;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set(SIGNATURE, 0);
  let at = 8;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    for (let k = 0; k < 4; k++) out[at + 4 + k] = type.charCodeAt(k);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}

function ihdrOf(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}

// ---- Image analysis ----------------------------------------------------------

function analyse(rgba) {
  const n = rgba.length >>> 2;
  const u32 = new Uint32Array(rgba.buffer, rgba.byteOffset, n);
  let opaque = true;
  let grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const c = u32[i];
      const k = counts.get(c);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(c, 1);
      } else counts.set(c, k + 1);
    }
  }
  const colours = many ? null : [...counts.keys()].map((c) => {
    const b = new Uint8Array(Uint32Array.of(c).buffer);
    return { rgba: [b[0], b[1], b[2], b[3]], word: c, count: counts.get(c) };
  });
  return { opaque, grey, colours };
}

// The one fully transparent value the image may key by tRNS: every
// non-opaque pixel is that exact value at alpha 0, and no opaque pixel
// shares the value. Null when there is none.
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

function samplesOf(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 3];
    } else {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 1];
      out[s + 2] = rgba[d + 2];
    }
  }
  return out;
}

// Palette entries: transparent ones first (by alpha), then by order.
function paletteForm(rgba, colours, order) {
  const lum = (c) => 299 * c.rgba[0] + 587 * c.rgba[1] + 114 * c.rgba[2];
  const entries = [...colours].sort((x, y) => {
    const ta = x.rgba[3] === 255 ? 1 : 0;
    const tb = y.rgba[3] === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.rgba[3] !== y.rgba[3]) return x.rgba[3] - y.rgba[3];
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.rgba[0];
    plte[i * 3 + 1] = c.rgba[1];
    plte[i * 3 + 2] = c.rgba[2];
    if (c.rgba[3] !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.rgba[3]);
  const n = rgba.length >>> 2;
  const u32 = new Uint32Array(rgba.buffer, rgba.byteOffset, n);
  const indices = new Uint8Array(n);
  for (let i = 0; i < n; i++) indices[i] = index.get(u32[i]);
  return { plte, trns, indices };
}

// All colour forms for an image, each with the filter choices to screen.
function formsOf(rgba) {
  const { opaque, grey, colours } = analyse(rgba);
  const forms = [];
  if (colours !== null) {
    for (const order of ['count', 'luminance']) {
      const p = paletteForm(rgba, colours, order);
      forms.push({
        colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns,
        filters: order === 'count' ? [0] : [0, 'minsum', 'brute'],
      });
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
  forms.push({
    colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns,
    // Screen only the three filterings that ever win: unfiltered,
    // minimum-sum and brute force. The fixed filters and the pairs
    // heuristic never won a screen in practice and cost full passes.
    filters: [0, 'minsum', 'brute'],
  });
  return forms;
}

// ---- Filtering ----------------------------------------------------------------

function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) { out.set(cur); return; }
  if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    if (prev === null) { out.set(cur); return; }
    for (let i = 0; i < n; i++) out[i] = cur[i] - prev[i];
  } else if (type === 3) {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      out[i] = cur[i] - ((a + b) >> 1);
    }
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paeth(a, b, c);
    }
  }
}

function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

function pairsOf(row, seen, stamp) {
  let n = 0;
  for (let i = 1; i < row.length; i++) {
    const pair = (row[i - 1] << 8) | row[i];
    if (seen[pair] !== stamp) {
      seen[pair] = stamp;
      n++;
    }
  }
  return n;
}

const BRUTE_CONTEXT = 32768;
const BRUTE_LEVEL = 4;

// Build the minimum-sum and brute-force filterings in ONE pass: both need
// all five trial rows per row, so computing them twice is pure waste.
function filteredPair(samples, width, height, bpp) {
  const stride = width * bpp;
  const rawMin = new Uint8Array(height * (stride + 1));
  const rawBrute = new Uint8Array(height * (stride + 1));
  const trial = Array.from({ length: 5 }, () => new Uint8Array(stride));
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    for (let t = 0; t < 5; t++) filterRow(t, cur, prev, bpp, trial[t]);
    let typeMin = 0;
    let bestMin = Infinity;
    for (let t = 0; t < 5; t++) {
      const s = signedSum(trial[t]);
      if (s < bestMin) {
        bestMin = s;
        typeMin = t;
      }
    }
    const beforeBrute = rawBrute.subarray(Math.max(0, at - BRUTE_CONTEXT), at);
    let typeBrute = 0;
    let bestBrute = Infinity;
    for (let t = 0; t < 5; t++) {
      const cost = deflateSync(trial[t], beforeBrute.length === 0 ? { level: BRUTE_LEVEL, memLevel: 9 } : { level: BRUTE_LEVEL, memLevel: 9, dictionary: beforeBrute }).length;
      if (cost < bestBrute) {
        bestBrute = cost;
        typeBrute = t;
      }
    }
    rawMin[at] = typeMin;
    rawMin.set(trial[typeMin], at + 1);
    rawBrute[at] = typeBrute;
    rawBrute.set(trial[typeBrute], at + 1);
  }
  return { minsum: rawMin, brute: rawBrute };
}

function filtered(samples, width, height, bpp, choice) {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));
  const trial = Array.from({ length: 5 }, () => new Uint8Array(stride));
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - BRUTE_CONTEXT), at);
    let type = 0;
    let best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t]);
      let cost;
      if (choice === 'minsum') cost = signedSum(trial[t]);
      else if (choice === 'pairs') cost = pairsOf(trial[t], seen, ++stamp);
      else cost = deflateSync(trial[t], before.length === 0 ? { level: BRUTE_LEVEL, memLevel: 9 } : { level: BRUTE_LEVEL, memLevel: 9, dictionary: before }).length;
      if (cost < best) {
        best = cost;
        type = t;
      }
    }
    raw[at] = type;
    raw.set(trial[type], at + 1);
  }
  return raw;
}

// ---- Per-image driver -----------------------------------------------------------

const SCREEN = { level: 6, memLevel: 8, strategy: constants.Z_DEFAULT_STRATEGY };

// Chain cap by the screen size (zlib-6 bytes): a byte saved on a small
// (already tiny) stream is worth far more points than one on a big stream,
// so the small streams get the deepest search and the big ones a shallow
// one. Screen size tracks the scale size, which sets the points-per-byte.
function chainCapFor(rawLen, screenBytes) {
  void rawLen;
  if (screenBytes <= 30000) return 1280;
  if (screenBytes <= 60000) return 1024;
  if (screenBytes <= 120000) return 256;
  return 128;
}

function processImage(rgba, width, height) {
  const forms = formsOf(rgba);
  const candidates = [];
  for (const form of forms) {
    const chunks = (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);
    const raws = {};
    for (const choice of form.filters) {
      if (choice === 'minsum' || choice === 'brute') {
        if (raws.pair === undefined) raws.pair = filteredPair(form.samples, width, height, form.bpp);
        raws[choice] = raws.pair[choice];
      } else {
        raws[choice] = filtered(form.samples, width, height, form.bpp, choice);
      }
    }
    for (const choice of form.filters) {
      const data = raws[choice];
      const z6 = deflateSync(data, SCREEN);
      candidates.push({ form, choice, data, z6len: z6.length + chunks });
    }
  }
  candidates.sort((a, b) => a.z6len - b.z6len);
  // Deflate only the screen winner with the real encoder. A second
  // candidate never flipped a ranking in practice (checked on the close
  // calls) and costs a full deflate; the screen gap is reliable here.
  const toDeflate = [candidates[0]];
  let best = null;
  for (const cand of toDeflate) {
    const cap = chainCapFor(cand.data.length, cand.z6len);
    // The largest stream benefits from more blocks (finer Huffman
    // adaptation); smaller streams pay more header than they gain.
    const blocks = cand.z6len > 150000 ? 16 : 8;
    const mine = deflateZlib(cand.data, { chainCap: cap, blocks, iterations: 5 });
    const z9 = deflateSync(cand.data, { level: 9, memLevel: 9 });
    const idat = mine.length <= z9.length ? mine : z9;
    const chunks = (cand.form.plte === null ? 0 : 12 + cand.form.plte.length) + (cand.form.trns === null ? 0 : 12 + cand.form.trns.length);
    const total = 8 + 25 + chunks + 12 + idat.length + 12;
    if (best === null || total < best.total) {
      best = { form: cand.form, idat, total, choice: cand.choice, mineLen: mine.length, z9Len: z9.length };
    }
  }
  const chunks = [['IHDR', ihdrOf(width, height, best.form.colourType)]];
  if (best.form.plte !== null) chunks.push(['PLTE', best.form.plte]);
  if (best.form.trns !== null) chunks.push(['tRNS', best.form.trns]);
  chunks.push(['IDAT', best.idat]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return { png: pngOf(chunks), total: best.total, choice: best.choice, colourType: best.form.colourType };
}

// ---- Main ----------------------------------------------------------------------

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

for (const id of readdirSync(I).sort()) {
  const { rgba, width, height } = decodePng(new Uint8Array(readFileSync(join(I, id, 'image.png'))));
  const { png, total, choice, colourType } = processImage(rgba, width, height);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'image.png'), png);
}
