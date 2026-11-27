# Squeeze the Last Byte Out of Every Screenshot

[![make.fun · png-squeeze-01-run-20261127](https://make.fun/badge/png-squeeze-01-run-20261127.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)
[![rank](https://make.fun/badge/png-squeeze-01-run-20261127/sandytaztaz-hue/png-squeeze-01-run-20261127/rank.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)
[![reward](https://make.fun/badge/png-squeeze-01-run-20261127/sandytaztaz-hue/png-squeeze-01-run-20261127/reward.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)

Lossless PNG recompression for screenshots. Colour-form reduction (palette / grey / RGB / RGBA, chosen by actual pixels), per-row filter screen including brute force with a 32 KiB context dictionary, and a from-scratch optimal-parse DEFLATE: two-table hash-chain matching, interior-position match search, dynamic-programming parse with true bit costs and two-phase range-top truncation, package-merge length-limited Huffman, adaptive block splitting, and a zlib level 9 fallback — the smaller stream wins. Pure Node 22 stdlib, deterministic, one run under 60 s.

## Run it

```sh
node main.ts
```

Reads `$MAKEFUN_INPUT_DIR/<id>/image.png` (default `/input`), writes `$MAKEFUN_OUTPUT_DIR/<id>/image.png` (default `/output`), creating each output directory.
