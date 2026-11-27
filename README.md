# Squeeze the Last Byte Out of Every Screenshot

[![make.fun · png-squeeze-01-run-20261127](https://make.fun/badge/png-squeeze-01-run-20261127.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)
[![rank](https://make.fun/badge/png-squeeze-01-run-20261127/sandytaztaz-hue/png-squeeze-01-run-20261127/rank.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)
[![reward](https://make.fun/badge/png-squeeze-01-run-20261127/sandytaztaz-hue/png-squeeze-01-run-20261127/reward.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)

Lossless PNG recompression for screenshots. Colour-form reduction (palette / grey / RGB / RGBA, chosen by actual pixels), per-row filter screen including brute force with a 32 KiB context dictionary, and a from-scratch optimal-parse DEFLATE: hash-chain lazy matching, interior-position match search, dynamic-programming parse with true bit costs, package-merge length-limited Huffman, block splitting, and a zlib level 9 fallback — the smaller stream wins. Pure Node 22 stdlib, deterministic, one run under 60 s.
