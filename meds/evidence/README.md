# Frozen benchmark evidence

Each subdirectory contains summary.json and raw results.jsonl from the final measured campaign for that implementation family. The evidence was copied byte-for-byte from the 2026-09-19 research campaign; object files, executables, source checkout caches, diagnostic stderr, and local absolute-path build metadata are excluded from the public package.

The legacy-hybrid campaign compares the corrected published AVX2 baseline to the hybrid candidate. legacy-packed-control compares the same corrected baseline to a packed-only control. rectangular, minimeds, and official compare distinct pinned baselines and must not be pooled into a single speedup. rectangular-arithmetic-only isolates arithmetic without inverse cancellation.

Timing ratios in README.md are baseline median divided by candidate median. Benchmark-specific trial counts and checks are in summary.json and results.jsonl. The superseded pre-fix legacy timing campaign is intentionally omitted. The C sources and harnesses shipped in implementations let readers rerun the comparisons on their own supported machines; new measurements may differ.
