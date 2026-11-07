# Benchmark report

The measurements compare complete in-memory recognition and reconstruction pipelines. All 11 cases agreed, including the two accepted published functions and the published negative example. No SageMath runtime was measured.

## Reproduce

```console
python benchmarks/run.py --repeats 5 --max-m 10
```

To reproduce the optional external-library comparison, install `sympy==1.14.0` into the active environment first. An existing dependency directory can instead be supplied explicitly:

```console
python benchmarks/run.py --repeats 5 --max-m 10 --sympy-path PATH_TO_DEPENDENCIES
```

The recorded run used SymPy 1.14.0 loaded from an existing dependency directory, with the same five-repeat/max-m=10 options. Dependency paths are intentionally omitted from results.

## Methods

- **Tool:** packed implementation of the bordered-rank/normalization theorem, full exact design checks, reconstruction, and independent spectrum/incidence/linear-structure self-check.
- **TSDP reference:** independent Python implementation of exact design validation, normalized pair-closure TSDP decision, coordinate reconstruction, and exact spectrum/incidence/linear-structure verification. It checks unordered pairs, not a deliberately slow literal triple enumeration.
- **Rank ablation:** the identical reference pipeline with only the TSDP decision replaced by packed GF(2) rank saturation. This isolates that decision change from other implementation improvements.
- **SymPy reference:** the same reference pipeline using actual `DomainMatrix` over `GF(2)` for normalized rank, including matrix conversion. This is a real library call but is not a Sage or M4RI comparison.

Input JSON parsing and fixture generation are outside every timed scope. The phase-only timings additionally exclude validation, normalization, reconstruction and certificate checking. One warmup precedes five timed runs, with garbage collection before each sample; the table reports medians. Concurrent machine load was not controlled, so small differences near 1.0x are inconclusive.

## End-to-end medians

| Case | Shape | Tool ms | TSDP ms | Rank ablation ms | SymPy ms | TSDP/tool | TSDP/rank ablation |
|---|---:|---:|---:|---:|---:|---:|---:|
| published-example-1 | 64 × 64 | 1.400 | 1.929 | 1.800 | 12.227 | 1.38x | 1.07x |
| published-example-2 | 16 × 32 | 0.314 | 0.320 | 0.296 | 1.489 | 1.02x | 1.08x |
| published-example-2-permuted | 16 × 32 | 0.306 | 0.321 | 0.295 | 1.572 | 1.05x | 1.09x |
| quadratic-family-m4 | 16 × 16 | 0.227 | 0.193 | 0.186 | 0.797 | 0.85x | 1.04x |
| cubic-mm-family-m6 | 64 × 64 | 1.386 | 1.924 | 1.791 | 12.213 | 1.39x | 1.07x |
| plateaued-stabilization-m7 | 64 × 128 | 2.336 | 3.857 | 3.331 | 25.276 | 1.65x | 1.16x |
| proof-counterexample-64x128 | 64 × 128 | 1.934 | 1.920 | 1.969 | 22.982 | 0.99x | 0.98x |
| published-example-4-negative | 256 × 256 | 16.685 | 17.759 | 18.009 | 303.637 | 1.06x | 0.99x |
| stress-quadratic-family-m8 | 256 × 256 | 17.700 | 30.072 | 27.185 | 237.295 | 1.70x | 1.11x |
| stress-plateaued-stabilization-m9 | 256 × 512 | 34.019 | 69.871 | 53.120 | 486.413 | 2.05x | 1.32x |
| stress-quadratic-family-m10 | 1024 × 1024 | 313.748 | 578.697 | 508.378 | 4614.785 | 1.84x | 1.14x |

## Decision-only medians

These two columns start with the identical precomputed normalized column vectors. They explain why a much larger decision-phase improvement can translate into a modest whole-pipeline improvement.

| Case | Packed rank ms | Normalized TSDP closure ms |
|---|---:|---:|
| published-example-1 | 0.0278 | 0.1607 |
| published-example-2 | 0.0120 | 0.0423 |
| published-example-2-permuted | 0.0118 | 0.0404 |
| quadratic-family-m4 | 0.0083 | 0.0162 |
| cubic-mm-family-m6 | 0.0257 | 0.1608 |
| plateaued-stabilization-m7 | 0.0517 | 0.6207 |
| proof-counterexample-64x128 | 0.0587 | 0.0337 |
| published-example-4-negative | 0.2895 | 0.0465 |
| stress-quadratic-family-m8 | 0.1137 | 2.7163 |
| stress-plateaued-stabilization-m9 | 0.2301 | 10.6707 |
| stress-quadratic-family-m10 | 0.7804 | 78.5665 |

## Interpretation

The 1024 × 1024 generated stress instance took about 314 ms in the tool and 579 ms in the TSDP reference (1.84x). On that case, switching only the reference decision rule gave 1.14x; the rest of the full implementation difference includes packing and certificate verification. The generated 256 × 512 instance gave 2.05x tool/reference and 1.32x for the decision-rule ablation. The tool was slower on the smallest 16 × 16 valid fixture. Both methods can reject a negative input early, so rank decision is not uniformly faster on rejected instances.

These are measured comparisons against the implementations described above, not a state-of-the-art claim. A compiled Sage/M4RI backend could be faster; it was not available for a measured comparison in this run. The two exact published positive examples, published negative Example 4, and generated family stress cases retain distinct provenance labels in the JSON.

## Environment

CPython 3.13.5, Windows AMD64, 16 logical CPUs, processor identifier `Intel64 Family 6 Model 165 Stepping 5, GenuineIntel`, SymPy 1.14.0.

All raw timing samples and algorithm/fixture hashes are in `results.json`.
