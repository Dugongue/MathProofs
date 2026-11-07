# Full-pipeline benchmark against actual software

All primary measurements use the same preparsed integer incidence matrices and include input conversion, recognition, full coordinate/function reconstruction and exact realization checks. Runtime startup and corpus JSON parsing are excluded; fresh command-line wall times are reported separately. All timing runs were serialized after extraction and compilation completed, with one warmup and five measured repetitions. Tables report medians.

## Actual backends and scope

- **Design Boolean 0.2 native:** original portable C++17 implementation plus the Python API. Complete certificate-first validation; no prevalidated-design promise.
- **Native explicit ablation:** same native implementation plus explicit block and point-pair checks; isolates the certificate-first validation improvement.
- **SageMath 9.3 / bundled M4RI 20200115:** actual Sage GF(2) matrices, pivots, basis-coordinate solving, BooleanFunction Walsh transform, matrix incidence check and affine rank. Its strongest spectral mode uses the same certificate-first proof as our implementation. Validated flat-byte matrix construction was selected after checking three input routes. This is an archived Windows runtime, not a claim about current Sage releases.
- **M4RI 20260122 reference:** actual upstream arithmetic at pinned commit 397a70fcffeb17b0c25c0aa40231145fc392317f, composed with the independent Python reconstruction pipeline. This is a full adapter, not a claim to beat M4RI rank arithmetic in isolation.
- **GAP 4.16.1 / DESIGN 1.8.2:** actual BlockDesign, simplicity and PairwiseBalancedLambda validation, compressed GF(2) semi-echelon coordinates, reconstruction and exact spectral/incidence checks. The adapter is original; DESIGN is not claimed to supply a built-in plateaued reconstructor.

## Full-pipeline medians in milliseconds

| Case | Shape | Native certificate | Native explicit | Sage spectral | M4RI reference | GAP DESIGN | Sage/native |
|---|---:|---:|---:|---:|---:|---:|---:|
| published-example-1 | 64 × 64 | 0.245 | 0.258 | 2.483 | 1.873 | 15.497 | 10.13× |
| published-example-2 | 16 × 32 | 0.195 | 0.177 | 0.885 | 0.339 | 0.943 | 4.54× |
| published-example-2-permuted | 16 × 32 | 0.157 | 0.173 | 0.882 | 0.336 | 0.947 | 5.62× |
| quadratic-family-m4 | 16 × 16 | 0.142 | 0.139 | 0.725 | 0.215 | 0.587 | 5.10× |
| cubic-mm-family-m6 | 64 × 64 | 0.270 | 0.255 | 2.442 | 1.858 | 15.594 | 9.06× |
| plateaued-stabilization-m7 | 64 × 128 | 0.324 | 0.368 | 4.081 | 3.359 | 30.353 | 12.61× |
| proof-counterexample-64x128 | 64 × 128 | 0.227 | 0.240 | 3.094 | 2.003 | 28.440 | 13.65× |
| published-example-4-negative | 256 × 256 | 0.775 | 1.107 | 25.580 | 17.505 | 1146.998 | 33.01× |
| stress-quadratic-family-m8 | 256 × 256 | 1.035 | 1.378 | 27.330 | 27.037 | 1136.730 | 26.40× |
| stress-plateaued-stabilization-m9 | 256 × 512 | 1.670 | 2.312 | 50.472 | 52.815 | 2216.348 | 30.22× |
| stress-quadratic-family-m10 | 1024 × 1024 | 11.273 | 31.717 | 366.127 | 498.378 | Not completed | 32.48× |

The native tool is faster than every completed full-pipeline Sage, GAP and M4RI-adapter case in this corpus. This is a measured statement for these versions and adapters, not a state-of-the-art or all-input speed guarantee. On 1024 × 1024, native certificate-first is about 11.3 ms versus Sage spectral 366 ms; explicit native validation is about 31.7 ms. The latter comparison isolates a roughly 2.8× benefit from changing validation strategy in the same native pipeline.

## Actual Sage IncidenceStructure validation

This mode additionally calls Sage IncidenceStructure.is_t_design on the eight shipped fixtures; it also reconstructs and checks the function. It is distinct from the stronger spectral-only mode above.

| Case | Sage incidence full pipeline ms |
|---|---:|
| published-example-1 | 7.742 |
| published-example-2 | 1.147 |
| published-example-2-permuted | 1.168 |
| quadratic-family-m4 | 0.911 |
| cubic-mm-family-m6 | 7.618 |
| plateaued-stabilization-m7 | 14.662 |
| proof-counterexample-64x128 | 13.685 |
| published-example-4-negative | 439.878 |

## GAP timeout and checkpoints

The initial 11-case, five-repeat GAP job exceeded its 600-second total limit. No missing-case median or per-call lower bound is inferred from that timeout. A checkpointed 10-case run, through 256 × 512, completed with five samples per case. The 1024 × 1024 GAP entry is deliberately unreported. The general DESIGN pair-counting routine is expensive on dense designs; this report does not claim the adapter is the fastest possible GAP program.

gap_streaming.py preserves independently checked completed cases on timeout, prints progress and supports bounded --cases and contract-checked --resume. The mathematical GAP pipeline is unchanged by checkpointing.

## Fresh CLI wall time

Each sample launches a fresh installed interpreter from another folder, reads the same JSON file, recognizes/reconstructs/verifies, and emits complete JSON. Thus process startup, file parsing and serialization are included. One warmup and five timed processes were used per version/case.

| Case | Python 0.1 CLI ms | Native 0.2 CLI ms | Ratio |
|---|---:|---:|---:|
| plateaued-stabilization-m5 | 114.654 | 124.534 | 0.92× |
| quadratic-family-m8 | 137.789 | 126.382 | 1.09× |
| quadratic-family-m10 | 500.495 | 194.826 | 2.57× |

Small CLI calls are dominated by process startup and can be slower in version 0.2. Bulk users should call the Python API in a persistent process. The large CLI case improves by about 2.6×, which is a different measurement from the approximately 28× in-memory gain over our Python implementation.

## Reproduce

Build the source-tree native backend, then generate the shared corpus:

```console
python native/build.py
python benchmarks/compare_backends.py --corpus-only benchmarks/corpus.local.json
python benchmarks/compare_backends.py --m4ri-library PATH_TO_M4RI_WRAPPER --repeats 5
```

With Sage available:

```console
sage -python benchmarks/sage_m4ri_sage.py --corpus benchmarks/corpus.local.json --output benchmarks/sage-results.json --repeats 5 --validation spectral
```

Use sage_m4ri_windows.py for the extracted Sage 9.3 runtime. Run GAP separately with checkpointing:

```console
python benchmarks/gap_streaming.py --gap-root GAP_ROOT --runtime-bin CYGWIN_BIN --max-m 9 --repeats 5 --timeout 240 --output benchmarks/gap-results.json
```

For fresh CLI comparisons, supply two installed interpreters to compare_cli.py. Exact runtime setup, licenses, limitations and full commands are in ../sage-m4ri-notes.md and ../specialist-notes.md. External runtimes are not bundled.

## Environment and evidence

Windows AMD64, 16 logical CPUs. Product/reference runner: CPython 3.13.5; Sage runtime: Python 3.7.10. Native compiler: MinGW GCC with portable -O3 -std=c++17; standalone M4RI uses its separately documented host-tuned build. No affinity or frequency governor was imposed. Individual raw samples are retained in comparison-results.json, sage-results.json, sage-incidence-results.json, gap-results.json and cli-results.json. Historical 0.1 measurements remain explicitly labeled historical.

All positive Sage certificates were independently checked against the original corpus after timing. The GAP wrapper independently checks every positive certificate before accepting a checkpoint. The product/reference harness checks every positive output with the independent reference checker. Source hashes and canonical incidence hashes bind the recorded data; these are software and benchmark receipts, not Lean kernel receipts.
