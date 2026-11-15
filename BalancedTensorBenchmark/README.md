# Balanced tensor isomorphism as an executable pipeline

This package implements the Lean-checked balanced order reduction and two smaller tag policies. It also implements exact binary backends, generates the test corpus, and replays two external solver comparisons. The code handles ordered modes and leaves of dimension at most three over $\mathbb F_2$, with at most $2^{20}$ input coefficients. The encoder itself supports larger dimensions as a symbolic coordinate representation.

## Run it

Install Python 3.10 or later, NumPy, and a C++20 compiler. From this folder, build the native solver and produce example pairs.

~~~powershell
python -m pip install numpy
g++ -std=c++20 -O3 -DNDEBUG native_ti.cpp -o native_ti.exe
python benchmark.py --corpus corpus --corpus-only
python pipeline.py corpus/d6-222222-iso-00.ti
python check_encoder.py
~~~

The input starts with tensor order and field characteristic, then the mode dimensions, then the two coefficient arrays in row-major order. Coefficients are separated by whitespace. The pipeline emits a JSON verdict, timings, and a verified factorwise witness on positive instances. A timeout means the budget expired with the verdict unresolved. To repeat the benchmark with the optional adversarial negatives and all native controls, use the following command.

~~~powershell
python benchmark.py --corpus full-corpus --exhaustive --repeats 7 --extra-negatives solver-transfer-fixtures --algorithms balanced balanced-runs half-runs direct-rank direct-exhaustive published-runs balanced-grouped half-grouped --output native-results.json
~~~

Run the Traces or CaDiCaL adapters with the location of those installed tools.

~~~powershell
python baseline_benchmark.py --corpus corpus --runtime $SageRuntime --output traces-results.json
python baseline_benchmark_sat.py --corpus corpus --cadical $CadicalExe --output cadical-results.json
~~~

The Traces runner expects the portable Sage/Cygwin runtime used in the benchmark, with dreadnaut in its usual bin directory. The adapter also accepts an explicit dreadnaut binary for single-input use. The CaDiCaL runner accepts the standalone native executable. No third-party binaries are bundled. For the separate covector-count and meet-in-the-middle experiment, build the second backend and run its driver.

~~~powershell
g++ -std=c++20 -O3 -DNDEBUG solver_transfer.cpp -o solver_transfer.exe
python solver_transfer_pipeline.py --corpus corpus --repeats 5 --output transfer-results.json
~~~

## What is executed

- **Balanced** constructs a three-way payload view and its named product-tree constraints. The backend eliminates the internal variables using those exact constraints and leaves the fixed ordinary markers implicit. It screens candidate factor maps using binary contraction ranks and verifies the original coordinate equation on positive returns.
- **Balanced runs and half runs** construct the compact ordinary tensor as run descriptors before calling the same backend. **Published runs** constructs the Grochow–Qiao path-algebra multiplication tensor as sparse descriptors, then calls that backend using the known relation blocks. These tests include compiler construction cost for each pair.
- **Grouped rank controls** use ranks of whole grouped-mode contractions, recorded as conditional rank histograms at the original leaf covectors. This tests how the choice of group sizes affects pruning under the same exact search.
- **Direct rank and direct exhaustive** use the original coefficient arrays. Both native solvers independently verify all returned witnesses. The tests include definite negatives with equal marginal ranks, random isomorphic copies, degenerate tensors, and adversarial examples with equal projective-count and all-cut profiles.

See [benchmarks](BENCHMARK.md), [external adapters and independent layout experiment](baseline_notes.md), [encoder and spectral-erasure proof](ENCODER.md), [compact proof and solver correctness](CompactTags.md), and [covector solver transfer](SOLVER-TRANSFER.md). The proof-to-code translation, revised tags, and backend code have informal audits and exact executable controls. [Original Lean certificate](https://github.com/Dugongue/MathProofs/blob/main/BalancedOrdinaryReduction.lean).
