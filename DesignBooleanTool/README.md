# Design Boolean 0.2

Recognize a supported binary incidence design and reconstruct an explicit plateaued Boolean function, with a certificate that can be checked directly against the original matrix.

The tool accepts arbitrary row and column order: the function and coordinate labels are recovered, not supplied. It reconstructs a representative and verifies the complete Walsh spectrum and every incidence identity using exact arithmetic. The native certificate-first path proves the required design conditions from these checks; it does not assume that an input is already a design.

**Python 3.10+ · Python API and CLI · optional native C++ backend · JSON, CSV and block-list input**

Version 0.2 adds complete native recognition/reconstruction and a proof-backed certificate-first validation strategy. It runs without SageMath, M4RI or GAP; those are external benchmark comparators.

## Install

From this directory, the usual installation is:

```console
python -m pip install .
design-boolean build-native
```

The second command explicitly compiles the optional backend with `g++` or `clang++`. Set `CXX` to choose a compiler. Recognition never downloads or builds software automatically. The Python implementation remains available without a compiler, but the reported native speedups require a successful native build.

An offline installation needs only Python and pip; no build dependency download is required:

```console
python tools/build_wheel.py
python -m pip install --no-index --no-deps dist/design_boolean-0.2.0-py3-none-any.whl
design-boolean build-native
```

The offline wheel, installed native build and console command were tested in a fresh virtual environment. To use a virtual environment, run `python -m venv .venv` first and use its Python executable for the two installation commands. Python module invocation is also supported: `python -m design_boolean`.

## Reconstruct a published example

```console
design-boolean recognize examples/published-example-2.json -o result.json --certificate-out certificate.json --function-out function.json
design-boolean verify examples/published-example-2.json certificate.json
```

The first command recognizes the published 16 × 32 design, reconstructs a five-variable function, and saves its truth table, algebraic normal form and Walsh statistics. The second checks the standalone certificate without repeating the basis-recovery algorithm.

For this fixture the reconstructed algebraic normal form is:

```text
x0*x2 + x1*x3 + x0*x1*x4
```

Use `--backend native` to require native execution or `--backend python` to force the Python implementation. The default `auto` uses an explicitly built native library when available and otherwise selects Python.

The package uses zero-based variable names; integer bit i represents x_i. A differently relabeled input may produce a different representative. The output is an explicit realization, not a canonical form for equivalence testing or a cryptographic-security certificate.

Try `examples/published-example-4-negative.json` to see a genuine published negative, or `examples/proof-counterexample-64x128.json` to see why ordinary incidence rank is insufficient. A negative result deliberately exits with code 1.

## Python API

```python
import json
from design_boolean import recognize, verify_certificate

with open("examples/published-example-2.json", encoding="utf-8") as stream:
    data = json.load(stream)

result = recognize(data["incidence"])
if result.recognized:
    f = result.function
    print(f.num_variables, f.anf(), f.nonlinearity)
    assert verify_certificate(data["incidence"], result.certificate).valid
else:
    print(result.status, result.reason)
```

`BooleanFunction` exposes a truth table, integer evaluation, `anf_terms()`, `anf()`, `walsh_spectrum()` and `nonlinearity`. Within SageMath, `f.to_sage()` converts to its BooleanFunction type. Sage conversion is optional and was not exercised on the test host.

For an application already holding packed rows, use `IncidenceMatrix(tuple_of_integer_rows, num_blocks)`. Bit j of a row is the entry in block j. `IncidenceMatrix.from_blocks(point_count, blocks)` accepts lists of point indices. Both packed and dense paths produce the same reconstruction certificate.

## Input formats

A JSON file can be a rectangular point-by-block array, or:

```json
{"incidence": [[0, 1], [1, 0]], "point_labels": ["a", "b"], "block_labels": ["A", "B"]}
```

The tiny matrix above illustrates syntax only; its size is outside the supported theorem. A block-list file instead has `point_count` and `blocks`, for example `{"point_count": 3, "blocks": [[0, 2], [1]]}`. Point indices are zero-based and repetitions within a block are rejected. Labels are optional annotations and are never treated as a hidden coordinate system.

CSV files contain one binary row per point, without a header. JSON and CSV also support gzip compression. The CLI defaults to at most 16,000,000 incidence cells and 128,000,000 decompressed input bytes; use `--max-cells` and `--max-bytes` to change these bounds for trusted larger data.

Exit codes are 0 for recognized/verified, 1 for a negative recognition or certificate failure, 2 for malformed input or an I/O error, 3 for an unsupported shape, and 4 for an unavailable or failed native backend. JSON output includes a readable reason and recognition diagnostics. Certificate and function files are emitted only on success.

## Exact supported scope

Let v=2^n be the number of points and b=2^m the number of blocks. This release covers even n ≥ 4, m ≥ n, and r=m−n, with:

- every block having k=2^(n−1)−2^(n/2−1) points;
- every pair of distinct points lying in λ=2^r·2^(n/2−1)·(2^(n/2−1)−1) blocks;
- no repeated blocks.

For this family the characterization requires bordered binary rank m+2. The tool computes this through normalized columns and directly recovers coordinates. Successful reconstruction has Walsh values 0 or ±2^(m−n/2), exactly v nonzero Walsh coefficients, and no nonzero linear structures.

The r=0 bent case and every r≥1 in this range are included. Other design parameters, complemented families, degenerate cases and incidence structures outside this family have no general classification from this release. A `not_recognized` answer is scoped to the specified family. Complexity is polynomial in the explicit incidence size, which may be exponential in the number of Boolean variables.

See [the algorithm and proof correspondence](algorithm-notes.md) for formulas, the direct verifier and source theorem names. The mathematical argument is formalized in the cited Lean source; this Python implementation is independently tested software and is not extracted from a Lean program.

## Tests and published examples

[Published-example documentation](published-examples.md) identifies two exact published positive functions, one exact published negative construction, a shuffled positive, three family instances and the proof's own negative control. The matrices are regenerated from the cited formulas rather than copied from screenshots. Their point/block labels and source functions are test metadata; recognition works without them.

```console
python native/build.py
python -m unittest discover -s tests -v
python examples/validate.py
```

The main suite includes Python, native, dispatch and CLI regression tests; see AUDIT.json for the final count. A separate exhaustive check covers all 65,536 four-variable truth tables converted into candidate incidence matrices; the native certificate-first, native explicit-validation and Python methods agree, accepting 896 and rejecting 64,640. This is a finite structured stress check, not enumeration of every binary incidence matrix.

```console
python tests/exhaustive_four_variable.py
```

The tests include independent direct Walsh sums and incidence checks, coordinate relabeling, corrupted matrices and certificates, malformed data, gzip, resource limits and CLI round trips. The fixture validator independently checks the full design axioms and both binary ranks.

## Benchmark against actual backends

[Full results, scope and reproduction](benchmarks/README.md) compare complete pipelines using actual SageMath, upstream M4RI and GAP DESIGN, alongside both native strategies and the Python implementation. External runtimes and compiled arithmetic libraries are not emulated.

The available local Sage runtime is the archived Windows/Cygwin SageMath 9.3, with bundled M4RI 20200115. Standalone M4RI 20260122 and GAP 4.16.1 / DESIGN 1.8.2 are also exercised. Results against Sage 9.3 do not establish a claim against current Sage releases or every tuned build. Every comparator is documented as an explicit adapter; these packages do not all supply a stock design-to-Boolean reconstructor.

The strongest Sage mode uses the same certificate-first mathematical strategy as our tool and native Sage GF(2)/M4RI basis solving, Walsh transforms and matrix incidence checks. A separate mode runs its actual `IncidenceStructure.is_t_design`. GAP's full adapter calls actual DESIGN validation and GAP compressed GF(2) reconstruction. Timers include conversion, validation, reconstruction and exact realization checks; corpus JSON parsing and runtime startup are excluded from those primary timings. User-facing fresh-CLI timings are reported separately.

```console
python benchmarks/compare_backends.py --corpus-only benchmarks/corpus.local.json
python benchmarks/compare_backends.py --m4ri-library PATH_TO_M4RI_WRAPPER --repeats 5
```

See [Sage/M4RI setup](sage-m4ri-notes.md) and [GAP DESIGN setup](specialist-notes.md) for exact versions, optional external runtime commands and licenses. Historical Python-only release measurements remain in `benchmarks/python-0.1-report.md`; they are not the new native measurements.

## Native validation and portability

The native default derives all design axioms from a complete verified reconstruction certificate. [The validation theorem](VALIDATION-THEOREM.md) gives the Walsh-inversion and orthogonality argument. Explicit block and pair counting remain available as an ablation through `design_boolean.native.recognize_native(matrix, validation="explicit")`.

The compiler default targets its portable baseline; `DESIGN_BOOLEAN_NATIVE_TUNE=native` explicitly enables host-specific tuning. The release source and wheel do not bundle a native binary or any external computer-algebra runtime. Windows AMD64 is the tested native build platform in this run. The C++ backend bounds m at 20 and the incidence product at 2^28 cells; larger trusted instances can select Python explicitly. CLI byte/cell limits remain independently enforced.

## Attribution and license

The construction follows `linearize`, `reconstruct`, `complete_characterization` and `open_problem_4` in [our bordered-rank Lean proof](https://github.com/Dugongue/MathProofs/blob/main/PlateauedAdditionDesigns_BorderedRankCharacterization.lean). The design theory and published examples are credited to [Hyun, Kwon, Wang and Wu](https://arxiv.org/html/2605.24355v1); additional original-function attribution is in the fixture documentation. The benchmark includes established TSDP mathematics, not a claimed new baseline method.

Original implementation: MathProofs contributors. Apache License 2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE). No external mathematical library or third-party runtime source is bundled.
