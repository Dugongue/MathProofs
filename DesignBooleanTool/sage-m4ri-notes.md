# SageMath and actual M4RI comparison setup

## Backends actually exercised

- **SageMath 9.3**, official archived Windows/Cygwin distribution, released 2021-05-09, with Python 3.7.10 and bundled M4RI package version 20200115. It was extracted privately rather than installed through a global installer. Native Sage GF(2) matrices, matrix basis/solve operations, `BooleanFunction.walsh_hadamard_transform` and actual `IncidenceStructure.is_t_design` were exercised.
- **Upstream M4RI 20260122**, Git commit `397a70fcffeb17b0c25c0aa40231145fc392317f`, built with MinGW GCC, `-O3 -march=native -msse2`, single-threaded, explicit 32 KiB/256 KiB/8 MiB cache configuration. The generated configuration is documented; it was not auto-tuned. Upstream arithmetic source was not patched.

These are actual backend calls, not timings of a Python imitation. SageMath 9.3 is an older distribution; measurements cannot establish a speed claim against current SageMath releases or every tuned build.

## Sage full pipeline

`sage_m4ri_sage.py` imports Sage directly and does not import the product implementation. Its full pipeline checks binary input and shape, normalizes a native GF(2) incidence matrix, obtains independent basis columns with Sage/M4RI, solves a square basis submatrix for all block coordinates, reconstructs the truth table, computes the full Sage Walsh transform, verifies every support sign, reconstructs the complete incidence matrix by native matrix multiplication, and checks affine support rank.

The strongest default, `--validation spectral`, validates all design conditions through the complete spectral-incidence realization certificate. This is the same sufficient mathematical validation strategy used by the optimized product; it is not an unverified design promise. The optional `--validation incidence` additionally constructs Sage's actual `IncidenceStructure` and calls `is_t_design(2,v,k,lambda)`. The optional `--validation gram` additionally validates weights, simplicity and an exact integer incidence Gram matrix.

The certificate-first implication is exact: Walsh inversion gives constant column signed sums `b/A`; signed row sums are `A`; distinct support frequencies give zero signed row-pair correlation, hence pair count `(b-2A)/4`. Full affine support excludes duplicate columns. Consequently the spectral checker proves the block sizes, pair counts and simplicity on every accepted input.

Run within a Sage environment:

```console
sage -python benchmarks/sage_m4ri_sage.py --corpus corpus.json --output sage-results.json --repeats 5 --validation spectral
```

For an existing extracted Windows/Cygwin runtime:

```console
python benchmarks/sage_m4ri_windows.py --runtime CYGWIN_ROOT --corpus corpus.json --output sage-results.json --repeats 5 --validation spectral
```

The corpus is JSON `{"cases": [{"id": "name", "incidence": [[0,1]], "expected_status": "recognized"}]}`; the tiny matrix only illustrates syntax. Results include native version information, per-case median and individual milliseconds, classification and the reconstructed certificate. Input JSON loading and interpreter startup are excluded; each measured call includes input validation through complete reconstruction and certificate checks. Each case receives one untimed warmup.

The correctness smoke run passed both published positive functions and both negative constructions, in spectral and IncidenceStructure modes. Its timings were deliberately not promoted to final measurements because extraction was still active. The final benchmark harness collects measurements after background extraction and compilation finish.

## Standalone M4RI build and adapter

M4RI itself supplies rank, not an entire design-to-Boolean reconstruction product. `m4ri_baseline.py` exposes a callable rank backend compatible with the complete independent reference pipeline. Such a composed measurement must be labeled as that reference pipeline with actual M4RI rank; it is not a measurement of a complete Sage pipeline.

```console
python benchmarks/m4ri/build.py --work EXTERNAL_BUILD_DIRECTORY --cc gcc
python benchmarks/m4ri/validate.py --library EXTERNAL_BUILD_DIRECTORY/m4ri_rank.dll
```

On Linux the output suffix is `.so`. The thin wrapper consumes little-endian packed rows and includes the conversion/copy cost in its rank call. The current build is intended for little-endian targets. The validation script checks 110 rectangular, zero-dimension and word-boundary cases against an independent binary-rank implementation.

The pinned external checkout retains M4RI's GPL-2.0-or-later license and upstream attribution. No upstream source, DLL or installer is copied into the runtime package or this benchmark source directory. The benchmark wrappers and generated configuration are original adapter code. The official Sage Windows archive and its known compatibility limitations are documented in the upstream release page: https://github.com/sagemath/sage-windows-cygwin/releases/tag/0.6.3-9.3 . Current Windows Sage installation guidance is at https://github.com/sagemath/sage-windows .
