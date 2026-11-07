# Native backend

This optional backend implements the full recognition and reconstruction contract in original C++17 code. It does not call Sage, GAP or M4RI. The source is Apache-2.0, as is the surrounding project.

## Build and selection

```console
python native/build.py
```

The standalone builder writes a shared library below `build/`. The public `build_native()` helper instead defaults to a package-local `_native/` directory, supporting an installed package whose distribution includes `_native_src/recognizer.cpp`. Recognition never compiles or downloads anything automatically. A specific compiler executable can be passed explicitly or set with `CXX`; a specific shared library can be selected with `DESIGN_BOOLEAN_NATIVE_LIBRARY`.

Builds default to `-O3 -std=c++17 -shared` and the compiler's baseline target. Set `DESIGN_BOOLEAN_NATIVE_TUNE=native` only when deliberately building a library for that host CPU. Windows builds additionally link the GNU C++ and threading runtime statically, avoiding a hidden MinGW DLL search requirement. The resulting Windows library inspected here imports only `KERNEL32.dll` and `msvcrt.dll`. Runtime redistribution notices belong with any separately distributed compiled binary; the source-only distribution does not bundle those runtime libraries.

## Exact contract and ABI

`recognize_native(incidence, *, point_labels=None, block_labels=None, validation="certificate")` returns the same `RecognitionResult` and certificate schema as the Python implementation. Its positive certificates are identical to the Python construction for the same ordered matrix. Both dense iterable rows and packed `IncidenceMatrix` input are accepted; raw conversion time is part of a full-call benchmark.

Dense list/tuple rows use the fast `bytes` conversion. Other iterables are converted elementwise through integer indexing, so typed buffers such as `array('I')` do not accidentally expose their raw multi-byte storage as extra columns. Every dense byte is checked to be zero or one. Ragged rows, invalid indices, nonzero packed padding, labels of the wrong length, and malformed values are rejected. The native engine explicitly bounds dimensions and allocation sizes before multiplication or shifting. Its present resource bound is m ≤ 20 and at most 2^28 incidence cells; the Python backend remains available for other trusted sizes in the mathematical family.

ABI version 2 passes explicit lengths for the input and all output arrays. Outputs contain the truth table, block coordinates, point frequencies, offsets and basis indices; packed original rows are returned so the Python layer computes the same input hash without repeating slow bit packing. The native engine checks lengths and null pointers, catches C++ exceptions, and returns a status and bounded reason string. It never hands ownership of an allocation across the ABI.

## Two validation strategies

- `validation="explicit"` checks all block weights, distinct blocks and point-pair multiplicities before rank and reconstruction.
- `validation="certificate"` reconstructs first, then checks a complete exact realization certificate. The verified certificate itself implies those design axioms, so no design promise is supplied or assumed.

Both strategies require a bijective block labeling, distinct complete Walsh support, exact signed plateaued spectrum, every incidence identity, and full affine rank of the support. Integer FWHT checks the complete spectrum. The incidence verifier builds packed coordinate rows and reconstructs every input row by XOR, checking all bits rather than sampling.

The affine-rank condition excludes a nonzero linear structure. It also forces simple blocks: if two columns labeled by different x,y were equal, every support frequency u would satisfy u·(x+y)=f(x)+f(y), placing the support in a proper affine hyperplane.

For completeness, put N=2^m and A=2^(m−n/2). The certificate has exactly v=2^n frequencies u_p, with W_f(u_p)=A(-1)^g_p and no others. Walsh inversion gives the column sign sum N/A, so every column has weight (v−N/A)/2. Each row sign sum is A, and distinct character rows have correlation zero, so pair multiplicity is (N−2A)/4. These are exactly the supported k and lambda. Thus certificate-first success proves all original design requirements. A failure before certificate completion does not claim that the design was already validated.

## Validation

The final release suite passes 34 test methods, including nine native-specific differential and ABI tests. It covers dense and packed matrices, typed buffers, iterators, label permutations, malformed input, single-bit corruption and exact agreement of both validation strategies. All 65,536 derived four-variable candidates also agree with the independent Walsh expectations: 896 recognized and 64,640 rejected. These are structured candidates, not all binary incidence matrices.

The selected packing implementation separates dense and packed loops and avoids a branch per bit. Two alternating-order local comparisons found a small consistent large-input benefit; small examples were neutral within timing noise. This is a minor implementation improvement. The principal gains come from the native pipeline and the certificate-first theorem. Authoritative external comparisons and raw samples are in ../benchmarks/README.md; earlier development diagnostics are not release timing claims.
