# Exact recognition and reconstruction algorithm

## Mathematical contract

Input is a binary point-by-block incidence matrix. The supported family consists of simple designs with v = 2^n points, n even and n ≥ 4, b = 2^m blocks with m ≥ n, and

- r = m − n;
- q = 2^(n/2 − 1);
- block size k = q(2q − 1);
- point-pair multiplicity λ = 2^r q(q − 1);
- nonzero Walsh amplitude A = 2^(m − n/2).

The Python and explicit-native paths check the shape, every block size, every pair multiplicity and every distinct-block condition. The default native path checks binary input, reconstructs and verifies the entire realization certificate; the proof in VALIDATION-THEOREM.md then establishes every design axiom without explicit pair enumeration. It does not infer the 2-design promise from a filename or an expected result. Shapes outside this family are `unsupported`; malformed binary data are `invalid_input`. Valid binary candidates that fail design or rank conditions are `not_recognized`.

These conditions match `PlateauedDesign.open_problem_4` and its general `complete_characterization` in `PlateauedAdditionDesigns_BorderedRankCharacterization.lean`. Both r = 0 bent functions and r ≥ 1 plateaued functions are included. The source proof's excluded n = 2 and degenerate parameter cases are not silently generalized.

## Constructive rank test

Choose anchor point p₀ = 0 and anchor block b₀ = 0. Form normalized column vectors

N_b(p) = M(p,b) ⊕ M(p,b₀) ⊕ M(p₀,b) ⊕ M(p₀,b₀).

Binary Gaussian elimination chooses original normalized basis columns, in deterministic input order, while tracking the coordinate β_b of every normalized column. The source theorem proves that the binary rank of the canonical matrix obtained by adjoining an all-one row and column with zero corner is rank(N) + 2. Therefore rank(N) = m is the required bordered-rank test.

The implementation also explicitly checks that the β_b form a bijection with integers 0,…,2^m−1. It does not rely on the theorem to waive that executable check.

Let selected basis blocks be c₀,…,c_(m−1). Define

- φ_p = Σ_i N_(c_i)(p) 2^i;
- f(β_b) = M(p₀,b);
- g_p = M(p,b₀) ⊕ M(p₀,b₀).

The tracked basis coordinates give N_b(p) = parity(φ_p AND β_b), hence

M(p,b) = parity(φ_p AND β_b) ⊕ f(β_b) ⊕ g_p.

This is a direct coordinate implementation of `linearize` in the Lean proof. No search through Boolean functions, affine changes of coordinates, or permutations is necessary.

## Direct certificate verification

Every successful call invokes a checker that is independent of the basis choice and does not accept a rank-only argument. Its mandatory certificate includes the full truth table f, β, φ, g, amplitude A, inferred parameters, and an input hash. The checker validates:

1. β is a bijection of all blocks with the entire m-dimensional binary cube.
2. Every φ_p is a distinct cube element.
3. Exact integer FWHT of the signs (−1)^f has only values 0,+A,−A.
4. Its entire nonzero support is exactly the listed φ_p.
5. The coefficient at φ_p is A(−1)^g_p.
6. Every input incidence bit satisfies the displayed identity.
7. The affine span of the support has rank m.

For step 7, f has a linear structure (a,c), meaning f(x+a)=f(x)⊕c for every x, exactly when every frequency u in its Walsh support satisfies parity(u AND a)=c. Such a nonzero a exists exactly when the differences u⊕u₀ span a proper subspace. The checker computes the rank of those differences, so its no-linear-structures conclusion is exact.

The hash binds the certificate to its input representation; correctness does not rely on collision resistance alone, since every incidence identity is checked against the actual input as well. Anchor and selected-basis metadata describe the construction; the mandatory realization fields carry the mathematical witness.

## Runtime and representation

The core has no third-party dependencies. Rows and columns are arbitrary-precision integer bitsets; pair multiplicities use the population count of the bitwise intersection of two rows. Raw input conversion and certificate construction are included in end-to-end timings, together with design validation, rank computation, reconstruction and certificate verification. Packed `IncidenceMatrix` input avoids repeated dense conversion for applications that already hold bitsets.

The Python and explicit-native paths perform v(v−1)/2 pair-intersection tests on b-bit rows. The default certificate-first native path derives all design axioms from the fully checked Walsh/incidence witness instead, as proved in VALIDATION-THEOREM.md. Column elimination uses at most min(v,b) pivots on v-bit vectors. The FWHT has b log₂ b integer additions/subtractions. Direct certificate incidence evaluation first builds coordinate masks, then uses packed row XORs. These are polynomial operations in the explicit incidence size; arbitrary-precision bit operations are not unit-cost operations. In particular, v = 2^n and b = 2^m, so no polynomial claim in only n or m is made.

This is a certificate-producing implementation, not an executable formally verified by Lean. It reuses the proof's mathematical construction; all successful outputs are additionally checked by the direct exact verifier. A positive recognition is not a claim of cryptographic security or a classification up to a canonical equivalence relation.

## Local checks performed by the core author

All fixture matrices available at implementation time were exercised: the two exact published positives, their relabeling, derived bent and plateaued examples, the published negative, and the proof counterexample. Positive cases pass reconstruction and direct verification. The 64×128 proof counterexample passes design validation but has bordered rank 10 rather than 9 and is rejected for the intended reason. The published Example 4 negative is also rejected by rank. Dense and packed paths produce identical certificates, and the `BooleanFunction` property reports the inferred number of variables.
