# Exact smoothed orthogonal and unitary tensor isomorphism

Informal proof, November 14, 2026. This answers the exact decision version of Open Problem 2 in §1.5 of Chizewer, Everett, Mithal and Qiao, [Random tensor isomorphism under orthogonal and unitary actions](https://arxiv.org/html/2603.27128v1#S1.SS5), for bounded discrete noise of arbitrarily small magnitude. Their Theorem 1.4 gives an earlier local analysis with a perturbation size governed by the input. The approximate orbit-distance version with inverse-polynomial spectral gaps is a separate question.

The earlier [MathProofsCrossovers proof](https://github.com/Dugongue/MathProofs/blob/main/MathProofsCrossovers/PROOF.md#2-small-noise-smoothed-analysis-for-orthogonal-and-unitary-tensor-isomorphism) already gives a Gaussian spectral-gap analysis for this question and invokes a published residual torus algorithm. The new points here are bounded exact discrete noise, a polynomial detecting full support in the spectral coordinates, and a bit complexity proof for the phase test using only a fixed number of algebraic parameters at a time. The spectral-gap result and the bit complexity proof address different requirements.

## Theorem

Fix n ≥ 1. In the orthogonal case let the adversarial starting tensor A₀ have rational entries. In the unitary case let it have entries in ℚ(i). Fix any rational radius σ > 0 and confidence parameter 0 < ε < 1. Choose a power of two M ≥ 2 with M ≥ n⁶/ε and perturb each real coordinate, including both real and imaginary parts in the unitary case, independently by one of the M equally spaced numbers in [−σ/2, σ/2], sampled uniformly. Denote the resulting tensor by A, so every tensor entry moves by at most σ in absolute value.

There is a deterministic bit-polynomial-time algorithm on explicit rational inputs A and B. It outputs YES, NO or UNDECIDED, and every YES or NO is correct for exact orbit equality under the product of three orthogonal or three unitary groups. With probability at least 1−ε over A, it gives a definite answer for every B of the same format, even if B is selected after A is revealed. The bit cost is polynomial in the size of the perturbed pair, and the perturbation increases each coordinate's representation length by at most O(bitlength(σ) + log n + log(1/ε)) when M is the smallest permitted power of two.

## 1. A polynomial whose nonvanishing certifies the desired spectrum and support

For a tensor A, write a for its vectorization and G₁(A), G₂(A), G₃(A) for its three Hermitian Gram matrices of the mode flattenings. Put N = n³, Q = n²+1, and define

    K(A) = G₁(A) ⊗ I ⊗ I + Q I ⊗ G₂(A) ⊗ I
           + Q² I ⊗ I ⊗ G₃(A).

Consider the determinant

    P(A) = det [ a | K(A)a | K(A)²a | ... | K(A)^(N−1)a ].

Each Gram matrix entry is a degree-two polynomial in real coordinates, or in the real and imaginary parts in the complex case. The column with exponent j has degree 2j+1. Consequently P is a polynomial of total degree at most N² in either model.

For a fixed A, the tensor products of any orthonormal mode eigenbases form an eigenbasis for K. In such a basis let κₗ be the eigenvalues of K and cₗ the coordinates of a. The determinant above is, up to a nonzero change-of-basis factor, the product of all cₗ times the Vandermonde determinant on all κₗ. Thus P(A) ≠ 0 exactly when K(A) has simple spectrum and the vector a has a nonzero component in every eigenline. In particular, no individual Gⱼ has a repeated eigenvalue, since repetition in a mode would force repetition in K. Moreover, every entry in the tensor expressed in the three mode eigenbases is nonzero.

## 2. The polynomial is nonzero

It is enough to give a witness over the reals, since the same real subspace exists in the complex model. Let D have D_{iii} = i for i from 1 to n and all other entries zero. Let J be the all-ones tensor, and put A(t) = D + tJ. At t = 0, the three Gram matrices are diagonal with entries 1² through n². The eigenvalues of K(D) are i² + Qj² + Q²k² for the triples (i,j,k). They are distinct by base-Q expansion, so they remain distinct for sufficiently small real t by eigenvalue continuity.

For each mode, choose a real normalized differentiable eigenvector uᵢ(t) for the eigenvalue branch starting at i², with uᵢ(0) = eᵢ. Such a choice exists locally by simplicity of the eigenvalue, for instance via the simple root and adjugate column formulas. The derivative of each Gram matrix at t = 0 has (i,j) entry i+j. Differentiating the eigenvector equation gives

    (uᵢ'(0))ⱼ = (i+j)/(i²−j²) = 1/(i−j)  for j ≠ i.

Let C_{ijk}(t) be the coefficient of A(t) in the resulting mode eigenbases. If i,j,k are pairwise distinct, then C'_{ijk}(0) = 1, since changing one eigenvector cannot contract the diagonal D nontrivially at those three distinct indices. If exactly two indices coincide, say j=k ≠ i, the only basis derivative contributing is on uᵢ. The direct derivative of A(t) contributes 1, while the basis derivative contributes j/(i−j). Consequently

    C'_{ijj}(0) = 1+j/(i−j) = i/(i−j) ≠ 0.

The other two repeated-index placements have the same calculation. Finally, C_{iii}(0) = i ≠ 0. Hence for all sufficiently small nonzero t every core coefficient is nonzero. Combined with simplicity of K, this gives P(A(t)) ≠ 0. The case n = 1 also follows directly, with P(A) its sole entry.

## 3. Perturbation bound

Translate and scale the variables of P by A₀ and the nonzero grid step σ/(M−1), respectively. The resulting polynomial is still nonzero and has degree at most N². The Schwartz–Zippel bound applies over ℝ or ℂ to the independently selected grid coordinates. It gives

    Pr[P(A) = 0] ≤ N²/M ≤ ε.

This requires no assumption on A₀ and permits arbitrary dependence of B on the sampled A. The randomized sampling can use exactly log₂ M independent bits per real coordinate. The decision algorithm itself uses no randomness.

## 4. Decide orbit equality on this promise

If the exact determinant P(A) is zero, output UNDECIDED. Otherwise compare the characteristic polynomials of Gⱼ(A) and Gⱼ(B) for j = 1,2,3. Mismatch implies NO, since the Gram matrices transform by orthogonal or unitary conjugation. On a match they have the same simple ordered spectra. Choose specific normalized eigenvectors for each matched eigenvalue separately for A and B. Denote the core tensors after expressing A and B in these bases by S and T.

Every transporter between A and B must send each ordered mode eigenline of A to the matching line of B. Its residual actions in the two sets of eigenbases are diagonal with entries in the group of modulus one scalars, or {−1,1} in the real case. Conversely any such diagonal transporter between S and T gives the required original transporter.

Now |S_{ijk}| = |T_{ijk}| is required at every coordinate, so test these equalities exactly. All S_{ijk} are nonzero. If the tests pass, define r_{ijk}=T_{ijk}/S_{ijk}, which has modulus one. These ratios admit a factorization r_{ijk}=xᵢyⱼzₖ by three lists of modulus one scalars if and only if

    r_{ijk} r_{111}² = r_{i11} r_{1j1} r_{11k}

for every i,j,k. Necessity is direct from the factorization. For sufficiency take xᵢ = r_{i11}/r_{111}, yⱼ = r_{1j1}/r_{111}, and zₖ = r_{11k}. These lists give the required factors and automatically belong to {−1,1} in the real case. Thus the modulus checks and displayed identities are sufficient and necessary. Output YES if they all hold and NO otherwise.

## 5. Bit complexity of the exact tests

Use the standard polynomial-time rational algorithms for characteristic polynomials, determinant computation, and real root isolation of univariate rational polynomials. Construction of the Krylov matrix uses N powers of a rational or Gaussian rational matrix of dimension N. Clearing a common denominator first, the denominator and numerator bit lengths in the j-th column are bounded by O((j+1)(L+log N)), where L is a bound for the bit lengths of the denominator and integer matrix entries after clearing. Here L is polynomial in the input length. Thus computing and testing P(A) is polynomial in input bits.

Each simple real eigenvalue λ is represented by its characteristic polynomial and a rational isolating interval, with bit lengths polynomial in the input. An eigenvector at λ is given by a nonzero column of the adjugate of G−λI. Such a column exists because the nullity is one. Its entries are rational or Gaussian rational polynomials in λ of degree at most n−1 and polynomial coefficient size. They can be constructed by polynomial interpolation of determinants. Choose the first column that is nonzero at λ by exact univariate tests, and divide it by the positive square root of its squared norm. These rules fix an eigenvector for every mode and eigenvalue.

A single core coordinate is then a rational expression in the three selected real eigenvalues and their three positive norm square roots. Its numerator is a sum over the n³ input entries with a product of three adjugate coordinates in each summand. The expression has polynomial degree and polynomial coefficient bit length. Squared modulus and ratio tests can be cross-multiplied using the already verified nonzero denominators. A whole displayed identity involves at most five coordinates of each tensor, so each test uses an absolute constant number of real algebraic parameters, independent of n.

For explicit bit bounds, express each such test as a fixed-variable existential real formula. For each λ include its characteristic equation and isolating interval. For each norm root include the squared-norm equation and strict positivity. These fix the parameter values uniquely. Test the equality of squared moduli, or the two real equality conditions of the cross-multiplied complex identity, over that unique tuple. Expanding the resulting polynomials uses a polynomial number of monomials since the variable count is fixed. The coefficients have polynomial bit length. Standard fixed-dimensional real algebraic decision algorithms therefore give polynomial bit cost for each test. This does not require constructing a common number field for all eigenvalues of all six Gram matrices. See Basu, Pollack and Roy, [Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/978-3-662-05355-3), especially the algorithms for real root isolation and the existential theory of the reals.

There are O(n³) tests. All definitive outputs are correct for every rational input, and the polynomial failure bound ensures a definitive answer uniformly over arbitrary B after the perturbation. This completes the theorem.
