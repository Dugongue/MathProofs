# Binary linear-circuit complexity and rigidity from a finite Fourier estimate

Conditional on the cited unrefereed finite Fourier estimate.

### Theorem K1 (F_2 transfer). Conditional on OAI Fourier Thm 1.1/1.2.
Let N = 3^k and let ω ∈ F_4 be a primitive cube root of unity. Let M = (ω^{x·y})_{x,y ∈ F_3^k} be the character table of (Z/3)^k over F_4 (admissible: N is odd, and ω has order 3 = exp). Let M_R ∈ F_2^{n×n}, n = 2N, be its realification: block (x,y) is the 2×2 matrix of multiplication by ω^{x·y} on F_4 = F_2·1 ⊕ F_2·ω. Then:
1. (XOR circuits) C_{F_2}(M_R) ≥ 2c N√log N − 4N = Ω(n√log n).
2. (F_2 rigidity) If M_R = B + Z over F_2 (or over F̄_2) with rank B ≤ βn and |supp Z| ≤ (η/4)·n·2^{√log(n/2)/8}, then N is bounded. So for large n, R^{F_2}_{M_R}(βn) > (η/4)·n·2^{√log(n/2)/8}, a superlinear rigidity lower bound at linear rank for an explicit F_2 matrix.

*Proof.* Let E_N be the block-diagonal map on F_4^{2N} acting on each coordinate pair by E = [[1, ω],[1, ω²]] (det E = ω² − ω = 1). For x_0, x_1 ∈ F_2^N with x = x_0 + ωx_1, E_N(x_0,x_1) = (x, x̄), where x̄ applies Frobenius entrywise. Since M_R(x_0,x_1) represents Mx, we get E_N M_R (x_0,x_1) = (Mx, M^σ x̄), where M^σ = (ω^{2x·y}). F_2^{2N} spans F_4^{2N}, so as F_4-matrices
E_N · M_R = (M ⊕ M^σ) · E_N.
M^σ is a row permutation of M (row x of M^σ is row −x of M). So M ⊕ M^σ = batchMatrix of J = 2 forward blocks of order N in the coordinates allowed by `FourierBlock`.
- (1) An F_2-circuit for M_R is an F_4-circuit, since F_2 coefficients lie in F_4. Pre-compose E_N^{-1} (2N binary gates), fold scaled readouts into the gate coefficients, and post-compose E_N (2N gates). This computes M ⊕ M^σ, so C_{F_4}(M⊕M^σ) ≤ C_{F_2}(M_R) + 4N. Thm 1.1 with J = 2 gives C_{F_4}(M⊕M^σ) ≥ c·2N√log N.
- (2) Conjugation by E_N preserves rank, and maps each nonzero entry of Z into one 2×2 block, so the support grows by ×4. A decomposition of M_R thus gives M⊕M^σ = B' + Z' with rank B' ≤ βn = β h (h = 2N) and |supp Z'| ≤ η h 2^{√log N/8}. With the zero feedback system (s = 0, readouts zero), this puts M⊕M^σ in the set of Thm 1.2, which forces 0 = s ≥ c h√log N. That is a contradiction for N ≥ 2. Zariski closure over F̄_2 is preserved by the same fixed linear conjugation. ∎

*Machine check.* [local reference omitted] verifies E_N·M_R = (M⊕M^σ)·E_N and that M^σ is a row permutation of M for k = 1..4 (N up to 81). All four pass.

*Status and value.* The transfer is elementary. Its value is that it puts the claimed breakthrough onto the classical F_2 targets: superlinear XOR-circuit complexity, and Valiant rigidity over F_2 at rank εn (previously the explicit bound was Θ((n/ε) log(n/ε))). It is still short of Valiant's n^{1+δ} threshold for log-depth consequences. The same argument works for any (Z/p)^k over F_{2^e} with p | 2^e − 1 and **fixed** e (J = e conjugate blocks; the basis change costs O(e²N)).
