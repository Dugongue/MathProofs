# Quantitative halting in matrix-product families

Explicit dimensions, first-entanglement length, input localization, and the specified PEPS realization.

## 1. Explicit dimensions

### 1.1 A cheaper threshold state: Bell-diagonal with one moving coefficient

Use the real Pauli basis I, X, Z, W := XZ = [[0,−1],[1,0]]. Note W⊗W = −Y⊗Y is real. Define
$$\tau(\varepsilon)=\tfrac14\Big[I\otimes I+(\tfrac13+\varepsilon)X\otimes X+\tfrac13 W\otimes W+\tfrac13 Z\otimes Z\Big].$$
In the usual (XX,YY,ZZ) correlation coordinates this is t = (1/3+ε, −1/3, 1/3). The Bell projectors are Φ± = (II ± XX ∓ YY + ZZ)/4 and Ψ± = (II ± XX ± YY − ZZ)/4.

- **Spectrum.** The eigenvalues are (1+t_x−t_y+t_z)/4 = (2+ε)/4, (1−t_x+t_y+t_z)/4 = (2/3−ε)/4, (1+t_x+t_y−t_z)/4 = (2/3+ε)/4 and (1−t_x−t_y−t_z)/4 = (2/3−ε)/4. So τ(ε) is positive definite for |ε| < 2/3, and both one-qubit marginals are I/2.
- **Partial transpose.** Transposing qubit 1 sends Y to −Y and fixes X and Z, so t becomes t' = (1/3+ε, 1/3, 1/3). The eigenvalues are (4/3+ε)/4, (4/3−ε)/4, (4/3+ε)/4 and **−ε/4** on Ψ−.
- **Separability.** By the two-qubit PPT criterion (Horodecki–Horodecki–Horodecki, arXiv:quant-ph/9605038, as already used in Network.md), τ(ε) is separable iff ε ≤ 0, for |ε| < 2/3.

Compare σ(F) in Network.md: there the moving parameter sits in all three channels XX, YY, ZZ. Here **only the XX channel moves**. This is optimal among Bell-diagonal threshold states. If any correlation coefficient is 0, the face |t_x|+|t_y|+|t_z| = 1 of the separable octahedron meets the state tetrahedron only on its boundary, where a Bell eigenvalue is 0. So all three channels must be non-zero, but only one has to vary.

### 1.2 The sign trick: the key register costs no bond dimension

**Keys.** Each internal site has a key g ∈ G = (ℤ/2)². Write V_{(u,v)} = X^u Z^v. Then V_h P V_h^* = χ_P(h) P with characters χ_X(u,v) = (−1)^v, χ_Z(u,v) = (−1)^u and χ_W = χ_Xχ_Z. With h = Σg_i, χ_P(h) = Π_i χ_P(g_i). Hence
$$(I\otimes V_h)\tau(\varepsilon)(I\otimes V_h)^*=\tfrac14\Big[II+\sum_{P\in\{X,W,Z\}}c_P\,\textstyle\prod_i\chi_P(g_i)\,P\otimes P\Big],$$
where c_X = 1/3+ε and c_W = c_Z = 1/3. Network.md carried the running key h in a 4-dimensional virtual register and made 4 copies indexed by the left endpoint matrix entry, a factor of 16. Here the sign is a **scalar multiplied site by site**, one bond channel per Pauli.

**Construction (general form).** Take a weighted automaton (fixed matrices A_a of size N×N, input row c_t, fixed column v_0). Suppose that for words w of length m ≥ 1 it gives a value
$$\varepsilon_w=c_tA_{a_1}\cdots A_{a_m}v_0\,/\,\beta^m\in(-\tfrac23,\tfrac23),$$
where β ≥ 1 is a fixed rational.

The bond space is ℂ_I ⊕ ℂ_W ⊕ ℂ_Z ⊕ (ℂ_X ⊕ ℂ^N_X), of dimension **χ = 4+N**. The bulk tensor is diagonal in the physical index (a,g) and acts on each bond channel as follows:

- **I channel:** 1/q.
- **W channel:** χ_W(g)/q.
- **Z channel:** χ_Z(g)/q.
- **X channel:** χ_X(g)·diag(1/q, A_a/(qβ)).

The left tensor at endpoint entry (i,j) is the row
$$\big(\tfrac14\delta_{ij},\ \tfrac1{12}W_{ij},\ \tfrac1{12}Z_{ij},\ \tfrac1{12}X_{ij},\ \tfrac14X_{ij}c_t\big).$$
The right tensor at (r,l) is the column (δ_{rl}, W_{rl}, Z_{rl}, X_{rl}, X_{rl}v_0).

Contraction gives exactly ρ_{t,m} = q^{−m} Σ_{w,g} |w,g⟩⟨w,g| ⊗ (I⊗V_h)τ(ε_w)(I⊗V_h)^*. All of the following arguments go through verbatim from Network.md:

- normalization, rationality and strict positivity;
- block-diagonal NPT ⟺ some ε_w > 0;
- full separability otherwise;
- erasing one site averages one uniform key, so χ_P sums to 0 for every P ≠ I and the right qubit is depolarized. Every proper marginal is therefore maximally mixed.

**Commutativity.** If the A_a commute, all bulk matrices commute, because each is block diagonal with scalar or A_a blocks. The physical index is classical, so permutation invariance follows.

**Minimality of keys.** Four keys are the minimum for this marginal property among Pauli twirls. One needs Σ_g χ_P(g) = 0 for P = X, Z and W with χ_W = χ_Xχ_Z. With 2 keys, χ_W(g_1)χ_W(g_2) = (−1)(−1) = +1, so the W channel does not cancel. An odd number of ±1 terms cannot sum to 0.

**Lower bound for this state family.** Consider the cut between sites p and p+1 at fixed m. The operator is Σ_{P∈{I,X,W,Z}} (P on qubit A)⊗(P on qubit B)⊗M_P. The left factors are linearly independent, and so are the right factors, so the operator Schmidt rank equals Σ_P rank M_P.

- rank M_I = rank M_W = rank M_Z = 1.
- M_X(w_1,w_2) = ±(1/3 + ε_{w_1w_2}) at fixed total length. Its rank is the Hankel rank of 1/3 + (translation-span of the series), which equals N_t for long enough blocks when the series is polynomial in letter counts. Here N_t is the dimension of the translation span of J_t.

So any MPO for these states, commuting or not, needs bond ≥ 3+N_t. The construction uses 4+N. The extra 1 pays for a single bulk serving all lengths: the constant 1/3 and the decaying β^{−m} part cannot share a channel. N ≥ N_t because one bulk serves every t.

### 1.3 Commuting instances from universal Diophantine equations

As in Network.md, let U(t,x_1,…,x_s) be universal over ℕ of degree δ in x, with letters {0, e_1,…,e_s} and A_a the translation matrices on monomials of degree ≤ D = 2δ. Put J_t = 1−2U², and set ε_w = J_t(k(w))/(8L_t b^m) with b = 2^{D+1}, so |ε| ≤ 2^{−m}/8. Then N = dim of the translation-closed span containing all J_t, which is at most |↓(supp U + supp U)| ≤ C(s+2δ, 2δ). Here ↓ is the down-closure in ℕ^s, because translation-closed monomial spans are down-sets.

Universal pairs (ν,δ) over ℕ come from J. P. Jones, *Universal Diophantine equation*, J. Symbolic Logic 47 (1982) 549–571, [doi:10.2307/2273588](https://doi.org/10.2307/2273588). Sources checked:

- (58,4) and the 9-unknown pair (9, 1.64·10^45) are restated in the formal-proof paper [arXiv:2505.16963](https://arxiv.org/abs/2505.16963). That paper credits ν = 9 to Matiyasevich's announcement, with the complete proof published by Jones.
- An esolangs.org table ([Diophantine equation](https://esolangs.org/wiki/Diophantine_equation)) lists rows of Jones's table. It has (58,4), (12, 1.3·10^44), (11, 4.6·10^44) and (10, 8.6·10^44), but **no 9-unknown row**.
- The other ν rows, (38,8), (32,12), (29,16), are quoted from memory of the table and were not seen in a checked source.

Jones's U is universal in the form x ∈ W_v, with parameters x and v; the halting set K comes from setting x = v = t.

For the integer case, Sun's 11 unknowns over ℤ (arXiv:1704.03504, Cor. 1.1; also 9 unknowns with z_9 ≥ 0) can be used with **signed letters**. The letters ±e_i act by A_i^{±1}, which still commute and are rational and unipotent. This gives q = 4(2s+1). No degree is stated, and q is larger than for Jones over ℕ.

| Source (ν, δ) | D = 2δ | N ≤ C(ν+D, D) | **χ = 4+N (this note)** | Network.md 16(1+N) | q = 4(ν+1) |
|---|---|---|---|---|---|
| Jones (58, 4) | 8 | 5,743,572,120 | **5,743,572,124** | 91,897,153,936 | 236 (59 without keys) |
| Jones (38, 8) | 16 | 21,094,923,659,355 | 2.1·10^13 | — | 156 |
| Jones (32, 12) | 24 | 4.36·10^15 | — | — | 132 |
| Jones/Matiyasevich (9, 1.64·10^45) | 3.28·10^45 | ≈ (3.28·10^45)^9/9! ≈ 10^404 | ≈ 10^404 | — | **40** (10 without keys) |

Without the marginal-hiding keys, q = ν+1. Dropping the padding letter as well gives q = ν. Only "some length" survives then, not "all large lengths". The witness k = 0 needs one dummy unknown in that case.

**1c (conditional).** Suppose a universal V ≥ 0 of degree 4 has V ≥ 1 off its zero set, for example a sum of squares of a quadratic system as produced by Skolem's reduction. Then J = 1−2V with D = 4. If Jones's degree-4 polynomial in 58 unknowns has that form, N ≤ C(62,4) = 557,845, so **χ ≤ 557,849**. I have not seen Jones's quartic, so this is unverified.

The obvious do-it-yourself route is worse. Adding a product variable y_{ab} = x_ax_b for every pair gives up to 58+1711 unknowns and a dense bound C(1773,4) ≈ 4·10^11.

**Why squaring cannot be avoided in one block.** Suppose a block is affine in the integer U. The separable states on a line form a closed interval, so the entangled parameters form a complement of an interval. That set cannot be {0} ∩ ℤ, so degree 2 in U is necessary in this architecture.

**Site dimension: lower limits are open problems.** With commuting physical-diagonal bulk and a single counting letter plus padding, every block is governed by c_tA^n v. Deciding ∃n: ε_n > 0 is then an instance of the Positivity problem for linear recurrences with a fixed matrix and variable initial vector. Its decidability is open in general and known only for low orders (Ouaknine–Worrell). With two counting letters the polynomial case is the 2-unknown Diophantine problem, which is open. So the minimal commuting q is tied to open problems. The best certified value is q = 40 (keys) or 10 (no keys).

### 1.4 Non-commuting instances: from Rote's fixed PFA

G. Rote, *Probabilistic finite automaton emptiness is undecidable for a fixed automaton*, [arXiv:2412.05198](https://arxiv.org/abs/2412.05198) (2024). Checked against the arXiv HTML text:

- Emptiness means "∃w: p(w) > λ". The paper says "≥" gives the same results.
- **Theorem 1(2):** 6 fixed positive doubly-stochastic 7×7 matrices, cutpoint 1/7, only the start distribution π varies.
- **Theorem 1(4):** 2 fixed 28×28 matrices, only π varies.
- **Theorem 2(2):** 5 fixed positive 6×6 matrices, fixed start distribution, only the output vector f ∈ [0,1]^6 varies.
- **Source:** the Matiyasevich–Sénizergues 7-pair PCP, from the 3-rule semi-Thue system with undecidable individual accessibility, via Claus's reduction. Rote's Appendix B patches the empty-word rule.

**Theorem 1d.** Put ε_w = (p_t(w)−λ)/2 ∈ (−1/2, 1/2), with β = 1. The matrices are stochastic and π·1 = 1, so 1/3 + ε_w = π M_w (c·1 + f/2) with c = 1/3 − λ/2. The constant is therefore absorbed into the automaton space, and the **X channel has dimension N** with no separate constant coordinate. So χ = 3+N.

| Rote theorem | letters | N | χ | q with keys | q without keys |
|---|---|---|---|---|---|
| 2(2), input in f; reverse the chain, use M_a^T, and put f-data at the left end | 5 | 6 | **9** | **20** | 5 |
| 1(2), input in π | 6 | 7 | 10 | 24 | 6 |
| 1(4), binary | 2 | 28 | 31 | 8 | 2 |

Every bulk matrix is fixed and rational. The state is strictly positive and every proper marginal is maximally mixed (keys). It is entangled at length m iff some word of length m is accepted. There is no permutation invariance.

**Empty word.** Our chains have m ≥ 1. Rote's question counts the empty word. If p(ε) = π·f > λ (a decidable check), map the input to a fixed yes-instance. This is a many-one reduction.

**Upward closure.** Add an idle letter with M = I. This adds +4 to q (+1 without keys) and makes the entangled lengths [L(t),∞).

**Closeness to a separable reference.** To keep it, use ε_w = (p−λ)/(2·2^m), which costs one extra constant X coordinate.

**Hardness.** Rote proves undecidability. Many-one Σ1-completeness additionally needs the Matiyasevich–Sénizergues reduction to be many-one from K. It is a computable simulation, so this is standard, but **I did not check it in their text**. The Diophantine versions in 1.3 are unconditional.

Other prior cutpoint constructions (counts as tabulated by Rote): Claus 9×9 with 9 letters; Hirvensalo 2007, 25×25 with 2 letters; Blondel–Canterini 46×46. These have variable matrices, so they cannot serve as a fixed bulk.

## 2. Growth of the first entangled length

Fix an acceptable numbering, K = {t: φ_t(t)↓}, and T(t) the step count. Take the construction of Network.md, or 1.3, and set L(t) = min{m ≥ 1 : ρ_{t,m} entangled} (∞ if none).

**Lemma 2.0 (exact formula).** L(t) = max(1, h(t)), where h(t) = min{Σ_i k_i : U(t,k)=0}.

*Proof.* Some block at length m is NPT iff some word of length m has U(t,k(w)) = 0. Padding with letter 0 shows this happens iff some witness has Σk ≤ m. ∎

**Theorem 2.** Define Λ(n) = max{L(t): t ∈ K, t ≤ n}, with max ∅ = 0.

- (a) L is partial computable with domain exactly K.
- (b) For every total computable f, {t ∈ K : L(t) > f(t)} is infinite.
- (c) For every total computable f, Λ(n) > f(n) for all but finitely many n. The same holds with the binary length, Λ'(ℓ) := Λ(2^ℓ−1).
- (d) Λ ≡_T K.

*Proof.*

(a) Search lengths in increasing order. Entanglement at a fixed length is decidable by the rational tests of Network.md (U(t,k(w)) = 0 over finitely many words).

(b) Suppose not: L(t) ≤ f(t) for all but finitely many t ∈ K. Then t ∈ K iff t is in a finite table, or entanglement occurs at some m ≤ f(t). That is decidable, a contradiction.

(c) First, step 1. Put g(m,t) = T(t) if ρ_{t,m'} is entangled for some m' ≤ m, and 0 otherwise. This is total computable: if such an m' exists then t ∈ K, so running φ_t(t) halts. Let G(m,n) = max_{t≤n} g(m,t). It is computable and nondecreasing in m. For t ∈ K with t ≤ n, T(t) = g(L(t),t) ≤ G(Λ(n),n). So BB(n) := max{T(t): t∈K, t≤n} ≤ G(Λ(n), n).

Step 2 (Lemma): for computable increasing H, BB(n) > H(n) for all large n. Let S(e,x) be a padded s-m-n function, strictly increasing in x, with φ_{S(e,x)}(y) = φ_e(⟨x,y⟩). By Kleene's recursion theorem choose e_0 with φ_{e_0}(⟨x,y⟩) = "compute S(e_0,x+1), idle H(S(e_0,x+1)) steps, halt". Put u_x = S(e_0,x). Then u_x ∈ K, u_x is increasing, and T(u_x) ≥ H(u_{x+1}). For n ≥ u_0 take u_x ≤ n < u_{x+1}. Then BB(n) ≥ T(u_x) ≥ H(u_{x+1}) > H(n).

Step 3. If Λ(n) ≤ f(n) for infinitely many n (f WLOG increasing), then BB(n) ≤ G(f(n),n) =: H(n) for infinitely many n. Applying Step 2 to H+id contradicts this. For the binary-length version, compose with n = 2^ℓ−1.

(d) ≤: with a K-oracle, compute L(t) for t ∈ K by (a). ≥: t ∈ K iff entanglement occurs at some m ≤ Λ(t), which is a finite check. ∎

**Remarks.**

- Because of Lemma 2.0, Theorem 2 is the same as the classical non-boundedness of minimal Diophantine witness heights. The tensor-network content is that L is an exact physical observable equal to it.
- The same theorem holds for the PFA chains of 1.4, with L equal to the shortest accepted word length. The decidability-at-fixed-length step is the exact rational evaluation of p(w).
- PEPS (§4): L_PEPS(t) = ⌈√(L(t)+2)⌉ in the padded versions, so it is also busy-beaver-like.

## 3. Moving the input off the boundary

**Theorem 3a (no-go for fully fixed families).** Let (ρ_m)_{m≥1} be any family of rational density matrices computable from m, for example an MPO or PEPS with every tensor fixed and rational. Then E = {m: ρ_m is entangled across a fixed cut} is decidable. With ρ_m of dimension d^{O(m)}, E ∈ DTIME(2^{2^{O(m)}}).

*Proof.* By Carathéodory, ρ on ℂ^{d_A}⊗ℂ^{d_B} with N = d_Ad_B is separable iff ρ = Σ_{i≤N²} |a_i⟩⟨a_i|⊗|b_i⟩⟨b_i|. This is an existential sentence over the reals, with poly(N) variables and degree-4 equations. The existential theory of the reals is decidable in time (size)·(#eq·deg)^{O(#vars)} (Tarski–Seidenberg; Basu–Pollack–Roy). Here N = 2^{O(m)}. ∎

**Corollaries.**

- **No c.e.-universality.** For an undecidable c.e. S, no fixed family has E = S.
- **Not even all decidable sets.** By the time hierarchy theorem there is a decidable S ∉ ∪_c DTIME(2^{2^{cm}}), and no fixed computable-in-2^{2^{O(m)}} family realises it.
- **Upward-closed sets are trivial.** They are ∅ or [L,∞), and both are realisable: take P(m,y) = m−L−y_1 in 3b. So "exactly the upward closure" carries no information.
- **Finitely many program tensors do not help.** If the input enters only through one site with finitely many possible tensors, there are finitely many families, and the problem is a finite table.

**Theorem 3b (exact class for the commuting architecture).** Let
$$\mathrm{BD}=\{S\subseteq\mathbb N_{\ge1} : S=\{m\ge1:\exists y\in\mathbb N^s,\ \textstyle\sum y\le m,\ P(m,y)=0\}\text{ for some }P\in\mathbb Z[m,y]\}.$$
For every S ∈ BD there is a fully fixed (boundaries included) commuting rational MPO family of the §1.2 form with E = S. Conversely, every family of that form, meaning a commuting translation automaton on letter counts with a polynomial series, has E ∈ BD.

*Proof.* Use the letters 0,1,…,s and track all counts k_0,…,k_s, so that m = Σk. Put J(k) = 1 − 2P(Σk, k_1,…,k_s)². Then ε_w = J/(8Lb^m) with b = 2^{D+1}, fixed boundaries, and E = {m : ∃k ∈ ℕ^{s+1}, Σk = m, P(m,k_{≥1}) = 0} = S. Conversely, E = {m : ∃k, Σk = m, J(k) > 0}, and J > 0 is equivalent to Q(k) = 0 for an integer polynomial Q in this design. ∎

**What BD contains.** Witnesses y ≤ m^c reduce to y ≤ m by writing them in base m, so BD equals the class of sets with Diophantine witnesses polynomially bounded in value. This class lies in P for unary m and in NP for binary m. Its relation to the linear-time hierarchy (Adleman–Manders style questions) is open.

**Theorem 3c (input only in which lengths are probed).** Let C(t,j) = (t+j)(t+j+1)/2 + j. There is one fully fixed commuting rational MPO family ρ*_m such that, for all t,
$$t\in K\iff\exists j\ge0:\ \rho^*_{C(t,j)}\text{ is entangled},$$
and then entanglement holds for all large j.

*Proof.* Define S* = {C(t,j) : ∃k ∈ ℕ^s, r: Σk + r = j, U(t,k) = 0}. For t+j ≥ 1, C(t,j) ≥ t + 2j ≥ t + j + Σk + r. So S* ∈ BD with P = (m−C(t,j))² + (j−Σk−r)² + U(t,k)², and the unknowns (t,j,k,r) sum to at most m. Apply 3b. The columns {C(t,j)}_j are disjoint, so the equivalence holds. ∎

This needs s+3 counting letters and degree 2·max(2,δ).

**Fixed-size program site in the bulk.** Put one site with input-dependent tensor G_t^{(ij)} at any position, carrying qubit A. Add one pre-program channel with scalar transfer 1/q and fixed left vector e_*, so the left part contracts to q^{−|w_1|}e_*. Set G_t^{(ij)} = e_*^T ⊗ (left row of §1.2). The bond grows by 1. So the input can live in one fixed-dimension bulk site. It still varies over infinitely many rational tensors, which is necessary by 3a.

## 4. PEPS on n×n grids

**Theorem 4.** There are fixed rational PEPS tensors (bulk, left-column, right-column, bottom-left corner) and a computable input-dependent top-left corner tensor with the following properties. For each n ≥ 2 the n×n network defines a strictly positive state ρ^PEPS_{t,n} whose proper marginals are maximally mixed, invariant under permutations of the n²−2 non-corner sites. Moreover:

- if t ∈ K, the top-left corner qubit is NPT-entangled with the rest for all n ≥ ⌈√(L(t)+2)⌉;
- otherwise every ρ^PEPS_{t,n} is fully separable.

So "entangled at some n" is c.e.-complete.

*Construction.* Let B be the χ-dimensional bond of §1.2. Horizontal bonds are B_f ⊕ B_r (forward and return channels, dimension 2χ). Vertical bonds are B in column 1 and trivial elsewhere. Qubit A sits at corner (1,1) and qubit B at corner (n,1). Every other site is a letter site with physical (a,g).

- **Bulk site** (columns 2..n−1): forward channel multiplied by T_{a,g} (the §1.2 bulk matrix); return channel identity.
- **Right column:** forward-in, multiplied by T_{a,g}, then sent out on the return channel (a cap).
- **Left column**, rows 2..n−1: up-in, multiplied by T_{a,g}, sent forward-out; return-in passed identically to down-out.
- **Corner (1,1):** emits L_t^{(ij)} forward; passes the return channel down.
- **Corner (n,1):** passes up to forward; contracts the return channel with R^{(rl)}.

*Proof.* The contraction is the snake product L_t·Π T_{a,g}·R over the n²−2 letter sites. The T commute, so ρ^PEPS_{t,n} equals ρ^MPO_{t,n²−2} after relabeling sites. Every property transfers from §1.2 and Network.md. Padding gives entanglement for all n²−2 ≥ L(t). ∎

The commuting bulk is what makes the snake order irrelevant. The non-commuting PFA bulk of 1.4 also works, with the idle letter, but loses permutation invariance.

**Dimensions.** The Jones (58,4) instance has PEPS bond ≤ 2χ = 11,487,144,248 and q = 236. The Rote 2(2) instance has PEPS bond 18 and q = 24 with keys plus the idle letter (6 without keys). In the Rote version the snake order is then the word order.

By 3a, removing the input corner (all tensors fixed, input n) makes the problem decidable. The analogue of 3c, probing grid sizes n in a computable column of t, needs C(t,j)+2 to be a perfect square. One can instead probe rectangles n_1×n_2 with n_1n_2−2 = C(t,j), or use PEPS on n×n with m = n²−2 inside S*-type sets. Treat this as a routine variant; it was not written out.
