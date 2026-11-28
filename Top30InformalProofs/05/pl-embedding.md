# A repaired reduction to PL embeddability

The reduction proves HTP(Q)-hardness in the stated dimensions. Undecidability and completeness inherit the stated arithmetic assumptions.

## 1. Final theorem

**Theorem.** For every (k,d) with 8 ≤ d ≤ (3k+1)/2 and k ≤ d there is a polynomial-time many-one reduction HTP(ℚ) ≤ EMBED_{k→d} (PL embeddability of finite k-complexes in ℝ^d). Hence, under BB, EMBED_{k→d} is Σ⁰₁-complete in this range. Unconditionally: EMBED_{k→d} is undecidable iff-at-least HTP(ℚ)-hard; codim ≤ 1, d ≥ 5 is unconditionally undecidable (MTW).

Exact range: {(k,d): d ≥ 8, ⌈(2d−1)/3⌉ ≤ k ≤ d}. (5,7) is outside because d=7<8: it needs l=d−k−1=1, and the method needs l ≥ 2 (complement of Σ^k simply connected, CKMVW needs l ≥ 2). The same reason excludes (3,5), (4,6); the thesis only names (5,7) because it assumes k ≥ 5.

Base cases: (2l+1, 3l+2), l ≥ 2. Transport: (i) K ↪ S^d ⟺ CK ↪ ℝ^{d+1} (link of the apex), k<d; (ii) K ↪ ℝ^d ⟺ K ⊔ Δ^{k+1} ↪ ℝ^d, k+1 ≤ d. A pair in range is reached from an even l iff an even integer lies in [max(2,d−k−1), ⌊(d−2)/3⌋]. This fails exactly for (2l+1+i, 3l+2+i), l odd ≥ 3, i ∈ {0,1,2} (first: (7,11),(8,12),(9,13)); these use the l-odd branch. So **without Step 8 the theorem still holds for all other pairs** (in particular all d ≤ 10, and all codim ≤ 3).

## 2. Step 1: the Segal–Spież complex

F=F_{k,l}: vertices [k+l+3]∪{0}; all simplices of dim ≤ k on [k+l+3], all of dim ≤ l+1 containing 0. Δ^{l+1}={0,…,l+1}, Σ^l=∂Δ^{l+1}, Σ^k=∂{l+2,…,k+l+3}, Δ^k a facet of Σ^k, F_-=F−IntΔ^{l+1}. k-simplices of Σ^k are maximal in F.

**1a.** g: q_1..q_{m+1} affinely independent in ℝ^m (m=k+l+1), q_0 barycentre, vertices ↦ q_i linearly on the k-skeleton; apex ↦ b = barycentre of q_0..q_{k+1}; cone simplices linear except Δ^{l+1}, which is mapped as the cone from d = barycentre(q_0..q_k) over ∂(b∗⟨q_{k+2}..q_{m+1}⟩).
- *Hand computation (all k,l):* in barycentric coordinates the linear simplex b∗⟨q_{k+2}..q_{m+1}⟩ meets Π=aff(q_0..q_k) in exactly one point, namely q_0, with α=(k+2)/(k+l+3), β_j=1/(k+l+3) all positive, and the affine hulls are complementary. So lk(∂(b∗τ), Π)=±1, the cone from d meets Π only in d, and the local intersection index of g(Δ^{l+1}) and g(Δ^k) at d is ±1. (This is why SS move the apex: the linear simplex passes through the vertex q_0.)
- *Machine check:* `sscheck.exe k l` tests, in exact rational arithmetic, every pair of maximal simplices of the subdivided F (conv hulls meet only in the image of the common face), by vertex enumeration on the sign-constrained kernel. Results: (5,2): 55 278 pairs, 0 bad, exactly the l+2=4 pieces of Δ^{l+1} meet Δ^k, exactly at d with all barycentric coordinates of Δ^k positive. (7,3): 2 011 015 pairs, 0 bad, 5 special. Also (4,2),(3,1),(2,1) pass.
- Consequence: e=g|F_- is an embedding, D=g(Δ^{l+1}) is an embedded disk with D∩e(F_-)=eΣ^l∪{p}, p∈Int eΔ^k, index ±1, so lk(eΣ^l,eΣ^k)=±1. The quotient L=F/(c∼x') embeds (FWZ's L(k,l)).

**1b.** For a general position map f:F→ℝ^{k+l+1} let v(f) = parity of the number of intersection points of disjoint simplices of complementary dimension. ST17 Lemma 6: v(f) is independent of f if for all disjoint σ^s,τ^t, s+t=k+l, N_1=#{(s+1)-simplices ⊃σ, disjoint from τ} ≡ N_2 (symmetric) mod 2. Check: |σ|+|τ|=k+l+2, two vertices u,v remain. If 0 is free: N_1=[s<k]+[s=l], N_2=[t<k]+[t=l], and s=l⟺t=k gives N_1−N_2=2([s<k]−[t<k]). If 0∈σ: (s,t)∈{(l,k),(l+1,k−1)} and (N_1,N_2)=(2,0) or (0,2). So v≡v(g)=1. For an almost embedding h of F_-, extend over Δ^{l+1} generically rel boundary (after a small perturbation, which keeps "almost"); the only disjoint pairs that can meet are (Δ^{l+1}, facet of Σ^k), so |hΔ^{l+1}∩hΣ^k| is odd, i.e. lk(hΣ^l,hΣ^k) is odd. Holds for all 0≤l≤k.

## 3. The gadget (uniform in l) and Steps 2–3

**Definition.** Let β⊂IntΔ^{l+1} be a small (l+1)-disk around c, μ=∂β. P_1 := (μ×[0,1]) ∪ Cyl(ψ_0: S_out → μ^+∨T), μ×{0}=μ⊂L, μ×{1}=μ^+, T an l-sphere, [ψ_0]=(1,2)∈π_l(μ^+∨T)=ℤ². **G := L ∪_μ P_1** (dimension k=2l+1; fixed complex for each l). For l even L may be replaced by F_- ∪ (Δ^{l+1}∖Int β).

**(P) Parity.** For every PL embedding (indeed almost embedding, if P_1 and Σ^k are vertex-disjoint) h of G: lk(hS_out,hΣ^k) is odd. *Proof.* P_1∪(Δ^{l+1}∖Intβ) is disjoint from Σ^k. In H_l(S^d∖hΣ^k)≅ℤ (Alexander duality; no unknotting needed): [S_out]=[μ]+2[T], [μ]=[Σ^l], and lk(Σ^l,Σ^k) is odd by 1b. ∎

**(D)** Σ^l bounds Δ^{l+1}⊂L, and Δ^{l+1}∩Σ^k={c}.

**(R) Realisation.** For every odd c there are a PL embedding h_c:G→S^d and R⊂S^d, R≅S^l×D^{k+1} a regular neighbourhood of an l-sphere μ', with h_c(G)∩R=h_c(S_out)⊂∂R and [h_cS_out]=c[μ'] in H_l(R).

*Proof.* Let ē:L→S^d be induced by g, p=ē(c), D=ē(Δ^{l+1}). Take a triangulation with ē(L) a subcomplex and B_p the star of p in a second derived: (B_p; B^k, D_p) = p∗(∂B_p; S^{k−1}, μ_p), B^k=B_p∩ē(F_-) (only Δ^k is near p), D_p=B_p∩D; choose β with ē(β)=D_p.
1. H_l(∂B_p∖S^{k−1})≅ℤ and [μ_p] is a generator, because lk_{∂B_p}(μ_p,S^{k−1}) is the local index ±1 (1a). S^{k−1} is unknotted in ∂B_p (codim l+1 ≥ 3), so B_p∖B^k ≃ S^l; π_l(B_p∖B^k)=ℤ·[μ_p], simply connected.
2. Removing D_p (dim l+1) or an l-sphere from a d-manifold does not change π_j for j ≤ k−2; l ≤ k−2. So V:=B_p∖(B^k∪D_p) has π_1=0, π_l=ℤ, generated by a push-off of μ_p.
3. Choose an embedded l-sphere μ'⊂Int B_p∩V representing the generator (2l<d), R a regular neighbourhood of μ' in Int B_p∩V. μ' is unknotted in S^d, so R≅S^l×D^{k+1}. Choose an embedded S_out⊂∂R≅S^l×S^k of class c (2l<l+k). In V_R:=V∖Int R, π_l=ℤ and [S_out]=c·gen.
4. A map f:P_1→(B_p∖B^k)∖Int R with f|μ×0 = id onto μ_p, f|S_out = inclusion, exists iff c·gen = gen + 2[fT] is solvable, i.e. iff c is odd (take [fT]=(c−1)/2; the other orientation gives −c). Use a collar of ∂R for S_out×[0,δ].
5. Relative general position (Zeeman Ch. VI Thms 15, 18) in the open manifold S^d∖(ē(F_-)∪Int R), rel μ×0 ∪ S_out-collar, with respect to D: f becomes an embedding (2(l+1)<d) with f(P_1∖μ×0)∩D=∅ ((l+1)+(l+1)<d), staying in Int B_p∖B^k by compactness. The intersection with ē(F_-) (where (l+1)+k=d and general position would *not* suffice) is empty by construction, because the map takes values in the complement. ∎

This is the repaired form of Q-FWZ's (R). The original text's claim that P_0 misses things "because 2(l+1)<3l+2" omitted the pair (P_0, e(F_-)), for which the count is exactly 0; that pair is what the homotopy computation in step 4 handles, and it is the only place where "c odd" enters.

## 4. Step 4: the embedding theorem (replacement for FWZ Thm 3.7 = FWZ Thm 10)

X=X(a,b)=Cyl(φ)∪_A Cyl(f) (simplicial double mapping cylinder), A=⋁_q S^{2l−1}_q, W=⋁S^l, Y=S^l or S^l∨S^l, X∖(W∪Y)≅A×(−1,1), σ_q:=S^{2l−1}_q×(−1,1), I'=the arc over the base point from Y to W, Γ:=Y∪I'∪W.

**Theorem E.** Let l ≥ 1, d ≥ 3l+2, Q⊂S^d a codimension-0 PL submanifold (open or compact), (l−1)-connected. Every map F:X→Int Q is homotopic to a map F' with F'|Γ an embedding, and there is a PL embedding G':X→Int Q with G'|Γ=F'|Γ.

*Proof.*
1. **Model.** X ⊂ A∗(W⊔Y) ⊂ ℝ^{2l}∗ℝ^{l+1} ⊂ ℝ^{3l+2} via (a,t)↦(1−t)a⊕tφ(a), (a,s)↦(1−s)a⊕sf(a). So there is an embedding j:X→S^d. (The thesis invokes Lemma 3.32 for X but proves it only for Cyl(φ); this closes that.)
2. **Spine.** Make F|Γ an embedding (2l<d) and F(X∖Γ)∩F(Γ)=∅ (2l+l<d). Γ is an l-polyhedron and d ≥ 2l+2, so F|Γ and j|Γ are ambient isotopic in S^d (Gugenheim); m:=h^{-1}j is an embedding of X in S^d with m|Γ=F|Γ. (The ambient S^d is essential: in an abstract manifold the normal data of F(W) could differ.)
3. **Replace near the spine.** Nested derived neighbourhoods N_Γ⊃N_2⊃N_3'⊃N_3 of F(Γ) in Int Q, M_•=m^{-1}(N_•), with F(M_2)⊂Int N_Γ. F|M_2≃m|M_2 rel Γ in N_Γ by a homotopy H; by general position H((M_2∖Γ)×I) misses F(Γ) ((2l+1)+l<d). With τ:M_2∖Int M_3'→[0,1] a Urysohn function put g=m on M_3', g(x)=H(x,τ(x)) on M_2∖Int M_3', g=F outside M_2, and choose N_3 so small that it misses H((M_2∖IntM_3')×I)∪F(X∖Int M_2). Then g|M_3'=m is an embedding, g^{-1}(N_3)=M_3, and no point of Int M_3 is a double point. No uniqueness theorem for regular neighbourhoods in polyhedra is needed.
4. **General position** of g rel a neighbourhood of M_3: S:=closure of the double-point set is a compact polyhedron, dim S ≤ 4l−d ≤ l−2, S⊂X∖M_3 ⊂ ⋃σ_q∖I'.
5. **Engulf once.** Fix p∈Int I'∩A×(−1,1). Each σ_q is a (2l−2)-connected 2l-manifold, so S_q:=S∩σ_q lies in an embedded cone C'_q=cone_p(S_q)⊂σ_q with C'_q∩I'={p} (2(l−1)<2l, (l−1)+1<2l). C':=⋃C'_q is collapsible, dim ≤ l−1, and g^{-1}g(C')=C' because S⊂C'. Q is (l−1)-connected, so g(C') bounds an embedded cone C⊂Int Q with C∩g(X)=g(C') (2l<d, l+2l<d). Let N be a derived neighbourhood of C (a d-ball); M:=g^{-1}(N) is a derived neighbourhood of C' in X; M_q:=M∩σ_q is a 2l-ball; M_q∩M_{q'}=J:=M∩I', an arc, proper and unknotted in every M_q (codim ≥ 3); Fr M=⋃∂M_q, the spheres meeting pairwise exactly in ∂J; g|Fr M is an embedding into ∂N.
6. **Cone.** (M_q,J)≅ cone on (∂M_q,∂J) rel ∂M_q, compatibly on J (Zeeman unknotting of ball pairs + Alexander trick), so M ≅ cone(Fr M). Define G'=g outside Int M and G'|M = cone of g|Fr M into N=cone(∂N). G' is injective: g is injective off Int M with image off Int N, and the cone of an embedding is an embedding. ∎

**Why the arc matters.** If the engulfing cones were taken separately in each σ_q (M a disjoint union of balls), the spheres g(∂M_q)⊂∂N form a link whose pairwise linking class lies in π_{2l−1}(S^{d−2l−1}) (=ℤ for l=2, the algebraic intersection number of two cylinders), a genuine obstruction rel a neighbourhood of I'. Passing all cones through one point p of the common arc makes M a cone; the cone of a Hopf link is a wedge. This is the content of FWZ's use of Ĩ.

**Defects found in the thesis proof (all repaired above).**
- 4a. Lemma 3.56/3.57: "dim(S_σ∪Ĩ)=m−2" is false for m=2 (it is 1), and then the cone over S_σ∪Ĩ has dimension 2 in a 4-manifold, where 2·2<4 fails. m=2 is the base case (5,8). Repair: cone from a point p∈Ĩ plus the arc.
- 4b. Skopenkov's flag (S(g_1)⊂S(g) in Lemmas 41/42): true, for the reason he gives (cone C of dim ≤ l meets g(X) of dim 2l only in its base since 3l<d), provided the engulfing ball is the full preimage. The one-shot proof makes the question moot.
- 4c. Lemma 3.57 quotes Lickorish for "M_σ ∪_Ĩ M_σ' unknotted". The correct citation is that ∂M_σ∪∂M_σ' is a suspension; in the repaired proof no unknotting of the pair is needed, only coning.
- 4d. Proof of Thm 1.15: "apply an ambient isotopy so that G(S^{2m+1}) is standard, which implies EXTEMBED" is not an argument; the direct argument (embedding ⇒ map X→S^d∖hΣ^k≃S^l with rim degree = lk) is what is used below.
- Also: Remark 3.55.1 says "m ≥ 5"; Theorem 1.14/1.15 as printed ("d < 3(k+1)/2") include 2d=3k+2, which the text itself excludes.

## 5. Steps 5–7: the reduction for l even

Instance: K(a,b):=G ∪_{S_out=Y} X(a,b), φ_q=Σ_{i<j}a^q_{ij}[ι_i,ι_j], f_q=b_q[ι,ι], with a^q_{ij}∈{0,±1}, b_q∈{0,1}, at most three terms per q. Size is polynomial.

**Soundness.** h:K→S^d an embedding. X∪P_1 misses hΣ^k; S^d∖hΣ^k≃S^l (Zeeman, codim l+1≥3). deg(h|Y)=lk(hS_out,hΣ^k)=:c is odd by (P). With x_i=deg(h|S^l_i): through Cyl(f), h|A≃(cι)∘f; through Cyl(φ), h|A≃(h|W)∘φ. So Σa^q_{ij}x_ix_j[ι,ι]=c²b_q[ι,ι], and [ι,ι] has infinite order (l even): **Σ_{i<j}a^q_{ij}x_ix_j=c²b_q, c odd.**

**Completeness.** Given such (x,c): h_c and R from (R). The map X→R≃S^l with degrees x on W and c on Y exists. Theorem E in Q=Int R gives an embedding X⊂Int R with rim Y' of class c. Y' and a push-in of S_out are homotopic in R; a general position annulus rel X∪ends is embedded and meets X only in Y' (2(l+1)<d, (l+1)+2l<d); re-map the S_out-collar of P_1 onto (annulus ∪ product collar). The union is an embedding of K. ∎

**Algebra.** ∃x∈ℤ^s, c odd: Σaxx=c²b ⟺ ∃r∈ℤ_(2)^s: Σarr=b (r=x/c; conversely c = odd common denominator). Normal form from an arbitrary system over ℤ_(2): Skolem to {z=1, z=x+y, z=xy}; variables u,v,u' and X,X' per variable; equations uv=1, u'v=1, vX−vX'=0, uX−uu'=0, uZ−uX−uY=0, uZ−XY'=0. All monomials are products of two distinct variables, coefficients ±1, right sides in {0,1}; u is a unit, u'=u, X'=X, x=X/u. HTP(ℚ)≤HTP(ℤ_(2)) by E4 Lemma 1 (g(t)=t²+t+2; re-checked in the L2 audit). Binary input coefficients are expanded by a doubling chain w_{j+1}=w_j+w_j. Everything is polynomial time.

## 6. Step 8: l odd (l ≥ 3)

Instance: X(a,b) with Y=S^l_1∨S^l_2, f_q=b_q[ι'_1,ι'_2], **all a, b even**; K_2:=X ∪ G^{(1)} ∪ G^{(2)}, two disjoint copies of G glued to X along S_out^{(i)}=S^l_i (so they meet only in the wedge point of Y).

**Soundness.** Σ_1,Σ_2 are disjoint PL k-spheres. Ω_2=S^d∖(Σ_1⊔Σ_2) is simply connected with H_l=ℤ² (basis e_1,e_2 dual to linking), H_{d−1}=ℤ, so Ω_2≃(S^l∨S^l)∪e^{d−1} and π_{2l−1}(Ω_2)=π_{2l−1}(S^l∨S^l). C_{ij}:=lk(hS_out^{(i)},Σ_j). C_{ii} is odd by (P). For i≠j: S_out^{(i)}∼Σ^l_i+2T_i in the complement of Σ_j and Σ^l_i bounds Δ^{l+1}_i⊂L^{(i)}, disjoint from Σ_j, so C_{ij}=2lk(T_i,Σ_j) is even. Hence det C is odd. With h|W: ι_i↦x_ie_1+y_ie_2, [e_2,e_1]=−[e_1,e_2], 2[e,e]=0 and a,b even: **Σ_{i<j}a^q_{ij}(x_iy_j−x_jy_i)=det(C)·b_q**, det C odd. This is SKEW1 with an odd scalar.

**Completeness.** Given a solution with odd t: embed G^{(1)} with c=t and G^{(2)} with c=1 in disjoint balls, join R^{(1)}, R^{(2)} by a 1-handle to R_2≃S^l∨S^l, apply Theorem E (Y=S^l∨S^l) and glue by two annuli meeting in one point.

**Algebra.** SKEW1≡HTP(ℤ_(2)): E4 S1(ii) (Plücker pivot) re-derived line by line: p_01p_{α_iβ_j}=p_{0α_i}p_{1β_j}−p_{0β_j}p_{1α_i}; completeness with ξ=e_0−Σr_ie_{β_i}, η=te_1+Σw_ie_{α_i}, t=T², p_{α_iβ_j}=(Tr_i)(Tr_j)∈ℤ; integral bivector decomposable over ℚ is integrally decomposable. PASS.

Differences from Q-FWZ: FWZ's wedge of k-spheres is replaced by a disjoint union; "off-diagonal linking 0" is replaced by "even" (T_i may link Σ_j); the collar is attached at μ⊂Δ^{l+1}, which removes the need to push D off itself.

## 9. Prior art

arXiv API, 22 queries (dumps in [local reference omitted] log [local reference omitted] arxq2.log): authors Filakovský, Zhechev, Wagner, Skopenkov, Karasev, Tancer, Paták; phrases embeddability/undecidable, almost embedding, metastable range, Hilbert's tenth + embedding.
- FWZ is not on arXiv; no erratum or corrected version found.
- Skopenkov 2008.00492v2 (DCG 69 (2023)) still states undecidability in codim >1 as Conjecture; KS 2008.02523v3 (DCG 70 (2023)) still lists "almost can be deleted" and Problem 1.7 as open.
- Alkin 2206.13486 (2022): conditional NP-hardness of almost embeddability; no undecidability.
- Nothing found on a parity-doubling collar, on the embedding version of KS Thm 1.6, or on the fold lemma.
Verdict: the bypass and Theorem A− appear new **as far as an arXiv search can show**. Not searched: MathSciNet, zbMATH, SODA/SoCG proceedings 2021–2026, Skopenkov's home-page updates. Must cite: SS92, KS20, Sk20e (odd-scalar ≡ ℚ-with-odd-denominators, Moroz–Kogan), FWZ/Zhechev (X, the scaffold L, the role of Ĩ), CKMVW, ST17.
