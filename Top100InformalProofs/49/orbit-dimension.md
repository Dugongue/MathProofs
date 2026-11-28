# Polynomial Calculus proofs from tensor orbit dimension

The main bounds distinguish flattening-rank witnesses and strict degeneration. The positive-characteristic statement retains the smooth-stabilizer hypothesis.

# Orbit dimension and raw Polynomial Calculus degree for tensor isomorphism

**Status.** Written proof. Three independent internal audits: the concise reduction passed with fixes (applied), the skeptic found no counterexample and contributed the shorter proof of §2, and the positive-characteristic audit proved the smooth case and found the family in §8 showing the smoothness hypothesis is needed for this method. No Dirichlet GRH or other external hypothesis is used.

## Question addressed

Galesi, Grochow, Pitassi and She ask for the correct Polynomial Calculus (PC) degree of rank-$r$ tensor isomorphism, and whether a bound polynomial in $r$ holds without the field equations $x^q-x$ ([arXiv 2305.19320, §7.1](https://arxiv.org/html/2305.19320#S7)). Their Theorem 6.1 gives Nullstellensatz degree $2^{O(r^2)}$ over algebraically closed fields, and $O(qr^2)$ only with field equations over $\mathbb F_q$. Earlier MathProofs results prove polynomial bounds for structured classes (all matrix pencils, thin and Morita-thin algebras, Lovitz–Petrov and Kruskal decompositions, frames, direct sums) and a matching linear lower bound for one $0,1$ family.

This note proves a polynomial-in-rank bound for a class defined by geometry rather than by structure: **every pair in which one tensor degenerates to the other** (characteristic zero; positive characteristic under a smoothness condition), and more generally every pair separated by the rank of the Lie orbit map. It also isolates the remaining case of Question 7.1 exactly.

## Conventions

Let $k$ be a field with algebraic closure $\bar k$. Tensors $T,S\in k^{n_1}\otimes k^{n_2}\otimes k^{n_3}$. Write $g=(X,Y,Z)$ and $g\cdot T=(X\otimes Y\otimes Z)T$, i.e. $(g\cdot T)_{ijk}=\sum X_{ii'}Y_{jj'}Z_{kk'}T_{i'j'k'}$. The literal system $\mathrm{TI}(T,S)$ consists of the cubic equations $(g\cdot T)_{ijk}-S_{ijk}=0$ and the quadratic equations $XX'-I=X'X-I=0$, and likewise for $Y,Z$. There are no field equations and no further variables. The GGPS convention lets $X^{\mathsf T}$ act; it differs from ours by renaming each variable matrix as its transpose, which changes no degree. In GGPS variables the transport map of Lemma 1 below reads $A\mapsto X'^{\mathsf T}AX^{\mathsf T}$; all ranks and degrees are unchanged. *PC degree* is the largest degree of a line of an ordinary PC refutation (linear combinations and multiplication by a variable). The pair is *geometrically negative* if $\mathrm{TI}(T,S)$ has no solution over $\bar k$. We write $r$ for the larger tensor rank (or border rank) of $T,S$ and $d_i(T)$ for the rank of the $i$-th flattening, so $d_i\le r$.

For $T$ in $V=V_1\otimes V_2\otimes V_3$ define the *Lie orbit map*
$$
L_T:\mathfrak{gl}(V_1)\oplus\mathfrak{gl}(V_2)\oplus\mathfrak{gl}(V_3)\to V,\qquad (A,B,C)\mapsto A^{[1]}T+B^{[2]}T+C^{[3]}T,
$$
where $A^{[1]}=A\otimes I\otimes I$ and similarly. It is the differential at the identity of the orbit map $g\mapsto g\cdot T$, and it is a constant matrix of size $\dim V\times\sum_i\dim V_i^2$.

## Results

**Theorem A (covariant rank principle).** Let $T,S$ have the same format and suppose $\rho=\operatorname{rank}L_T\ne\operatorname{rank}L_S$; put $\rho_{\min}=\min(\operatorname{rank}L_T,\operatorname{rank}L_S)$. Then $\mathrm{TI}(T,S)$ has a PC refutation over $k$ of degree at most $5\rho_{\min}+8$, and even a Nullstellensatz refutation of degree at most $3\rho_{\min}+6$ (§2). This holds over every field, for arbitrary (not necessarily concise) tensors.

**Theorem B (degenerations).** Suppose $S$ lies in the Zariski closure of the $\mathrm{GL}_{n_1}(\bar k)\times\mathrm{GL}_{n_2}(\bar k)\times\mathrm{GL}_{n_3}(\bar k)$-orbit of $T$ but not in the orbit, or the same with $T,S$ exchanged. If $\operatorname{char}k=0$, then $\mathrm{TI}(T,S)$ has a PC refutation of degree $O(r^2)$, with an absolute constant, independent of the ambient dimensions $n_i$. If $\operatorname{char}k=p>0$ the same conclusion holds provided the stabilizer group scheme of the concise part of the non-degenerate tensor is smooth.

**Corollary C (the remaining case).** Let $\operatorname{char}k=0$ and let $T,S$ be geometrically negative with equal flattening ranks. Either $\mathrm{TI}(T,S)$ has a refutation of degree $O(r^2)$, or the concise orbits have equal dimension, neither concise tensor lies in the other's orbit closure, and $\mathrm{TI}(T,S)$ has a refutation of degree at most $\max\{3\sigma, C_0\}$, where $C_0$ is an absolute constant and $\sigma=\sigma(T,S)$ is the least degree of a polynomial on the concise space vanishing on the orbit closure of the concise part of $T$ but not at that of $S$.

Consequently, in characteristic zero Question 7.1 has a polynomial answer as soon as *equal-dimensional* tensor orbits of rank $r$ are separated by equations of degree $\mathrm{poly}(r)$ vanishing on one orbit closure. Any polynomial lower bound beyond $O(r^2)$ must come from pairs with equal orbit dimension; the linear lower-bound family of [Ordinary tensor transfer fallout](https://github.com/Dugongue/MathProofs/blob/main/OrdinaryTensorTransferFallout/Degree.md) is consistent with this.

## 1. The transport identity

**Lemma 1.** For every $(A,B,C)$, and for $g$ invertible,
$$
L_{g\cdot T}(A,B,C)=g\cdot L_T\big(X^{-1}AX,\;Y^{-1}BY,\;Z^{-1}CZ\big).
$$
*Proof.* $A^{[1]}(X\otimes Y\otimes Z)T=(AX\otimes Y\otimes Z)T=(X\otimes Y\otimes Z)(X^{-1}AX)^{[1]}T$, and similarly in the other slots. $\square$

Define the polynomial matrices $\Phi=X\otimes Y\otimes Z$ (entries of degree $3$) and $\Psi$, the block-diagonal matrix of $(A,B,C)\mapsto(X'AX,Y'BY,Z'CZ)$ in the matrix-unit bases (entries $(X'E_{ab}X)_{cd}=X'_{ca}X_{bd}$, of degree $2$). Define $\Phi^\ast=X'\otimes Y'\otimes Z'$ and $\Psi^\ast$ for $(A,B,C)\mapsto(XAX',YBY',ZCZ')$.

**Lemma 2.** Every entry of $L_S-\Phi L_T\Psi$ has a PC derivation from $\mathrm{TI}(T,S)$ of degree at most $5$, and every entry of $L_T-\Phi^\ast L_S\Psi^\ast$ has one of degree at most $8$.

*Proof.* The column of $\Phi L_T\Psi$ at $E_{ab}$ in the first summand is the vector $(XX'E_{ab}X\otimes Y\otimes Z)T$, whose entries have degree $5$. Replacing $XX'$ by $I$ uses the axioms $XX'-I$ multiplied by monomials of degree $3$, in degree $5$, and yields $(E_{ab}X\otimes Y\otimes Z)T=E_{ab}^{[1]}(g\cdot T)$. Its entries are constant combinations of the cubics $(g\cdot T)_{ijk}$, which the action axioms replace by $S_{ijk}$ in degree $3$; the result is the column $E_{ab}^{[1]}S$ of $L_S$. The other summands are identical. For the second identity the column of $\Phi^\ast L_S\Psi^\ast$ at $E_{ab}$ is $(X'XE_{ab}X'\otimes Y'\otimes Z')S$, of degree $5$. Multiply each action axiom $S_{ijk}-(g\cdot T)_{ijk}$ by monomials of degree $5$ to replace $S$ by $g\cdot T$, obtaining $(X'XE_{ab}X'X\otimes Y'Y\otimes Z'Z)T$ in degree $8$. Then the inverse axioms $X'X-I$, $Y'Y-I$, $Z'Z-I$ reduce it, factor by factor and never raising the degree above $8$, to $E_{ab}^{[1]}T$. $\square$

## 2. Proof of Theorem A

Assume first $\rho=\operatorname{rank}L_T<\operatorname{rank}L_S$ and put $s=\rho+1$. Choose row and column sets $I,J$ of size $s$ such that the constant matrix $N=(L_S)_{IJ}$ is invertible. Factor $L_T=UV$ over $k$ with $U$ of size $\dim V\times\rho$ and $V$ of size $\rho\times\sum\dim V_i^2$. Set
$$
P=N^{-1}\Phi_{I,\ast}U\quad(s\times\rho,\ \text{entries of degree }3),\qquad Q=V\Psi_{\ast,J}\quad(\rho\times s,\ \text{entries of degree }2).
$$
By Lemma 2 each entry of $R-I_s$, with $R=PQ$, is a constant linear combination of entries of $L_S-\Phi L_T\Psi$, hence has a derivation of degree at most $5$.

Telescoping the rows gives the polynomial identity
$$
\det R-\det I_s=\sum_{t=1}^{s}\det(e_1,\dots,e_{t-1},R_t-e_t,R_{t+1},\dots,R_s),
$$
where $R_t$ is the $t$-th row. Expanding the $t$-th term along its $t$-th row writes it as $\sum_j c_{tj}\,(R-I)_{tj}$ with cofactors $c_{tj}$ of degree at most $5(s-t)\le5(s-1)$. Multiply the degree-$5$ derivation of $(R-I)_{tj}$ by the monomials of $c_{tj}$; every line has degree at most $5s$. Summing derives $\det R-1$. Since $R=PQ$ factors through dimension $\rho<s$, the Cauchy–Binet formula gives $\det R=0$ as a polynomial over any field. The derived line is therefore $-1$, a refutation of degree $5s=5\rho+5$.

If instead $\rho'=\operatorname{rank}L_S<\operatorname{rank}L_T$, repeat the argument with the roles exchanged, using $L_T\equiv\Phi^\ast L_S\Psi^\ast$ (Lemma 2, degree $8$). The entries of the new $R-I$ have derivations of degree at most $8$ and the cofactors have degree at most $5(s-1)$, so the refutation has degree at most $5\rho'+8$. $\square$

**Shorter proof with a better constant (found during the skeptical audit).** Let $\rho=\operatorname{rank}L_T<\operatorname{rank}L_S$ and let $f(U)$ be a $(\rho+1)$-minor of $L_U$ that is nonzero at $U=S$. The entries of $L_U$ are linear in $U$, so $\deg f=\rho+1$. By Lemma 1, $\operatorname{rank}L_{g\cdot T}=\rho$ for every invertible $g$ over $\bar k$, so $f(g\cdot T)$, a polynomial in the entries of $X,Y,Z$, vanishes on the dense set of invertible triples and is the zero polynomial. The telescoping argument of §5 then derives the nonzero constant $f(S)=f(S)-f(g\cdot T)$ from the action axioms alone, in degree $3(\rho+1)$, a Nullstellensatz refutation. If instead $\operatorname{rank}L_S<\operatorname{rank}L_T$, apply the same argument to the reverse action $T=(X',Y',Z')\cdot S$, derivable in degree $6$ (Lemma 3), for degree at most $3(\rho'+1)+3$. Lemma 5 removes the constants of $\bar k$. Hence Theorem A holds with the bound $3\rho_{\min}+6$, and Theorem B with $\max(6,9r^2)$.

This is a special case of the *orbit-separation principle*: if a polynomial $f$ of degree $\sigma$ vanishes on the orbit $G\cdot T$ over $\bar k$ and $f(S)\ne0$, then $\mathrm{TI}(T,S)$ refutes in degree $3\sigma$, and in degree $3\sigma+3$ with the roles of $T,S$ exchanged. Theorem A is the case of rank minors of the Lie orbit map; Corollary C is the case of equations of the orbit closure.

*Remark.* The Cauchy–Binet proof above also applies to any matrix-valued covariant $M(T)$ with a transport congruence $M(S)\equiv P(g)M(T)Q(g)$ derivable in degree $D_0$ from $\mathrm{TI}(T,S)$, with $\deg P=p$, $\deg Q=q$: rank differences give refutations of degree at most $(p+q)\min\operatorname{rank}+D_0$. Flattening ranks, Koszul–Young flattenings with fixed exterior power, and the dimensions of the centroid and of the derivation algebra are covariants of this kind.

## 3. From the ambient system to concise tensors

**Lemma 3 (concise reduction; [*Arbitrary tensor direct sums*, §1](https://github.com/Dugongue/MathProofs/blob/main/TensorPCRankBounds/DirectSums.md)).** If the flattening ranks of $T$ and $S$ differ in some mode, $\mathrm{TI}(T,S)$ has a refutation of degree at most $\max(6,2r)$ (Cauchy–Binet), or $2$ (traces) when the difference of the ranks is nonzero in $k$. If they agree, $d=(d_1,d_2,d_3)$, choose constant bases adapted to the supports of $T$ and of $S$. Writing each variable matrix in block form, the off-support blocks $X_{21}$ and $X'_{21}$ (rows outside the target support, columns inside the source support, and the reverse for $X'$) vanish by derivations of degree at most $5$ and $6$ respectively; the second uses the reverse action $T=(X',Y',Z')\cdot S$, which is itself derived in degree $6$ by multiplying the action axioms by degree-$3$ monomials in $X',Y',Z'$ and reducing $X'X,Y'Y,Z'Z$ to identities. Removing terms multiplied by the vanished blocks, the supported blocks satisfy $\bar X\bar X'=\bar X'\bar X=I_{d_1}$ (and likewise for $Y,Z$) in degree at most $6$, and the concise action equations $(\bar X,\bar Y,\bar Z)\cdot\bar T=\bar S$ are a subset of the original axioms. The blocks $X_{12},X_{22}$ and their primed versions stay free and occur in no output equation. Every degree is independent of the ambient dimensions $n_i$. (In that source the letter $n$ denotes the largest flattening rank, not the ambient dimension.)

Lemma 3 is reused from that earlier proof. An independent line-by-line audit confirmed it with the constants above and noted that the source should state the derivation of the reverse action explicitly. Since substituting constant linear forms does not raise degree, any degree-$D$ refutation of $\mathrm{TI}(\bar T,\bar S)$ becomes a refutation of $\mathrm{TI}(T,S)$ of degree $\max\{D,C_0\}$ for an absolute constant $C_0$.

**Lemma 4 (degenerations of concise parts).** Suppose $S\in\overline{G\cdot T}$ in the ambient space, with $G=\prod_i\mathrm{GL}_{n_i}(\bar k)$, and $d(S)=d(T)=d$. Then the concise part $\bar S$ lies in the closure of $L\cdot\bar T$ in $W_d=\bar k^{d_1}\otimes\bar k^{d_2}\otimes\bar k^{d_3}$, where $L=\prod_i\mathrm{GL}_{d_i}(\bar k)$. If $S\notin G\cdot T$ then $\bar S\notin L\cdot\bar T$.

*Proof.* The tensors with flattening ranks exactly $d$ form a locally closed $G$-stable subset $\mathcal Z_d$, and taking supports gives a $G$-equivariant map to the product of Grassmannians $\prod_i\mathrm{Gr}(d_i,n_i)$. With $P\subseteq G$ the stabilizer of the coordinate subspaces, $\mathcal Z_d=G\times^P F$, where $F\subseteq W_d$ is the open set of concise tensors. Block upper-triangular elements of $P$ act on a tensor supported in the coordinate subspaces through their diagonal blocks only, so $P$ acts on $F$ through $L$. For the closed $L$-stable set $K=\overline{L\cdot\bar T}\cap F$ of $F$, the set $G\times^P K$ is closed in $\mathcal Z_d$, since its preimage $G\times K$ in $G\times F$ is closed and $G\times F\to G\times^P F$ is a quotient map. It contains $G\cdot T$, so it contains $S$, and the fibre over the coordinate point gives $\bar S\in K$ after moving $S$'s support to the coordinate subspaces by an element of $G$. The last statement holds because an $L$-isomorphism of concise parts extends to a $G$-isomorphism. $\square$

## 4. Proof of Theorem B

If flattening ranks differ, Lemma 3 refutes in degree $O(r+1)$. Otherwise, by Lemma 4, $\bar S\in\overline{L\cdot\bar T}\setminus L\cdot\bar T$ over $\bar k$, after exchanging $T$ and $S$ if necessary. Orbits of an algebraic group acting on a variety are locally closed, and $\overline{L\cdot\bar T}\setminus L\cdot\bar T$ is a union of orbits of strictly smaller dimension, in every characteristic. Hence $\dim L\cdot\bar S<\dim L\cdot\bar T$.

For any concise $U$, $\ker L_U$ is the Lie algebra of the scheme-theoretic stabilizer of $U$, which contains the Lie algebra of the reduced stabilizer. Hence $\operatorname{rank}L_U\le\dim L\cdot U$, with equality exactly when the stabilizer scheme is smooth. In characteristic zero every group scheme of finite type is smooth (Cartier). Thus
$$
\operatorname{rank}L_{\bar S}\le\dim L\cdot\bar S<\dim L\cdot\bar T=\operatorname{rank}L_{\bar T},
$$
where the equality on the right uses smoothness of the stabilizer of $\bar T$ only; it is automatic in characteristic zero and is the stated hypothesis in characteristic $p$. Ranks of constant matrices do not change under field extension, so this is a statement over $k$. Theorem A applied to the concise system gives degree at most $5\operatorname{rank}L_{\bar S}+8$. Since the two-dimensional torus $\{(a I,bI,cI):a+b+c=0\}$ lies in $\ker L_{\bar S}$, $\operatorname{rank}L_{\bar S}\le d_1^2+d_2^2+d_3^2-2\le3r^2-2$, so the degree is at most $15r^2-2$. Lemma 3 transfers it to the ambient system, with overall bound $\max(6,15r^2-2)$. $\square$

The bound is linear in the smaller orbit dimension, and it holds equally with $r$ the border rank, since $d_i\le$ border rank.

## 5. Proof of Corollary C

If flattening ranks agree and $\operatorname{rank}L_{\bar T}\ne\operatorname{rank}L_{\bar S}$, Theorem A and Lemma 3 apply. Otherwise both orbits have the same dimension in characteristic zero. Since the boundary of an orbit closure consists of orbits of smaller dimension and $\bar S\notin L\cdot\bar T$, we get $\bar S\notin\overline{L\cdot\bar T}$, and symmetrically. Choose $f\in\bar k[W_d]$ of degree $\sigma$ vanishing on $\overline{L\cdot\bar T}$ with $f(\bar S)\ne0$. The polynomial $f(g\cdot\bar T)$ in the entries of $(\bar X,\bar Y,\bar Z)$ vanishes on the dense set $L$ of $\mathrm{Mat}_{d_1}\times\mathrm{Mat}_{d_2}\times\mathrm{Mat}_{d_3}$, so it is the zero polynomial. For each monomial $m=\prod_e u_e$ of $f$, the telescoping identity
$$
\prod_e a_e-\prod_e b_e=\sum_t\Big(\prod_{e<t}a_e\Big)(a_t-b_t)\Big(\prod_{e>t}b_e\Big)
$$
with $a_e=\bar S_e$ (constants) and $b_e=(g\cdot\bar T)_e$ (cubics) derives $m(\bar S)-m(g\cdot\bar T)$ from the action axioms in degree at most $3\sigma$. Summing derives $f(\bar S)-f(g\cdot\bar T)=f(\bar S)$, a nonzero constant. This refutation uses only the action equations; its coefficients lie in a finite extension of $k$, and Lemma 5 below returns it to $k$ at the same degree. $\square$

**Lemma 5 (coefficient descent).** For a system over $k$ and an extension $K\supseteq k$, a degree-$D$ PC refutation over $K$ implies one over $k$ of the same degree.

*Proof.* The set of polynomials of degree at most $D$ derivable in degree at most $D$ is the smallest subspace $\mathcal V_D$ of the degree-$\le D$ polynomials containing the axioms of degree $\le D$ and closed under multiplication by variables whenever the product still has degree $\le D$. It is obtained by iterating linear spans, so $\mathcal V_D(K)=\mathcal V_D(k)\otimes_kK$. If $1\in\mathcal V_D(K)$ then $1\in\mathcal V_D(k)$, since a $k$-subspace $W$ satisfies $(W\otimes_kK)\cap k[x]=W$. $\square$

## 6. Comparison with previous results

- GGPS Theorem 6.1: Nullstellensatz degree $2^{O(r^2)}$, or PC degree $O(qr^2)$ with field equations over $\mathbb F_q$. Theorem B gives $O(r^2)$ raw PC degree with no field equations, for every degeneration pair, over every field of characteristic zero; in positive characteristic under smoothness of one stabilizer.
- Earlier structured bounds (matrix pencils, thin algebras, decompositions, frames, direct sums) each require a structural hypothesis on one tensor. Theorem B has no structural hypothesis; its hypothesis is a geometric relation between the two tensors. The classes overlap but neither contains the other.
- Closest precedent: the [*Determinantal frames*](https://github.com/Dugongue/MathProofs/blob/main/TensorPCRankBounds/DeterminantalFrames.md) proof compares the dimension of the Lie stabilizer of one mode's minor space through projected conjugations and a rectangular rank contradiction. That is one specific covariant inside a structural argument. The general principle that any orbit-dimension difference refutes in degree linear in the rank, and its consequence for all degeneration pairs, does not appear there. A literature search (GGPS, Berkholz–Grohe-type rank arguments, Grochow–Qiao, recent invariant-degree work) found no orbit-dimension PC bound. Priority remains provisional.
- GGPS show that PC needs linear degree to compare matrix ranks. Theorem A shows the matching upper bound suffices to detect any difference in orbit dimension, and Corollary C shows that the only remaining obstacle to a polynomial answer in characteristic zero is the degree of equations separating equal-dimensional orbit closures.

## 7. Small cases

In the $2\times2\times2$ format, $\operatorname{rank}L$ equals $8$ at the unit tensor $e_1^{\otimes3}+e_2^{\otimes3}$ and $7$ at the W-tensor, which lies in the boundary of the unit tensor's orbit, so Theorem A refutes this pair in degree $3\cdot8+6$ at most. In characteristic $2$, $\operatorname{rank}L_W=6$ while its orbit still has dimension $7$. Thus the stabilizer scheme of $W$ is not smooth there, and the inequality $\operatorname{rank}L_U\le\dim G\cdot U$ can be strict. This does not affect Theorem B, whose hypothesis concerns only the larger orbit, but it shows that the smoothness condition is substantive in positive characteristic. The only equal-dimensional distinct orbits in $2\times2\times2$ are the three biseparable orbits of dimension $5$. Flattening ranks separate them, so they are not core cases of Corollary C. Genuine core cases first occur among the continuous families of $3\times3\times3$ tensors.

## 8. The smoothness hypothesis is necessary for the rank-of-$L$ route

For $S$ in the boundary of $G\cdot T$, lower semicontinuity of rank (the entries of $L_U$ are linear in $U$) gives $\operatorname{rank}L_S\le\operatorname{rank}L_T$ in every characteristic. Write $\delta_U=\dim G\cdot U-\operatorname{rank}L_U\ge0$ for the non-smoothness defect. Then
$$
\operatorname{rank}L_T-\operatorname{rank}L_S=(\dim G\cdot T-\dim G\cdot S)-(\delta_T-\delta_S),
$$
so Theorem A applies whenever $\delta_T<\dim G\cdot T-\dim G\cdot S$; smoothness ($\delta_T=0$) is the case used in Theorem B.

**The hypothesis cannot simply be dropped.** For each prime $p$, consider the $2\times(p+1)\times(p+1)$ pencils
$$
T=e_1\otimes I+e_2\otimes\big(J_p(0)\oplus(1)\big),\qquad S=e_1\otimes I+e_2\otimes J_{p+1}(0).
$$
Both are concise. Companion matrices of $(x-\lambda)^p(x-\mu)$ with $\lambda\ne\mu$ are regular and lie in the orbit of $T$ after a Möbius change of the pencil coordinates; as $\lambda,\mu\to0$ they converge to the companion matrix of $x^{p+1}$, which is conjugate to $J_{p+1}(0)$. So $S$ lies in the boundary of $G\cdot T$. An independent audit computed by hand that in characteristic $p$, $\operatorname{rank}L_T=\operatorname{rank}L_S=2(p+1)^2-p$. In the smallest case, $2\times3\times3$ over characteristic $2$, both ranks are $16$ while $\dim G\cdot T=17$ and $\dim G\cdot S=16$. The degeneration argument was rechecked here; the rank computation is the auditor's hand calculation. This pair is still refuted in linear degree by the [theorem for all matrix pencils](https://github.com/Dugongue/MathProofs/blob/main/TensorPCRankBounds/MatrixPencils.md), so it limits only the method, not the degree. No counterexample exists in the $2\times2\times2$ and $2\times2\times3$ formats in any characteristic.

## 9. What remains open

Question 7.1 is not closed. The exact remaining case in characteristic zero is a geometrically negative concise pair with $\operatorname{rank}L_{\bar T}=\operatorname{rank}L_{\bar S}$ (equal orbit dimension). For it, Corollary C bounds the degree by three times the degree of an equation separating one orbit closure from the other tensor, but no polynomial bound on that degree is known. In positive characteristic the degeneration case with non-smooth stabilizers is also open here.
