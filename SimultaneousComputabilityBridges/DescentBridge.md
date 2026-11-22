# Multiplication tensor witnesses and their exact probe degrees

Let $K$ be a field and $A,B$ be nonzero finite-dimensional separable semisimple $K$-algebras of the same dimension. Give each geometric simple factor the color $n$ if it is a matrix algebra of degree $n$. Write $C=\operatorname{Isom}(Z_A,Z_B;\mathrm{colors})$ for the finite étale scheme of center isomorphisms preserving these degree strata. Its connected points $c$ have residue fields $F_c$ and canonical center isomorphisms $z_c$.

**Theorem 1 (natural normalization).** For every commutative $K$-algebra $R$, ordered multiplication-tensor isomorphisms $A_R\to B_R$ naturally correspond to
$$
B_R^\times\times B_R^\times\times
\bigsqcup_{z\in C(R)}\operatorname{Isom}_{Z_{B,R}\mathrm{-alg}}(z_*A_R,B_R).
$$
The residual isomorphism sheaf over $C$ is a torsor under the $C$-base change of $\operatorname{Aut}_{Z_B}(B)$, acting by postcomposition in the étale topology.

After an extension splitting the centers, $C$ is the finite set of degree-preserving bijections on geometric central idempotents, with its Galois action. This identifies the functor over all probes by étale descent. Separability gives $Z(A_R)=Z_A\otimes_K R$ and likewise for $B$, since the corresponding equality holds on split matrices after faithfully flat base change. A witness is a triple of linear isomorphisms $P,Q,T$ with $T(xy)=P(x)Q(y)$. Put $a=P(1)$, $b=Q(1)$. The identities $T=aQ=Pb$ imply that left multiplication by $a$ and right multiplication by $b$ are bijective. A one-sided inverse from surjectivity is two-sided by injectivity. Then
$$
\phi(x)=a^{-1}T(x)b^{-1}=a^{-1}P(x)=Q(x)b^{-1}
$$
is a unital multiplicative linear isomorphism. Conversely $P=L_a\phi,\ Q=R_b\phi,\ T=L_aR_b\phi$ give the tensor witness. These operations are inverse and commute with $R$-maps. Over an étale cover where the two transferred Azumaya algebras split, their matrix sizes agree by the colors, proving the torsor claim.

Decompose $Z_B\otimes_K F_c=\prod_j L_{cj}$. Let $\delta_{cj}\in\operatorname{Br}(L_{cj})$ be the difference of the two Brauer classes identified via $z_c$, and put
$$
e_c=\operatorname{lcm}_j\operatorname{per}(\delta_{cj}),\qquad h_c=[F_c:K]e_c .
$$
The zero class has period 1. Fix a finite Galois extension $S/K$ splitting both centers. It splits $C$, so all $F_c$ embed in $S$, and $S/F_c$ splits all $L_{cj}$.

**Theorem 2 (exact extension degrees).** Suppose either of the following holds.

- $K$ is a nonarchimedean local field and $\operatorname{Gal}(S/F_c)$ has cyclic Sylow subgroups for each $c$.
- $K$ is a global field and at every finite place $v$ of $F_c$ beneath a nonzero local invariant of some $\delta_{cj}$, the Galois group of a completion $S_w/F_{c,v}$ has cyclic Sylow subgroups.

Then the degrees of finite separable $E/K$ admitting a tensor isomorphism are exactly $\bigcup_c h_c\mathbb N_{>0}$. If $C\ne\varnothing$, the least witness degree is $\min_c h_c$, and the gcd of the witness degrees is $\gcd_c h_c$. For global $K$ the same calculation with $E$ linearly disjoint from a specified finite separable extension $M/K$ uses precisely the $c$ with $F_c\otimes_K M$ a field. For local $K$ the same assertion holds when $M\subset S$.

The global hypothesis only tests discrepancy support. In particular arbitrary finite Galois center splitting fields are allowed when the discrepancies are supported at archimedean places and places unramified in $S/F_c$.

*Proof.* A field point of $C$ is a branch $c$ and an embedding $F_c\hookrightarrow E$. The residual torsor has a point precisely when all $\delta_{cj}$ split over $L_{cj}\otimes_{F_c}E$, by equality of central simple algebras with the same degree and Brauer class. If $d=[E:F_c]$, the sum of the corestrictions from the field factors of this finite étale algebra, composed with restriction, is multiplication by $d$. Thus $e_c\mid d$.

The local avoidance lemma states that if $S'/F$ is finite Galois over a nonarchimedean local field with cyclic Sylow subgroups, a separable extension $U/F$ of any degree $d>0$ can be chosen disjoint from $S'$. Indeed Zassenhaus gives a group $C_a\rtimes C_b$ for coprime $a,b$. The characteristic subgroups of the cyclic normal subgroup and preimages from the cyclic quotient give a prime-factor normal series. Consequently maximal subgroups have prime index, by induction on the series using a first normal subgroup of prime order. For each prime $\ell$, all subgroups of index $\ell$ are conjugate. If $\ell\mid b$ a subgroup of index $\ell$ contains $C_a$ and is the unique such preimage from $C_b$. If $\ell\mid a$, the subgroup meets $C_a$ in its characteristic subgroup of index $\ell$ and surjects onto $C_b$. In the quotient by that characteristic subgroup the resulting groups are conjugate complements by Schur–Zassenhaus. Therefore the degree-$\ell$ subfields of $S'$, if present, have a common type, unramified or totally ramified. Allocate the whole $\ell$-part of $d$ to the opposite kind of degree. First take an unramified extension of the chosen residue degree, then a totally ramified extension of the remaining degree $r$. For $r>1$, $X^r+\pi X+\pi$ is separable Eisenstein in every characteristic. A nontrivial intersection with $S'$ would contain a prime-degree subfield by supersolvability and contradict the assigned degrees. Since $S'/F$ is Galois this proves disjointness. [Drinfeld, Appendix C](https://arxiv.org/abs/1509.06059).

Fix $c$ and a positive multiple $d$ of $e_c$. Locally the lemma over $F_c$ gives a degree-$d$ field disjoint from $S/F_c$. Each invariant over $L_{cj}$ is multiplied by $d$, so vanishes. It also gives the specified avoidance of $M\subset S$ whenever $F_c\otimes_K M$ is a field.

Globally use the lemma at every finite place under the support to choose a degree-$d$ local field disjoint from $S_w/F_{c,v}$. Every relevant completion of each $L_{cj}$ embeds into $S_w$, so this suffices for simultaneous disjointness at that place. At each real place under nonzero support prescribe $\mathbb C^{d/2}$, using $2\mid e_c$. At an auxiliary finite place prescribe a separable degree-$d$ Eisenstein polynomial, or a linear polynomial for $d=1$. For avoidance of $M$, choose this place completely split in the normal closure of $F_cM/F_c$ by Chebotarev, assuming $F_c\otimes_K M$ is a field. Weak approximation of coefficients and Krasner's lemma give a global polynomial with the prescribed completions. Eisenstein at the auxiliary place ensures irreducibility over $F_c$, and over $F_cM$ if avoidance was requested. At the finite support places every invariant is multiplied by $d$, and the complex completions kill the real invariants. Already zero invariants remain zero. Albert–Brauer–Hasse–Noether gives vanishing over each field factor of $L_{cj}\otimes_{F_c} E$, proving sufficiency. [Colliot-Thélène, Albert–Brauer–Hasse–Noether](https://www.numdam.org/item/AST_1992__209__215_0.pdf), [Chernousov–Rapinchuk–Rapinchuk, §3.1](https://doi.org/10.1007/s13373-013-0037-z).

## Shared probes, volume, and examples

**Corollary 3 (shared probes).** For a finite collection of pairs $(A_i,B_i)$, replace $C$ by the product of their center schemes. For a common branch $F_c$, form all discrepancies after base change to $F_c$ and take their single least common multiple $e_c$. Theorem 2 then gives exactly the degrees supporting a shared tuple of witnesses with the same hypotheses on the joint splitting field. The proof applies normalization factorwise and uses the same local extensions for all discrepancies. For two distinct quadratic fields $L_1,L_2/K$, each comparison $L_i$ with $K^2$ has a degree-2 witness. A shared probe must contain both fields, so its least degree is 4. In the finite étale case all discrepancies vanish and the weight of a branch is its residue field degree for any center group.

For a weighted example, take a quadratic number field extension $L/K$ and a quaternion division algebra $D/L$. Compare $A=D$ as $K$-algebra to $B=M_2(K)\times M_2(K)$. Both have dimension 8 over $K$. There is one center branch with residue field $L$. Its two discrepancies are the class of $D$ and its conjugate, both of period 2. The branch weight is 4, and the attainable degrees are exactly the multiples of 4.

For a common Galois center $L/K$, on probes disjoint from $L$ the branches that contribute are precisely the rational ones indexed by $g\in\operatorname{Gal}(L/K)$. Their weights are $\operatorname{per}(g[A]-[B])$. This gives the exact degree spectrum under the hypotheses of Theorem 2 and recovers the primary Brauer restriction test in prime–Helly descent. The sufficiency constructs probes even when every candidate center map has nontrivial discrepancy.

For finite étale $A,B$ over $\mathbb F_q$, the count of witnesses is zero if their field-factor degree multiplicities differ. If the common multiplicities are $a_\ell$, the count is
$$
\prod_{\ell\ge1}(q^\ell-1)^{2a_\ell}\ell^{a_\ell}a_\ell!.
$$
There are $a_\ell!$ block permutations for degree $\ell$, $\ell$ field automorphisms per such block, and two independent units.

**Corollary 4 (determinant-one probes).** In fixed $K$-bases, there is a union $C^+$ of connected components of $C$ such that the determinant-one witnesses are precisely normalized data above $C^+$ with $\det L_a=\det R_b=1$. Thus the determinant-one spectrum is the union in Theorem 2 restricted to $C^+$.

Over the part $Z_{A,n}$ of the center of degree color $n$, the corresponding Azumaya algebra has a canonical relative volume. The ordered matrix-unit wedge descends since conjugation has determinant 1 in dimension $n^2$. Choose bases of that volume and expand by ordered $K$-bases of the corresponding centers for $A$ and $B$. The determinant of an algebra isomorphism inducing $z$ is then
$$
d(z)=\prod_n (\det z_n)^{n^2}.
$$
Its semilinear part applies $z_n$ to $n^2$ copies of the center. The remaining map preserves the relative volume, so the norm of its center-linear determinant is 1. An arbitrary choice of fixed $K$-bases multiplies the entire formula by a fixed nonzero scalar. The locus of $d(z)=1$ is a union of components of the finite étale scheme because the equation can be checked in each residue field. Finally Theorem 1 gives $\det P\det Q/\det T=\det\phi$, implying the three claimed determinant conditions and their converse. Identity units lift every allowed normalized isomorphism.

## Integral multiplication tensors

**Theorem 5 (the integral branch formula).** Let $R$ be a Dedekind domain and $I,J$ invertible fractional ideals. Define the algebra
$$
A(I)=Re_1\oplus Re_2\oplus I\oplus I^{-1}
$$
with orthogonal idempotents $e_1,e_2$ summing to 1 and square-zero ideal $N=I\oplus I^{-1}$ with corners $e_1Ne_2=I$ and $e_2Ne_1=I^{-1}$. Its module is free of rank 4 by Steinitz. Under any extension to a Dedekind domain $R'$, the two possible types of multiplication-tensor isomorphism between $A(I)$ and $A(J)$ have precise obstructions.

- A witness preserving the quotient idempotents exists exactly when $[I]-[J]$ vanishes in $\operatorname{Pic}(R')$.
- A witness exchanging them exists exactly when $[I]+[J]$ vanishes in $\operatorname{Pic}(R')$.

Quotient action means the quotient action of the normalized algebra isomorphism. For $R=\mathcal O_K$ with $K$ a number field, the degrees of extensions whose integer rings admit these types are respectively
$$
\operatorname{ord}([I]-[J])\,\mathbb N_{>0},\qquad
\operatorname{ord}([I]+[J])\,\mathbb N_{>0}.
$$
The ordinary spectrum is the union. In particular $J=R$ recovers the exact integral principalization profile of the split cube using unmarked multiplication tensors.

The normalization of Theorem 1 initially uses only the unital associative algebra structure. In $A(I)_{R'}$, the ideal $N_{R'}$ is the set of nilpotent elements because $N_{R'}^2=0$ and the quotient $(R')^2$ is reduced. The intrinsic ideal is a bimodule over the quotient because it squares to zero. The primitive idempotents of the quotient are matched or exchanged, so the witness gives $IR'\cong JR'$ or $IR'\cong (JR')^{-1}$. Each such isomorphism of lines, its inverse dual on the other line, and the specified permutation define a unital algebra isomorphism. Both units can be taken equal to 1. These explicit transports give the accepting witnesses and extract line isomorphisms from them.

For the degree formula, an ideal class of order $m$ can vanish in degree $d$ only when $m\mid d$ by ideal norm. If $H^m=(a)$, adjoining a root $t$ of $X^m-a$ gives degree at most $m$. The equality of $m$-th powers shows by valuations that $(t)=H\mathcal O_E$. Necessity forces degree $m$, and further extensions of arbitrary degree realize every multiple.

**Proposition 6 (the split Azumaya case).** For same-rank $r>0$ projective modules $P,Q$ over a Dedekind domain $R$, the endomorphism algebras have free modules of rank $r^2$. Their multiplication tensors are isomorphic precisely when
$$
[\det Q]-[\det P]\ \in\ r\operatorname{Pic}(R).
$$
The determinant of $P^*\otimes P$ is trivial, so Steinitz implies freeness. A normalized algebra isomorphism makes $Q$ an $\operatorname{End}(P)$-module, and $H=\operatorname{Hom}_{\operatorname{End}(P)}(P,Q)$ is invertible with evaluation $P\otimes H\cong Q$. Where $P$ is free, matrix units split $Q$ into $r$ isomorphic rank-one summands and identify $H$ with the first summand, proving the evaluation locally. Conversely a line twist $Q\cong P\otimes H$ gives the algebra isomorphism, and Steinitz gives exactly the determinant criterion. If a split free rank-one summand of each module is marked by its projector and normalized isomorphisms must respect the projectors, evaluation sends that marked summand tensored with $H$ to the other marked summand and forces $H\cong R$. Conversely equality of determinant classes gives an isomorphism of complements by Steinitz and hence an isomorphism respecting the marks. The constructions commute with base change among the Dedekind probes. [Endomorphism sheaf isomorphisms of neutral Azumaya algebras](https://doi.org/10.1007/s13370-025-01261-5).

Witness normalization and projection to a discrete matching are the shared operations. For separable algebras the matching is a center isomorphism and the residual obstruction is a Brauer discrepancy. For $A(I)$ it is a permutation of the two quotient idempotents and the obstruction is an ideal class. The exact spectra express realizability of each branch. Products of matching schemes retain the information needed for a shared field witness. Standard ingredients include Albert’s field-level normalization of unital associative isotopy, finite étale Galois classification, central simple isomorphism by Brauer class and degree, and periods of reductive torsors. [Albert, Theorem 12](https://doi.org/10.2307/1968960). The witness-level correspondences and branch spectra here are prose proofs. [Stacks Project, finite étale schemes](https://stacks.math.columbia.edu/tag/04JI), [Gille–Szamuely, central simple algebras](https://www.math.ens.psl.eu/~benoist/refs/Gille-Szamuely.pdf), [Borovoi–Reichstein, reductive torsors](https://arxiv.org/abs/2403.07659).
