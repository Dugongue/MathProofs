# Counterexamples to local–global existence of symmetric determinantal representations in every degree at least five

**Theorem.** For every integer $d\ge5$ and every number field $k$, there exist a finite extension $K/k$ and a smooth plane curve $C/K$ of degree $d$, with a $K$-rational point, such that $C$ has a symmetric linear determinantal representation over each completion $K_v$ and has none over $K$. One may take $[K:k]\le |G_d|$, where $G_d$ is the finite symplectic or orthogonal group in Section 1.

This answers Problem 1.6(2) of Ishitsuka and Ito in every degree asked. The number field $K$ may depend on $d$. [Ishitsuka and Ito, The local-global principle for symmetric determinantal representations of smooth plane curves, Problem 1.6(2)](https://arxiv.org/pdf/1412.8336)

Their separate question about quartics over specified base fields was answered in the follow-up. [Ishitsuka, Ito, Ohshita, Taniguchi, and Uchida, Theorem 8.1 and Example 8.2](https://arxiv.org/pdf/2002.10203)

## 1. Curves carrying the full allowed Galois image and the required theta characteristics

Put $g=(d-1)(d-2)/2$. Let $U$ be the open of the projective space of degree-$d$ ternary forms parametrizing smooth curves, and let $X\to U$ be the universal curve. A point of $X$ is a plane curve with a marked point. The variety $X$ is rational over $k$. It is a nonempty open in the projective bundle over $\mathbb P^2_k$ whose fiber at $p$ parametrizes forms vanishing at $p$, obtained from the kernel of the surjective evaluation from the constant bundle of degree-$d$ forms to $\mathcal O_{\mathbb P^2}(d)$.

The geometric monodromy on the $2$-torsion of the universal Jacobian over $U$ is
$$
G_d =
\begin{cases}
\operatorname{Sp}_{2g}(\mathbb F_2),&d\ \text{even},\\
\operatorname O(q),&d\ \text{odd}.
\end{cases}
$$
For odd $d$, $q$ is the Riemann–Mumford quadratic form of the canonical theta characteristic $\theta_*=\mathcal O_C((d-3)/2)$. Indeed, Beauville computes integral homological monodromy as the full integral symplectic group or the inverse image of the indicated orthogonal group under reduction modulo $2$. The reduction map on the integral symplectic group is surjective. Comparison with the étale finite covering computes geometric monodromy on $J[2]$. For odd $d$ the relative class of $\theta_*$ is defined on the whole parameter space, so arithmetic monodromy also preserves $q$. In either parity, the finite étale cover of $U$ parametrizing compatible frames of $J[2]$ is a $G_d$-torsor with geometrically connected total space. Its pullback to $X$ remains geometrically connected because its projection to the original cover is smooth proper with geometrically integral fibers. [Beauville, Le groupe de monodromie des familles universelles d'hypersurfaces et d'intersections complètes, Theorem 4 and Proposition 3](https://math.univ-cotedazur.fr/u/beauvill/pubs/mono.pdf)

On the universal pointed family over $X$, the finite étale scheme of theta characteristics is the inverse image of the relative canonical class under doubling on the relative Picard scheme. It has a universal rigidified line bundle because the family has a section. Theta parity is locally constant and equals the Arf invariant of the corresponding quadratic form on $J[2]$. By Beauville's monodromy, the even theta-characteristic scheme has a single geometrically connected component after removing the canonical section when that section has even parity. For odd $d$ this also follows directly from transitivity of $\operatorname O(q)$ on its nonzero vectors of either given quadratic value and the identity
$$
\operatorname{Arf}(q_v)=\operatorname{Arf}(q)+q(v),
\qquad q_v(x)=q(x)+\langle x,v\rangle.
$$
For even $d$ use transitivity of the symplectic group on quadratic refinements of Arf invariant zero. The theta cover component in question is smooth and geometrically integral. [Beauville, Proposition 3](https://math.univ-cotedazur.fr/u/beauvill/pubs/mono.pdf) [Ishitsuka and Ito, Proposition 6.2](https://arxiv.org/pdf/1412.8336)

Effectivity is a closed condition on that component by upper semicontinuity of $h^0$. This closed locus is proper. Over $\mathbb C$, choose a general projective plane of symmetric $d\times d$ matrices. The symmetric determinant hypersurface has singular locus the rank-at-most-$d-2$ locus, of codimension $3$ in the ambient space of symmetric matrices. A general plane avoids it and, by Bertini, meets the smooth locus transversely. The result is a smooth plane curve with a symmetric determinantal representation. Its corresponding non-effective theta characteristic is even and, in odd degree, differs from the effective canonical one. Marking any complex point of this curve supplies a point on the even component outside the effectivity locus. [Beauville, Determinantal hypersurfaces, Proposition 4.2](https://arxiv.org/abs/math/9910030)

Because the component is integral and finite étale over $X$, the image of its proper closed effectivity locus is proper and closed in $X$. Explicitly, every proper closed subset of the integral component has dimension strictly less than $\dim X$, and a finite map is closed with zero-dimensional fibers. Thus there is a nonempty open $X^\circ$ where all even theta characteristics are geometrically non-effective, apart from $\theta_*$ when that characteristic is even. The restricted frame cover remains geometrically connected. Since $X^\circ$ has a rational affine-space chart, Hilbert irreducibility gives a $k$-point of $X^\circ$ with a connected fiber of the finite étale $G_d$-torsor. Such a fiber implies full image $G_d$ on $J[2]$. Denote the resulting smooth pointed curve by $C_0/k$.

## 2. A subgroup whose elements fix non-effective theta characteristics

We need a subgroup $H\subseteq G_d$ with two properties. Each one of its elements fixes a geometrically non-effective even theta characteristic. There is no such characteristic fixed by the whole subgroup.

If $d$ is even, take the subgroup of $\operatorname{Sp}_{2g}(\mathbb F_2)$ in Ishitsuka–Ito Lemma 6.6. It has precisely the stated fixed-point properties for quadratic refinements of Arf invariant zero. All corresponding theta characteristics on $C_0$ are non-effective by construction.

If $d$ is odd and $\theta_*$ is odd, the same argument applies inside $\operatorname O(q)$. In the proof of Lemma 6.6 the authors explicitly construct their subgroup inside $\operatorname O(Q)$ for a quadratic form $Q$ of Arf invariant one. Conjugate this group to a subgroup of $\operatorname O(q)$ using a symplectic isometry between the two refinements. [Ishitsuka and Ito, Lemma 6.6 and its proof](https://arxiv.org/pdf/1412.8336)

It remains to handle odd $d$ with $\theta_*$ even. The even non-effective theta characteristics of $C_0$ are identified with the nonzero isotropic vectors for $q$. We have $d\ge7$ here since $h^0(\mathcal O_{C_0}(1))=3$ for $d=5$, so $g\ge15$. We construct an orthogonal action with the required fixed-point behavior. Let $B=(\mathbb Z/3)^2$, and for each of its four order-$3$ subgroups $D$ choose a surjective $\chi_D:B\to\mathbb Z/3$ with kernel $D$. Take two copies of the anisotropic binary quadratic plane for each $D$. On each of the two copies use the action through $\chi_D$, with a generator acting by cyclically permuting the three nonzero vectors. The resulting orthogonal direct sum has eight planes and Arf invariant $0$. Every $b\in B$ acts trivially on a matched pair of planes, because every element lies in some $D$. A sum of one nonzero vector from each plane of that pair is a nonzero isotropic fixed vector. The common fixed subspace of $B$ is zero, since the action through each $\chi_D$ has no nonzero common fixed vectors.

If $g$ is even, add $g-8$ anisotropic planes, with the action through any one of the same nontrivial characters. Their number is even, so the full form still has Arf invariant zero, and the common fixed subspace is zero. If $g$ is odd, add $g-9$ such planes and one hyperbolic plane. Enlarge the group to $B\times\mathbb Z/2$, with the new factor trivial on the anisotropic summands. On the hyperbolic plane let $B$ act trivially and let the new generator swap a hyperbolic basis $e,f$. The common fixed subspace now is the line spanned by $e+f$, with $q(e+f)=1$. Every element of the enlarged group still fixes a nonzero isotropic vector on the original eight planes. The total form has dimension $2g$ and Arf invariant zero in both constructions, hence it is isometric to $q$. Transport the group along an isometry to obtain the required $H\subseteq\operatorname O(q)$.

## 3. Preserving the global image while making decomposition groups cyclic

Let $E/k$ be the splitting field of $J(C_0)[2]$, and put $M=E^H$. Thus $E/M$ is Galois with group $H$, and $C_0$ has Galois image $H$ over $M$. We construct a finite $K/M$ linearly disjoint from $E/M$ such that every decomposition group of $EK/K$ is cyclic.

Let $S$ be the finite set of finite places of $M$ ramified in $E$. If $S$ is empty, take $K=M$. Otherwise, let $n=|H|$. For each $v\in S$, choose one $w\mid v$ in $E$. Its local degree divides $n$, so there is a degree-$n$ extension $F_v/M_v$ containing $E_w$, obtained by an unramified extension of $E_w$ of the required remaining degree. Pick a finite place $v_0\notin S$. Approximate a monic primitive-element polynomial for each $F_v/M_v$ by the same monic polynomial $P\in M[T]$ of degree $n$, close enough by Krasner's lemma that $M_v[T]/(P)\cong F_v$. At $v_0$ impose an Eisenstein polynomial by weak approximation. Thus $P$ is irreducible over $M$ and $K=M[T]/(P)$ is a field. It remains Eisenstein at every completion of $E$ over $v_0$ since $v_0$ is unramified, so $P$ is irreducible over $E$. This proves linear disjointness and $\operatorname{Gal}(EK/K)\cong H$. The bound follows from $[M:k]=|G_d|/|H|$ and $[K:M]\le |H|$.

For $v\in S$, the unique completion of $K$ above $v$ contains a copy of the Galois local extension $E_w/M_v$, so the decomposition group after base change is trivial. Elsewhere finite decomposition groups are subgroups of unramified cyclic groups. Archimedean decomposition groups have order at most two. This is the ramification step in the Ishitsuka–Ito construction, with the disjointness requirement enforced by an Eisenstein place. [Ishitsuka and Ito, proof of Theorem 1.2](https://arxiv.org/pdf/1412.8336)

## 4. Reading off the existence obstruction

For $C=(C_0)_K$, the absolute Galois action on theta characteristics factors through the action on the quadratic refinements of the Weil pairing on $J[2]$. The non-effective even characteristics are preserved by field extension and have precisely the fixed-point behavior in Section 2. Every local image is cyclic. A generator fixes a geometrically non-effective even theta characteristic, which therefore descends to $K_v$ because $C(K_v)$ is nonempty. Thus $C/K_v$ has a symmetric determinantal representation. Globally its Galois image is $H$, which fixes no such characteristic. Any globally defined non-effective theta characteristic would give a fixed one after base change, so the global representation cannot exist. [Ishitsuka and Ito, Theorem 2.2, Proposition 6.2, and Corollary 6.3](https://arxiv.org/pdf/1412.8336)

## Verification and scope

This is a classical proof using published monodromy, the published correspondence with non-effective theta characteristics, Hilbert irreducibility, and a finite orthogonal-group construction in the case of an even canonical theta characteristic. The conclusion allows a finite extension of the starting number field and is existential. No Lean formalization or explicit coefficients for the higher-degree curves are claimed. Searches for work citing Problem 1.6(2) and for subsequent counterexamples in degrees at least five located the original problem and later work on quartics. Priority remains provisional pending a wider literature check.

---

# Integral equivalence of linear determinantal representations over Dedekind domains

## Main theorem

Let $A$ be a Dedekind domain with fraction field $K$. Let $f\in A[x,y,z]$ be homogeneous of degree $d\ge 2$ and assume that $C=V(f)\subset \mathbb P^2_A$ is smooth over $A$ with geometrically integral fibers of dimension one. A representation is a $d\times d$ matrix $M$ of homogeneous linear forms with $\det M\in A^\times f$. The plane coordinates are fixed throughout. Left–right equivalence means $N=UMV^{-1}$, with $U,V\in\mathrm{GL}_d(A)$. For symmetric matrices, projective congruence means $N=cUMU^{\mathsf T}$, with $U\in\mathrm{GL}_d(A)$ and $c\in A^\times$. Strict congruence requires $c=1$.

1. In any fraction-field left–right equivalence class containing an integral representation, the integral equivalence classes form a torsor under $\operatorname{Pic}(A)[d]$. They all belong to one equivalence class over each $A_{\mathfrak p}$.
2. In any fraction-field projective-congruence class containing an integral symmetric representation, the integral projective-congruence classes form a torsor under $\operatorname{Pic}(A)[\gcd(d,2)]$. They likewise belong to one projective-congruence class over each $A_{\mathfrak p}$.
3. Every fraction-field strict congruence $N=GMG^{\mathsf T}$ between two integral symmetric representations already has $G\in\mathrm{GL}_d(A)$. Over a number field, for any ring of $S$-integers $A$, two integral symmetric representations strictly congruent over every completion of $K$ admit a strict congruence over $A$. Finite completions suffice.
4. A line bundle $L$ on $C$ acyclic on every geometric fiber comes from a free matrix after tensoring by a line bundle from $A$ if and only if $[\det(q_*L(1))]$ vanishes in $\operatorname{Pic}(A)/d\operatorname{Pic}(A)$, where $q:C\to\operatorname{Spec}A$. For the given $L$ itself the obstruction is its determinant class in $\operatorname{Pic}(A)$.

## The relative presentation

Write $\pi:\mathbb P^2_A\to\operatorname{Spec}A$ and $i:C\hookrightarrow\mathbb P^2_A$. The sequence
$$
0\longrightarrow\mathcal O(-2)^d\xrightarrow{M}
\mathcal O(-1)^d\longrightarrow i_*L_M\longrightarrow0
$$
associates a line bundle to a representation. Indeed, at any geometric point of $C$ a $(d-1)$-minor must be invertible locally. If all such minors vanished, the adjugate formula would make the fiber singular at that point. Elementary operations over the local ring then reduce the matrix to a block identity and one entry generating $(f)$. The nonzerodivisor $f$ gives injectivity, and the cokernel is invertible on $C$. The same calculation after base change to a fiber gives its presentation there. Cohomology of $\mathcal O(-1)$ and $\mathcal O(-2)$ on the plane proves acyclicity.

Conversely let $L$ be fiberwise acyclic. On a geometric fiber its degree is $g-1$ by Riemann–Roch. The sheaf $i_*L(1)$ is $0$-regular there since $H^1(C_s,L_s)=0$ and its support has dimension one. Thus $H^j(C_s,L_s(m))=0$ for $j>0$ and $m\ge1$, and $h^0(C_s,L_s(m))=md$. By cohomology and base change, $E=q_*L(1)$ is locally free of rank $d$ and commutes with base change. The evaluation $\pi^*E\to i_*L(1)$ is surjective on each fiber and hence globally. Its kernel $\mathcal S$ is locally free of rank $d$. Locally the target is a free rank-one $\mathcal O/(f)$-module and a surjection from a free rank $d$ module onto it has kernel isomorphic to $\mathcal O^{d-1}\oplus(f)$. The sequence remains exact on fibers because $i_*L(1)$ is flat over $A$.

On a geometric fiber the evaluation induces the identity on global sections, so $H^1(\mathcal S_s)=0$. Also $H^2(\mathcal S_s(-1))=0$ by $H^1(L_s)=0$ and $H^2(\mathcal O(-1))=0$. Thus $\mathcal S_s(1)$ is $0$-regular. Its space of sections has dimension $3d-2d=d$ by the evaluation sequence twisted by one. Its evaluation is consequently a surjection between vector bundles of the same rank and is an isomorphism. A second application of cohomology and base change gives $F=\pi_*\mathcal S(1)$, locally free of rank $d$, and $\pi^*F\cong\mathcal S(1)$. This yields the presentation
$$
0\longrightarrow\mathcal O(-2)\otimes\pi^*F\longrightarrow
\mathcal O(-1)\otimes\pi^*E\longrightarrow i_*L\longrightarrow0.
$$
The construction is functorial. For any two such presentations the map on $E$ induced by an isomorphism of cokernels is forced by applying $\pi_*(-\otimes\mathcal O(1))$. It then forces the map on the kernel and hence on $F$. Presentations originally given by matrices are identified with the canonical ones by this argument and $H^0(\mathcal O(-1))=H^1(\mathcal O(-1))=0$.

The determinant section of the presentation cuts out $C$ with its scheme structure, by the local evaluation description. Since $C$ is cut out by the single global $f$, the class $\pi^*(\det E\otimes(\det F)^{-1})$ is trivial. Pullback along any section of $\pi$ gives $[\det E]=[\det F]$. Steinitz classification over $A$ now says that a free matrix exists for $L$ exactly when $[\det E]=0$. For a base line bundle $P$, both $E$ and $F$ are tensored by $P$ upon replacing $L$ by $L\otimes q^*P$. Thus $[\det E]$ changes by $d[P]$. This proves assertion 4.

## Integral left–right equivalence

Two line bundles on $C$ which become isomorphic on $C_K$ differ by $q^*P$ for a unique line bundle $P$ on $\operatorname{Spec}A$. For existence, a generic trivialization of their quotient gives a vertical divisor on the regular integral scheme $C$. Each vertical prime divisor is an entire integral fiber and occurs with multiplicity one in the pullback of the base prime, since its scheme-theoretic fiber is reduced. For uniqueness, $q_*\mathcal O_C=\mathcal O_{\operatorname{Spec}A}$, for example by pushing forward the plane exact sequence $0\to\mathcal O(-d)\to\mathcal O\to i_*\mathcal O_C\to0$ and using $H^1(\mathbb P^2_A,\mathcal O(-d))=0$. Apply the projection formula to $q^*P$.

Functoriality of the relative presentation identifies matrix equivalence with isomorphism of the line bundles. Fixing one integral representation in the generic class identifies every other integral representation with a unique base twist $P$. The twists admitting free matrices are exactly those with $P^d$ trivial. Every such twist is trivial over each $A_{\mathfrak p}$, proving assertion 1. The same argument also shows that the automorphisms of a line bundle are precisely multiplication by base units and that their lifts to each of the two presenting modules are the same scalar.

## Symmetric presentations and strict congruences

Suppose $M,N$ are symmetric and left–right equivalent. Transposition turns the pair $(U,V)$ giving $N=UMV^{-1}$ into the pair $(V^{-\mathsf T},U^{-\mathsf T})$ for the same oriented equivalence. Their two induced cokernel isomorphisms differ by a unique scalar unit. By the functoriality and scalar uniqueness just proved, $V^{-\mathsf T}=cU$ for a base unit $c$, so $N=cUMU^{\mathsf T}$. This works over $A$, over $A_{\mathfrak p}$, and over $K$.

Suppose two integral symmetric representations lie in the same generic projective-congruence class and put $L_N=L_M\otimes q^*P$ up to isomorphism. Identify the line of base sections inducing maps $L_M\to L_N$ with $P$. Fix a generic nonzero section $s_0$, with lift $(U_0,V_0)$, and write $N=c_0U_0MU_0^{\mathsf T}$. At a nonzero prime $\mathfrak p$ choose a local generator $s_{\mathfrak p}=\lambda_{\mathfrak p}s_0$ of $P_{\mathfrak p}$. Its lift is $(\lambda_{\mathfrak p}U_0,\lambda_{\mathfrak p}V_0)$. The transpose argument over $A_{\mathfrak p}$ yields the local unit $c_{\mathfrak p}=c_0\lambda_{\mathfrak p}^{-2}$. It follows that $c_0s_0^{\otimes2}=c_{\mathfrak p}s_{\mathfrak p}^{\otimes2}$ generates $P^{\otimes2}$ at every nonzero prime and hence globally. Also $P^d$ is trivial by assertion 1.

Conversely, if $P^2$ and $P^d$ are trivial, fix a global generator $\sigma$ of $P^{\otimes2}$. Regard $M$ as a symmetric tensor in $E\otimes_A E$ with linear-form coefficients, where $E=A^d$. Then $M\otimes\sigma$ is a symmetric tensor on the free module $E\otimes P$. Viewed as a map from its dual, its cokernel is $L_M\otimes q^*P$. To see this, $\sigma$ identifies $P^{-1}$ with $P$ and the map becomes the original presentation tensored by $P$. Choosing a basis produces the desired symmetric matrix. Its generic cokernel agrees with $L_M|_{C_K}$, so the transpose argument gives generic projective congruence. The same argument over $A$ shows that the projective-congruence class is independent of the choice of generator and basis. Thus assertion 2 follows.

For assertion 3, suppose $N=GMG^{\mathsf T}$ over $K$. Its lift $(G,G^{-\mathsf T})$ induces a generic cokernel isomorphism. Choose a local cokernel isomorphism at $\mathfrak p$, which exists since the two line bundles differ by a base line bundle. Its integral lift is $(U,V)$ over $A_{\mathfrak p}$. Scalar uniqueness over $K$ gives
$$
G=\lambda U,\qquad G^{-\mathsf T}=\lambda V,\qquad
I=\lambda^2 VU^{\mathsf T}
$$
for a common $\lambda\in K^\times$. Taking the valuation of the last identity's determinant shows $\lambda\in A_{\mathfrak p}^\times$. Both $G$ and $G^{-1}$ are therefore integral at every nonzero prime. The intersection formula for Dedekind domains proves $G\in\mathrm{GL}_d(A)$.

Finally suppose strict congruence holds at every finite completion of a number field $K$. A single such completion trivializes $L_N|_{C_K}\otimes (L_M|_{C_K})^{-1}$ after field extension. Cohomology commutes with field extension. Hence the quotient line bundle has a nonzero section over $K$ whose extension is nowhere vanishing, so it is already trivial. The generic transpose argument gives $N=c_0U_0MU_0^{\mathsf T}$. Over any field extension of $K$, a strict congruence matrix must be a scalar multiple of $U_0$ by uniqueness of lifts up to a scalar on this geometrically integral curve. Such a multiple exists precisely when $c_0$ is a square. A nontrivial quadratic extension has a nonsplit finite place, so $c_0$ is a square in $K$. Apply the integrality statement already proved.

## An unbounded number of classes for a fixed symmetric quartic

Set $S=\{2,3,5,7,11\}$ and fix
$$
M_0=
\begin{pmatrix}
x+y&z&0&0\\
z&x+2y&z&0\\
0&z&x-2y&z\\
0&0&z&x-y
\end{pmatrix}.
$$
Its determinant is the fixed quartic
$$
f=x^4-5x^2y^2+4y^4-3x^2z^2-3y^2z^2+z^4.
$$
Write $f=Q(x^2,y^2,z^2)$. The Hessian of $Q$ is
$$
H=\begin{pmatrix}
2&-5&-3\\
-5&8&-3\\
-3&-3&2
\end{pmatrix}.
$$
The principal minors of size one are $2,8,2$, those of size two are $-9,-5,7$, and the full determinant is $-198$. Outside the primes in $S$, a geometric point with zero gradient would give a nonzero vector of squares in the kernel of the principal submatrix of $H$ on its nonzero coordinates, which is impossible. Thus this is a smooth quartic over $\mathbb Z[1/2310]$. Its geometric fibers are integral because distinct plane components must intersect.

For any $t\ge 2$, take $t-1$ distinct primes $p_j$ congruent to $1$ modulo $8\prod_{\ell\in S\setminus\{2\}}\ell$. By the Chinese remainder theorem and Dirichlet's theorem choose a further prime $r\equiv 3\pmod 8$ with $-r$ a quadratic nonresidue at every odd $\ell\in S$. Then $D=-r\prod_jp_j$ is an odd negative fundamental discriminant, $D\equiv5\pmod8$, and all primes of $S$ are inert in $K=\mathbb Q(\sqrt D)$. Their prime ideals are already principal, so $\operatorname{Pic}(\mathcal O_K[1/2310])\cong\operatorname{Pic}(\mathcal O_K)$.

The classes of the $t$ ramified prime ideals of $\mathcal O_K$ generate a subgroup of $2$-torsion of order $2^{t-1}$. Each squares to a principal ideal and their full product is $(\sqrt D)$. If a proper nonempty subproduct were principal, its complementary subproduct would be principal too. Choose the smaller of their norms $N\le\sqrt{|D|}$, and write a generator as $(a+b\sqrt D)/2$. For $b\ne0$, its norm is at least $|D|/4>\sqrt{|D|}$ since we may choose $|D|>16$. For $b=0$, the generator is a rational integer whose norm is a square, while $N>1$ is squarefree. Thus there is only the full-product relation.

Taking $A=\mathcal O_K[1/2310]$ now gives at least $2^{t-1}$ integral symmetric $4\times4$ representations of the same quartic, all locally projectively congruent and pairwise globally inequivalent even under independent left–right equivalence. The determinants can each be made exactly $f$. In the construction for a $2$-torsion $P$, choose the basis of $E\otimes P$ to have determinant equal to the original basis volume tensored with $\sigma^{\otimes 2}$, which is possible by a unit change of basis. The determinant tensor of $M_0\otimes\sigma$ equals that of $M_0$ tensored with $\sigma^{\otimes4}$, giving exactly $f$ in this volume.

## Literature and verification

Over fields, the cokernel construction and the line-bundle descriptions are classical, including [Beauville, Determinantal hypersurfaces, Propositions 3.1 and 4.2](https://arxiv.org/abs/math/9910030). The argument above tracks the two relative presenting modules, their Steinitz classes, and the square trivialization needed for symmetry. [Ishitsuka and Ito, The local–global principle for symmetric determinantal representations of smooth plane curves](https://arxiv.org/abs/1412.8336) study local-to-global existence over the field. The strict-congruence assertion here compares already given integral representations. The distinguishing classifications and fixed-curve family have been checked by the proof above. Their literature novelty is provisional, and no Lean formalization is claimed.
