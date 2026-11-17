# Which finite extensions make two tensors isomorphic?

Fix any finite field $F=\mathbb F_q$. For two tensors $T,S$ of the same format, their extension-degree spectrum is
$$
 {\cal E}(T,S)=\{d\ge1:T\simeq_{\mathbb F_{q^d}} S\}.
$$
The following statements concern ordinary tensor isomorphism.

1. The possible spectra are exactly the empty set and the finite nonempty unions of divisibility progressions $m\mathbb Z_{>0}$. Every nonempty spectrum occurs for raw balanced, absolutely indecomposable 3-tensors, with scalar matrix-mode pair adjoint over the algebraic closure.
2. If $T,S$ are geometrically isomorphic and the geometric stabilizer component group of $T$ is nilpotent, the spectrum is one divisibility progression $d_0\mathbb Z_{>0}$, where $d_0$ divides the order of that component group. In particular, isomorphism over extensions of relatively prime degrees gives base-field isomorphism in this case.
3. For distinct primes $\ell_1,\ldots,\ell_k$, the smallest balanced side length in the étale template below that admits isomorphism after *each* of those prime degrees, with base-field inequivalence, is
$$
 4+2^{k-1}\prod_{i=1}^k\ell_i .
$$
The construction at this size has no other allowed degrees except those divisible by at least one of the primes.

## 1. Reduce every geometric transporter to its component

Suppose $T,S$ are isomorphic over an algebraic closure $\overline F$. Let $H$ be the reduced stabilizer of $T$ in the product of general linear groups. Reduction does not change the points over $\overline F$ or finite extensions. The base field is perfect, so the reduced group is smooth and its identity component $H^\circ$ is a smooth connected group over $F$. The geometric transporter $X$ is a right torsor under $H$ on points: for any geometric transporter $g$, every other is uniquely $g h$. The set $C$ of components, viewed as a finite set of right $H^\circ$-cosets in $X(\overline F)$, carries the $q$-Frobenius permutation $\sigma$ and is a torsor under $\Gamma=H(\overline F)/H^\circ(\overline F)$.

A rational transporter over $\mathbb F_{q^d}$ gives a $\sigma^d$-fixed component. Conversely if $\sigma^d$ fixes a component containing $g$, then $g^{-1}\sigma^d(g)=a\in H^\circ(\overline F)$. Lang's theorem for $H^\circ$ over $\mathbb F_{q^d}$ gives $b\in H^\circ(\overline F)$ with $b\sigma^d(b)^{-1}=a$. Thus $g b$ is a rational transporter over the required extension. This shows
$$
 {\cal E}(T,S)=\bigcup_{c\in C}
            \operatorname{period}_{\sigma}(c)\,\mathbb Z_{>0}.
$$
When geometric isomorphism fails the spectrum is empty. Once a fixed component has a rational point, all its rational points are the translate of $H^\circ(\mathbb F_{q^d})$ through that point. Hence the number of rational transporters is exactly the number of fixed geometric components times $|H^\circ(\mathbb F_{q^d})|$. The descent here uses the classical connected-group theorem. [Lang, Algebraic Groups Over Finite Fields](https://doi.org/10.2307/2372673)

For 3-tensors with dimensions $n_1,n_2,n_3$, put $D=\sum_i n_i^2$. A nonempty spectrum contains a degree at most $3^D$. Indeed the transporter is the invertible open part of the affine variety in $D$ scalar matrix entries cut out by the cubic tensor equations. The total degree of the affine irreducible components is at most $3^D$ by the degree bound for successive intersections. For completeness, at each intersection maintain the weighted sum $\sum_C \deg(C)3^{\dim C}$. A defining cubic either vanishes on a component $C$ or cuts it in components of dimension $\dim C-1$ of total degree at most $3\deg(C)$, by projective Bézout on its closure. Component deletion or deduplication cannot increase the sum. It starts at $3^D$. Passing to the invertible open part keeps at most one irreducible component from each surviving affine component. Thus $|C|\le3^D$, and some Frobenius orbit on $C$ has length at most this bound. The period description is a structural classification, and the argument does not assert polynomial-time recovery of these components.

## 2. Nilpotent component groups force descent to a minimal field

Identify a finite torsor with its acting finite group $\Gamma$ by choosing a point. Under this identification the Frobenius acts as $f(x)=a\alpha(x)$ for an automorphism $\alpha$ of $\Gamma$. If $\Gamma$ is nilpotent, it is the direct product of its Sylow subgroups, each characteristic, and $f$ is the product of the corresponding affine permutations. It suffices to analyze a single finite $p$-group $P$. Here $p$ is any prime dividing the component group order and can differ from the base-field characteristic.

We first show that an affine permutation $u$ on a finite $p$-group torsor with $u^r=1$ for $\gcd(r,p)=1$ has a fixed point. Take the quotient torsor by the center $Z(P)$, which is characteristic. Induct on $|P|$ to find a fixed coset when $P$ is nonabelian. On that coset the same permutation is affine on a torsor under the abelian $p$-group $Z(P)$, of order dividing $r$. For an abelian $p$-group torsor, choose a point as origin and average the $r$ successive orbit points, using the inverse of $r$ modulo the exponent of the group. Affine maps commute with the average since its coefficients sum to one. The resulting point is fixed. This also handles the abelian case of the induction.

If $f^d$ has a fixed point and $d=p^a r$ with $\gcd(r,p)=1$, the nonempty set of fixed points of $f^d$ is a torsor under $P^{\alpha^d}$. Indeed after choosing a fixed point, a second point is fixed precisely when the unique displacement in $P$ is fixed by $\alpha^d$. The permutation $f^{p^a}$ acts affinely on this set, and its $r$-th power is the identity there. The preceding lemma gives a point fixed by $f^{p^a}$. Let $a_0$ be the least $p$-adic valuation of the period of any point for $f$. The argument gives a point of exact period $p^{a_0}$, because any smaller $p$-power period would contradict the definition. Therefore $f^d$ has a fixed point exactly at multiples of $p^{a_0}$, and $p^{a_0}\le |P|$, hence $p^{a_0}\mid |P|$.

Take the product of these minimum prime-power periods over the Sylow factors. A power of the full permutation has a fixed point exactly if it has one on every factor. This proves the asserted single progression with a minimum degree $d_0\mid |\Gamma|$. It also proves descent to the gcd of any finite list of allowed extension degrees in the nilpotent case. Connected stabilizers give $d_0=1$.

## 3. Realize every spectrum by a balanced tensor pair

It suffices to realize every nonempty finite union of progressions. We use the earlier étale tensor template, included here for completeness. Take a finite étale algebra $A$ of dimension $m$ over $F$, and set $V=F^2\otimes F^2$. On $V$, let $e=e_1\otimes f_1+e_2\otimes f_2$ and let $\epsilon$ be the coefficient functional of $e_1\otimes f_1$. The slices have labels $(a,B)\in A\oplus\operatorname{Mat}_2(F)$, and are
$$
 M_A(a,B)=
 \begin{pmatrix}
  L_a & B_{12}1_A\epsilon\\
  B_{12}e\operatorname{Tr}_{A/F} & B\otimes I_2
 \end{pmatrix}
$$
on $A\oplus V$, where $L_a$ is left multiplication by $a$. The format is $(m+4)^3$. The tensor is concise because labels are detected by the two diagonal blocks and the slices at $(1_A,0)$ and $(0,I_2)$ are complementary projections. Its geometric rank-one label lines are exactly the primitive idempotent lines of the split algebra $A_{\overline F}$. A nonzero $B$ already has rank at least two on the bottom block, while $L_a$ on the split algebra is diagonal.

The fixed-label pair adjoint $QM_A=M_AP$ is scalar over every extension. The two projection slices force $P=Q$ block diagonal. Its top block commutes with the regular algebra and is $L_c$ for $c\in A_{\overline F}$. Its bottom block commutes with $\operatorname{Mat}_2\otimes I_2$ and is $I_2\otimes J$. The upper mixed equation at $B=E_{12}$ forces $c=\lambda1_A$ by evaluating on a vector where $\epsilon=1$. The lower mixed equation and the nonzero split trace then give $(I_2\otimes J)e=\lambda e$, forcing $J=\lambda I_2$. The centroid is scalar as well, since the other two actions already belong to this fixed-label system and the label map is injective. Scalar centroid implies absolute indecomposability.

Two such tensors are isomorphic over $K=\mathbb F_{q^d}$ exactly when $A\otimes_F K$ and $A'\otimes_F K$ are isomorphic. In one direction a tensor isomorphism identifies the intrinsic rank-one frame lines equivariantly for $K$-Frobenius, so its cycle type determines the factors of the étale algebra. In the other direction an étale isomorphism preserves the unit, multiplication and trace and gives an explicit tensor isomorphism leaving the auxiliary modes unchanged. Thus if $A,A'$ correspond to finite permutations $\pi,\pi'$, the spectrum is the set of $d$ for which $\pi^d,(\pi')^d$ have the same cycle type. Recall that a cycle of length $s$ contributes $s$ fixed points to the $t$-th power exactly when $s\mid t$; all fixed-point counts of powers determine the cycle type by Möbius inversion.

Now fix a finite list $m_1,\ldots,m_j$ of positive generators of the desired nonempty spectrum, set $L=\operatorname{lcm}(m_1,\ldots,m_j)$, and on the divisors of $L$ put $f(t)=1$ if no $m_i$ divides $t$, and zero otherwise. Choose integers $c_s$ for $s\mid L$ with $f(t)=\sum_{s\mid t}c_s$, by ordinary Möbius inversion. Use the signed difference of cycle multiplicities $L c_s/s$ at length $s$, placing positive entries in the first permutation and negative entries in the second. The two total sizes agree because
$$
 \sum_{s\mid L} Lc_s=Lf(L)=0.
$$
If needed add a common one-cycle to make both positive in size. The difference in fixed-point counts of the $t$-th powers is $L f(\gcd(t,L))$ for every $t\ge1$. For an excluded degree $d$, the difference is already nonzero at $t=d$. For an included degree $d$, the difference vanishes for every multiple of $d$, so the powered permutations have the same cycle type. This realizes exactly the desired spectrum. An empty spectrum is possible, for example for two geometrically inequivalent tensors of the same format. The realization is a finite construction and is not claimed polynomial in the binary encodings of the spectrum generators.

## 4. Sharp template size for prime-degree failures of gcd descent

Let $\ell_1,\dots,\ell_k$ be distinct primes, $k\ge1$, and put $P=\prod_i\ell_i$. For a pair of étale permutations let $\Delta_s$ be the difference of cycle multiplicities at length $s$. Equality of cycle type after powering by $\ell_i$ implies two conditions. When $s$ has $\ell_i$-adic valuation at least two, $\Delta_s=0$, because powered cycles with positive $\ell_i$-valuation come only from their original lengths multiplied by $\ell_i$. At each $\ell_i$-coprime $s$, the equality gives $\Delta_s+\ell_i\Delta_{\ell_i s}=0$. Therefore, for each $t$ coprime to $P$, all possible nonzero differences over $t$ are determined by $\Delta_{tP}=z_t$:
$$
 \Delta_{t\prod_{i\in S}\ell_i}
  =(-1)^{k-|S|}\Big(\prod_{i\notin S}\ell_i\Big)z_t ,
 \qquad S\subseteq\{1,\dots,k\}.
$$
If the base permutations disagree some $z_t\ne0$. Each of its terms has absolute contribution $tP|z_t|$ to the difference in the number of elements. Exactly half contribute positively. Hence the common size of the permutations is at least $2^{k-1}P$. Taking $z_1=1$ and all other $z_t=0$ attains this bound by placing the signed multiplicities on opposite sides. It gives the union of the prime progressions, since the difference in fixed-point counts at $d$ is, up to a fixed overall sign, $P\prod_i(1-\mathbf1_{\ell_i\mid d})$, zero at all multiples of every included $d$. This proves the exact minimum side $4+2^{k-1}P$ within the template. For example side $16$ admits a pair isomorphic over both the quadratic and cubic extensions of every finite field while inequivalent over the base field.

The structural forward description uses classical Lang descent and was also used in our earlier work on modular isomorphism profiles. The converse realization, the nilpotent-component criterion as applied to these spectra, and the sharp size computation are presented as informal proofs. Publication priority is unverified. The earlier binary-degree hardness result addresses the complexity of selecting an extension on this template. The classification here addresses which spectra are possible and when gcd descent holds.
