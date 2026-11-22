# Four-by-four pencils separate tensor isomorphism from every scalar-extension rank test

A square matrix pencil supplies an ordinary three-tensor with one mode of dimension two. The two matrix modes and the slice mode all have independent general linear actions. Here the arithmetic comparison uses all those actions.

## 1. Simple regular pencils

**Lemma 1.** Let $F$ be infinite, and represent a regular $n$-by-$n$ pencil with simple determinant roots by $(I,M)$. Its determinant roots are regarded as an unordered divisor of $n$ geometric points of $\mathbb P^1_F$. Two such tensors are isomorphic over $F$ exactly when their divisors are projectively equivalent over $F$. The rank is $n$ when every determinant root belongs to $F$, and $n+1$ otherwise.

*Proof.* An invertible slice exists over $F$, since its determinant polynomial is nonzero and $F$ is infinite. A change in the slice mode makes a fractional linear substitution on eigenvalues. After choosing the first slice invertible, the resulting second matrix has the form $(aI+bM)^{-1}(cI+dM)$. Left and right equivalences of normalized pencils reduce to similarity. A matrix with simple determinant roots is cyclic, so it is determined up to $F$-similarity by its characteristic polynomial. This proves both implications of the classification, with no conditions on whether the roots split over $F$. Equivalently one may take the roots of $\det(xI-M)$ as the divisor, since that just chooses fixed coordinates on the projective pencil parameters.

A rank $n$ decomposition of a pencil with an invertible slice uses bases in both matrix modes. In these two bases all slices are diagonal, so the eigenvalues belong to $F$. Conversely, if the roots all belong to $F$, a diagonalization gives rank $n$. For the upper bound $n+1$, use the companion description $M(v)=zv\bmod f(z)$ for the monic degree-$n$ determinant polynomial $f$. The pencil performs the product of a polynomial of degree at most one and a polynomial of degree at most $n-1$, modulo $f$. Evaluation at $n+1$ distinct scalars, componentwise multiplication, interpolation and reduction give a decomposition of rank at most $n+1$. $\square$

## 2. Every quadratic entry field in format $2\times4\times4$

**Theorem 2.** For every nonsquare $d\in K^\times$ over a number field $K$, there are two simple regular pencils of format $2\times4\times4$ with identical rank over every extension $E/K$, which are ordinarily isomorphic over $E$ exactly when $E$ contains $K(\sqrt d)$. Their common rank is four over extensions containing a shared biquadratic splitting field $L/K$ and five elsewhere.

*Proof.* Choose $a,b\in K^\times$ giving independent square classes with $ab\in dK^{\times2}$ and $a+b=1$. To do so, choose a finite prime of odd residue characteristic where $d$ is a unit and $-d$ is a square modulo the prime. Such a prime exists by the splitting-prime theorem for $K(\sqrt{-d})/K$, including the split case. Choose $u\in K$ such that the valuation of $1+du^2$ there is exactly one, by choosing a root modulo the prime and avoiding its unique lift modulo the square of the prime. The derivative $2du$ is a unit. Then take $a=(1+du^2)^{-1}$, $b=du^2(1+du^2)^{-1}$. Each has odd valuation, and their product is in the nonsquare class of $d$. This proves independence.

The following explicit descent construction also works for any independent $a,b$ for which there exist $\lambda\in K(\sqrt b)^\times$ and $\nu\in K(\sqrt a)^\times$ of respective norms $a,b$. Here one can use $\lambda=1+\sqrt b$, $\nu=1+\sqrt a$. Put $L=K(\sqrt a,\sqrt b)$ and define
$$
 g_1(z)=\frac{\sqrt a\,z+\lambda}{\sqrt b(\sqrt a\,z-\lambda)},\qquad
 g_2(z)=\frac{\sqrt b\,z+\nu}{\sqrt a(\sqrt b\,z-\nu)} .
$$
With $s(z)=-z$ and $r(z)=1/z$, direct substitution gives
$$
 \sigma(g_1)=g_1s^{\chi_a(\sigma)}r^{\chi_b(\sigma)},\qquad
 \sigma(g_2)=g_2s^{\chi_b(\sigma)}r^{\chi_a(\sigma)}.
$$
Here $\chi_c$ records the sign change of $\sqrt c$. For the nonsign generator of the first formula, use $\lambda\bar\lambda=a$ to find $\sigma_b(g_1(z))=g_1(1/z)$. The formulas for the second are obtained by exchanging the roles of $a,b$.

Take the four rational points $S=\{2,-2,1/2,-1/2\}$. Its projective automorphism group is $V_4=\langle s,r\rangle$. Indeed its cross-ratio $9/25$ has six distinct images under the six transformations of a cross-ratio, so the stabilizer in $S_4$ has order four. The divisors $g_i(S)$ are defined over $K$ by the displayed Galois transformations. Every geometric projectivity between them is $g_2hg_1^{-1}$ for $h\in V_4$. It is defined over $E$ exactly when $h$ intertwines the two Galois actions over $E$. Since $V_4$ is abelian, this occurs exactly when $\chi_a=\chi_b$ over $E$, which is the condition $\sqrt d\in E$. In either divisor the Galois action on $S$ is regular with kernel fixing $L$. Thus the splitting field is $L$ in both cases. The divisors have no point at infinity: a pole would require $\lambda/\sqrt a$ or $\nu/\sqrt b$ in $K$, which contradicts independence of the classes. Take companion pencils of their monic equations and apply Lemma 1. $\square$

An example over $\mathbb Q$ uses $a=2$, $b=7$, $\lambda=3+\sqrt7$, and $\nu=3+\sqrt2$. Before monic normalization the two companion polynomials are
$$
 \begin{aligned}
  &2303x^4+4704x^3+2926x^2+672x+47,\\
  &-124x^4+768x^3+1532x^2+384x-31 .
 \end{aligned}
$$
Isomorphism is exactly at extensions containing $\mathbb Q(\sqrt{14})$, while the common rank drops only over extensions containing $\mathbb Q(\sqrt2,\sqrt7)$.

## 3. A local-global failure over $\mathbb Q(\sqrt{-3})$ in the same format

**Theorem 3.** Put $K=\mathbb Q(\sqrt{-3})$ and $L=K(\sqrt{-17},\sqrt{-89})$. There are simple regular pencils $T_1,T_2$ of format $2\times4\times4$ over $K$ such that, for every extension $E/K$,
$$
 T_1\simeq_E T_2\quad\Longleftrightarrow\quad E\cap L\ne K .
$$
Their common rank is four if $L\subseteq E$ and five otherwise. In particular they are isomorphic over every completion of $K$ and nonisomorphic over $K$.

*Proof.* In $K(i)=\mathbb Q(i,\sqrt3)$, let $t=(1+i)(1+\sqrt3)/2$ and $S=\{t,-t,1/t,-1/t\}$, using compatible square roots so $i\sqrt3=\sqrt{-3}$. Since $t^2+t^{-2}=2\sqrt{-3}$, the four-point polynomial is
$$
 z^4-2\sqrt{-3}\,z^2+1.
$$
For the cross-ratio $\eta=((t^2-1)/(t^2+1))^2$, the identity $\eta^2-\eta+1=0$ follows from $t^8+14t^4+1=0$. The six cross-ratio transformations yield just two distinct values, so the geometric projective automorphism group of $S$ is the alternating subgroup $A_4$ of $S_4$. Its normal Klein subgroup is $\langle s,r\rangle$. The nontrivial $K$-conjugation of $K(i)$ sends $t$ to $-1/t$, so the action on $S$ is $(sr)^{\chi_{-1}}$.

Use the explicit maps $g_1,g_2$ from Theorem 2 with $a=17$, $b=89$, $\lambda=151+16\sqrt{89}$ and $\nu=19+4\sqrt{17}$. Their norms are $17$ and $89$, respectively. The classes $17,89$ are independent in $K(i)$, as both primes are unramified there and their valuations separate the classes. In particular the maps have no pole on $S$. For each $i$ use $g_i$ to label the new divisor by $S$. The transported Galois actions on these labels are
$$
 h_1=s^{\chi_{-17}}r^{\chi_{-89}},\qquad
 h_2=s^{\chi_{-89}}r^{\chi_{-17}} .
$$
Indeed the transformations of $g_i$ multiply their action on $S$ by the base action $(sr)^{\chi_{-1}}$. Both actions are regular through $\operatorname{Gal}(L/K)=V_4$, with the classes independent by valuations at $17,89$ over $K$. The common splitting field is therefore $L$.

A geometric projectivity between the divisors corresponds to a permutation in $A_4$ on these labels. It is defined over $E$ precisely when that permutation intertwines the displayed actions of the absolute Galois group of $E$. This follows because a projectivity is determined by its values on three distinct points, so Galois equivariance is exactly descent of the projectivity itself. Every proper subgroup of $V_4$ has order at most two. Its two images are conjugate in $A_4$, because the three nonidentity elements of $V_4$ are conjugate in $A_4$. The two full images cannot be intertwined, since the automorphism interchanging $s,r$ is a transposition on the three nonidentity elements, while conjugation in $A_4$ induces only their cyclic permutations. The image of the Galois group over $E$ is proper exactly when $E\cap L\ne K$, proving the isomorphism criterion. The rank formula follows from Lemma 1.

At the dyadic places the two classes $-17$, $-89$ coincide, since $17,89$ are both squares in $\mathbb Q_2$. At $17$, the class $-89$ is a square in $\mathbb Q_{17}$ because $89\equiv4\bmod17$ and $-1$ is a square. The corresponding argument at $89$ uses quadratic reciprocity and $-1$ again. At every other finite place the extension over $K$ is unramified, so its decomposition group is cyclic. Archimedean places of $K$ are complex. Hence all decomposition groups are proper, and all local tests are positive. $\square$

For explicit coefficients put $\kappa=2\sqrt{-3}$. For $a,b,\lambda$ as above, write $\lambda=c+e\sqrt b$, $U=c^2+be^2$, $V=2ce$. A polynomial for $g_1(S)$ is
$$
 b^2(2U-a\kappa)x^4+8Vb^2x^3
 +b(12U+2a\kappa)x^2+8Vbx+(2U-a\kappa).
$$
Use $(a,b,c,e)=(17,89,151,16)$ for the first and $(89,17,19,4)$ for the second. The formula follows by substituting $z=\lambda(\sqrt b\,x+1)/(\sqrt a(\sqrt b\,x-1))$ in $z^4-\kappa z^2+1$ and clearing denominators. Divide by the leading coefficient, form the companion matrix, and take $I$ and that matrix as the two slices.

**Corollary 4.** Side length four is minimal among simple regular square pencils with these properties, either for a failure of the local-global principle or for a failure of isomorphism detection by the full rank profile.

*Proof.* For $n\le3$, equality of rank profiles implies equality of splitting fields by Lemma 1, tested at both splitting fields. Local isomorphism everywhere also gives equality of splitting fields. Indeed, in a common Galois splitting extension, at each unramified prime the local splitting of a divisor means that Frobenius lies in the kernel of its permutation action. Equality of these conditions means equality of the two kernels by Chebotarev. For a common splitting field $L$, the two faithful actions of $G=\operatorname{Gal}(L/K)$ on $n\le3$ letters are conjugate in $S_n$, since the possible subgroups are $1,C_2,C_3,S_3$ and their faithful degree-$n$ representations as permutation groups of this size are unique up to relabelling. In degree three a Galois-equivariant bijection between the point sets extends to a unique projectivity and descends. In degree two the split case is immediate, and in the nonsplit case the two conjugate pairs in a common quadratic field are related by an affine linear map over $K$, after choosing coordinates with neither pair at infinity. Single rational points are projectively equivalent. Apply Lemma 1. $\square$

## 4. Rank equality for finite étale multiplication tensors

**Theorem 5.** Let $K$ be infinite, let $L/K$ be finite Galois of group $G$, and let $A,B$ be equal-dimensional finite étale $K$-algebras split by $L$, with geometric factor sets $X,Y$. Their multiplication tensors have the same rank over every field extension of $K$ if and only if $X,Y$ have equal cyclic subgroup marks. Consequently, the arithmetic TI profiles realizable by such rank-indistinguishable pairs are exactly the conjugacy-invariant downward-closed subgroup families containing all cyclic subgroups of $G$.

*Proof.* Write $n=\dim_K A$. For every $E/K$, with $H_E\le G$ the Galois image over $E$,
$$
 \operatorname{rank}_E(T_A)=2n-\#(H_E\backslash X).
$$
The factors of $A_E$ are the orbits of $H_E$, and the Alder–Strassen bound gives the lower bound. For each factor of degree $m$, its multiplication uses at most $2m-1$ products of linear forms by evaluation and interpolation of degree-$(m-1)$ polynomials, followed by reduction modulo its primitive polynomial. Sum these algorithms across the factors for the upper bound. [Alder–Strassen](https://doi.org/10.1016/0304-3975(81)90070-0)

Equal cyclic marks imply equal $H$-orbit counts by averaging element fixed-point counts over $H$. Conversely, equality of all $H$-orbit counts follows by testing $L^H$. For a cyclic $H$, group its fixed-point average by its cyclic subgroups and induct on $|H|$. All terms from proper subgroups cancel, leaving the difference of the two $H$-marks multiplied by the number of generators of $H$. Thus every cyclic mark agrees. In that case the restrictions of $X,Y$ to a cyclic $H$ are isomorphic, because every subgroup of $H$ is cyclic and the marks determine an $H$-set. This proves necessity for the profile classification. For sufficiency choose the Burnside-mark virtual difference whose marks vanish exactly on the prescribed downward family, as in the finite-étale profile theorem. Its cyclic marks agree, so the tensor ranks agree over every extension. $\square$

The classical inputs are the projective geometry of binary-form roots, matrix-pencil classification, and the algebra multiplication lower bound. The results here use them for a small-format arithmetic profile and exact rank-indistinguishable realizations, including the local-global example. Priority remains unestablished. The local-global counterexample concerns ordinary TI over a number field and the behavior of its field probes, a scalar-extension aspect of Grochow–Qiao’s across-fields question. Since the pair is isomorphic over an algebraic closure, it supplies no polynomial-calculus refutation bound for geometrically nonisomorphic pairs. These are manuscript proofs. [Lercier–Ritzenthaler–Sijsling, projective isomorphisms of binary forms](https://msp.org/obs/2013/1-1/obs-v1-n1-p23-p.pdf) · [Grochow–Qiao, Open Question 10.6 in the combined preprint](https://arxiv.org/html/1907.00309#S10.SS2)
