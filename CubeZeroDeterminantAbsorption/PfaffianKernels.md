# Ordinary tensor isomorphism for local algebras via commutator Pfaffians

Work over $F=\mathbb F_3$. A one-sign comparison asks for a transporter between two raw 3-tensors that has determinant $+1$ in one designated mode. An odd-automorphism test asks for a stabilizer of a single raw 3-tensor with determinant $-1$ in that mode. Use $L$ for total dense input length.

**Theorem.** Suppose the compared raw tensors are equivalent under independent changes of basis to multiplication tensors of unital associative local $F$-algebras with scalar residue and radical cube zero. Fix a finite extension $E/F$ of degree $e$. On one such algebra $R$ put
$$
V=J/J^2,\quad W=J^2,\quad
\mu:V\times V\longrightarrow W,\quad
\beta(x,y)=\mu(x,y)-\mu(y,x).
$$
Write $w=\dim_F W$. Let $c$ be the minimum $E$-corank of $\lambda\beta$ on $V_E=V\otimes_F E$, over all $\lambda\in\operatorname{Hom}_F(W,E)$. For a fixed constant $C$, assume $ew+c\le C\log_2 L$ at each endpoint. There is a deterministic polynomial-time many-one reduction from one-sign comparison on this family to ordinary 3-tensor isomorphism. Odd-automorphism testing on the family also reduces to one ordinary 3-tensor comparison.

The family is recognizable from raw input. It handles logarithmic corank even when every contraction is singular. Consequently an arbitrary one-sign comparison absorbs an odd-automorphism test from this family in a single one-sign comparison. The same conclusion holds when the relative one-sign comparison is on this family and the odd-automorphism test is unrestricted.

## Recover the multiplication and calibrate the sign

Use the regular fixed-label module reconstruction underlying the square-zero theorem. In equal positive mode dimensions $d$, view the tensor as $M(u):X\to Y$. Compute the unital algebra $B$ of pairs satisfying $QM(u)=M(u)P$, by linear equations. Require $u\mapsto M(u)$ to be injective and $\dim B=d$. Compute the Jacobson radical $I$ of $B$ by the finite-field algebra algorithm, which is deterministic in polynomial time in fixed characteristic. Require $\dim(B/I)=1$ and $I^3=0$. Compute $IX,IY$ by linear algebra and require that each quotient module have dimension one. A vector $x$ outside $IX$ generates $X$ as a $B$-module: $X=Bx+IX$ implies that $X/Bx$ is equal to its product by $I$, hence to zero by $I^3=0$. The same holds for a vector $y$ outside $IY$. The two equal-dimension maps $b\mapsto bx$ and $b\mapsto by$ give explicit regular-module charts. Under these charts $M(u)$ is right multiplication by its value at the identity, since it intertwines the left regular actions. Its value at the identity gives the first-role chart by injectivity and equal dimensions. The resulting bilinear map is multiplication in $R=B^{\mathrm{op}}$. Conversely in a unital multiplication tensor the identity slice equates the two components of each pair in $B$, and commuting with every left multiplication makes that component right multiplication by its value at the unit. Thus scalar-residue cube-zero multiplication tensors pass these tests in any raw frames. [Ivanyos and Qiao, Theorem 18](https://arxiv.org/html/1708.03495)

If $p(x)q(y)=r(xy)$ is an isotopy between unital multiplication tables, setting one input at a time to the identity gives $p=L_u\phi,\ q=R_v\phi,\ r=L_uR_v\phi$, where $u,v$ are units of the target and $\phi$ is an algebra isomorphism. Surjectivity proves that left multiplication by $u$ and right multiplication by $v$ are invertible. Their one-sided inverses are two-sided in a finite-dimensional unital algebra. Substitution proves that $u^{-1}p$ is a unital algebra isomorphism, and the displayed form also suffices. Left and right multiplication by a unit with residue $a\in F^\times$ have determinant $a^d$, since they act as $a$ on every radical grade.

If $d$ is odd, left or right multiplication by the unit $-1$ gives an odd stabilizer in each designated mode, using the output action in the isotopy formula. Hence ordinary isomorphism is equivalent to one-sign isomorphism. Also, if $\dim V$ is odd, fix a linear splitting $R=F1\oplus V\oplus W$. Acting by $-I$ on the lift of $V$ and by the identity on the other two summands is an algebra automorphism. Every radical product is bilinear in the two $V$-coordinates and lands in $W$. Its determinant is $-1$, with the same consequences. For the remaining branch $d$ and $n=\dim V$ are both even. The square-zero case $W=0$ is included in the odd-$d$ or odd-$n$ cases.

After choosing ordered bases of $V,W$, lift the first to $J$, and take the algebra basis consisting of $1$, the chosen lift, and the ordered $W$-basis. If $g:V\to V'$ and $h:W\to W'$ are induced by an algebra isomorphism $\phi$, its determinant in these bases is
$$
\det \phi=\det(g)\det(h).
$$
The dimensions and all eligibility conditions are invariant under an isotopy. A mismatch allows a fixed negative output. Let $\delta$ be the product of the two physical chart determinants in the designated mode, expressed relative to the selected adapted algebra bases. The ordinary tensor convention uses duals in some modes, which leaves the sign unchanged over $F$. In the even-$d$ case the raw sign of a transporter is therefore $\delta\det(g)\det(h)$. Set the requested raw sign to $\sigma$, with $\sigma=1$ for the one-sign comparison, and require $\det\phi=\sigma\delta$. For an odd-automorphism test use the tensor and its physical reflection in the designated mode as the endpoints of a one-sign comparison.

## The determinant on a family of radicals

Enumerate the $3^{ew}$ linear maps $\lambda:W\to E$ and compute the corank of each $\lambda\beta$. If $ew$ exceeds the logarithmic bound, reject eligibility without this enumeration. Otherwise the scan and all rank computations have polynomial cost. Let $\mathcal L$ be the nonempty set of minimizers and $K_\lambda=\ker(\lambda\beta)$ for $\lambda\in\mathcal L$.

For each $\lambda\in\mathcal L$ let $k_1,\ldots,k_c$ be a basis of $K_\lambda$ and choose a complement basis $v_1,\ldots,v_{n-c}$ in $V_E$. Define an $E$-linear functional $Q_\lambda : \Lambda_E^c K_\lambda\to E$ by
$$
Q_\lambda(k_1\wedge\cdots\wedge k_c)=
\frac{\det[k_1,\ldots,k_c,v_1,\ldots,v_{n-c}]}
{\operatorname{Pf}\big[(\lambda\beta)(v_i,v_j)\big]_{i,j=1}^{n-c}}.
$$
The determinant uses the chosen $F$-basis of $V$ extended to $E$. The denominator is nonzero because the induced form on $V_E/K_\lambda$ is nonsingular. It is 1 in dimension zero. A different complement basis changes the quotient vectors by an invertible matrix and changes numerator and denominator by the same determinant. Adding kernel components to any complement vector changes neither. The numerator is alternating multilinear in the ordered kernel vectors and the denominator is independent of them. Thus this defines a well-defined nonzero $E$-linear functional on the top line. Compute the value by Gaussian elimination and alternating Pfaffian elimination. The covariance of the Pfaffian under a basis change is a polynomial identity with integer coefficients, so it holds even when the characteristic divides the factorial of half the alternating matrix size.

Let $\phi:R\to R'$ be an algebra isomorphism, with induced maps $g:V\to V'$ and $h:W\to W'$. For $\lambda\in\mathcal L$ put $\lambda'=\lambda h^{-1}$. The map $\lambda\mapsto\lambda'$ is a bijection between the two minimizer sets, and $g_E=g\otimes 1$ sends $K_\lambda$ bijectively to $K'_{\lambda'}$, since
$$
(\lambda'\beta')(g_E x,g_E y)=(\lambda\beta)(x,y).
$$
Use $g_Ev_i$ as the complement in the target evaluation. The Pfaffian is unchanged and the determinant of the combined frame acquires a factor $\det g$. Therefore
$$
Q'_{\lambda'}\big((\Lambda^c g_E)z\big)=\det(g)\, Q_\lambda(z)
\quad(z\in\Lambda_E^c K_\lambda).
$$
For $c=0$ this construction uses the reciprocal of the previous nonsingular Pfaffian table, with the same sign covariance over $F$.

## Encoding the family in one ordinary instance

Form a tensor system of order at most three. Include the multiplication and unit of $R$, the inclusions $J\to R$, $W\to J$, and the quotient $J\to V$. Include the evaluation pairing of $W$ with its dual to a scalar line pinned by the vector 1. Give the $E$-coordinate space, viewed over $F$, a fixed basis via the first basis vector and a linear shift that carries each basis vector to the next and the last to zero. The two marks force the $E$-map to be the identity. Include $V_E$ and $W^*\otimes_F E$, linked to their factors by their tensor-product maps.

Let $D=F^{\mathcal L}$, with coordinate primitive idempotents $e_\lambda$. Include its multiplication and unit and the linear map $D\to W^*\otimes_F E$ defined by $e_\lambda\mapsto\lambda$. The $D$-map permutes the primitive idempotents, and the last map forces the permutation to be $e_\lambda\mapsto e_{\lambda'}$ where $\lambda'=\lambda h^{-1}$. The correspondence uses the same $h$ as the encoded algebra isomorphism. A mismatch in the number of minimizing labels proves the original tensors are in different ordinary orbits and yields a fixed negative comparison before compilation.

Use the additional $F$-algebra
$$
B_{\mathrm{ext}}=\prod_{\lambda\in\mathcal L}\Lambda_E K_\lambda.
$$
Include its multiplication and unit. Attach $D\to B_{\mathrm{ext}}$ by sending $e_\lambda$ to the unit of the $\lambda$-factor, and attach $E\to B_{\mathrm{ext}}$ diagonally as scalars. Include the direct sum $U=\bigoplus_{\lambda\in\mathcal L}K_\lambda$ of degree-one pieces via the linear maps $U\to B_{\mathrm{ext}}$ and
$$
U\longrightarrow V_E\otimes_F D,\qquad
x_\lambda\longmapsto x_\lambda\otimes e_\lambda.
$$
Here $V_E\otimes_F D$ is linked by its tensor-product map. The maps out of $U$, the label idempotents, and the fixed $E$-action force the map on each exterior factor to be the functorial exterior map induced by $g_E|_{K_\lambda}$. Each factor is generated as an $E$-algebra by the unit and its degree-one part, including when that part is zero. Conversely these exterior actions always give the required isomorphism on $B_{\mathrm{ext}}$.

Include $H=\bigoplus_{\lambda\in\mathcal L}\Lambda_E^c K_\lambda$ with its inclusion into $B_{\mathrm{ext}}$. Let $P$ be a one-dimensional $F$-role with coordinate vector $p$. Link $E\otimes_F P$ by the tensor-product map. Add the linear map $H\to E\otimes_F P$ with $\lambda$-component $z\mapsto Q_\lambda(z)\otimes p$. Its covariance and its nonzero values force the $P$-map to be multiplication by $\det g$ in the coordinate vectors. Every algebra isomorphism extends to all these data by taking this scalar on $P$.

Construct also the exterior $F$-algebra $\Lambda_F W$ with its multiplication, unit and degree-one inclusion. Link a one-dimensional role $Q$ to its top exterior power by sending its coordinate vector to the wedge of the chosen $W$-basis. The same generator argument forces the action on $Q$ to be $\det h$. Attach a final one-dimensional role with a map $P\times Q$ to that role that multiplies coordinates. Pin its vector to have coordinate 1 at the source and $\sigma\delta$ at the target. This enforces exactly the desired raw sign by the determinant calibration. All system isomorphisms restrict to eligible algebra isomorphisms with that sign, and all such algebra isomorphisms give system isomorphisms.

The largest exterior product algebra used here has $F$-dimension at most $e\,3^{ew}2^c$, and the separate exterior algebra on $W$ has dimension $2^w$. The dense arrays for all roles have polynomial size under the bound in the theorem. There is one product algebra for the entire parameter set, one direct sum for all the degree-one pieces, and one direct sum for all their top lines. Accordingly the number of roles and tensors is fixed even when the number of contractions grows. The fixed-signature tensor-system reduction gives one ordinary raw 3-tensor instance in deterministic polynomial time. When $c=0$, omit the $U$-role and the degree-one inclusion into $B_{\mathrm{ext}}$, since $B_{\mathrm{ext}}$ is already generated by $E$ and the label idempotents. In the even-$d$, even-$n$ branch $W$ has odd positive dimension, so its exterior role has nonzero degree-one piece. The elementary odd-dimension cases require no exterior encoding. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

## Fixed width with logarithmic geometric corank

A deterministic rule for selecting $e$ from the shared input dimensions gives the same reduction whenever $ew+c$ satisfies the logarithmic bound. First handle the elementary parity cases. In the remaining branch $w\ge1$, so the bound implies $3^e=\operatorname{poly}(L)$. Construct the selected extension by enumerating monic polynomials of degree $e$ over $F$ and testing irreducibility. Supply the same coordinate field on both endpoints. Once this field is constructed the preceding proof applies verbatim.

In particular, for fixed $w$ choose the least $e$ with $3^e>n$. The minimum corank over this extension equals the minimum corank over an algebraic closure of $F$. Indeed, a nonzero minor of maximum achievable rank is a nonzero polynomial in $w$ contraction coordinates of total degree at most $n$. A polynomial of degree less than $3^e$ in each variable vanishing on the full extension-field grid is zero, by induction from the univariate root bound. Some point of the grid therefore attains the geometric maximum rank. Thus fixed $w$ and logarithmic geometric corank suffice even when the optimum is unattainable over $F$ itself.

For example, take $w=3$ and let $V$ be the direct sum of two copies of $F^3$ and a symplectic space of dimension $2m$. On each $F^3$, take the alternating map to $F^3$ given by the exterior square in its usual three coordinates. On the symplectic space, take its symplectic form times the first coordinate vector of $W=F^3$. Set the cross-summand products to zero. These maps define an associative cube-zero multiplication by making every radical product involve two tangent vectors and setting their outputs in $W$. Any nonzero contraction has rank two on each $F^3$, and its action on the symplectic space is nonsingular whenever its first coordinate is nonzero. Every contraction is singular and the minimum corank is two. One may add an arbitrary symmetric $W$-valued bilinear part without changing these commutator ranks. The conclusion applies at unbounded even tangent dimension and even algebra dimension.

## One-instance consequence and proof provenance

One-sign TI admits the conjunction of one signed comparison with an ordinary comparison by the determinant-neutral conjunction construction. Given the two comparisons here, replace the eligible member by the ordinary comparison just constructed, and represent an unrestricted odd-automorphism member by reflection when needed. Apply the conjunction construction to produce one signed instance.

This is an informal proof. It extends the earlier nonsingular Pfaffian evaluation diagram for alternating matrix pencils by extracting the tangent determinant from the commutator, including when every form in the pencil is singular. It reuses the raw recognition argument for the square-zero theorem. The unrestricted cube-zero case without the hypotheses remains open in this argument.
