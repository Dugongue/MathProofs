# Unbounded arithmetic genera at the second Betti number three

**Theorem.** For each $m\ge1$ there are at least $(3^{m-1}+1)/2$ pairwise non-homotopy-equivalent, stably parallelizable, closed simply connected smooth six-manifolds with $b_2=3$, $b_3=0$, and torsion-free homology, whose cohomology rings are pairwise isomorphic over $\mathbb Z_{(p)}$ for each prime $p$. They all have the same rational homotopy type. The local cohomology isomorphisms preserve orientation. This is a local-global failure for the cohomology test for degree-one maps and for integral cubic isometry.

Set $K=\mathbb Q(i)$ and $\mathcal O_m=\mathbb Z+3^m\mathbb Z[i]$. Use invertible fractional $\mathcal O_m$-ideals. For such an ideal $I$ let $N(I)>0$ be its rational lattice covolume relative to $\mathcal O_m$. This norm is multiplicative. Indeed on localization at a rational prime $p$ an invertible ideal is principal over the semilocal order, and the valuation of its covolume is the valuation of the determinant of multiplication by a generator. The determinant is the field norm. Define the normalized norm quadratic on the lattice $I$ by
$$
q_I(x)=N_{K/\mathbb Q}(x)/N(I).
$$
Each local generator reduces $q_I$ to a $p$-unit times the ordinary norm on $\mathcal O_{m,(p)}$. Hence its values are integral at every prime and therefore integral over $\mathbb Z$. Its coefficients in an integral basis are integral by polarization on the basis and their pairwise sums. Over the reals it is positive definite.

The ideal class exact sequence for a quadratic order of conductor $3^m$ identifies its Picard group with
$$
(\mathbb Z[i]/3^m\mathbb Z[i])^\times\big/
  ((\mathbb Z/3^m\mathbb Z)^\times\cdot\{\pm1,\pm i\}).
$$
This is the extension-contraction sequence for ideals prime to the conductor, using that the maximal order $\mathbb Z[i]$ is principal. More explicitly, every invertible class has a representative prime to the conductor by approximation to its local generators. It extends to a principal ideal in the maximal order, and the choice of generator at the conductor is determined modulo rational residue units and maximal-order units. Equality of those residue classes is exactly the condition that the ratio can be taken in the order locally at the conductor, which is the kernel of the extension map. Since $3$ is inert in $\mathbb Z[i]$, the numerator has order $8\cdot 3^{2m-2}$. The denominator has order $4\cdot 3^{m-1}$. Thus the Picard group has order $2\cdot3^{m-1}$ and its subgroup of squares has order $3^{m-1}$. [Ring class exact sequence and class number formula](https://www.wiley.com/en-us/Primes+of+the+Form+x2%2Bny2%3A+Fermat%2C+Class+Field+Theory%2C+and+Complex+Multiplication%2C+3rd+Edition-p-9781119536355)

Choose ideals $I,J$ whose classes lie in this square subgroup. Then $I=aJL^2$ for some $a\in K^\times$ and invertible fractional ideal $L$. At each prime choose a generator $b$ of $L_{(p)}$. Such a generator lies in $K$, since the localization is a semilocal ring inside $K$ and its invertible modules are free of rank one. The scalar $N(L)/N(b)$ is a unit in $\mathbb Z_{(p)}$, by the determinant calculation of local valuation. Multiplication by
$$
a b^2\,N(L)/N(b)
$$
takes $J_{(p)}$ onto $I_{(p)}$, and its field norm is exactly $N(I)/N(J)$. It is therefore a $\mathbb Z_{(p)}$-linear isometry from $q_J$ to $q_I$. The same norm calculation for any nonzero $b\in K$ gives an isometry over $\mathbb Q$.

Conversely, an integral isometry $J\to I$ of the norm forms extends to a rational linear norm similitude $T$ of $K$. Divide by $T(1)$ to obtain a norm isometry fixing $1$. Polarization against $1$ shows that it preserves trace. It must send $i$ to $i$ or $-i$, since these are exactly the trace-zero vectors of norm one in $K$. Thus $T$ is multiplication composed with identity or conjugation. Integral isometry of the forms forces $[I]=[J]$ or $[I]=[J]^{-1}$, where conjugation inverts ideal classes. For the last statement, locally an invertible ideal times its conjugate has generator equal to the determinant norm of a local generator, which differs from its rational lattice norm only by a local unit. Hence globally $I\bar I=N(I)\mathcal O_m$.

Now use the diagonal cup cubic $6tq_I(x,y)$ on a rank-three lattice. Its monomial coefficients are multiples of six, so the framed realization by surgery constructs a smooth manifold with this diagonal and all the stated tangential and homological properties. Its orientation and Poincaré duality recover the whole cohomology ring from this cubic, because the trilinear polarization determines the product $H^2\otimes H^2\to H^4$ and $H^4$ is dual to $H^2$. The local isometries of the binary forms extend by fixing $t$, and therefore give orientation-preserving isomorphisms of the cohomology rings over $\mathbb Z_{(p)}$.

The factor $t$ is the unique rational linear factor of the cubic because $q_I$ is positive definite on its two-dimensional quotient. An integral cubic equivalence must carry this factor to a unit multiple of itself. Its induced map on $t=0$ is unimodular and satisfies the binary norm isometry after canceling the common linear factor and using positivity. A reversal of orientation merely reverses the overall sign and can be absorbed by $t\mapsto-t$. Distinct classes modulo inversion therefore give non-homotopy-equivalent manifolds, by invariance of the integral cup cubic. The number of those classes in the square subgroup is $(3^{m-1}+1)/2$, since it has odd order. Finally the rational cubic isometries yield rational cohomology algebra isomorphisms. Simply connected closed six-manifolds are formal by Miller's formality theorem, so these are actual rational homotopy equivalences. [Miller, On the formality of $(k-1)$-connected compact manifolds](https://mathscinet.ams.org/mathscinet-getitem?mr=528561)

The surgery construction starts directly with the diagonal cubic whose coefficients are divisible by six. [Framed realization](IntegralTensorManifolds.md)
