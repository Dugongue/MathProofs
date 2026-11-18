# Many colored elementary abelian groups with the same second-game invariant

For every fixed number of pebbles, Hella’s second bijective game fails to identify some nonisomorphic two-colored elementary abelian $2$-groups. More strongly, write $s\ge2$ for the number of pebbles. For every sufficiently large $t$, one $s$-pebble game-equivalence class contains at least
$$
2^{\binom{t}{s+2}-t^2-1}
$$
pairwise nonisomorphic groups of order $2^{t+\sum_{j=1}^s\binom tj}$. All of these examples have the same Boolean color degree. The third bijective game identifies every colored group in one round with three pebbles. This strengthens the negative answer to Grochow–Levet’s ordinary counting-WL Question 8.3. The uncolored question about the first two games has a separate scope. [Parallel Complexity, Question 8.3](https://arxiv.org/html/2112.11487v7#S8) · [Descriptive Complexity, Questions 5.1–5.5 and the second game](https://arxiv.org/html/2209.13725v7#S5) · [Earlier one-point shear proof](https://github.com/Dugongue/MathProofs/tree/main/ColoredAbelianWL)

## The two-point extension

All vectors and colors are over $\mathbb F_2$. Let $X=\mathbb F_2^t$, and let $Y$ have coordinates indexed by the nonconstant squarefree monomials of degree at most $s$ on $X$. Write $\Phi(x)$ for the vector of their values. For each Boolean polynomial $f$ of degree at most $s+2$ with $f(0)=0$, color $X\oplus Y$ by
$$
c_f(x,y)=\langle y,\Phi(x)\rangle+f(x).
$$

An invertible linear coordinate change on $X$ acts invertibly on the space of polynomials of degree at most $s$ that vanish at zero. Indeed substitution followed by $x_i^2=x_i$ preserves the bound and vanishing, and the inverse substitution has the same property. Thus we may use the monomials of any adapted $X$-basis, changing coordinates on $Y$ by the dual transform.

In the second bijective game Duplicator announces one bijection before Spoiler chooses the two new positions. We prove that any two colorings $c_f,c_g$ above admit a winning Duplicator strategy with $s$ pebbles. The invariant on retained positions is that some linear map $L:U\to Y$, where $U$ is the span of the retained $X$-coordinates, sends marked elements $(u,y)$ to $(u,y+Lu)$ and satisfies
$$
\langle Lu,\Phi(u)\rangle=f(u)+g(u)\qquad(u\in U).
\tag{1}
$$

The invariant holds with no marks and survives forgetting positions by restriction. The induced shear is a color-preserving linear isomorphism on $U\oplus Y$. In particular it gives an isomorphism on the entire marked generated subgroup, which also suffices for the two initial-color conventions in the source.

After removing the positions to be moved, write $X=U\oplus W$ and put
$$
E(u,w)=f(u+w)+g(u+w)+\langle Lu,\Phi(u+w)\rangle.
$$
This has degree at most $s+2$ and vanishes identically at $w=0$. In adapted coordinates every monomial of $E$ therefore includes a $W$-variable. We construct $P:W\to Y$ with $P(0)=0$ such that
$$
\langle P(z+w)+P(z),\Phi(u+w)\rangle=E(u,w)
\qquad(u\in U,\ z,w\in W).
\tag{2}
$$

Do this separately for each monomial $m$ of $E$. If $\deg m\le s+1$ and $m$ has degree at least two, choose a $W$-factor $w_i$. Put $z_i$ in the feature slot $m/w_i$, whose degree lies between one and $s$. Its difference in direction $w$ contributes $m$. If $m=w_i$, put $z_i$ in the slot $w_i$ itself and use $w_i^2=w_i$.

If $\deg m=s+2$, there are at least three $W$-factors because $\dim U\le s-1$. Choose three such factors with indices $i,j,k$. For each of the three unordered pairs $a,b$ among them, put $z_a z_b$ in slot $m/(w_a w_b)$, whose degree is $s$. This contributes
$$
\bigl(z_a w_b+w_a z_b+w_a w_b\bigr)\frac{m}{w_a w_b}.
$$
Each term $z_a m/w_a$ occurs twice and cancels. The remaining three copies of $m$ sum to $m$. Adding these contributions gives $P$ satisfying (2).

Duplicator now announces the single bijection
$$
(u+w,y)\longmapsto(u+w,y+Lu+P(w)).
$$
Suppose the two selected points have $W$-coordinates $w_1,w_2$. Extend $L$ to $U+\operatorname{span}\{w_1,w_2\}$ by giving $w_i$ the value $P(w_i)$. This is consistent when either is zero or they coincide. The cosets with $W$-coordinates $w_1,w_2$ satisfy (1) by (2) with $z=0$. The coset with $W$-coordinate $w_1+w_2$ satisfies (1) by (2) with $z=w_1$ and $w=w_1+w_2$. These cosets and $U$ exhaust the larger span. This argument includes a single selection. The bijection is its own inverse, so it also handles selections specified on the second domain. The invariant survives every round.

Taking $t=s+2$, $f=0$, and $g=x_1\cdots x_{s+2}$ gives nonisomorphism by Boolean degree, because invertible linear substitution preserves degree. The underlying rank is $2^{s+2}-2$. Adding unused $Y$-coordinates and leaving them fixed in the shear gives a lower bound of $\log_2\log_2 |X\oplus Y|-O(1)$ pebbles for counterexamples at each sufficiently large rank. In the third game, Duplicator’s first bijection either has a color mismatch or fails to preserve some multiplication triple $x,y,xy$. Spoiler selects the offending point or triple in one move.

## Recovering the top form and counting isomorphism types

Set $d=s+2$. The degree-$d$ part of a Boolean polynomial is naturally an exterior form in $\Lambda^d X^*$ when considered modulo terms of smaller degree. In the associated graded algebra the variables square to zero because $x_i^2=x_i$, and the squarefree products of each degree form a basis. Thus the associated graded is the exterior algebra over $\mathbb F_2$, with its usual linear change of variables. For a translation by $a\in X$, the degree-$(d-1)$ part of $f(x+a)+f(x)$ is the contraction $\iota_a\omega_f$, where $\omega_f$ is the degree-$d$ form. This follows by keeping the terms obtained by replacing exactly one variable in a degree-$d$ monomial by its $a$-coordinate.

Restrict to $f$ for which the map $a\mapsto\iota_a\omega_f$ is injective. The subspace $Y$ is then intrinsic to the coloring. It is the set of translations $v\in X\oplus Y$ for which the function $c_f(\,\cdot+v)+c_f$ has degree at most $s$. The term $\langle y,\Phi(x)\rangle$ has degree at most $s+1$, so any difference of it has degree at most $s$. A translation with nonzero $X$-component contributes the nonzero degree-$(s+1)$ contraction of $f$. A translation in $Y$ leaves $f$ fixed.

Every group isomorphism of the underlying elementary abelian groups is linear, and invertible linear maps preserve the degrees of these differences. Consequently any color isomorphism preserves $Y$ and induces a linear automorphism $A$ on the quotient $X$. Comparing top degrees in the coloring equation shows that $\omega_f$ and $\omega_g$ must be equivalent under $A$.

Conversely, suppose $A\in\mathrm{GL}(X)$ aligns the two top forms. Write $\Phi(Ax)=C_A\Phi(x)$ with $C_A$ invertible. The difference $f(x)+g(Ax)$ has degree at most $s+1$ and zero constant term. It is of the form $\langle Kx,\Phi(x)\rangle$ for a linear $K:X\to Y$. Factor each monomial of degree at least two into one variable times a feature, and use $x_i^2=x_i$ for degree one. Then
$$
(x,y)\longmapsto \bigl(Ax,C_A^{-\mathsf T}(y+Kx)\bigr)
$$
preserves the colors. Hence in this family the isomorphism classes are exactly the orbits of the top exterior forms.

There are $2^{\binom td}$ top forms. For a fixed nonzero $a$, an invertible change of basis takes it to the first basis vector. In that basis, $\iota_a\omega=0$ imposes one independent zero-coefficient condition for each degree-$d$ monomial involving the first coordinate. The fraction of forms for which some nonzero $a$ has zero contraction is at most $2^{t-\binom{t-1}{d-1}}$. For fixed $s\ge2$ this is less than one half for all sufficiently large $t$. Each $\mathrm{GL}(t,2)$-orbit has at most $2^{t^2}$ forms. Taking the homogeneous polynomial representatives of the remaining forms gives the claimed count, and every representative has degree $d$.

## A same-degree pair with an explicit distinction

Take $t=2d$ and two disjoint coordinate sets $A,B$, each of size $d\ge4$. Choose $C$ containing two coordinates of $A$ and $d-2$ of $B$. For a set $D$ write $x_D=\prod_{i\in D}x_i$. Consider $f=x_A+x_B$ and $g=f+x_C$. Both first-contraction maps are injective, since their projections to pure $A$ and pure $B$ monomials give distinct monomials for each basis vector.

The rank of the second-contraction map $\Lambda^2 X\to\Lambda^{d-2}X^*$ distinguishes the forms. For $f$ it has rank $2\binom d2$, with the same-half input pairs giving all pure $A$ and $B$ monomials and the mixed input pairs giving zero. For $g$, the projection to the pure monomials on the same-half inputs is still invertible. For $d>4$ its only change is a single off-diagonal entry from an $A$-pair to a $B$-monomial. For $d=4$ there are two changes, from the $A\cap C$ and $B\cap C$ pairs into the output monomials corresponding to the complementary pairs. In either case the change, in the original input and output bases paired by complement, has square zero. A mixed pair contained in $C$ supplies a nonzero mixed monomial, outside the image of the same-half inputs because the pure projection is injective there. Thus the rank for $g$ is larger. The corresponding two colored groups have the same degree and Duplicator still wins the second game with $s$ pebbles.

The statements above are informal proofs about color-preserving group isomorphism.
