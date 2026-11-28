# Heisenberg quotients of closed oriented three-manifold groups

**Theorem.** Fix an odd prime $p$ and let $H_p$ be the Heisenberg group of order $p^3$ over $\mathbb F_p$. Let $M$ be a closed, connected, oriented $3$-manifold given by a finite triangulation. Write $b=\dim_{\mathbb F_p} H^1(M;\mathbb F_p)$ and let $\mu$ be its alternating triple cup form

$$
\mu(x,y,z)=\langle x\smile y\smile z,[M]\rangle.
$$

Then $\pi_1(M)$ surjects onto $H_p$ exactly when $b=2$, $b\ge 4$, or $b=3$ and $\mu=0$. Thus the surjection problem is in deterministic polynomial time. The source is restricted to closed oriented three-manifolds, as in the fixed-target surjection problem considered by Samperton and Weiß. [Samperton and Weiß, Section 1.5](https://arxiv.org/html/2602.02885v2#S1.SS5)

## Reduction to the triple cup form

Write $H_p=\mathbb F_p^3$ with multiplication

$$
(a,b,c)(a',b',c')=(a+a',b+b',c+c'+ab').
$$

Its quotient by the central last coordinate is $\mathbb F_p^2$. A homomorphism $\pi_1(M)\to\mathbb F_p^2$ is specified by two characters $x,y\in H^1(M;\mathbb F_p)$. A lift to $H_p$ is a function $z$ on $\pi_1(M)$ with

$$
z(gg')=z(g)+z(g')+x(g)y(g').
$$

This is possible precisely when the group cohomology class of the cocycle $(g,g')\mapsto x(g)y(g')$ is zero. It is the cup product of the two degree-one classes. The map $H^2(\pi_1(M);\mathbb F_p)\to H^2(M;\mathbb F_p)$ is injective. Indeed, one can construct a $K(\pi_1(M),1)$ from the CW complex $M$ by attaching cells of dimension at least three to kill the higher homotopy groups, and the relative cohomology in degree two is then zero. Consequently the lift exists exactly when $x\smile y=0$ on $M$.

For a lift to be onto, its projection must be onto $\mathbb F_p^2$, which means that $x,y$ are linearly independent. Conversely, if $x,y$ are independent, a lift contains elements projecting to $(1,0)$ and $(0,1)$. Their commutator generates the central subgroup $\{(0,0,c):c\in\mathbb F_p\}$, so the lift is onto.

Poincaré duality pairs $H^2(M;\mathbb F_p)$ perfectly with $H^1(M;\mathbb F_p)$. Thus $x\smile y=0$ is equivalent to $\mu(x,y,z)=0$ for all $z$. Odd characteristic and graded commutativity make $\mu$ alternating. The problem reduces to the existence of two independent vectors with zero contraction against this $3$-form.

## Alternating forms over an odd finite field

Let $V$ have dimension $b$ over $\mathbb F_p$ and let $\mu\in\bigwedge^3 V^*$. For $x\ne 0$, write $B_x(y,z)=\mu(x,y,z)$. Its radical contains $x$. Independent $x,y$ with zero contraction exist exactly when some $B_x$ has radical dimension at least two.

If $b\le 1$, independence is impossible. If $b=2$, every alternating $3$-form is zero. When $b=3$, any independent $x,y$ extend to a basis, so their contraction vanishes exactly when $\mu=0$. For even $b\ge 4$, every $B_x$ has even rank at most $b-1$, hence at most $b-2$.

Suppose that $b$ is odd and $b\ge 5$. Choose a basis and replace the coordinates of $x$ by indeterminates $X=(X_1,\ldots,X_b)$. Write $P_i(X)=(-1)^{i+1}\operatorname{Pf}(B_X^{\widehat{i}})$, where $B_X^{\widehat{i}}$ is the even square matrix obtained by deleting row and column $i$. The column $P(X)$ has homogeneous degree $(b-1)/2$ and satisfies $B_XP(X)=0$. This is the Pfaffian expansion of the alternating matrix obtained by duplicating a row and column of $B_X$, whose Pfaffian is zero.

For any specialization to a field of odd characteristic, $P=0$ is equivalent to $\operatorname{rank}B_x\le b-3$. One direction follows because each principal $(b-1)$-minor is the square of its Pfaffian. For the other, if rank is $b-1$, the adjugate is a nonzero rank-one matrix. It is symmetric because $B_x$ is skew-symmetric and $b-1$ is even. A nonzero symmetric rank-one matrix has a nonzero diagonal entry, so a principal $(b-1)$-minor is nonzero.

At the generic point over $\mathbb F_p(X_1,\ldots,X_b)$, either $P=0$ or $B_X$ has rank $b-1$. In the latter case $X$ spans its radical, and therefore $P_iX_j=P_jX_i$ as polynomial identities for all $i,j$. Coprimality of the distinct variables gives $P_i=X_iq$ for a common homogeneous polynomial $q$ of degree $(b-3)/2$. If $P$ is identically zero, take $q=0$.

There is a nonzero $x\in\mathbb F_p^b$ with $q(x)=0$. For $q=0$ any nonzero vector works. Otherwise $0<\deg q<b$ and the usual Chevalley–Warning argument applies. Modulo $p$, the number of zeros is the sum of $1-q(x)^{p-1}$ over $x\in\mathbb F_p^b$. Each monomial of $q^{p-1}$ has some variable exponent less than $p-1$, so its sum over that variable is zero in $\mathbb F_p$. The number of zeros is therefore divisible by $p$, and it cannot consist of the origin alone. At the chosen nonzero $x$, we have $P(x)=0$, so $\dim\operatorname{rad} B_x\ge 3$. Choose $y$ in that radical outside the span of $x$. This completes the form classification.

## Algorithm

Compute $b$ by linear algebra over $\mathbb F_p$ on simplicial cochains. In the single case $b=3$, choose a cohomology basis and evaluate its triple cup product on a mod-$p$ fundamental cycle using the simplicial cup product. The form vanishes exactly when this one value is zero. These computations have polynomial cost in the triangulation size. $\square$

Verification status is a written mathematical proof.
