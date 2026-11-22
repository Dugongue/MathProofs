# Exponential explicit witness length for rational Tensor Isomorphism

For every integer $n\ge4$, there are two polynomial-size triangulated, closed, simply connected stably parallelizable smooth six-manifolds with $b_2=O(n)$ and $b_3=0$ that admit maps of nonzero degree in both directions. Every rational cup similitude, in the displayed integral bases, has an entry of bit length $\Omega(2^n)$. The same is true of the pullback on $H^2$ of every map of nonzero degree. There are also isomorphic ordinary three-tensors over $\mathbb Q$, of side $O(n)$ and bounded integer entries, for which every isomorphism triple has a coefficient of bit length $\Omega(2^n)$. This gives a worst-case output bound for explicit rational search, even under a YES promise.

## Quadratic systems with an intrinsic monomial action

Use coordinate variables in two parts
$$
L=\{u,x_0,\ldots,x_n,a\},\qquad
R=\{v_1,v_2,z,y_0,\ldots,y_{n-1},b\}.
$$
For $c\in\{1,2\}$, let $W_c\subseteq\operatorname{Sym}^2(X^*)$ be spanned by the squares of all the coordinates and the following quadrics:
$$
\begin{gathered}
uv_1-uv_2,\qquad x_0z-cuz,\qquad av_2-ab,\\
x_i v_1-u y_i,\qquad x_i y_i-x_{i+1}v_2
\qquad(0\le i<n).
\end{gathered}
$$
Here $X$ is the vector space with the listed coordinates. All off-diagonal monomials are distinct across the pairs, and each pair has nonzero coefficients. In particular the displayed generators and the coordinate squares form a basis of $W_c$.

The only rank-one lines of quadrics in $W_c$ are the coordinate square lines. Indeed, over $\mathbb Q$ a nonzero rank-one symmetric form is a nonzero scalar times a square of a linear form. If that linear form has support of size at least three, its nonzero off-diagonal entries include a triangle. The off-diagonal support graph of $W_c$ is bipartite with parts $L,R$, so this is impossible. If the support has size two, there is exactly one off-diagonal monomial. Each nonzero off-diagonal component of an element of $W_c$ includes both monomials of one of the listed pairs, so support of size two is impossible as well.

An invertible linear change of coordinates carrying $W_c$ to $W_{c'}$ must therefore be monomial. Its permutation preserves the off-diagonal support graph. It also preserves the pairing on edges, since the subspace of off-diagonal quadrics is a direct sum of lines with pairwise disjoint supports of size two, and these supports are precisely the inclusion-minimal nonempty supports in that subspace.

The vertices $u,v_1,v_2$ are individually distinguished by their degrees $n+3,n+1,n+2$. All other vertices have degree at most three. The pair containing the two edges incident at $z$ is identifiable as follows. Besides the two pairs sharing $u$ or $a$, it is the only pair whose two edges share an endpoint. The vertex $z$ has one neighbor $u$ and one neighbor $x_0$, whereas $a$ is adjacent to $v_2$ and $b$. Thus $z$ and $x_0$ are fixed. Now the pair containing $x_i v_1$ identifies $y_i$ by its other edge $u y_i$. The pair containing $x_i y_i$ identifies $x_{i+1}$ by its other edge $x_{i+1}v_2$. Induction fixes every $x_i,y_i$. This argument allows any permutation of other auxiliary vertices consistent with the markers.

Write $s_\xi$ for the scalar on the coordinate line $\xi$ for the induced pullback on $X^*$. Comparing coefficient ratios in the corresponding edge pairs gives
$$
s_{v_1}=s_{v_2},\qquad
s_{x_0}/s_u=c/c',\qquad
s_{x_i}s_{v_1}=s_u s_{y_i},\qquad
s_{x_i}s_{y_i}=s_{x_{i+1}}s_{v_2}.
$$
Consequently $s_{x_n}/s_u=(c/c')^{2^n}$. For $c=1,c'=2$, every transporter has one of these two rational scalars with absolute $2$-adic valuation at least $2^{n-1}$. The bit length of a reduced rational is at least the absolute value of that valuation. The transporter is nonempty. Take $s_u=s_{v_1}=s_{v_2}=s_z=s_a=s_b=1$ and $s_{x_i}=s_{y_i}=2^{-2^i}$ wherever $y_i$ is present. These assignments give equality of every edge-pair line and rescale each coordinate square line.

## From the system to a cubic and a manifold

For each generator $q$ in this basis of $W_c$, introduce one coordinate $t_q$ on another vector space $Y$. Put
$$
F_c(x,t)=6\sum_{q\in\text{the displayed basis of }W_c}t_q q(x).
$$
Diagonal polarization gives an integral symmetric trilinear form $\mu_c$ with diagonal $F_c$. Its entries have bounded absolute value. The locus $\{w: \mu_c(w,w,-)=0\}$ is exactly $Y$: every coordinate square generator forces the associated coordinate on $X$ to vanish, and the cubic has degree one in $t$. Hence an invertible similitude preserves $Y$ and acts on $X\cong (X\oplus Y)/Y$. Comparing terms linear in $t$ shows its quotient map carries one quadratic subspace to the other. Conversely any such map of subspaces extends to a cubic isometry by the inverse induced map on the $t$ coefficients. Thus the two explicit large entries in the pullback argument are positions in the quotient matrix, and their bound applies in the displayed basis to every full cubic similitude.

The triangulated surgery construction for six-manifolds realizes a common factor of six times this cubic with torsion-free homology and zero $H^3$, at polynomial cost. For these equal-Betti manifolds cubic similitude is equivalent to existence of a nonzero-degree map by the rational mapping theorem. A nonzero-degree map induces a rational cubic similitude, so its integral cup-pullback matrix inherits the same bit lower bound. [Triangulated realization](https://github.com/Dugongue/MathProofs/blob/f98f6bdf13cb7ba606f020ef0ea07512028cc9d1/ManinGrochowCrossovers/IntegralTensorManifolds.md) · [Rational maps](https://github.com/Dugongue/MathProofs/blob/f98f6bdf13cb7ba606f020ef0ea07512028cc9d1/ManinGrochowCrossovers/RationalTensorMaps.md)

## From a unital algebra to ordinary Tensor Isomorphism

The contraction radical of $\mu_c$ is zero. Any vector in the radical is first in $Y$ by the square-zero computation; contraction of an element of $Y$ gives its linear combination of the independent quadrics. Put $V=X\oplus Y$. Form the commutative unital associative algebra
$$
A_c=\mathbb Q\oplus V\oplus V^*\oplus\mathbb Q s
$$
with product $v w=\mu_c(v,w,-)$ and $v\varphi=\varphi(v)s$ in positive grades, all products above grade three zero. Its maximal ideal $\mathfrak m$ consists of the positive grades. The product $V\cdot V$ spans $V^*$ by the zero contraction radical, so $\mathfrak m/\mathfrak m^2=V$ and $\mathfrak m^3=\mathbb Q s$. Thus an algebra isomorphism induces a similitude. These algebras are isomorphic by the cubic isometry, which extends to the inverse dual on $V^*$.

Use the two ordinary multiplication tensors of $A_1,A_2$. Every tensor isomorphism gives invertible linear maps $P,Q,S:A_1\to A_2$ with $S(ab)=P(a)Q(b)$, by using the duals of the two input-side transformations if necessary. Put $w=S(1)=P(1)Q(1)$. Both factors are units by surjectivity of the corresponding left and right multiplication maps, hence $w$ is a unit. Commutativity and the identities with one input equal to 1 give
$$
S(ab)=w^{-1}S(a)S(b).
$$
Therefore $f=w^{-1}S$ is a unital algebra isomorphism. It sends the maximal ideal onto the maximal ideal, so $S$ does likewise. The induced map of $f$ on $\mathfrak m/\mathfrak m^2$ is the corresponding grade-one submatrix of $S$, divided by the common nonzero residue of $w$ in $A_2/\mathfrak m=\mathbb Q$. The ratio of the two distinguished quotient coefficients therefore has the same valuation as for the similitude. It follows that the *output-side* matrix $S$ of every isotopy has a coefficient of bit length at least $2^{n-1}$. In the ordinary three-tensor action this is the primal output mode. The argument does not require an estimate on the other two matrices.

All structure constants are bounded independently of $n$. Matrix sizes and input construction times are polynomial in $n$, with tensor side $O(n)$. The exhibited diagonal witnesses have $O(2^n)$ bits per entry. Thus the exponential lower bound is sharp for these instances up to a constant in the bit bound. Explicit-matrix search on rational TI cannot be polynomial time in the dense binary input length, even if decision queries are free. A polynomial-size certificate for rational TI membership in NP would need an encoding that avoids writing every matrix entry explicitly on this family. [Grochow–Qiao, Remark 3.4](https://arxiv.org/html/1907.00309#S3)

The argument is an informal proof. It makes a search-output claim and supplies a family and explicit witnesses.
