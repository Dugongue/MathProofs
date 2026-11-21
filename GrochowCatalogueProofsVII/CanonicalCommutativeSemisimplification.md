# A canonical rational closed representative for triangularizable tuples

## GP-0670

Given a rational tuple $(A_1,\dots,A_m)$ of $n$ by $n$ matrices, with $\operatorname{GL}_n(\mathbb C)$ acting by simultaneous conjugation, one can recognize in deterministic polynomial bit time whether its semisimplification is commutative. On this recognizable class one can return a canonical rational representative of its unique closed orbit. The class includes all commuting tuples and noncommuting tuples admitting a common complete flag over $\mathbb C$. Rational diagonalizability of individual matrices is unnecessary.

### Recognizing the class

Construct the unital matrix algebra $E$ generated over $\mathbb Q$ by the $A_i$. Start from the identity, multiply each retained basis word on the right by all generators, and retain only linearly independent words. The process has at most $n^2$ insertions. Stability under right multiplication makes the result a basis of the generated algebra.

The radical of the trace pairing $(u,v)\mapsto\operatorname{tr}(uv)$ on $E$ is the Jacobson radical $J(E)$. To see this, work after extension to $\mathbb C$. A composition filtration of the given faithful module gives the same trace as its associated semisimple module. Its annihilator in $E_\mathbb C$ is exactly the Jacobson radical. Indeed, an element of that annihilator strictly lowers the filtration, so the annihilator is a nilpotent ideal, and the Jacobson radical annihilates every simple factor. Thus every simple matrix block of the semisimple quotient acts with positive multiplicity. The trace pairing there is the direct sum of the ordinary matrix trace pairings multiplied by those positive multiplicities, and is nondegenerate in characteristic zero. The computation descends through the rational pairing matrix. It identifies the radical by exact linear algebra. Check that every commutator of basis words belongs to it. This is equivalent to commutativity of $E/J(E)$.

### A canonical primitive element

In the commutative case the diagonal characters on a composition filtration give a multiset of joint points $\alpha^{(a)}\in\mathbb C^m$ with positive multiplicities $\mu_a$, indexed by the distinct joint points. There are $h\le n$ of them. For every nonnegative integer $t$ define $B(t)=\sum_{j=1}^m t^{j-1}A_j$. For any two distinct joint points, their evaluations on this curve coincide at at most $m-1$ values of $t$. Among the first $1+(m-1)\binom n2$ nonnegative integers there is therefore a $t$ separating every joint point.

For each candidate count the distinct roots of the characteristic polynomial of $B(t)$ by its squarefree degree. Choose the least candidate attaining the largest count $h$. Both $h$ and this choice depend only on the joint multiset. Let $B=B(t)$ and denote its distinct eigenvalues by $\beta_1,\dots,\beta_h$, with the corresponding multiplicities $\mu_a$. For each $j$, the unique polynomial $p_j$ of degree less than $h$ with $p_j(\beta_a)=\alpha^{(a)}_j$ is computed over $\mathbb Q$ by the linear system
$$
\sum_{r=0}^{h-1} p_{j,r}\operatorname{tr}(B^{r+s})
=\operatorname{tr}(A_j B^s),\qquad 0\le s<h .
$$
On the composition filtration, the traces on the right are exactly the diagonal moments $\sum_a\mu_a\alpha^{(a)}_j\beta_a^s$. The coefficient matrix is $V\operatorname{diag}(\mu_a)V^{\mathsf T}$ for the square Vandermonde matrix $V=(\beta_a^r)_{r,a}$. It is invertible. The solution is the desired polynomial.

### Constructing the closed tuple

Factor the characteristic polynomial of $B$ over $\mathbb Q$ into monic irreducibles $P_\nu^{m_\nu}$ and sort the $P_\nu$ by degree and then lexicographically by coefficient list. Let $B_*$ be the ordered direct sum of $m_\nu$ copies of the companion matrix of $P_\nu$ for each $\nu$. Return
$$
\bigl(p_1(B_*),\dots,p_m(B_*)\bigr).
$$

The tuple is conjugate over $\mathbb C$ to the tuple on the associated semisimple module, with the same joint multiplicities. That semisimple tuple belongs to the original orbit closure by rescaling the filtration blocks with a one-parameter subgroup to remove all strictly triangular blocks. Its own orbit is closed by direct equations: the corresponding linear combination $B'$ satisfies the fixed squarefree polynomial $\prod_\nu P_\nu$, has the fixed characteristic polynomial, and all the tuple coordinates are $p_j(B')$. These equations define exactly one conjugacy orbit over $\mathbb C$, since a matrix with squarefree annihilator is diagonalizable and the prescribed characteristic polynomial determines its conjugacy class. By uniqueness of the closed orbit in an affine orbit closure for a reductive group, this is the closed orbit of the input. Every construction used to choose the output depends only on the joint multiset, so two inputs in this class give the same output exactly when their closed orbits agree.

Retained words have length at most $n^2$, trace moments use only powers of degree at most $2n$, and the candidate integers have polynomial bit length. Clearing common denominators in these products and using determinant bounds for linear systems keeps bit complexity polynomial. Univariate rational factoring is deterministic polynomial time. [Univariate rational factoring](https://doi.org/10.1007/BF01457454) · [Orbit-closure background](https://arxiv.org/abs/1911.03990)
