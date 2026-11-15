# Sharp invariant degree growth for a single symmetric balanced quartic

AI-assisted informal proof. The input tensors have integer coefficients, and the group and its orbit closures are over the complex numbers.

## Statement

Let $V=\mathbb C^n$ and let $G=\mathrm{GL}(V)$ act on $W=\mathrm{Sym}^2(V)\otimes\mathrm{Sym}^2(V^*)$ by its natural action. Use the inclusion into $V^{\otimes 2}\otimes(V^*)^{\otimes 2}$ with symmetric tensors in both pairs. For a tensor outside the null cone, let its detection degree be the least degree of a positive-degree homogeneous invariant nonzero on it.

1. Every coordinatewise nonnegative $T\in W$ outside the null cone has detection degree at most $n2^{n-1}$.
2. For every $n\ge3$ there is an explicit nonnegative tensor $T_+$ with at most $2n$ nonzero ordered coordinates, all equal to $1$, whose detection degree is exactly
   $$D_n=\frac{(3n+1)2^n-(-1)^n}{9}.$$
   Thus the maximum detection degree for nonnegative tensors is $\Theta(n2^n)$.
3. Changing the sign of just one coordinate gives an integer tensor $T_-$ such that both $G$-orbits are closed and distinct, and both stabilizers consist of the scalar matrices. Every invariant of degree less than $D_n$ agrees on the pair, while a homogeneous invariant of degree $D_n$ distinguishes them.

These statements use the full invariant ring. Any division-free arithmetic formula with addition and multiplication that computes an invariant separating this pair must have at least $D_n$ variable leaves, since the formal degree of a formula is at most its variable leaf count. Repeated squaring in an arithmetic circuit with sharing can produce exponential degree with polynomial size, so the result does not imply a circuit-size or runtime lower bound for orbit-closure intersection.

## 1. Nonnegative supports and incidence determinants

Write $e_i$ for basis vectors and $e^i$ for their duals. A symmetric ordered basis consists of products of the symmetric sums of two basis vectors in each pair, with a single term when the indices agree. The diagonal torus acts on a basis tensor indexed by the two unordered pairs $(a,b)$ and $(c,d)$ with weight
$$w=e_a+e_b-e_c-e_d\in\mathbb Z^n.$$
Here the same notation $e_i$ denotes the corresponding coordinate vector in the weight lattice. Each weight is the sum of two directed incidence columns, each of the form $e_i-e_j$.

For any tensor, the restriction of a homogeneous $G$-invariant to the span of its supported basis tensors can have only weight-zero monomials. Indeed, this subspace is torus-invariant and each variable scales separately, so comparing the distinct monomials and their characters proves the claim. In particular, if a positive-degree invariant is nonzero on the tensor, some nonempty multiset of supported basis weights sums to zero.

For nonnegative tensors the converse holds constructively. Given any such multiset, take one tensor occurrence for each selected weight, with the selected ordered coordinate at that occurrence. For every basis index the total count of primal positions equals the total count of dual positions. Pair these occurrences bijectively by index and contract all pairs. This produces a homogeneous $G$-invariant whose evaluation contains the product of the selected nonzero coordinates. All other summands are nonnegative because the contractions are just sums of products of entries. The evaluation is therefore positive. The least size of a nonempty balanced multiset is exactly the detection degree. Over $\mathbb C$, reductive orbit separation gives the equivalence between existence of such an invariant and being outside the null cone. This also reduces null-cone membership on the nonnegative rational inputs to testing whether the convex hull of their supported weights contains zero, by rational linear programming.

To bound the least multiset size, take a minimal support $S$ admitting a positive real kernel vector for its weight matrix. If the real kernel on this support has dimension greater than one, vary the positive vector along a linearly independent kernel vector until some coordinate first hits zero. The resulting nonnegative vector is nonzero and has smaller support, a contradiction. For $s=|S|$ the rank is thus $s-1$, and $s\le n$ since the weights have coordinate sum zero. Choose $s-1$ independent rows. The signed $(s-1)$-column cofactors of this row submatrix give a nonzero integer kernel vector, either all positive or all negative. The empty cofactor is $1$ when $s=1$. Orient the sign and divide by the coordinate gcd to obtain a positive primitive relation.

Every $r\times r$ minor of the weight matrix has absolute value at most $2^r$. Expand each column as a sum of its two incidence columns and use multilinearity. Each of the $2^r$ resulting determinants is $0$, $1$, or $-1$. To see this last fact for any square submatrix of directed incidence columns, expand by a column with at most one nonzero entry. If there is no such column, every column has one $+1$ and one $-1$, so the sum of the rows is zero and the determinant vanishes. Induction gives the claim including repeated columns, absent rows, and zero columns. Each cofactor above is bounded by $2^{s-1}$ in absolute value. The resulting multiset has size at most $s2^{s-1}\le n2^{n-1}$.

## 2. An integer tensor attaining the exponential scale

Number the basis from $0$ through $n-1$ and take indices modulo $n$. Define
$$
t_0=e_0\otimes e_0\otimes e^1\otimes e^1,
\qquad
t_i=e_i\otimes e_i\otimes(e^{i+1}\otimes e^{i+2}+e^{i+2}\otimes e^{i+1})\quad(1\le i<n).
$$
Put $T_+=\sum_i t_i$ and $T_-=T_+-2t_0$. Their weights are
$$w_0=2e_0-2e_1,\qquad w_i=2e_i-e_{i+1}-e_{i+2}\quad (1\le i<n).$$
For a relation with multiplicities $x_i$, the equations at coordinates $1,2,3,\ldots,n-1$ are
$$
2x_1=2x_0+x_{n-1},\qquad 2x_2=x_1,\qquad 2x_j=x_{j-1}+x_{j-2}\quad(3\le j<n).
$$
The equation at $0$ follows from these because all columns have coordinate sum zero. All solutions are given by
$$x_j=x_1\left(\frac23+\frac13(-1/2)^{j-1}\right)\ (1\le j<n),\qquad x_0=x_1-x_{n-1}/2.$$
In the coefficient of $x_1$ for $j=n-1$, the reduced denominator is $2^{n-2}$, since $(2^{n-1}+(-1)^{n-2})/3$ is an odd integer. Integrality of $x_{n-1}$ requires $2^{n-2}\mid x_1$, and integrality of $x_0$ then requires $2^{n-1}\mid x_1$. Conversely $x_1=2^{n-1}$ makes all coordinates positive integers. This gives the primitive positive kernel vector $x$. Its coordinate $x_0$ is odd since $x_{n-1}/2$ is odd. Summing the geometric progression gives $\sum_i x_i=D_n$. Every nonzero nonnegative integral relation is a positive multiple of $x$. The nonnegative-support criterion now gives the exact detection degree of $T_+$.

On the linear space with basis $t_i$, every homogeneous invariant of degree $0<d<D_n$ restricts to zero. In degree $D_n$, it restricts to a scalar multiple of $\prod_i z_i^{x_i}$, where $z_i$ are the coefficients in that basis. The contraction in Section 1 has a nonzero scalar there. It takes opposite nonzero values on $T_+$ and $T_-$ because $x_0$ is odd. Constants agree, so this proves the claim for arbitrary inhomogeneous invariants of degree below $D_n$ as well.

The two example tensors can be generated in polynomial bit time, using $2n-1$ signed nonzero entries in ordered coordinates or $O(n^4)$ entries if written densely. None of the numbers in the proof of closedness below has to be part of the input. An invariant of degree $D_n$ exists by pairings of positions, regardless of the cost of storing the full pairing or evaluating that contraction.

## 3. Both examples have closed orbits and trivial projective stabilizers

Take the Hermitian norm on the full ordered tensor product for which the standard ordered basis is orthonormal. It is unitary-invariant and restricts to $W$. The $t_i$ are orthogonal. Let $M$ be the matrix of their weights. Section 2 proves $\ker_{\mathbb R}M=\mathbb Rx$. Choose $\lambda>0$ so that the vector with coordinates $\tfrac12\log(\lambda x_i/\|t_i\|^2)$ is orthogonal to $x$. This is possible because its dot product with $x$ is affine in $\log\lambda$ with nonzero slope. Then this vector is $M^T h$ for some real $h$. Acting by $\operatorname{diag}(\exp h_j)$ sends $T_\pm$ to points $v_\pm=\sum_i c_i t_i$ with $|c_i|^2\|t_i\|^2=\lambda x_i$.

For a diagonal Hermitian matrix $H$, the inner product $\langle d\rho(H)v_\pm,v_\pm\rangle$ is the pairing of its diagonal with $\lambda\sum_i x_i w_i=0$. For an off-diagonal matrix unit $E_{ab}$ with $a\ne b$, its derived action sends weight $w_i$ to weight $w_i+e_a-e_b$ or to zero. These weights cannot equal any $w_j$. They differ from $w_i$, and for $i\ne j$ the vector $w_i-w_j$ has coordinate $i$ at least $2$, hence is never a root $e_a-e_b$. Torus weight spaces are orthogonal under the restricted Hermitian norm. Thus all off-diagonal contributions vanish as well. The moment map vanishes at $v_\pm$, so the Kempf–Ness criterion gives closed complex $G$-orbits. The invariant giving opposite values proves that the closed orbits are distinct.

View either tensor as an operator on $\mathrm{Sym}^2(V)$. Its image is the span of $e_i^{\otimes 2}$, because the dual factors in the $t_i$ are distinct symmetric basis elements and every coefficient is nonzero. A stabilizer must preserve that subspace under $\mathrm{Sym}^2(g)$. The squares it contains are exactly the squares of coordinate vectors: a vector with two nonzero coordinates has a nonzero mixed coefficient in its square. Therefore $g$ is monomial. Its permutation permutes the support weights, and must preserve their unique primitive positive relation. All its entries $x_i$ are distinct, since the displayed formula for $x_j$ also gives $x_0$ by setting $j=n$, and the magnitudes $|x_j-2x_1/3|$ decrease strictly as $j=1,\ldots,n$. Hence the permutation is the identity.

For a diagonal stabilizer with entries $\lambda_i$, divide by its scalar to set $\lambda_0=1$. Then $s=\lambda_1$ satisfies $s^2=1$. Put $u=\lambda_2/s$. The equations $\lambda_{i+2}=\lambda_i^2/\lambda_{i+1}$ for $1\le i<n$ give $\lambda_j=s u^{v_j}$, where $v_j=(1-(-2)^{j-1})/3$, including the periodic indices $j=n,n+1$. In particular $s u^{v_n}=1$ and $u^{v_{n+1}}=1$. Now $v_{n+1}=1-2v_n$, so $u^{2v_n}=u^{v_{n+1}}=1$ implies $u=1$. This forces $s=1$ and every $\lambda_i=1$. Thus the effective group $\mathrm{PGL}(V)$ acts with trivial stabilizer at both of these closed orbits.

## 4. Comparison and reuse

- [Derksen–Makam, Sections 3 and 6](https://arxiv.org/html/1902.10773) prove exponential bounds for tuples of cubic forms and tensors under special linear groups, using torus weights and the Grosshans principle. Their criterion for closed orbits with weight supports avoiding root differences gives the closedness step used here.
- [The minimal canonical form of a tensor network, Proposition 4.15](https://arxiv.org/html/2209.14358) gives an exponential detection-degree example for one PEPS tensor under $\mathrm{GL}(D)\times\mathrm{GL}(D)$, already using a recurrence in multiplicities. In the single diagonal $\mathrm{GL}(n)$ action studied here, allowing contractions between the two original positions enlarges the set of contractions, so the product-group lower bound does not directly transfer. The present recurrence makes the stronger single-color balancing constraint explicit, yields two closed orbits, and yields a matching upper bound up to a constant for the nonnegative null-cone problem.
- [Lysikov–Walter, Theorem IV.23 and Questions I.12–I.14](https://arxiv.org/html/2411.04639v2) gives the contraction-invariant context. Our earlier symmetric quartic construction showed completeness of this representation for TOCI. This theorem supplies explicit separation-degree information in that same representation. It neither asserts an upper bound for arbitrary signed or complex tensors nor settles special-linear OCI containment.

The proof uses the previous single-quartic and colored contraction research to identify the relevant representation, an incidence-matrix argument from graph theory for the upper bound, and torus weight arithmetic and the moment map for the closed examples. Priority for the precise combined statement is unestablished. No Lean verification is claimed.

Exact finite checks confirmed the recurrence, positive primitive multiplicities, odd coordinate, degree formula and diagonal-stabilizer gcd for $3\le n\le200$. Exhaustive permutation checks on the support found only the identity for $3\le n\le8$. The general conclusions follow from the proofs above.
