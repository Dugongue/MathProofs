# Scalar obstructions to homogeneous and rank-based reductions of special-linear tensor isomorphism

## Explicit separated scalar multiples

Let $F$ be a field with more than two elements. Represent a three-tensor as a linear matrix map $A(x)$ in $r$ label variables. A transporter from $A$ to $B$ is a triple satisfying
$$
B(fx)g=hA(x)
$$
of invertible maps on the label, column, and row spaces respectively. The special-linear condition prescribes determinant $1$ for all three. Transposes and inverses translate this convention to the usual covariant tensor action.

For nonproportional nonzero forms $L_1,\ldots,L_\ell$ and pairwise distinct positive integers $m_1,\ldots,m_\ell$, put
$$
A(x)=\operatorname{diag}\big(L_1(x)I_{m_1},\ldots,L_\ell(x)I_{m_\ell}\big),\qquad N=\sum_i m_i.
$$
Assume the list includes the $r$ coordinate forms and their sum. For every $a\in F^\times$, $A$ and $aA$ are ordinarily isomorphic. Their exact special-linear scalar-ray condition is
$$
A\cong_{\rm SL}aA
\quad\Longleftrightarrow\quad
\exists\lambda\in F^\times\ \big(\lambda^r=1\ \text{and}\ (a\lambda)^N=1\big).
$$

To prove it, take the determinant of $(aA)(fx)g=hA(x)$ as an identity of polynomials in $x$. The respective determinant factorizations show that $f$ permutes the projective classes of the forms $L_i$ preserving their multiplicities $m_i$. The polynomial ring over $F$ is a unique factorization domain, and the forms are irreducible and pairwise nonassociate. The distinct multiplicities therefore force every form line to be fixed. Fixing the coordinate form lines makes $f$ diagonal, and fixing their sum makes it scalar, say $f=\lambda I_r$. The determinant-one condition for $f$ is $\lambda^r=1$. The same determinant identity now gives $(a\lambda)^N=1$ if $g$ and $h$ have determinant one. Conversely, the two equalities give the transporter $f=\lambda I_r$, $g=I_N$, and $h=a\lambda I_N$ of determinant one in all three modes. Ordinary isomorphism always holds by taking $f=I_r$, $g=I_N$, and $h=aI_N$.

The following explicit examples give failures of special-linear equivalence over every such field.

- In characteristic different from two take $(r,N)=(3,11)$ with forms $x_1,x_2,x_3,x_1+x_2+x_3$ of multiplicities $1,2,3,5$. Exactly the scalars $a$ with $a^{33}=1$ preserve the special-linear orbit. Necessity follows by cubing $(a\lambda)^{11}=1$. For sufficiency, $a^{11}$ is a cube root of unity and raising cube roots of unity to the eleventh power is bijective. In particular $a=-1$ separates the two orbits.
- In characteristic two take $(r,N)=(2,8)$ with forms $x_1,x_2,x_1+x_2$ of multiplicities $1,2,5$. A field of characteristic two has no nontrivial roots of unity whose order divides a power of two. Thus the displayed ray condition reduces to $a=1$, and every other nonzero scalar separates the two orbits.

Both examples have full support in each of the three modes. The label flattening is injective because the coordinate forms occur. The column and row flattenings are injective because $A(x)$ is invertible over $F(x_1,\ldots,x_r)$. A common null vector in the slices or their transposes would give a null vector over this extension. Consequently the examples do not rely on missing directions that could absorb a determinant. Over $\mathbf F_2$, every invertible matrix already has determinant one.

## No homogeneous map can serve as an objectwise reduction

Suppose a tensor map $\Psi$ satisfies $\Psi(aT)=a^d\Psi(T)$ for every $a\in F^\times$ on its domain, for some fixed integer $d$. There are no degree, dimension, equivariance, or computation bounds. Then $\Psi(aT)$ and $\Psi(T)$ are ordinarily isomorphic, since multiplication by $a^d$ can be absorbed in one output mode. This applies to every homogeneous polynomial tensor map, and to a homogeneous rational tensor map defined at the displayed separated pair. Hence an objectwise reduction
$$
A\cong_{\rm SL} B\quad\Longleftrightarrow\quad \Psi(A)\cong_{\rm GL}\Psi(B)
$$
is impossible for any such map on all inputs, even when restricted to the full-support examples above at the indicated shapes. This obstruction also applies to any collection of independently computed homogeneous output tensors when the target equivalences allow independent output bases for those outputs.

## Exact test for homogeneous blocks with shared output summands

Decompose the three output spaces as
$$
X=\bigoplus_{i\in I}X_i,\qquad
Y=\bigoplus_{j\in J}Y_j,\qquad
Z=\bigoplus_{k\in K}Z_k .
$$
Suppose each block $\Psi_e(T)\in X_i\otimes Y_j\otimes Z_k$, $e=(i,j,k)$, is homogeneous of degree $d_e$ under input scaling. Degrees may differ across blocks, and fixed padding has degree zero. An identically zero block can be omitted.

Fix $T,a$. Let $E$ be the blocks at which $\Psi_e(T)\ne0$. The active set is the same at $aT$. A change of output basis which multiplies each output summand by a scalar carries $\Psi(T)$ to $\Psi(aT)$ exactly when
$$
\alpha_i\beta_j\gamma_k=a^{d_e}\qquad(e=(i,j,k)\in E)
$$
has a solution in $F^\times$. Necessity follows by comparing the two scalars on each nonzero block tensor. Sufficiency follows by applying the block-scalar basis changes in all three modes. This criterion concerns the stated class of basis changes.

Let $D$ be the integer matrix whose rows are indexed by $E$ and columns by the disjoint union of output summand indices. Each row has a $1$ at each of its three incidences and zeros elsewhere. For a finite field of order $q$ put $Q=q-1$. A generator of $F^\times$ identifies the equations with the linear congruences
$$
D u \equiv z d \pmod Q,
$$
where $a$ is the generator to exponent $z$ and $d=(d_e)_{e\in E}$. In particular the block-scalar solution exists for every $a$ exactly when
$$
d\in D\mathbf Z^{|I|+|J|+|K|}+Q\mathbf Z^{|E|}.
$$
A generator is unnecessary for testing one chosen $a$. Append the columns of $QI_{|E|}$ to $D$, take a basis of the full-rank column lattice, and put that basis in Smith normal form. Let $U$ denote the unimodular row transform and $s_i$ the positive diagonal entries. Each $s_i$ divides $Q$, since the transformed lattice contains $Q\mathbf Z^{|E|}$. Apply the monomial row transform to $w=(a^{d_e})_e$ to obtain $\widetilde w_i=\prod_e w_e^{U_{ie}}$. The block-scalar equations have a solution exactly when
$$
\widetilde w_i^{Q/s_i}=1\qquad\text{for all }i .
$$
Indeed the extra columns evaluate to $1$ on the finite field multiplicative group, integral changes of lattice generators preserve the monomial image, and on a cyclic group of order $Q$ the $s_i$-power image is precisely the subgroup killed by $Q/s_i$. This gives a deterministic polynomial bit-time test in the dimensions of $D$, the exponent bit lengths, and the explicit field bit length. [Kannan and Bachem, integer normal forms](https://epubs.siam.org/doi/10.1137/0208040)

For all fields, an integer solution $D u=d$ gives explicit output scalars $a^{u_v}$. Consequently any architecture whose entire support admits that solution collapses all input rays. More generally the congruence condition suffices over a finite field. These architectural conditions also suffice for every subset of the support. They cover arbitrary block direct sums, arbitrary fixed padding on disjoint summands, and block diagonal padding in the two matrix modes even when every block shares the same complete label space. In these cases each degree can be assigned to an unshared summand of its block. In particular, multiplying the data by repeating a direct summand and attaching independent constant rank markers along the shared-label rows and columns cannot by themselves make an objectwise special-linear reduction.

A further sufficient rule is that every nonempty set of support edges has an edge containing a summand used by no other edge of that set. Repeatedly remove such an edge. Reinsert edges in reverse order, choosing a value on the private summand to realize the desired degree after the other summands are assigned. A summand private at removal time has not been constrained by any already reinserted edge. Free values can be set to zero. This constructs integer solutions for every degree vector.

When one mode has a single summand, the support in the other two modes is a bipartite graph. Its block-scalar equations are feasible for a fixed $a$ exactly when every graph cycle has alternating degree sum $b$ satisfying $a^b=1$. The scalar for the single summand can be absorbed into the row scalars. The equations on a spanning forest are solved by propagating a row or column scalar along each tree. A non-tree edge is consistent precisely when the alternating product of the prescribed scalars along its fundamental cycle is $1$. Multiplication around any cycle proves necessity. In particular forests always collapse rays, and a four-edge cycle is the smallest possible failure in a simple matrix block support.

## Rank-only tests and adaptive use

For the separated $A,aA$, every labeled contraction has identical rank at the same contraction coordinates, over every field extension. A contraction with fixed vectors or covectors scales by $a$, and multiplication of a nonzero tensor by a nonzero scalar preserves tensor rank and all flattening ranks. In the matrix-pencil presentation this includes $\operatorname{rank} A(x)$ for every $x$. It also gives equality of the entire determinantal rank subschemes in the same coordinates. Each size-$j$ minor of $(aA)(x)$ is $a^j$ times the corresponding minor of $A(x)$, so the defining ideals coincide.

More generally, any rank probe whose queried matrix has entries all homogeneous of the same degree in the rescaled input gives identical answers on $A$ and $aA$. This covers probing individually labeled algebraic rank loci after such a construction. It also covers arbitrary ordinary isomorphism comparisons involving transformed outputs from the balanced block maps above. Replacing any occurrence of the second input $A$ by $aA$ changes each such output within its ordinary isomorphism class. This preserves the result of comparison to any other output, including a constant reference tensor.

This also rules out an adaptive decision procedure whose only access to the pair is through such scalar-invariant rank probes and ordinary-isomorphism comparisons. The chosen queries may depend on previous answers. Compare the input pairs $(A,A)$ and $(A,aA)$ and induct on the transcript. At each stage the same preceding answers produce the same next query, and the invariances give the same answer. The procedures therefore have the same final output on an affirmative and a negative instance. The transcript argument also applies if each query uses both inputs, provided its outputs satisfy the specified homogeneity and balance with respect to rescaling the second input alone. It allows random choices by coupling the same choices between the two runs.

## Sharp boundary for the block-scalar criterion

Over any field with a nonidentity unit, consider the one-label output matrix
$$
\Psi(t)=
\begin{pmatrix}
1&t\\
1&1
\end{pmatrix}.
$$
The four scalar blocks on its row-column support are homogeneous with degrees $0,1,0,0$. At $t=1$ the determinant is zero. At $t=a\ne1$ the determinant is $1-a\ne0$. The outputs therefore differ even in ordinary rank. The alternating degree sum on the four-edge cycle is a unit integer, so the block-scalar equations fail for exactly these $a$. This is the smallest support cycle in the one-label bipartite model. The example shows how overlapping constant and input-dependent blocks can defeat the ray-collapse criterion without increased polynomial degree.

The obstructions here concern homogeneous objectwise maps, the stated block-scalar architecture, and algorithms whose observations all preserve the separated rays. An ordinary-TI reduction could use inhomogeneous probes, data-dependent transformations, or coupled basis constraints outside these classes. The unrestricted reverse reduction remains open here. This is a paper proof with no Lean certificate. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)
