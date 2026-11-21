# Tensor orbit closures and polynomial-calculus degree

## GP-0738

For ordinary affine GL orbits the proposed comparison has a negative answer. The origin lies in every orbit closure, by scaling one entire mode. The comparison has a positive answer for affine SL orbit closures in a particularly strong form. Over **every fixed finite field**, there are equally formatted pairs of concise, geometrically nonisomorphic three-tensors with the following properties.

* The hard pair has intersecting geometric SL orbit closures, and every ordinary TI polynomial-calculus (PC) refutation has degree $\Omega(d)$ and monomial size $2^{\Omega(d)}$, where the common format is $d\times d\times d$.
* The easy pair has disjoint geometric SL orbit closures and a bounded-degree, polynomial-size ordinary TI PC refutation.

Orbit closures in this statement are taken over the algebraic closure. The equations refuted are always those of ordinary GL tensor isomorphism with inverse variables and no field equations.

### Hard pair, including conciseness and a cubic format

Use the previous catalogue's sparse GI-to-TI substitution, applied to the bounded-color CFI graph pairs of Grädel–Grohe–Pago–Pakusa, Theorem 6.3. From the original graphs it passes through the bipartite graph extension and then codes of the form $M=[I_k\mid I_k\mid I_k\mid D]$ with $N$ columns. The tensors in Galesi–Grochow–Pitassi–She Proposition 5.5 have the formula
$$
R(M)=\sum_{i=1}^N c_i\otimes e_i\otimes f_0+
\sum_{i=1}^N\sum_{b=1}^2 g_{i,b}\otimes e_i\otimes f_{i,b}.
$$
Here $c_i$ is column $i$ of $M$, the $g_{i,b}$ are additional first-mode basis vectors, the $e_i$ form the second-mode basis and $f_0,f_{i,b}$ form the third. The graph extension has no isolated vertices, so all $c_i\ne 0$. The identity part gives full row rank on their span. In each mode, the displayed terms therefore force full contraction support. The dimensions $a=k+2N$, $b=N$, $c=2N+1$ are pairwise distinct once $k\ge2$.

Every PC line pulls back by the sparse substitution, which sends each variable to zero or a monomial of degree at most four. The images of the initial axioms have constant-degree derivations. A degree-$D$ proof thus produces a proof of degree $O(D+1)$ under the substitution. Multiplication by a target variable is simulated by at most four multiplications by source variables. Consequently both the linear degree lower bound and the exponential monomial-size lower bound transfer from the bounded-color graph equations. The tensor pairs are geometrically nonisomorphic by the published reduction and the graph recovery. [Graph degree and size lower bounds](https://lmcs.episciences.org/5119/pdf) · [GI-to-TI reductions](https://arxiv.org/html/2305.19320#S5) · [Sparse substitution and graph extension](https://github.com/Dugongue/MathProofs/blob/d7366c4348bc03f0e93cb8674db191de32ba58bf/GrochowCatalogueProofsII/SparseTensorPC.md)

For an individual $R(M)$, act on the first factor with diagonal weights $-2N$ on the $k$ core rows and $k$ on the $2N$ other rows. Act trivially on the second factor. Act on the third with weight $4N$ on $f_0$ and $-2$ on each $f_{i,b}$. All three weight sums are zero, and each tensor term has strictly positive weight once $k>2$. So $0$ lies in its SL orbit closure.

Take the direct sum of the three cyclic rotations of $R(M)$, each repeated three times. Do this to both tensors. The resulting format is cubic of side $d=3(a+b+c)$, linear in the graph parameter, and every tensor is concise. Use the above one-parameter subgroups on every block, permuted to match its factor order. The direct sum still degenerates to zero by a one-parameter subgroup of $\mathrm{SL}_d^3$. The padded TI equations restrict to the old ones by setting the transporter and its inverse to the repeated rotated block copies of the old variables, with zeros between blocks. This pulls a PC proof back without increasing its degree or monomial size and maps each axiom to zero or an original axiom.

For geometric nonisomorphism of the direct sums, use the centroid of a concise tensor. It consists of triples of endomorphisms whose separate single-mode actions on the tensor are equal. The centroid of $R(M)$ consists just of common scalars. Indeed, equate the first and second actions at the $f_{i,b}$ slice. The equation forces both $g_{i,b}$ and $e_i$ to be eigenvectors with the same eigenvalue $\lambda_i$. Now compare the second and third actions on the core first-mode rows in the $i$th second-mode coordinate. Since $c_i\ne0$ this gives $C f_0=\lambda_i f_0$ for the third endomorphism $C$. All $\lambda_i$ coincide. The second endomorphism is therefore scalar, and conciseness forces the others to be that scalar. In a direct sum of concise tensors the centroid is the product of the centroids. Comparing the first and second actions on a summand with only the first summand index changed kills every off-diagonal first-mode map by conciseness. Applying the same argument to the other two modes kills their off-diagonal maps. The primitive idempotents of the product centroid then recover the summands intrinsically. The three distinct ordered formats match the same rotations on the two sides, so isomorphism of the direct sums would imply the original isomorphism. This also records the exact cancellation mechanism used here.

### Easy pair with disjoint SL closures

Let $D_d=\sum_i e_i\otimes e_i\otimes e_i$. Let $S_d$ be the direct sum of $d/3$ copies of the concise $3\times3\times3$ tensor with slices $I_3,E_{12},E_{23}$. On each small block use first-mode weights $(2,0,-2)$, their negatives in the second mode, and third-mode weights $(2,-1,-1)$. The supported terms have positive weight and all sums of weights are zero. Thus $S_d$ belongs to the SL null cone.

The diagonal tensor lies outside the SL null cone. The slice-determinant map $T\mapsto \det(\sum_i z_iT_i)$ is equivariant for the third SL factor and invariant under the first two. For $D_d$ the determinant is a product of $d$ independent linear forms. In a basis diagonalizing any third-mode one-parameter subgroup, let $w_1,\ldots,w_d$ be the weights on the polynomial variables, with sum zero. A nonzero permutation term in the coefficient matrix of the forms gives a selection of one supported variable from each form using each variable once. The sum of the minimum weights of the forms is therefore at most $\sum_i w_i=0$. The lowest weight part of their product is the product of the lowest weight parts, nonzero because the polynomial ring is a domain. No one-parameter subgroup takes the determinant to zero. Hilbert–Mumford applies over the algebraically closed field in arbitrary characteristic. The orbit closure of $D_d$ therefore excludes zero. Its orbit closure cannot meet that of $S_d$, since the null cone is closed and invariant and any point in it has zero in its own orbit closure. [Hilbert–Mumford and instability](https://arxiv.org/abs/1807.02890)

### A constant-degree PC contradiction

Take a fixed linear combination of the target slices of $S_d$ which is $I_d$, using all block identity slices. Denote its source diagonal slice before the first two mode changes by $D_0$. For arbitrary other slices write $S_i=X D_iY^{\mathsf T}$, where $D_i$ is diagonal with entries from the unknown third transporter. All these equations have degree at most three. From $X D_0Y^{\mathsf T}=I$ and the two-sided inverse equations, derive $Y^{\mathsf T}X D_0=I$ by multiplying on the left by $Y^{\mathsf T}$ and on the right by its inverse. More explicitly, multiply the original equation by $(Y^{\mathsf T})^{-1}$ on the right and then by $Y^{\mathsf T}$ on the left. The inverse variables occur in bounded-degree products and all summations have polynomially many terms.

Write $H=Y^{\mathsf T}X$. For $r\ne s$, use $H_{rs}(D_0)_{ss}=0$ and $H_{ss}(D_0)_{ss}=1$. Multiplying the first by $H_{ss}$ and the second by $H_{rs}$ gives $H_{rs}=0$ by subtraction. Hence $D_iHD_j=D_jHD_i$ follows entrywise by bounded-degree operations. Substitute the original slice equations to derive
$$
S_iS_j-S_jS_i=X(D_iHD_j-D_jHD_i)Y^{\mathsf T}=0.
$$
This substitution uses linear combinations and multiplication by monomials of bounded degree. Choose the two target slices $E_{12}$ and $E_{23}$ on the same block. The $(1,3)$ entry of their commutator is $1$, yielding the refutation. All constructions use fixed constants or entries from the graph reductions and have polynomial output size.
