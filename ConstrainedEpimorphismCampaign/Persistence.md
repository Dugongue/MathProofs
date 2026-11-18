# Exact counting of persistence-module epimorphisms over prescribed maps

**Theorem.** Let $A,B,C$ be finite ordinary persistence modules over an explicitly represented finite field $F$. Each module is a diagram on the same chain $1\to2\to\cdots\to n$, given by its vertex spaces and linear transition matrices. Given natural maps $\rho:A\to C$ and $\psi:B\to C$, a deterministic polynomial-bit-time algorithm exactly counts the componentwise surjective natural maps
$$
 f:A\longrightarrow B,\qquad \psi f=\rho.
$$
It produces one such map when the count is positive and enumerates all such maps exactly once with polynomial delay. An exact uniform sampler runs in expected polynomial time. The same holds for several simultaneous equations $\psi^{(k)} f=\rho^{(k)}$.

The input size is the explicit coordinate size, including the sum of the vertex dimensions, the written matrix entries, and the field description. For example, a binary prime and an explicit irreducible polynomial for a finite extension suffice. If isolated dimensions appear only as binary headers, they can encode exponentially many coordinates and output bits. The complexity bound here concerns fully sized spaces and explicit output. The theorem is informal and applies to arbitrary ordinary persistence diagrams. No interval basis is part of the input.

For several maps, combine them into one pair with target $\bigoplus_k C^{(k)}$. One can check the naturality conditions by matrix multiplication. A surjective $f$ requires $\operatorname{im}\rho=\operatorname{im}\psi$ as subdiagrams. Check equality at each vertex by elimination and return count zero if the images differ. Otherwise restrict the codomain to the common image and express the two maps in computed bases. This makes them surjective without changing the solutions. The argument below uses only the equations, so it can also run on the unreduced maps.

## 1. Compute an interval basis from the input

Write $I[b,d]$ for the interval with one copy of $F$ at each vertex from $b$ through $d$, identity along its internal arrows, and zero elsewhere. Write $A_{b,d}:A_b\to A_d$ for the composite along the chain, with $A_{b,b}=1$.

In the current residual source diagram, choose its first nonzero vertex $b$ and the largest $d$ for which $A_{b,d}\neq0$. Choose $x\in A_b$ with $x_d=A_{b,d}x\neq0$. Its images $x_i$ for $b\leq i\leq d$ are all nonzero and form a copy of $I[b,d]$, since the next composite is zero when $d<n$. Choose a functional $\ell_d:A_d\to F$ taking value one on $x_d$. For $b\leq i\leq d$, put $\ell_i=\ell_d A_{i,d}$, and take the zero map at all other vertices. These functionals define a natural retraction onto $I[b,d]$. Naturality at the arrow entering $b$ follows because the residual space immediately before $b$ is zero. At the arrow leaving $d$ both sides of the required equation are zero.

The componentwise kernel of the retraction is a residual subdiagram, and the source is the direct sum of this kernel diagram and the interval. Repeat on the residual source. Each iteration decreases the total dimension by at least one and uses only matrix multiplication and Gaussian elimination. Recording the chosen vectors and kernel bases computes interval coordinates and their changes of basis from the original input. One can evaluate $\rho$ on each interval generator in the given coordinates. Interval decomposition itself is classical. [Zomorodian–Carlsson, Computing Persistent Homology](https://geometry.stanford.edu/paper/zc-cph-04/zc-cph-04.pdf)

## 2. Independent affine choices for source intervals

A natural map from an interval $I[b,d]$ with generator $a\in A_b$ into $B$ is determined by $x=f_b(a)\in B_b$. Its subsequent images are $B_{b,i}x$. The exact conditions for this map to lie over $\rho$ are
$$
 \psi_b x=\rho_b(a),\qquad B_{b,d+1}x=0,
$$
where the second map is zero if $d=n$. The second condition gives naturality at the end of the bar. The first implies equality with $\rho$ at all interior vertices by naturality. These equations are independent across source intervals. If one system is inconsistent, the answer is zero.

Define the head at a vertex by
$$
 H_b(B)=B_b/\operatorname{im}(B_{b-1,b}),
$$
with incoming image zero at the first vertex, and let $\pi_b:B_b\to H_b(B)$ be the projection. The head of an interval is its one generator at its birth vertex. Thus the head columns at $b$ are exactly the $\pi_b(x)$ from the intervals born there.

For an interval of length $t=d-b+1$, the permitted head column ranges over the affine space
$$
 v+U_t,\qquad U_t=\pi_b\bigl(\ker\psi_b\cap\ker B_{b,b+t}\bigr),
$$
where $v=\pi_b(x_0)$ for a particular solution $x_0$. All vectors in this coset occur. For fixed $b$, the subspaces $U_t$ increase with $t$ because later composites factor through earlier ones. Each permitted column has exactly
$$
 |F|^{\,\dim(\ker\psi_b\cap\ker B_{b,b+t}\cap\ker\pi_b)}
$$
original preimages. Elimination computes these spaces, offsets, and exponents.

A natural map is componentwise onto precisely when its head map is onto at each vertex. One direction follows by quotienting. For the other, use induction in $b$. At the first vertex the head is the whole space. If $f_{b-1}$ is onto, naturality ensures the image of $f_b$ contains the whole incoming image in $B_b$, and surjectivity onto the head supplies the remaining vectors. The constraints at distinct birth vertices concern disjoint sets of source intervals.

This specializes the truncated-projective module algorithm in [Groups.md](Groups.md). For the line path algebra $R$, its radical $J$ is generated by the arrows and $I[b,d]$ is $Re_b/J^{d-b+1}Re_b$, where $e_b$ is the length-zero path at $b$.


## 3. Count heads by one rank per vertex

At one vertex fix $H=H_b(B)$. Order the intervals by nondecreasing length. Write their affine sets as $v_j+U_j$, where $U_1\subseteq\cdots\subseteq U_s$. Suppose the columns chosen before the $j$-th span a subspace $W$ of rank $r$. After projection to $H/U_j$, this span is exactly the span of the projected offsets $v_i$ with $i<j$, since $U_i\subseteq U_j$. Denote its fixed dimension by $d_j$.

The number of extensions preserving rank $r$ is the size of $(v_j+U_j)\cap W$. It is zero when the projected $v_j$ is outside the projected prior span. Otherwise it is $|F|^{r-d_j}$, because the intersection is a coset of $W\cap U_j$. All $|F|^{\dim U_j}$ choices either preserve rank or raise it by one. Subtract the preserving count to get the raising count.

For each $j$, compute the fixed projected-span test by elimination. Start at rank zero and accumulate integer counts over the ranks $0,\ldots,\dim H$ using the two transitions. The final count for rank $\dim H$ counts exactly the spanning head choices for that vertex. Multiply over birth vertices and by the uniform original-preimage factors in Section 2, one factor for each interval. This is the exact count. A vertex of zero head dimension needs rank zero, and a positive head dimension with no source columns has count zero.

For witnesses, also compute suffix counts indexed by the current rank. These counts are valid for every prefix with that rank by the fixed projection argument. At each column choose a transition that has a positive suffix count. If it preserves rank, solve the intersection $(v_j+U_j)\cap W$. If it raises rank and $v_j\notin W$, use $v_j$. Otherwise add a basis vector of $U_j$ outside $W$. The positive count guarantees such a choice. When all head columns are selected, lift each through its affine equations, propagate the images along its interval, and convert back to the original bases. This constructs the required vertex matrices without enumerating field elements.

For enumeration, follow all branches whose suffix count is positive. Enumerate the rank-preserving choices in their affine coordinates. For rank-raising choices with nonempty rank-preserving intersection, take an origin in that intersection and split $U_j$ into its direction subspace and a complement. The raising choices are exactly the vectors with nonzero complement coordinate. If the intersection is empty, every vector in the affine space raises rank. These forms allow each next viable choice to be generated by a field-coordinate counter. Once the heads are fixed, enumerate the affine lift fibers in the same way. Each search path contributes a different map because its interval-generator images determine it uniquely. The search depth is polynomial, every visited node extends to an output, and the next viable child or the end of its child list can be found in polynomial time. This gives polynomial delay.

For exactly uniform sampling, first choose a rank transition with weight equal to its number of choices times its suffix count. An exact integer random draw uses fair bits with rejection from the next power of two. Conditional on the transition, choose the column uniformly from its permitted affine intersection or affine complement. In a nonempty raising class, any excluded intersection is a proper affine subspace, so rejection from the whole affine coset has acceptance probability at least $1-1/|F|$. Alternatively sample the complement coordinate uniformly among its nonzero vectors. When all heads are fixed, sample independently and uniformly in each interval lift fiber. The transition probabilities telescope to the reciprocal of the number of successful head assignments. Since every such assignment has the same number of lifts, the resulting distribution is uniform on the original maps. This takes expected polynomial time.

Let $D_A=\sum_b\dim A_b$ and $D_B=\sum_b\dim B_b$. The total number of vector-space map families is at most $|F|^{D_A D_B}$, bounding the bit length of the output count. Intermediate products and suffix counts are bounded by the same expression, because each partial assignment has at most one choice of a vector of $B_b$ per source generator at $b$. The output matrices have at most $D_A D_B$ field entries. Parsing, interval splitting, all affine calculations and rank recurrences involve polynomially many field and integer operations. Field arithmetic is polynomial in the explicit field representation. This establishes all the stated raw-input bounds.

## 4. How this differs from type-based counts

Fixed quotient maps carry information beyond barcodes and the kernels' abstract types. For a two-vertex example take $A=B=(F^2\xrightarrow{[1\ 0]}F)$ and $C=(F^2\to 0)$. Let $\psi_1$ be the identity and $\psi_2=0$. For $\rho=\psi$, the identity $f$ is a valid lift. For $\rho_1$ the coordinate swap and $\rho_2=0$, no natural lift exists. The prescribed equation forces $f_1$ to swap the coordinates, which fails to preserve the kernel of the transition. The two instances have identical module barcodes and the very same kernel diagrams for $\rho$. Ordinary Hall counts aggregate by isomorphism types. Induced barcode matchings extract information from a given morphism, whereas the problem here fixes two morphisms and asks for every compatible epimorphism between their sources. [Ringel, Hall polynomials for representation-finite hereditary algebras](https://noah.nrw/ubbihs/download/pdf/5112430) · [Bauer–Lesnick, Induced Matchings and the Algebraic Stability of Persistence Barcodes](https://arxiv.org/abs/1311.3681)

The nested homogeneous rank count has a classical precedent in finite-field matrices supported on Ferrers boards. The algorithm above also uses the specified affine offsets outside each variation subspace. A focused search found these precedents and no direct reference for the marked algorithm. The transfer uses elementary operations, and no publication priority or resolution of a published open problem is claimed. [Haglund, $q$-Rook polynomials and matrices over finite fields](https://arxiv.org/abs/math/9706219)
