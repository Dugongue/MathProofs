# Quantum nonvanishing and logarithmic degree for graph homomorphisms

Informal proof, November 14, 2026. The proof uses the gadget and contraction conventions in Cai and Young, [*Vanishing Signatures, Orbit Closure, and the Converse of the Holant Theorem*](https://arxiv.org/html/2509.10991v1#S6.SS1). Their arXiv version asks, after Corollary 6.3, for a characterization of the class of graphs whose equality and adjacency signature pair is quantum-nonvanishing. The first theorem answers that question and extends it to other signature families. The ITCS paper treats bounded-degree graph homomorphisms in [Section 5.1](https://drops.dagstuhl.de/storage/00lipics/lipics-vol362-itcs2026/html/LIPIcs.ITCS.2026.32/LIPIcs.ITCS.2026.32.html).

## A support criterion for quantum nonvanishing

Let $L$ and $R$ be finite conjugation-closed families of complex signatures on a domain of size $q\ge 1$. These are the left and right signatures in a bipartite Holant problem. Suppose the left family contains binary equality $=_{2}$, the identity matrix considered as a two-left-leg tensor. For a right signature $F$ and a position $j$, write $M_{F,j}$ for its mode flattening with position $j$ indexing the rows. Define

$$
S=\sum_{F\in R}\sum_{j=1}^{\operatorname{arity}(F)}M_{F,j}M_{F,j}^*.
$$

Then $L\mid R$ is quantum-nonvanishing if and only if $S$ is invertible. Equivalently, the column spaces of the right-signature flattenings span $\mathbb C^q$. This is a polynomial-time test given explicit Gaussian rational signature tables. In particular, for every $d\ge 2$, the graph signature family $\mathrm{EQ}_{\le d}\mid\{A_G\}$ is quantum-nonvanishing exactly when the adjacency matrix $A_G$ is nonsingular.

**Construction of the test matrix.** Each summand $M_{F,j}M_{F,j}^*$ is a two-right-leg gadget. Use a copy of $F$ and of $\overline F$, join their matching positions other than $j$ through copies of the left $=_{2}$, and leave both positions $j$ open. Sum these gadgets. As a matrix, $S$ is Hermitian positive semidefinite. Conjugation closure makes it real, hence symmetric. For every vector $x$, the identity

$$
x^*Sx=\sum_{F,j}\lVert M_{F,j}^*x\rVert^2
$$

gives both the kernel and the stated column-space condition. Forming the matrices and testing the rank use polynomial bit time by exact linear algebra.

**If the test matrix is invertible.** This is also an immediate application of Cai and Young's Lemma 6.1. Explicitly, take any nonzero quantum gadget signature $K$. Attach the right binary gadget $S$ to each left leg to turn all the open legs to the right. The resulting signature $K'$ is nonzero by invertibility. The complex conjugate gadget for $K'$ is available by conjugation closure. Attach left binary equality to each leg of this conjugate to obtain a fully left signature with entries $\overline{K'}$. Connecting this signature to $K'$ gives $\sum |K'|^2>0$ and hence a closed quantum grid containing the original $K$. Expansion exhibits a nonzero closing grid as required by Definition 4.2. If $K$ is a scalar, its nonzero value is already such a closure.

**If the test matrix is singular.** Attach left binary equality to one leg of $S$ and keep one open leg of each orientation. The resulting mixed matrix gadget has matrix $S$. Its chains give the positive powers of $S$, and a bare wire is the mixed identity (Definition 2.5 and the discussion following it). Write the characteristic polynomial as $t^k h(t)$ where $h(0)\ne 0$. Since $S$ is diagonalizable, the polynomial $p(t)=h(t)/h(0)$ gives $P=p(S)$, the orthogonal projection onto $\ker S$. So $P\ne0$ is available as a mixed quantum gadget. Attach its right leg to one of the legs of left binary equality, leaving a two-left-leg signature $K$ with matrix $P$.

In every closed grid over $L\mid R$ with an extra left vertex carrying $K$, one of its legs meets an original right signature $F$, at some position $j$. A chain of bare wires can be suppressed. If both legs meet the same vertex, contract the specified leg first. The single-leg contraction replaces the flattening by $P M_{F,j}=0$, since $\ker S$ is orthogonal to its column space and $P=P^\top$. Thus the whole grid evaluates to zero. By the base-grid criterion in Definition 4.2, $K$ is quantum-vanishing. This constructs a nonzero witness of type $(2,0)$.

For a graph, the two flattenings of the sole right signature are both $A_G$ because it is real symmetric. Thus $S=2A_G^2$, which is invertible exactly when $A_G$ is. This proves both directions of the characterization requested after Corollary 6.3. Collected values from the gadget spaces may include loops and parallel edges, as in Cai and Young's conventions. The next theorem also applies when probes are restricted to simple graphs.

## A rank-size characterization for bounded-degree probes

Takanori Maehara previously proved the degree-three case, using an isometry between adjacency images that intertwines the adjacency operator and preserves the restricted trilinear form. Contracting that form with the identity on the image recovers the linear form as explained in his proof. The result below treats every degree bound $d\ge 2$. [Maehara, *Distinguishing graphs with simple spectrum by homomorphism counts*, Lemma 13](https://arxiv.org/html/2610.09042v1#S3)

Let $F,G$ be simple graphs on the same number $n$ of vertices, and let $d\ge 2$. For either graph $H$ let $E_H=\operatorname{im} A_H\subseteq\mathbb R^n$, let $P_H$ be the orthogonal projection onto $E_H$, and form the following tuple on that Euclidean space:

$$
C_H=A_H|_{E_H},\qquad T_{H,j}=\sum_{i=1}^n(P_He_i)^{\otimes j}\quad(1\le j\le d).
$$

Then $F,G$ have equal homomorphism counts for all maximum-degree-$d$ simple graphs if and only if their tuples are simultaneously equivalent under a real orthogonal isomorphism $E_F\to E_G$. If the graphs have different vertex counts, the one-vertex probe distinguishes them. Regard the zero-dimensional case as the tuple of the empty graph on the given number of vertices.

**Passing between simple and multigraph probes.** Let $\Lambda$ be the union of the nonzero eigenvalues of $A_F,A_G$, and choose a real polynomial $f$ with $f(\lambda)=\lambda^{-2}$ for $\lambda\in\Lambda$. Then $A_H=A_H^3f(A_H)$ for both graphs. Interpret each term $cA_H^\ell$, $\ell\ge 3$, as replacing a source edge with a length-$\ell$ path with fresh interior vertices. The internal variables sum to the entry of $A_H^\ell$ between the old endpoints. For a loop use the same construction returning to its old vertex. Replacing all edges by such paths turns any multigraph probe into a linear combination of simple probes. Degrees at old vertices are unchanged, counting a loop twice, and each new vertex has degree two. Coefficients are the same for both graphs, so simple-probe equality implies multigraph-probe equality. The reverse implication is immediate.

**Removing the invisible coordinates.** Write each homomorphism count as the contraction of the vertex equality tensors with the edge tensors $A_H$. Since $P_H A_H P_H=A_H$, projecting each leg onto $E_H$ leaves every such contraction unchanged. The vertex signatures become $T_{H,j}$ and the edge signature becomes $C_H$. Isolated vertices contribute $n$ each. Also $T_{H,2}$ is the identity in any orthonormal basis of $E_H$, because $\sum_i(P_He_i)(P_He_i)^\top=P_H$.

Assume the counts agree. For each $k\ge 3$, the simple cycle of length $k$ gives $\operatorname{tr}(A_F^k)=\operatorname{tr}(A_G^k)$. For the distinct nonzero eigenvalues $\lambda$ in $\Lambda$, a Vandermonde system on the powers $k=3,\dots,2+|\Lambda|$ shows that their multiplicities agree. Thus $E_F,E_G$ have the same dimension. If it is zero, both adjacency matrices vanish and there is nothing left to prove.

Choose one polynomial $q(t)$ with $q(0)=0$ and $q(\lambda)=1$ for all $\lambda\in\Lambda$. On either effective space, $q(C_H)=I_{E_H}$ is a right binary equality gadget. Indeed, every positive power $C_H^\ell$ is a chain of $\ell$ right edge tensors joined through the left $T_{H,2}$. Left and right binary equality are now both available, with the same gadget coefficients on the two inputs. Using them to flip the orientation of legs realizes every pairing of the legs of the real tensors $(C_H,T_{H,1},\dots,T_{H,d})$ as a linear combination of the original bipartite contractions. These values therefore agree. Apply Cai and Young's real Holant converse, Theorem 2.2, to these corresponding real signatures. It gives a real orthogonal isomorphism carrying the tuple for one graph to the tuple for the other. The converse follows by invariance of contractions under orthogonal change of basis. [Real Holant converse and the correspondence convention](https://arxiv.org/html/2509.10991v1#S2.SS2)

## The logarithmic degree bound is attained infinitely often

For every integer $n\ge 1$, two simple $n$-vertex graphs are isomorphic if all homomorphism counts match for probes of maximum degree at most

$$
d(n)=\max\bigl(4,\lfloor\log_2(2n)\rfloor\bigr).
$$

For every integer $m\ge 4$ and $n=2^{m-1}+m$, the universal threshold is exactly $m$. Here the threshold means the minimum $d$ for which equality against all probes of maximum degree at most $d$ forces isomorphism on all simple $n$-vertex targets. No bound on the number of vertices of a probe is imposed.

**Upper bound.** By the preceding characterization, transport the two tuples onto one real Euclidean space $E$. There is a common invertible edge operator $C$ and two lists $u_i,v_i$ spanning $E$, obtained from the two projected coordinate bases. They satisfy

$$
\sum_i u_i^{\otimes j}=\sum_i v_i^{\otimes j}\quad(1\le j\le d(n)),\qquad
u_i^\top C u_k= (A_F)_{ik},\quad v_i^\top C v_k=(A_G)_{ik}.
$$

If $E$ has dimension zero, both graphs are edgeless. Otherwise for each $v_k$ consider the real linear functional $b(x)=v_k^\top Cx$. The sum of the polynomial $b(x)^2(b(x)-1)^2$ over the $v_i$ is zero because the entries of $A_G$ are binary. Equality of moments of degrees two through four gives zero for the same sum over $u_i$. Every summand is nonnegative, so all cross entries $v_k^\top C u_i$ are binary. Define a linear map into $\mathbb R^n$ by

$$
\beta(x)=(u_1^\top Cx,\ldots,u_n^\top Cx).
$$

It is injective by the spanning property and invertibility of $C$. It maps both lists into $\{0,1\}^n$. The difference $\mu$ of their counting measures on the cube has support of size at most $2n$ and vanishing moments of every monomial of degree at most $d(n)$. For degree zero this follows from equality of the lengths of the lists. For positive degrees, a moment in the cube coordinates pulls back along $\beta$ to a homogeneous polynomial of the same degree, and thus agrees by the tensor-moment identities.

A nonzero real-valued function on a Boolean cube whose monomial moments through degree $d$ vanish has support of size at least $2^{d+1}$. To see this, for $d=0$ it has at least two nonzero values because its sum is zero. If $d>0$, select a coordinate on which two support points differ. On each slice, monomial moments through degree $d-1$ vanish by multiplying a test monomial by the indicator $x_k$ or $1-x_k$ of that slice. Both slices are nonzero and induction gives support size at least $2^d$ on each. As $2^{d(n)+1}>2n$, this proves $\mu=0$. The injectivity of $\beta$ gives equality of the point lists as multisets. Match the lists by a permutation and use the common edge operator $C$ to see that this permutation is a graph isomorphism.

**Matching lower examples.** For $m\ge 4$, let $H_0,H_1$ be bipartite incidence graphs with one side $[m]$, the other side respectively the even and the odd subsets of $[m]$, and incidence given by containment of a coordinate in a subset. Both have $2^{m-1}+m$ vertices. The empty subset in $H_0$ is isolated, while $H_1$ has no isolated vertex. Thus they are nonisomorphic.

For a connected bipartite probe with at least one edge, fix one of the two ways to send its color classes to the two sides of a target. First assign all the vertices on the coordinate side arbitrary values in $[m]$. Each vertex on the subset side must contain the set of distinct coordinates assigned to its neighbors. If the probe has maximum degree below $m$, this required set has size $s<m$. There are exactly $2^{m-s-1}$ even supersets and exactly that many odd supersets, by toggling any one unrestricted coordinate. Choices for the subset vertices are independent. Summing over coordinate assignments and over the two orientations gives equal counts. A nonbipartite connected probe has zero homomorphisms to either target, and an isolated probe vertex has the same count. Multiplication over connected components proves equality on all probes of maximum degree at most $m-1$. Since $\lfloor\log_2(2(2^{m-1}+m))\rfloor=m$ for $m\ge4$, the upper bound gives equality of the threshold with $m$.

Roberson previously proved that every fixed degree bound is insufficient for arbitrary target size, using oddomorphisms. The parity-incidence examples here provide a simple size-specific lower bound for the logarithmic upper bound. [Roberson, *Oddomorphisms and homomorphism indistinguishability over graphs of bounded degree*](https://arxiv.org/abs/2206.10321)

## Exact adjacency-nullity threshold for every degree bound at least four

For every integer $d\ge 4$, the least possible common adjacency nullity of two nonisomorphic graphs with matching homomorphism counts from every simple probe of maximum degree at most $d$ is
$$
k_{\min}(d)=2^d-d-2.
$$
In particular, every simple graph of adjacency nullity $k$ is determined by homomorphism counts from probes of maximum degree $O(\log(k+2))$, independently of its vertex count.

**Lower bound on the nullity of a counterexample.** Counts from the one-vertex probe give a common vertex count $n$. By the rank-size characterization the two adjacency images have dimension $n-k$. Use their common realization by $C,u_i,v_i$ from the preceding theorem. The same argument using the fourth-degree polynomial $b^2(b-1)^2$ makes the linear embedding $\beta$ send both frames into the Boolean cube. Write the multisets of cube points as $U,V$, with length $n$ each. They have the same moments through degree $d$. Cancel their common points with multiplicity, leaving multisets of length $w$ each with disjoint support. If $w=0$, the graphs are isomorphic. Assume $w>0$, let $S$ be the union of the remaining supports, and let $\mu:S\to\mathbb Z\setminus\{0\}$ be the difference of the remaining multiplicities. Then $|S|\le 2w$. The remaining points of $U$ span at least $w-k$ dimensions because the original points span $n-k$ dimensions and at most $n-w$ canceled vectors can contribute to the span.

For each $j\ge0$, let $V_j$ be the space of real functions on $S$ obtained by evaluating polynomials of degree at most $j$. Write $h(j)=\dim V_j$. In particular $h(1)\ge w-k$, as the rank of linear evaluation is the dimension of the span of $S$. The pairing
$$
\langle f,g\rangle_\mu=\sum_{x\in S}\mu(x)f(x)g(x)
$$
is nondegenerate on the function space because no weight on $S$ is zero. If $a+b\le d$, then $V_a$ and $V_b$ are orthogonal under this pairing by moment equality. Thus $h(a)+h(b)\le |S|$. The same moment equality makes the nonzero functional $f\mapsto\sum_{x\in S}\mu(x)f(x)$ vanish on $V_d$, so $h(d)<|S|$.

Take a degree-compatible monomial order in the ambient cube coordinates. The standard monomials of the ideal of polynomials that vanish on $S$ are the monomials outside its leading-monomial ideal. They form a basis for the coordinate ring, and the number of these monomials of degree at most $j$ equals $h(j)$. One way to see both facts is to process monomials in order and keep one exactly when its evaluation is independent of all earlier evaluations. A dependency on earlier monomials is precisely a vanishing polynomial with that leading monomial. All functions on $S$ are polynomial evaluations, since products of the literals $x_i$ and $1-x_i$ realize the point indicators. Thus $h(d)<|S|$ guarantees a standard monomial of degree greater than $d$. Standard monomials are closed under taking divisors, because the leading monomials of vanishing polynomials are closed under multiplication by monomials. They are squarefree, because $x_i^2-x_i$ vanishes on $S$ for every $i$. Consequently there is a standard monomial on $d+1$ distinct variables, and all its squarefree divisors are standard. For $j\ge1$ this gives
$$
h(j)\ \ge\ h(1)+\sum_{i=2}^j\binom{d+1}{i}.
$$
Use $a=\lfloor d/2\rfloor$ and $b=\lceil d/2\rceil$. By binomial symmetry, the sums up to $a$ and $b$ starting at zero add to $2^{d+1}$. Their sums starting at two therefore add to $2^{d+1}-2(d+2)$. Combining the dimension inequalities gives
$$
2w\ge h(a)+h(b)\ge 2(w-k)+2^{d+1}-2(d+2),
$$
so $k\ge 2^d-d-2$.

**Matching examples at the stated nullity.** Start with the even and odd incidence graphs on $m=d+1$ coordinates from the previous construction. Add one extra coordinate vertex to each, adjacent to every subset vertex. In a bipartite probe orientation, any neighbor mapped to this extra coordinate creates no constraint on the subset vertex. With maximum degree at most $d=m-1$, each subset vertex is still required to contain fewer than $m$ ordinary coordinates. The same parity-toggling argument gives equality of all the required homomorphism counts. The targets are nonisomorphic. The $m$-leaf star distinguishes them, since the ordinary and extra coordinate degrees are equal across the pair, and the signed difference from the subset vertices is
$$
\sum_{j=0}^m(-1)^j\binom mj (j+1)^m=(-1)^m m!\ne0.
$$
Here the alternating sum is the $m$-fold finite difference of a monic polynomial of degree $m$.

On either parity class, the incidence matrix has full row rank $m+1$. Its extra row is constant $1$, and the span of this row and the $m$ membership rows is the span of the constant and the $m$ one-coordinate sign functions $(-1)^{1_{i\in S}}$. These $m+1$ functions are pairwise orthogonal on the parity class. A product of two distinct functions is the sign of a nonempty proper set of at most two coordinates, and toggling one coordinate in that set and one outside it preserves parity while negating the sign. Since these functions are all nonzero, the rank assertion follows. The adjacency matrix has the incidence matrix and its transpose as opposite off-diagonal blocks, so its rank is $2(m+1)$ and its nullity is
$$
2^{m-1}+(m+1)-2(m+1)=2^d-d-2.
$$
