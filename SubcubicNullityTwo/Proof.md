# Subcubic homomorphisms distinguish graphs of adjacency nullity two

Informal computer-assisted proof of [Takanori Maehara's Problem 2](https://arxiv.org/html/2610.09042v2#S5). Let $G$ be a finite simple graph whose adjacency matrix has nullity at most two. If another finite simple graph $H$ has the same homomorphism counts from all simple graphs of maximum degree at most three, then $G$ and $H$ are isomorphic. Maehara's nullity-three example shows the cutoff is sharp. The finite calculation below involves graphs on at most eight vertices, regardless of the original graph sizes.

## Moment data from the subcubic counts

By Maehara's Lemma 13, the vertex counts agree and there is a common realization of the two adjacency images in a real Euclidean space $E$. The common invertible symmetric edge operator is $C$. Write $u_1,\ldots,u_n$ and $v_1,\ldots,v_n$ for the projected coordinate bases of the two graphs. We have
$$
(A_G)_{ij}=u_i^{\mathsf T}Cu_j,\qquad
(A_H)_{ij}=v_i^{\mathsf T}Cv_j,\qquad
\sum_i u_i^{\otimes j}=\sum_i v_i^{\otimes j}\quad(1\le j\le3).
$$
The moment of degree two is the identity on $E$, and the moment of degree one follows from contraction of the cubic with that identity, or directly from Lemma 13. Both lists span $E$. The space of linear relations among either list has dimension $k=n-\dim E\le2$. [Maehara, Lemma 13](https://arxiv.org/html/2610.09042v2)

Cancel equal points between the two lists with multiplicity. Each canceled pair is already matched, with equal frame vectors. Call these matched vertices anchors. Their mutual edges agree automatically. Subtracting the terms for the anchors leaves equal moments through degree three on the remaining lists, including degree zero.

## Splitting a signed cubic identity into small lists

Lift each remaining point $u$ or $v$ to $(u,1)$ or $(v,1)$ in $E\oplus\mathbb R$. Equality of moments through degree three is equality of the sums of the tensor cubes of these lifts. Combine repetitions within each side and subtract the two sums. This gives a linear relation among the cubes of distinct lifted points, with every coefficient nonzero.

Split the cubes repeatedly into groups whose spans are in direct sum, until each group is connected in the sense of Lovitz and Petrov. The signed sum vanishes within every group. Since every coefficient is nonzero and every cube is nonzero, no group can be a singleton. Recover the moments of orders zero through three by expanding the cube according to its factors from $E$ and the final coordinate. Within each group the moments thus match, and degree zero gives a common number $w$ of remaining vertices counted with multiplicity on each side.

Consider one group with $m$ distinct points in the union and $r$ the dimension of the span of their lifted vectors. By [Lovitz and Petrov, Theorem 4](https://arxiv.org/html/2103.15633v2), connectivity implies that the span of the cubes has dimension at least $3(r-1)+1=3r-2$. The relation forces its dimension to be at most $m-1$. In particular $2w\ge m\ge3r-1$.

Let $k'$ be the dimension of the space of linear relations among the $w$ original, unlifted points on the $G$ side of the group, still counting multiplicity. Then $r\ge w-k'$, and
$$
w\le 3k'+1.
$$
If $k'=0$, the group has $w\le1$, and equality of the first moments would contradict the cancellation of all common points. Thus every group has $k'\ge1$. The relation spaces of the groups are subspaces of the original $k$-dimensional relation space and have disjoint vertex supports, so the sum of their dimensions is at most $k$. We obtain either one group of length at most seven, or two groups each of length at most four. If there are no groups, the anchored vertices already give an isomorphism.

## The edges to already matched vertices

In this section work within one group of length at most seven. Its moments of orders zero through three agree separately.

Send a remaining point $x$ to the vector of its adjacencies to all anchored vertices, computed by the linear forms $x\mapsto x^{\mathsf T}Ca$ for the common anchor vectors $a$. On both sides its pattern lies in a Boolean cube. The lists of patterns have equal moments through degree three by linearity. They have identical pattern multiplicities. Indeed, a nonzero signed function on a Boolean cube with vanishing monomial moments through degree $t$ must have support at least $2^{t+1}$. For $t=0$ this follows from zero sum. For $t>0$, choose a coordinate separating two support points. The two nonzero slices have vanishing moments through degree $t-1$, by multiplying by the corresponding linear slice indicators. Induction then proves the claim. Here $t=3$ and the combined size is at most fourteen.

The set $S$ of distinct patterns has cardinality at most seven. Every pattern indicator on $S$ is represented by a polynomial of degree at most two. To see this, select monomials greedily in a degree-compatible monomial order, retaining one when its evaluation on $S$ is linearly independent of preceding evaluations. If a monomial evaluation is dependent, then every multiple is dependent on earlier evaluations by multiplying the relation and using the monomial order. Thus the retained monomials form a downset. They are squarefree, because reducing $x_i^2$ to $x_i$ preserves evaluation and lowers degree. They span all functions on $S$ since a product of Boolean literals can isolate any point. If a retained monomial had degree at least three, its divisors would already give at least eight independent evaluations, a contradiction.

For a pattern class of size one, multiply its degree-two indicator by linear forms on the vectors $x$. These are tests of degree at most three on the group, so the unique frame vector of that class agrees on both sides. This contradicts the initial cancellation of all equal frame vectors, so singleton classes cannot occur. There are consequently at most three distinct patterns. Any set of at most three distinct Boolean vectors is affinely independent: a line through two distinct Boolean vectors intersects the cube in just those two Boolean points, as seen in a coordinate where they differ. So every indicator of the current pattern classes can be given by an affine linear function. Multiplying it by arbitrary tests of degree at most two now recovers the first and second moments of each class. A class of size two is determined as a multiset of frame vectors by those moments. For vectors $x,y$, their sum and their second moment determine $(x-y)(x-y)^{\mathsf T}$, so they determine the difference up to sign. This also contradicts the initial cancellation, so classes of size two cannot occur.

Thus every pattern class has size at least three. A single group of length at most seven has either one pattern class of size at most seven or two classes of sizes $3+3$ or $3+4$. With two groups of length at most four each, each group has only one pattern class, and the sizes are $3+3$, $3+4$, or $4+4$. Any isomorphism of the residual graphs that respects their groups and pattern classes preserves every edge to the anchors and extends to an isomorphism of the original graphs.

## The finite check

For one remaining group, uncolored subcubic homomorphism counts in the induced graph on the remaining vertices are determined by $C$ and that group's restricted frame moments. In the case of two pattern classes in one group, one can additionally require specified probe vertices of degree at most two to map into a specified pattern class. The affine selector for that class times a degree-$j$ vertex moment uses only moments through degree $j+1\le3$. Thus every such partially colored count agrees. A probe vertex with no selector can map anywhere in the group. With two original groups, the restricted moments are already separately available for both groups. Partial or full color requirements on the probe vertices of any degree up to three are therefore allowed. The same $C$ connects both groups.

It suffices to verify the following finite statements by counting homomorphisms exactly.

- Simple uncolored graphs on at most seven vertices are separated by connected simple subcubic probes on at most seven vertices.
- For simple graphs colored in two classes of sizes $3+3$ or $3+4$, the same probes separate the color-preserving isomorphism classes if each probe vertex of degree at most two may also have a specified color.
- The two-color splits $3+3$, $3+4$, and $4+4$ are likewise separated when colors can be specified at any probe vertex, including those of degree three.

The [accompanying exhaustive verifier](CheckSmallSubcubic.cpp) partitions the target graphs into orbits under permutations within the color classes, enumerates the probe graphs, and refines unresolved classes by exact homomorphism counts. Counts use integer arithmetic with enough bits for the maximum number of assignments. Distinct representatives end in distinct classes in each case. The uncolored checks have 1, 2, 4, 11, 34, 156, and 1,044 representatives at orders one through seven. The colored checks have 1,408, 20,364, and 580,656 representatives respectively. One can independently obtain each orbit total by averaging $2^{c(\pi)}$ over the permitted permutations $\pi$, where $c(\pi)$ counts their cycles on unordered vertex pairs. The verifier uses all connected simple subcubic probes on up to seven vertices, stopping once it has separated the complete list.

Compile and run from the proof directory.

    g++ -O3 -std=c++17 CheckSmallSubcubic.cpp -o check-small-subcubic
    ./check-small-subcubic

This yields an isomorphism of the remaining graphs respecting the classes. Joining it with the anchor matching proves the theorem.

The proof combines Maehara's adjacency-image characterization with the Lovitz–Petrov dimension bound. The small list sizes come from charging every ambiguous cube component to a disjoint subspace of the adjacency kernel. The finite check only handles those residual list sizes.\n
