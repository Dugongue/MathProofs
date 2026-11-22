# Recovering multipersistence from priced boundary matroids

Let $C_\bullet$ be a finite chain complex over a field $K$, with distinguished cell sets $E_k$ as bases for $C_k$. Each cell $i$ enters at one grade $\gamma_i\in\mathbb Z^d$, ordered coordinatewise. The boundary can have a nonzero $ij$ entry only when $\gamma_i\le\gamma_j$. Write $E_{k,s}=\{i\in E_k\colon\gamma_i\le s\}$, so the spans of these sets form the subcomplex $C_\bullet(s)$. The labels identifying the same cell across adjacent boundaries are part of the presentation.

For each boundary matrix $D_k$, augment it by the identity on the target:
$$
 A_k=[I_{E_{k-1}}\mid D_k].
$$
Its column matroid $M_k$ has ground set $E_{k-1}\sqcup E_k$, with distinguished basis $I_k=E_{k-1}$. Include the zero boundary at either end. In particular the top-degree augmented matrix has identity columns and no source columns. Let $G$ be the graph on all cells with an edge $ij$ whenever $D_{k,ij}\ne0$ for some $k$.

The input consists of the following value oracles and the marked cell sets. The matrices $D_k$ and grades are hidden. Replace each column $j$ of $A_k$ by $\mathbf t^{\gamma_j}$ times itself and each row $i$ by $\mathbf t^{-\gamma_i}$ times itself, where $\mathbf t^a=\prod_\ell t_\ell^{a_\ell}$. Denote the resulting augmented Rees matrix by $A_k(\mathbf t)$. For each parameter $\ell$, the oracle on a rational price vector $z$ returns
$$
 L_{k,\ell}(z)=\min_{B\text{ basis of }M_k}
 \big(w_{k,\ell}(B)-z(B)\big),\qquad
 w_{k,\ell}(B)=\operatorname{ord}_{t_\ell}\det A_k(\mathbf t)_B ,
 \quad z(B)=\sum_{i\in B}z_i.
 \tag{1}
$$
Here the valuation treats the other variables as units. An explicit finite uniform bound on the absolute finite weights is supplied. The presentation is promised to come from a filtered chain complex as above.

**Theorem.** Let $N=\sum_k |E_k|$, and let $\kappa$ be the number of connected components of $G$.

1. From the value oracles, reconstruct $G$ and every cell grade up to an independent common translation in $\mathbb Z^d$ on each component of $G$. These translations are precisely the possible grade ambiguity for fixed boundaries. The reconstruction uses at most
   $$
   \sum_k |E_{k-1}||E_k|+(d-1)(N-\kappa)
   \tag{2}
   $$
   oracle calls. The intermediate local grades are the canonical price vectors from valuated-matroid normalization, with each grade coordinate centered in its own matroid component.
2. Choose the coordinatewise minimum grade to be zero in each component. For that canonical representative, each multipersistence rank query at comparable grades needs at most three evaluations of priced value oracles, after polynomial preprocessing. One absolute grade anchor in every component restores the original rank invariant and all its one-parameter slice barcodes. Without anchors, the recovered persistence data are interpreted with the stated component translations.
3. Over $\mathbb F_2$, the reconstruction recovers the entire based filtered chain complex, with the same grade ambiguity. Comparing these complexes up to arbitrary cell permutations respecting homological degree and up to componentwise grade translations is equivalent to colored graph isomorphism. The problem is GI-hard already on graph chain complexes with all grades zero in an explicit matrix presentation.

If the coordinate differences of grades along all nonzero boundary entries lie in $[0,R]$, a single scalar valuation per boundary suffices for all $d$ parameters by radix encoding, with polynomial bit overhead.

## 1. What the canonical prices retain

All determinant terms of a fixed maximal minor carry the same monomial factor. Thus for a basis $B$
$$
 w_{k,\ell}(B)=\sum_{j\in B}\gamma_{j,\ell}
                      -\sum_{i\in I_k}\gamma_{i,\ell}.
 \tag{3}
$$
The support is the column matroid over $K$. Formula (3) uses the valuation of the actual determinant, including cancellations among coefficient terms. It is also the familiar grading of the boundary in the multigraded module description of persistence. [Zomorodian–Carlsson, graded persistent homology](https://doi.org/10.1007/s00454-004-1146-y) · [Carlsson–Singh–Zomorodian, multiparameter computation](https://arxiv.org/abs/0907.2423)

For each $M_k$, let $\mathcal C_k$ be its matroid components and let
$$
 U_k=\left\{z\in\mathbb Q^{E_{k-1}\sqcup E_k}:
                 \sum_{i\in H}z_i=0
                 \text{ for each }H\in\mathcal C_k\right\}.
$$
Take a point $p$ in the relative interior of the base polytope, and form the lower convex envelope of the base weights. By (3) that envelope is affine on the entire base polytope. The base differences span $U_k$, so at $p$ its only supporting slope in $U_k$ is the orthogonal projection of $\gamma_{\bullet,\ell}$ to $U_k$. Indeed if a second slope supported the affine function, the difference would pair nonpositively with every direction from $p$. Both signs of every small direction in $U_k$ are feasible, so the difference vanishes. Consequently the price and the constant term supplied by canonical normalization are
$$
 a_{k,\ell}(i)=\gamma_{i,\ell}
                 -\operatorname{mean}_{j\in H_i}\gamma_{j,\ell},
 \qquad
 b_{k,\ell}=-a_{k,\ell}(I_k).
 \tag{4}
$$
Every normalized basis weight is zero. In this application the useful information is the price vector that is subtracted. Keeping the reduced weight function alone would discard all relative times. For example, the reduced weight on a single-edge chain is zero for any time gap between a vertex and the edge, even though changing that gap can change the length of a finite bar. [Canonical price normalization](https://github.com/Dugongue/MathProofs/blob/main/ParametricConvexFour/Valuated.md) · [Dress–Wenzel, projective equivalence of valuations](https://www.sciencedirect.com/science/article/pii/000187089290028J)

## 2. Extract the prices from value queries

Let $r_k=|I_k|$ and suppose the finite weights in (1) are bounded in absolute value by $W$. For any set $B$ of size $r_k$, set the price equal to $P>2W$ on $B$ and zero elsewhere. If $B$ is a basis, it is the unique minimizer and the reported value is $w_{k,\ell}(B)-Pr_k$. If it is not a basis, every feasible choice contains at most $r_k-1$ of these elements and the value is at least $-W-P(r_k-1)>W-Pr_k$. The one value therefore tests basis membership and returns its weight in the affirmative case.

For each $i\in I_k$, $j\in E_k$, apply this test to $B=I_k-i+j$. Since the corresponding ordinary minor is $\pm D_{k,ij}$, the feasible exchanges are precisely the nonzero boundary entries. By (3) their weights are
$$
 w_{k,\ell}(I_k-i+j)=\gamma_{j,\ell}-\gamma_{i,\ell}.
 \tag{5}
$$
Locally the feasible exchanges form the fundamental exchange graph of $M_k$ at $I_k$, whose components are its matroid components. To see the component claim, each exchange lies in a fundamental circuit. Conversely every nonbasis column lies in the span of the identity columns in its graph component, and those sets of identity columns are disjoint. The local data are therefore a direct sum by those graph components.

Perform all these exchange tests at one parameter. This recovers $G$. For every other parameter use only the edges of a fixed spanning forest of $G$, since the difference on a forest path is the sum of the edge differences. The same cell label occurs in both relevant augmented matrices, so the path sums consistently glue across homological degrees. Integrating the forest differences and subtracting the coordinatewise minimum in each component recovers the canonical representative and proves (2). Formula (4) can be read from that representative since centering also removes the arbitrary translations. All that is needed from the oracles for this reconstruction is one value per tested set.

If two grade assignments for fixed boundaries give the same oracle data, (5) forces all their differences to agree along $G$, so they differ by constants per component. Conversely adding a constant grade vector to each component of $G$ restricts to adding a constant on each local matroid component. Every basis, including $I_k$, contains the same number of elements from each local component. Thus such shifts cancel in (3). This proves the stated ambiguity. Any choice of a known absolute grade on one cell per component fixes it uniquely.

For radix encoding choose an integer $B_0>\max\{1,R\}$ and use the scalar grade
$$
 \gamma_i^*=\sum_{\ell=1}^d B_0^{\ell-1}\gamma_{i,\ell}.
$$
Scalarizing the augmented matrices makes (5) the corresponding scalar difference, with digits between zero and $R$. Reading these digits recovers every coordinate difference. Even when the represented powers are large, their binary exponents have $O(d\log(R+2))$ bits plus the grade bit lengths. The oracle model need not expand them as dense polynomials. For explicit boundaries (3) gives each priced minimum by ordinary weighted matroid greedy on the columns of $A_k$, with independence tested by linear algebra. Thus the scalarization needs no polynomial arithmetic on the large exponents.

## 3. Three priced minima for a persistence rank

At any one parameter and any subset $S$ of the ground set of $M_k$, use (4) to write
$$
 L_{k,\ell}(a_{k,\ell}+{\bf1}_S)
   = b_{k,\ell}-\max_{B\text{ basis}}|B\cap S|
   = b_{k,\ell}-r_{M_k}(S).
 \tag{6}
$$
The last equality follows by extending a largest independent subset of $S$ to a basis. Thus one evaluation at a specified price gives any needed column rank, independently of which parameter is used. With the single scalarized oracle, use the component-centered scalar grades as the price vector in (6).

For $s\le t$, set $A=E_{k,s}$ and $B=E_{k+1,t}$. Then the rank of the map $H_k(C_\bullet(s))\to H_k(C_\bullet(t))$ is
$$
 \rho_k(s,t)
   = r_{M_{k+1}}(A\cup B)-r_{M_{k+1}}(B)-r_{M_k}(A).
 \tag{7}
$$
Here $A$ is counted as an identity column set in $M_{k+1}$ and as a boundary column set in $M_k$. To prove (7), the cycles in the span of $A$ have dimension $|A|-r_{M_k}(A)$. The boundaries at $t$ are the span of $D_{k+1}(B)$, so their intersection with the span of $A$ has dimension
$$
 r_{M_{k+1}}(B)+|A|-r_{M_{k+1}}(A\cup B).
$$
Every vector in this intersection is already a cycle at $s$, since $D_kD_{k+1}=0$. It is exactly the kernel of the map from the cycles at $s$ to homology at $t$. Subtraction gives (7). This establishes the rank invariant using the optimization queries in (6). [Carlsson–Zomorodian, the rank invariant](https://doi.org/10.1007/s00454-009-9176-0)

The component decomposition of $G$ is a direct-sum decomposition of the chain complex. Changing the grade origin in one component translates its entire multifiltration, which explains how the unspecified offsets affect the output. Given offsets, build the sets $A,B$ with the restored grades and use the same rank formula. Each query uses at most three oracle calls even when multiple components contribute.

For an affine line $t\mapsto x+t v$ with nonzero $v\ge0$, each cell enters at $\max_{\ell:\,v_\ell>0}(\gamma_{i,\ell}-x_\ell)/v_\ell$, provided it satisfies every coordinate fixed by the line. A cell that fails such a fixed coordinate never enters. Sort the finite entry times and use (7) at the ordered breakpoints. On a chain of $u$ breakpoints, with index zero before any cell enters, the multiplicity of a finite interval born at $i$ and dying at $j>i$ is
$$
 \rho(i,j-1)-\rho(i-1,j-1)-\rho(i,j)+\rho(i-1,j).
$$
The number of bars born at $i$ that survive indefinitely is $\rho(i,u)-\rho(i-1,u)$. This follows by counting the intervals containing both arguments. The slice algorithm uses $O(N^2)$ rank queries per homological degree. The result is an oracle extraction theorem and does not require a classification of general multiparameter modules. [Zomorodian–Carlsson, barcodes](https://doi.org/10.1007/s00454-004-1146-y) · [Lesnick–Wright, fibered barcode queries](https://arxiv.org/abs/2511.05837)

## 4. Exact reconstruction and the isomorphism action

Over $\mathbb F_2$ each nonzero boundary entry is one, so the feasible exchanges recover every matrix in the complex. This gives the whole filtered chain complex in the canonical origins, including persistence maps that the rank invariant by itself need not determine. To compare two anonymous cell presentations, decorate each vertex of $G$ by its homological degree and its recovered coordinatewise-minimum-centered grade. An isomorphism of these colored graphs gives a permutation in every chain degree that intertwines the reconstructed boundaries and all centered grades. Conversely a cell-permutation equivalence allowing a grade translation on each component gives a colored graph isomorphism. With explicit anchors, the actual component shifts are obtained by subtracting the grades of matched anchors. This is a coordinate-permutation action on the distinguished bases. [Grochow–Qiao, isomorphism reductions and marked coordinates](https://arxiv.org/abs/1907.00309)

For hardness, encode a finite simple graph by the binary chain complex with its vertices in degree zero, its edges in degree one, and the usual mod-two vertex–edge incidence matrix as $D_1$. Set every grade to zero. An incidence-preserving bijection in the two marked degrees is exactly a graph isomorphism, including isolated vertices. The matrices are explicit, and their optimization oracles are computable by weighted matroid greedy in polynomial time. The upper bound is a polynomial oracle reduction to colored graph isomorphism on already supplied oracle data, and a polynomial-time reduction with explicit binary boundary arrays or other polynomial-time evaluable realized oracles. Colors can be encoded in ordinary graph isomorphism with degree-separated leaf counts. For example, if there are $c$ colors and the input maximum degree is at most $\Delta$, attach $j(\Delta+2)$ fresh leaves to each vertex of color $j$, for $1\le j\le c$. Original vertices are recognizable by degree greater than one, and the resulting color bands are disjoint.

## 5. Controls and prior work

A filled triangle over $\mathbb F_2$ gives a control with both merging and killing. Assign vertices $0,1,2$ the grades $(0,0),(1,0),(0,1)$, the edges $01,02,12$ the grades $(3,0),(0,3),(2,2)$, and the face the grade $(4,4)$. The exchange for edge $12$ with vertex $1$ records $(1,2)$, and the exchange with vertex $2$ records $(2,1)$. On the diagonal line the degree-zero barcode is $[0,\infty),[1,2),[1,3)$, and the degree-one barcode is $[3,4)$. The three edge columns in the degree-one boundary sum to zero even though their supports admit a perfect matching. Thus substituting entrywise tropical matching for actual nonzero-minor support would return a wrong matroid in this example.

An exhaustive control considered all 58 pairs of $2\times2$ binary boundary matrices with product zero. For each pair, 20 deterministic bidegree assignments in $\{0,1,2\}^2$ were made monotone by taking each source grade coordinatewise at least its nonzero boundary grades. The resulting 1,160 cases gave 9,280 forced exchange tests. After reconstructing the grades up to component translations, (7) agreed with direct enumeration of cycles and boundaries in all 125,280 queries on comparable pairs in the grid, across the three homology degrees.

Henselman and Ghrist use matroid filtrations and matrix factorizations in persistent homology algorithms. Güzel and Kaygun encode filtered homological information by matroids and rooted forests. Tropical methods have also encoded statistics of barcodes. The result here starts with named priced maximal-minor oracles, recovers the missing componentwise filtration grades, and obtains each rank with three further priced queries. The exact binary chain reconstruction concerns the cellular coordinate action. The proof is in prose, and the inspected sources did not establish priority for the oracle reconstruction. [Matroid filtrations and computational persistent homology](https://arxiv.org/abs/1606.00199) · [Persistent homology, matroids and cobordisms](https://arxiv.org/abs/2209.01099) · [Tropical sufficient statistics](https://arxiv.org/abs/1709.02647) · [Fink–Moci, valuated matroids over valuation rings](https://arxiv.org/abs/1707.01026)
