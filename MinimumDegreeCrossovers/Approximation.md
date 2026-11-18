# The sharp approximation threshold for minimum faithful permutation degree on small orbits

Fix a prime $p$. All input permutations are explicit. An approximation from above within $c$ is a value $v$ with $\mu(G)\le v\le c\mu(G)$, where $\mu(G)$ is the least degree of any faithful permutation action of the abstract group $G$.

**Theorem.** There is a deterministic polynomial-time $p$-approximation that outputs a faithful action for every permutation $p$-group supplied with orbits of size at most $p^3$. For every fixed $c<p$, approximating even the value from above within $c$ is NP-hard on that orbit class. The lower bound holds on class-two groups of exponent dividing $p$ for odd $p$, and exponent dividing four for $p=2$. Thus the sharp thresholds include factor three for the 27-point-orbit class at $p=3$ and factor two for the eight-point-orbit class at $p=2$. The assertions are informal proofs.

## An upper bound for arbitrary permutation $p$-groups on these orbits

Write $S=Z(G)[p]$ for the elementary abelian subgroup of central elements killed by $p$. A family of coset actions with point stabilizers $H$ is faithful exactly when $\bigcap_H(H\cap S)=0$. Every nontrivial normal subgroup of a finite $p$-group meets the center nontrivially, by the class equation, and a nontrivial central subgroup contains an element of order $p$. This proves the criterion.

A minimum action can be chosen with its orbit stabilizers cutting out independent hyperplanes on $S$. To see this, among minimum actions maximize the number of orbits. Remove any orbit with $H\cap S=S$. If $D=H\cap S$ has codimension at least two, choose $S_1,S_2\le S$ strictly containing $D$ with $S_1\cap S_2=D$, by choosing complementary nonzero subspaces of $S/D$. Replace the orbit by the coset actions of $HS_1,HS_2$. The faithfulness criterion is unchanged, and each new index is at most $[G:H]/p$. For odd $p$ the replacement lowers the degree, while at $p=2$ it lowers the degree or keeps it and increases the number of orbits. This excludes codimension at least two. A dependent collection of resulting hyperplane marks permits omitting an orbit while preserving faithfulness, so in a minimum action with maximum orbit count the marks form a basis of $S^*$. [Elias, Silberman and Takloo-Bighash on minimal permutation representations](https://arxiv.org/abs/0705.4122)

Write $d=\dim S$ and $a=\dim S/(S\cap\Phi(G))$, where $\Phi(G)=G^p[G,G]$. The index-$p$ marks on $S$ span precisely the $a$-dimensional subspace annihilating $S\cap\Phi(G)$, because index-$p$ subgroups of a $p$-group are kernels of characters of $G/\Phi(G)$. Therefore
$$
\mu(G)\ \ge\ pa+p^2(d-a).
$$
Use a basis of these $a$ characters first. For each orbit of the supplied action with point stabilizer $H$, choose a basis of the annihilator of $H\cap S$ in $S^*$. Any nonzero member $\lambda$ of that basis is realized as the mark of $H\ker\lambda$: its intersection with $S$ is $\ker\lambda$, and its index is at most $[G:H]\le p^3$. The union of these lists spans $S^*$ by faithfulness of the input action. Greedily choose a complement to the previously found $a$ characters. This constructs a faithful action of degree at most $pa+p^3(d-a)\le p\mu(G)$.

The computations are polynomial on explicit permutations. Compute the center and its abelian cyclic coordinates, and form $S$ from the order-$p$ parts of the cyclic factors. Abelian cyclic coordinates can be obtained from constructive membership and a Smith reduction of successive relative-order relations. Compute $\Phi(G)$ by taking the normal closure of generator powers and pairwise commutators, adding conjugates until membership tests find closure. Read coordinates of the elementary abelian quotient $G/\Phi(G)$ by successive adjoining of generators and constructive membership. For each supplied orbit compute its point stabilizer and the kernel $H\cap S$ of the restriction of $S$ to the orbit. The latter follows from dependencies of the elementary abelian images of the $S$ generators, by constructive membership. Compute the marked subgroups by adjoining a kernel basis to each stabilizer. Enumerate their cosets by membership, with at most $p^3$ cosets each. The number of basis marks, the resulting permutation degree, and all bit lengths are polynomial. [Seress, Permutation Group Algorithms](https://doi.org/10.1017/CBO9780511546549)

## Reciprocal tensors span a codimension-$(s-1)$ space

Put $F=\mathbb F_p$ and $E=\mathbb F_{p^s}$ for $s\ge1$. Write $m:E\otimes_F E\to E$ for multiplication. Then
$$
 \operatorname{span}_F\{x\otimes x^{-1}:x\in E^\times\}=m^{-1}(F1),
 \qquad \dim_F m^{-1}(F1)=s^2-s+1.
$$
The inclusion follows from $m(x\otimes x^{-1})=1$. For equality use the finite-field tensor-product isomorphism $E\otimes_F E\to E^s$ with coordinates $x\otimes y\mapsto (xy^{p^i})_{i=0}^{s-1}$. It follows by evaluating the separable minimal polynomial of an $F$-generator of $E$ at its $s$ Frobenius conjugates. The reciprocal tensors have coordinates $(1,x^{1-p},\ldots,x^{1-p^{s-1}})$.

By nondegeneracy of the field trace, every $F$-linear functional on $E^s$ has the form $(z_i)\mapsto\sum_i\operatorname{Tr}_{E/F}(a_i z_i)$. On the reciprocal set the $i=0$ term is a constant. For $i>0$, expand the trace on that coordinate. Its multiplicative exponents, reduced modulo $p^s-1$, are $p^j-p^{(i+j)\bmod s}$ for $0\le j<s$. Across all these terms there is exactly one for each ordered pair of distinct powers $p^j,p^k$ in this range. The signed differences are distinct integers: their sign and $p$-adic valuation recover which power is smaller and its exponent, and their absolute value then recovers the larger power. All lie between $-(p^{s-1}-1)$ and $p^{s-1}-1$, an interval of width less than $p^s-1$, so they remain distinct modulo $p^s-1$; none is zero. This applies also at $p=2$. Distinct power functions of exponents from $0$ to $p^s-2$ are linearly independent over $E$ on $E^\times$, by the polynomial root bound. A functional vanishing on the reciprocal set must therefore have $a_i=0$ for $i>0$ and $\operatorname{Tr}(a_0)=0$. These are exactly the $s-1$ independent dimensions of its annihilator, proving the formula. At $s=1$ the same argument has no nonconstant terms and gives the one-dimensional span directly.

## A polynomial reduction from bipartite precoloring extension

Use the [matrix space from bipartite list three-coloring](PrimeHardness.md), where singleton lists implement precolors. It is a linear space $L_{\rm core}$ of $a_0$-by-$b_0$ matrices with a distinguished coefficient $c(M)=M_{00}$. Its hyperplane $c=0$ has a rank-one basis, there is an explicitly computed matrix $M_*$ with $c=1$ of rank at most two, and there is a rank-one matrix with $c=1$ precisely when the precoloring extends. The construction and all three properties work for every prime, including two. [Kratochvíl, Precoloring Extension with Fixed Color Bound](https://www.iam.fmph.uniba.sk/amuc/_vol-62/_no_2/_kratoch/kratochv.html)

Enlarge the row and column spaces by $E$. Define a new linear matrix space $L$ as follows. Its upper left block is any $M\in L_{\rm core}$, the two mixed blocks are arbitrary, and its $E\otimes_F E$ block $B$ satisfies
$$
                      m(B)=c(M)\,1 .
$$
All conditions are linear in the matrix entries. At fixed $p$ the field $E$ and its multiplication table are constructible deterministically in polynomial time in $s$. [Shoup, deterministic construction of irreducible polynomials](https://www.shoup.net/papers/detirred.pdf)

Let $L_0$ be the subspace with core block in $c=0$, arbitrary mixed blocks, and $B=0$. Its dimension is $d_0=\dim L_{\rm core}-1+s(a_0+b_0)$. It has a rank-one basis from the core hyperplane basis and the mixed-block matrix units. Projection to $B$ has kernel $L_0$ and image $m^{-1}(F1)$, since $c$ is onto. Write $h=s^2-s+1$ and $d=d_0+h=\dim L$.

If the coloring fails, a rank-one element of $L$ has $c=0$, since its core submatrix has rank at most one. Its $B$ block, being a pure tensor $x\otimes y$, satisfies $xy=0$. Thus the field property forces $B=0$, and its rank-one span is exactly $L_0$. If the coloring succeeds, fix one rank-one core matrix $u v^{\mathsf T}$ with $c=1$. For every $x\in E^\times$, the rank-one matrix with factors $(u,x)$, $(v,x^{-1})$ lies in $L$. Its projection to $B$ ranges through the reciprocal tensors. Their span is the whole image, while $L_0$ is already spanned by rank-one matrices. Thus in the yes case the rank-one span is all of $L$.

The space $L$ has a polynomially computable basis of rank at most two in both cases. Use the rank-one basis of $L_0$, and bases of the kernel of $m$ in the dummy block. For the latter take $e_i\otimes e_j-1\otimes e_i e_j$ for $i>0$ and all $j$, with $e_0=1$. These tensors have rank at most two, and their independent projections away from the first row prove they form a basis. Finally express the pivot matrix $M_*$ as the sum of at most two rank-one terms by elimination. Extend one term by the dummy coordinate $1\in E$ in each factor, and leave the other term supported on the core. The resulting rank-at-most-two matrix has pivot one and dummy block $1\otimes1$, satisfying the constraint. Its mixed blocks are allowed. These matrices give the required explicit basis.

## Transfer the gap to permutation-group optimization

Use the [cross commutator construction and exact rank formula](PrimeHardness.md) on $L$ over $F$, after removing the common left and right radicals from the tangent halves. Removing these radicals does not change the ranks of the matrices or the dimension of $L$. The center is the derived group, with dual $L$. The computed rank-at-most-two basis supplies a faithful action all of whose orbits have size at most $p^3$, with degree polynomial in the written matrix space. The construction uses exponent dividing $p$ for odd $p$, and the split quadratic class-two group of exponent dividing four at $p=2$. For a rank-$j$ central mark, the least orbit that detects it has size $p^{j+1}$. Every nonzero mark here has positive rank, and the exhibited basis gives every remaining needed direction at cost at most $p^3$. Thus the least degree is $p^2r+p^3(d-r)$, where $r$ is the dimension of the rank-one span. In the two cases we have exactly
$$
  \mu_{\rm yes}=p^2(d_0+h),\qquad
  \mu_{\rm no}=p^2d_0+p^3h.
$$

Take $s=C(a_0+b_0+1)$ for an integer constant $C$. Since $\dim L_{\rm core}\le a_0b_0$, the ratio $d_0/h$ tends to zero uniformly in the input as $C$ tends to infinity. For example $d_0\le s(a_0+b_0)+(a_0+b_0)^2/4$ and $h\ge s^2/2$, giving $d_0/h\le 2/C+1/(2C^2)$. Hence $\mu_{\rm no}/\mu_{\rm yes}$ tends to $p$. For any fixed rational $c<p$, choose $C$ so this ratio is strictly greater than $c$ on every input. The two values are explicitly computable from the construction. An approximation from above of factor $c$ falls strictly below $\mu_{\rm no}$ exactly in the yes case. This proves NP-hardness. For a real factor below $p$, take a rational factor between it and $p$. The result for factor $p$ is the algorithm in the first section.

The earlier minimum-degree reduction turned independent low-rank central directions into abnormally small orbits. This proof replaces symmetric padding with a bilinear multiplication constraint. Its many reciprocal points fill a space with only a linear number of missing dimensions, attaining the approximation threshold dictated by the orbit cap.
