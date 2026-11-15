# Faster computation of low-degree graph multiplicity obstructions

**Theorem.** Given two simple graphs on $n$ vertices and a degree bound $d$, one deterministic algorithm computes all multiplicities in their degree-at-most-$d$ vanishing modules over characteristic zero in
$$
2^{O(d\log(d+2))}\,
n^{O(1+d/\sqrt{\log(d+2)})}
$$
bit time. It returns a partition witnessing a multiplicity obstruction when one exists, together with both exact multiplicities. The same bound decides whether a degree-at-most-$d$ separating module exists and produces one specified by a compact orbit-span description. All degrees up to $d$ can be tested separately within this bound.

This gives a sublinear exponent of $n$ as a function of $d$ with a separate $2^{O(d\log(d+2))}$ factor, for Grochow and Urisman's Question 1.10. In particular the entire running time is $n^{o(d)}$ in the joint regime $d\to\infty$, $d=n^{o(1)}$. The proof uses characteristic zero, as in their introduction. The compact separating-module output differs from their explicit list of monomials. An unrestricted jointly uniform $n^{o(d)}$ time bound without the displayed parameter factor is a separate question. [Grochow–Urisman, Question 1.10 and Theorems 3.1 and 6.3](https://arxiv.org/html/2606.26244v2)

## 1. A small exact algebra represents the large vanishing modules

Let $\mathcal M_d$ be the set of squarefree monomials of degree at most $d$ in the $\binom n2$ unordered edge variables. Put $V_d=\mathbb Q^{\mathcal M_d}$ and use the standard dot product. The symmetric group $S_n$ acts by permuting the variables and thus the monomial basis. For a labeled graph $G$ let $v_G$ have coordinate $m(G)$ at monomial $m$. Set
$$
 A_G=\sum_{\sigma\in S_n} v_{\sigma G}v_{\sigma G}^{\mathsf T}.
$$
The vanishing module $I_{G,\le d}$ is the kernel of $A_G$: a rational vector lies in that kernel exactly when it is orthogonal to every $v_{\sigma G}$, by evaluating the sum of squares in its quadratic form over the reals. The matrices are rational, so this equality also holds after extension to any characteristic-zero field. The entries of the matrix are constant on orbits of ordered pairs of monomials. If their union of edges defines a graph $Q$ on the $s$ incident vertices, the entry is $(n-s)!\operatorname{inj}(Q,G)$, where $\operatorname{inj}$ counts injective graph homomorphisms. This is because an injection of the support vertices into $G$ extends to exactly $(n-s)!$ label permutations.

Use the orbit-indicator matrix basis of $B=\operatorname{End}_{S_n}(V_d)$. Each basis element has entry $1$ at the pairs in one orbit, and $0$ elsewhere. Every orbit has a representative on at most $4d$ vertices, specified by two marked edge sets of size at most $d$. Representatives can be listed in $2^{O(d\log(d+2))}$ time by listing the possible small edge sets and identifying isomorphism types by permutations of at most $4d$ vertices. Use only representatives with at most $n$ vertices. The identity is the sum of the diagonal orbit matrices.

To compute the coefficient of the product of two orbit matrices at a representative $(m_1,m_3)$, count the middle monomials $m_2$ such that $(m_1,m_2)$ and $(m_2,m_3)$ are in the two prescribed orbits. Keep the labels in $m_1,m_3$ fixed and list $m_2$ patterns using up to $2d$ new placeholders. For a pattern using exactly $u$ new placeholders, all labeled $m_2$ are counted by dividing $(n-s)_u$ by the size of the automorphism group of the new placeholders fixing the old labels, where $s$ is the number of old labels and $(x)_u$ is a falling factorial. Use one representative under renaming of placeholders and discard patterns requiring more than $n-s$ of them. This computes every structure constant in $2^{O(d\log(d+2))}\operatorname{poly}(n)$ bit time, including the enumeration of all orbit pairs and all entries. The trace is also cheap. A diagonal orbit represented by a monomial with graph $Q$ on $s$ vertices contributes $(n)_s/|\operatorname{Aut}(Q)|$, and an off-diagonal orbit has trace zero.

Once the entries of $A_G$ are known, compute its minimal polynomial by finding the first linear dependence of $1,A_G,A_G^2,\ldots$ in $B$. Let $b=\dim B$. At most $b$ powers are needed. If the minimal polynomial has no zero root the kernel projector $P_G$ is zero. Otherwise write that polynomial as $Tg(T)$ with $g(0)\neq0$. This is possible since $A_G$ is real symmetric and hence diagonalizable. Then $P_G=g(A_G)/g(0)$ is the orthogonal projector onto the kernel. Matrix products and rational linear algebra use the compact coordinates throughout. To see the bit bound, the input entries of $A_G$ are nonnegative integers at most $n!$, and those of its first $b$ powers have magnitudes at most $(n!\dim V_d)^{b}$ up to the identity term. Thus their bit lengths are $2^{O(d\log(d+2))}\operatorname{poly}(n)$. Fraction-free elimination or rational elimination with minors bounding intermediate numerators and denominators suffices. The same analysis applies to $H$.

## 2. Reading the exact irreducible multiplicities

For a partition $\lambda$ of $n$, let $f^\lambda$ be the dimension of the corresponding Specht module and $\chi_\lambda$ its character. We compute the central projector
$$
 E_\lambda=\frac{f^\lambda}{n!}\sum_{\sigma\in S_n}\chi_\lambda(\sigma^{-1})\rho(\sigma)
$$
in the orbit-matrix basis, where $\rho$ is the action on monomials. Only partitions with $\lambda_1\ge n-2d$ are needed. In fact a monomial with support size $s\le2d$ has a stabilizer containing a copy of $S_{n-s}$ fixing those $s$ vertices individually. An irreducible present in its orbit span therefore has a nonzero $S_{n-s}$-fixed vector by Frobenius reciprocity. By the branching rule, the one-row diagram of size $n-s$ must fit in $\lambda$, which requires $\lambda_1\ge n-s$. All candidate partitions are listed by their tail of size at most $2d$.

For an ordered pair of monomials, list every bijection $\pi$ from the support of the column monomial to the support of the row monomial that maps the former edge set to the latter. The $(\text{row},\text{column})$ entry in the character sum is the sum of $\chi_\lambda(\sigma)$ over all permutations extending such $\pi$. Inverse permutations have the same character since they have the same cycle type. There are at most $(2d)!$ partial bijections and their extension sets are disjoint.

Here is a direct exact calculation of a partial-bijection character sum. Let $\ell$ be the number of rows of $\lambda$. By Jacobi–Trudi and the Frobenius characteristic, write $\chi_\lambda$ as a signed sum indexed by $\tau\in S_\ell$ of Young permutation characters. The ordered block sizes in the term $\tau$ are $\alpha_i=\lambda_i-i+\tau(i)$. Discard terms with a negative part and treat size-zero blocks as empty. A Young permutation character with block sizes $\alpha_i$ counts colorings of $[n]$ having those sizes whose colors are preserved by the permutation. This is the character identity obtained by expanding $\det(h_{\lambda_i-i+j})$, since $h_{\alpha_1}\cdots h_{\alpha_\ell}$ is the characteristic of the representation on those ordered partitions. [Garsia and Remmel, Algorithms for the Character Theory of the Symmetric Group](https://sites.cs.ucsb.edu/~omer/DOWNLOADABLE/symmetric_group85.pdf)

For each $\pi$ and each term, enumerate colors of the union of domain and image of $\pi$, which uses at most $4d$ vertices. Require that $\pi$ preserve those colors. If there are $u_i$ already colored vertices of color $i$ and $b_i$ prescribed arrows with domain color $i$, the number of pairs consisting of a completed coloring and a color-preserving permutation extending $\pi$ is
$$
 \frac{(n-\sum_i u_i)!}{\prod_i(\alpha_i-u_i)!}\,
 \prod_i(\alpha_i-b_i)!.
$$
Take the number as zero if some $u_i>\alpha_i$. The first factor assigns the remaining colors. The second factor independently completes a partial permutation inside each block. Summing gives the required character contribution. Since $\ell\le2d+1$, enumeration over all determinant terms, partial maps and colors takes $2^{O(d\log(d+2))}\operatorname{poly}(n)$ bit time. The hook-length formula computes $f^\lambda$ within the same bound.

The multiplicity of $\lambda$ in $I_{G,\le d}$ is
$$
 \frac{\operatorname{tr}(E_\lambda P_G)}{f^\lambda}.
$$
Indeed $P_G$ commutes with the action and therefore with $E_\lambda$, and the product projects onto the $\lambda$-isotypic part of the kernel. Computing the multiplicity in the degree-filtered orbit coordinate ring instead subtracts this integer from $\operatorname{tr}(E_\lambda)/f^\lambda$. Either convention gives the same obstruction comparison. Products and traces use the orbit-matrix algebra. If any multiplicities differ, output $\lambda$ and both integers.

For the optional separating-module search, the exact value
$$
 \operatorname{tr}(P_G A_H)=n!\|P_G v_H\|^2
$$
decides the oriented question of vanishing on $G$ and nonvanishing on $H$. The equality uses equivariance of the orthogonal projection. When it is positive, $P_Gv_H$ interpreted as a polynomial separates the labeled inputs, and its $S_n$-span is a separating module. Output $H$ and the compact orbit coefficients for $P_G$, with the specified rule to form that span. Check the opposite orientation as well if desired. This algorithm does not expand the degree-$d$ monomial basis.

## 3. Exact graph counts with sublinear exponent in the edge bound

The remaining inputs are $\operatorname{inj}(Q,G)$ with at most $2d$ edges. To compute them, first compute homomorphism counts for quotients of $Q$ by all partitions of its incident vertices, identifying duplicate edges and treating loops as giving zero on simple hosts. A quotient still has at most $2d$ distinct edges. Möbius inversion on vertex partitions gives the injective count, since a map with a prescribed equality partition factors uniquely through that quotient. The number of partitions and the cost of the inversion are $2^{O(d\log(d+2))}$ and the count integers have $O(d\log n)$ bits.

Consider one pattern with $e\le 2d$ edges. Isolated vertices supply a factor of $n$ each, so remove them for the computation. To compute its homomorphism count, introduce one variable taking values in $[n]$ for each incidence of a vertex with an edge. For each edge require that the two incidence values are adjacent in the host. For each pattern vertex join its incidence variables along a path of equality constraints. There are at most $4d$ variables, the constraint graph has degree at most three, and the counting is exact. Represent the constraints by explicit complete tables on domain $[n]$, using the host adjacency matrix for adjacency and the identity table for equality. Nguyen's Theorem 1.2 counts complete-table binary CSP instances of any fixed maximum primal degree $\Delta$ in deterministic finite-alphabet machine time $L^{O_\Delta(1)}D^{O_\Delta(k/\sqrt{\log k})}$ for sufficiently large $k$, where $L$ is the encoded length, $D$ the domain size, and $k$ the variable count. Here $D=n$, $k\le4d$, $\Delta=3$ and $L=O(d^2(n+1)^2)$. The exact native encoding in that paper uses the edge mask and one relation table for each ordered pair of variables. Both the encoding and its length satisfy these bounds. It follows that the host-size factor for one homomorphism count is $n^{O(1+d/\sqrt{\log(d+2)})}$ times a polynomial in $d$. For the finitely many values of $k$ below the fixed bound of Theorem 1.2, brute-force counting uses a constant exponent of $n$. The polynomial factors in $d$, the enumeration of pattern counts, and the orbit algebra overhead are all absorbed by $2^{O(d\log(d+2))}$. Small $n$ and $d=0$ are immediate by direct evaluation. [Nguyen, *A Sublinear Treewidth Exponent for Binary Constraint Satisfaction*, Theorem 1.2 and §2.3](https://hexagonmath.org/2611.00004v1)

Nguyen's exact finite-alphabet counting theorem comes from the clique-contraction recursion of Claude (Anthropic), Theorem A(a,b) and Theorem B. It handles arbitrary complete relation tables with a growing domain and charges bit complexity. The reduction here uses it for degree-three networks, independently of the expander and treewidth parts of Nguyen's result. [Claude (Anthropic), *A $2^{o(n)}$ Time Algorithm for 3-SAT*, Appendices A and B](https://hexagonmath.org/pdf/2610.00577v1#page=28)

If ordered adjacency variables are retained, all pair-orbit and character computations work unchanged on ordered-edge patterns. For an undirected input graph one can also use the equivariant surjection from the ordered degree-filtered polynomial space to the unordered one, identifying opposite variable directions and sending loops to zero. The graph-independent kernel adds the same multiplicities to both vanishing spaces, so all obstructions agree. For a directed input one uses directed adjacency tests in the corresponding incidence network.

The reduction from filtered orbit multiplicities to graph counts uses the pair-orbit algebra and the partial-permutation character sums above. A targeted search found no previously published algorithm with this bound for Question 1.10. This is an informal proof.
