# When can one batch of matrix products compute another?

Write $M(a,b,c)$ for multiplication of an $a\times b$ matrix by a $b\times c$ matrix. Its two input dimensions are $ab$ and $bc$. A restriction may linearly encode the inputs and linearly decode the outputs. A border restriction belongs to the Zariski closure of all such restrictions in the target tensor space. All three maps may vary. Work over an algebraically closed field, in particular over $\mathbb C$.

## Classification with both input dimensions saturated

Let the source and target be direct sums of independent products
$$
S=\bigoplus_j M(a_j,b_j,c_j),\qquad T=\bigoplus_i M(u_i,v_i,w_i)
$$
with positive integer parameters. Assume
$$
\sum_j a_j b_j=\sum_i u_i v_i,\qquad
\sum_j b_j c_j=\sum_i v_i w_i.
$$
Suppose all the target ratios $u_i/w_i$ agree. There is no ratio hypothesis on the source.

**Theorem.** The following conditions are equivalent.

1. $T$ is a border restriction of $S$.
2. $T$ is an exact restriction of $S$.
3. There are nonnegative integers $k_{ji}$ satisfying
   $$
   a_j=\sum_i k_{ji}u_i,\qquad c_j=\sum_i k_{ji}w_i,\qquad
   v_i=\sum_j b_j k_{ji}.
   $$

The criterion allows arbitrary linear encoders. Whenever it holds, input coordinate permutations and an output map with coefficients in $\{0,1\}$ suffice. For one source and one target, the two dimension equalities make the criterion exactly $b_1\mid v_1$. For example, $M(3,2,3)$ cannot degenerate to $M(2,3,2)$, although both inputs have dimension $6$ on each side and the output dimension drops from $9$ to $4$.

### The algorithm from the integers

In source product $j$, partition its $a_j$ rows into $k_{ji}$ groups of size $u_i$ for each $i$. Partition the $c_j$ columns into correspondingly labeled groups of size $w_i$. For target product $i$, partition its inner index into $k_{ji}$ intervals of length $b_j$ for each $j$. Copy the two input slabs on each interval into the matching source row and column groups. The source output block on that matching pair is precisely the partial product for the interval. Add these blocks over all its intervals to obtain the target product. Ignore the other output blocks. The three equalities allocate every input coordinate exactly once. This proves $3\Rightarrow2\Rightarrow1$.

### Why limits also have integer multiplicities

Write the common ratio as $p/q$ in lowest terms, with $p,q>0$. A slice of a tensor at an output dual coordinate is the coefficient matrix of the resulting bilinear form, with its rows indexing the first input and its columns the second. For $M(a,b,c)$ the slice with output coefficients $Z\in K^{a\times c}$ is, up to fixed permutations, $I_b\otimes Z$.

For a tensor $U$ on the target spaces, write $A_\ell$ for its slices in the standard output basis. Introduce one independent generic $q\times p$ matrix $X_\ell$ per output coordinate. Form the determinant
$$
D_U(X)=\det\left(\sum_\ell A_\ell\otimes X_\ell\right).
$$
This matrix is square since $q\sum_i u_i v_i=p\sum_i v_i w_i$. Its determinant coefficients depend polynomially on $U$. For $T$, permuting rows and columns yields
$$
D_T=\pm\prod_i \Delta_i^{v_i},
$$
where $\Delta_i$ is the determinant of a fully generic square matrix of size $q u_i=p w_i$. Indeed, each entry of the $u_i\times w_i$ slice is replaced by its own generic $q\times p$ matrix. The resulting determinants are nonassociate irreducibles since their variables are disjoint. For completeness, the singular matrices of size $h\ge2$ are the image of the product map on $h\times(h-1)$ and $(h-1)\times h$ matrices, hence form an irreducible hypersurface. The generic determinant has degree one in an individual entry, so it cannot be a proper power of an irreducible polynomial. Size one gives an indeterminate.

Under an exact restriction of $S$, the output map first produces arbitrary linear combinations of its slices. Before input encodings, the blown-up matrix is a direct sum, for each $j$, of $b_j$ identical blocks of size $q a_j\times p c_j$. The two input maps act on its left and right by square matrices tensored with identities. Thus any nonsquare block forces the entire determinant to vanish, since the sum of the individual ranks is then strictly smaller than the common total dimension. A singular input map also forces vanishing. If some $q a_j\ne p c_j$, the determinant therefore vanishes identically on all restrictions and their closure, contradicting $D_T\ne0$. Hence every source block has the target ratio.

Write $h_j=q a_j=p c_j$. For each restriction with nonzero determinant we now have, up to a scalar,
$$
D_U=\prod_j f_j^{b_j},\qquad \deg f_j=h_j,
$$
where $f_j$ is the determinant of a single blown-up block. This factorization pattern survives every nonzero limit. Indeed, multiplication of powers defines a morphism from the product of the projective spaces of nonzero degree-$h_j$ homogeneous forms up to scalar to the projective space of degree-$\sum_j b_jh_j$ forms. Its image is closed by projectivity. The affine cone over that image also includes zero and is closed. The polynomial map $U\mapsto D_U$ therefore takes the whole restriction closure into this cone.

Unique factorization at $D_T$ now writes $f_j$ up to scalar as $\prod_i\Delta_i^{k_{ji}}$. Comparing degrees gives $q a_j=\sum_i k_{ji}q u_i$. Comparing the exponent of $\Delta_i$ gives $v_i=\sum_j b_j k_{ji}$. The common ratios supply $c_j=\sum_i k_{ji}w_i$. This proves $1\Rightarrow3$.

The rectangular determinant here is a matrix semi-invariant of the familiar tensor blow-up type. Its factor degrees and multiplicities record the feasible allocations in this family. [Derksen and Makam, *Polynomial degree bounds for matrix semi-invariants*](https://arxiv.org/abs/1512.03393)

## Decision complexity and group algebras

**Corollary.** Given the two lists of dimensions in this theorem, deciding either restriction relation is strongly NP-complete. Hardness already holds when all source products are identical square products.

The multiplicities are polynomial-size certificates in binary since $k_{ji}\le a_j$. For hardness, take a 3-PARTITION instance with $3m$ integers $B/4<s_i<B/2$ summing to $mB$. Use $m$ copies of $M(B,B,B)$ as the source and one $M(s_i,B,s_i)$ per item as the target. Each input dimension totals $mB^2$ on both sides. The equations become $\sum_j k_{ji}=1$ for each item and $\sum_i k_{ji}s_i=B$ for each bin. Thus each item goes to exactly one bin, and the strict size bounds force exactly three items per bin. Strong hardness of 3-PARTITION implies hardness even for unary dimensions, where the canonical sparse or dense tensors also have polynomial encoding length. The NP upper bound here uses the supplied block lists. General tensor orbit-closure containment already has an NP-hardness theorem. Partition packing also appears in the embedding theory of finite-dimensional semisimple algebras. [Garey and Johnson](https://doi.org/10.1137/0204035) · [Bläser et al.](https://doi.org/10.1137/1.9781611976465.152) · [*On stable embeddability of partitions*](https://www.sciencedirect.com/science/article/pii/S0195669805001630)

For a finite group $G$ over $\mathbb C$, group-algebra multiplication is a direct sum of $M(d_j,d_j,d_j)$ indexed by the irreducible representation dimensions. Hence it computes a batch $\bigoplus_i M(u_i,v_i,u_i)$ using both full input dimensions $\sum_i u_iv_i=|G|$, even in the border sense, exactly when $d_j=\sum_i k_{ji}u_i$ and $v_i=\sum_j d_jk_{ji}$ have a nonnegative integer solution. Any solution gives an exact algorithm in Fourier coordinates. The trivial representation contributes $d_j=1$, so at least one target has $u_i=1$. For a single product this leaves exactly the inner product $M(1,|G|,1)$, realized by taking the identity coefficient of the group product after reversing the group indices in one input. This describes finite, input-saturating reductions with arbitrary encoders, a special case of interest in the group-theoretic approach. It provides no bound on the asymptotic exponent. [Cohn and Umans](https://arxiv.org/abs/math/0307321) · [Blasiak, Cohn, Grochow, Pratt and Umans](https://arxiv.org/abs/2204.03826)

## A sharp result with unused input dimensions

**Theorem.** Take a single source $M(a,b,a)$ and target $M(u,v,u)$. If the unused dimension in each input is $0\le\delta=ab-uv<b$, the target is a border restriction exactly when $u$ divides $a$. Every feasible conversion is exact. The strict threshold is sharp for every $b$.

Suppose $u\mid a$. The saturated theorem gives $M(u,ab/u,u)$ exactly. Zero-padding the two inputs along the inner index gives $M(u,v,u)$.

For necessity, let $Y$ be a generic $u\times u$ matrix of output coefficients. After an arbitrary linear output map, the source slice is $I_b\otimes Z(Y)$ for an $a\times a$ matrix $Z$ of linear forms. The two input encoders compress this matrix to size $uv$. By Cauchy–Binet its determinant is a linear combination of $(ab-\delta)$-minors of $I_b\otimes Z$. In each nonzero minor, every diagonal block retains the same number of rows as columns. At most $\delta$ copies lose rows, so at least $b-\delta$ copies retain both all rows and all columns. Their determinants factor out. If $\det Z$ is identically zero, the full slice has rank at most $ab-b<uv$ over the rational function field, and the compressed determinant is zero.

Consequently any nonzero compressed determinant has the form $f^{b-\delta}g$ with $\deg f=a$ and $\deg g=\delta(a-1)$. This homogeneous factor pattern, with zero adjoined, is closed by the same projective multiplication argument as above. At the target the determinant is $\pm\det(Y)^v$. Unique factorization makes $f$ a scalar multiple of a power of $\det(Y)$, so $u\mid a$. For sharpness choose $u\ge2$, $a=u+1$ and $v=b$. Deleting the extra row and column gives an exact restriction with $\delta=b$ and $u\nmid a$.

The same minor argument gives a numerical loss bound for a finite group algebra. If its multiplication degenerates to $M(u,v,u)$ and $\delta=|G|-uv\ge0$, then
$$
\delta\ \ge\ \max\bigl(\{d_j: u\nmid d_j\}\cup\{0\}\bigr).
$$
Indeed, the source slice is block diagonal with $d_j$ copies of a $d_j\times d_j$ matrix of linear forms for each $j$. Whenever $d_j>\delta$, every nonzero minor retains at least $d_j-\delta$ intact copies in block family $j$. The same closed factorization condition then forces $u\mid d_j$. For example, $S_3^k$ has order $6^k$ and an irreducible of degree $2^k$, obtained by tensoring its standard representations. Any degeneration to $M(3,v,3)$ loses at least $2^k$ dimensions in each input, so $v\le\lfloor(6^k-2^k)/3\rfloor$.

These are mathematical proofs on paper. Publication priority for the classification and its restricted hardness corollary is unverified.
