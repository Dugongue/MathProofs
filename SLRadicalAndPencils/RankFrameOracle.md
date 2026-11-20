# A variable-dimension Turing reduction to tensor isomorphism using rational rank loci

## Statement

Let $F=\mathbf F_q$ be explicitly represented in a polynomial basis. Take two $m$ by $n$ linear matrix maps $A(x),B(x)$ in $r\ge 2$ variables over $F$, with $m,n,r,q$ part of the input. For a nonnegative integer $k$ write
$$
S_k(A)=\{[x]\in\mathbf P^{r-1}(F):\operatorname{rank} A(x)\le k\}.
$$
Suppose the same threshold $k$ is used for $A$ and $B$ and complete lists of $S_k(A)$ and $S_k(B)$ are supplied or computable in polynomial time. The source list contains a projective frame, meaning $r+1$ points such that every $r$ of their vector representatives are independent. The target list may be arbitrary.

Given $c,s,t\in F^\times$, there is a deterministic polynomial-time Turing reduction to ordinary three-tensor isomorphism over the same $F$ for deciding whether
$$
B(fx)g=hA(x),\qquad
\det f=c,\qquad\det g=s,\qquad\det h=t,
$$
for invertible $f,g,h$ of sizes $r,n,m$. For supplied complete lists, running time is polynomial in their explicit lengths and the tensor input bit length. For algorithmically computed lists, running time is polynomial in the tensor input bit length. In particular, the relation is decidable by this reduction when the three prescribed determinants are $1$. The covariant convention takes inverse transposes on the label and column modes as in the accompanying pencil theorem.

The final section gives a variable-$r$ family with no supplied lists or list-computing assumption, arbitrary data blocks, and a rank locus that is generated explicitly in polynomial time. The reduction uses the ordered transporter and determinant-image algorithms from “Ordered equivalence with prescribed determinants” in the accompanying paper *Deterministic polynomial-time special-linear equivalence of matrix pencils over finite fields*. It uses the ordered algorithm in arbitrary label dimension, as allowed by that lemma.

## Queries with marked images

Suppose $j$ distinct rational projective points $p_1,\ldots,p_j$ are required to map to distinct specified rational projective points $u_1,\ldots,u_j$. For any rational point $p$, choose a surjective linear map $L_p:F^r\to F^{r-1}$ with kernel equal to its line. Regard $L_p(x)$ as an $(r-1)$ by $1$ matrix with linear entries. It has rank $0$ at $p$ and rank $1$ at every other projective point. Compute it by linear algebra on a point representative.

Put $D=j+1$ and $C=\sum_{i=1}^j i$. Query ordinary tensor isomorphism on the pair
$$
A^{\oplus D}\oplus\bigoplus_{i=1}^j L_{p_i}^{\oplus i},
\qquad
B^{\oplus D}\oplus\bigoplus_{i=1}^j L_{u_i}^{\oplus i},
$$
where direct sums are on row and column spaces with the same label variables. The rank of the first matrix at any point, minus $C$, is congruent to $-i$ modulo $D$ at $p_i$, and to $0$ elsewhere. The second has the corresponding property at $u_i$. These residues are distinct for $0\le i\le j$. Thus a label map in any affirmative augmented instance has all the required point images. When $j=0$ this is the unmarked ordinary TI query.

Once $f$ has the required point images, $L_{u_i}(fx)$ and $L_{p_i}(x)$ are strictly equivalent by a constant invertible row map, since both linear maps are surjective and have the same kernel. Strict equivalence is isomorphism of representations with two vertex spaces and $r$ parallel arrows, one per variable. The Krull–Schmidt theorem gives cancellation of common summands and equality of the multiplicities of all indecomposable representations. Canceling the marked summands and dividing the remaining multiplicities by $D$ shows that $A(x)$ and $B(fx)$ are strictly equivalent. Conversely an ordinary transporter with the required marks gives an augmented transporter by taking direct sums with the marked equivalences. Therefore the oracle answer is exactly the existence of an ordinary transporter with the imposed point images. The construction is polynomial in the input length and $j$, including the number $C$ of marker summands. [Sergeichuk, Theorem 2.1 over arbitrary fields](https://arxiv.org/pdf/0709.2470)

## Generating the permitted projective label group

An ordinary transporter maps $S_k(A)$ bijectively onto $S_k(B)$, since it is rational and preserves slice rank. Reject differing list sizes. The frame assumption lets us compute a short tuple of source points which determines projective maps. This construction uses the list directly, without a supplied frame.

Choose a basis $v_1,\ldots,v_r$ from the list by Gaussian elimination, which exists since the list contains a frame. Write each remaining point in this basis. Make a graph on the $r$ basis indices, joining two whenever a list point has both corresponding coordinates nonzero. The graph is connected. Otherwise every list point is supported in one component, and a frame of $r+1$ points would contradict this partition. More explicitly, a frame has a unique relation among its representatives, with all coefficients nonzero. A partition into nonempty component subsets would split that relation into independent groups, giving a dependence of a proper frame subset. If all frame points were supported in a single proper component, they could not span. Take a spanning tree of the graph. For each tree edge record one list point having both coordinates nonzero, and remove repeated records. Append their points to the basis points in a fixed ordering. This gives a determining tuple of at most $2r-1$ distinct points. Any projective map fixing the tuple pointwise has a diagonal representative in the basis, and fixing a recorded line forces equality of the two diagonal entries at its corresponding edge. By the spanning tree all entries are equal. In the explicit family one can simply use its frame as the determining tuple.

Write $p_1,\ldots,p_d$ for the chosen tuple. Its images under a rational projective map determine that map uniquely. Indeed, two maps with those images differ by an element fixing the tuple pointwise. To recover the map from images $u_1,\ldots,u_d$ known to be feasible, solve the homogeneous linear equations
$$
f(v_i)\in \langle w_i\rangle
$$
in the entries of $f$, with representatives $v_i,w_i$ of the corresponding lines. The solution space is one-dimensional. To see this, compose on the left by a feasible invertible map's inverse and on the right use the source basis coordinates. Every solution becomes diagonal because each basis line is fixed or mapped to zero, and fixing each recorded line in the sense of containment forces the same diagonal equalities as before, including when all the supported diagonal entries are zero. Thus all solutions are scalar multiples of the feasible map. This proof also works for a frame directly by taking its first $r$ points as the basis and the last point as the single recorded line with full support. Choose any nonzero solution and normalize by its first nonzero entry.

First decide ordinary equivalence using the unmarked oracle. If it holds, find a feasible sequence of images of the determining tuple in $S_k(B)$ by extending the partial marks one at a time. At each step query each candidate target point with all existing marks until a feasible one is found. Recover a normalized label matrix $f_0$. Its scalar class has an ordinary transporter. Any nonzero scalar multiple of a feasible $f$ is feasible, since a scalar multiplier in $B(fx)$ can be absorbed by the inverse scalar on $g$. Find $(g_0,h_0)$ by ordered module isomorphism with the actual normalized $f_0$.

Let $P_A$ be the group of projective classes of labels of ordinary automorphisms of $A$. It acts faithfully on $S_k(A)$ by the determining tuple property. Let $P_i$ be the subgroup fixing $p_1,\ldots,p_i$, and let $P_0=P_A$. For each $i$ and each possible image $u\in S_k(A)$ of $p_i$, use the marked oracle with fixed images for $p_1,\ldots,p_{i-1}$ and image $u$ for $p_i$. When affirmative, extend the marks greedily to recover a representative $\sigma_{i,u}$ in $P_{i-1}$. For every $\sigma\in P_{i-1}$ with $\sigma(p_i)=u$, the element $\sigma_{i,u}^{-1}\sigma$ belongs to $P_i$. Thus the representatives together with $P_i$ generate $P_{i-1}$. The group $P_d$ is trivial. The resulting polynomial-size collection generates $P_A$. Lift each representative to its normalized rational matrix $f_a$ and find ordered pairs $(g_a,h_a)$ by module isomorphism. All greedy extensions and all generator searches use at most a polynomial number of marked queries. Each query uses an ordinary tensor instance of polynomial dimensions over the given $F$.

## The determinant quotient

Let
$$
G_A=\{(f,g,h): A(fx)g=hA(x)\}
$$
be the group of ordinary automorphisms under componentwise multiplication. Project to $P_A$ using the projective class of $f$. The kernel consists exactly of ordered strict units together with the scalar-label transformations
$$
(\lambda I_r,\lambda^{-1}I_n,I_m),\qquad \lambda\in F^\times.
$$
Indeed $A(\lambda x)=\lambda A(x)$, and composing a kernel element with the inverse of its scalar-label transformation leaves $f=I_r$. Let $H$ be the image of this kernel under the homomorphism $(f,g,h)\mapsto(\det f,\det g,\det h)$. It is the monomial image from the ordered stabilizer columns, each with first coordinate $0$, together with the column $(r,-n,0)^{\mathsf T}$ for the scalar-label transformations. The accompanying ordered determinant-image algorithm computes the columns without finite-field factoring.

Put $N_F=q-1$. Adjoin $N_F I_3$ to the three-row column matrix, take its integer column lattice basis, and choose a Smith normal form. Let $U$ be its unimodular row transform and $d_i$ its positive diagonal entries. Each $d_i$ divides $N_F$ because the transformed lattice contains $N_F\mathbf Z^3$. For $w\in(F^\times)^3$, write $(U\cdot w)_i=\prod_j w_j^{U_{ij}}$. The quotient map
$$
\Phi(w)_i=(U\cdot w)_i^{N_F/d_i}
$$
has kernel exactly $H$: coordinatewise, raising to $N_F/d_i$ on the cyclic group $F^\times$ has kernel the $d_i$-power subgroup. Its image is a subgroup of $(F^\times)^3$, and implements the quotient without finding a primitive field element. [Kannan and Bachem, integer normal forms](https://epubs.siam.org/doi/10.1137/0208040)

The determinant image of $G_A$ modulo $H$ is generated by the $\Phi$-images of the determinant triples of $(f_a,g_a,h_a)$. Every choice of lift for a projective element differs by a kernel element, and the listed projective elements generate $P_A$. All ordinary transporters from $A$ to $B$ are the right coset of $G_A$ based at $(f_0,g_0,h_0)$. Thus the prescribed determinant test is precisely the membership of
$$
y=\Phi\!\left(c/\det f_0,\ s/\det g_0,\ t/\det h_0\right)
$$
in the subgroup of $(F^\times)^3$ generated by the $\Phi$-images of the lifted generators.

## Membership in the smooth-order subgroup

Let $L=|S_k(A)|$ and $E=L!$. The group $P_A$ is a subgroup of the permutation group on $L$ points, so its order divides $E$. The map $\Phi\circ\det$ on $G_A$ factors through $P_A$. Consequently each generator image has order dividing $E$. If some coordinate of $y$ has $E$th power different from $1$, reject. The integers $E$ and its prime-power factors can be computed directly with a sieve up to $L$ and the usual factorial valuations. Their bit lengths are polynomial in $L$.

For every prime $p$ dividing $E$, let $p^a$ be its full power in $E$. In each coordinate raise the target and the generator entries to $E/p^a$ to kill the other prime parts. The resulting values have $p$-power orders. Testing equality before these projections is equivalent to testing equality after every such projection, since the projections are injective on their respective primary parts. In each coordinate and for each $p$, choose from the projected entries, including the target, an entry $\gamma$ of maximum order $p^b$. Determine exact orders by successive power tests. Cyclicity of $F^\times$ means every projected entry in that coordinate is a power of $\gamma$. If $b=0$ there is no equation for that coordinate and prime.

Compute these exponents by a base-$p$ digit calculation. If an entry $z=\gamma^u$ and $v$ is the part of $u$ already computed modulo $p^j$, then
$$
(z\gamma^{-v})^{p^{b-j-1}}=(\gamma^{p^{b-1}})^{z_j}
$$
with $z_j$ the next digit. Precompute the $p$ possibilities on the right, recover $z_j$, and continue until $j=b-1$. This costs polynomial time since all relevant primes are at most $L$ and all exponent bit lengths are polynomial in $L+\log q$. The calculation also works when the target generates a larger cyclic subgroup than the generator entries in a coordinate, in which case a congruence can reject it.

For a single list of unknown integer generator exponents, all coordinate and prime tests are linear congruences modulo the computed orders $p^b$. Collect the generator discrete log columns and append one diagonal column for each modulus. Membership of the target log vector in this integer column lattice, decided by Hermite normal form, is exactly solvability of all congruences together. This decides the required subgroup membership in polynomial bit time. Only primes bounded by the explicitly listed number of points were enumerated, and no discrete log in a cyclic group of unknown or potentially large prime order was needed.

Together with the marked-query construction this gives a same-field deterministic polynomial-time Turing reduction. The result decides the existence of a prescribed-determinant transporter. It does not require producing such a transporter.

## An explicit variable-dimension family

Let $r\ge 3$ vary, take arbitrary same-size $a$ by $b$ data matrix maps $A_{\rm data}(x),B_{\rm data}(x)$, and choose $P>\min(a,b)$. Use the same scalar blocks on both sides:
$$
A(x)=\operatorname{diag}\big(A_{\rm data}(x),L_1(x)I_P,\ldots,L_{r+1}(x)I_P\big),\qquad
L_i=x_i\ (i\le r),\quad L_{r+1}=-\sum_{i=1}^r x_i .
$$
Define $B$ by replacing the data block. Both inputs can be given in this form or constructed from the data as explicit tensors. The label map $x\mapsto(L_1(x),\ldots,L_{r+1}(x))$ identifies $F^r$ with the sum-zero subspace of $F^{r+1}$. At threshold $k=2P+\min(a,b)$, the low rank points are exactly those with two nonzero coordinates in the sum-zero subspace. Exactly two give rank at most $k$, at least three give rank at least $3P>k$, and one nonzero coordinate cannot have sum zero. Thus both rational lists are the explicit $\binom{r+1}{2}$ lines of the vectors $e_u-e_v$ for $u<v$, represented by their first $r$ coordinates. The cyclic differences $e_i-e_{i+1}$ for $i$ modulo $r+1$ are a frame, since the only relation on all $r+1$ vectors has all coefficients equal. This holds in every characteristic. The input is square when $a=b$ and rectangular otherwise. For $r\ge3$ the generic rank-drop locus includes positive-dimensional hyperplanes $L_i=0$.

The theorem uses data blocks of arbitrary rank and applies with both the label dimension and the field varying. The finite point lists and a frame are obtained directly for this family. The reduction uses no Riemann hypothesis. This is a paper proof and has no Lean certificate. It concerns a restricted family of the open special-linear reverse reduction. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)
