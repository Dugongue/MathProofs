# Derived equivalence with identical Hochschild cup products

**Theorem.** Over every field $k$, Graph Isomorphism has a deterministic polynomial-time many-one reduction to $k$-linear derived equivalence of split basic algebras of global dimension exactly two, with three simple modules and scalar center. Each output algebra has dimension linear in the number of vertices and edges of its graph. The two algebras in every output pair have the same Cartan matrix and isomorphic full graded Hochschild cohomology algebras under the cup product. In odd characteristic and characteristic zero every product of positive-degree classes vanishes. In characteristic two the only positive-degree product is an explicit coordinatewise product modulo one line, independent of the graph at fixed vertex and edge counts. The Lie bracket in degree one still distinguishes the output derived classes.

This is an informal result. The reduction uses the earlier MathProof construction carrying a commutative algebra inside the first Hochschild Lie algebra. The new step is a graph encoding for which all Hochschild cup products can be computed uniformly.

## 1. A projective configuration that recovers the graph

Start with a finite simple undirected graph $G$ on $n\ge1$ vertices with $e$ edges. Form $H$ by subdividing every edge once and attaching two private cycles of length five at each original vertex. Each cycle shares exactly that vertex with the rest of $H$. Thus $H$ is triangle-free. Its original vertices have degree at least four, while every other vertex has degree exactly two. Two original vertices came from an edge of $G$ precisely when they have a common neighbor in $H$. In particular, $G$ is recovered from $H$ without supplied vertex labels. Write $r=9n+e$ for the number of vertices of $H$ and $h=10n+2e$ for its number of edges.

Let $V=k^r$ with basis $b_1,\ldots,b_r$. Consider the projective points represented by the vectors
$$
b_i,\qquad b_i+b_j\ \text{for every edge }ij\text{ of } H,\qquad f=\sum_{i=1}^r b_i.
$$
Write their list of representatives as $v_1,\ldots,v_N$ with $N=r+h+1$. These are nonzero and pairwise nonproportional. A projective line containing at least three selected points contains exactly two coordinate points $b_i,b_j$ and the corresponding edge point $b_i+b_j$. To prove this, first note that $f$ cannot lie on the line through two of the other points, because their union of supports has size at most four and $r\ge9$. For two of the remaining points with disjoint supports, a linear combination with both coefficients nonzero has support their union. It can be included only when both are coordinate points and the edge between them is present. If one support is properly contained in the other, the line is a coordinate two-plane and contains just the stated triple. In the remaining case both supports have size two and intersect in one coordinate. A combination with both coefficients nonzero could have support at most two only by cancelling that common coordinate. Another selected point on this support requires an edge joining the other two vertices, contrary to triangle-freeness.

A coordinate point is in at least two of these lines, an edge point in exactly one, and $f$ in none. Thus a projective equivalence between configurations induces an isomorphism of $H$ and hence of $G$. Conversely a graph isomorphism induces a permutation of the basis of $V$ and maps each representative vector, including $f$, exactly onto its corresponding representative.

## 2. A commutative algebra with controlled derivations

Let $U=k^N$ with basis $u_1,\ldots,u_N$. Define the unital commutative algebra
$$
B=k1\oplus U\oplus V,\qquad u_i u_j=0\ (i\ne j),\qquad u_i^2=v_i,\qquad V(U\oplus V)=0.
$$
These formulas are associative because every triple product of elements of $I=U\oplus V$ vanishes. The nilpotent ideal $I$ is the Jacobson radical, $I^2=V$, and the product $I/I^2\times I/I^2\to I^2$ is intrinsic. For $u=\sum c_i u_i$ the rank of multiplication by $u$ on $I/I^2$ is the dimension of the span of the $v_i$ with $c_i\ne0$. Consequently the rank-one lines are precisely the coordinate lines $ku_i$, and their squares recover the projective configuration. This proves $B(G)\cong B(G')$ exactly when $G\cong G'$. The forward implication uses the projective recovery in Section 1, and the reverse uses the exact permutation of representatives.

Let $\delta$ be a $k$-derivation of $B$. Write its value on $u_i$ as $a_i1+\sum_j D_{ji}u_j+F_i$ with $F_i\in V$. In the derivation equation for $u_iu_j=0$ with $i\ne j$, the degree-one component is $a_i u_j+a_j u_i=0$. Thus all $a_i=0$. The degree-two component is $D_{ji}v_j+D_{ij}v_i=0$. Pairwise nonproportionality gives all off-diagonal entries of $D$ zero. Since the $v_i$ span $V$ and $v_i=u_i^2$, we have $\delta(V)\subseteq V$ and $\delta(v_i)=2D_{ii}v_i$. The only endomorphisms of $V$ having all $v_i$ as eigenvectors are scalars. Indeed the coordinate points give a diagonal endomorphism, and the full-support vector $f$ forces equality of the diagonal entries.

In characteristic different from two it follows that
$$
\operatorname{Der}_k(B)=k E\oplus\operatorname{Hom}_k(U,V)
$$
as vector spaces, where $E(1)=0$, $E|_U=1$, and $E|_V=2$. The maps $U\to V$ vanish on $V$ and $k1$. In characteristic two there are $N$ independent diagonal derivations, acting by arbitrary diagonal entries on the $u_i$ and killing $V$, together with the same space $\operatorname{Hom}_k(U,V)$. In both cases every stated map satisfies the derivation equations by the multiplication table. The derivation dimension is $Nr+1$ in characteristic different from two and $Nr+N$ in characteristic two. The diagonal derivations form an abelian subalgebra. The subspace $\operatorname{Hom}_k(U,V)$ is an abelian ideal, since every such map kills $V$. Thus $\operatorname{Der}_k(B)$ is solvable in all characteristics.

## 3. The three-simple algebra and its cochain complex

Put $d=\dim_k B=1+N+r$. Put $m=5$ if $5\ne 0$ in $k$ and $m=6$ otherwise, and put $W=B^m$. Use the three-vertex algebra $A(B)$ with one diagonal copy of $k$ at each vertex and strict corners $B$ from the middle vertex to the last, $W_X=W$ from the first vertex to the middle, and $W_Y=W$ from the first vertex to the last. Its only product between strict corners is
$$
B\otimes_k W_X\longrightarrow W_Y,\qquad b\otimes w\longmapsto bw,
$$
with multiplication coordinatewise on $W$. The structural quantities are independent of the graph at fixed $d,m$. In vertex order $s,x,y$ the matrix of corner dimensions is
$$
\begin{pmatrix}
1&0&0\\
md&1&0\\
md&d&1
\end{pmatrix}.
$$
The strict-corner space $J$ is the radical since it is nilpotent with quotient $k^3$. A central element must be diagonal by commutation with the vertex idempotents. Commutation with the nonzero adjacent corners forces all its scalar entries equal. For left projectives $P_i=Ae_i$, the module $P_y$ is simple and the radical of $P_x$ is $P_y^d$. Multiplying elements of $P_x$ by $W_X$ gives a surjection $P_x\otimes_k W_X\to JP_s$, with kernel $P_y^{(d-1)md}$. Its $x$-component is the identity and its $y$-component is the surjection $B\otimes W_X\to W_Y$. The kernel is nonzero and is contained in the radical of the domain. If $JP_s$ were projective this surjection would split, but a nonzero direct summand of a projective cannot lie inside its radical. The simple at $s$ therefore has projective dimension two, and the other two simples have projective dimension at most one. This proves the asserted global dimension.

An algebra isomorphism $B\cong B'$ gives an algebra isomorphism $A(B)\cong A(B')$ by acting on each corner. For the converse at the derived level, the degree-one cocycle description below and the commutator of derivations identify the first Hochschild Lie algebra as
$$
\mathfrak h(B)=
\left((\mathfrak{gl}_m(B)/kI_m)\oplus B/k1\right)\rtimes\operatorname{Der}_k(B).
$$
The second summand in parentheses is abelian, and derivations act entrywise on the first summand and naturally on the second. This follows by taking commutators in the operators $P=\delta_W+D$ and $R=\delta+L_a$. The trace-zero ideal $T=\mathfrak{sl}_m(B)$ embeds because $m$ is invertible. It is perfect, since $\mathfrak{sl}_m(k)$ is perfect and $T=\mathfrak{sl}_m(k)\otimes_k B$, with $B$ unital. The quotient $\mathfrak h(B)/T$ is an extension of the solvable algebra $\operatorname{Der}_k(B)$ by two abelian copies of $B/k1$. Thus $\mathfrak h(B)/T$ is solvable and $T$ is the stable term of the derived series of $\mathfrak h(B)$. In particular $T$ is intrinsic and this characterization works with constant $m$, independent of $d$.

The centroid of $T$, the ring of linear maps commuting with the bracket in each position, is $B$. Indeed $\mathfrak{sl}_m(k)$ is absolutely simple for $m\ge 5$ with $m$ invertible in $k$. By scalar extension and Schur's lemma, every endomorphism of its adjoint representation is scalar. Therefore a centroid map of $T$ commuting with the constant subalgebra has the form $\mathrm{id}\otimes F$ for a $k$-linear map $F:B\to B$. Commutation with the bracket gives $F(ab)=F(a)b$, so the map is multiplication by $F(1)$. This identifies centroid multiplication with the multiplication of $B$. The argument so far applies to every finite-dimensional commutative unital $B$ of dimension at least two for which $\operatorname{Der}_k(B)$ is solvable.

For finite-dimensional algebras of finite global dimension over $k$, a $k$-linear derived equivalence yields an equivalence on the perfect categories. Rickard's tilting theorem supplies a standard derived Morita equivalence, under which Keller's invariance theorem preserves the Gerstenhaber bracket. The preceding Lie ideal and centroid consequently recover $B$ up to isomorphism from the derived category, proving the required converse. [Rickard, Morita theory for derived categories](https://doi.org/10.1112/jlms/s2-39.3.436) · [Keller, derived invariance of higher Hochschild structure](https://webusers.imj-prg.fr/~bernhard.keller/publ/dih.pdf)

For the cup product calculation take the separable subalgebra $S=k^3$ of diagonal elements and its bimodule complement $J$ of strict corners. The $S$-relative normalized bar resolution computes $HH^*(A(B))$ and its cup product. One can see the comparison directly from the bar resolution $A\otimes_S J^{\otimes_S q}\otimes_S A$. Its terms are projective $A$-bimodules because $S^e$ is a product of copies of $k$, and the normalized relative bar contraction gives exactness. The bar diagonal gives the ordinary concatenation formula for cup products. The cochain groups here are
$$
C^0=k^3,\qquad
C^1=\operatorname{End}_k(B)\oplus\operatorname{End}_k(W)^2,\qquad
C^2=\operatorname{Hom}_k(B\otimes_k W,W),\qquad
C^{\ge3}=0.
$$
Indeed the only composable pair of strict corners is $B,W_X$, and there is no composable triple. For a one-cochain $(R,P,Q)$ on $B,W_X,W_Y$, respectively, the boundary evaluated at $(b,w)$ is
$$
  (d_1(R,P,Q))(b,w)=bP(w)-Q(bw)+R(b)w.
$$
Hence the degree-one cocycles have
$$
  R(b)=ab+\delta(b),\quad P=\delta_W+D,\quad Q=P+L_a
$$
for $a\in B$, $\delta\in\operatorname{Der}_k(B)$, and $D\in\operatorname{End}_B(W)$. Here $L_a$ means multiplication by $a$, and $\delta_W$ applies the derivation in each copy of $B$. For completeness, at $b=1$ the cocycle equation gives $a=R(1)$, $Q=P+L_a$, and its remaining equations give $[P,L_b]=L_{R(b)-ab}$. Taking the commutator with $L_bL_c$ shows that $\delta(b)=R(b)-ab$ is a derivation. Subtracting $\delta_W$ from $P$ leaves a $B$-linear map. Degree-zero boundaries vary the scalar parts of $a,D$ independently, so have dimension two and have zero $\delta$-part. The Hochschild dimensions are
$$
 \dim HH^0=1,\quad
 \dim HH^1=d+m^2d+\dim\operatorname{Der}_k(B)-2,\quad
 \dim HH^2=d(md)^2-d^2-2(md)^2+\dim HH^1+2.
$$
They are independent of the graph at fixed $n,e$ and field. [Gerstenhaber–Schack, relative Hochschild cohomology via separable subalgebras](https://www2.math.upenn.edu/~mgersten/papers/Barrfest.pdf)

## 4. Cup product in characteristic different from two

The cup of two degree-one cocycles evaluated at $(b,w)$ is $R_1(b)P_2(w)$. The term $a_1 b P_2(w)$ is a boundary, using $P=L_{a_1}P_2$, $Q=R=0$. The term $\delta_1(b)D_2(w)$ is also a boundary, using $P=Q=-\delta_{1,W}D_2$, $R=0$, because $D_2$ commutes with all multiplications. The only remaining term is $\delta_1(b)\delta_{2,W}(w)$.

Any $U\to V$ component of either derivation contributes zero here, since the images of the derivations lie in $I$ and $VI=0$. The product therefore reduces to a scalar multiple of $E(b)E_W(w)$. This is a boundary, as seen by setting $P=Q=-E_W^2/2$, $R=-E^2/2$ and using the derivation rule twice. Thus all products of positive-degree classes are zero. Products involving degree-two classes already land beyond the top nonzero cochain degree.

## 5. Cup product in characteristic two

For the characteristic-two diagonal derivations with coefficient vectors $(c_i)$, $(d_i)$, the remaining term from Section 4 is $\sum_i c_i d_i F_i$, where $F_i(b,w)$ multiplies the $u_i$-coefficient of $b$ by the $u_i$-coefficient in each coordinate of $w$ and returns the corresponding multiple of $v_i$ in that coordinate. The $U\to V$ components still contribute zero. The classes of the $F_i$ have exactly the relation space $k(1,\ldots,1)$.

To see necessity, suppose $\sum_i\lambda_i F_i=d_1(R,P,Q)$. Restrict the input and output to one copy of $B$ in $W$, so regard the corresponding blocks of $P,Q$ as maps from $B$ to itself. The proposed cup combination vanishes whenever $b=1$ or $w=1$. The first condition gives $Q=P+L_{R(1)}$, and the second gives $R(b)=P(b)-bP(1)+R(1)b$. Therefore the boundary on that copy is
$$
 bP(w)-P(bw)+P(b)w-P(1)bw.
$$
At $b=w=u_i$ the first and third terms cancel in characteristic two. Hence $P(v_i)+P(1)v_i=\lambda_i v_i$, using that minus equals plus. The $v_i$ span $V$. It follows that $P|_V$ is an endomorphism of $V$ and satisfies the specified eigenvector equations after adding the restriction of multiplication by $P(1)$. The coordinate points and $f$ then give equality of all $\lambda_i$. Conversely any constant vector of coefficients is realized by taking $P=Q$ to act by that scalar on $V$ in every copy and by zero on $k1\oplus U$, and taking $R$ to act by the same rule on $B$. This proves the relation assertion.

Thus the whole positive-degree cup structure has a uniform description. Split $HH^1$ as its diagonal derivation quotient $k^N$ and an arbitrary linear complement on which all positive-degree products vanish. Split $HH^2$ as the product span $k^N/k(1,\ldots,1)$ and an arbitrary complement. The product between quotient vectors is
$$
(c_i)\smile(d_i)=[(c_i d_i)].
$$
All these splittings exist over the input field and the quotient descriptions specify the cohomology algebra up to isomorphism. Its dimensions and multiplication depend only on $n,e$ and the field.

## 6. Reduction and scope

The graph isomorphism reduction sends $G$ to the dense multiplication table of $A(B(G))$. If the two input graphs have different vertex or edge counts, send them to the fixed negative pair given by a four-vertex path and a four-vertex star. These graphs have identical vertex and edge counts, so their outputs satisfy the identical-cup promise. An empty matching pair may be handled by a fixed positive pair. Otherwise Section 1 proves the graph recovery and the prior construction gives the derived-class equivalence. The split basic output has $3+d+2md=O(n+e)$ dimensions. Its coefficients are given directly by copies of input incidence entries, zero and one, so the reduction runs in polynomial time in the usual dense model over every field. In particular it requires no Hochschild calculation as part of the reduction. The calculations here certify the output promise.

There are in particular $2^{\Omega(n^2)}$ pairwise nonderived-equivalent members of this family with one and the same Cartan matrix and graded Hochschild cup algebra for some fixed edge count at each sufficiently large $n$. Among the $2^{\binom n2}$ labelled graphs on $n$ vertices, some edge count has at least $2^{\binom n2}/(\binom n2+1)$ graphs. Each isomorphism class accounts for at most $n!$ of them, and the construction preserves and reflects graph isomorphism.


The distinction is between the full graded Hochschild algebra with its cup product and its enhancement by the Gerstenhaber bracket. The cup algebra is the same on each fixed-size output family, while the bracket in degree one suffices for the encoded graph comparison. This proves Graph Isomorphism hardness on that promise, with no tensor-isomorphism hardness claim for the equal-cup promise. The bar machinery and the bracket invariance are standard. A focused literature search located earlier vanishing results for triangular monomial algebras and general triangular extension sequences. Publication priority for the explicit equal-cup GI-hardness family remains unverified. [Artenstein–Letz–Oswald–Solotar, Hochschild cup products for monomial algebras](https://arxiv.org/abs/2312.14699) · [Cibils–Marcos–Redondo–Solotar, split algebras and one-point extensions](https://arxiv.org/abs/math/0102194) · [Keller, derived invariance of higher Hochschild structure](https://webusers.imj-prg.fr/~bernhard.keller/publ/dih.pdf)
