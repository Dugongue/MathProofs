# Compiling arbitrary tensor degenerations into one symmetric balanced quartic

AI-assisted informal proof. All orbit closures in this note are Zariski closures over $\mathbb C$. The inputs can be given in rational coordinates and the reductions use exact rational arithmetic.

## Results

**Theorem.** For every $d\ge3$ and ordered format $(V_1,\ldots,V_d)$ with $1\le\dim V_i\le n$, $n\ge2$, there is an affine map with rational coefficients
$$
\Phi:\bigotimes_{i=1}^d V_i\longrightarrow \mathrm{Sym}^2(W)\otimes\mathrm{Sym}^2(W^*)
$$
with $\dim W\le13n^{\lceil d/4\rceil}$. Write $H=\prod_i\mathrm{GL}(V_i)$ and $G=\mathrm{GL}(W)$. The map preserves and reflects both ordinary orbit equality and directed orbit closure containment. For every $x$, each $G$-orbit in $\overline{G\Phi(x)}$ contains $\Phi(y)$ for some $y\in\overline{Hx}$, and this $y$ is unique up to $H$-orbit. Thus the whole degeneration order below $x$ is isomorphic to that below $\Phi(x)$. The map is uniformly computable in polynomial bit time on dense rational inputs, including when $d$ varies.

All images of one format have the same closed orbit in their orbit closures, namely $G\Phi(0)$. Consequently every polynomial $G$-invariant agrees on the entire image of a format. Nevertheless, directed orbit closure containment of a pair of symmetric balanced quartics is NP-hard over rational inputs, even under the promise that their closures contain the same closed orbit. This last statement already uses the construction for $d=3$.

For equal input dimensions $n$ and fixed $d\ge3$, any polynomial map into a symmetric balanced quartic space that preserves and reflects orbit equality requires $\dim W=\Omega(n^{d/4})$. In particular the exponent of the construction is optimal when $4\mid d$.

## 1. Closure over a closed marker

Let an algebraic group $J$ act on a variety $Z$, let $p:Z\to B$ be an equivariant morphism, and fix a point $b\in B$ whose orbit is closed. Suppose the map $J\to Jb$ has regular sections on a Zariski open cover. Put $K=J_b$. For any $z\in p^{-1}(b)$,
$$
\overline{Jz}\cap p^{-1}(b)=\overline{Kz}^{\,p^{-1}(b)}.
$$
Moreover every orbit in $\overline{Jz}$ meets this fiber, and two points in the fiber are in the same $J$-orbit exactly when they are in the same $K$-orbit.

Indeed, the orbit closure stays in the closed subvariety $p^{-1}(Jb)$. Over a section $s:U\to J$, the preimage of $U$ is isomorphic to $U\times p^{-1}(b)$ by $(u,v)\mapsto s(u)v$. The orbit corresponds to $U\times Kz$, whose closure in that open set is $U\times\overline{Kz}$. This product-closure identity follows from the density of $Kz$ in its closure or by restricting a closed set to each fixed first coordinate. This proves the fiber assertion. Any orbit in the closure reaches the fiber by applying $s(u)^{-1}$, and any transporter between two points in the fiber fixes $b$.

Below the first group uses a spectral section and the second has a global regular section, both explicit. No nonconstructive assertion about arbitrary homogeneous spaces having Zariski sections is used.

## 2. Four trees and the spectral marker

Partition the input modes into four consecutive groups of sizes differing by at most one, with an empty group replaced by a one-dimensional dummy mode. Let the leaves in the first two groups be the spaces $V_i$ and those in the last two groups the dual spaces $V_i^*$. Build a prefix product tree for each group. Each internal node $Z$ is a fresh named vector space canonically identified with the tensor product $X\otimes Y$ of its two children. Distinct named spaces are separate direct summands, even if they have the same dimension. Write $R_1,R_2,R_3,R_4$ for the four roots. Put $W$ equal to the direct sum of every named space plus one extra line $L=\mathbb C\ell$.

Use the usual coordinate identification of $\mathrm{Sym}^2(W)\otimes\mathrm{Sym}^2(W^*)$ with those operators on $W\otimes W$ which restrict to the symmetric part and vanish on the alternating part. Let $P=(I+S)/2$ be the symmetric projector, where $S$ exchanges the two factors. Let $D$ act on each named block and on $L$ by a distinct fixed rational eigenvalue. The first marker is
$$
M(D)=(D\otimes I+I\otimes D)P.
$$
Write $N=\dim W$. Partial trace over the second factor gives
$$
\operatorname{Tr}_2 M(D)=\big((N+2)D+(\operatorname{tr}D)I\big)/2.
$$
The two terms involving $S$ each have partial trace $D$, and the identity terms give $ND$ and $(\operatorname{tr}D)I$. The equivariant affine map
$$
p(A)=\frac{2\operatorname{Tr}_2 A-(\operatorname{tr}D)I}{N+2}
$$
recovers $D$ when applied to $M(D)$ plus any operator whose partial trace vanishes. Equivariance of the constant term follows because it is scalar.

The conjugacy orbit of $D$ is closed. It is specified by the fixed characteristic polynomial and by the annihilation equation given by the product of the distinct eigenvalue factors. Those two conditions force exactly the prescribed eigenspace multiplicities and semisimplicity. Its stabilizer $K$ is the product of the general linear groups on all blocks. For any $D'$ in the orbit, project standard basis columns into its eigenspaces using the fixed interpolation polynomials in $D'$. Choose enough projected columns to make a basis in each eigenspace. On the open set where the chosen determinant is nonzero, the matrix of these columns is a regular section carrying $D$ to $D'$. The open sets cover the orbit.

For distinct blocks $A,B\subset W$, the summand of $\mathrm{Sym}^2(W)$ with one entry from each is canonically $A\otimes B$, via $a\otimes b\mapsto a\otimes b+b\otimes a$. Use these identifications for all off-diagonal operator blocks below, with inverse coordinate normalizations on the symmetric part. If the two source colors are disjoint from the two target colors, its partial trace vanishes since the traced primal and dual legs always have different colors.

## 3. The inverse product markers

For each internal node $Z=X\otimes Y$, put a fixed pair of inverse maps
$$
A^0_Z:Z\otimes L\longrightarrow X\otimes Y,
\qquad B^0_Z=(A^0_Z)^{-1}
$$
into the corresponding symmetric operator blocks. The first map sends $z\otimes\ell$ to the tensor product vector represented by $z$. All four colors of each pair are distinct. Channels for different nodes are disjoint since each parent is a fresh named space and each child has just one parent. Define $C$ to be their sum. The partial trace of $C$ vanishes.

In the spectral fiber $p^{-1}(D)$, take the equivariant map to the tuple of these designated operator blocks. The spectral marker has zero extraction to these blocks because it acts as a scalar on each unordered pair of eigenspaces and preserves that pair. The $K$-orbit of the inverse tuple $c_0=(A_Z^0,B_Z^0)_Z$ is exactly the affine closed set defined by $A_ZB_Z=I$ and $B_ZA_Z=I$ for every node. To prove transitivity, identify the line by $\ell$, take all leaf changes to be the identity and take $g_L=1$. Given the desired inverse pairs $A_Z,B_Z$, set recursively
$$
g_Z=B_Z(g_X\otimes g_Y)A_Z^0.
$$
It follows that $(g_X\otimes g_Y)A_Z^0g_Z^{-1}=A_Z$ and the inverse map transforms to $B_Z$. The recursion is polynomial on the coordinates of the inverse tuple and gives a global regular section. If there are no internal nodes this is the constant section on a one-point tuple space.

The stabilizer $K_0$ of the inverse tuple is also explicit. Write $g_L=\lambda\in\mathbb C^*$. The leaves and $\lambda$ can be chosen arbitrarily, and the internal action is then forced by
$$
g_Z=\lambda^{-1}(g_X\otimes g_Y)
$$
in the specified prefix identifications. At a root with $k$ leaves the induced map is $\lambda^{-(k-1)}$ times the tensor product of its leaf maps.

## 4. Payload and exact orbit correspondence

The linear inclusion $F$ of the tensor data is the operator block
$$
R_3\otimes R_4\longrightarrow R_1\otimes R_2
$$
under the natural reshaping of $\bigotimes_i V_i$, using $(V_i^*)^*\cong V_i$ in the last two groups. The dummy leaf, if needed, is filled with its basis vector in the corresponding dual-root coordinate. All four roots are distinct and none is $L$. Its channel is thus different from every product marker channel, and its partial trace is zero.

Set $\Phi(x)=M(D)+C+F(x)$. The first extraction is $D$ and the second tuple is $c_0$. The affine subspace $M(D)+C+\operatorname{im}F$ of their common fiber is closed and $K_0$-invariant. On its data block $K_0$ acts by the source leaf action and an additional scalar coming from the line and any dummy leaf. The leaf actions in dual groups become arbitrary primal actions by inverse transpose. Any additional nonzero scalar can be absorbed into the scalar part of one of the original leaf actions. Conversely every source action occurs by taking $\lambda=1$ and the dummy identity. Thus the $K_0$-orbits on this subspace are exactly the transported $H$-orbits, with the same closures there.

Apply the closed-marker statement first to $p$ and then to the inverse tuple inside $p^{-1}(D)$. The fiber of the full target orbit closure over $(D,c_0)$ is precisely $\Phi(\overline{Hx})$. Every target orbit in it corresponds to exactly one source orbit. Every target orbit in the full target closure meets it, since one may move the first marker back by $G$ and then move the second back by $K$. The same fiber argument applied to any $y\in\overline{Hx}$ preserves and reflects its degeneration order to all lower points. This proves the entire partially ordered set assertion, not just one direction of containment.

## 5. Complexity and consequences

For a group of $k\ge1$ leaves, the sum of their dimensions is at most $kn\le n^k$. The internal prefixes contribute at most $\sum_{j=2}^k n^j\le2n^k$. Empty groups have one dummy dimension. Adding the line gives $N\le13n^{\lceil d/4\rceil}$. If the actual dense input coordinate count is $P_0=\prod_i \dim V_i$, every leaf and prefix has dimension at most $P_0$. Thus $N=O(dP_0)$ even in imbalanced formats. The output has at most $N^4$ ordered coordinates. The fixed basis maps, spectral tags, and copies of input entries can be written in polynomial bit time. Distinct integer eigenvalues at most $O(d)$ suffice. The symmetric basis and dual identifications add only rational factors of bounded bit length. The sections in the proof are used for correctness, not computed by the reduction.

The group $H$ can scale one mode, so $0\in\overline{Hx}$ for every $x$. The same fiber proof for zero shows $G\Phi(0)$ is closed. Its inclusion in every image closure proves equality of all target invariant values. Since $G$ is reductive, it is the unique closed orbit in each image closure. The NP-hardness then follows from order-three orbit closure containment of Bläser, Ikenmeyer, Lysikov, Pandey and Schreyer, by applying $\Phi$ to both input tensors of the same shape. Their hardness uses rational inputs, and the reduction here applies without any extra tensor promise. [Source, Theorem 8.9 and Corollary 8.10](https://arxiv.org/html/1911.02534#S8.SS2).

The local product charts in the proof also identify the germ of $\overline{G\Phi(x)}$ along each orbit with the source germ after adjoining smooth factors. Indeed, the first factor is an open set of the conjugacy orbit of $D$, and the second is the space of inverse pairs, which is a product of general linear groups. Thus $\Phi(y)$ is a smooth point of the target orbit closure exactly when $y$ is a smooth point of the source closure. Orbit codimensions inside the respective closures also agree, since the same two factors occur in the charts for the orbit and its ambient closure.

For the side lower bound, any polynomial map reflecting orbit equality has every nonempty fiber contained in one source orbit. In the equal-side format the source dimension is $n^d$ and every orbit has dimension at most $dn^2$. By the fiber dimension theorem, the image closure has dimension at least $n^d-dn^2$. The ambient space of the output has dimension $(N(N+1)/2)^2$. Hence $N=\Omega(n^{d/4})$ for fixed $d\ge3$ and increasing $n$. Reflection of directed containment alone also suffices when preservation holds: two group orbits whose points belong to each other's closures coincide, because each orbit is open dense in its own closure.

## Context and scope

The four product trees adapt the prefix-space mechanism of the existing balanced tensor-order reduction. The inverse-arrow comparison and semisimple spectral charts extend the existing closed-marker proofs for balanced orbit-closure intersection, including the single symmetric quartic. Lysikov and Walter's published tensor-tuple normalization is designed for intersection, which collapses every orbit of each ordinary tensor format into one closure-equivalence class because of zero. The claim here concerns the whole directed degeneration relation in precisely that situation. [Lysikov–Walter](https://arxiv.org/html/2411.04639v2). The earlier theorem for symmetric quartics established TOCI-completeness for intersection. Here the new hardness conclusion is for directed containment and relies on the published three-tensor hardness. This proof gives no reduction for arbitrary special-linear orbit-closure intersection. The exact combination and quantitative bound have not been checked exhaustively for publication priority. No Lean certificate is claimed.
