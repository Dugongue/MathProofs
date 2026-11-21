# Four orbit-closure tests for the symmetric final-digit tensor

Let $k$ be a finite field of characteristic $p$ and $K$ an algebraic closure. Consider two ring-scheme models over $k$. In equal characteristic, use $D\mapsto R\otimes_k D$ for a finite local $k$-algebra $R$ with residue $k$, nonzero maximal ideal $\mathfrak m$, and a nonzero socle value $s\in\operatorname{Ann}_R(\mathfrak m)$ as in the original construction. In mixed characteristic, use $D\mapsto W_e(D)$ for $e\geq2$. In particular this includes $\mathbb Z/p^e\mathbb Z=W_e(\mathbb F_p)$ on the original finite-field points. All closures below are taken geometrically over $K$, with the tensor scheme written in the affine ring coordinates of one of these models.

For an ordinary trilinear form $t$ of positive format $(a,b,c)$, write $F_t$ for the fully symmetric final-digit tensor from the fixed-slice construction, recalling its ingredients below. The tensor $F_t$ has the same prescribed invertible slice for every $t$ of the format. The four acting groups are independent $\operatorname{GL}^3$, independent $\operatorname{SL}^3$, diagonal $\operatorname{GL}$, and diagonal $\operatorname{SL}$, over the indicated ring-scheme model.

**Theorem.** For all $t,t'$ in the original format and each of the four groups $\mathcal G$,
$$
 t'\in\overline{(\operatorname{GL}_a\times\operatorname{GL}_b\times
                         \operatorname{GL}_c)t}
 \quad\Longleftrightarrow\quad
 F_{t'}\in\overline{\mathcal G F_t}.
$$
The right side is in the full ambient affine tensor scheme, even for the independent-mode action. In equal characteristic, one may equivalently test the projective orbit-closure containment of $[F_{t'}]$ in that of $[F_t]$ for any of the four groups. These are comparisons at constructed endpoints. They allow arbitrary drops in the support ranks of $t'$.

The main step is a degeneration theorem for the intermediate symmetric field tensor. It uses determinant factors to keep the marker lines distinct in a limit and polynomial idempotents to recover the three ordered roles. This deals with a limit where the ranks of the input contractions shrink.

## The symmetric marker form

Let $X_1,X_2,X_3$ be the argument spaces of dimensions $a,b,c$, and put $n=a+b+c$, $M=n+7$, and $h_i=2^i M$ for $1\leq i\leq3$. The space $H_i$ is split symmetric of dimension $h_i$, with the direct sum of the two-by-two swap pairings. Let
$$
 O_i=X_i\oplus X_i^*\oplus H_i,\qquad
 K_0=\bigoplus_i O_i,\qquad
 L=K_0\oplus\bigoplus_i Kz_i .
$$
The symmetric trilinear form $C_t$ on $L$ has the restriction $t$ on $X_1\times X_2\times X_3$ and $C_t(z_i,-,-)=\beta_i$ on $O_i\times O_i$, along with their symmetric copies. Here $\beta_i$ is the evaluation-plus-split pairing on $O_i$. The other restrictions to ordered summands vanish.

The rank of $C_t(u,-,-)$ is at most $n+6$ when $u\in K_0$. Indeed its restriction to $K_0^2$ uses only the $X_i$, and the three additional coordinates contribute at most six to the rank. If $u$ has any nonzero $z_i$-coefficient, its restriction to $H_i^2$ has rank $h_i>n+6$. Thus the locus of small slice rank is exactly $K_0$ on geometric points. This also proves that $C_t$ is concise in its single space $L$. Any contraction-radical vector belongs to $K_0$, and pairing with $z_i$ and $O_i$ forces its $O_i$-component to vanish.

Write $\alpha_i$ for the $z_i$-coordinate as a functional on $L/K_0$. The determinant of the slice restricted to $K_0^2$, as a polynomial in $u$, is a nonzero constant times
$$
 \prod_{i=1}^3 \alpha_i(u)^{h_i+2\dim X_i}.
$$
To compute it, the $H_i$-blocks contribute nonzero constants times $\alpha_i^{h_i}$. On $(\bigoplus_i X_i)\oplus(\bigoplus_i X_i^*)$, the block form is
$\left(\begin{smallmatrix}P_u&A\\A&0\end{smallmatrix}\right)$, where $A$ is the block diagonal matrix with scalars $\alpha_i$. Exchanging the two column groups makes the matrix block triangular, and its determinant is $(-1)^n\det(A)^2$. In particular the formula does not depend on the $X_i$-data matrix $P_u$ or on the choice of a lift of a marker vector modulo $K_0$. The three exponents are distinct by the sizes $h_i$.

## Keeping the three roles through a degeneration

Suppose $C_{t'}$ is in the geometric diagonal $\operatorname{GL}(L)$ orbit closure of $C_t$. Use an integral curve and its normalization to get a DVR $\mathcal O$ with residue field $K$ and a family $C$ whose generic fiber is obtained from $C_t$ by an actual change of basis over the fraction field and whose special fiber is $C_{t'}$. One way to ensure the generic change of basis is to close the graph of the orbit map in $\mathbb P(K\oplus\operatorname{End}(L))\times\operatorname{SymTril}(L)$, where $\operatorname{SymTril}(L)$ denotes the space of symmetric trilinear forms. The projection is proper, so choose a point of the graph closure above $C_{t'}$, then an integral curve through that point with generic point in the graph. In an affine neighborhood use finite Noether normalization and choose a line through the image point not contained in the image of the graph boundary. This boundary has smaller dimension, and its image under the finite map is closed and has smaller dimension. A component of the inverse image through the chosen point has dimension one by finiteness and the principal ideal theorem, and therefore dominates the line. Normalizing the curve gives the DVR. When the target is already in the orbit a constant family suffices.

Transport $K_0$ in the generic fiber and saturate its lattice in $L_{\mathcal O}$. The result $\mathcal K$ is a direct summand of the same rank. The small-slice-rank minors vanish on its generic vectors and hence on the subbundle, so its reduction is contained in the small-rank locus of $C_{t'}$. The ranks agree, hence it reduces to the target $K_0$. Now take the slice determinant on $\mathcal K^2$ in a basis. Generically the three linear factors are forms on $L/\mathcal K$, and choose primitive integral representatives for them. Their product is primitive because the residue polynomial ring is a domain. The scalar in the determinant factorization is a unit, since the special determinant is nonzero. The three reduced factor lines cannot collide, because the target determinant has three distinct factors. By their exponents, each factor reduces to the corresponding labeled target factor, with no permutation. Thus the primitive factors form a basis of $(L_{\mathcal O}/\mathcal K)^*$.

Take lifts $u_1,u_2,u_3$ of the basis dual to these primitive factors. In the generic and special displayed coordinates they have the form $u_i=\gamma_i z_i+v_i$ with $\gamma_i\ne0$ and $v_i\in K_0$. Let $B_i=C(u_i,-,-)|_{\mathcal K^2}$, and put $B=\sum_i B_i$. Then $B$ is invertible over $\mathcal O$, by the determinant formula or its nonzero residue. Define $A_i=B^{-1}B_i$ as an endomorphism of $\mathcal K$.

To evaluate this endomorphism in the generic and special coordinates, let $E_i$ be the projection onto $O_i$. For $\beta=\bigoplus_i\gamma_i\beta_i$, a data term supported on $(\bigoplus X_i)^2$ becomes, after applying $\beta^{-1}$, an element of
$$
 \mathcal N=\{N:K_0\to K_0:\ N(X^*\oplus H)=0,\
                                    \operatorname{im}N\subset X^*\},
$$
where $X^*=\bigoplus X_i^*$ and $H=\bigoplus H_i$. Elements of $\mathcal N$ compose pairwise to zero, and left or right composition with $E_i$ preserves $\mathcal N$. Consequently $B^{-1}B_i=E_i+N_i$ for some $N_i\in\mathcal N$, by the inverse of $1+N$. In particular $A_i(1-A_i)$ has square zero. The polynomial
$$
 P_i=3 A_i^2-2 A_i^3
$$
is an idempotent, because for $P(x)=3x^2-2x^3$, the polynomial $P^2-P$ is divisible over the integers by $x^2(1-x)^2$. This argument holds in characteristic two and three. The identity extends from the fraction field to the DVR. In either displayed fiber $P_i$ differs from $E_i$ by an element of $\mathcal N$. Their images have equal dimensions, for instance they are conjugate by the invertible map $P_iE_i+(1-P_i)(1-E_i)$, the identity plus a square-zero operator. The projection of $\operatorname{im}P_i$ on $\bigoplus_j X_j$ is exactly $X_i$.

The image modules $\operatorname{im}P_i$ over the DVR are free summands of ranks $\dim O_i$. Restrict $C$ to the product of these three modules. It gives a family of ordinary tensors whose generic and special fibers are $t$ and $t'$ padded by unused coordinates, respectively. Indeed, with all arguments in $K_0$ the form only sees their projections on the $X_i$, which were just recovered. No independence of the three idempotent images as subspaces of $\mathcal K$ is needed to take their ordered product.

Padding can be canceled in this type of family even when the contraction ranks drop. In each generic argument choose a subspace of unused directions of exactly the padding dimension and saturate it over the DVR. All corresponding contractions vanish over the DVR since they vanish generically. The family therefore descends to the fixed original three quotient ranks. In the special fiber the chosen subspaces lie in the contraction radicals. The supported tensor in the quotient is still the supported tensor of $t'$, and extending bases on the unused directions gives exact equivalence in the nominal original format. This proves $t'\in\overline{(\prod_i\operatorname{GL}(X_i))t}$.

We will also use cancellation for simultaneously padded symmetric forms. When both cores are concise, saturate their common generic contraction-radical dimension. Its reduction is contained in the target radical of that same dimension, so quotienting recovers a family in the core dimension. This applies to $C_t,C_{t'}$ because both are concise.

## A regular extractor on the ambient tensor orbit

In the coefficient ring model let $i(u)$ denote the final additive coordinate, equal to $s u$ in the equal-characteristic model and $V^{e-1}(u)$ for Witt vectors. Its image is a square-zero ideal. Multiplication by an element of residue $r$ acts by $r$ in equal characteristic and by $r^{p^{e-1}}$ for Witt vectors. The latter is the iterated projection formula for Verschiebung. These ring operations are polynomial in the affine ring coordinates, and inverse on the unit locus is regular since the residue kernel is nilpotent. [Hazewinkel, Witt vectors, Part 1](https://arxiv.org/abs/0804.3888) · [Bertapelle and González-Avilés, The Greenberg functor revisited](https://arxiv.org/abs/1311.0051)

Recall the anchor algebra $A_t$ with unit and augmentation ideal
$$
 I=L\oplus L^*\oplus Q\oplus \mathcal R z .
$$
Here the displayed vector spaces mean their free lifts, $Q$ has rank zero or one, and its rank makes $N=\operatorname{rank}A_t$ prime to $p$. Inside $I$, the product of two elements of $L$ is the image of the pullback of $C_t$ in $i(L^*)$, the evaluation product between $L$ and $L^*$ is valued in $z$, and the optional generator of $Q$ has square $z$. All other products vanish. The left-associated triple product on $I$, read in the coordinate of $z$, is exactly the padded $C_t$ in the final coordinate. Left multiplication by every element of $I$ has trace zero, and the augmentation is the normalized trace. The fixed functional $\lambda$ reads the coefficient of $z$; its perfect pairing $G(x,y)=\lambda(xy)$ has the same matrix for every input. The output is $F_t(x,y,w)=\lambda(xyw)$.

Use this fixed $G$ to turn any candidate trilinear form into a bimap $T$ with values in the fixed module, so at $F_t$ it equals the multiplication on $A_t$. Independent basis changes still give the ordinary three-mode action on the bimaps. On the open where $A_T(x)=T(x,1)$ and $B_T(y)=T(1,y)$ are invertible, define
$$
 \nu_T(x,y)=T(A_T^{-1}x,B_T^{-1}y).
$$
It is unital with unit $u=T(1,1)$. Restrict further to the open where the first coefficient of $u$ is a unit. All the constructed endpoints satisfy these opens. Write $\epsilon_T(x)=\operatorname{tr}L_x^{\nu_T}/N$. Since $\epsilon_T(u)=1$, the frame
$$
 (u,\ b_1-\epsilon_T(b_1)u,\ \ldots,\ b_{N-1}-\epsilon_T(b_{N-1})u)
$$
is invertible, with $b_i$ the original nonunit basis vectors. Define a regular field coefficient map on this chart by computing left-associated triple products of the marked nonunit vectors, selecting their fixed $z$-coordinate in this frame, and reading its final coordinate. At the endpoint $F_{t'}$ it returns exactly $C_{t'}$ padded by zeros.

On the ordinary tensor orbit of $F_t$, the normalized law $\nu_T$ is a unital isotope of the associative source and hence is isomorphic to it. This conclusion does not assume associativity of the target in advance. If $h(xy)=f(x)g(y)$ and the target identity has preimages $a,b$ under $f,g$, then $h(ay)=g(y)$ and $h(xb)=f(x)$. The source multiplications by $a,b$ are invertible, so $a,b$ are units. In source coordinates via $h$, the target product is $x b^{-1}a^{-1}y$, isomorphic to the source. The argument is valid over the coefficient ring. Therefore on the normalized orbit the trace frame marks the true augmentation ideal. The original triple products land in $i(K)z$. Under an algebra isomorphism, taking the chosen coordinate on its transported socle generator gives a scalar, and taking the final coefficient converts any coefficient multipliers into their residues, with the stated Witt power when applicable. Thus the regular extractor takes each point of the open orbit to a field basis transform of the padded $C_t$ times a scalar. If the scalar vanishes it gives zero. If it is nonzero, it can be absorbed into diagonal basis change over $K$, by a cube root. In either case the extracted form belongs to the closed ordinary diagonal orbit closure of the padded $C_t$.

It follows by regularity that an ambient three-mode degeneration to $F_{t'}$ induces a diagonal field degeneration of the padded intermediate forms. Cancel symmetric padding and apply the determinant and idempotent argument. This proves the reverse implication from the largest group in the theorem.

## Forward degenerations and projective tests

An ordinary field transporter acts on all $X_i$ by its three maps, on $X_i^*$ contragrediently, and fixes $H_i,z_i$. This carries the intermediate forms by an exact isometry. It extends to the anchor algebra by lifting the map on $L$, taking the inverse transpose on $L^*$, and fixing the unit, $Q$, and $z$. When the final coordinate is Witt, choose the leading coordinates of the lift to be the entrywise inverse Frobenius of those of the field isometry. This is possible at the geometric points. The lift preserves all products by the final-ideal multiplication rule. It preserves $\lambda$ and has determinant one by the two dual blocks. Consequently the polynomial map $t\mapsto F_t$ carries the whole source orbit to the diagonal special-linear orbit and carries its closure into that orbit's closure. This gives the forward implication for the smallest group, and proves all four tests.

If the original Witt convention uses $p^{e-1}$ times lifted coefficients, this raises the parameters to the $p^{e-1}$-th powers in the final coordinate. The marker and pairing coefficients lie in the prime field. Entrywise Frobenius takes the displayed algebraic orbits to the orbits of their Frobenius images and is a homeomorphism on geometric closures. Thus the equivalence also holds in that convention. On $\mathbb F_p$ it is identical.

For the projective assertion, every constructed tensor is nonzero by its invertible slice. The independent general-linear orbit in affine ring coordinates is stable under nonzero geometric scalar dilation in equal characteristic. In Witt coordinates, ordinary coordinatewise scalar dilation need not agree with multiplication by a scalar of the ring model. The corresponding projective statement is therefore taken in equal characteristic with its ordinary projective tensor space. There the closure of the projective independent general-linear orbit is the projectivization of its affine closure away from zero. Each of the four projective orbits lies in that largest projective orbit, and each relevant affine inclusion already follows from the diagonal special-linear case. This proves the equivalence of the projective tests in equal characteristic.

## Relation to the literature and scope

Bläser and Lysikov's unital normalization for a binding tensor and their comparison of field tensor and algebra degeneration are the closest precedents for the first step of the ambient extraction. The fixed trace and final ideal then extract the intermediate symmetric law on the ring-scheme chart. The separate marker determinant and idempotent calculations are what recover the ordered input tensor in a limit. The determinant exponents need not be units modulo $p$, since the proof tracks factors over a DVR instead of differentiating their coefficients. [Bläser and Lysikov, On Degeneration of Tensors and Algebras, Theorem 3.2 and Lemma 3.5](https://doi.org/10.4230/LIPIcs.MFCS.2016.19)

The starting symmetric final-digit reduction concerns exact isomorphisms. Jagiełła and Jelisiejew compare perfect-pairing evaluation tensors and multiplication tensors over fields. The result here treats geometric degenerations of the particular symmetric anchor, using equal-characteristic and unramified Witt models and precise endpoint restrictions. Geometry.py tests 2,880 active-block determinants, 162 idempotents, and 6,750 recovered tensor entries over the fields of orders 2, 3, and 5, including formats with rank-zero, rank-one and rank-two data. This is a prose proof, with publication priority and Lean verification unestablished. [Symmetric final-digit construction](https://github.com/Dugongue/MathProofs/blob/main/FinalDigitFour/Tensor.md) · [Jagiełła and Jelisiejew, Unrestrictions and concise secant varieties](https://arxiv.org/abs/2604.24879) · [Grochow, Qiao, Stange and Sun, On the Complexity of Isomorphism Problems for Tensors, Groups, and Polynomials V](https://arxiv.org/abs/2611.00735)
