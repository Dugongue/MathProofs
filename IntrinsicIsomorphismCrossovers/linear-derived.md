# Linear-size tensor reduction to derived equivalence

**Theorem.** Over every field $k$, ordinary three-tensor isomorphism reduces in deterministic polynomial time to $k$-linear derived equivalence of split basic algebras of global dimension exactly two, with three simple modules and center $k$. If $L$ is the sum of the three input side lengths, each output algebra has dimension $O(L+1)$. The two outputs have the same Cartan matrix for each common input format. On the image family derived equivalence coincides with algebra isomorphism. All statements include characteristics two and three. This is an informal proof.

The earlier dimension-two construction used a matrix rank growing with the coefficient algebra dimension to single out a current Lie ideal. Here the coefficient algebra is split local Frobenius and its socle is derivation-stable. A bound on faithful representations of its current Lie algebra allows constant matrix rank.

## 1. A faithful representation bound

Fix $m\ge5$ invertible in $k$, put $\mathfrak g=\mathfrak{sl}_m(k)$, and let $B$ be a commutative finite-dimensional local $k$-algebra with residue field $k$. Suppose its socle, the annihilator of its maximal ideal, has dimension one. Write $d=\dim_k B$ and choose a nonzero socle vector $s$. Every nonzero ideal of $B$ contains $ks$. In fact multiplying the ideal by successive powers of the maximal ideal and taking the last nonzero product produces a nonzero subspace of the socle. Thus, for any linear functional $f$ with $f(s)\ne0$, the form $(b,c)\mapsto f(bc)$ is nondegenerate. Its radical would otherwise be a nonzero ideal on which $f$ vanishes.

**Lemma.** Every faithful representation of $\mathfrak g\otimes_k B$ has dimension at least $(m-1)d$.

Extend scalars to an algebraic closure. The split local form and the one-dimensional socle persist since the original nilpotent maximal ideal has a one-dimensional quotient, and its annihilator is defined by linear equations. Let $\rho$ be a faithful representation on $V$. Decompose $V$ into simultaneous generalized weight spaces for the commuting operators representing the constant trace-zero diagonal matrices. For $i\ne j$, the operator representing $E_{ij}\otimes b$ sends $V_\lambda$ to $V_{\lambda+\varepsilon_i-\varepsilon_j}$. This follows from
$$
  [\rho(H\otimes1),\rho(E_{ij}\otimes b)]
  =(\varepsilon_i-\varepsilon_j)(H)\rho(E_{ij}\otimes b)
$$
by moving a sufficiently large power of each shifted operator past $\rho(E_{ij}\otimes b)$. It holds for generalized weights in every characteristic.

Set $z=E_{1m}$. By faithfulness, $\rho(z\otimes s)\ne0$. Choose $v\in V_\lambda$ and a linear functional $\ell$ on $V_{\lambda+\varepsilon_1-\varepsilon_m}$ with $\ell(\rho(z\otimes s)v)\ne0$, extending $\ell$ by zero to the other weights. Put $f(b)=\ell(\rho(z\otimes b)v)$. For each $i=2,\ldots,m-1$ the identity
$$
[E_{1i}\otimes b,E_{im}\otimes c]=z\otimes bc
$$
writes the rank-$d$ pairing $f(bc)$ as the difference of two pairings. The first factors through $V_{\lambda+\varepsilon_i-\varepsilon_m}$, the second through $V_{\lambda+\varepsilon_1-\varepsilon_i}$. Each rank is bounded by the corresponding dimension, so the sum of the two dimensions is at least $d$. All $2(m-2)$ intermediate weights are distinct, even in characteristic two. In coordinates the root functionals listed have distinct supports, and the difference between two has support at most four. Restriction to the trace-zero diagonals could make them equal only if their difference were a multiple of the all-ones vector, which requires it to be zero since $m\ge5$. Summing the dimension inequalities over the disjoint weight pairs gives $(m-2)d$. Choose a trace-zero diagonal $H$ with $(\varepsilon_1-\varepsilon_m)(H)=1$. The bracket $[H\otimes b,z\otimes c]=z\otimes bc$ gives one more rank-$d$ pairing, whose two terms factor through $V_\lambda$ and $V_{\lambda+\varepsilon_1-\varepsilon_m}$. Each of these weights differs from each intermediate weight by the same support test, and they differ from each other. The two additional dimensions sum to at least $d$, which proves the stated $(m-1)d$ estimate.

## 2. Linear recovery from the first Hochschild Lie algebra

Assume $d\ge2$, and require that every $k$-derivation of $B$ preserves its maximal ideal. It then preserves $ks$, since for $a$ in that maximal ideal and $t$ in its annihilator, $a\,\delta(t)=\delta(at)-\delta(a)t=0$.

Fix $m=5$ unless the characteristic is five, and fix $m=6$ in characteristic five. Let $W=B^m$. Define $A(B)$ with three diagonal vertices $s_0,x,y$ and strict corners $W_X$ from $s_0$ to $x$, $B$ from $x$ to $y$, and $W_Y$ from $s_0$ to $y$. The only product of two strict corners is $b\cdot w=bw$ under the coordinatewise regular action. The diagonal acts by scalars at the corresponding ends. The corner rule and the absence of any composable triple of strict corners prove associativity. Isomorphisms of $B$ act on all corners to give isomorphisms of $A(B)$.

The strict-corner ideal $J$ is nilpotent, with quotient $k^3$, so $A(B)$ is split basic with three simples. Its center is $k$, because an element commuting with the diagonal idempotents is diagonal and commuting with the adjacent nonzero corners forces the three diagonal entries equal. Its Cartan matrix, with entries $\dim e_iAe_j$ in vertex order $s_0,x,y$, is
$$
 \begin{pmatrix}1&0&0\\md&1&0\\md&d&1\end{pmatrix}.
$$
For the left projectives $P_i=Ae_i$, $P_y$ is simple and $JP_x\cong P_y^d$. Multiplication gives a surjection $P_x\otimes_k W_X\to JP_{s_0}$, with kernel $P_y^{(d-1)md}$. Its $x$-component is the identity and its $y$-component comes from the surjection $B\otimes_k W_X\to W_Y$. The kernel is nonzero because $d\ge2$ and lies in the radical of the domain. A splitting would place a nonzero direct summand of that projective in its radical, which is impossible by taking tops. Hence the simple at $s_0$ has projective dimension exactly two, while the other two simples have projective dimension at most one. This gives global dimension exactly two.

The normalized Hochschild cochain complex relative to the diagonal subalgebra $k^3$ has dimensions $3,d^2+2(md)^2,d(md)^2$ in degrees $0,1,2$, respectively, and vanishes in higher degrees. This follows from the relative normalized bar resolution, whose degree-$q$ term uses $q$ composable off-diagonal corners. The diagonal subalgebra is separable, so this computes ordinary Hochschild cohomology. In degree one a cocycle consists of maps $R,P,Q$ on $B,W_X,W_Y$, with
$$
 QL_b-L_bP=L_{R(b)},
$$
where $L_b$ is multiplication on $W$. Evaluating at $1$ gives $Q=P+L_a$, with $a=R(1)$, and then $[P,L_b]=L_{\delta(b)}$, where $\delta(b)=R(b)-ab$. The commutator identity on $L_bL_c$ shows that $\delta$ is a derivation, and $P=\delta_W+D$ for a $B$-linear $D$ on $W$. Here $\delta_W$ acts coordinatewise. Conversely these choices give all cocycles. The inner diagonal derivations independently add scalar matrices $kI_m$ to $D$ and elements of $k1$ to $a$. Taking commutators of the operators $P$ and $R$ identifies $HH^1$, with its Lie bracket, as
$$
 \mathfrak h(B)=
 \big((\mathfrak{gl}_m(B)/kI_m)\oplus (B/k1)\big)
          \rtimes\operatorname{Der}_k(B).
$$
The second summand inside parentheses is abelian and derivations act entrywise on the first. [Gerstenhaber–Schack, relative Hochschild cohomology](https://www2.math.upenn.edu/~mgersten/papers/Barrfest.pdf)

Because $m$ is invertible, the trace-zero Lie ideal $T=\mathfrak g\otimes B$ embeds in $\mathfrak h(B)$. The quotient is
$$
 Q(B)= (B/k1)^2\rtimes\operatorname{Der}_k(B).
$$
It has a faithful representation of dimension $2d+1$ on $B\oplus(B/k1)\oplus k^2$. Derivations act on $B$ and on $B/k1$ and kill $k^2$. The two abelian summands act as the two independent columns of maps from $k^2$ to $B/k1$.

We show that a Lie isomorphism $\mathfrak h(B)\cong\mathfrak h(B')$, when $B,B'$ have the same dimension, must carry $T$ to $T'=\mathfrak g\otimes B'$. First, the ideals of $\mathfrak g\otimes B$ are precisely $\mathfrak g\otimes I$ for ideals $I$ of $B$. To see this, the constant algebra acts by copies of its absolutely simple adjoint module, for which the commuting endomorphisms are $k$. Every submodule of this direct sum of copies has form $\mathfrak g\otimes I$ for a subspace $I\subseteq B$. Closure under brackets with $\mathfrak g\otimes B$, together with $[\mathfrak g,\mathfrak g]=\mathfrak g$, gives $BI\subseteq I$. Therefore the unique minimal nonzero ideal of $T$ is $S=\mathfrak g\otimes ks$, and every proper ideal of $T$ acts trivially on $S$ by the bracket. Also $S$ is an ideal of $\mathfrak h(B)$ since the coefficient socle is derivation-stable. Use $S'$ for the analogous ideal in $T'$.

Let $K$ be the image of $T$ in $\mathfrak h(B')$, and $S_K$ the image of $S$. The map $K\to Q(B')$ cannot be injective. Otherwise the faithful quotient representation would give a faithful representation of $K$ of dimension $2d+1<(m-2)d$, contradicting Section 1. Its nonzero kernel contains the unique minimal ideal $S_K$, so $S_K\subseteq T'$. Since $S_K$ is an ambient ideal, it contains $S'$. The same argument with the inverse isomorphism gives $S'\subseteq K$, and then $S_K\subseteq S'$. Hence the two socle ideals coincide.

Consider the adjoint action on this common socle ideal. The images of $K,T'$ are two copies of the simple Lie algebra $\mathfrak g$ in its adjoint representation. Each normalizes the other since the original algebras are ideals in the ambient Lie algebra. If the images were distinct, their intersection would vanish by simplicity and they would commute. The centralizer of either adjoint image consists of scalars by absolute simplicity, precluding a nonzero commuting simple image. Thus the images coincide, and the image of $[K,T']$ is the full simple Lie algebra. Since $[K,T']$ is an ideal of $K$ and of $T'$, neither of which has a proper ideal acting nontrivially on the common socle, it is all of both. This proves $K=T'$.

The centroid of $\mathfrak g\otimes B$ recovers $B$, since a centroid map commutes with the constant adjoint action and so has form $\mathrm{id}\otimes F$, with $F(bc)=F(b)c$. This makes $F$ multiplication by $F(1)$, and composition of such maps gives the algebra multiplication. The argument used absolute simplicity of $\mathfrak{sl}_m(k)$ for $m\ge5$ invertible in $k$, which holds in all the stated characteristics.

A $k$-linear derived equivalence preserves the Hochschild Gerstenhaber bracket via derived Morita theory. It also preserves $\dim HH^2-\dim HH^1$, which here equals
$$
  (d-2)m^2d^2-d^2+2.
$$
This is the cochain Euler characteristic formula because $HH^0=k$, and it is strictly increasing in integer $d\ge2$ for fixed $m$. Thus derived equivalence itself enforces equality of $d$. The Lie isomorphism then identifies the two current ideals and their centroids. We have proved $A(B)$ and $A(B')$ are derived equivalent exactly when $B\cong B'$. The linear size is $\dim_k A(B)=3+(1+2m)d$. [Rickard, Morita theory for derived categories](https://doi.org/10.1112/jlms/s2-39.3.436) · [Keller, derived invariance of higher Hochschild structure](https://webusers.imj-prg.fr/~bernhard.keller/publ/dih.pdf)

## 3. Linear coefficient encodings for ordinary tensors

We give the coefficient encoding explicitly to cover zero and nonconcise tensors and to fix the dimensions from the input format. Regard an ordinary array as a bilinear map $\mu:X\times Y\to Z$ by taking dual coordinate spaces as necessary. Build a triangular algebra $D_\mu$ with three main vertices $0,1,2$ and strict corners $X$ at $01$, $Y$ at $12$, and $Z$ at $02$. The product $X\times Y\to Z$ is $\mu$. Give each main vertex two private source vertices, and give their arrows to that main vertex pairwise distinct corner dimensions larger than $\max(\dim X,\dim Y,\dim Z)$. All products of strict corners involving a tag are zero. These rules are associative, since any product of three strict corners vanishes under either parenthesization. Each vertex has a diagonal scalar algebra.

The strict-corner ideal $J_D$ is the span of commutators, as every strict corner consists of elements $[e_i,x]$ with its source idempotent. It is also nilpotent. The quotient $D_\mu/J_D$ is a product of copies of $k$, so an isomorphism permutes its primitive idempotents. In $J_D/J_D^2$ the unique large dimensions of tag corners fix their ordered endpoints, including all main vertices. Lift preservation of diagonal idempotents by simultaneous conjugation: if the images are $f_i\equiv e_i\pmod{J_D}$, then $u=\sum_i f_i e_i$ is a unit with $f_i u=u e_i$. Thus the original three corners and their product can be read after conjugation. This gives $D_\mu\cong D_{\mu'}$ exactly when the tensors are isomorphic. The reverse lifts the three coordinate maps and keeps the tags fixed. Its dimension is $O(L+1)$, including when a side is zero.

Next form a commutative unital algebra $C$ on $k\oplus (D_\mu\oplus D_\mu^*)\oplus D_\mu^*$. The final summand annihilates the two nonscalar summands, and the product of $w=(x,\phi),w'=(y,\psi)$ in the middle summand has value at $a\in D_\mu$ given by
$$
 \beta(w,w')(a)=\psi(ax)+\phi(ay).
$$
The products span the last summand by taking $x=1,\phi=0,y=0$ and arbitrary $\psi$. Hence the last summand is the square of the nilpotent maximal ideal. Any isomorphism of these commutative algebras therefore yields a congruence of the families with matrix
$$
 J_a=\begin{pmatrix}0&L_a^T\\L_a&0\end{pmatrix}.
$$
Conversely, a congruence between the families gives an isomorphism of the commutative algebras. An isomorphism of the $D_\mu$ induces such a congruence by acting on $D_\mu$ and by its inverse dual on $D_\mu^*$.

For reflection, a congruence takes $J_1$ to some invertible $J_b$, so $L_b$ is invertible and $b$ is a unit. Ratios of slices to a selected invertible slice are transported by conjugation. In the source, the ratios relative to $1$ are $\operatorname{diag}(L_a,L_a^T)$. In the target the ratios relative to $b$ are $\operatorname{diag}(L_d,L_{bdb^{-1}}^T)$, where $d=b^{-1}a$. The second-factor inner automorphism may be removed when taking the abstract generated algebra. In both cases this generated algebra is
$$
 D_\mu\times_{D_\mu/J_D} D_\mu^{\mathrm{op}},
$$
with the corresponding target construction on the other side. Indeed under the faithful left-regular and transpose left-regular representations its generators are $(a,a^{\mathrm{op}})$. A product of two generators minus the generator for their first-coordinate product gives $(0,(ba-ab)^{\mathrm{op}})$, and the commutators span $J_D$. This produces both copies of the strict ideal, while the diagonal pairs produce the common quotient. The commutator ideal in the fiber product is $J_D\times J_D^{\mathrm{op}}$, and its quotient by its square has the original tag corners and their reverses. Each big tag dimension now fixes an unordered pair of vertices. The two tags at each main vertex intersect precisely at that vertex, so all vertices of the tagged algebra are identified. Conjugate to align the diagonal idempotents as above, then keep only the forward off-diagonal corners in the chosen vertex order, with private sources before the main vertices. They recover $D_\mu$ from the fiber product. Thus an isomorphism of the commutative $C$'s implies tensor isomorphism. All these constructions use linear dimension and work over every field. [Related triangular construction in Grochow–Qiao, Part I](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full)

## 4. A split local Frobenius algebra with stable socle

Put $U=C_1\oplus C_2\oplus C_3^*$, using two copies of $C$ and one dual copy. Define a symmetric trilinear form $F$ by $\phi(xy)$ on the ordered triple of these distinct summands, extending symmetrically to every order, and zero on triples with repeated summand. The unit and free dual imply that $F$ is concise, meaning that no nonzero vector has identically zero contraction. Indeed, testing against the other two summands isolates each component, and choosing a unit in one factor where needed and testing against the full remaining dual or algebra recovers that component.

The centroid of $F$ is $C$. To see this, define the centroid by equality of inserting an endomorphism in any of the three positions. For an off-diagonal block sending one summand $i$ to a different summand $j$, use two arguments from $i$ and one from the remaining summand. Comparing insertion into the first argument and into the remaining-summand argument shows that the block vanishes by the perfect separation of the typed triple. The diagonal blocks satisfy
$$
 \phi((P x)y)=\phi(x(Qy))=(S\phi)(xy).
$$
Evaluation at the unit shows that $P,Q$ are multiplication by one element of $C$, and $S$ is its dual multiplication. Conversely these blocks give centroid maps, with multiplication from composition. In particular a linear equivalence of such forms up to nonzero scalar induces an algebra isomorphism of their centroids. An isomorphism of the $C$'s gives an exact equivalence of the forms by acting on the three summands.

Now take
$$
 B=k1\oplus U\oplus U^*\oplus ks,\qquad
 uv=F(u,v,-),\qquad u\phi=\phi(u)s
$$
for $u,v\in U,\phi\in U^*$, and all other products of nonscalar components zero. Extend commutatively with unit. The only possibly nonzero triple of nonscalar inputs consists of vectors of $U$, and both products are $F(u,v,w)s$. This proves associativity. Conciseness of $F$ gives that the products $uv$ span $U^*$, by duality, and $u\phi$ spans $ks$. The maximal ideal $I$ is the sum of the three nonscalar components, with $I^2=U^*\oplus ks$, $I^3=ks$, and $I^4=0$. Its annihilator is exactly $ks$: testing against $U^*$ forces the $U$-part of an element in $I$ to vanish, and testing against $U$ forces its $U^*$-part to vanish. A nonzero scalar part cannot annihilate $I$ since its effect on $s$ is nonzero. Thus $B$ is split local Frobenius. An isomorphism of such $B$'s induces linear maps on $I/I^2$ and $I^3$ preserving the induced triple product. This gives an equivalence of $F$'s up to scalar and hence recovers $C$. Conversely a $C$-isomorphism induces an exact $F$-equivalence, which extends by inverse dual on $U^*$ and identity on $ks$ to a $B$-isomorphism.

Every derivation preserves $I$ in all characteristics. Within each of the three original summands of $U$, every pair of vectors has zero product by the definition of $F$. Each summand has dimension at least two. For any nonzero $u$ in such a summand, take a linearly independent $v$ in the same summand. Writing $a(u),a(v)$ for the scalar parts of their derivative, the $U$-component of the derivative of $uv=0$ is $a(u)v+a(v)u=0$. Thus $a(u)=0$. All of $U$ maps into $I$. Since $U^*$ is spanned by products of two vectors from $U$ and $s$ by products of three, the whole of $I$ maps into $I$. This supplies the derivation-stable socle for Section 2 even in the small characteristics.

## 5. Size and scope

The composite $\mu\mapsto D_\mu\mapsto C\mapsto B\mapsto A(B)$ is explicit and each step multiplies the dimension by at most a constant. All dimensions used in the construction depend only on the three input side lengths. Arbitrary zero tensors and zero-sized sides are permitted. Different input formats can be rejected at the outset or sent to a fixed negative pair of the same format. If an unused dimension is written succinctly as part of a zero-sized format, one can decide the corresponding trivial comparison directly. For every nonempty dense format the sum of side lengths is polynomial in the input length. The coefficient operations are copies and signed sums of bounded length, and over finite fields and $\mathbb Q$ the resulting dense tables have polynomial binary size. For abstract fields the statement uses the explicit coordinate model.

The comparison on the promised image is TI-complete. For the reverse reduction remember that multiplication isotopy of unital associative algebras is equivalent to algebra isomorphism. If $h(xy)=f(x)g(y)$ for invertible linear maps, then $a=f(1)$ and $b=g(1)$ are units since multiplication by each is bijective. One obtains $h(xy)=h(x)(ab)^{-1}h(y)$, so $x\mapsto(ab)^{-1}h(x)$ is an algebra isomorphism. The corresponding multiplication tensor gives the reverse map. For cubic $n\times n\times n$ tensors over any fixed finite field $\mathbb F_q$, the linear output dimension is optimal in order of growth for objectwise encodings into multiplication tables. There are at least $q^{n^3-3n^2}$ source orbits by dividing the number of tensors by an upper bound on the group size. There are at most $(D+1)q^{D^3}$ multiplication tables of dimension at most $D$, even before imposing algebra identities or taking derived classes. An objectwise reduction must inject the source orbits into output comparison classes, forcing $D=\Omega(n)$. The intermediate $B$-construction also gives a linear-size equivalence with isomorphism on the promised split local Frobenius family, whose radical filtration has successive dimensions $1,\dim U,\dim U,1$. The reverse map is again multiplication isotopy.



The theorem is a hardness and promised comparison result for derived equivalence. Publication priority for the faithful-module estimate and its use in the reduction remains unverified.
