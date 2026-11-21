# Tensor isomorphism in one reduction fiber of abelian matrix groups

**Theorem.** Fix a finite commutative local nonfield $R$ with maximal ideal $\mathfrak m$, residue field $k$ of characteristic $p$, and a nonzero $s\in\operatorname{Ann}(\mathfrak m)$. Ordinary three-tensor isomorphism over $k$ reduces to conjugacy of generator-given abelian subgroups $P_t\leq\operatorname{SL}_N(R)$. The reduction for an $a\times b\times c$ tensor has $N\leq 2a+b+c+6$. It has the following additional properties.

- The groups of a given format are all abstractly isomorphic to $(R,+)^{N-1}$. They act regularly on the same affine hyperplane, and each $P_t$ is conjugate by a permutation of coordinate axes to a subgroup of the upper unitriangular group.
- The listed generators and subgroup images are identical modulo $sR$ for a given format. Every word in the generators has characteristic polynomial $(X-1)^N$.
- Conjugacy by $\operatorname{GL}_N(R)$, conjugacy by $\operatorname{SL}_N(R)$, conjugacy as subgroups of the affine group on the hyperplane, and source tensor isomorphism are equivalent. Any matrix conjugator yields a source transporter by linear operations.
- Each scalar extension $R^\times P_t$ is a maximal abelian subgroup of $\operatorname{GL}_N(R)$. For fixed $R$, one can instead choose the number of padding directions so that $P_t$ itself is maximal abelian in $\operatorname{SL}_N(R)$, with constant extra rank. For $R=\mathbb Z/2^e\mathbb Z$, $e\geq2$, this takes no extra padding beyond the bound above, uniformly in $e$.

For fixed $R$, conjugacy on the promised generator-given subgroup family, including its entire $\operatorname{GL}_N(R)$-conjugacy saturation, is polynomial-time equivalent to ordinary tensor isomorphism over $R$ and over $k$. For $R=\mathbb Z/p^e\mathbb Z$, $e\geq 2$, the lower reduction with $N\leq 2a+b+c+6$ is uniform in $p,e$, with $N-1$ supplied generators. In that case all generators agree at every strictly smaller precision. Proofs use the standard dense tensor input and ordinary subgroup conjugacy, where the generator list itself does not have to be preserved. [Final-digit tensor construction](https://github.com/Dugongue/MathProofs/blob/main/FixedRingFour/CongruenceClass.md)

## 1. A symmetric bimap with a square-zero basis

Write the input as $t:X\times Y\longrightarrow Z_0$ over $k$, with $X=k^a,Y=k^b,Z_0=k^c$. Let $A_\xi(x,y)=\xi(t(x,y))$, for $\xi\in Z_0^*$. Introduce two more roles and put
$$
 D=X\oplus Y\oplus X^*\oplus k^2 .
$$
For $d=(x,y,z,h)$, $d'=(x',y',z',h')$, define on $D$ the symmetric bilinear forms
$$
 Q_\xi(d,d')=A_\xi(x,y')+A_\xi(x',y),
 \qquad
 F(d,d')=z'(x)+z(x')+h_1h'_2+h_2h'_1 .
$$
Use as output bimap $\beta_t:D\times D\to Z_0\oplus k$ the map whose slices are the $Q_\xi$ and $F$. Every displayed slice has zero diagonal entries in the coordinate basis. The forms work in characteristic two, where they are alternating as well as symmetric. This uses the hyperbolic block idea of Grochow–Qiao. [Grochow–Qiao I, Corollary 7.4](https://arxiv.org/html/1907.00309#S7) · [Grochow–Qiao IV, Theorem 2.1 and Section 6](https://arxiv.org/html/2306.16317#S2)

Tensor equivalence implies equivalence of these symmetric bimaps. Given a source transporter $(g_X,g_Y,g_Z)$, extend the domain map by $g_X^{-{\mathsf T}}$ on $X^*$ and the identity on $k^2$, and extend the output map by the identity on the last line. The first slices transform as the original tensor and the last slice is fixed.

For the reverse, the subspace $\mathcal S_t=\{Q_\xi\}$ in the full slice space is intrinsic. Its elements have rank at most $2a$. Every slice $\lambda F+Q_\xi$ with $\lambda\ne0$ has rank $2a+2$: the map
$$
 (x,y,z,h)\longmapsto(x,y,z-\lambda^{-1}A_\xi(-,y),h)
$$
pulls $\lambda F+Q_\xi$ back to $\lambda F$ and fixes each $Q_\eta$. If $g$ gives a congruence of the full slice spaces, $g^*F$ from the target is such a high-rank form. Precompose with the indicated shear on the source. The corrected map still carries the data spaces into each other and sends the radical of the source $F$ to the radical of the target $F$, which is precisely $Y$ in both. Restrict the data evaluation to $D\times Y$. Its common kernel on the left gives the quotient $X/\{x:t(x,Y)=0\}$, and its common kernel on the right gives $Y/\{y:t(X,y)=0\}$. The dual of the data slice space is canonically the image of the original bimap. Thus the corrected map induces a source isomorphism on the two support quotients and the output image. Extend it over independent complements in the original spaces. This includes dependent or zero tensor slices because the data space is taken as a span. All maps are computed by linear algebra given a symmetric-bimap transporter.

## 2. Put the product in the socle and detect the augmentation by trace

Write $D_R,W_R$ for free coordinate lifts of $D,W=Z_0\oplus k$. Add $d$ unused directions $Q_R=R^d$, with $d=1$ or $2$ chosen to make $N=1+\dim D+\dim W+d$ prime to $p$. Put
$$
 B_t=D_R\oplus W_R\oplus Q_R,\qquad A_t=R1\oplus B_t,\qquad
 xy=s\,\widetilde{\beta_t}(\overline{x_D},\overline{y_D}) \quad(x,y\in B_t).
$$
Here $k\to sR$ given by multiplication by $s$ is an $R$-module isomorphism. Indeed $\operatorname{Ann}(s)=\mathfrak m$ by maximality. Also $s\in\mathfrak m$, since a unit cannot annihilate the nonzero ideal $\mathfrak m$. The formula means apply this isomorphism to the values of $\beta_t$. Make $1$ the unit. The product is commutative. Associativity on $B_t$ follows from $B_t^2\subseteq sW_R$ and $W_R B_t=0$, and extends to $A_t$ by bilinearity and the unit rule.

Let $L_x$ denote left multiplication by $x$. Ordering $1,D_R,W_R,Q_R$ makes $L_b$ strictly triangular for $b\in B_t$. In particular
$$
 \operatorname{tr} L_{r1+b}=Nr,\qquad
 \det(XI-L_{r1+b})=(X-r)^N .
$$
Thus $B_t$ is intrinsic under algebra isomorphism. The map $\bar B_t=B_t/\mathfrak mB_t\to sB_t$, $\bar b\mapsto sb$, is a canonical linear isomorphism for the given scalar $s$. Dividing the product on $B_t$ by this map recovers a $k$-bimap on $\bar B_t$, with both arguments in $\bar B_t$ and output also in $\bar B_t$. Let $K$ be its radical and $J$ its output span. The induced bimap on $(\bar B_t/K)^2\to J$ is exactly the supported $\beta_t$. An algebra isomorphism therefore recovers an isomorphism of $\beta_t$, by extending its maps on these quotient and image spaces to the displayed $D$ and $W$ of equal dimensions. The two occurrences of $D$ use the same extension. Section 1 then recovers the original transporter. In the other direction, lift the two maps of a symmetric-bimap isomorphism to invertible $R$-matrices on $D_R,W_R$. Any entrywise lift is invertible by the residue determinant test. Fix $1$ and all padding coordinates but one. On that unused coordinate use the inverse determinant of the two lifted maps combined. This gives an algebra isomorphism with determinant exactly one. The product rule verifies multiplicativity, since its values lie in $sW_R$ and depend on the domain maps only through their residues.

## 3. Same group law up to abstract isomorphism, different embeddings

Take the subgroup
$$
 P_t=\{L_{1+b}:b\in B_t\}.
$$
It is abelian and is a group because $B_t^3=0$. The determinant is one by triangularity. In the standard basis $b_1,\ldots,b_{N-1}$ of $B_t$, each $b_i^2=0$ by the zero-diagonal construction. Hence $r\mapsto 1+r b_i$ is a homomorphism from $(R,+)$. The product of these commuting one-parameter groups gives
$$
 (r_i)_i\longmapsto \prod_i (1+r_i b_i)
   =1+\sum_i r_i b_i+\sum_{i<j}r_i r_j b_i b_j .
$$
It is bijective: read the $D_R,Q_R$ coordinates first, then subtract their product corrections in $W_R$ to read $W_R$. This gives the claimed abstract group type, including characteristic two, without division by two. Supply the matrices $L_{1+r b_i}$ for additive generators $r$ of $R$; for $\mathbb Z/p^e\mathbb Z$ the single generator $r=1$ suffices. The resulting subgroup acts regularly on $1+B_t$, since the image of $1$ under $L_{1+b}$ is $1+b$. The action in affine coordinates is $y\mapsto b+y+by$. In the quotient by $sR$ all $B_t$-products vanish, so the reduced action is the same translation action for all these tensors. Every word is an element of $P_t$ and has the displayed characteristic polynomial with $r=1$.

The span of $I$ and $P_t$ over $R$ is precisely $L(A_t)$, since $L_b=L_{1+b}-I$. Conjugation of the subgroups therefore induces an $R$-algebra isomorphism of the two regular algebras. Conversely, an algebra isomorphism intertwines their regular actions and sends trace kernels to trace kernels, so it conjugates their $P_t$. On instances from the construction the map in Section 2 gives a determinant-one conjugator, and it preserves the common affine hyperplane. An affine conjugator of the regular actions extends to a linear conjugator in homogeneous coordinates, so affine subgroup equivalence also gives source TI.

The commutant of $L(A_t)$ in the entire endomorphism ring equals $L(A_t)$. If $F_0$ commutes with left multiplication then $F_0(x)=F_0(L_x1)=xF_0(1)$, and commutativity identifies this right multiplication with left multiplication. Hence
$$
 C_{\operatorname{GL}_N(R)}(P_t)=L(A_t^\times)=R^\times P_t.
$$
The centralizer is abelian, so $R^\times P_t$ is maximal abelian. Its conjugacy is again equivalent to source TI because its span is $L(A_t)$. The centralizer in $\operatorname{SL}_N(R)$ is $\{r\in R^\times:r^N=1\}P_t$. For fixed $R$, choose $N\equiv1\bmod p(|k|-1)$ by adding unused directions; all prime divisors of $|R^\times|=(|k|-1)|\mathfrak m|$ then fail to divide $N$. Thus $P_t$ is self-centralizing and maximal abelian in $\operatorname{SL}_N(R)$. For residue field $\mathbb F_2$ the previous requirement that $N$ be odd already suffices. Scalar extensions in the fixed-ring case can be supplied by adding the constant list of scalar units to the generators. [Caranti–Dalla Volta–Sala on abelian regular affine subgroups](https://arxiv.org/abs/math/0510166) · [Arzhantsev–Zaitseva on regular subgroups and algebras over fields](https://doi.org/10.4213/rm10046e)

Fix an algebra isomorphism $\phi:A_t\to A_{t'}$. Every ambient conjugator inducing that algebra isomorphism has the form $L_u\phi$, with $u\in A_{t'}^\times$, by the same commutant calculation. In particular the normalizer is $A_t^\times\rtimes\operatorname{Aut}_R(A_t)$, with the usual action of algebra automorphisms on units. If $\gcd(N,|R^\times|)=1$, then for each $\phi$ there is a unique scalar $r\in R^\times$ with $r^N=(\det\phi)^{-1}$. The determinant-one conjugators inducing $\phi$ are therefore exactly $L_{r(1+b)}\phi$ with $b\in B_{t'}$, a set of size $|R|^{N-1}$.

## 4. Upper reduction and scope

For the saturation promise one can recover $L(A_t)$ from any generator list, in any matrix basis. Start with the $R$-span of the identity and multiply a generating set of the current span on one side by the supplied generators until the span stops growing. Every strict enlargement at least doubles the order and the ambient additive group has order $|R|^{N^2}$. At equality the module contains all positive words. The generators have finite order, so the positive words include inverses, and the resulting module is the span of $I$ and the subgroup. Additive linear systems over the fixed ring, or integer presentations and Smith normal form, implement the span operations. The recovered algebra is free of rank $N$ by the promise. A basis modulo its maximal-ideal multiple lifts to an $R$-basis by Nakayama and the free rank. Compute its multiplication tensor over $R$. For unital associative algebras, independent-mode equivalence of their multiplication tensors implies algebra isomorphism: setting one argument to the unit gives invertible left and right multipliers, and right-multiplying the output map by $(f(1)g(1))^{-1}$ normalizes it to an algebra isomorphism. The reverse is immediate. [Isotopy normalization, written and Lean checked](https://github.com/Dugongue/MathProofs/blob/main/FixedRingFour/NormalizeIsotopy.lean)

For these regular subgroups algebra isomorphism gives conjugacy by the regular module argument, even in arbitrary ambient coordinates. The determinant of the conjugator can still be adjusted by an automorphism scaling an unused padding coordinate, conveyed to the target by any change of ambient basis. Therefore the upper reduction covers both ambient matrix groups. The fixed-ring tensor theorem identifies this upper bound with residue-field TI. The saturation promise is used to recover the free regular algebra and the determinant adjustment. The lower construction itself works over a variable prime-power modulus and never enumerates the group elements.

The classical regular-representation correspondence and the earlier symmetric-matrix-space reductions give separate ingredients. Here the product lives in the socle, the trace recovers it intrinsically, and the same abstract abelian group acts regularly by embeddings with identical lower-precision matrices. In particular the reduction concerns **conjugacy of embedded subgroups**. The proofs are written and priority for this exact combination is unconfirmed.
