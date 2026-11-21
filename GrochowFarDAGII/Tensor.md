# Homogeneous form equivalence via truncated local algebras

**Theorem.** For every field $F$ and fixed degree $d\ge3$, linear equivalence of homogeneous degree-$d$ forms reduces to ordinary isomorphism of finite-dimensional commutative unital $F$-algebras. An algebra isomorphism yields a form transporter over the same field without extracting a $d$th root. For cubics this gives an affirmative construction for the all-fields question of Agrawal and Saxena, and composition with known reductions places the problem in Tensor Isomorphism over every field. In characteristic three, TI-hardness persists with a one-dimensional polarization radical on which the cubic is nonzero.

The proofs are informal. All forms are formal polynomials. The finite controls below were enumerated separately.

## 1. Recovering the auxiliary direction from multiplication

Write $f\in\operatorname{Sym}^d V$, where $V$ is the space of linear forms of dimension $n\ge2$. Equivalence means an invertible linear map of $V$ sends $f$ to $g$ by its induced symmetric-power action. Let $J$ be the positive-degree ideal of $\operatorname{Sym}(V\oplus Fz)$ and define
$$
 A_f=\operatorname{Sym}(V\oplus Fz)/(J^{d+1},\,zV,\,f-z^d).
$$
The target is an unmarked algebra.

The algebra is graded, generated in degree one, and has unique maximal ideal $\mathfrak m$ consisting of positive degrees. That ideal is nilpotent, and an element with nonzero constant term is invertible by a finite geometric series. Its powers are sums of the degrees at or above each index, since the algebra is generated in degree one. Every $F$-algebra isomorphism therefore induces a graded isomorphism.

On degree one, multiply by $v+cz$ into degree two. Degree two is $\operatorname{Sym}^2 V\oplus Fz^2$, since $d\ge3$. Multiplication by nonzero $v$ is injective on $V$ in the polynomial ring, hence contributes rank $n$. The $z^2$ direction contributes rank one precisely when $c\ne0$. Consequently $Fz$ is the rank-one locus with zero adjoined. Its degree-one annihilator is $V$. The induced degree-one map is given by $S\in\operatorname{GL}(V)$ and $z\mapsto az$ with $a\in F^\times$.

In degree $d$, before imposing the last relation, the space is $\operatorname{Sym}^d V\oplus Fz^d$. Its relation space is the line $F(f-z^d)$. Comparing the $z^d$ coefficient shows that $(S,a)$ descends exactly when
$$
  (\operatorname{Sym}^d S)f=a^d g.
$$
Then $a^{-1}S$ gives literal form equivalence. Conversely a form equivalence extends by fixing $z$. For $n=1$, add an unused second variable. For nonzero forms $cx^d,c'x^d$, the pure $d$th-power coefficient of the new variable forces a transporter to preserve $Fx$. The zero cases are immediate.

The dimension is $\binom{n+d}{d}+d-1$. Multiplying ordinary monomials up to degree $d$, killing mixed products, and replacing $z^d$ by the given coefficient vector yields a polynomial-size table for fixed $d$ on dense input. The bit-time statement uses standard effective coefficient encodings. Algebra isomorphisms are field-linear throughout.

Agrawal and Saxena's truncated quotient without the auxiliary branch remembers the line $Ff$ and assumes all scalars have $d$th roots. Their concluding questions ask for a cubic reduction over all fields. The degree-one rank test above forces the scalar witness $a$ in the given field. Grochow and Qiao's alternative route in Part I uses polarization with $3!$ invertible. Their reduction from general $F$-algebra isomorphism to TI applies to these outputs in all characteristics. [Agrawal–Saxena, Theorem 2.3 and Section 6](https://www.cse.iitk.ac.in/%75sers/nitin/papers/cubic-forms.pdf), [Grochow–Qiao I](https://doi.org/10.1137/21M1441110).

**Reduced base rings.** The same equivalence proof works over any reduced commutative ring $R$ with free variable space of rank $n\ge2$. The output is finite free over $R$, since the top relation replaces $z^d$ by $f$. The positive-degree ideal is the nilradical because $R$ is reduced, so its filtration is intrinsic to $R$-algebra isomorphisms. Reduce the induced degree-one map modulo every prime and pass to the residue field. The field rank argument makes each of these maps block diagonal. All original off-block entries therefore lie in every prime and vanish. The invertible block map has $z\mapsto az$ with $a$ a unit of $R$. The relation-line argument again gives the exact form map $a^{-1}S$. This is an algebra-isomorphism reduction over reduced rings, with no extra assertion about tensor-isomorphism complexity over rings. [Grochow–Qiao–Stange–Sun V](https://arxiv.org/abs/2611.00735).

## 2. Exact finite-field search and counts for cubics

Let $d=3$, $n\ge2$, $F=\mathbb F_q$ and $D_i=\dim\operatorname{Sym}^i V$. The graded automorphisms are the pairs $(S,a)$ above, all lifting by homogeneous substitution. These pairs form $F^\times\times\operatorname{Aut}(f)$ under $(S,a)\mapsto(a,a^{-1}S)$. An automorphism inducing the identity on the associated graded has generator images
$$
 x\mapsto x+Q(x)+\ell(x)z^2+C(x),\qquad z\mapsto z+B+bz^2+D,
$$
where $Q:V\to\operatorname{Sym}^2 V$, $\ell:V\to F$, and $C:V\to\operatorname{Sym}^3 V$ are linear, $B\in\operatorname{Sym}^2 V$, $b\in F$, and $D\in\operatorname{Sym}^3 V$. The top-degree relation is unchanged. The mixed relations become $xB+\ell(x)f=0$ for every $x$. If $B\ne0$, the products $xB$ span an $n$-dimensional subspace of $\operatorname{Sym}^3 V$, which cannot lie in $Ff$. Hence $B=0$ and $\ell=0$ for $f\ne0$, while $\ell$ is arbitrary for $f=0$. The remaining choices work and give invertible maps because they induce identities on the filtration quotients.

Therefore
$$
 |\operatorname{Aut}_F A_f|
 = (q-1)q^{\,nD_2+(n+1)D_3+1+n{\bf 1}_{f=0}}|\operatorname{Aut}(f)|.
$$
The same factor applies to transporter counts on equivalent inputs, since both transporter sets are cosets. The algebra witness yields a form witness by the degree-one extraction.

## 3. Degree equal to characteristic and polarization

For a homogeneous degree-$p$ form over a field of characteristic $p$, use the unnormalized polarization
$$
 T_f(v_1,\ldots,v_p)=[s_1\cdots s_p]\,f(s_1v_1+\cdots+s_pv_p).
$$
On a monomial with exponents $(e_i)$, the tensor entry at a tuple of basis vectors with those multiplicities is the monomial's coefficient times $\prod_i e_i!$. The kernel is thus the space of sums of pure $p$th powers with arbitrary coefficients. Its image consists of symmetric $p$-linear tensors with vanishing full diagonal. For a symmetric tensor, the diagonal function in characteristic $p$ depends only on entries with all indices equal, because all intermediate multinomial coefficients vanish.

Let $R$ be the contraction radical of $T_f$ and choose a complement $C$. The same coordinate test gives $f(c+r)=f_C(c)+q_R(r)$, with $q_R$ a pure-power polynomial. Its image $D=q_R(R)$ is an $F^p$-subspace of $F$. Two forms of the same ambient dimension are equivalent exactly when the radical dimensions and image subspaces $D$ agree, and some polarization isometry between the quotients has complement-polynomial discrepancy taking values in $D$.

Indeed, the two radical forms with equal image and equal source dimension are equivalent. In Frobenius coordinates their maps are linear over $F^p$, and the entrywise $p$th-power map identifies the allowed changes of basis with all invertible matrices over $F^p$. After identifying the radical forms, take a quotient transporter with the stated discrepancy. The discrepancy is pure-power because its polarization vanishes. Choose a preimage in the radical for each coefficient and use these as the images of the complement basis under a linear shear. Its contribution from $q_R$ absorbs the discrepancy. Conversely, the block form of any transporter preserving the radical gives the same conditions. A pure-power discrepancy takes values in $D$ precisely when its coefficients lie in $D$, as is seen by evaluating on the complement basis.

Over a perfect field, if $q_R$ is nonzero then its image is all of $F$, so only the quotient polarization and radical dimension are needed. If the radical has dimension one, every quotient tensor transporter lifts uniquely between fixed forms. The radical scalar and shear coefficients are forced by taking unique $p$th roots. Adding a variable with form $w^p$ to a lift of a radical-free diagonal-zero tensor thus gives an exact transporter-preserving encoding in the other direction. Characteristic-three polarization and its additive ambiguity have an established role in code loops. [Drápal–Vojtěchovský, Sections 7 and 10](https://doi.org/10.1007/s10801-009-0203-2).

## 4. A hard cubic subclass over every characteristic-three field

Start from symmetric matrix-space isometry with independent symmetric basis matrices $A_1,\ldots,A_m$, each $n$-by-$n$. In the Part IV construction of Grochow and Qiao, take variable families $x,u$ of length $n$, $z$ of length $m$, $b,c$ of length $r>(n+m+1)/2$, and the single anchor $h$. Form
$$
 F_A(x,z,u,b,c,h)=\sum_{i=1}^m z_i x^\mathsf{T}A_i x
                 +h(x^\mathsf{T}u+b^\mathsf{T}c).
$$
The polarization is the symmetric version of the Section 6 gadget for $2A_i$. The entries with two $x$ slots and one $z$ slot are $2A_i$, including repeated $x$ indices. The anchor terms use three distinct labels. Thus the published recovery implication for that symmetric gadget applies, and there is no full-diagonal entry. The published forward block map acts on the $x$ family by the matrix congruence, the $z$ family by tuple basis change, and the $u$ family by the inverse dual, fixing $b,c,h$. Direct substitution verifies exact polynomial equivalence for the displayed formulas. This verification works over imperfect fields.

The polarization has zero radical. Pairing a putative radical vector with an $x$ vector and a $u$ vector detects its $h$ coordinate. Pairing with $h$ and each of the families $u,x,c,b$ eliminates its $x,u,b,c$ coordinates. Pairing with two $x$ vectors now reads a linear combination of $2A_i$, which vanishes only when the remaining $z$ coordinates vanish.

Output $F_A+w^3$ for a fresh variable $w$. Its polarization has radical exactly $Fw$, with nonzero cubic restriction there. Cubic equivalence induces isometry on the quotient polarizations, and the matrix-space recovery gives the original isometry. Conversely the exact polynomial map extends by fixing $w$. This gives linear-length hardness of the subclass after the matrix-space reduction over every characteristic-three field. Combining with Section 1 proves TI-completeness there. General cubic hardness belongs to the prior work. Over perfect characteristic-three fields, the older Agrawal–Saxena upper reduction also applies, since every scalar has a cube root. The additional restriction here is the exact one-dimensional nonzero radical, alongside the root-independent upper direction. The upper reduction has polynomial dimension increase, so it gives no linear-length running-time transfer for arbitrary cubics. [Grochow–Qiao IV, Theorems 1.10 and 6.1, Equation (11), and footnote 9](https://arxiv.org/pdf/2306.16317).

## 5. Finite controls and priority

Over $\mathbb F_7$, the ordinary ideals generated by $x^3$ and $2x^3$ coincide. The forms are inequivalent, since $2$ is not a cube. Enumeration of all $2016$ matrices of $\operatorname{GL}(2,7)$ found zero form transporters to $2x^3$ and $126$ to $6x^3$. With the auxiliary scalar the graded algebra transporter counts were zero and $756$, respectively.

Over $\mathbb F_3$, $x^2y$ and $x^2y+y^3$ have the same polarization yet are inequivalent. They have two and one projective zeros, respectively, and exhaustive search over all $48$ elements of $\operatorname{GL}(2,3)$ found no transporter. Adding $w^3$ gives the explicit equivalence $w\mapsto w+y$. An independent enumeration of the degree-two mixed constraints in the jet-algebra automorphism proof found one allowable pair $(B,\ell)$ when $f=x^3$ and nine when $f=0$.

The source inspiration comes from comparing finite total-degree jets with pure-power quotients. The latter show how the pure powers become invisible to polarization, while the new algebra uses a second branch whose role is detected below the top degree. The literature checked establishes the older root-dependent reduction and the prior hardness direction. Priority for the present construction remains unverified.
