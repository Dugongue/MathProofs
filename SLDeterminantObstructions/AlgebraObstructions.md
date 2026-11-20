# Obstructions for determinant-one tensor isomorphism via associative algebras

Two exact obstructions concern matrix amplification and passage to the associated graded algebra. The first gives a necessary and sufficient condition for any fixed schedule of matrix amplifications to preserve determinant-one equivalence of multiplication isotopes. The second gives explicit local algebras with identical ordered graded data but opposite determinant-one outcomes. Over odd finite fields, the graded obstruction occurs at the first possible radical length.

Work over $F=\mathbb F_q$, with $m=q-1$. Use the convention $T'(Px,Qy)=R T(x,y)$. A multiplication isotope is a tensor ordinarily isomorphic to the multiplication tensor of a finite-dimensional unital associative $F$-algebra. All algebras are given in ordered bases.

## Multiplication and determinant profiles

Let $A$ be such an algebra. Put
$$
 D_A=\det_F\operatorname{Aut}_{F\text{-alg}}(A),\quad
 I_A=\det_F\operatorname{Inn}(A),\quad
 C_L(A)=\det_F L_{A^\times},\quad C_R(A)=\det_F R_{A^\times}.
$$
If $R(xy)=P(x)Q(y)$, then $a=P(1)$ and $b=Q(1)$ are units. Indeed, evaluation at $1$ in either argument gives invertible left multiplication by $a$ and right multiplication by $b$. Substitution gives the unital algebra isomorphism $\phi(x)=a^{-1}R(x)b^{-1}$. Conversely, every algebra isomorphism $\phi$ and pair of units give the transporter
$$
 (P,Q,R)=(L_a\phi,R_b\phi,L_aR_b\phi).
$$
Thus ordinary equivalence of multiplication tensors is algebra isomorphism, and determinant-one equivalence is existence of a determinant-one algebra isomorphism. For the latter, $\det\phi=\det P\det Q/\det R$, and an algebra isomorphism of determinant one gives it in all three modes. The exact stabilizer determinant group of a multiplication tensor or any of its raw isotopes is
$$
 H_A=\{(u r,v r,uvr): u\in C_L(A),\ v\in C_R(A),\ r\in D_A\}.
\tag{1}
$$
Raw normalization conjugates each stabilizer coordinate, preserving determinants.

Write $A/J=\prod_i M_{n_i}(E_i)$ for the semisimple quotient by the radical $J$. Let $\ell_i,r_i$ be the total multiplicities of the natural left and right simple modules of factor $i$ on all $J^k/J^{k+1}$, starting with $J^0=A$. For a unit with residue matrices $u_i$, left and right multiplication have determinants
$$
 \prod_i N_{E_i/F}(\det_{E_i}u_i)^{\ell_i},
 \qquad
 \prod_i N_{E_i/F}(\det_{E_i}u_i)^{r_i},
\tag{2}
$$
respectively. Each formula follows by multiplying the determinants on the invariant radical filtration. The determinant of conjugation by the same unit has exponents $\ell_i-r_i$. Every quotient unit lifts to a unit, and both field norms and matrix determinants over finite fields are surjective. These are therefore exact descriptions of all three images.

## Sharp obstruction for matrix amplification

For $d\ge1$ let $T^{[d]}=\mu_{M_d(F)}\otimes T$, with matrix multiplication and $T$ in corresponding modes. On multiplication tables this is the multiplication table of $M_d(A)$. It is a multiplication isotope whenever $T$ is one.

**Theorem.** Fix positive integers $d_1,\ldots,d_s$, with $s\ge1$. The following equivalence holds for all multiplication isotopes $T,T'$ over $F$ exactly when $\gcd(m,d_1,\ldots,d_s)=1$:
$$
 T\simeq_{\mathrm{SL}} T'
 \quad\Longleftrightarrow\quad
 T^{[d_j]}\simeq_{\mathrm{SL}} (T')^{[d_j]}
 \text{ for every }j.
\tag{3}
$$
For $q>2$, the failing cases already have counterexamples from one fixed cube-zero-radical algebra and a change of basis. The same pair defeats every subsequent test of the amplified data that is invariant under independent special-linear changes of the amplified inputs.

To prove the theorem, first observe that two full labelled systems of $d$-by-$d$ matrix units in an algebra $A$ are conjugate by a unit when both exist. Modulo $J$, in each simple matrix factor the diagonal idempotents decompose the natural space into $d$ equal-dimensional spaces, identified by the off-diagonal matrix units. Match bases on the first spaces and transport them to the rest to conjugate the quotient systems. Lift this quotient unit and perform that conjugation. The resulting two systems $e_{ij},f_{ij}$ agree modulo $J$, so $w=\sum_i f_{i1}e_{1i}$ equals $1$ modulo $J$, is a unit, and satisfies $we_{ab}=f_{ab}w$.

Consequently $M_d(A)\cong M_d(B)$ implies $A\cong B$ by aligning matrix units and restricting to the first corner. Any isomorphism respecting matrix units acts entrywise on that corner. In particular every algebra automorphism of $M_d(A)$ is inner conjugation composed with an entrywise automorphism of $A$. The latter's determinant is $(\det_F\phi)^{d^2}$. The semisimple factors of $M_d(A)$ have sizes $d n_i$ and the same centers as those of $A$. In the radical grades, a standard first diagonal corner of such a factor acts on $d$ copies of the corresponding first diagonal corner for $A$ on the left, and likewise on the right. Hence the multiplicities become $d\ell_i,d r_i$. By (2) the exact changes of groups are
$$
 \begin{split}
 C_L(M_d(A))&=C_L(A)^d,\qquad C_R(M_d(A))=C_R(A)^d,\\
 I_{M_d(A)}&=I_A^d,\qquad D_{M_d(A)}=D_A^{d^2}I_A^d.
 \end{split}
\tag{4}
$$
Here $K^j$ means the subgroup of $j$-th powers in $K$.

If $T,T'$ have no ordinary transporter, none of the amplified pairs does, by cancellation on the normalized algebras. Otherwise choose one ordinary transporter with determinant triple $\delta$. The set of determinant triples is $\delta H_A$, and the amplified pair has set $\delta^{d^2}H_{M_d(A)}$, with powers coordinatewise. This follows because tensoring each of the three transporter maps with the identity of dimension $d^2$ gives one amplified transporter. For a prime $\ell\mid m$, if $\ell\nmid d$, then (1) and (4) give the same $\ell$-primary stabilizer group before and after amplification, since powers $d,d^2$ are automorphisms on such subgroups and $I_A\subseteq D_A$. Consequently the $\ell$-primary obstruction to membership $\delta\in H_A$ is detected in any such amplification. Subgroup membership in this finite abelian group holds exactly when it holds at every prime. This proves reflection under the stated gcd condition. Preservation follows by tensoring a determinant-one transporter with the identity.

For sharpness, take $A=M_m(F[t]/(t^3))$ when $q>2$. Its radical has cube zero. For $B=F[t]/(t^3)$, the left and right multiplications have equal determinants, so $I_B=\{1\}$. By (2) and (4), both unit groups' determinant images and all algebra-automorphism determinants of $M_{dm}(B)$ are trivial for every $d\ge1$. Thus every $H_{M_d(A)}$ is trivial. If $\ell\mid\gcd(m,d_1,\ldots,d_s)$, choose a basis change of determinant of order $\ell$ in one mode of the multiplication tensor of $A$. The modified tensor is not determinant-one equivalent to the original, by (1). All amplified pairs are determinant-one equivalent, since the chosen basis-change determinant raised to $d_j^2$ is $1$. The exact kernel on the $(F^\times)^3$ determinant classes of this raw ordinary orbit is the product in the three coordinates of the common roots of unity of order dividing $\gcd(m,d_1^2,\ldots,d_s^2)$.

There is a related obstruction for more general fixed tensor factors. If every auxiliary tensor factor used in one chosen mode has dimension divisible by the same prime $\ell\mid m$, use the same one-mode twist of order $\ell$. For a linear map $P$ and auxiliary space of dimension $b$, $\det(P\otimes I_b)=(\det P)^b$. Hence every expanded pair is already special-linear equivalent. This conclusion applies with multiplication tensors of arbitrary finite-dimensional auxiliary algebras, even without any cancellation theorem for those factors.

For ordinary TI outputs alone, the same example gives an obstruction to any construction that, on each input separately, maps all ordinarily equivalent raw tensors to ordinarily equivalent output tensors or isomorphic algebras. Even a list of such outputs and arbitrary isomorphism-invariant postprocessing cannot distinguish the twisted raw pair from the self-pair. This includes any construction that keeps only the underlying unmarked associative algebra of a multiplication isotope.

## Ordered radical grades do not determine the oriented answer

**Theorem.** For every $q>2$, there are pairs of commutative local multiplication tensors with the following retained data identical: the ordered associated graded multiplication tables of both endpoints, the full radical flags as coordinate subspaces, the radical-annihilator subspaces, the left and right unit determinant images, and the basis-change determinant calibration. Nevertheless one pair has determinant-one equivalence and the other does not. The local algebras can also agree modulo an arbitrarily deep specified power of the radical. Any decision or reduction whose input factors through this retained data therefore fails.

Set $a=6rm-1$, $c=8rm+1$, $d=10rm$ for an arbitrary integer $r\ge1$. Then $3\le a<c<d<2a$. Consider two commutative local $F$-algebras on three generators:
$$
 A_y=F[x,y,z]/(xy,xz,yz,y^{c+1},z^{d+1},x^a-y^c),\qquad
 A_z=F[x,y,z]/(xy,xz,yz,y^{c+1},z^{d+1},x^a-z^d).
$$
In each algebra the same ordered basis is
$$
 1,\ x,\ldots,x^{a-1},\ y,\ldots,y^c,\ z,\ldots,z^d .
\tag{5}
$$
To check independence as well as spanning, the algebra with the listed individual powers and pairwise zero cross products first quotients $x^{a+1}$ to zero. In that intermediate algebra $x^a$, $y^c$, $z^d$ are independent and are annihilated by its radical. Imposing $x^a-y^c$ or $x^a-z^d$ then imposes exactly one linear relation. Both original presentations already imply $x^{a+1}=0$.

The radical consists of the positive powers in (5), is nilpotent, and has residue field $F$. The $k$-th power is precisely the span of the displayed monomials with exponents at least $k$. Indeed the only redirected power is $x^a$, which lands in degree $c>a$ or $d>a$. Hence the ordered associated graded multiplication is identical in both algebras, namely the separated three branches with $x^a=0$. Their common radical annihilator in the radical is $F y^c+F z^d$. This follows by multiplying a candidate by each branch generator. In particular $x^{a-1}$ is never in the annihilator, since its product with $x$ is nonzero in both tables. The annihilator lies in $J^2$, so the quotient of the annihilator by its intersection with $J^2$ vanishes for both. The two presentations also agree modulo $J^c$. Their dimension is $a+c+d=24rm$. The radical filtration shows that left and right multiplication by a unit with residue $u$ both have determinant $u^{24rm}=1$.

Any algebra automorphism acts diagonally on the images of $x,y,z$ in $J/J^2$, with nonzero coefficients $\alpha,\beta,\gamma$. To see this, in the graded algebra their degree-two squares are independent. The products between images of different generators are zero, so the tangent matrix has at most one nonzero entry in each row, and invertibility makes it monomial. The differing nilpotence degrees $a,c+1,d+1$ in the graded algebra distinguish the three axes. The automorphism determinant is then the product of its grade determinants, namely
$$
 \alpha^{a(a-1)/2}\beta^{c(c+1)/2}\gamma^{d(d+1)/2}=\alpha\beta.
\tag{6}
$$
The congruences follow from $a\equiv-1,\ c\equiv1,\ d\equiv0\bmod 2m$.

The exact filtered relation forces more than the graded algebra. In $A_y$, $\phi(x)^a=\phi(y)^c$ forces $\alpha^a=\beta^c$. The higher terms of $\phi(x)$ in the other two branches contribute only powers of degree at least $2a>d$, which vanish. In the $x$-branch only its leading terms contribute, because $x^{a+1}=0$. The same argument for $\phi(y)^c$ uses $2c>d$. Analogously in $A_z$ the condition is $\alpha^a=\gamma^d$. These conditions are sufficient for the displayed diagonal scalings themselves to be automorphisms. Thus in $A_y$ necessarily $\beta=\alpha^{-1}$, so $D_{A_y}=\{1\}$. In $A_z$ necessarily $\alpha=1$ but $\beta$ can be arbitrary, so $D_{A_z}=F^\times$.

For each algebra compare its multiplication table with the table obtained by conjugating its coordinates by the same diagonal map $D$ of determinant $\zeta\ne1$. One may take $D$ to scale the coordinate $x$ and fix the other basis vectors. The conjugated multiplication is $D\mu(D^{-1}{-},D^{-1}{-})$, so $D$ is a relative algebra isomorphism. The set of algebra-isomorphism determinants is $\zeta D_{A_y}$ or $\zeta D_{A_z}$. It contains $1$ only for $A_z$. All the retained data agree across the two comparisons, since the original ordered graded tables agree and the same filtration-preserving diagonal change is performed on them. This proves the claimed obstruction, including the identical calibration.

## The first possible radical length over odd fields

When $J^3=0$, the graded obstruction cannot occur over a finite field. Choose a Wedderburn–Malcev section of $A/J$. The enveloping algebra of the semisimple quotient is semisimple, so choose a bimodule complement $V$ to $J^2$ in $J$. The product of two elements of $V$ lies in $J^2$ and encodes exactly the grade-one product. All products $J J^2$ and $J^2 J$ vanish. This gives a splitting $A\cong\operatorname{gr}_J A$ inducing identity on all grades. Lifts of ordered bases of the grades give a basis of $A$, and changing these lifts only adds block-triangular entries with identity diagonal. Therefore the algebra-isomorphism determinant profile is determined by the ordered graded algebras and the changes of frame to raw coordinates. The unit images are already given by (2). [Wedderburn–Malcev theorem](https://doi.org/10.1007/978-1-4419-8616-0)

Over odd $F$, the conclusion fails for $J^4=0$ in dimension $9$. Use generators $x,u,y,w$. Products between the $(x,u)$ and $(y,w)$ branches are zero. Put $u^2=w^2=y^2w=y^4=0$, and take $x^2=0$ in $B_0$ and $x^2=y^3$ in $B_1$. These define commutative local algebras with the same basis
$$
 1,\ x,u,y,w,\ y^2,yw,xu,\ y^3 .
$$
For example, one may start with this basis and the indicated products, with $x^3=0$ and all products of degree greater than three zero. Associativity holds in the $(y,w)$ branch by its monomial relations. Within the other branch, every product of three positive-degree elements is zero. The redirected value $x^2=y^3$ is annihilated by all four generators, so cross-branch products remain associative. This proves the dimension and nonvanishing of the listed powers directly. Both have $J^3=F y^3$, and the same ordered radical flags and associated graded multiplication. The same radical-annihilator subspace is $F yw+F xu+F y^3$. Indeed multiplication by $w,u,x,y$, in that order, forces zero for the four tangent coefficients and then for the coefficient of $y^2$.

To compute determinants in $B_1$, use the graded tangent space. The set of elements of degree one whose cubes are zero is $H=\langle x,u,w\rangle$, since $(\beta y+h)^3=\beta^3 y^3$ in the graded algebra. The product on $H$ has image the line $F xu$, with radical $F w$, and is hyperbolic on $H/Fw$. Let $\beta$ be the induced scalar on the tangent quotient by $H$, let $\gamma$ be the scalar on $F w$, let $C$ be the induced matrix on $H/F w$, and let $\rho$ be the scalar on $F xu$. Since the only isotropic lines for the hyperbolic product on $H/Fw$ are its two coordinate axes in odd characteristic, $C$ is diagonal or antidiagonal. In $B_1$ it cannot interchange these axes. Such an interchange would send $x$ to an element with tangent in $F u+F w$, whose square is zero. Products of $H$ with $J^2$ are zero, and $J^4=0$, so higher corrections cannot change that square. But $\phi(x)^2=\phi(y)^3=\beta^3 y^3\ne0$. For diagonal $C$, if $\alpha$ is the $x$-coefficient, the same calculation gives $\alpha^2=\beta^3$. Hence $\beta$ is a square, and $\det C=\rho$.

The grade-one determinant is $\beta\gamma\det C$. In grade two the diagonal scalars in the basis $y^2,yw,xu$ are $\beta^2,\beta\gamma,\rho$. In grade three the scalar is $\beta^3$. Thus every automorphism of $B_1$ has determinant
$$
 \beta^7\gamma^2(\det C)\rho=\beta^7\gamma^2\rho^2,
$$
a square. Scaling $w$ scales $w,yw$ together and realizes every square. It works in both algebras. In $B_0$, freely scaling $y$ yields determinant $\beta^7$, which is a nonsquare for nonsquare $\beta$. Hence
$$
 D_{B_1}=(F^\times)^2,\qquad D_{B_0}=F^\times.
$$
Using the same conjugation of nonsquare determinant on either multiplication table now gives opposite determinant-one answers with identical graded data, identical annihilator and identical calibration. The two unit determinant images are the same as well, since both algebras are local of dimension $9$ with residue field $F$.

## Scope

These obstructions are unconditional on their specified models. A construction can escape the matrix obstruction by retaining determinant information separately. It can escape the graded obstruction by retaining the full filtered multiplication. Neither result excludes arbitrary reductions in the direction asked by [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5). Over $F_2$ all invertible linear maps have determinant one.

The existing multiplication-isotope and Peirce profiles give the regular-module norm method. The exact amplification schedule and the displayed filtered counterexamples are the additional statements here. The proofs are informal. Publication priority is unverified.

Finite controls checked all 1,458 basis associativity triples for the two nine-dimensional tables, 129,216 candidate diagonal or axis-swapping maps over five odd prime fields, 422,496 tangent-scale assignments for the three-branch family, and 7,840 cyclic-group amplification schedules. All passed. The universal assertions follow from the written proofs.
