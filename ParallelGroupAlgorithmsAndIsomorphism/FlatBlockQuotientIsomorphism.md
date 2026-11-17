# Deterministic polynomial-time isomorphism of flat genus-two quotients

Let $p$ be odd. Given two groups promised to be quotients of flat blocks $H_m^\flat(\mathbb F_{p^e})$ by arbitrary normal subgroups, their isomorphism can be decided in deterministic time polynomial in the bit size of their commutator matrices over $\mathbb F_p$ and the group order in binary. The fields, block sizes and kernels need not be supplied. This applies to the compact matrix input and to the generating-set representations from which Schrock obtains those matrices and the order in polynomial time. The proof also answers Schrock's Conjecture 4.4.2.5 about Algorithm 4.1 and the pointwise pencil stabilizer conjecture in §4.5. These are informal proofs. [Schrock, §2.5.3](https://math.colorado.edu/~tysc3584/Tyler_Schrock-PhD_Thesis.pdf#page=49) · [Conjecture 4.4.2.5](https://math.colorado.edu/~tysc3584/Tyler_Schrock-PhD_Thesis.pdf#page=114) · [Pointwise stabilizer conjecture](https://math.colorado.edu/~tysc3584/Tyler_Schrock-PhD_Thesis.pdf#page=120)

## 1. Commutator matrices and two marked forms

Write $K=\mathbb F_{p^e}$, $E=K^m$, $U=K^{m+1}$, and $V=E\oplus U$. Index the $U$ coordinates by $0,\ldots,m$. For row operators $J_1,J_2:U\to E$, take
$$
 J_1 u=(u_0,\ldots,u_{m-1}),\qquad J_2 u=(u_1,\ldots,u_m).
$$
The original block has center and derived group $P=K^2$, with commutator components $b_i((x,u),(y,v))=x^{\mathsf T}J_i v-y^{\mathsf T}J_i u$. This bimap is surjective and has zero radical. If the central kernel is $N$, then $G=H_m^\flat(K)/N$ has derived group $P/N$ and abelianization $V$, even when $Z(G)$ strictly contains $G'$. In odd characteristic, the group is the Baer group on $V\oplus(P/N)$ with multiplication $(v,z)(w,z')=(v+w,z+z'+(b(v,w)+N)/2)$. Thus an isomorphism between such groups is equivalent to a simultaneous domain isometry and invertible change of output coordinates for their commutator bimaps on the derived group and abelianization. If the input describes the commutator matrices on $G/Z(G)$, recover the abelianization version by adding $\log_p|G|-\dim_{\mathbb F_p}(G')-\dim_{\mathbb F_p}(G/Z(G))$ zero rows and columns to each form. Those extra directions are the radical $Z(G)/G'$. [Schrock, §§4.2.1 and 4.3](https://math.colorado.edu/~tysc3584/Tyler_Schrock-PhD_Thesis.pdf#page=98)

Identify the dual of $P/N$ with the space $S=N^\perp\subseteq K^2$ using the trace pairing $(w,z)\mapsto\operatorname{Tr}_{K/\mathbb F_p}(w^{\mathsf T}z)$. A weight $w=(a,b)$ gives the scalar form
$$
 \omega_w((x,u),(y,v))
 =\operatorname{Tr}\bigl(x^{\mathsf T}(aJ_1+bJ_2)v-y^{\mathsf T}(aJ_1+bJ_2)u\bigr).
$$
For nonzero $w$, its radical is $0\oplus\ker(aJ_1+bJ_2)$, of dimension $e$ over $\mathbb F_p$. The $m$ equations $au_{i-1}+bu_i=0$ are independent, by solving successively from one endpoint. Weights on the same $K$-line have equal radical. Weights on different $K$-lines have disjoint radicals, since their two equations force $u_{i-1}=u_i=0$ for each $i$.

Every $K$-linear change on $P$ lifts. One direct construction takes $L_0=K^2$, $E=\operatorname{Sym}^{m-1}(L_0)$, $U=\operatorname{Sym}^{m}(L_0)^*$ and $P=L_0^*$. Evaluate the output at $r\in L_0$ by $v(rx)-u(ry)$. In the monomial bases these are the displayed forms. For $D\in\operatorname{GL}(L_0)$, act on $E$ by $\operatorname{Sym}^{m-1}(D)$ and on $U$ by the dual of $\operatorname{Sym}^{m}(D^{-1})$. The action on $P$ is the dual of $D^{-1}$ by equivariance of polynomial multiplication. Coordinatewise Frobenius lifts because the commutator matrices have prime-field coefficients in this model. Consequently any ordered $K$-independent weight pair can be put at $(1,0),(0,1)$, and a single nonzero weight can be put at $(1,0)$. [Brooksbank, Maglione and Wilson, Proposition 5.3](https://joshmaglione.com/papers/Genus2.pdf#page=23)

## 2. Recover coefficients from a raw matrix pair

In a nonzero form space, choose a nonzero form from its input basis. If another basis form has a different radical, choose that form as the second mark. This is possible whenever $S$ spans $K^2$, since otherwise all basis weights would lie on the first weight's $K$-line. Work in the hypothetical cover coordinates normalizing the two marks to $(1,0),(0,1)$. The following matrix operations recover the normalized coefficient data without constructing those coordinates.

Let $\alpha_i(v)=\omega_i(v,-)$. Compute the suffix flag $R_0=\ker\alpha_1$ and $R_{j+1}=\alpha_1^{-1}(\alpha_2(R_j))$. In the normalized model $R_j=\bigoplus_{i=m-j}^m U_i$ for $0\le j\le m$, where $U_i$ is the $i$-th $K$-coordinate line. Indeed $\alpha_2$ identifies the terminal coordinates $u_i$ with the corresponding $x_i$-dual coordinates, and the preimage under $\alpha_1$ shifts the suffix by one position. Swapping the two forms yields the prefix flag. The flags recover $U$ and each $U_i$. On $X=V/U$, the pairings with $U_{i-1}$ by $\omega_1$ and with $U_i$ by $\omega_2$ have the same kernel, and induce perfect pairings on $X_i$, their common quotient of $X$. This follows from the trace formula, where both use $x_i$. These two pairings identify $X_i$ with $U_{i-1}^*$ and $U_i^*$. Adjacent $X_i$ are thereby identified through their shared $U_i^*$.

Each input form $\omega$ gives two endomorphisms by dividing its pairing on $X_1\times U_0$ by the corresponding marked pairing, and dividing its pairing on $X_m\times U_m$ by the other marked pairing. Explicitly, a quotient-level operator $T$ satisfies $\omega(\bar x,u)=\omega_j(T\bar x,u)$ on the indicated spaces. These equalities determine $T$ by linear equations because the marked pairings are perfect. Every $\omega$ vanishes on $U\times U$ and shares the indicated pairing kernels by the cover formula. Transport the second operator to $X_1$ using the adjacent identifications. In normalized coordinates the identifications on $K$ are the identity, so the two operators for $\omega_{(a,b)}$ are precisely $x\mapsto ax$ and $x\mapsto bx$ on one copy of $K$.

In the other case every nonzero weight lies on one $K$-line. Normalizing the first mark to $(1,0)$, all forms have its radical. On the common radical quotient, define $T$ by $\omega(\bar x,\bar y)=\omega_1(T\bar x,\bar y)$. These are scalar multiplications by the normalized weights $a$ on $K^{2m}$.

In either case compute the unital algebra $F$ generated over $\mathbb F_p$ by the coefficient matrices of a form basis. Its generators are scalar operators, so $F$ is a subfield of a displayed copy of $K$. Repeatedly adjoining independent products of current basis elements computes its basis and structure constants using linear algebra in the ambient matrix space. Regard the corresponding coefficients of the forms as a subspace $S_F$ of $F^r$, where $r=2$ in the two-mark case and $r=1$ in the one-mark case. It contains the $r$ coordinate vectors, and its coefficients generate $F$.

## 3. Recover the isomorphism criterion

The zero form space gives an elementary abelian group, which can be compared by order. For nonzero form spaces, the dimension of a nonzero form radical gives $e$, and $\dim_{\mathbb F_p}V=(2m+1)e$ then fixes $m$. The prime and $r$ are also isomorphism invariants. Thus compare groups with these parameters equal.

An isomorphism induces a bijection of weight spaces preserving matched form radicals. In the two-mark case, first change the target cover coordinates so that the images of the two source marks become the two target coordinate weights. The induced domain map respects the entire flag and pairing construction. In particular it gives a map on $X_1$ simultaneously conjugating every paired coefficient operator to those of the corresponding target form. It induces an $\mathbb F_p$-field isomorphism on the algebra of scalar coefficients. In the one-mark case, normalize the image of the source mark instead, and use the relative operators on the common radical quotient. The same conjugation conclusion holds.

In cover coordinates the two coefficient fields are subfields of $K$. Equal degree makes them the same subfield of $K$, and their isomorphism extends to a Frobenius automorphism of $K$. Undoing the mark normalization gives a semilinear map on $K^r$ sending the source weight space to the target weight space. Conversely a semilinear map of the weight spaces extends in the one-mark case to a semilinear map on the full weight plane. Its inverse-transpose linear part, with the same Frobenius, maps their annihilators $N,N'$ onto each other by trace invariance. The lifted map on $H_m^\flat(K)$ then induces an isomorphism of the quotients.

This argument also shows why one arbitrary mark choice per input suffices for computation. In arbitrary normalized coordinates let $S_F\subseteq F^r$ and $S_{F'}'\subseteq (F')^r$. For any semilinear transporter $A\sigma$ between them, each column of $A$ is the image of a coordinate vector and belongs to $(F')^r$. The inverse matrix has columns in $\sigma(F)^r$ by the same argument on coordinate vectors of the target. Thus $A,A^{-1}$ have entries in both fields. Applying $A^{-1}$ to the target inclusion gives $\sigma(S_F)\subseteq (F')^r$. Applying $A$ to the source inclusion gives $S_{F'}'\subseteq\sigma(F)^r$. Since the respective coefficients generate their fields, $\sigma(F)=F'$. Consequently all transporters of interest can be sought just over the two generated fields, using isomorphisms between them.

## 4. A linear computation followed by a quadratic determinant test

Reject if the two generated fields have different dimensions over $\mathbb F_p$. Otherwise use Lenstra's deterministic algorithm to construct one isomorphism between them from their structure constants. The other isomorphisms are obtained by composition with the powers of Frobenius, of which there are $[F':\mathbb F_p]$. Frobenius evaluation is by binary powering. [Lenstra, *Finding Isomorphisms Between Finite Fields*](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf)

For each such isomorphism $\sigma:F\to F'$, form the $\mathbb F_p$-linear space
$$
 \mathcal M_\sigma=\{A\in M_r(F')\mid A\,\sigma(S_F)\subseteq S_{F'}'\}.
$$
Membership in $S_{F'}'$ is a system of linear equations over $\mathbb F_p$, and evaluating $A$ on a fixed source basis is linear in its $r^2[F':\mathbb F_p]$ coordinates. Solve for a basis $A_1,\ldots,A_h$ of $\mathcal M_\sigma$. Since the spaces being transported have equal dimension, inclusion under an invertible $A$ is equality. For $r=1$, a nonzero basis element suffices. For $r=2$, test the determinants of all basis elements and their pairwise sums. Indeed, the determinant of $\sum_i z_i A_i$ is the homogeneous quadratic with square coefficients $\det A_i$ and mixed coefficients $\det(A_i+A_j)-\det A_i-\det A_j$. If no test succeeds all coefficients vanish. A successful test provides an invertible transporter.

Each step uses polynomially many matrix operations in the dimensions of the compact form input and polynomially many bit operations in $\log p$ per field operation. The flag length is at most the matrix dimension, the field degree at most $e$, and the determinant test uses $O(e^2)$ candidates for each field isomorphism. The number of field elements never appears in the computation. This proves the deterministic compact-input bound.

## 5. Schrock's conjugation step for the smallest block

This answers Conjecture 4.4.2.5 for Algorithm 4.1 as specified in the thesis. In Step (1) the first scalar form has normalized matrix with first cross block $I_e$ and second block $0$. Its final $e$ coordinate vectors span its radical $R_1$. The nonzero final-column condition imposed in Step (2) means precisely that $R_1$ is distinct from the radical $R_2$ of the chosen second slice. Thus the two marks have $K$-independent weights. For $m=1$, $R_1\oplus R_2=U$ is isotropic for both forms. Choose any complement $W$ to $U$. The pairings $\omega_1:W\times R_2\to\mathbb F_p$ and $\omega_2:W\times R_1\to\mathbb F_p$ are perfect by the normalized trace model.

Construct linear maps $u_2:W\to R_2$ and $u_1:W\to R_1$ characterized by
$$
 \omega_1(w,u_2(w'))=-\omega_1(w,w')/2,\qquad
 \omega_2(w,u_1(w'))=-\omega_2(w,w')/2.
$$
Replace $W$ by the graph of $u_1+u_2$. For the first form, the $u_1$ terms vanish because they lie in its radical and all terms within $U$ vanish. The two $u_2$ terms sum to $-\omega_1(w,w')$ by skew-symmetry. For the second form, the same calculation uses $u_1$. Thus the new complement is isotropic for both. Keep a basis of the new complement, followed by the $\omega_1$-dual basis of $R_2$ and the $\omega_2$-dual basis of $R_1$. The resulting first matrix is exactly its normalized matrix from Step (1). The second is exactly the prescribed target of Step (3). Finding radicals, a complement and the two shear maps uses Gaussian elimination. If all radicals agree, Step (2) finds no valid second mark and the one-mark algorithm above decides that case. [Schrock, Algorithm 4.1 and Conjecture 4.4.2.5](https://math.colorado.edu/~tysc3584/Tyler_Schrock-PhD_Thesis.pdf#page=114)

## 6. The pointwise stabilizer for every flat block size

Use Schrock's row congruence convention $M\mapsto QMQ^{\mathsf T}$ and let $M_1,M_2$ be the two matrices with pure cross blocks $J_1,J_2$, with every nonzero block $I_e$ over $\mathbb F_p$. The flags and pairings in Section 2 apply with that identity pairing. They force any common isometry to preserve each $U_i$ and to act in the quotient on each $X_i$ by a common $D\in\operatorname{GL}_e(\mathbb F_p)$. To see the latter explicitly, the two cross pairings involving $X_i$ force the row action on $U_{i-1},U_i$ to be inverse transpose to the action on $X_i$, and $U_i$ occurs also at $X_{i+1}$. The other quotient coordinates cannot contribute to $X_i$ because they pair trivially with $U_{i-1}$. Thus the stabilizers are of the block form
$$
 Q=\begin{pmatrix}D^{\oplus m}&C\\0&D^{-\mathsf T\,\oplus (m+1)}\end{pmatrix}.
$$
Here $C_{i,a}$ is the shear from quotient position $i\in\{1,\ldots,m\}$ to terminal position $a\in\{0,\ldots,m\}$. Set $F_{i,a}=C_{i,a}D^{\mathsf T}$. The upper-left block of $QM_jQ^{\mathsf T}$ is zero precisely when
$$
 F_{i,j-1}=F_{j,i-1}^{\mathsf T}\quad(1\le i,j\le m),
 \qquad
 F_{i,j}=F_{j,i}^{\mathsf T}\quad(1\le i,j\le m),
$$
where the first equality corresponds to the first marked form and the second to the second. For $i\ge2$ and $a\le m-1$, these imply $F_{i,a}=F_{a+1,i-1}^{\mathsf T}=F_{i-1,a+1}$. So $F_{i,a}$ is constant on anti-diagonals. Those with $i+a$ odd contain a diagonal entry of the first symmetry equation, and those with $i+a$ even contain one of the second. Every anti-diagonal value is therefore symmetric. Conversely these anti-diagonal and symmetry conditions imply both displayed equations, hence fix the ordered pair.

Equivalently $C_{i,a}=E_{i+a}$ for $2m$ matrices $E_t$ satisfying $DE_t^{\mathsf T}=E_tD^{\mathsf T}$. This is the block-Hankel formula in §4.5, with the symmetry condition expressed in terms of its displayed diagonal block $D$. The formula describes the pointwise stabilizer of the two forms. [Schrock, §4.5](https://math.colorado.edu/~tysc3584/Tyler_Schrock-PhD_Thesis.pdf#page=120)

## 7. Arbitrary normal quotients

Work first in the Baer coordinates $V\oplus P$ of an original flat block. Any subgroup $N$ is an $\mathbb F_p$-linear subspace in these coordinates. Powers give scalar multiples because $b(v,v)=0$. For two elements of $N$, their commutator belongs to $N$ and so does half that commutator. Removing the half-commutator from their group product gives their ordinary sum. Set $C=N\cap P$ and let $W$ be the projection of $N$ to $V$. Modulo $C$, the subgroup $N$ is the graph of a linear map $W\to P/C$. Extend that map to a linear map $V\to P$ by choosing lifts and a complement, and subtract it from the center coordinates. This is an automorphism of the Baer group by linearity. It sends $N$ to $W\oplus C$. If $N$ is normal, $[N,H]\subseteq N$ gives $b(W,V)\subseteq C$. Thus the quotient is the Baer group of the projected bimap on $V/W$, with values in $P/C$.

Let $S=C^\perp$ be its weight space before dividing out $W$. If $S$ contains a $K$-independent pair of weights, the common radical of their forms is zero. Since $b(W,V)\subseteq C$, we have $W=0$, and the two-mark algorithm applies exactly as before. If $S=0$, the result is elementary abelian. For all remaining inputs $S$ lies on one $K$-line and is nonzero. Before dividing by $W$, all nonzero forms have the same radical $R$ by Section 1. After dividing by $W$, that radical is $R/W$. In a raw comparison, these three cases are distinguished by checking whether there are nonzero forms and whether two basis forms have distinct radicals.

In the one-mark case match the primes, dimensions of the common radical and dimensions of the quotient domain $Y=(V/W)/(R/W)$. The underlying covering block sizes can differ. Choose any marked nonzero scalar form $\omega_1$ on $Y$. Relative operators again identify every form with $\omega_a(x,y)=\omega_1(ax,y)$ for a coefficient $a$ in a generated field $F$. Let $S_F\subseteq F$ be the coefficient subspace. It contains $1$. An isomorphism can send the marked form to any nonzero target weight $c\in S_{F'}'$. Using this target form as the mark divides all target coefficients by $c$. The resulting coefficients generate the same field $F'$, because $1\in S_{F'}'$ implies $c^{-1}$ belongs to the divided space and $c$ can then be recovered in its generated field. Conjugation of relative operators therefore forces a field isomorphism $\sigma:F\to F'$ with $c\sigma(S_F)=S_{F'}'$.

Conversely, given such a field isomorphism and multiplier $c$, define the $F$-valued form $B$ on $Y$ by
$$
 \operatorname{Tr}_{F/\mathbb F_p}\bigl(tB(x,y)\bigr)=\omega_1(tx,y)\qquad(t\in F).
$$
The perfect trace pairing gives existence and uniqueness at each $(x,y)$. The formula is $F$-linear in $x$ by associativity of the field action. It is $F$-linear in $y$ because the scalar endomorphisms are self-adjoint for $\omega_1$, as seen in the cover trace formula. The same self-adjointness and odd characteristic give $\omega_1(tx,x)=0$ for all $t$, which proves alternation. Nondegeneracy of $\omega_1$ gives nondegeneracy of $B$. Construct $B'$ in the same way on the target. The dimensions over the two matched fields agree. Symplectic bases then give a $\sigma$-semilinear bijection $g:Y\to Y'$ with $B'(gx,gy)=c^{-1}\sigma(B(x,y))$, by scaling one member of each target symplectic pair by $c^{-1}$. Invariance of trace gives $\omega'_{c\sigma(a)}(gx,gy)=\omega_a(x,y)$ for every coefficient $a$. Extend by a linear bijection on the radicals to obtain a simultaneous isometry. It induces a group isomorphism by the Baer product.

This is the same one-dimensional transporter computation of Section 4 with the size comparisons just described. It applies equally to central quotients with a common radical and to quotients by noncentral subgroups. The compact algorithm therefore covers the whole flat-block quotient family.

## 8. Relation to the stated algorithm question

The thesis states Conjecture 4.4.4.5 for its outlined algorithm on the smallest block. The proof here establishes its polynomial-time isomorphism conclusion on compact inputs, also for larger flat blocks. It proves the specific missing Step (3) of Algorithm 4.1. Its final field-linear transporter is an explicit implementation of the kernel-orbit comparison, without assuming a polynomial-time orbit algorithm merely from a list of automorphism group generators. The targeted priority search found the thesis, the earlier genus-two algorithms for the original blocks, and Lenstra's field isomorphism algorithm. Publication priority for the compact quotient algorithm remains unestablished. [Schrock, Conjecture 4.4.4.5 and §4.5](https://math.colorado.edu/~tysc3584/Tyler_Schrock-PhD_Thesis.pdf#page=119) · [Brooksbank, Maglione and Wilson](https://arxiv.org/abs/1508.03033)
