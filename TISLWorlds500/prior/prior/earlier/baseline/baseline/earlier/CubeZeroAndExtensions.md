# Cube-zero commutative rings and finite extension fields

For a fixed finite field $F$, let $H(F)$ mean that special-linear three-tensor isomorphism over $F$ deterministically polynomial-time many-one reduces to ordinary three-tensor isomorphism over $F$. All tensor and ring inputs use dense coefficients in displayed ordered bases. A finite ring presented as a unital $F$-algebra isomorphism problem here uses $F$-linear unital maps. For prime $F$, every unital ring isomorphism fixes these scalars.

**Theorem.** Let $K/F$ be any extension of fixed finite fields. Write $m=|K^\times|$. Let $\mathcal C_K$ be the class of commutative unital local $K$-algebras with scalar residue, radical $J$, and
$$
 J^3=0,\qquad \operatorname{Ann}_J(J)=J^2,\qquad
 \dim_K(J/J^2)\equiv -2,\quad \dim_K J^2\equiv1\pmod m.
$$
Let $\mathsf C_K$ be ordinary isomorphism in this class and $\mathsf C_K^1$ determinant-one isomorphism in the displayed bases. Then:

1. $\mathsf{TI}(K)\equiv_m\mathsf C_K$ and $\mathsf C_K\le_m\mathsf C_K^1\le_m\mathsf{TI}_{SL}(K)$. On the indicated multiplication tables the output determinant-one test is equivalent to the three determinant-one tests and to $\mathsf C_K^1$.
2. $H(K)$ is equivalent to $\mathsf C_K^1\le_m\mathsf C_K$. An instance of $\mathsf{TI}_{SL}(K)$ is a conjunction of at most $m^3$ explicitly constructed $\mathsf C_K^1$ instances. Each algebra in this reduction has dimension linear in the sum of the three tensor side lengths, for fixed $K$.
3. $H(K)$ implies $H(F)$. More precisely, any prescribed determinant-character test on tensors over $F$ reduces to one $\mathsf C_K^1$ instance, with exact determinant-image preservation under $F^\times\subseteq K^\times$. Its dimension is $O_K((n_1+n_2+n_3+1)^{|F|})$ in general.
4. If $H(\mathbb F_3)$ fails, $H(\mathbb F_{3^r})$ fails for every positive integer $r$. On each of these fields the determinant-one problem in the displayed commutative local class has strictly larger many-one degree than ordinary algebra isomorphism in that class. The $\mathbb F_3$ assertion concerns scalar-residue rings of even total dimension, even first radical layer and odd second radical layer.

The proof constructs symmetric bilinear maps with specified transporter determinants. It gives an exact finite extension transfer by enforcing the base-field Frobenius condition on the matrix entries inside the larger field. The fixed fields enter the polynomial constants and exponents.

## 1. A typed system for prescribed coefficients

Put $q=|F|$, and let $T:V_1\times V_2\longrightarrow V_3$ be an input bilinear map over $F$, with the usual bimap convention for the first two mode maps. In the covariant tensor convention, invert the first two determinant weights. Compare only matching positive formats. Different formats give fixed no instances and matching formats having a zero side give fixed yes instances.

Extend the three spaces to $K$. If $F\ne K$, attach to each extended space $V$ the role spaces $\operatorname{Sym}^j_K V$ for $2\le j\le q$, the multiplication maps
$$
 V\times\operatorname{Sym}^{j-1}_K V\longrightarrow\operatorname{Sym}^j_K V,\quad 2\le j\le q,
$$
and the linear map $\iota:V\to\operatorname{Sym}^q_K V$ defined by $\iota(e_a)=e_a^q$ in the input coordinate basis. For $j=2$ the domain is $V\times V$ and the map is symmetric. Retain the three original roles and $T$. If $F=K$, take only the original roles and $T$.

A typed isomorphism consists of an independent invertible linear map on each role preserving all listed maps. Multiplication spans each successive symmetric power, so preservation forces the map on $\operatorname{Sym}^j V$ to be $\operatorname{Sym}^j(g)$. Commuting with $\iota$ says that every coefficient $c$ of $g$ satisfies $c^q=c$, by the $q$-power identity and linear independence of the $e_a^q$. Thus the three original maps have matrices over $F$, and every $F$-bimap transporter gives a unique typed isomorphism. This encoding also works when an input radical is nonzero or the image of $T$ is proper.

The total number of roles and constraints is bounded in terms of $F$. There is at most one bilinear constraint for any unordered pair of input roles. Every repeated-input constraint is symmetric. Each linear constraint will be assigned its own pin line. The construction below uses these properties of this system.

## 2. Put the system inside a symmetric bimap

Use $V_i$ now for all variable roles of the system, including auxiliary roles when present. Choose a positive integer $k_i$ whose residue modulo $q-1$ is the desired determinant weight on an original role, and is zero on every auxiliary role. All $k_i$ can be bounded in terms of $F$. Let the main input space $M$ be the sum of the variables, a pin line $Ke$, and $s$ further distinct pin lines $Kf_j$. There are enough pins to assign a distinct pin for every linear constraint and to reserve at least $m-1$ different pairs of further pins. Reserve separate pins for prescribed copying and linear constraints. Choose $s$ in the first usable residue class so that
$$
 D:=\dim_K M\equiv-1\pmod m.
$$
For copies numbered $1,\ldots,k_i-1$, a distinct pin per copy slot is sufficient and the same slots can serve all variable roles. These choices take a number of pins bounded in terms of the fields.

Define a symmetric bimap $\eta:M\times M\to W$ by specifying its output summands and nonzero blocks as follows. Unspecified blocks are zero.

- For each variable role $V_i$, take $k_i$ output copies $W_{i,\ell}$ of it. Multiplication by $e$ maps $V_i$ identically onto $W_{i,0}$. Each remaining copy is likewise obtained by multiplying $V_i$ by the reserved distinct pin for that copy slot. Each of these products lands only in that copy.
- A bilinear constraint with particular variable input roles and output role $V_k$ is the corresponding block into $W_{k,0}$. Use symmetry to define the reverse block when the roles differ. For each linear constraint $L:V_i\to V_k$, multiply its dedicated pin by $V_i$ using $L$ into $W_{k,0}$. There are no block collisions.
- Include one output line $Kz_*$ and distinct output lines $Kz_j$ for all further pins. Set $\eta(e,e)=\eta(e,f_j)=z_*$ and $\eta(f_j,f_j)=z_j$. If further adjustment is needed, use $h$ distinct pairs of different reserved pins with their products equal to independent new output basis vectors. Choose $0\le h<m$ to make $Q:=\dim_K W\equiv0\pmod m$, since each pair adds one.

Every output summand is spanned by the displayed products. The common radical of $\eta$ is zero. Pairing a vector with $e$ gives its variable components in the separate $W_{i,0}$. A radical vector hence has only pin coordinates. Pairing with $f_j$ detects its $f_j$ coordinate in the unique line $Kz_j$. Pairing with $e$ then detects its last coordinate.

Suppose an isomorphism of $\eta$ respects each input role, including each line. Let $\tau$ be its nonzero scalar on $e$. From $e^2=ef_j=z_*$, its scalar on every $f_j$ equals $\tau$. If its restriction to $V_i$ is $g_i$, the map on every $W_{i,\ell}$ is precisely $\tau g_i$ by the identity blocks, and pure pin output lines scale by $\tau^2$. Let $h_i=\tau^{-1}g_i$. Comparing the bilinear blocks gives $h_k B(x,y)=B'(h_i x,h_j y)$. The linear blocks give $h_k L=L'h_i$. Thus the normalized maps $h_i$ are a typed isomorphism. Conversely any typed isomorphism lifts by taking $\tau=1$, using the same maps on the output copies and identity on all pure pin lines. The determinant of the output map is
$$
 \tau^{2Q}\prod_i(\det_K h_i)^{k_i}
 =\prod_i(\det_K h_i)^{k_i}.
 \tag{1}
$$
The exponent vanishes because $m\mid Q$. The explicit output decompositions are transported blockwise since each summand is the image of a distinguished product, even when some of the constraint maps vanish.

## 3. Make all the roles intrinsic and cancel the auxiliary determinant

Choose $b\ge4$ no smaller than the number of roles of $M$, with $b\equiv -D\pmod m$. Make a cycle with $b$ vertices and a marker space $Z_0=\bigoplus_{a=1}^b Kz_a^0$. Assign a distinct vertex to each role of $M$, with extra vertices allowed. For every role include its dual in $P=M^*$, and give its evaluation on the original role values in the assigned marker line. Define these evaluations symmetrically in the two input arguments.

Write $u=|K|$, set $L=2m$, and choose a finite extension $E/K$ of degree $L$ and a primitive element $\theta\in E^\times$. All these field data are fixed constants. For each cycle edge $e'=\{a,c\}$ with a fixed ordering of the two vertices, use an input summand $S_{e'}=E^{r_{e'}}$. On it define two symmetric $K$-valued forms as the coefficients of $z_a^0,z_c^0$ respectively:
$$
 B_a(x,y)=\operatorname{Tr}_{E/K}\sum_j x_j y_j,\qquad
 B_c(x,y)=\operatorname{Tr}_{E/K}\theta\sum_j x_j y_j .
$$
Choose $r_{e'}$ positive, each larger than the sum of preceding $r_{e'}$ in a fixed ordering of edges, with $Lr_{e'}>D$. Since the number of edges is bounded in terms of $K,F$, all dimensions of these summands are $O_{K,F}(D+1)$.

Let
$$
 X=M\oplus P\oplus\bigoplus_{e'}S_{e'},\qquad Z=W\oplus Z_0.
$$
Define $\beta:X\times X\longrightarrow Z$ to be $\eta$ on $M$, the tagged evaluations for $M,P$, and the displayed forms on the anchor edge summands. All other blocks vanish. For each edge the trace pairing is nondegenerate and remains so after multiplication by any nonzero scalar in $E$. Since $\theta\notin K$, a combination of its two forms is nondegenerate whenever either coefficient is nonzero. The two forms are independent, so the values of $\beta$ span every marker line as well as $W$.

For any functional $\lambda\in Z^*$, the rank of the form $\lambda\beta$ is at most $D$ exactly when $\lambda$ vanishes on $Z_0$. A functional vanishing there gives a form supported on $M$. For any other functional, some incident edge supplies a restriction of rank $Lr_{e'}>D$. Consequently $Z_0$ and the common radical $X_0=P\oplus\bigoplus S_{e'}$ of all the low-rank forms are intrinsic. The formula for $X_0$ uses the zero common radical of $\eta$. The common radical of the marker-valued form on $X_0$ is exactly $P$. On $X_0/P$ the rank for a marker functional is the sum of $Lr_{e'}$ for the edges on which at least one endpoint coefficient is nonzero. The chosen weights determine the subset from its sum. The functionals vanishing on the endpoints of any specified edge thus form an intrinsic subspace, with annihilator the span of those two marker lines. Two incident edges intersect in exactly their shared vertex line, so each marker line is individually intrinsic.

The marker forms now recover each $S_{e'}$ on $X_0/P$ by intersecting the radicals of the forms at vertices outside that edge. This intersection is precisely its edge space because a different edge contains an outside vertex. The pairing $P\times(X/X_0)\to Z_0$ recovers each main role from the common kernel of the other roles' marker coordinates, and likewise the decomposition of $P$ into dual roles. In particular every transporter induces a role-preserving isomorphism of $\eta$ on $X/X_0$ with output $Z/Z_0$. The common radical of the full $\beta$ is zero. Any vector in it is first in $X_0$, then in $P$, then zero by the full evaluation against $M$.

Write $\alpha_a$ for the induced nonzero scalar on marker line $a$. For an ordered edge $\{a,c\}$ let $g$ be the induced map between its $E^{r_{e'}}$ space. Preservation of the two forms implies
$$
 g^{-1}M_\theta g=(\alpha_c/\alpha_a)M_\theta ,
$$
where $M_\theta$ denotes multiplication by $\theta$. Indeed $B_c(x,y)=B_a(M_\theta x,y)$, and $B_a$ is nondegenerate. If $\rho\theta$ with $\rho\in K^\times$ has the same minimal polynomial as $\theta$, it equals $\theta^{u^j}$ for $0\le j<L$. By primitivity, $\theta^{u^j-1}\in K^\times$ requires $(u^L-1)/(u-1)\mid u^j-1$, which for this range requires $j=0$. Hence the two marker scalars are equal. The cycle is connected, so there is one common scalar $\alpha$.

The same identity then makes $g$ $E$-linear. Testing its first trace-form equality after multiplying one argument by arbitrary elements of $E$ and using the nondegenerate trace pairing shows that $g$ is an $E$-bilinear dot-product similitude of multiplier $\alpha$. If $d=\det_E g$, then $d^2=\alpha^{r_{e'}}$. Therefore $d^{2m}=1$, and $N_{E/K}(d)=1$. For odd $u$, $d^2\in K$ implies $d$ lies in the degree-two subfield $K_2\subseteq E$, and $N_{E/K}(d)=N_{K_2/K}(d)^m=1$. For even $u$, squaring is bijective on both fields, so $d\in K$ and its norm is $d^{2m}=1$. Thus the determinant on each edge space over $K$ is one.

On the dual of a main role with map $G$ the induced action is $\alpha G^{-\mathsf T}$. The flag $P\subseteq X_0\subseteq X$ yields an $X$-determinant of $\alpha^D$ after cancelling every main-role determinant against its dual and using the edge calculation. On $Z_0$ the determinant is $\alpha^b$. No sign from a block permutation occurs, since ranks individually recover all roles. Coordinate bases use the same ordering of component bases at the two endpoints. The total determinant on $X\oplus Z$ equals the output determinant (1) because $m\mid D+b$. Conversely every typed transporter lifts: take each evaluation dual to be inverse transpose, act identically on marker lines and edge spaces, and use the lift of $\eta$ with $\tau=1$. This proves equality of the two determinant sets, including when they are empty.

## 4. The local ring and the comparison reductions

Take $A(T)=K1\oplus X\oplus Z$. Set the radical product of two $X$-coordinates to be $\beta$, and make every radical product involving $Z$ zero. This is commutative and associative and has local residue $K$. The radical is $J=X\oplus Z$, $J^2=Z$, $J^3=0$, and $\operatorname{Ann}_J(J)=Z$ because $\beta$ has zero common radical. The congruences are
$$
 \dim_K X=2D+\sum Lr_{e'}\equiv -2,\qquad
 \dim_K Z=Q+b\equiv1\pmod m .
$$
All algebra isomorphisms fix the unit and induce preservers of $\beta$ on $J/J^2,J^2$. Their determinant is the product of their determinants on the two layers. Conversely every such preserver lifts blockwise. Thus
$$
 \{\det_K\phi:\phi:A(T)\overset{\sim}{\longrightarrow}A(T')\}
 =
 \Big\{\prod_{i=1}^3 (\det_F g_i)^{w_i}:
             (g_1,g_2,g_3):T\overset{\sim}{\longrightarrow}T'\Big\}.
 \tag{2}
$$
Here the right-hand tuple is an original bimap transporter and the chosen weights $w_i$ include the covariant convention change if needed. The $k_i$ residue choices suffice since all normalized actions lie over $F$, including the actions on the auxiliary symmetric power roles. The dimensions of the auxiliary roles are $\binom{\dim V+j-1}{j}$, $j\le q$. All remaining dimensions are linear in the sum of role dimensions, and all coefficient formulas construct dense tables in polynomial time. Omit the auxiliary roles for $F=K$ to get the stated linear dimension bound.

For any finite-dimensional associative unital multiplication table, a bimap isotopy has the form $(L_a\phi,R_b\phi,L_aR_b\phi)$, with $\phi$ a unital algebra isomorphism and $a,b$ target units. Evaluating each input at the unit gives this identity by normalization and shows that the multipliers are units. In $\mathcal C_K$ every unit is $\lambda 1+j$, with $\lambda\in K^\times$, $j\in J$, and has both regular determinants $\lambda^{\dim A}=1$. The congruences give $\dim A\equiv0\pmod m$, and multiplication by $j$ is nilpotent. Thus all three isotopy determinants, using bimap coordinates, equal $\det\phi$. This proves the claimed reductions from the ring comparisons. The zero character in (2) gives $\mathsf{TI}(K)\le_m\mathsf C_K^1$ and $\mathsf{TI}(K)\le_m\mathsf C_K$. In particular fixed negative pairs of rings exist, by applying this construction to zero and nonzero matching tensors for the zero character. Using either ring in both positions gives a fixed positive pair.

For a tensor pair, the triples of determinants of ordinary transporters form either the empty set or a coset $aB$ in $(F^\times)^3$. Such a coset contains the identity precisely when every character maps it to a coset containing $1$. For separation use a character of the quotient by $B$ when $aB\ne B$. The trivial character detects the empty case. Formula (2) gives the stated fixed list of ring queries. If each oriented query reduces to ordinary TI, pack their resulting ordinary queries by the constant-signature tensor-system compiler. This use of conjunction concerns ordinary TI. The converse implication from $H(K)$ follows by composing $\mathsf C_K^1\le_m\mathsf{TI}_{SL}(K)$ with $H(K)$ and $\mathsf{TI}(K)\le_m\mathsf C_K$. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1 and Open Question 1.9](https://arxiv.org/html/2306.03135v2)

For the finite extension implication, $\mathsf{TI}(K)\le_m\mathsf{TI}(F)$. Restrict the three spaces and bimap to $F$, and include on each role the linear endomorphism given by multiplication by a specified generator of $K/F$. These four typed tensors have order at most three. A transporter of the typed system commutes with the generator on each role, so its maps are exactly $K$-linear. The same constant-signature compiler finishes the ordinary reduction. If $H(K)$ holds, apply (2) to each $F$-character test, followed by $\mathsf C_K^1\le_m\mathsf{TI}_{SL}(K)$, $H(K)$, and this ordinary restriction-of-scalars reduction. A fixed conjunction over $F$ produces $H(F)$.

## 5. Relation to earlier positive algebra models

For scalar-residue local algebras with $J^2=0$, the multiplication is determined by the dimension. If $J\ne0$, any invertible linear action on $J$ is an automorphism, so it supplies every determinant. The one-dimensional residue algebra is immediate as well, using the displayed unit coordinates to check its unique map. Thus the new cube-zero result reaches the shortest possible nontrivial radical length for conditional failure on scalar-residue algebras. The constructed class gives no detachable radical correction because $\operatorname{Ann}_J(J)=J^2$. Ordinary grade scaling acts by $t$ on $J/J^2$ and by $t^2$ on $J^2$, so its determinant is $t^{\dim(J/J^2)+2\dim J^2}=1$. The quotient has matrix size $1$. These facts match the scopes of the earlier detachable-radical, graded-scalar, and matrix-corner sufficient criteria. The construction keeps the orientation constraint and does not conflict with those criteria.

The extension implication is an implication between same-field deterministic many-one collapses with the fields fixed. It supplies no comparison in the reverse direction or between different characteristics, and no complexity bound polynomial uniformly in the binary field sizes is claimed. The proof is informal. Publication priority for the determinant-preserving ring and Frobenius constructions is unverified.


## 6. Bounded controls

Over $\mathbb F_3$, direct matrix elimination checked all 81 marker functionals on a four-edge trace-form cycle with edge dimensions $4,8,16,32$. The ranks gave the exact predicted active-edge sums. All four nonzero $d\in\mathbb F_{81}$ with $d^2\in\mathbb F_3$ had norm and regular determinant one. Over $\mathbb F_9$, explicit expansion of the cubed coordinate forms found precisely the 48 matrices in $\operatorname{GL}_2(\mathbb F_3)$ among all 5,760 matrices in $\operatorname{GL}_2(\mathbb F_9)$ satisfying the linear $\iota$ condition. These checks supplement the general proof.
