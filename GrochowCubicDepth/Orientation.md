# Sign-preserving integral tensor encodings in every degree

**Theorem.** Fix $d\ge2$. There is a deterministic polynomial-time map from dense homogeneous degree-$d$ forms in $n\ge1$ variables over $\mathbb Z$ to multiplication tensors of finite free commutative unital $\mathbb Z$-algebras. For two input forms, the realizable determinant triples of all ordinary integral tensor transporters are exactly
$$
\bigl\{(\det h,\det h,\det h)\ :\ h\in\operatorname{GL}_n(\mathbb Z)
                         \text{ transports the first form to the second}\bigr\}.
$$
Witnesses convert in either direction. In particular the same map reduces ordinary form equivalence to ordinary three-tensor isomorphism and determinant-one form equivalence to literal special-linear three-tensor isomorphism. Each output side has length $O_d(n^{\lfloor d/2\rfloor})$. For cubics the side length is at most $3n+19$.

A form transporter is written in the argument convention $f(x)=g(hx)$. Its sign agrees with the determinant sign of the inverse-transpose substitution on the coefficient module. All polynomial equalities are formal. The proof is informal.

## 1. Change even degree to odd while retaining the sign

For odd $d$, leave the input alone. For even $d$, let $v_f$ be the $2$-adic valuation of the positive gcd of the coefficients of a nonzero $f$. Set
$$
\kappa_f=2^{(d-1)v_f+d+1},\qquad
F_f(x,t)=t\bigl(\kappa_f f(x)+t^d\bigr),\qquad F_0(x,t)=t^{d+1}.
$$
An exact witness extends by fixing $t$, since unimodular substitution preserves the coefficient gcd. For recovery, a nonzero $f$ gives $F_f$ with unique rational linear factor $t$ of multiplicity one. In fact, a linear form with zero $t$ coefficient cannot divide the second factor, which is monic in $t$. Any other linear factor can be written as $t-L(x)$, and would imply $L(x)^d=-\kappa_f f(x)$. The coefficients of $L$ would be integers, since the pure $d$th-power coefficients of $L^d$ are integers. The minimum $2$-adic valuation of the coefficients of $L^d$ is $d$ times that of $L$: every coefficient has at least that valuation, and some pure coefficient attains it. On the other side the valuation is $dv_f+d+1\equiv1\pmod d$. The zero input is recognized by multiplicity $d+1$ of the unique linear factor.

Thus any unimodular substitution of the lifted forms has $(x,t)\mapsto(Sx+bt,\mu t)$ with $\mu=\pm1$ and $S$ unimodular. Compare the coefficient of $t^{d+1}$ modulo $4$. Since both multipliers are divisible by $4$, the equation is $\mu^{d+1}\equiv1\pmod4$, which forces $\mu=1$. This also holds directly for two zero inputs. Comparing the coefficients of $t^1$ now gives $\kappa_f f(x)=\kappa_g g(Sx)$ when both inputs are nonzero. Their coefficient-gcd valuations give $v_f=v_g$, so the multipliers coincide and $S$ is an exact transporter. The determinant of the full map equals $\det S$.

Let $q$ denote the resulting odd degree, so $q=d$ for odd $d$ and $q=d+1$ for even $d$. The degree adjustment adds at most one variable and at most polynomially many coefficient bits.

## 2. Add a few arithmetically distinguishable directions

For a degree-$q$ integer form $F$ on a lattice $X$, let $T_F$ be its unnormalized symmetric polarization, defined by the coefficient of $s_1\cdots s_q$ in $F(\sum_i s_i x_i)$. Over $\mathbb Q$ it is faithful and $T_F(x,\ldots,x)=q!F(x)$. The contraction radical is the kernel of $v\mapsto T_F(v,-,\ldots,-)$, and the contraction rank is its codimension. Compute this rank $c_0$ over $\mathbb Q$. If it is odd take $k=2$, and if it is even take $k=3$. Use the first $k$ odd primes $p_1,\ldots,p_k$ and set
$$
G_F(x,w)=2F(x)+\sum_{i=1}^{k}p_iw_i^q.
$$
This increases contraction rank to the odd integer $c=c_0+k\ge3$. The dimension of the contraction radical stays the same.

Let $A$ be an integral transporter of two such padded forms, initially allowing different numbers of markers. At each marker vector $e_i$ in the source the contraction has flattening rank one, viewing the $(q-1)$-linear form as a map from its first argument to the dual of the remaining tensor power. The unit coordinate vectors from distinct direct summands have disjoint domain and image supports in this flattening. Consequently the rank of the target contraction at $Ae_i$ is the sum of the rank on $X$ and the number of nonzero marker coordinates of $Ae_i$. Also the value on $Ae_i$ is the odd number $p_i$, so this vector has at least one nonzero marker coordinate by the factor $2$ on the original form. It follows that there is exactly one such coordinate, say $b$ on marker $j$, and the $X$ component lies in the contraction radical. Its contribution to the value is zero. Thus $p_i=p_j b^q$ with $b\in\mathbb Z$. Unique prime factorization gives $i=j$, and oddness of $q$ gives $b=1$. The polar equation with $q-1$ copies of $e_i$ and one vector of $X$ next forces the $i$th marker component of $A(X)$ to vanish. The target polarization on the original variables vanishes in that equation because the $X$ component of $Ae_i$ is radical. Therefore the marker diagonal block is the identity and the original diagonal block is an exact unimodular transporter with the same determinant. The converse extends a witness by identities. Recovery needs only the indicated diagonal block.

The same argument applies when the marker counts differ. Each prime in the source then occurs in the target, and applying the argument to the inverse gives equality of the marker sets.

## 3. The contraction algebra over the integers

For a padded form let $\Lambda$ be its variable lattice in the argument convention, of rank $N$. Let $T=T_{G_F}$, and let $D_0$ be its integral contraction radical. It is a saturated sublattice, being a kernel of an integer matrix with free codomain. Choose a complementary free sublattice $C$ of rank $c$, with bases on $D_0$ and $C$ whose concatenation has determinant $+1$ in the ordered coordinates of $\Lambda$. Equivalently $C$ represents $\Lambda/D_0$. The restriction of $T$ to $C$ has zero contraction radical over $\mathbb Q$.

Let $\tau:\operatorname{Sym}^q C\to\mathbb Z$ be the functional defined by products of $q$ arguments of $T$. For $1\le i<q$, write $B_i$ for the quotient of $\operatorname{Sym}^i C$ by the kernel of the map to $(\operatorname{Sym}^{q-i}C)^*$ induced by $\tau$. These quotients are free, as they identify with the image lattices. Set $B_0=\mathbb Z$, $B_q=\mathbb Zs$, and take higher degrees zero. The algebra $B$ uses ordinary multiplication of representatives below degree $q$, and uses $\tau(-)s$ for a product in degree $q$. The kernels defining $B_i$ form a homogeneous ideal in the positive degrees below $q$, since multiplying by a factor is equivalent to moving that factor into the complementary test. This proves well-definedness and associativity. The choice of a full top line $\mathbb Zs$ is allowed even if the image of $\tau$ is a proper sublattice of $\mathbb Z$. The attachment below generates that line.

We have $B_1=C$. Multiplication $B_i\times B_{q-i}\to\mathbb Zs$ is a rationally nondegenerate integral pairing. Define
$$
P=\sum_{i=1}^{(q-1)/2}\operatorname{rank}B_i .
$$
For each pair of complementary degrees choose bases whose pairing matrix has positive determinant. This can be done by changing the sign of one basis vector on the higher-degree side. Keep the already oriented basis on $B_1=C$. These choices fix the determinant convention for the entire tensor.

## 4. Add the multiplication markers and retain the determinant

Choose $b\in\{1,2\}$ so that
$$
c+qP+\frac{q(q+1)}2+b
$$
is even. Let $W_0$ have rank $b$, and let $W=\mathbb Zw\oplus W_0$. In degree one, besides $C$, put the inert space $D_0$, the space $W$, and a generator $z$. Add $z^2,\ldots,z^{q-1}$, and write $z^q=s$. The products of $z$ with positive degrees of $B$ vanish, as do those of $W$ with positive degrees of $B$ except for $wx$ with $x\in C$. Add the following degree-two spaces, all annihilating positive degrees:

- A copy $E_0$ of $W_0$, with $zv$ the copy of $v$ for $v\in W_0$.
- A copy $C'$ of $C$, with $wx$ the copy of $x$ for $x\in C$.
- Optionally a line $\mathbb Zu$ with $w^2=u$. Write $\varepsilon=1$ when this line is present and set $w^2=0$ when $\varepsilon=0$.

All remaining products involving $D_0$ or $W$ and positive degrees are zero. The $z$ powers multiply as indicated and truncate above degree $q$. These rules define a commutative associative unital graded algebra $A_F$. To verify associativity on three positive-degree basis elements, the new degree-two outputs kill the third element. A product of two positive degrees from $B$, or of two $z$ powers, can enter the other branch or a marker product only if it had degree one. Its degree is at least two. The shared top element kills all positive degrees. The remaining associativity equations are those of $B$ and of the truncated pure-power branch.

The rank is
$$
L=2P+N+q+2+2b+\varepsilon .
$$
Choose $\varepsilon\in\{0,1\}$ to make $L$ even. In the cubic case $P=c$, $b=2$, and $N\le n+3$, so $L=2c+N+9+\varepsilon\le3n+19$.

### Recover the form from an unmarked algebra witness

The positive ideal is the nilradical over $\mathbb Z$. It is generated in degree one and its powers are precisely the sums of the corresponding and higher degrees. Indeed all $B_i$ for $i<q$ are generated by degree-one products, all new degree-two elements have the displayed products, and $z^q=s$. Hence an algebra witness induces an integral isomorphism of associated graded algebras. In the following recovery work first over $\mathbb Q$. For each recovered subspace the corresponding integral sublattice is its intersection with the graded input lattice. All filtrations used for the determinant below split as lattice filtrations in the given bases.

1. The radical of the degree-one product, tested against degree one, is $D_0$. Testing against $z$ detects the $z$ and $W_0$ coordinates in the disjoint summands $\mathbb Qz^2$ and $E_0\otimes\mathbb Q$. Testing against $C$ then detects $w$ via the $C'$ summand and detects $C$ via its zero contraction radical.
2. The degree-two annihilator of degree one is $E=E_0\oplus C'\oplus\mathbb Qu$ if $\varepsilon=1$, and $E_0\oplus C'$ otherwise. Indeed $z^2$ has nonzero product with $z$. Any element of $B_2\otimes\mathbb Q$ killing $C$ pairs to zero with $B_{q-2}\otimes\mathbb Q$, which is generated by products of $q-2$ elements of $C$. Thus it vanishes.
3. Modulo $D_0$ in degree one and $E$ in degree two, the product has radical $W$. Inside $W$, the locus of multiplication rank at most one under the original degree-two product is $W_0$. A nonzero vector in $W_0$ multiplies only $z$ nontrivially. A vector with nonzero $w$ coefficient acts on $C$ with rank $c\ge3$.
4. In degree one modulo $D_0$, the annihilator of $W_0$ is $C\oplus W$. Thus the reduced degree-one quotient by $D_0\oplus W$ has an intrinsic $C$. The orthogonal complement of $C$ under the reduced product is the $z$ line, because $C\cdot z=0$ and the contraction on $C$ has zero radical.

The witness induces a map $R_0$ on $D_0$, a map $S$ on $C$, a scalar $a=\pm1$ on the recovered $z$ line, a map $J$ on $W_0$, and a scalar $\beta=\pm1$ on $W/W_0$. These are unimodular integer maps in the indicated bases. In the degree-one lifts of $C$ or $z$, additional components are in $D_0\oplus W$. They have no effect on a product of at least three such lifts, since every extra product in degree two lies in $E$. The relation $z^q=s$ forces the scalar $a^q$ on $s$, and products of $q$ vectors from $C$ give
$$
T'(Sx_1,\ldots,Sx_q)=a^q T(x_1,\ldots,x_q).
$$
Consequently $h_C=a^{-1}S$ is an exact isometry of the restriction to $C$. On the original variable lattice of the padded form, take $h_C\oplus R_0$ in the chosen decompositions. It is an exact isometry since $D_0$ is radical. Section 2 gives equality of the padding numbers and recovers the unpadded witness, and Section 1 removes the degree adjustment if used. Each of these operations preserves determinant.

Conversely a form witness extends through the arithmetic adjustments and induces $R_0$ and an exact $h_C$ on the contraction radical and quotient. Use the graded map on $B_i$ given by substitution by $h_C$, fix $z,w,W_0,s,u$, and use $h_C$ on $C'$ and $R_0$ on the inert space. This is well-defined since $h_C$ carries the complementary contraction kernels to each other, and it preserves all indicated products. The extension can omit any shear into the radical. Such shears do not enter the form or contribute a determinant factor.

### Compute the determinant

The determinant of the algebra witness equals that of its associated graded map. In that map the $z$ powers have scalars $a^j$ for $1\le j\le q$, after quotienting by $E$ in degree two. This contributes $a^{q(q+1)/2}$. The degree-two space $E_0$ is the product of $W_0$ with degree one, and its map is $aJ$. Together with $W_0$ this contributes $a^b(\det J)^2$.

The span of squares of $W$ is either zero or the line $\mathbb Qu$. Thus the existence of the optional line agrees on both sides of an isomorphism, and its scalar is $\beta^2$. Modulo $E_0$ and this square line, degree-two marker products $wx$ transform by $\beta S$ on $C'$. Together with the factor from $W/W_0$, their determinant is $\det(S)\beta^{c+1+2\varepsilon}$.

In degree two modulo $E$, the $B_2$ and $z^2$ parts are separately preserved since they are generated by the corresponding degree-one products. In all degrees $3\le i<q$, the $B_i$ and $z^i$ parts are separately preserved directly by generation and the vanishing of the extra degree-two terms against positive degrees. Let $P_i$ denote the resulting map on $B_i$ for $1\le i<q$. Write $K_i$ and $K_i'$ for the source and target pairing matrices in complementary degrees. The equation
$$
P_i^{\mathsf T}K_i'P_{q-i}=a^q K_i
$$
holds since the top line transforms by $a^q$. Both pairing determinants are positive. Taking signs of determinants shows that the product of the two signed determinants is $a^{q\operatorname{rank}B_i}$. Summing over the distinct complementary pairs gives the factor $a^{qP}$. This argument uses rational nondegeneracy of the pairing and does not require unimodularity of its matrix.

Multiplying these factors and the factor from $D_0$ gives
$$
\begin{aligned}
\det\phi
 &=\det R_0\det S\,
   a^{qP+q(q+1)/2+b}(\det J)^2\beta^{c+1+2\varepsilon}\\
 &=\det R_0\det h_C.
\end{aligned}
$$
Here $\det S=a^c\det h_C$, the exponent of $a$ is even by choice of $b$, and $c$ is odd. Orientation of the bases on $D_0$ and $C$ makes the final expression equal to the determinant of the recovered integral form transporter. When matched outputs have equal ranks, use the same order for all the displayed basis blocks on both sides so that filtration regrouping gives no permutation factor.

## 5. Transfer to the three tensor legs

Let $\mu_f$ denote the tensor of the resulting multiplication, in $A_F^*\otimes A_F^*\otimes A_F$. A tensor witness is equivalent to invertible linear maps $(P,Q,H)$ satisfying $H(xy)=P(x)Q(y)$, with literal tensor legs $(P^{-1})^*,(Q^{-1})^*,H$. Put $u=P(1)$ and $v=Q(1)$. Unit evaluation gives $H=L_vP=L_uQ$, where $L_a$ is multiplication by $a$. The maps $L_u,L_v$ are invertible, so $u,v$ are units. Then
$$
\phi=L_{(uv)^{-1}}H,\qquad
P=L_u\phi,\qquad Q=L_v\phi,\qquad H=L_{uv}\phi
$$
with $\phi$ a unital algebra isomorphism, by substitution into the product equation. Conversely any algebra isomorphism and any pair of target units give such a witness.

Every unit has constant coefficient $\pm1$ in the augmentation. Its multiplication map is triangular with that coefficient on the full diagonal. The target rank $L$ is even, so each unit multiplication has determinant $1$. Thus every literal tensor leg has determinant $\det\phi$, since the input-leg dual inverses do not change a sign. The determinant theorem follows in both directions.

All spaces through degree $q$ have polynomial rank for fixed $q$. Polarization, saturation via integer Smith normal form with basis transformations, and image-lattice coordinates via integer normal forms compute the free graded quotients and their multiplication tables in polynomial bit time. Ordinary elimination computes ranks and pairing determinants. In the even-degree lift, the exponent of $2$ in $\kappa_f$ is linear in the input coefficient bit length for fixed $d$. For $i\le(q-1)/2$, $\operatorname{rank}B_i\le\binom{c+i-1}{i}$, which gives side length $O_d(n^{\lfloor d/2\rfloor})$ after both adjustments. Dense trilinear tensor output still has polynomial bit size. [Kannan–Bachem](https://doi.org/10.1137/0208040)

## 6. A quadratic sign separation and literature scope

Consider $f(x,y)=2x^2+xy+3y^2$ and $g(x,y)=f(x,-y)$. The shortest nonzero vectors for $f$ are $\pm(1,0)$, since completing the square gives $2(x+y/4)^2+23y^2/8$ and hence value at least $3$ when $y\ne0$. An automorphism sends the first standard basis vector to $(s,0)$ and the second to $(m,t)$ with $s,t=\pm1$. Preservation of the polarized cross coefficient gives $s(4m+t)=1$, forcing $m=0$ and $s=t$. Both automorphisms have determinant $+1$, so all form transporters to $g$ have determinant $-1$. The lift $t(8f+t^2)$ is cubic with zero contraction radical. Its directional derivative in the $t$ direction has a nonzero $t^2$ term, while the derivatives in $x,y$ are independent multiples of $t$. Two markers give padded rank $N=c=5$. The theorem therefore produces an ordinary orbit pair of shape $24\times24\times24$ with determinant triple $(-1,-1,-1)$ for every transporter.

Grochow and coauthors' Part III studies several classical tensor actions and points to special-linear actions as a further direction. Part V proves equivalences of ordinary tensor actions over diagonal-full rings, including ordinary cubic-form equivalence over $\mathbb Z$. The construction here applies to the formal integral forms of each fixed degree $d\ge2$, and simultaneously retains the exact sign of a transporter in each tensor leg. It provides a reduction into a structured family of multiplication tensors. [Chen–Grochow–Qiao–Tang–Zhang, Part III, Section 1](https://arxiv.org/html/2306.03135v2#S1) · [Grochow–Qiao–Stange–Sun, Part V, Theorems 3.7 and 3.17](https://arxiv.org/html/2611.00735v1)

Additive splittings and contraction algebras have precedents in the theory of centers of higher-degree forms and Macaulay inverse systems. Earlier local-algebra encodings obtain exact scalar recovery with an auxiliary branch, and the field construction uses complementary-degree contraction. Over $\mathbb Z$ the same pairing need not be perfect as a lattice pairing. The orientation argument uses its positive chosen determinant, an extra copy of the concise first degree, and two independent parity adjustments. The arithmetic marker construction applies to forms with arbitrary contraction radical. Publication priority for the combination remains unverified. [Huang–Lu–Ye–Zhang](https://arxiv.org/abs/2009.12014) · [Elias–Rossi](https://arxiv.org/abs/0911.3565) · [Agrawal–Saxena, Theorem 2.3 and Section 6](https://www.cse.iitk.ac.in/%75sers/nitin/papers/cubic-forms.pdf)

The companion [Orientation.py](Orientation.py) checks all basis products and computes the actual algebra determinant for 24 signed integral witnesses at ranks 18, 20, and 36. These include both counts of $W_0$ markers, both choices for the square line, and a witness acting nontrivially on the contraction radical.
