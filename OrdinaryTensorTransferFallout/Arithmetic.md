# Compact power tests for ordinary tensor isomorphism

Ordinary tensors of side and rank linear in $k$ can first become isomorphic over a finite-field extension of degree $3^k$. They can also require precision $p^k$ to detect nonisomorphism over an equal-characteristic discrete valuation ring. Both results use a direct sparse compiler for one power equation, with explicit witness schemes over arbitrary commutative rings.

## 1. A power equation in two ordinary multiplication tensors

Fix an integer $N\ge2$. Use a straight-line chain of multiplication gates computing $x^N$ from $x$, with every intermediate power strictly increasing and with $L\le2\lfloor\log_2N\rfloor$ multiplication gates. For example, the binary method doubles the current exponent and, when the next bit is one, adds one by multiplying by $x$. Let $r=L+3$, counting the input and output registers and two extra registers $0,u$ along with the intermediate ones.

**Theorem 1.** Over any commutative ring $R$, let $a,b\in R$. There are two explicit ordinary tensors on free modules of side $15r+19$, both multiplication tensors of unital associative algebras, with these transporter schemes over $R$.
$$
\begin{array}{ll}
\text{initial register unconstrained:}&
 \{x\in\mathbb G_m:x^N=b\}\times \mathbb A_R^A\times\mathbb G_{m,R}^B,\\
\text{initial register constrained:}&
 \{x\in\mathbb G_m:x=a,\ x^N=b\}\times \mathbb A_R^A\times\mathbb G_{m,R}^B.
\end{array}
$$
The exponents $A=33r+27$ and $B=14r+31$ are the same for both choices. Tensor rank over any field probe is between the side and a fixed constant times the side. In the indicated bases all structure constants are in $\{0,1,a,b\}$, with only $O(r)$ nonzero entries. The witness formulas commute with arbitrary scalar extension.

*Proof.* Start with three vertices, an initial vertex $s$, middle vertex $m_0$, and terminal vertex $t_0$. On the corners $s\to m_0$, $m_0\to t_0$, and $s\to t_0$ place free rank-$r$ modules with bases $a_i,b_i,c_i$ indexed by registers. Denote the typed product in that order by $P(a_i,b_j)=b_j a_i$. Put in both algebras
$$
 P(a_0,b_0)=c_0,\qquad P(a_i,b_0)=P(a_0,b_i)=c_i\quad(i\ne0).
$$
At every gate with input registers $i,j$ and output register $k$, put $P(a_i,b_j)=c_k$ in both algebras. An ordered pair cannot occur twice in the chain, since it would give two registers of the same exponent. Also put $P(a_u,b_u)=c_u$, where $u$ is outside the gate chain.

Use the product on $(a_{\rm out},b_u)$ for the output constraint. In the source algebra set it to $bc_0$, and in the target to $c_0$. For the constrained version do the same on $(a_{\rm in},b_u)$ using $ac_0,c_0$, respectively. In the unconstrained version put zero in both tables for the latter product. The pairs of coordinates in all these rules are distinct.

For each $i$, add a private sink $x_i$ with rank-one corners $m_0\to x_i$, $s\to x_i$. Compose the first corner with $s\to m_0$ by the projection onto the $a_i$ coefficient. Also add a private source $y_i$ with rank-one corners $y_i\to m_0$, $y_i\to t_0$, and compose it with $m_0\to t_0$ by the projection onto $b_i$. Give every vertex its scalar diagonal and let it act on incident corners at the indicated endpoint. All unspecified strict products are zero. Every strict arrow goes from a source to the middle or a sink, or from the middle to a sink. Therefore all products of three strict elements vanish. This proves associativity, with the endpoint actions taking care of products involving a diagonal, and the sum of the diagonal idempotents is the unit.

For an isomorphism that preserves the specified idempotents, the two projection families force the maps on $a_i,b_i$ to act by individual units $\alpha_i,\beta_i$. Each projection kernel is the span of all lines other than the indicated line, and the lines are intersections of these spans. The three displayed initial products force the output map on $c_i$ to scale by $\alpha_i\beta_0=\alpha_0\beta_i$ for $i\ne0$, and on $c_0$ by $\alpha_0\beta_0$. Write $g_i=\alpha_i/\alpha_0=\beta_i/\beta_0$, with $g_0=1$. The extra product on $(a_u,b_u)$ requires $g_u^2=g_u$, hence $g_u=1$. Every gate now forces exactly $g_k=g_i g_j$; the terminal product forces $g_{\rm out}=b$, and the initial product in the constrained version forces $g_{\rm in}=a$. Conversely a solution of these equations, units $\alpha_0,\beta_0$, and the chosen units on the $2r$ first projection corners determine an isomorphism. The remaining projection maps are forced by their products. Thus the strict witness scheme is the indicated power scheme times $\mathbb G_m^{2+2r}$. It retains the power variable itself, with the section obtained by setting all extra units to one.

Use the rank-one label eraser on the algebra just constructed. Its old number of vertices is $v=3+2r$, its old strict rank is $7r$, and every directed path in the old strict support has length at most two. With the chain of length $v+3$, the decorated algebra has $w=2v+4$ vertices, $m=2v+3$ new rank-one arrows, and strict rank $j=7r+m=11r+9$. Ordinary multiplication-tensor transporters add $\mathbb A^{3j}\times\mathbb G_m^{m+2w}$ to the strict witness scheme. This gives the exponents, the side $w+j=15r+19$, and the precise base-change claim. All core products, diagonal actions, and added arrows have $O(r)$ nonzero coefficients. Each coefficient is attached to one basis product, yielding the upper rank bound by the coordinate expansion. Surjectivity of the output flattening follows by multiplication by the unit and gives the lower rank bound. $\square$ [Rank-one label eraser and exact transporter formula](Background/ArithmeticProof.md)

In the unpinned case, over a finite field $\mathbb F_Q$ the number of tensor isomorphisms is zero unless $b$ is a nonzero $N$-th power. If it is, the count is
$$
 \gcd(N,Q-1) Q^A (Q-1)^B.
$$
This follows from cyclicity of the multiplicative group. For $b=1$, this is a self-transporter and its source factor is the group scheme $\mu_N$.

## 2. Exponential compression over finite fields

**Corollary 2.** Over the fixed field $\mathbb F_7$, for each $k\ge1$ there are ordinary associative multiplication tensors of side and rank $O(k)$ whose exact extension profile is
$$
 T_0\simeq_{\mathbb F_{7^e}}T_1\quad\Longleftrightarrow\quad 3^k\mid e .
$$
They have exactly $3^k(7^e)^A(7^e-1)^B$ witnesses at every positive probe. Every pair of finite étale multiplication tensors with this same profile has side at least $3^k$.

*Proof.* Take $N=3^k$ and $b=2$ in the unpinned compiler. The element $2$ has multiplicative order three in $\mathbb F_7$. In a cyclic group of order $7^e-1$ it is a $3^k$-th power exactly when $v_3(7^e-1)\ge k+1$. Here $v_3(7^e-1)=1+v_3(e)$: a power of exponent prime to three preserves the valuation by the geometric sum, and cubing a number congruent to one modulo three adds exactly one because $z^2+z+1=3+3(z-1)+(z-1)^2$. This proves both the profile and the witness count. For an étale multiplication tensor pair, Frobenius acts by two permutations of the points of the spectra. Let $M$ be the common multiple given by the least common multiple of all cycle lengths. Over degree $M$ both permutations become trivial, so the pair accepts and $3^k\mid M$. Some cycle length is divisible by $3^k$, and the corresponding side is at least that large. $\square$ [Earlier sharp minimum for the finite étale subclass](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/SimultaneousComputabilityAndGrochow/FiniteFieldProfiles.md)

A version holds over every fixed finite field $\mathbb F_q$. Choose an odd prime $\ell>3$ dividing $q^2+q+1$. Such a prime exists since the sum is odd and at least seven, and it is either prime to three or has valuation one there. Work first over $\mathbb F_{q^3}$, take $N=\ell^k$ and $b$ of order $\ell^{v_\ell(q^3-1)}$, and use the existing fixed-degree restriction-of-scalars compiler to return to ordinary tensors over $\mathbb F_q$. Indeed $\mathbb F_{q^3}\otimes_{\mathbb F_q}\mathbb F_{q^e}$ is a product with factors $\mathbb F_{q^{\operatorname{lcm}(3,e)}}$; the images of $b$ in all factors retain its order. Since $\ell\ne3$, the same valuation calculation gives
$$
 v_\ell(q^{\operatorname{lcm}(3,e)}-1)=v_\ell(q^3-1)+v_\ell(e).
$$
For an odd $\ell$, this follows by the binomial expansion at a number congruent to one modulo $\ell$, with the first term having strictly smaller valuation than all other terms when taking the $\ell$-th power. Thus the returned ordinary pair has side $O_q(k)$ and accepts exactly the degrees divisible by $\ell^k$, while its finite étale counterparts need side at least $\ell^k$. The claimed rank bound in Corollary 2 concerns the direct multiplication construction. [Uniform restriction-of-scalars compiler](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/UniversalityConsequences/RestrictionOfScalars.md)

A purely inseparable counterpart uses the same direct construction over $K=\mathbb F_p(t)$, with $N=p^k$ and $b=t$. The pair accepts over $E/K$ precisely when $E$ contains $K(t^{1/p^k})$. The polynomial $X^{p^k}-t$ is Eisenstein for the valuation at $t$, and in the algebraic closure has only one distinct root. Thus the first finite accepting degree is $p^k$, achieved by a purely inseparable extension, and the ordinary tensors have side and rank $O(k\log p)$. Every finite separable extension rejects. These are quantitative statements about preserving one fixed input under extensions of its base field. They address that aspect of the across-fields question of Grochow and Qiao, and do not assert a complexity reduction between arbitrary base fields. [Open Question 7.6, journal version](https://par.nsf.gov/servlets/purl/10494304) · [Combined preprint, Open Question 10.6](https://arxiv.org/html/1907.00309#S10.SS2)

## 3. Exponential precision and exact higher-jet witness counts

Let $R=\mathbb F_p[t]$, $N=p^k$, and fix $q$ a power of $p$. Use $R_n=\mathbb F_q[t]/(t^n)$ and $\widehat R=\mathbb F_q[[t]]$.

**Corollary 3.** There are ordinary TI pairs over $R$ of side and rank $O(k\log p)$ with the following three properties.

1. A pair with structure constants only $0,1,1+t$ is isomorphic over $R_n$ exactly when $n\le N$, and is nonisomorphic over $\widehat R$. Its full transporter scheme is $\operatorname{Spec}R/(t^N)\times \mathbb A_R^A\times\mathbb G_{m,R}^B$.
2. Two self-transporter schemes of the same tensor format have identical absolute witness counts over every finite field of characteristic $p$, viewed over $\mathbb F_p$. Over $R_n$ the ratio of counts is exactly $q^{n-\lceil n/N\rceil}$.
3. For one of these self-transporters, the least truncation precision $m\ge n$ at which every self-witness modulo $t^m$ agrees modulo $t^n$ with a genuine self-witness over $\widehat R$ is exactly
$$
        \beta(n)=N(n-1)+1 .
$$

*Proof.* For part 1 choose the constrained pair with $a=1+t$, $b=1$. In characteristic $p$, the conditions $x=1+t$, $x^N=1$ are equivalent to $t^N=0$. The equality automatically makes $1+t$ a unit, so it is a scheme equality over the indicated base, not just equality at local rings. It gives the exact cutoff.

For parts 2 and 3 take the unpinned self-pair with output $b=1$, and compare with the self-pair where the initial register is pinned to $a=1$. The core and decorator use the same spaces and the same $A,B$. The source schemes are $\mu_N$ and a point, respectively. In a field of characteristic $p$, $\mu_N$ has only the point $1$. Over $R_n$, every element is uniquely represented as a polynomial of degree below $n$. The elements of $\mu_N(R_n)$ are exactly
$$
      1+t^{\lceil n/N\rceil}v,qquad
      v\in\mathbb F_q[t],\quad\deg v<n-\lceil n/N\rceil,
$$
since $(1+z)^N=1+z^N$ and distinct terms of $z$ give distinct exponents after Frobenius. This proves the ratio. Over the domain $\widehat R$, the normalized power coordinate of every genuine self-witness is $1$. The affine and unit coordinates lift freely from any quotient $R_n$ to $\widehat R$, with lifts of units remaining units. A witness modulo $t^m$ can therefore be matched modulo $t^n$ precisely when its normalized coordinate reduces to $1$. This holds for all such witnesses exactly when $\lceil m/N\rceil\ge n$. If the inequality fails, the witness with power coordinate $1+t^{\lceil m/N\rceil}$ and identity extra factors disproves the lifting statement. The least $m$ is $N(n-1)+1$. $\square$

For fixed $p$, parts 1 and 3 give exponential lower bounds in tensor side on uniform congruence precision, even for sparse ordinary multiplication tensors with coefficients affine-linear in the uniformizer. Part 1 concerns detection of global nonisomorphism over the complete discrete valuation ring. Part 3 concerns approximating genuine witnesses for a positive instance. Greenberg's theorem already gives an affine-linear lifting function for a fixed finite system over a complete discrete valuation ring. The example computes its exact slope in a concise family of ordinary TI systems. [Greenberg, rational points in Henselian discrete valuation rings](https://numdam.org/articles/10.1007/BF02684802/) · [Grochow–Qiao–Stange–Sun, tensor isomorphism over commutative rings](https://doi.org/10.1145/3717823.3718286)

## 4. Sharp exponential scale for stabilizer component element orders

**Theorem 4.** Let $T$ be any ordinary three-tensor over a field of characteristic $p\ge0$ with positive mode dimensions $d_1,d_2,d_3$. Let $s=d_1+d_2+d_3$, $d=\max_i d_i$, and $G$ be the geometric stabilizer in the product of the three general linear groups. Every element of the finite geometric component group $\pi_0(G)$ has order at most
$$
 3^{(s-2)/2}
 \begin{cases}
  1,&p=0\text{ or }p>s-3,\\
  p^{\lceil\log_p d\rceil},&0<p\le s-3.
 \end{cases}
]
In particular $s^2 3^{(s-2)/2}$ is a characteristic-independent bound. The exponential scale in $s$ is attained over the fixed field $\mathbb F_7$.

*Proof.* Work over an algebraic closure and use the reduced stabilizer, which has the same geometric points and components. Choose a representative $g$ of the given component. Its multiplicative Jordan decomposition $g=g_s g_u=g_u g_s$ has both parts in the stabilizer. Denote the corresponding components by brackets.

Diagonalize each mode of $g_s$ in a chosen basis, and use $D=\mathbb G_m^s$ for the full diagonal group in those bases. The scheme $D\cap G$, or its reduction for component purposes, is defined by monomial equations
\[
 x_i y_j z_k=1
]
for the nonzero coefficients of $T$ in the chosen bases. Let $L\subseteq\mathbb Z^s$ be the lattice generated by the corresponding weight rows, each a row with three entries one, one from each mode, and all other entries zero. The character group of the diagonal group cut out by these equations is $\mathbb Z^s/L$. Its number of geometric components is at most the order of the torsion subgroup of this quotient. Indeed Smith normal form writes it as a product of a torus and groups $\mu_a$, with $\mu_a$ contributing at most $a$ geometric points. The identity component maps into $G^0$, so the order of $[g_s]$ divides the number of geometric components of $D\cap G$.

Write $r_L=\operatorname{rank}L$. The two vectors constant on each mode with respective triples of values $(1,-1,0)$ and $(1,0,-1)$ are independent vectors in the kernel of all the rows. Hence $r_L\le s-2$. The torsion order is the greatest common divisor of the nonzero $r_L$-rowed minors, with order one in rank zero. Hadamard's inequality bounds each such minor by $3^{r_L/2}$, since each restricted row has Euclidean norm at most $\sqrt3$. Therefore $\operatorname{ord}[g_s]\le3^{(s-2)/2}$.

For $g_u=(U_1,U_2,U_3)$, put $N_i=U_i-I$, so $N_i^{d_i}=0$. In positive characteristic, the power $p^{\lceil\log_p d\rceil}$ kills every $U_i$ by Frobenius. To get the improved bound when $p=0$ or $p>s-3$, define polynomial matrices
\[
 U_i(z)=\sum_{j=0}^{d_i-1}\binom{z}{j}N_i^j .
$$
All factorials used are invertible, since $j\le d_i-1\le s-3$. The matrices are invertible for all $z$: each is the identity plus a nilpotent polynomial in $N_i$ with zero constant coefficient. The tuple agrees with powers of $g_u$ at every nonnegative integer in characteristic zero and at every element of the prime field in positive characteristic, taking the representative in $0,\ldots,p-1$. Its tensor defect is a polynomial of degree at most $\sum_i(d_i-1)=s-3$. It vanishes identically because it vanishes at infinitely many integers in characteristic zero, or at $p>s-3$ distinct points in positive characteristic. Thus the curve $z\mapsto(U_i(z))_i$ lies in the stabilizer and connects the identity to $g_u$ in its identity component. This gives $[g_u]=1$ in those characteristics. When $p\le s-3$, the original $p$-power bound is at most $pd\le s^2$. The two commuting components of $g$ give the asserted product bound.

For the lower bound, Theorem 1 with $b=1$ gives an ordinary self-transporter with stabilizer scheme isomorphic to $\mu_{3^k}\times\mathbb A^A\times\mathbb G_m^B$ over $\mathbb F_7$. The power coordinate is a group homomorphism by the normalized strict witnesses, and its identity-coordinate fiber is connected. Therefore the geometric component group is cyclic of order $3^k$. The side is $O(k)$, so this gives orders exponential in $s$. $\square$ [Milne, multiplicative Jordan decomposition in algebraic groups](https://www.jmilne.org/math/CourseNotes/ALA.pdf)

If a geometrically nonempty transporter over a finite field has a constant geometric stabilizer component group, its first accepting extension degree is the order of one component element. To see this, choose a geometric transporter component as an origin for its component torsor. Frobenius then acts by translation by one group element because the group action on the components is constant. All its orbits have the length of the order of that element. A fixed component has a rational transporter by Lang's theorem for the smooth reduced identity component. Thus Theorem 4 bounds the first degree in this case. For general nonconstant component groups, Frobenius also acts through an automorphism of the group, so the element-order theorem by itself gives no upper bound of the same scale for the first degree. [Lang, algebraic groups over finite fields](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf)

These are written proofs. The new results are the logarithmic-size explicit power compiler and its exact consequences on finite-field size, inseparable degree, and congruence precision, together with the component element-order bound. The mark normalization and earlier étale lower bound are reused with their original scope.

## 5. Linear PC degree for arbitrary scalar-block inputs

**Theorem 5.** Suppose every named block of each of the three modes of a block-preserving comparison is one-dimensional. Put $s$ for the sum of the three dimensions. The ordinary outputs of the ordered-path block eraser have side $O(s+1)$. Every geometrically negative pair of these ordinary tensors has raw PC degree $O(s+1)$ and a polynomial-size Hilbert-like IPS circuit refutation. Over $\mathbb F_q$ every negative pair has PC degree $O(q(s+1))$ with the field equations and a Hilbert-like IPS circuit of size polynomial in the input format and $\log q$.

*Proof.* In the covariant block system an isomorphism on each line is a scalar $x_i$ with designated inverse $y_i$ and relation $x_i y_i=1$. A support mismatch gives a monomial in units equal to zero, which refutes the system by multiplying by its named inverse. Otherwise the remaining equations have the form $x^{a_j}=\rho_j$, with $\rho_j$ a nonzero scalar and $\|a_j\|_1\le3$: at every nonzero tensor position one scalar occurs from each mode. It suffices to consider the subgroup $L\subseteq\mathbb Z^s$ generated by the $a_j$. The numbers $\rho_j$ extend to a character $L\to\overline{k}^{\,\times}$ exactly when every integer dependence $\sum_j m_j a_j=0$ has $\prod_j\rho_j^{m_j}=1$. A character of $L$ always extends to $\mathbb Z^s$ over the algebraic closure, by Smith normal form and existence of roots. Therefore a negative comparison supplies a dependence with nontrivial scalar product. In the finite-field version adjoin $x_i^{q-1}=1$ to this system, as consequences of $x_i^q=x_i$ and $x_i y_i=1$. These equations force all $x_i$, and hence all $y_i$, into $\mathbb F_q^\times$ over the closure. The same character criterion now applies to the augmented rows.

For a signed step $\nu=\pm a_j$ represent $x^\nu$ by the polynomial $[x^\nu]=x^{\nu^+}y^{\nu^-}$, where the positive and negative parts are nonnegative. This notation applies to any integral vector. The reverse step has scalar $\rho_j^{-1}$ and its equation follows by multiplying the forward equation by its inverse monomial and cancelling factors $x_i y_i$. Let $B\ge1$ bound the largest $\ell_1$ norm of the steps, with $B=3$ in the raw system and $B=\max(3,q-1)$ after adjoining the finite-field equations. Pick a violating dependence with the smallest sum of absolute multiplicities. View it as a multiset of signed steps. By the Steinitz rearrangement theorem in the $\ell_1$ norm, the steps can be ordered so every partial sum has norm at most $Bs$. From each signed step equation derive
$$
 [x^{v+\nu}]-\rho[x^v]=0
$$
by multiplying by $[x^v]$ and repeatedly cancelling factors $x_i y_i$ using the inverse equations. Here $v$ is the preceding partial sum and $\rho$ the signed scalar. The degree throughout is at most a constant times $B(s+1)$. A scalar-weighted telescope along the walk now gives the nonzero constant $1-\prod_j\rho_j^{m_j}$, with no larger degree. This gives the two claimed degree bounds after the constant-factor compiler transfer. [Grinberg and Sevast'yanov, Steinitz rearrangement bound](https://www.mathnet.ru/eng/faa1805) · [Ordered-path compiler](Background/MarkerProof.md)

For the IPS bound, the same shortest walk has no repeated partial sum, except its initial and terminal values. A proper closed consecutive portion with nontrivial scalar product contradicts minimality, and one with trivial scalar product could be deleted to obtain a shorter violation. There are at most $2^s\binom{Bs+s}{s}$ integral vectors in the allowed ball, by taking coordinate absolute values and then signs. For fixed B this is exponential in the sum of the mode dimensions, and the expanded PC walk uses only polynomial overhead per step. The monomial readout therefore gives a raw expanded PC size upper bound exponential in the ordinary side, also with field equations for fixed q. [Sparse transfer at arbitrary degree](Mixed.md) Hence each $m_j$ has bit length $O(s\log(B+s+1))$. Instead of listing the walk, take the product of the signed monomial equations, with powers $|m_j|$, by repeated squaring. At each multiplication, the difference of products is a sum of two terms using the preceding differences. This stores a polynomial-size vector circuit of coefficients in the original equations. The monomial obtained from all products has equal nonnegative exponents on $x_i,y_i$ separately for each $i$, because the signed total step is zero. Repeated squaring and telescoping reduce that product to one using $x_i y_i=1$, with polynomial circuit size in the bit lengths. Subtract the nontrivial scalar product and divide by the resulting nonzero field constant. The axiom $x_i^{q-1}=1$, when used, has the short representation $y_i(x_i^q-x_i)-(x_i^{q-1}-1)(x_i y_i-1)$. Both the field-power and coefficient circuits use repeated squaring. Finally the full compiler has polynomial circuit overhead by its shared-coefficient certificate transfer. $\square$ [Circuit transfer through label erasure](Background/LabelProof.md)
