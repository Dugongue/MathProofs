# Bit-polynomial special-linear isomorphism for regular pencils

Let $K=\mathbb F_q$ be given in an explicit finite-field representation. Identify a $2\times n\times n$ tensor with a homogeneous matrix pencil $P(x,y)=xA+yB$. The three special-linear actions ask whether
$$
 Q(v)=L\,P(Mv)\,R
 \quad\text{for}\quad
 M\in\operatorname{SL}_2(K),\quad L,R\in\operatorname{SL}_n(K).
$$
Here $v=(x,y)^{\mathsf T}$. Transposing the right factor or using inverse substitutions gives the same decision problem. Write $D_P(x,y)=\det P(x,y)$ and call $P$ regular if $D_P\ne0$.

**Theorem.** There is a deterministic algorithm, polynomial in $n,\log q$, for $\operatorname{SL}_2(K)\times\operatorname{SL}_n(K)^2$ orbit equivalence of regular pencils whose determinant forms have at least three distinct roots in $\mathbb P^1(\overline K)$. The roots need no labels or factorization. This includes pencils with no rational determinant root and pencils with no invertible rational slice. Over a fixed finite field, the same decision result holds for all regular pencils, without a condition on the number of roots. Since this is direct decision in polynomial time, it gives a same-field deterministic many-one reduction to ordinary tensor isomorphism on the stated family.

The algorithm uses projective root triples in an explicitly represented finite reduced algebra, with a Frobenius equation ensuring that candidate transformations are rational. A separate determinant calculation enforces all three special-linear conditions. Computing a transporter is outside the claim.

## 1. Strict equivalence and its determinant coset

Call two pencils strictly equivalent if they match by invertible left and right factors with the slice variables fixed.

A regular pencil $xA+yB$ can be split deterministically by linear algebra. Start with $U_0=0$ and $U_{i+1}=B^{-1}(A U_i)$. These spaces form an increasing chain. Write $U$ for its stationary value. The restriction of $A$ to $U$ is injective. Otherwise for a nonzero $u_j\in U_j\cap\ker A$ there are $u_i\in U_i$ with $B u_1=0$ and $B u_i=A u_{i-1}$ for $2\le i\le j$. Then $\sum_{i=1}^j z^{i-1}u_i$ is a nonzero polynomial kernel vector for $B-zA$, contradicting regularity. Also $B$ induces an isomorphism between the source modulo $U$ and the target modulo $A U$, by the stationary equation and equality of dimensions. Choose adapted frames and write
$$
 A=\begin{pmatrix}I&A_{12}\\0&C\end{pmatrix},\qquad
 B=\begin{pmatrix}N&B_{12}\\0&I\end{pmatrix}.
$$
The map $N=(A|_U)^{-1}(B|_U)$ is nilpotent since $N U_i\subseteq U_{i-1}$. Unipotent right and left factors with upper blocks $X,Y$ eliminate the off-diagonal entries by solving
$$
 X-NXC=-A_{12}+B_{12}C,\qquad Y=-NX-B_{12}.
$$
The first inverse is the finite geometric sum for the nilpotent operator $X\mapsto NXC$. This splits the pencil into the blocks $(I,N)\oplus(C,I)$.

Every strict equivalence preserves the chains and hence the induced maps on $U$ and the quotient. It induces similarities on $N$ and $C$. Conversely similarities of these two matrices give a strict equivalence of their split pencils. Constructive Frobenius normal form deterministically tests similarity, obtains a conjugator if one exists, and gives the invariant factors, in polynomially many field operations. Compose these conjugators with the computed frame changes and unipotent factors. This constructs one strict transporter $(L_0,R_0)$ and computes the invariant factors using only arithmetic and zero tests. [Berger–Ilchmann–Trenn, quasi-Weierstraß form and Wong sequences](https://doi.org/10.1016/j.laa.2009.12.036) · [Storjohann, constructive Frobenius normal form](https://cs.uwaterloo.ca/~astorjoh/p101-storjohann.pdf)

If $(L,R)$ fixes a regular pencil, comparison of its nonzero determinant polynomial gives $\det L\det R=1$. For either split block, the automorphisms are exactly $(Z,Z^{-1})$ with $Z$ commuting with the respective matrix. There are no off-diagonal automorphism blocks: in the notation $Y A=A X,\ YB=B X$, both $X,Y$ preserve their respective distinguished subspaces, and the remaining off-diagonal equations give $X_{12}=NX_{12}C$, forcing $X_{12}=Y_{12}=0$. Let $g$ be the greatest common divisor of the positive elementary-divisor exponents of $N$ and $C$. The image of the left determinant of the pencil stabilizer is $(K^\times)^g$.

For the image assertion, regard either matrix as a $K[z]$-module. Distinct primary summands do not mix. In a primary summand $\bigoplus_j(K[z]/(f^j))^{m_j}$ put $\kappa=K[z]/(f)$. Filter by powers of $f$. Maps from a shorter summand to a longer one are divisible by the difference of the powers of $f$, so the action on each layer is block triangular by lengths. The diagonal matrix $Z_j$ on the length-$j$ summands modulo $f$ occurs on each of their $j$ layers. It is invertible because the action on the first layer is invertible and block triangular. Thus the determinant on this primary summand is
$$
 \prod_j N_{\kappa/K}(\det_\kappa Z_j)^j .
$$
Conversely any such invertible $Z_j$ lifts on its summand over $K[z]/(f^j)$. The norm of finite fields is surjective. Taking the product over present lengths gives precisely the subgroup generated by the $j$-th power subgroups, which is $(K^\times)^g$. The required exponents come from squarefree decomposition of the invariant factors, with no irreducible factorization. A factorization-free implementation is described below. [Mingueza–Montoro–Roca, centralizer structure and determinants](https://arxiv.org/abs/1909.06198)

Fix a candidate projective slice map $[M]$ and take any representative $M\in\operatorname{GL}_2(K)$. Reject it if strict equivalence of $P\circ M$ and $Q$ fails. Otherwise put
$$
 \delta=\det L_0,\qquad \Delta=\det L_0\det R_0.
$$
A scalar lift $\lambda M$ rescales the pencil by $\lambda$, and the strict transporter can be adjusted to $(L_0,\lambda^{-1}R_0)$. All left determinant choices now form $\delta(K^\times)^g$, and every pair has product determinant $\lambda^{-n}\Delta$. It follows that the projective candidate works if and only if
$$
 \delta^{(q-1)/\gcd(g,q-1)}=1,\qquad
 \exists\lambda\in K^\times:\quad \lambda^2=(\det M)^{-1},\quad \lambda^n=\Delta.
 \tag{1}
$$
For sufficiency, choose a stabilizer factor correcting the left determinant after the product has been set to one. The right determinant is then also one. The power test uses cyclicity of $K^\times$, and the scalar test is a common-root test with $X^q-X$. Modular exponentiation modulo the monic quadratic $X^2-(\det M)^{-1}$ takes polynomial time in $n,\log q$.

## 2. Rational projective maps from geometric roots

A square pencil determinant can be computed symbolically using fraction-free determinant computation over $K[z]$ on $P(z,1)$, then homogenizing back to degree $n$. The regularity assumption makes this univariate polynomial nonzero. Let $f_P$ be its monic squarefree radical. The affine determinant roots are represented by the reduced algebra $K[z]/(f_P)$ and the point $[z:1]$. Adjoin a direct factor $K$, with point $[1:0]$, precisely if $D_P(1,0)=0$. Omit the affine algebra if $f_P=1$. This produces a finite reduced $K$-algebra $A_P$ of dimension at most $n$. Define $A_Q$ likewise.

Here is one implementation of the needed factorization-free polynomial computations. For monic $h$ let $h'=\partial h/\partial z$, and put $u=h/\gcd(h,h')$. Each irreducible factor over a finite field is separable. Consequently $u$ is the product, once each, of the factors whose multiplicity is not divisible by the characteristic. Strip their full powers by computing $\gcd(h,u^{\deg h})$. The remaining polynomial is a characteristic-$p$ power. Take its $p$-th root by extracting coefficients and using inverse Frobenius $a\mapsto a^{q/p}$ in $K$, and recur to compute its radical. The two sets of factors are disjoint. This computes the monic radical in polynomial time. To find the multiplicities that occur, set $h_j=\gcd(h,\partial^{[1]}h,\ldots,\partial^{[j]}h)$, with the Hasse derivative defined by the coefficient of $w^j$ in $h(z+w)$. A root of multiplicity $i$ occurs in $h_j$ exactly when $j<i$, by Taylor expansion at the root. Therefore $i$ occurs exactly when the squarefree radicals of $h_{i-1}$ and $h_i$ have different degree. This also gives the elementary-divisor lengths needed for (1).

Use the algebra
$$
 A=A_P^{\otimes 3}\otimes_K A_Q^{\otimes 3}.
$$
It represents ordered triples of source roots and ordered triples of target roots over $\overline K$. Over this field it is a product of at most $n^6$ copies of $\overline K$. Hence over $K$ it is a finite reduced algebra, a product of finite field extensions, though no decomposition is constructed. If $[v,w]$ denotes the determinant of two coordinate columns, localize at the product of all pairwise brackets within each triple. In a finite reduced algebra localization at $a$ is computed as the quotient by the kernel of the $K$-linear multiplication map by $a$. This removes exactly the components where $a=0$.

On the resulting algebra the triples are distinct. The projective frame map associated with a triple $s=(s_1,s_2,s_3)$ sends a column $v$ to
$$
 \phi_s(v)=
 \bigl([v,s_1][s_3,s_2],\ [v,s_2][s_3,s_1]\bigr)^{\mathsf T}.
$$
It sends the triple to $[0:1],[1:0],[1:1]$ and has unit determinant. For the target triple $u$, compute $M=\phi_s^{-1}\phi_u$. This is the unique projectivity sending $u_i$ to $s_i$ at each geometric point. Every valid slice map occurs, since its pullback carries the full source determinant-root set to the target set and each set has at least three roots. The construction may include other triples, which will later be tested by strict equivalence.

Cover the projective candidates by four charts. In each, invert the selected entry of $M$ and divide by it so that it becomes one. For every normalized entry $a$, quotient the algebra by the ideal generated by $a^q-a$. Each component is a finite field containing $K$, where the equation $a^q=a$ means $a\in K$. Thus every retained point specifies a projective map with a representative over the original field, including maps built from nonrational triples. Conversely if the projective map is $K$-rational, normalizing any nonzero entry gives constant entries in $K$, so at least one of the four charts retains each tuple representing it. Multiplication matrices and repeated squaring compute all these quotients and powers in polynomial time.

## 3. Evaluating the strict-equivalence test on the candidates

Run Section 1 on the pencils $P\circ M,Q$ over each chart algebra at once, with branches only when necessary. Whenever an arithmetic routine tests whether $a=0$ or needs to divide by $a$, split into the nonzero part $A/\ker(m_a)$ and the zero part $A/(a)$, where $m_a$ is multiplication by $a$. This exactly realizes the two branches componentwise without finding any factor field. A split with both pieces nonzero partitions dimensions. Across a full evaluation there are at most $\dim_K A$ terminal pieces, and each path uses only polynomially many operations of the original field routine. In particular Gaussian pivots and constructive Frobenius forms are valid with no enumeration of field elements. The input coefficients of each specialized $P\circ M$ are in $K$. Because all arithmetic steps and equality tests start from $K$ and use only field operations and constants of $K$, their componentwise outputs are precisely the chosen computation over $K$, regardless of the auxiliary residue-extension degrees. This point is needed for the left determinant coset over $K$.

Discard pieces failing strict equivalence, then impose the membership equation in (1) by a quotient of the chart algebra. The remaining scalar condition can be tested by adjoining a root of the monic quadratic $X^2-(\det M)^{-1}$ and quotienting by $X^n-\Delta$ and $X^q-X$. The final algebra is nonzero precisely when some retained point has a scalar $\lambda$ satisfying (1). The extra Frobenius equation again forces a root in $K$, even in characteristic two, when the quadratic can be inseparable. Adjoining $X$ multiplies the vector-space dimension by at most two. All computations are deterministic and polynomial in $n,\log q$. The polynomial exponent in $n$ here is a bound from elementary algebra arithmetic. It does not depend on $q$.

If $q$ is fixed, simply enumerate $M\in\operatorname{SL}_2(K)$ and apply the strict left-right test to each. The same method is bit-polynomial on any regime where $q$ is polynomially bounded in the input length. The reduction to TI on this promise family returns $(1,1)$ in tensor format $1\times1\times1$ after a positive decision and $(1,0)$ after a negative one, over the same $K$.

## 4. Determinants really matter

Over $\mathbb F_3$, use the block pencil
$$
 P=(xI_2+yJ_2(0))\oplus(xI_4+yJ_4(1))
                     \oplus(xJ_6(0)+yI_6),
$$
where $J_d(a)$ is a single Jordan block. Its determinant has three roots with distinct multiplicities $2,4,6$. Let $Q=D P D^{-1}$ with $\det D=-1$. The determinant forms agree. Any projective slice map carrying one to the other fixes all three points and is the identity in $\operatorname{PGL}_2$. The only possible determinant-one lifts of this projective class are $\pm I_2$, and their twelfth powers are both one. But $g=\gcd(2,4,6)=2$ and $-1$ is a nonsquare, so neither lift passes the left determinant test. This is a negative $\operatorname{SL}^3$ instance with a positive $\operatorname{GL}^3$ answer, even with identical determinant forms.

For a nonrational triple, $P=xI_3-yC$ with $C$ the companion matrix of $z^3-z-1$ over $\mathbb F_3$ gives three distinct roots and no rational root. For the opposite extreme, the regular pencil with diagonal entries $x,y,x-y,x+y$ has all four projective points of $\mathbb F_3$ as roots. There is no nonsingular rational slice.

Running `python Algorithms.py` enumerates the geometric projectivities of the irreducible cubic over $\mathbb F_{27}$ and obtains six candidates. Frobenius retains three, exactly the ones found among all 24 elements of $\operatorname{PGL}_2(\mathbb F_3)$. It also checks the square determinant subgroup for a length-two nilpotent block and the four singular rational slices of the regular diagonal example.

## Relation to prior work

Chen, Grochow, Qiao, Tang, and Zhang ask whether TI and special-linear TI coincide in full generality. Pervouchine classifies the corresponding matrix-pencil orbits over $\mathbb C$ using projectivities on the eigenvalues and a scalar determinant condition. Derksen, Klep, Makam, and Volčič give a polynomial-time left-right special-linear matrix tuple algorithm in an algebraically closed field setting. Over a finite field the left determinant power subgroup can introduce a rational obstruction even if the determinant forms already agree. The restricted result here enforces rationality through a finite root algebra and all three determinant conditions through (1), with bit complexity in $\log q$. It leaves the unrestricted TI vs. special-linear TI question open. This is a mathematical proof with finite controls, and priority for the factorization-free decision combination has not been established. [Chen et al., preprint Open Question 9](https://arxiv.org/html/2306.03135#S1.SS5) · [Pervouchine, Section 3](https://www.heldermann-verlag.de/jlt/jlt14/pervoula2e.pdf) · [Derksen–Klep–Makam–Volčič, Sections 5 and 7](https://jvolcic.neocities.org/ranks_orbits_21jan23.pdf)

