# Determinant profiles of tensor isomorphisms from truncated algebras

Fix a commutative unital ring $R$, a free based $R$-module $V$ of rank $n\ge2$, a degree $d\ge3$, and formal forms $f,g\in\operatorname{Sym}^d V$. Write $U=R^\times$ and $\mathcal T(f,g)=\{h\in\operatorname{GL}(V):(\operatorname{Sym}^d h)f=g\}$. We extend the two-branch truncated algebra construction from fields to every such base ring, including rings with nilpotents. Its multiplication tensors encode the complete determinant profile of the form transporters through explicit powers of units.

Let $J$ be the ideal of positive-degree polynomials in $\operatorname{Sym}(V\oplus Rz)$ and set
$$
A_f=\operatorname{Sym}(V\oplus Rz)/(J^{d+1},\,zV,\,f-z^d).
$$
Order a monomial basis by degree, using the same ordering for all inputs and eliminating $z^d$ by the displayed relation. Write $\mu_f$ for the multiplication tensor in $A_f^*\otimes A_f^*\otimes A_f$. Define
$$
D=\binom{n+d}{d}+d-1,\qquad
E=\binom{n+d}{d-1},\qquad
M=nE+\binom d2.
$$

**Theorem.** The set of determinant triples of all tensor transporters from $\mu_f$ to $\mu_g$, in the two-dual-leg convention above, is exactly
$$
\left\{((\delta u)^{-1},(\delta v)^{-1},\delta uv):
  \ h\in\mathcal T(f,g),\ \lambda,s,t\in U,\
  \delta=(\det h)^E\lambda^M,\ u=s^D,\ v=t^D
\right\}.
$$
In particular $\mu_f\cong_{\rm GL}\mu_g$ exactly when $\mathcal T(f,g)\ne\varnothing$, and $\mu_f\cong_{\rm SL}\mu_g$ exactly when some $h\in\mathcal T(f,g)$ has $(\det h)^E\in U^M$. The maps to and from witnesses are explicit. For fixed $d$ the reduction outputs a tensor of polynomial size on dense form input, and over $\mathbb Z$ it runs in deterministic polynomial bit time.

**Integral cubic consequence.** If $d=3$, $n\equiv3\pmod4$, and every unit of $R$ has square $1$, the construction preserves both ordinary equivalence and equivalence by determinant-one maps. The same tensors record the determinant of every individual form transporter, equally on all three legs. The rank restriction belongs to this consequence. The formula above holds for all $n\ge2$ and arbitrary unit groups.

The proofs use the formal monomial basis over $R$. Their verification is mathematical and informal.

## 1. Recovering the augmentation over arbitrary base rings

The homogeneous pieces of $A_f$ are $R$ in degree zero, $\operatorname{Sym}^k V\oplus Rz^k$ for $1\le k<d$, and $\operatorname{Sym}^d V$ in degree $d$. Indeed, the mixed relations act in each degree, and the final relation freely eliminates $z^d$ because its coefficient is $-1$. The positive-degree ideal $\mathfrak m_f$ is nilpotent, and $\mathfrak m_f^j$ consists of the pieces of degrees at least $j$, by generation in degree one. This also proves the asserted rank $D$.

First consider a field. The positive-degree ideal is then the unique maximal ideal, since a positive-degree element is nilpotent and an element with nonzero constant term is a unit by the finite geometric series. An isomorphism therefore induces a graded isomorphism. Multiplication by a degree-one vector $v+cz$ from degree one to degree two has rank
$$
 n\,\mathbf1_{v\ne0}+\mathbf1_{c\ne0}.
$$
Here a nonzero $v$ multiplies the polynomial space $V$ injectively into $\operatorname{Sym}^2 V$, and the product with $z$ lies in the independent direction $Fz^2$. Since $n\ge2$, the zero vector and all rank-one multipliers form exactly the line $Fz$. The degree-one annihilator of this line is exactly $V$. Every graded transporter over a field consequently preserves both pieces.

For general $R$, take any unmarked $R$-algebra isomorphism $\phi:A_f\to A_g$. In the given grading write
$$
\phi(x_i)=a_i+L_i+\text{higher degrees},\qquad
\phi(z)=b+L_z+\text{higher degrees}.
$$
After reducing at every maximal ideal of $R$, the field argument shows that $L_1,\ldots,L_n,L_z$ give a basis and that the coefficient of $z$ in $L_z$ and the $V$-block of the $L_i$ are invertible. An element outside every maximal ideal is a unit. Applying this to the appropriate determinants shows the same invertibility over $R$. The degree-one part of $\phi(x_i)\phi(z)=0$ is $bL_i+a_iL_z=0$. Since the $L_i,L_z$ are an $R$-basis, every $a_i$ and $b$ vanishes. The inverse isomorphism satisfies the same argument. Thus $\phi(\mathfrak m_f)=\mathfrak m_g$, and $\phi$ induces a graded isomorphism.

Write $L_i=Sx_i+c_i z$ and $L_z=w+\lambda z$, where $S\in\operatorname{GL}(V)$ and $\lambda\in U$. The degree-two mixed relation now says
$$
 (Sx_i)w+c_i\lambda z^2=0
 \quad\text{in }\operatorname{Sym}^2 V\oplus Rz^2.
$$
It follows that $c_i=0$ and $(Sx_i)w=0$. Multiplication by any member of an $R$-basis of $V$ is injective in the symmetric algebra, as is seen in that basis by shifting monomial exponents. Therefore $w=0$. The degree-$d$ relation is now
$$
(\operatorname{Sym}^d S)f=\lambda^d g.
$$
Hence $h=\lambda^{-1}S$ belongs to $\mathcal T(f,g)$. Conversely each such $h$ and each $\lambda\in U$ gives a graded isomorphism by $x\mapsto\lambda h(x)$ and $z\mapsto\lambda z$. In particular the augmentation and the two indicated subspaces of its first filtration quotient are intrinsic over every commutative base ring. The mixed products remove possible nilpotent constant terms and off-diagonal terms using linear and quadratic coefficients.

## 2. The determinant of an algebra transporter

The filtration of $\mathfrak m_f$ is preserved. Every filtered isomorphism is block triangular in our bases, so its determinant is the product of the determinants on the graded pieces. In degree $k$ its symmetric-power block is $\operatorname{Sym}^k S$. The identity
$$
\det(\operatorname{Sym}^k S)=(\det S)^{\binom{n+k-1}{k-1}}
$$
holds over every commutative ring. For a diagonal matrix it follows by counting the total exponent of each variable among the degree-$k$ monomials. For arbitrary complex matrices it then holds on the dense set of matrices with distinct eigenvalues. Both sides are universal polynomials with integer coefficients, so the identity holds after specialization to $R$.

The extra degree-$k$ block for $k<d$ contributes $\lambda^k$. Summing the symmetric-power exponents gives $E$ by the hockey-stick identity. Using $S=\lambda h$ gives
$$
\det\phi=(\det S)^E\lambda^{\binom d2}=(\det h)^E\lambda^M.
$$
Every value on the right is realized by the graded lift just constructed.

For a unit $a$ of $A_g$, let $L_a$ be multiplication by $a$. Its augmentation $s$ is a unit of $R$, and conversely every element with unit augmentation is a unit by the finite geometric series. Each filtration quotient sees multiplication by $s$, so $\det L_a=s^D$. Every value of this form is realized by a scalar unit.

## 3. From algebra to multiplication tensors

For any two unital associative commutative $R$-algebras of the same finite free rank, let $(P,Q,H)$ be invertible linear maps satisfying
$$
 H(xy)=P(x)Q(y).
$$
The corresponding tensor transporter has legs $(P^{-1})^*,(Q^{-1})^*,H$. Let $a=P(1)$ and $b=Q(1)$. Evaluation at the unit gives $H=L_bP=L_aQ$, so $L_a$ and $L_b$ are invertible. A preimage of $1$ under each multiplication map is the inverse of the corresponding element. Put $\phi=L_{(ab)^{-1}}H$. Then $P=L_a\phi$, $Q=L_b\phi$, $H=L_{ab}\phi$. The displayed product identity implies $\phi(xy)=\phi(x)\phi(y)$ and $\phi(1)=1$. Conversely any algebra isomorphism $\phi$ and target units $a,b$ give exactly this isotopy. These parameters are unique.

Apply this to $A_f,A_g$. Set $\delta=\det\phi$, $u=\det L_a$, and $v=\det L_b$. The determinants in the input-input-output convention are $\delta u,\delta v,\delta uv$, since $L_{ab}=L_aL_b$. Dualizing inverse maps on the two input legs gives the theorem's profile. For all three leg determinants to be $1$, the first two require $u=v=\delta^{-1}$. The last then requires $\delta=1$. Conversely a determinant-one $\phi$ gives a determinant-one tensor transporter by taking $a=b=1$. The condition that $\delta=1$ can be achieved for a given $h$ is exactly $(\det h)^E\in U^M$.

Given a tensor witness one obtains $\phi$ from its unit evaluations as above, then reads $S,\lambda$ in the linear coefficients of $\phi$ and returns $\lambda^{-1}S$. In the forward direction, graded polynomial substitution and multiplication by scalar units produce the witnesses for the entire displayed profile. The multiplication table is explicit. Two $V$-monomials multiply in the usual way through degree $d$, mixed products vanish, and positive powers of $z$ multiply until degree $d$, where $z^d$ is replaced by $f$. Higher-degree products vanish. Thus the dense table contains $D^3$ entries, each zero, one, or an input coefficient. This proves the dense polynomial-size and integer bit-time bounds.

## 4. Integral cubics and a strict orbit split

For $d=3$ and $n\equiv3\pmod4$, $E=\binom{n+3}{2}$ is odd, while $M=nE+3$ is even. Also $D=\binom{n+3}{3}+2$ is even, since $n+3\equiv2\pmod4$. If all units square to $1$, then $\lambda^M=s^D=t^D=1$ and $(\det h)^E=\det h$. The determinant triple is therefore $(\det h,\det h,\det h)$ and every such triple occurs.

For an integral example at rank $3$, take
$$
 f=x^3+2y^3+4w^3,\qquad g=-x^3+2y^3+4w^3.
$$
The reflection of $x$ transports $f$ to $g$. The only integral automorphism of $f$ is the identity. Indeed, its Hessian determinant over $\mathbb Q$ is a nonzero scalar multiple of $xyw$. The chain rule for Hessians forces every linear automorphism of $f$ to preserve the union of those three coordinate hyperplanes. Unique factorization of linear forms forces its matrix to be monomial. An integral invertible monomial matrix is a signed permutation matrix, since its nonzero entries are integers with product $\pm1$. The three distinct positive coefficients force the permutation and all signs to be trivial. Therefore every tensor transporter has determinant triple $(-1,-1,-1)$. This gives explicit multiplication tensors of shape $22\times22\times22$ in the same ordinary integral orbit and different special-linear orbits.

The ring theorem also handles genuinely nilpotent corrections to algebra transporter witnesses. For example, over $\mathbb Z/9$, set $f=x^3$. The substitution $x\mapsto x+3y$, $y\mapsto y$, $z\mapsto z$ preserves the algebra relation, since $(x+3y)^3=x^3$ in that coefficient ring. In contrast, $x^3$ and $4x^3$ are inequivalent. Comparing the $x^3$ coefficient in an alleged transporter would require a cube of an element of $\mathbb Z/9$ equal to $4$, whereas the cubes are $0,1,-1$.

## 5. Counting special-linear witnesses over finite rings

Suppose $d=3$ and $R$ is finite of size $q$. Put $D_j=\binom{n+j-1}{j}$, let $U[D]=\{s\in U:s^D=1\}$, and define the finite $R$-module
$$
K_g=\{(B,\ell)\in\operatorname{Sym}^2V\oplus V^*:
             xB+\ell(x)g=0\text{ for every }x\in V\}.
$$
Then the exact number of special-linear tensor transporters from $\mu_f$ to $\mu_g$ is
$$
q^{\,nD_2+(n+1)D_3+1+2(D-1)}
 |K_g|\,|U[D]|^2
 \bigl|\{(h,\lambda)\in\mathcal T(f,g)\times U:
                  (\det h)^E\lambda^M=1\}\bigr|.
$$
Indeed, each fixed graded isomorphism has as many lifts as there are graded-identity automorphisms of $A_g$, by composition with its inverse. For such an automorphism, write the images of generators as
$$
 x\longmapsto x+Q(x)+\ell(x)z^2+C(x),\qquad
 z\longmapsto z+B+bz^2+T,
$$
where $Q:V\to\operatorname{Sym}^2 V$ and $C:V\to\operatorname{Sym}^3 V$ are linear, $b\in R$, and $T\in\operatorname{Sym}^3 V$. The mixed relation is exactly $xB+\ell(x)g=0$ in degree three, and the top relation is automatically satisfied because the linear part is the identity. All monomials of degree four vanish under the proposed substitution. These choices determine all lifts, and the resulting endomorphisms are invertible by their block triangular matrices with identity diagonal. The free choices of $Q,C,b,T$ contribute the factor with exponent $nD_2+(n+1)D_3+1$. Lastly, for $\det\phi=1$, each of the two target units may have any positive-degree part and a constant term in $U[D]$. This contributes the remaining factors. The mixed constraints are a linear system over the base ring. The form transporter factor retains the original equivalence problem.

For a check over $\mathbb Z/9$, take $f=g=x^3$ in two variables. Exhaustive enumeration of all $3888$ invertible matrices gives $486$ transporters to each of $x^3$ and $8x^3$ and zero to $4x^3$. Here $K_g=0$, since the relation at $y$ requires $yB+\ell(y)x^3=0$, which forces both summands to vanish in the monomial basis, and the relation at $x$ then gives $\ell(x)=0$. The exponents are $D=12$, $E=10$, $M=23$, and $\lambda\mapsto\lambda^{23}$ is a bijection on the six units. Thus the count formula gives $17496\cdot9^{41}$ special-linear autotopies.

A base ring with two independent nilpotents has additional lifts that genuinely mix the two branches. In $R=\mathbb F_2[\epsilon,\eta]/(\epsilon^2,\eta^2)$, take $g=\epsilon x^3+\eta x^2y$. Writing $L=\ell(x)$ and $N=\ell(y)$, the mixed constraints reduce to $\eta L=0$, $\epsilon N=0$, $\epsilon L=\eta N$, and $B=\epsilon Lx^2$. The possibilities are $L=l_1\eta+l_2\epsilon\eta$ and $N=l_1\epsilon+n_2\epsilon\eta$ with three independent binary parameters. There are eight choices and four have $B\ne0$. Enumerating the $16^2$ pairs $(L,N)$ gives the same counts.

## 6. Relation to the literature

Part III of Chen, Grochow, Qiao, Tang and Zhang develops reductions for several classical groups and singles out special linear actions as a further direction. The profile above gives an explicit simultaneous comparison for one structured family, including exact recovery of orientation for integral cubics in the stated rank class. Part V of Grochow, Qiao, Stange and Sun studies the graph of reductions between tensor actions over commutative rings, with the diagonal-full hypothesis for their main framework on free modules (Theorem 3.7). Their Theorem 3.17 also gives an ordinary reduction to algebra isomorphism for commutative associative outputs from symmetric bilinear maps. The present forward construction from formal forms uses the multiplication relations to recover witnesses over arbitrary commutative rings and retains determinant data. Its scope is the displayed family of multiplication tensors. [Chen–Grochow–Qiao–Tang–Zhang, Part III, Section 1](https://arxiv.org/html/2306.03135v2#S1), [Grochow–Qiao–Stange–Sun, Part V, Sections 1–3](https://arxiv.org/html/2611.00735v1).

Agrawal and Saxena use a truncated quotient by the form, with scalar-root hypotheses in the equivalence proof. The auxiliary branch binds the scalar directly to the algebra transporter. The equivalence of ordinary isotopy and isomorphism for unital associative algebras is classical. The additions proved here are arbitrary-base augmentation recovery for $A_f$, the determinant formula through the filtration, and the resulting exact special-linear criterion and sign example. The checked sources establish the surrounding constructions and leave priority for this determinant-preserving combination unverified. [Agrawal–Saxena, Theorem 2.3 and Section 6](https://www.cse.iitk.ac.in/%75sers/nitin/papers/cubic-forms.pdf), [Garibaldi–Petersson–Racine, Section 13](https://doi.org/10.1017/fms.2023.7), [Guminov–Zhdanovskiy](https://arxiv.org/abs/2112.15436).
