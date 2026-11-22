# Composition-factor determinants and the modular group-algebra case

Let $k=\mathbb F_q$ and $A\ne0$ be a finite-dimensional unital
associative $k$-algebra. Write its semisimple quotient as
$$
 A/J(A)\cong\prod_i M_{n_i}(k_i),\qquad [k_i:k]=f_i.
$$
Let $\ell_i$ and $r_i$ be the multiplicities of the corresponding
simple left and right modules in the left and right regular modules.
Put $g_L=\gcd_i\ell_i$, $g_R=\gcd_i r_i$, and let $D_{\mathrm{aut}}$
be the determinant image of the algebra automorphism group.

**Theorem.** The number of $\mathrm{SL}^3$-orbits inside the
$\mathrm{GL}^3$-orbit of the multiplication tensor is
$$
 \gcd(q-1,g_L)\gcd(q-1,g_R)[k^\times:D_{\mathrm{aut}}].
$$
For every group algebra $A=kG$ of a finite group, both gcd factors
are 1. Thus the automorphism determinant, equivalently the
determinant ratio, is the only restriction for every modular and
nonmodular finite group algebra.

## Proof by determinants on composition series

A multiplication stabilizer consists of maps
$X=L_u\sigma,\ Y=R_v\sigma,\ Z=L_uR_v\sigma$, with $u,v$ units and
$\sigma$ an algebra automorphism. This follows by substituting 1 in
$Z(xy)=X(x)Y(y)$, using the bijectivity of $X,Y,Z$ to obtain units
$X(1),Y(1)$, and cancelling them. Their determinant triples are
$(a\delta,b\delta,ab\delta)$, where $a=\det L_u$,
$b=\det R_v$, and $\delta=\det\sigma$. The three values are
independent and recoverable from the triple. Since the three group
determinants surject onto $(k^\times)^3$, their joint kernel has
as many orbits on the ordinary orbit as the index of the stabilizer
image. This gives the count once the two unit determinant images
are known.

Fix a unit $u$. Every left ideal in a composition series of
${}_A A$ is stable under $L_u$. In a basis adapted to the series,
the diagonal blocks of $L_u$ are the induced maps on the simple
quotients. The $i$-th simple is the standard $k_i^{n_i}$ and the
action on it is the matrix $u_i$ obtained from the $i$-th block
of the quotient. For any $k_i$-linear matrix $M$, its determinant
over $k$ is $N_{k_i/k}(\det_{k_i} M)$. This identity follows by
extending scalars to an algebraic closure of $k$, where the
restricted operator is the direct sum of its $f_i$ conjugates.
Consequently
$$
 \det L_u=\prod_i N_{k_i/k}(\det_{k_i}u_i)^{\ell_i}.
$$
For a right simple the row action has the same determinant, and the
right regular multiplicities give the corresponding product for $R_u$.

Every quotient unit lifts to a unit since $J(A)$ is nilpotent. For
example, a lift of the inverse gives both a left and a right inverse
after correcting by finite geometric series. Within each block the
ordinary determinant surjects onto $k_i^\times$ by diagonal
matrices, and each finite-field norm surjects onto $k^\times$
by cyclicity. Thus the left unit determinant image is exactly the
product of the independent power subgroups $(k^\times)^{\ell_i}$.
This is $(k^\times)^{g_L}$ by Bézout, and the right image is
$(k^\times)^{g_R}$. Their indices give the theorem.

## Why the unit obstructions vanish for group algebras

Choose $e_i$ to be a primitive idempotent lifting the first diagonal
matrix unit in the $i$-th quotient block. The projection by
$e_i$ is exact on left modules and has $k$-dimension $f_i$ on
the $i$-th simple and zero on the others. Hence
$$
 \dim_k(e_i A)=f_i\ell_i,\qquad \dim_k(Ae_i)=f_i r_i.
$$
The $e_i A$ give every indecomposable right projective up to
isomorphism, and the $Ae_i$ give every indecomposable left
projective. Thus $g_L$ divides the dimension of every right
projective, and $g_R$ does the same on the left. This reasoning does
not require a splitting field.

Suppose now $A=kG$ and $p=\operatorname{char}k$. For a prime
$s\mid q-1$ let $P$ be a Sylow $s$-subgroup of $G$, using
$P=1$ when $s\nmid |G|$. The trivial $kP$-module is projective:
the averaging idempotent splits it off the regular module since
$s\ne p$. Induction takes it to a projective $kG$-module of
dimension $[G:P]$, coprime to $s$. The same holds for right
modules. No prime dividing $q-1$ can therefore divide $g_L$ or
$g_R$. The stronger classical gcd statement for projective module
dimensions also uses restriction to a Sylow $p$-subgroup.
[Grinberg, Huang and Reiner, Remark 5.11](https://www.cip.ifi.lmu.de/~grinberg/algebra/McKayTensor-long.pdf)

## Exact counts for all abelian $p$-groups

Let $q=p^f$ and $G=\prod_{i=1}^r C_{p^{e_i}}$ with $r\ge1$.
Put $N=|G|$ and $d=\gcd_i e_i$. The orbit count is exactly
$$
 \begin{cases}
  2^{\gcd(f,d)}-1,&p=2,\\
  \gcd\big(q-1,(p^d-1)/2\big),&p\text{ odd}.
 \end{cases}
$$

Indeed the algebra is $k[x_1,\ldots,x_r]/(x_i^{p^{e_i}})$, where
$x_i=g_i-1$. It is graded by total degree, and the powers of its
maximal ideal are exactly the degree filtration. An automorphism
has the same determinant as its action on the associated graded
because the matrix in an adapted basis is block triangular. Its
graded action is determined by the induced linear map on the degree-one
space. The condition $\sigma(x_i)^{p^{e_i}}=0$ forces the linear
coefficient of $x_j$ to vanish when $e_j> e_i$. To see this,
take the degree-$p^{e_i}$ part and use characteristic $p$ and
the independence of surviving monomials $x_j^{p^{e_i}}$.
Conversely, every invertible linear map with this height pattern
defines a graded automorphism, since its inverse preserves the
same flag and its linear substitutions respect all truncations.

The resulting block triangular group is generated by diagonal
coordinate scalings and its allowed elementary shears. Ordinary
Gaussian elimination proves this by first eliminating within the
equal-height diagonal blocks and then between distinct heights.
A shear has order dividing $p$, so its determinant on the
algebra is 1 because $k^\times$ has order prime to $p$.
Scaling $x_i$ by $c$ multiplies each monomial by $c$ to its
$i$-th exponent. The sum of these exponents is
$$
 E_i=\frac{N}{p^{e_i}}\sum_{j=0}^{p^{e_i}-1}j
    =\frac{N(p^{e_i}-1)}2.
$$
Thus $D_{\mathrm{aut}}=(k^\times)^{\gcd_iE_i}$. For odd $p$,
the common factor $N$ drops out of the index and
$\gcd_i(p^{e_i}-1)=p^d-1$, by the Euclidean algorithm. For $p=2$,
the factor $N/2$ drops out, leaving
$\gcd(2^f-1,2^d-1)=2^{\gcd(f,d)}-1$.
The two unit indices are 1 by the group-algebra theorem.

For example, over $\mathbb F_4$, the order-16 groups $C_4^2$
and $C_8\times C_2$ give three and one special orbits respectively.
For fixed $p$, the full orbit-count profile over field extensions
determines $d$: its maximum is $2^d-1$ for $p=2$ and
$(p^d-1)/2$ for odd $p$, attained when $f$ is a multiple of
$d$. This recovers information absent from the left and right
regular composition profiles, which are identical for the two groups
of the same order.

## The socle controls the determinant up to sign for every $p$-group

For any finite $p$-group over $k$, let $\lambda(\sigma)$ denote
the scalar by which an algebra automorphism acts on the socle
$k\sum_{g\in G}g$. Then
$$
   \det(\sigma)^2=\lambda(\sigma)^{|G|}.
$$
Use the linear functional $\tau$ taking the coefficient of the
identity. The bilinear form $\tau(xy)$ is perfect, since the
group basis pairs with the inverse group basis. There is a unique
$u\in kG$ satisfying $\tau(\sigma(x))=\tau(ux)$. The form
$\tau(\sigma(xy))=\tau(\sigma(x)\sigma(y))$ is also perfect, so
$L_u$ is invertible, and $u$ is a unit. Evaluating on
$\sum_g g$ gives $\varepsilon(u)=\lambda(\sigma)$, where
$\varepsilon$ is augmentation. The algebra is local with the
trivial quotient, so the composition-series determinant formula
gives $\det L_u=\lambda(\sigma)^{|G|}$. Comparing the Gram
determinants of the two expressions for the form yields the identity.

Writing $s$ for the index of the socle character image in $k^\times$,
the determinant index is $s$ in characteristic 2. In odd
characteristic it is $s$ when the determinant image has odd order
and $s/2$ when that image has even order. This follows because the
determinant square image has the same order as the socle image,
as raising to $|G|$ is invertible on $k^\times$. Benson's
socle theorem places $\lambda$ in the $(p-1)$-st powers, so
for odd $p$ the orbit count is always at least $(p-1)/2$.
The abelian formula above shows this is sharp for every elementary
abelian $p$-group of positive rank. Over the prime field the
socle character is trivial, so for odd $p$ the only possible counts
for any $p$-group are $p-1$ and $(p-1)/2$. [Benson](https://arxiv.org/abs/2303.09940)

## A sharp spectrum for split basic square-zero algebras

Suppose instead $A/J\cong k^v$ and $0\ne J$ with $J^2=0$.
Let $m_{ij}=\dim_k e_iJe_j$, with $e_i$ mutually orthogonal
lifts of the factor identities. These lifts span the semisimple
subalgebra $k^v$. The radical multiplication is zero, and the
left and right actions of $k^v$ on $J$ are determined by those
component indices. Scaling just one basis vector in any nonzero
$e_iJe_j$ therefore extends to an algebra automorphism. Its
determinant is the chosen scalar. Hence $D_{\mathrm{aut}}=k^\times$,
and the orbit count is the product of the gcd indices from the
row sums and column sums of $(m_{ij})$, each augmented by 1.

For example, the radical matrix $\left(\begin{smallmatrix}1&0\\1&0\end{smallmatrix}\right)$
gives left multiplicities $(2,2)$ and right multiplicities
$(3,1)$. The ordinary orbit splits into two special orbits
over any odd finite field. This verifies that the two indices can
differ even in dimension 4.

For $N\ge3$, write $b=\gcd(N,q-1)$. Across all such algebras of
dimension $N$, the attainable counts are all divisors of $b^2$
if $b<N$. If $b=N$, they are all divisors of $N^2$ except
$N^2/s$ for primes $s\mid N$.
For the proof, the two lists of multiplicities both sum to $N$,
so both indices divide $b$. If either index is $N$, positivity
forces a single component and both indices equal $N$. A local
split square-zero algebra attains $b^2$. Every pair $a,c$ of
divisors of $b$ strictly below $N$ is realized on two vertices.
Choose a nonnegative $2$-by-$2$ matrix with respective row and
column totals $(a-1,N-a-1)$ and $(c-1,N-c-1)$. Such matrices
exist: put the smaller of the two first margins in entry $(1,1)$
and the remaining masses are forced and nonnegative. Use these
dimensions to construct $k^2\oplus J$ with the indicated bimodule
actions and $J^2=0$. Its radical has dimension $N-2>0$.
The multiplicity gcds are exactly $a,c$.
When $b=N$, a divisor of $N^2$ is a product of two proper
divisors of $N$ precisely when its prime-exponent deficit from
$N^2$ contains at least two prime factors with multiplicity.
Necessity is immediate. For sufficiency, distribute each deficit
between the two factors with each part at most the corresponding
exponent in $N$, choosing both total deficits positive. This is
possible if one deficit is at least two, or if two different primes
have positive deficits. This leaves exactly the claimed excluded counts.

## Verification and prior work

The matrix identities underlying coordinate scaling, shear determinants
and the Gram determinant comparison are stated separately in Lean.
The composition series, projective induction, orbit-index argument,
and full algebraic conclusions above have written proofs.
The control program independently computes small examples using
895 actual substitution matrices and both regular
determinant maps on the whole group algebra of $S_3$ over each of
$\mathbb F_3$ and $\mathbb F_4$. It also enumerates 11,086
radical dimension matrices for dimensions 3 through 8.
The projective-dimension gcd and the socle-character constraint have
direct prior art, as cited. Priority for the exact orbit counts or
their combination with the determinant-ratio construction is unestablished.
[Lean checks](B.lean) · [Finite controls](BCheck.py)
