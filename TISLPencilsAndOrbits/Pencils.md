# Deterministic special-linear isomorphism for all matrix pencils over finite fields

Let $K=\mathbb F_q$ be given explicitly, and write $P(v)=xA+yB$ for an $m\times n$ pencil on $v=(x,y)^{\mathsf T}$. The special-linear equivalence question is whether
$$
 Q(v)=L P(Mv) R,\qquad
 (M,L,R)\in\operatorname{SL}_2(K)\times\operatorname{SL}_m(K)\times\operatorname{SL}_n(K).
$$
This convention is equivalent to the tensor action after transposes or inverses on the relevant group coordinates.

**Theorem.** There is a deterministic decision algorithm for every $2\times m\times n$ tensor over $K$ in time polynomial in $m,n,\log q$. It uses no factorization over $K$, no discrete logarithms, and no enumeration of $K$. Thus on the entire pencil format there is a same-field deterministic polynomial-time many-one reduction from special-linear to ordinary tensor isomorphism. The algorithm covers rectangular and singular pencils and every possible number of geometric eigenvalues. Decision is the scope of the algorithm.

## 1. Strict equivalence and determinant profiles

Strict equivalence means ordinary invertible left and right changes with the slice coordinates fixed. To compute a strict transporter, encode the pencil as the two-arrow Kronecker quiver module on $K^m\oplus K^n$, with the vertex projectors and the two maps from the second summand to the first as operators. Apply the deterministic constructive module-isomorphism algorithm of Brooksbank and Luks. A module isomorphism is a pair $(L,R^{-1})$ in the pencil convention above. The algorithm uses polynomially many arithmetic operations and zero tests, a fact used below to run it on several candidate pencils at once. [Brooksbank–Luks, Theorem 3.5](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

We use the partial Kronecker form over $K$. It gives a regular square summand and a direct sum of singular blocks of dimensions $(k+1,k)$ and $(k,k+1)$, including $k=0$. The tall block $S_k(v)$ for $k\ge1$ is multiplication by $v$ in the symmetric algebra, from $\operatorname{Sym}^{k-1}K^2$ to $\operatorname{Sym}^k K^2$. The wide block is its transpose. Their endomorphism rings equal $K$. In the tall case the two slice maps send the $i$-th basis vector to the $i$-th and $(i+1)$-th targets, respectively. Comparing at every overlap forces each successive column of the source endomorphism to be the shifted preceding column, with the necessary zero in the last position before each shift. These constraints make the source endomorphism scalar and the two slice equations make the target endomorphism the same scalar. Transposition and the one-dimensional zero-index cases give the other assertions. [De Terán–Dopico–Mackey, Lemma 6.2](https://eprints.maths.manchester.ac.uk/2017/01/covered/MIMS_ep2013_47.pdf)

Extraction of the regular complement and singular multiplicities needs no polynomial factorization. For each singular block type with $k\le m+n$, apply Theorem 3.5 of Brooksbank–Luks to the remaining module and to $m+n$ copies of that block. Retain the maximal common direct summand and remove it, stopping if the remaining module is zero. Their algorithm computes the complement as part of its direct-sum splitting loop. By Krull–Schmidt the common summand exhausts that type, and a polynomial number of trials of polynomial dimension removes exactly the singular part.

For the remaining regular pencil, the elementary-divisor exponents can be found without factoring. In a pencil $xA+yB$ let $U_0=0$, $U_{i+1}=B^{-1}(AU_i)$, and let $U$ be its stable value. The restriction $A|_U$ is injective. A nonzero last vector $u_j\in U_j\cap\ker A$ would otherwise yield a chain $Bu_i=Au_{i-1}$, $Bu_1=0$, and hence a nonzero polynomial kernel vector $\sum_{i=1}^jz^{i-1}u_i$ of $B-zA$. The induced $B$ on the quotient by $U,AU$ is invertible, and $N=(A|_U)^{-1}(B|_U)$ is nilpotent. In adapted frames the pencil is block triangular, with diagonal tuples $(I,N)$ and $(C,I)$. Off-diagonal blocks $A_{12},B_{12}$ can be eliminated by unipotent left and right factors with upper blocks $Y,X$, using $Y=-NX-B_{12}$ and $X-NXC=-A_{12}+B_{12}C$. The latter equation has the finite geometric-sum inverse because $N$ is nilpotent. Compute the invariant factors of $N,C$ by constructive Frobenius form. The exponents of irreducibles that occur in those polynomials are exactly the elementary-divisor exponents that occur. [Berger–Ilchmann–Trenn, Wong sequences](https://doi.org/10.1016/j.laa.2009.12.036) · [Storjohann, Frobenius form](https://cs.uwaterloo.ca/~astorjoh/p101-storjohann.pdf)

For clarity, the squarefree computations used here and below can be done with gcds. For a monic polynomial $f$, $u=f/\gcd(f,f')$ is the product once each of all factors whose multiplicity is not divisible by the characteristic $p$. Remove their full powers using $\gcd(f,u^{\deg f})$, take the $p$-th root of the remaining polynomial using $a\mapsto a^{q/p}$ on coefficients, and recur to obtain the squarefree radical. For the exponents, a root of multiplicity $j$ occurs in $\gcd(f,\partial^{[1]}f,\ldots,\partial^{[i]}f)$ precisely for $i<j$, where $\partial^{[i]}$ are Hasse derivatives. Thus $j$ occurs precisely when the squarefree radical degree drops from $i=j-1$ to $i=j$. This uses polynomially many arithmetic operations.

### Strict stabilizer determinant image

Let $H\subseteq (K^\times)^2$ be the image of the strict stabilizer under the determinants of the left and right factors. It is the subgroup generated by the images $z\mapsto(z^{u_i},z^{v_i})$ of the following integer columns:
$$
 (k+1,-k),\quad (k,-k-1),\quad (j,-j).
 \tag{1}
$$
The first two columns are used for the respective singular block types that occur. The last is used for each elementary-divisor exponent $j$ of the regular part. Multiplicities are unnecessary for the subgroup.

Here is a proof accounting for inter-block automorphisms. For a direct sum of finite-dimensional indecomposables, the endomorphism ring modulo its radical is the product of the matrix rings on isotypic multiplicity spaces over the corresponding local residue division rings. In this setting the statement also follows directly. Reduce all diagonal isotypic blocks modulo the local radicals and discard the off-isotypic blocks. A composite through two nonisomorphic indecomposables cannot give a unit on either, since a split inclusion into an indecomposable is an isomorphism. Thus this reduction is a surjective ring map. Its kernel is nilpotent. Expand a long product of kernel elements as paths through summands. By pigeonhole, some isomorphism type occurs repeatedly. Each loop between consecutive visits to this type lies in its local radical, either because the step already does or because the loop factors through a nonisomorphic indecomposable. Choosing the path long enough gives a zero product by the nilpotence of the local radical. Consequently units lift through this map and its kernel on units acts with determinant one at both vertices.

A regular indecomposable of elementary divisor $f^j$ has local ring $K[z]/(f^j)$. This follows from the regular splitting and the cyclic-module description of a companion block, with the same description for a nilpotent block at infinity. Its residue field is $K[z]/(f)$. On an isotypic collection of such blocks the residue multiplicity matrix acts on each of the $j$ successive layers of the $f$-adic filtration. Its determinant on either vertex is the same norm to $K$, raised to the $j$-th power. The determinant on the right factor is the inverse of the source-vertex determinant. Finite-field norms are surjective. Singular block types have residue field $K$ and dimensions as above, so their contributions are exactly the two other columns. This proves (1).

The strict groups and determinant profiles are unchanged by an invertible slice substitution, since preserving the two slices is equivalent to preserving any invertible linear recombination. If $(L_0,R_0)$ is a strict transporter, all determinant pairs form $(\det L_0,\det R_0)H$.

## 2. Monomial constraints without discrete logarithms

All remaining searches reduce to a constant number of equations of the form $\prod_j t_j^{b_{ij}}=c_i$ in $K^\times$ with an integer exponent matrix $B=(b_{ij})$. Compute an integer Smith form with unimodular multipliers $UBV=D$. The row operations act on the right-hand side by monomials and the column operations are bijective monomial changes of unknowns. On a diagonal row $d>0$ test whether the transformed right-hand side $c'$ satisfies $(c')^{(q-1)/\gcd(d,q-1)}=1$. On a zero row test $c'=1$. Cyclicity of $K^\times$ proves this criterion. Integer Smith form with the multipliers and repeated squaring take polynomial bit time. There is no need to find a generator of $K^\times$. [Kannan–Bachem, integer Smith form](https://doi.org/10.1137/0208040)

## 3. Three or more geometric roots

Use the determinant form of the regular summand, taking it to be $1$ when the summand is zero. Its projective root set is intrinsic to the pencil. Reject differing geometric root counts at once. A slice change pulls this root set back under its projectivity, since the singular blocks remain of the same type under any invertible slice change. This last fact will also follow from the symmetric-power identity below.

Represent the source and target root sets by finite reduced algebras $A_P,A_Q$. For their affine roots take $K[z]/(f)$, with $f$ the squarefree radical of the dehomogenized determinant, and include a factor $K$ for the point at infinity if present. The determinant itself is computed by polynomial arithmetic. Work in the tensor product of three copies of each root algebra. Its dimension is at most $(m+n)^6$. In this algebra choose the open subset where both triples are pairwise distinct by inverting all pairwise two-by-two brackets within each triple. For a tuple $s_1,s_2,s_3$, the frame map
$$
 \phi_s(v)=([v,s_1][s_3,s_2],\ [v,s_2][s_3,s_1])^{\mathsf T}
$$
sends it to $[0:1],[1:0],[1:1]$. The candidate matrix $M_0=\phi_s^{-1}\phi_w$ sends the target triple $w$ to the source triple $s$. Every eligible projectivity occurs among these candidates.

Retain the $K$-rational projectivities without extracting roots. In each of four charts invert one entry of $M_0$, normalize it to $1$, and impose $a^q=a$ on all its entries. The algebra before these operations is a product of finite extension fields. In it the localization at $a$ is the quotient by $\ker(m_a)$, with $m_a$ multiplication by $a$. Imposing an equation $b=0$ means quotienting by the ideal $bA$. These are polynomial linear algebra operations. The normalized entries satisfying Frobenius lie in $K$ on each surviving component.

Test strict equivalence of $P\circ M_0$ and $Q$, computing $(L_0,R_0)$ if it holds. A branch on $b=0$ splits the current product algebra into $A/(b)$ and $A/\ker(m_b)$; thus deterministic arithmetic algorithms run componentwise without explicitly factoring the algebra. The terminal nonzero pieces have total dimension at most that of the original algebra. Each branch path uses polynomial work. With rational input matrix entries all the specialized field operations of the strict routine stay in $K$, so its determinants are the rational transporter determinants.

Write $\delta_L=\det L_0,\ \delta_R=\det R_0,\ \kappa=\det M_0$. All scalar representatives are $\lambda M_0$. The right factor of the displayed strict transporter can be rescaled by $\lambda^{-1}$, and all further corrections lie in $H$. Therefore the test is exactly the monomial system
$$
 \lambda^2\kappa=1,\qquad
 \delta_L\prod_i t_i^{u_i}=1,\qquad
 \delta_R\lambda^{-n}\prod_i t_i^{v_i}=1.
 \tag{2}
$$
Use Section 2 to impose its resulting power equations by further algebra quotients. The final algebra is nonzero exactly when some rational candidate works.

## 4. Zero, one, or two geometric roots

For zero roots the pencil is completely singular. For $k\ge1$ naturality of the multiplication block gives
$$
 S_k(N v)\operatorname{Sym}^{k-1}(N)=\operatorname{Sym}^{k}(N) S_k(v)
 \qquad(N\in\operatorname{GL}_2(K)).
$$
For a tall block this restores $S_k(Nv)$ to $S_k(v)$ with determinant pair
$$
 \left((\det N)^{-k(k+1)/2},\,
       (\det N)^{k(k-1)/2}\right).
 \tag{3}
$$
For a wide block interchange the two entries. The determinant of $\operatorname{Sym}^{k}(N)$ is $(\det N)^{k(k+1)/2}$, seen by triangularizing $N$ over an algebraic closure and multiplying the monomial weights. The zero-index blocks have pair $(1,1)$. Thus every determinant-one slice change of a completely singular pencil can already be corrected by determinant-one left and right changes. Try just the identity slice change and test the strict determinant coset using (1) and Section 2.

For one or two roots, use frames $F_P,F_Q$ with matched columns on the corresponding root lines, using arbitrary rational complements for a single rational root. Write
$$
 M_0=F_P F_Q^{-1},\qquad M=F_P N F_Q^{-1},\qquad
 \det M=\kappa\det N,\qquad \kappa=\det M_0.
$$
The residual $N$ fixes each of the marked coordinate root lines individually. Test strict equivalence at $M_0$; the formulas below restore the varying slice change on the source. Hence failure at $M_0$ rejects every $M$ with that matching. If the test succeeds, let $c_L(N),c_R(N)$ be the correction determinants taking $P\circ M$ to $P\circ M_0$. The remaining requirements are
$$
 \kappa\det N=1,\qquad
 \delta_L c_L(N)\prod_i t_i^{u_i}=1,\qquad
 \delta_R c_R(N)\prod_i t_i^{v_i}=1.
 \tag{4}
$$
The contributions of the singular summands to $c_L,c_R$ are powers of $\det N$ from (3), applied to the conjugate of $N$ in the original slice variables.

### Rational roots

With a single root put it at $x=0$; then $N=\left(\begin{smallmatrix}a&0\\ b&d\end{smallmatrix}\right)$. A regular block of length $j$ there is $xI_j+yJ_j(0)$. Its substituted pencil is
$$
 x(aI_j+bJ)+ydJ.
$$
Left multiplication by $(aI+bJ)^{-1}$ gives $xI+yh(J)$, with $h(J)=dJ/(a+bJ)$. Use a nilpotent cyclic vector for $J$, ordered so the corresponding basis change $T$ has columns $h(J)^{j-1}e,\ldots,e$. Its triangular diagonal has powers $j-1,\ldots,0$ of $d/a$, and $T^{-1}h(J)T=J$. The pair $T^{-1}(aI+bJ)^{-1},T$ restores the pencil and has determinants
$$
 \left(a^{-j}(d/a)^{-j(j-1)/2},\ (d/a)^{j(j-1)/2}\right).
 \tag{5}
$$
They do not depend on $b$. For two rational roots, use both coordinate lines, so $N=\operatorname{diag}(a,d)$. For a block at $y=0$ apply (5) with $a,d$ interchanged. The block lengths at each root are the nilpotent lengths at that root, computable by the regular splitting of Section 1 after moving the specified point to $x=0$. All the conditions (4) are now monomial equations in $a,d,t_i$. Any accepted $a,d$ can be used with $b=0$.

The single rational root is read from its linear polynomial or is infinity. For two distinct rational roots we do not solve a quadratic to choose the frame: work in $A_P^{\otimes 2}\otimes A_Q^{\otimes 2}$ localized at the two brackets. This split algebra has both orderings and matchings among its geometric points, all rational. Frame computations and any zero branching are implemented as in Section 3.

### Two conjugate roots

The only remaining support type is a quadratic conjugate pair. Reject incompatible support types between source and target. In the tensor product of their two quadratic root algebras choose one affine root $\alpha$ from the source and $\beta$ from the target, and use as frames the columns $(\alpha,1)^{\mathsf T},(\alpha^q,1)^{\mathsf T}$ and their analogues for $\beta$. Componentwise $F_P^{(q)}=F_P J_2$ and $F_Q^{(q)}=F_Q J_2$, where $J_2$ interchanges columns. Thus $M_0$ and $\kappa$ are rational. The algebra tries both matchings without extracting a quadratic root. Every rational residual change in those frames is $\operatorname{diag}(a,a^q)$, with $a\in\mathbb F_{q^2}^\times$.

Over the quadratic field, choose a Jordan frame at the first root and its Frobenius conjugate at the second. The frame-coordinate involution interchanges the two slice variables. The matrices restoring a length-$j$ pair can therefore be chosen in conjugate pairs by the construction of (5). They descend to rational corrections. The two left determinant contributions multiply to $(aa^q)^{-j}$, and the two right contributions multiply to $1$. Consequently the entire regular part contributes $((\det N)^{-e},1)$, with $e$ half its dimension, and the singular blocks again contribute (3). The norm $a\mapsto aa^q$ is surjective onto $K^\times$, so enforcing $\det N=\kappa^{-1}$ imposes no further obstruction and fixes both correction determinants. The remaining two rows of (4) are determinant-profile tests in $K^\times$ using Section 2.

The geometric count and rational support type are determined by the degree of the squarefree projective root divisor and gcd with $z^q-z$ on its affine part, with infinity included separately. These computations are polynomial even if $q$ is larger than the input. The case split is now exhaustive. The output reduction returns the constant ordinary TI instance $(1,1)$ in format $1\times1\times1$ after a positive decision and $(1,0)$ after a negative one, over $K$.

Running `python Pencils.py` checks 240 rational Jordan-block corrections over the field of five elements, 144 singular-block corrections over the field of three elements, and 32 quadratic conjugate-block determinant products over its quadratic extension. The script tests the correction formulas used by the decision algorithm.

## Relation to prior results

Ja’Ja’ extended the general-linear theory to slice changes. Atkinson gave a criterion and efficient test for ordinary $2\times m\times n$ tensor equivalence using projective transformations of the elementary divisors. Pervouchine studied the literal three-factor special-linear action and classified its pencil orbits over $\mathbb C$. [Ja’Ja’, *An Addendum to Kronecker’s Theory of Pencils*](https://doi.org/10.1137/0137052) · [Atkinson, *Extensions to the Kronecker–Weierstrass Theory of Pencils*](https://doi.org/10.1080/03081089108818074) · [Pervouchine, *Hierarchy of Closures of Matrix Pencils*](https://jolt.centre-mersenne.org/articles/10.5802/jolt.345/)

Plût, Fouque, and Macario-Rat use projective root triples, low-root matching, and the regular/singular split in their odd-characteristic algorithm for pairs of quadratic forms with two secrets. Their formulation has a single input congruence and an output $\mathrm{GL}_2$ change, and their treatment uses polynomial factorization. Brooksbank, Maglione, and Wilson treat alternating genus-two bimaps by a common invertible change on the two input legs and an invertible output change. Their determinism qualification depends on the characteristic being bounded. These results supply nearby algorithms for linked input changes. [Plût–Fouque–Macario-Rat, Section 5](https://arxiv.org/pdf/1406.3163) · [Brooksbank–Maglione–Wilson, Theorems 5.1 and 6.1](https://joshmaglione.com/papers/Genus2.pdf)

The finite-field contribution here is the deterministic bit-polynomial enforcement of all three independent determinant-one conditions. It uses the rational root algebra, strict determinant profiles, and explicit correction characters for the positive-dimensional slice groups. A preceding finite-root argument treated regular pencils with at least three geometric roots. This proof covers singular shapes and all zero-, one-, and two-root cases as well. The unrestricted reverse reduction on all three-dimensional formats is the open question of Chen, Grochow, Qiao, Tang, and Zhang. This is a proof in mathematical prose. Literature priority remains open. [Chen et al., Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)


An independent [complete small-format check](SmallPencils.py) enumerates all 6,561 tensors of shape $2\times2\times2$ over $\mathbb F_3$. It checks that eight ordinary orbits exhaust the space and verifies the determinant coset of every transporter from each chosen representative.
