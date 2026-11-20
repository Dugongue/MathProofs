# Sharp polynomial separation for Frobenius-marked closed orbits

Let $K=\overline{\mathbb F}_p$ and $q=p^a$, with $a,n\ge 1$. For $V_i=K^n$, indexed cyclically by $0\le i<a$, take the product $G=\prod_i\mathrm{GL}(V_i)$. Write $F$ for entrywise $p$-power Frobenius, and write $V_i^{[p]}$ for the representation of $\mathrm{GL}(V_i)$ with matrix $F(g_i)$. Use the data space $V_0$ with two auxiliary records per edge,

$$
C_i:V_{i+1}\longrightarrow V_i^{[p]},\qquad D_i:V_i^{[p]}\longrightarrow V_{i+1}.
$$

At the two test points all $C_i$ and $D_i$ are the identity and the data are $0$ and $e_1$, respectively.

**Theorem.** These points belong to distinct closed geometric $G$-orbits. On the full linear space of the stated Frobenius-twisted records and the vector data, the least total degree of a polynomial invariant separating the two points is

$$
\frac{p}{p-1}\bigl(q^n-q^{n-1}\bigr).
$$

The sharp invariant is given by a characteristic polynomial of multiplication in an explicit finite free algebra. All Dickson generators have such polynomial lifts, with the same degree multiplier. For three tensor modes an explicit finite free algebra also gives a complete family of polynomial invariants on all points whose auxiliary records are identities.

There is a second comparison at $a=1$. Embed the two twisted factors in $\operatorname{Sym}^p V$ and $\operatorname{Sym}^p(V^*)$, respectively. On the **entire** symmetric-power ambient space, every separating invariant for the same pair has degree at least $p^n$. An invariant given by two homogeneous resultants has degree $(p+2n-2)p^{n-1}$ and separates the pair. The ambient space here uses symmetric powers as polynomial representations in characteristic $p$. It is distinct from a direct sum of raw mixed tensor powers.

The previous comparison by cyclic inverse markers gave the closed orbits and the scalar separating degree at $n=1$. The new lower bound uses the full finite general linear stabilizer rather than scalar weights alone. The constructions below give the sharp multivariable degree and explicit polynomial invariants. [Prior cyclic marker comparison and scalar case](https://github.com/Dugongue/MathProofs/blob/main/FourAlgebraicIsomorphismTransfers/ClosedOrbits.md) · [Lysikov–Walter, orbit-closure questions](https://arxiv.org/html/2411.04639#S1.SS4)

## 1. Closed orbits and their finite stabilizer

The action on a pair of record matrices is

$$
C_i\longmapsto F(g_i)C_i g_{i+1}^{-1},\qquad
D_i\longmapsto g_{i+1}D_i F(g_i)^{-1}.
$$

An element stabilizing the identity records has $g_{i+1}=F(g_i)$. Going around the cycle forces $g_0\in\mathrm{GL}_n(\mathbb F_q)$, and each such $g_0$ extends uniquely. The orbit of the identity records consists of all pairs with $D_i=C_i^{-1}$. Indeed the equations $g_{i+1}=C_i^{-1}F(g_i)$ reduce around the cycle to one equation $F^a(g_0)g_0^{-1}=B$ with $B$ invertible. Lang's theorem for $\mathrm{GL}_n$ solves it. This marker orbit is closed by the equations $C_iD_i=D_iC_i=I$.

For any added data, every point of the full orbit closure projects to this closed marker orbit, so its stabilizer is contained in a conjugate of the finite marker stabilizer. Its orbit therefore has dimension $\dim G$. Since boundary orbits have smaller dimension, the full orbit is closed. The two test data cannot lie in the same orbit because the action on the data is linear. The same argument works for multiple modes by taking the product of the marker systems. [Lang's theorem](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf) · [Algebraic group orbit dimensions and boundaries](https://www-fourier.univ-grenoble-alpes.fr/~mbrion/RAAG2.pdf)

The Frobenius-twisted spaces embed equivariantly as the spans of the pure basis powers in $\operatorname{Sym}^p V_i$ and $\operatorname{Sym}^p(V_i^*)$. For example $(\sum_j b_j e_j)^p=\sum_j b_j^p e_j^p$, and $(V_i^{[p]})^*=(V_i^*)^{[p]}$. In the full symmetric-power representation the marker orbit lies in the same invariant linear subspace. This subspace is closed, so the embedding preserves closedness of the orbits already constructed.

## 2. A sharp lower bound

If $f$ is an invariant on the twisted-record space, specialize all marker matrices to the identity. This gives a $\mathrm{GL}_n(\mathbb F_q)$-invariant polynomial in $x\in V_0$. Dickson's theorem describes the invariant ring as a polynomial algebra on the nonleading coefficients of

$$
\prod_{u\in \mathbb F_q^n}(t-u^Tx),
$$

of degrees $q^n-q^j$ for $0\le j<n$. The fixed spaces of a finite group commute with scalar extension by flatness, so the same description holds over $K$. In particular the least positive degree is $q^n-q^{n-1}$. If $f$ separates the test points, the specialized polynomial has a nonzero positive homogeneous part, and some monomial of $f$ has data degree $d\ge q^n-q^{n-1}$. [Dickson’s theorem and its coefficient description](https://www-users.cse.umn.edu/~reiner/Papers/GLCatInvar_ProcRoySocEdinburgh.pdf)

On the central torus, $g_i=z_iI$ gives weights $z_0$ on $x$, $z_i^p/z_{i+1}$ on $C_i$ and $z_{i+1}/z_i^p$ on $D_i$. Every monomial in an invariant has zero weight. For the indicated monomial put $h_i=\deg_{D_i}-\deg_{C_i}$. Comparing the exponents of each $z_i$ gives

$$
h_{i-1}=p h_i\quad(1\le i<a),\qquad
d=p h_0-h_{a-1}=(q-1)h_{a-1}.
$$

Since $d>0$, the $h_i$ are all positive and $\sum_i h_i=d/(p-1)$. The total degree is at least $d+\sum_i h_i=pd/(p-1)$. This proves the lower bound on the twist representation. The restriction of an ambient symmetric-power invariant to its twist subrepresentation is an invariant of no greater degree. Thus the same lower bound applies in that ambient space as well.

## 3. Explicit sharp invariants on the twist representation

Define the composite matrix

$$
A=D_{a-1}F(D_{a-2})\cdots F^{a-1}(D_0).
$$

Its transformation is $A\mapsto g_0 A F^a(g_0)^{-1}$. Let $R$ be the polynomial ring in the record entries and the data coordinates. Form

$$
\mathcal A_A=R[y_1,\ldots,y_n]\big/\bigl(y^{[q]}-A^Ty\bigr),
$$

where $y^{[q]}$ lists the coordinate $q$th powers. This algebra is free as an $R$-module on the $q^n$ monomials $\prod_i y_i^{b_i}$ with $0\le b_i<q$. For the total-degree order on the $y$ variables the given polynomials are monic with pairwise coprime leading monomials. The product criterion gives a monic Gröbner basis over $R$. Equivalently, replacing any $y_i^q$ by the corresponding linear form decreases total degree. If two different variables can be reduced, both reductions can then replace the other original power and produce the same product of the two linear forms. This gives unique normal forms and the asserted basis.

If $A'=g_0 A F^a(g_0)^{-1}$, the substitution $y'=g_0^{-T}y$ takes the equations for $A$ to those for $A'$. This follows by applying Frobenius to the substitution and using the action formula. Together with $x'=g_0x$ it preserves $y^Tx$. Therefore the characteristic polynomial of the $R$-linear endomorphism given by multiplication by $y^Tx$ has $G$-invariant coefficients. The freeness shows that the coefficients are polynomials in the original coordinates, with no localization needed. In particular the construction works on singular matrices $D_i$.

At the identity matrices the algebra splits as the product of the fields on all $y=u\in\mathbb F_q^n$. The characteristic polynomial is then the Dickson product. Its coefficient of $t^{q^{n-1}}$ vanishes at $x=0$ and equals $-1$ at $x=e_1$, since the product at $e_1$ is $(t^q-t)^{q^{n-1}}$. Thus this coefficient separates the stated points. The multiplication matrix is linear in $x$, so this coefficient is homogeneous of data degree $q^n-q^{n-1}$. It uses only the $D_i$ among the auxiliary records. The zero weight calculation consequently fixes its total auxiliary degree at $d/(p-1)$ and its total degree at $pd/(p-1)$, attaining the lower bound. Using $t^{q^j}$ gives the corresponding stated lift at each Dickson degree.

## 4. A complete explicit family for guarded tensor comparisons

For three source modes $V_{j,0}$ of positive dimensions $n_j$, build one cyclic marker system per mode. Write $A_j$ for its composite inverse matrix as above. Define the composite forward matrix by

$$
B_j=F^{a-1}(C_{j,0})F^{a-2}(C_{j,1})\cdots C_{j,a-1}.
$$

It transforms as $B_j\mapsto F^a(g_{j,0}) B_j g_{j,0}^{-1}$. For each mode take $n_j$ independent copies of the finite free algebra $\mathcal A_{A_j}$, one for each of $n_j$ ordered covectors, and tensor all these algebras over the coefficient ring. The resulting module has rank $Q=q^{\sum_j n_j^2}$. Write $Y_j$ for the square matrix whose rows are the covectors in mode $j$. In the algebra put

$$
w_j=\det(B_j)\det(Y_j)^{q-1},\qquad w=w_1w_2w_3.
$$

Under the same covector change of coordinates, the factors $w_j$ are invariant. The entries of the contraction $U=(Y_1\otimes Y_2\otimes Y_3)T$ of the datum $T$ are unchanged as well. Introduce indeterminates $s$ and $Z_{ijk}$. Take the characteristic polynomial of multiplication by

$$
w\left(s+\sum_{i,j,k}Z_{ijk}U_{ijk}\right)
$$

in the finite free algebra. Every coefficient in these indeterminates and the characteristic-polynomial variable $t$ is an ambient polynomial invariant. At identity records the algebra splits over all matrices $Y_j$ over $\mathbb F_q$. If any $Y_j$ is singular, $w=0$ and the corresponding factor is $t$. Otherwise $w=1$, and the factors are

$$
t-s-\sum_{i,j,k}Z_{ijk}\left((Y_1\otimes Y_2\otimes Y_3)T\right)_{ijk} .
$$

These linear factors encode the whole finite group orbit, with multiplicities. Its equality for two data tensors is equivalent to equality of their finite-field isomorphism orbits, by uniqueness of factorization with all factors monic in $t$. This argument is valid in the original characteristic, even when multiplicities are divisible by $p$. Hence the stated coefficient family separates all distinct closed orbits on the identity-marker slice.

For example, put $S=\sum_j n_j^2$, $L=\sum_j n_j$ and $b=(q-1)/(p-1)$. The family has total coordinate degree at most $Q(1+b(S+2L+3))$. In a multiplication matrix entry before reduction, the monomial basis contributes $y$-degree at most $S(q-1)$ and the displayed multiplier adds at most $L(q-1)+3$. Each reduction drops $y$-degree by $q-1$ and introduces a composite matrix entry of degree $b$. The existing determinant factors cost $bL$ and the data cost at most one. Taking a characteristic polynomial on a module of rank $Q$ gives the claimed bound. This is an explicit separation construction with an exponential-size algebra, not a polynomial-time orbit-comparison algorithm.

## 5. A separator in the full symmetric-power ambient space

Here take $a=1$. In the ambient space write the two marker records as arbitrary homogeneous degree-$p$ polynomial maps $\Phi:V^*\to V^*$ and $\Psi:V\to V$. The identity twist markers give coordinatewise Frobenius as both maps. Their transformation formulas are

$$
\Phi'(y)=g^{-T}\Phi(g^T y),\qquad \Psi'(z)=g\Psi(g^{-1}z).
$$

Write $\operatorname{Res}$ for the homogeneous resultant, normalized to give one on the coordinate powers. Define

$$
R(\Phi,x,t)=\operatorname{Res}_{y,z}\bigl(\Phi_i(y)-y_i z^{p-1}\ (1\le i\le n),\ tz-y^Tx\bigr),
\qquad R_0(\Psi)=\operatorname{Res}_{u}(\Psi_1(u),\ldots,\Psi_n(u)).
$$

The first resultant transforms by $(\det g)^{p^n-p^{n-1}}$. The variable change $(y,z)\mapsto(g^Ty,z)$ contributes exponent $p^n$, and the change by $g^{-T}$ among the degree-$p$ equations contributes exponent $-p^{n-1}$. The second transforms by the reciprocal character. Thus the coefficient of $t^{p^{n-1}}$ in $R(\Phi,x,t)R_0(\Psi)$ is an invariant in the full symmetric-power ambient. These are the usual covariance and multihomogeneity laws of the resultant. [D’Andrea–Dickenstein, explicit multivariate resultants](https://arxiv.org/abs/math/0007036)

At the Frobenius markers, the common projective zeros of the first $n$ equations are exactly $(y,z)=(u,1)$ with $u\in\mathbb F_p^n$. There are no points at infinity. Each distinct linear form $t-u^Tx$ divides the first resultant, since on its hyperplane the equations have a common zero. The forms exhaust its degree in $(t,x)$. At $x=0$ the resultant is $t^{p^n}$ by the normalization and the restriction to $z=0$. The specialization is therefore exactly the Dickson product. Also $R_0(\Psi)=1$ at the Frobenius marker. The indicated coefficient separates the two points as in Section 3.

This coefficient has data degree $(p-1)p^{n-1}$ and $\Psi$-degree $n p^{n-1}$. Under the scalar center the weights on $x,\Phi,\Psi$ are $1,p-1,1-p$, respectively. Invariance fixes the $\Phi$-degree at $(n-1)p^{n-1}$. Thus its total degree is $(p+2n-2)p^{n-1}$. Combining this with Section 2 gives both claimed bounds in the full ambient space. The proof of sharpness on the twist subrepresentation uses the different polynomial formula in Section 3.

## Verification and comparison

The argument uses the slice restriction principle familiar from invariant degree lower bounds. Derksen–Makam obtain exponential lower bounds for systems of generators and separating invariants in, among other representations, five copies of an ordinary three-mode tensor under products of special linear groups. The results here concern a specified pair of closed orbits under general linear groups with bounded Frobenius twists. The exact degree for that pair and the explicit characteristic-polynomial and resultant separators are the additional conclusions. [Derksen–Makam, Theorems 2.7 and 2.9](https://arxiv.org/abs/2107.06838)

The full theorems have written proofs. The Lean companion checks the arithmetic of the cyclic weight constraints and the resulting degree bounds. The finite replay checks the characteristic-polynomial construction using the finite free algebra and compares it with direct enumeration on the fixed marker slice.
