# Sparse proof preservation and matrix congruence inside ordinary tensor isomorphism

## Sparse proofs transfer at arbitrary degree through ordered label erasure

The following strengthens the sparse guarantee of the preceding block-erasure proof. It also applies before the specialization to simultaneous similarity and congruence.

**Theorem A.** Use the ordered-path compiler of [Linear block erasure](Background/MarkerProof.md) for any number of blocks of any dimensions in the three modes. In the literal based equations, an expanded PC proof of size $S$ and degree $D$ in either instance gives a proof in the other instance of size $O(S)+\operatorname{poly}(N+1)$ and degree $O(D+1)$, for an absolute constant and the sum $N$ of the original three dimensions. In the direction from the ordinary output to the labelled source, the degree bound is $\max(D,C)$ and the size bound is $S+\operatorname{poly}(N+1)$, as before. With field equations over the same $\mathbb F_q$, both conclusions hold with preparation also polynomial in $q$; the degree bound is unchanged in form. The size counts expanded monomial occurrences. No degree cutoff is needed in either direction.

*Proof.* The coordinate section already gives the ordinary-to-source assertion. For the other direction, work with the same multiplication algebras $A,B$, with split ordered diagonal and all strict corners lying forward in the order. Write the ordinary tensor witness in the isotopy convention $H(xy)=F(x)G(y)$, with inverse matrices supplied. As in the compiler, changing the covariant names to this convention uses entry permutations and the prepared inverse identities. Let $e_i,e'_i$ be the ordered idempotents in the two algebras. The corresponding Peirce corners are $A_{ij}=e_iAe_j$ and $B_{ij}=e'_iBe'_j$. Use their fixed matching bases.

Put $a=F(1), b=G(1)$. The unit extraction and multiplicativity steps of the compiler give
$$
 K(x)=a^{-1}H(x)b^{-1},\quad F(x)=aK(x),\quad G(x)=K(x)b ,
$$
with $K$ a unital algebra isomorphism. For example $H=R_b F=L_aG$, and evaluation at $H^{-1}(1)$ with the supplied inverse maps gives both left and right inverses of $a,b$. The normalized map $K$ fixes the ordered diagonal modulo the strict ideal $J$ by the constant-degree quotient calculation. With $u=\sum_i K(e_i)e'_i$ we have $u\in 1+J$, explicit inverse of bounded degree because $J^3=0$, and $K(x)=u\phi(x)u^{-1}$ where $\phi$ preserves all corners. Therefore
$$
 H(x)=A_0\phi(x)B_0,\qquad A_0=au,\quad B_0=u^{-1}b.
$$

For $x\in A_{ij}$, project this identity onto $B_{ij}$. Then
$$
 (H(x))_{ij}
   = (e'_i A_0e'_i)\,\phi(x)\,(e'_j B_0e'_j)
   = a_i b_j\,\phi(x).
\tag{A.1}
$$
Here $a_i,b_j$ are diagonal scalar coordinates, and $u$ has all diagonal coordinates one. The first equality is also an identity of matrix coefficient polynomials after corner preservation. Indeed $\phi(x)=e'_i\phi(x)e'_j$, so the left and right projections simply insert the two repeated idempotents on the outside; no sum over other corners survives. In the inverse formula $H^{-1}(y)=\phi^{-1}(A_0^{-1}y B_0^{-1})$, use that $\phi^{-1}$ also preserves corners. For $y\in B_{ij}$ this gives $(H^{-1}(y))_{ij}=a_i^{-1}b_j^{-1}\phi^{-1}(y)$.

The four diagonal scalars in these identities are **literal witness entries**. The map $F$ induces multiplication by $a_i$ on the line of $e_i$ in the diagonal quotient, and $G$ induces multiplication by $b_i$, since $K$ has identity quotient. The inverse maps similarly induce the inverse scalars. Thus $a_i=F_{e'_i,e_i}$ and $a_i^{-1}=(F^{-1})_{e_i,e'_i}$, with analogous entries of $G,G^{-1}$ for $b_i,b_i^{-1}$. In particular, for basis vectors $x\in A_{ij}$, $y\in B_{ij}$, the readouts can be written
$$
 \phi_{y,x}=(F^{-1})_{e_i,e'_i}(G^{-1})_{e_j,e'_j}H_{y,x},
 \qquad
 (\phi^{-1})_{x,y}=F_{e'_i,e_i}G_{e'_j,e_j}(H^{-1})_{x,y}.
\tag{A.2}
$$
Every equality used in (A.1)-(A.2) follows from bounded-degree preparation in the tensor equations. The older calculation obtains the corner-preserving polynomial map and its inverse already in constant-degree PC. Project that identity, use the literal basis multiplication entries, replace each formerly computed scalar diagonal by the displayed coordinate, and use the scalar inverse equations to cancel. The number of contracted matrix factors is bounded by an absolute constant. Expanding them and preparing all resulting coordinate equalities therefore uses polynomial sparse size, independent of the degree of any later source proof.

The maps on all source blocks and their inverses are restrictions of the corresponding strict corner maps in the block-erasure proof. The projection products show that these restrictions preserve the blocks. In particular the map on the output blocks is the restriction of the output-corner map, and the recovery of its blocks uses no change of coordinates. Hence each required source variable is represented by a **single monomial of degree three** in ordinary variables, using (A.2). Replace the polynomial readouts in the old axiom preparation by those monomials, one factor at a time, which still costs only a fixed degree and polynomial size. This prepares all source axioms under the new substitution. If field equations are present, the image of $z^q-z$ telescopes across the at most three factors using the coordinate field equations, with degree $O(q)$ and size polynomial in $N+1,q$. Prepare those images only when the source proof uses such axioms, in which case $D\ge q$.

Now replay any expanded source PC proof. A monomial substitution never increases the support of an individual line. A multiplication by a source variable is at most three successive ordinary variable multiplications, each with at most the support of the source parent. In ordinary PC over a field, multiplication by a variable preserves the parent support exactly, so the cost can be charged to the source multiplication line. Linear combinations replay directly. Monomial degrees expand by a factor at most three. The one-time preparations and this replay give the stated bounds. $\square$

For the mixed system below, its final normalization $R=a^{-1}P,\ S=aP^{-1}$ is also monomial in the block coordinates. Thus Theorem A strengthens Theorem 1 in exactly the same manner, with an absolute but larger constant for the degree and sparse-size overhead. In (A.2), the support of each proof line stays bounded by its original support at every degree.

## A shared change of basis for operators and forms

Fix a positive dimension $n$, and two lists of based data of the same format
$$
 \mathcal X=(L_1,\ldots,L_s; B_1,\ldots,B_h),\qquad
 \mathcal X'=(L'_1,\ldots,L'_s; B'_1,\ldots,B'_h).
$$
The $L_i$ are arbitrary operators and the $B_j$ are arbitrary bilinear forms. They can be singular, redundant, zero, or nonsymmetric. Use the written system in $R,S$
$$
 RL_i=L'_iR,\qquad R^{\mathsf T}B'_jR=B_j,\qquad RS=SR=I_n.
\tag{1}
$$
Named operators and forms do not mix. This includes the exact congruence system in Question 7.3 after transposing the name of the forward matrix and interchanging the input forms when appropriate. [Galesi–Grochow–Pitassi–She, Question 7.3](https://arxiv.org/html/2305.19320#S7.SS3)

**Theorem 1.** In linear side length $O(n+s+h+1)$, one can build ordinary three-tensors $T(\mathcal X),T(\mathcal X')$, each the multiplication tensor of a unital associative algebra, with the following guarantees.

1. Over every commutative base change, their isomorphism groupoid has natural compositional projection and section to the witnesses of (1). The two source matrices lift by coordinate and constant assignments to ordinary tensor witnesses with inverses. Tensor rank satisfies (3), and is within absolute constant factors of side length for bounded lists.
2. Every ordinary PC refutation gives a source PC refutation with degree at most $\max(D,C)$ and sparse size at most $S+\operatorname{poly}(n+s+h+1)$, where $D,S$ are its degree and sparse size. Every source PC refutation gives an ordinary PC refutation of degree $O(D+1)$, with size $O(S)+\operatorname{poly}(n+s+h+1)$ at arbitrary degree by Theorem A. The constants are absolute. The statement works with the coordinate field equations over the same finite field and allows a preparation cost polynomial in the field order when field axioms are used.
3. Polynomial-size Hilbert-like IPS certificates transfer in both directions with polynomial circuit overhead. The coordinate section also transfers equality-only Sum of Squares refutations from the ordinary system to the source over the reals, up to a constant additive overhead in degree.

**Proof.** Use three based spaces with each displayed summand separately named. The two copies of $V$ are $n$-spaces.
$$
\begin{aligned}
 X &= V \oplus k x_0\oplus \bigoplus_{j=1}^h k x_j,\\
 Y &= V \oplus k y_0\oplus k y_*\oplus \bigoplus_{i=1}^s k y_i,\\
 Z &= V \oplus k z_0\oplus \bigoplus_{j=1}^h k z_j.
\end{aligned}
$$
The bilinear table on these blocks is
$$
\begin{array}{c|l}
\text{arguments}&\text{product}\\ \hline
(x_0,y_0), (x_0,y_*), (x_0,y_i)& z_0\\
(v,y_0), (x_0,v)&v\\
(v,y_i)&L_iv\\
(x_j,y_0), (x_j,y_*)&z_j,\ z_0\ \text{respectively}\\
(v,w)&\sum_j B_j(v,w)z_j .
\end{array}
\tag{2}
$$
Every unlisted product is zero. Use identical roles for the primed data. The $z_j$ and all of $V\oplus k z_0$ are spanned by fixed basis products. The table is defined over the base ring, with no inverses of input coefficients.

Let $a,b$ be the blockwise scalar maps on $x_0,y_0$ and let the maps on $V$ in the first, second and third roles be $P,Q,W$. The products across $x_0$ and the right scalar blocks give scalar $ab$ on $z_0$ and scalar $b$ on $y_*,y_i$. The $y_*$ and $x_j$ relations give scalar $a$ on every $x_j$ and $ab$ on every $z_j$. The products with $y_0$ and $x_0$ give $W=bP=aQ$. Thus $R=a^{-1}P=b^{-1}Q$, $W=abR$. The data equations in (2) now give exactly (1), with $S=aP^{-1}$. This also describes the block transporter as the source transporter times two unit coordinates, in a way compatible with composition. Set $a=b=1$ for the section. In the section every block matrix or designated inverse is an original matrix or an identity. All extra scalar maps are one.

For the reverse PC preparation, derive these relations by the displayed scalar block equations, use the supplied inverses $a^{-1}, b^{-1},P^{-1}$ as variables, and replace one factor at a time. Each derivation involves a bounded number of factors at a time, independent of $n,s,h$. Concretely, $W=bP=aQ$ gives $Q=b(a^{-1}P)$ by multiplying by $a^{-1}$ and using the product $aa^{-1}=1$. In the congruence relation, substitute $P=aR,Q=bR$ and multiply $P^{\mathsf T}B'_jQ=abB_j$ by $a^{-1}b^{-1}$, then cancel via the two scalar inverse axioms. For similarity, use $bPL_i=bL'_iP$, cancel $b$, and multiply by $a^{-1}$. The inverse equations for $R,S$ follow from $PP^{-1}=P^{-1}P=I$. These steps give explicitly bounded-degree derivations with polynomially many expanded monomials. A field equation for an entry of a decoded matrix follows by Frobenius and telescoping products in degree $O(q)$; this cost is needed only when the source proof used such an equation, so $D\ge q$. In the other direction all projections of field equations are axioms or zero.

Apply the linear all-field block-erasure compiler of [the preceding theorem](Background/MarkerProof.md) to (2). Its triangular algebra has products of two strict basis elements supported by one full core bilinear table and block projections, with all longer strict products zero. To bound its rank, count two rank-one bilinear terms per strict basis vector for the endpoint actions and one per diagonal idempotent. Add one per basis vector for each block projection and output copy, and $O(n+s+h+1)$ for the transport and pairing products of (2) outside the input data. The bound including the data table is
$$
 d\le\operatorname{rank} T(\mathcal X)
       \le C_1\bigl(d+\operatorname{rank} D_{\mathcal X}\bigr),
\tag{3}
$$
where $d$ is the new side length and $D_{\mathcal X}$ denotes the direct sum of the two data subtables $V\times k^s\to V$, $V\times V\to k^h$. A unit evaluation gives the lower bound. For a bounded number of named matrices, their data rank is $O(n)$, so both sides and ranks are $\Theta(n)$. In all cases $\operatorname{rank}T\ge d\ge n$.

Compose the two PC preparations with those of block erasure. The entire section still uses zeros, ones, or a source entry per tensor entry. Hence each original proof line specializes without growing its support, and the only sparse cost in that direction is preparing the images of the original axioms. In the reverse direction the final block normalization is monomial in the block coordinates, so Theorem A gives multiplicative constant sparse overhead and additive polynomial preparation in any degree. For Hilbert-like IPS, annotate proof steps in each preparation with circuits for their coefficients on the target axioms, sharing previous coefficients. Compose an input certificate with these circuits and with the entry substitutions. This is polynomial in the input certificate size and presentation size. When field equations occur, use gate-by-gate Frobenius telescoping with repeated squaring instead of expanding a $q$-th power. For the ordinary-to-source SoS transfer, substitute the coordinate section in the squares and ideal terms. Every image axiom has a bounded-degree direct ideal certificate. Indeed all lifts through (2) and the algebra compiler are fixed block maps, and direct substitution reduces each product transport or inverse identity to a source axiom or a constant-linear combination of them. This preserves the SoS form of the certificate and adds at most constant degree. $\square$

## Degree and IPS upper bounds for arbitrarily long lists

**Theorem 2.** For the ordinary tensors of Theorem 1, over a field of characteristic different from two, geometric nonisomorphism has raw PC refutations of degree $O(n+1)$. In characteristic zero this improves to an absolute constant. Over any odd $\mathbb F_q$, every pair nonisomorphic over $\mathbb F_q$ has a degree-$O(qn)$ PC refutation with field equations and a division-free Hilbert-like IPS refutation of size $\operatorname{poly}(n+s+h+1,\log q)$. Thus the degree bound depends on the original matrix dimension, independently of the number of named matrices. The size and degree results hold even when the tensors become isomorphic over the algebraic closure.

**Proof.** Form a two-vertex quiver representation containing $V,V^*$. Add the $L_i$ as loops at $V$ and the $L_i^{\mathsf T}$ as loops at $V^*$. Add $B_j,B_j^{\mathsf T}$ as arrows from $V$ to $V^*$. The duality swaps vertices, dualizes the node maps, pairs the corresponding loops and the two arrows for each form. The input representation is self-dual with the displayed identity self-duality. The map with entries $R,S^{\mathsf T}$ is an isometry exactly when (1) holds.

Here the stated logical implication admits a useful small-degree preparation. From $R^{\mathsf T}B'_jR-B_j=0$ multiply by $S^{\mathsf T}$ to obtain $B'_jR=S^{\mathsf T}B_j$ using $RS=I$. The transpose form uses the transpose of the congruence equation. From $RL_i=L'_iR$, left and right multiplication by $S$ gives $SL'_i=L_iS$, then transpose to obtain the dual loop equation. These are linear equations in the original variables derived in degree at most three. Project the node pair along a constant complement onto the actual Hom space between the two quiver representations. Differences of coordinates are linear combinations of the derived linear equations. Replacing factors one at a time yields in degree at most three the two isometry inverse equations on that projected morphism. Here its displayed adjoint under the duality is its polynomially supplied inverse.

First suppose the underlying quiver representations differ. By Krull–Schmidt their direct sum endomorphism algebra has a radical quotient in which one simple matrix factor has unequal multiplicities $u,v$ for the two representations. In the algebraically closed case the residue field is the base. Over a finite field it is a finite extension $K$, by the finite division ring theorem. In that factor the maps between the two fixed idempotent summands are rectangular matrices of linear forms, and the projected inverse equations are $XY=I_u$ and $YX=I_v$. Applying the quotient is a constant-linear combination of the prepared quadratic equations. Take the determinant at the larger size: the product determinant vanishes identically by rank factorization and replacing each entry of its defect by the corresponding derived equation gives a refutation of degree at most $2\max(u,v)$. One can realize the replacement by replacing rows, with at most $u^2+v^2$ cofactors represented by division-free determinant circuits. The preparation and refutation consequently have polynomial IPS circuit size. Since the total vertex dimension on either side is $2n$, $\max(u,v)\le 2n$. In characteristic zero subtract the traces of the two inverse systems to get the nonzero constant $v-u$ already in degree two after preparation.

If the representations agree, choose an underlying representation isomorphism. Identifying the two representations reduces the isometry equation to $g^*Pg=1$ in the endomorphism algebra $E$ of one representation, for an invertible self-adjoint $P$. Its Jacobson radical $J$ is invariant under the involution. In odd characteristic, a solution modulo $J$ lifts: lift an invertible solution to a unit $g_0$, put $T=g_0^*Pg_0=1+j$, and solve $b^2T=1$ for a polynomial $b$ in $j$ one coefficient at a time. The coefficient multiplying the next unknown is always $2$. Then $b^*=b$, so $g_0b$ is a solution. In the quotient, factors exchanged by the involution always allow a solution by choosing one matrix freely and solving for its paired matrix. Each fixed factor has an involution adjoint to a nonsingular symmetric, alternating or Hermitian form, by the classification of involutions on a matrix algebra over a field. Over an algebraic closure of characteristic different from two, nonsingular bilinear forms of the same dimension and the relevant symmetric or alternating type are equivalent, so this case gives geometric isomorphism. For the resulting raw PC bound over an arbitrary coefficient field, run the geometric proof over its closure and descend its degree by coefficient projection onto the original field, retaining a line for each coefficient in the finite-dimensional span of the proof scalars. For each linear combination one takes combinations of the component lines of the parent polynomials. Equivalently the degree-filtered PC consequence space commutes with scalar extension. [Semisimple isometry method for tuples](https://arxiv.org/html/1708.03495)

Over a finite field of odd order, nonsingular Hermitian forms of the same dimension are equivalent by diagonalization and norm surjectivity. The same holds for alternating forms. A negative instance in this case therefore fails on a fixed symmetric factor $M_\ell(K)$, with two symmetric forms having different determinant square classes. The prepared quadratic equations give $Z^{\mathsf T}H_1Z=H_2$ there, where $Z$ has linear entries. Put $\delta=\det(H_2)/\det(H_1)$. Taking determinants by row replacement gives $(\det Z)^2-\delta$, with polynomial circuit coefficients, in degree $2\ell$. Let $d=[K\colon\mathbb F_q]$, take all $d$ coefficient conjugates, and multiply by telescoping to give
$$
 t^2-\delta_0,\qquad
 t=\prod_{\tau\in\operatorname{Gal}(K/\mathbb F_q)}\det Z^{\tau},
 \quad \delta_0=\operatorname{Norm}_{K/\mathbb F_q}(\delta).
$$
The element $\delta_0$ is a nonsquare. The polynomial $t$ has coefficients in $\mathbb F_q$ and degree $d\ell\le 2n$. For the latter inequality use the faithful $E$-module $V\oplus V^*$ and its $J$-adic filtration. Each matrix factor occurs on the associated graded, since otherwise a lift of that factor's idempotent would raise the filtration and hence be nilpotent in the faithful representation. Its simple module has $\mathbb F_q$-dimension $d\ell$.

The individual coordinate field axioms give $t^q-t$ in degree $qd\ell$, by telescoping each monomial. For a compressed circuit certificate, descend the circuit for $t$ through an $\mathbb F_q$-basis of $K$ with first element $1$, and apply gate-by-gate Frobenius telescoping over $\mathbb F_q$. Set $m=(q-1)/2$. Modulo $t^2-\delta_0$, $t^q+t=t[(t^2)^m-\delta_0^m]$ because $\delta_0^m=-1$. Compute the quotient $(X^m-Y^m)/(X-Y)$ by binary doubling on pairs of powers and their divided differences, using $O(\log q)$ gates. Subtract $t^q-t$ to obtain $2t$, multiply by $t$, and use $t^2-\delta_0$ to finish. All polynomial degrees are $O(qn)$; each circuit calculation involves polynomially many arithmetic gates in $n+s+h+\log q+1$. As above, annotate the preparatory PC lines, use determinant and power differences as direct ideal certificates, and take the first coordinate to descend a $K$-certificate to $\mathbb F_q$. Apply Theorem 1 to finish. [Prior single-matrix proof and norm calculation](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/ExactMatrixProofDegrees/ALL-ODD.md) $\square$

**Corollary.** For each fixed odd $\mathbb F_q$, the optimal worst-case expanded PC size on this compiled ordinary TI class, at side length $N$, is $N^{\Theta_q(N)}$ on an infinite sequence of sides, while every negative output has polynomial-size Hilbert-like IPS. In addition, over every odd prime characteristic the same geometrically negative family can attain degree linear in tensor rank, using one named operator and no forms.

For size, the one-form specialization of (1) is the exact finite-field matrix congruence system under variable renaming. The prior diagonal lower bound gives $n^{\Omega_q(n)}$ in that system. The ordinary-to-source specialization of Theorem 1 transfers it with additive polynomial cost, and $N=\Theta(n)$ for a single form. For the upper bound, Theorem 2 gives degree $O_q(N)$ in $O(N^2)$ variables. A degree consequence basis gives an expanded proof using a polynomial in the number of monomials up to that degree, at most $N^{O_q(N)}$. The circuit upper bound is that of Theorem 2. For the geometric rank-scale degree example, take the source operator which is an idempotent having multiplicities $p^a,2p^a$ and compare with the swapped multiplicities. The exact source degree is $p^a+2$ by the rectangular inverse formula; the side and rank of its ordinary companions are $\Theta(p^a)$ by (3). [Sharp odd finite-field congruence lower bound](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/ExactMatrixProofDegrees/PROOF.md) · [Source exact degree](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/ExactMatrixProofDegrees/ConjugacyDegree.md)

The result combines the older semisimple-form method and the previously proved one-matrix size and degree bounds with a uniform shared-witness compiler and an unbounded-list certificate theorem. The polynomial-in-rank upper bound is for the specified compiled class. The unrestricted ordinary TI problem of Question 7.1 has wider scope. The proofs are written mathematics. [TiedTransport.lean](TiedTransport.lean) certifies a scalar instance of the tied-action identity.

## Sharp bounds on specified arithmetic probes

The one-form examples can be kept fixed while varying the probe. For any fixed $d\in\mathbb Q^\times$, compile the forms $I_n,\operatorname{diag}(d,1,\ldots,1)$ over $\mathbb Z[1/b]$ where $b$ is the denominator of $d$. The ordinary pair is geometric-positive over any odd good residue characteristic. At a good prime $p$, it is positive over $\mathbb F_{p^e}$ if and only if $d$ is a square there. A nonsquare reduction therefore accepts exactly the even values of $e$. For each odd $e$, the same ordinary pair has minimum expanded PC size $N^{\Theta_{p,e}(N)}$ with the field equations, and an IPS circuit of size $\operatorname{poly}(N,e\log p)$. The lower bound holds uniformly in odd $p$ and $e$ by the original square-class lower bound. Over $\mathbb Q$ the pair tests whether $d$ is a square.

For a list of such rational parameters, the exact same ordinary tensors can be used at every good prime. If $d_1,\ldots,d_m$ are given in reduced fractions, set $M$ to four times the product of their absolute numerators and denominators. Under Dirichlet GRH, Bach's subgroup test yields a prime $p=O(\log^2(2M))$, with $p\nmid M$, detecting each nonsquare product of the $d_i$. Applying this to all products shows that their joint square-class dependencies are precisely the kernel of the binary table of reduction signs at the primes up to that bound. The construction turns any detected negative individual square class into the sharp ordinary TI proof-size gap above. The conditional input is the prime cutoff. [Matrix square-class proof and conditional prime panel](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/ExactMatrixProofDegrees/PROOF.md) · [Bach, explicit GRH bounds](https://doi.org/10.1090/S0025-5718-1990-1023756-8)
