# Exact Polynomial Calculus degree of matrix conjugacy

For two nonconjugate square matrices $A,B$ of the same positive size over a field $F$, consider the equations $XA=BX$, $XY=I$, $YX=I$. All polynomials are in the entries of $X,Y$. Ordinary Polynomial Calculus (PC) permits field-linear combinations and multiplication of a previously derived polynomial by one entry variable. The degree of a proof is the largest total degree of an actual line. Cancellations can lower degree. This is the conjugacy system in Open Question 7.3 of Galesi, Grochow, Pitassi and She. [Question and equations](https://arxiv.org/html/2305.19320#S7.SS3)

**Theorem.** Compute the Jordan data over a splitting field. The minimum PC refutation degree is **two** exactly when the minimal polynomials differ or some eigenvalue has different algebraic multiplicities as elements of $F$. Otherwise let $\tau$ range over mismatched types (one eigenvalue and one exact block length), with multiplicities $a_\tau,b_\tau$. Define $r_\tau=\min(a_\tau,b_\tau)$ and $g_\tau=|a_\tau-b_\tau|$. Put $D_\tau=0$ when $r_\tau=0$. For $r_\tau>0$ put
$$
D_\tau=
\begin{cases}
2 & \operatorname{char} F=0,\\
\min(r_\tau+2,\ 2p^{v_p(g_\tau)}) & \operatorname{char} F=p>0 .
\end{cases}
$$
When the degree-two test fails, the minimum degree is exactly $\max(3,\min_\tau D_\tau)$. In characteristic zero this leaves only the values two and three. This gives the degree for each pair in its original coordinates over its original field. The theorem concerns the conjugacy degree part of the published question. It has no analytic hypothesis.

The proof has two new ingredients. Independent Laurent weights on the individual edges of a partial matching give an exact degree obstruction for rectangular inverse equations. The degree-two trace test becomes a test on the minimal polynomials and multiplicities. The lower bound uses the matching designs of Riis and a one-step extension of their stated range, detailed below. Literature priority for the final formula has not been independently established. [Riis, Section 14](https://arxiv.org/html/2611.07280v1#S14)

## Matching designs at the endpoint

Write $E_j(R,S)$ for the vector space of field-valued functions on matchings of at most $j$ edges in the complete $R$-by-$S$ bipartite graph. Extend functions by zero on collisions. The value on a matching $T$ of size below $j$ must equal the sum of its extensions obtained by assigning a fixed row to each possible column, and also the corresponding sum for a fixed column. Use unions, so adding an already present edge leaves its matching unchanged.

**Design lemma.** If $0\le R<S$, $q=p^a$ divides $S-R$, $j<q$, and $2j-1\le R$, there is a design with value one on the empty matching. Every degree-$(j-1)$ design extends to degree $j$ when $j>0$. For $j=0$ any value on the empty matching works.

For $j>0$ and $2j\le R$ this is the design construction and extension of Riis, Sections 14.1–14.4. We give the precise endpoint argument since using just his stated rectangular obstruction would lose one degree. His integral reduction expresses every matching as an integer combination of terminal matchings using only matchings of no larger cardinality. Its validity on designs, termination, and integral independence of the terminal coordinates on the full square are proved for arbitrary sizes in Sections 14.1 and 14.2. The numerical stable-range condition in Section 14.3 ensures that the deterministic reduction in a rectangle with rows appended to the original $R$ rows never selects a failing row prefix ending in an appended row. For a matching $T$ of size at most $j$, failure at prefix $b$ means
$$
 b < h(T_{\le b})+|\operatorname{rows}(T_{\le b})|\le 2j ,
$$
where $h$ is the longest increasing chain length. Thus $b\le 2j-1\le R$. A failure at exactly $R$ is an old prefix and all its rows stay fixed in every compression. The signed history identity (65) therefore holds throughout the stated range. Explicitly, in a row replacement an edge already on an appended row remains fixed context, and in a column replacement a token retains its row or disappears. Each starting edge can visit at most one appended row. A path starting with a marked appended edge visits between one and $j$ appended rows. Increasing renamings of the appended rows that fix the old rows preserve every failed row prefix, the column-prefix chain lengths and the tie-breaking order. The signed sums of paths with a fixed history support consequently depend only on its size. Their sum is $\sum_{i=1}^j c_i\binom{S-R}{i}$, zero in the field since $j<q$. This is precisely the removed part of each column sum when one restricts square terminal coordinates to the old rows. All row sums are retained. Each old terminal matching remains terminal when the extra rows are added, since those later prefixes add only unused rows. Hence the resulting rectangular coordinates take the Kronecker delta values on old terminal matchings. The empty terminal coordinate is normalized. Weight the terminal coordinates through degree $j-1$ by the values of any given lower design. The resulting degree-$j$ design agrees with that design on all matchings through degree $j-1$ by the integral reduction. This proves the endpoint claim. [Original reduction, equations (64) and (65)](https://arxiv.org/html/2611.07280v1#S14)

## Rectangular inverse degree

Let $1\le r<s$, with $P$ an $s$-by-$r$ matrix of variables and $Q$ an $r$-by-$s$ matrix of independent variables. Then $PQ=I_s,\ QP=I_r$ have minimum degree $\min(r+2,2q)$ in characteristic $p>0$, with $q=p^{v_p(s-r)}$. In characteristic zero, or when $p$ does not divide $s-r$, the two traces already give degree two. If $r=0$ one input equation is a nonzero constant.

For the positive-characteristic lower bound fix $D<\min(r+2,2q)$. On each edge $e=(j,i)$, with $j\in[r]$ and $i\in[s]$, substitute
$$
 P_{ij}=t_e x_e,\qquad Q_{ji}=t_e^{-1}x_e .
$$
Here the $t_e$ are formal independent Laurent indeterminates. The $x_e$ satisfy only the Boolean and collision relations for now. The resulting algebra has basis $t^w x_T$ with $w$ an integral vector on edges and $T$ a matching. Indeed the Boolean and collision quotient on the $x_e$ has its squarefree matching basis, by evaluation on the indicator of each partial matching and triangular inversion. Laurent extension preserves independence. Off-diagonal inverse equations vanish and diagonal equations become ordinary row and column totalities.

The image of polynomials of degree at most $d$ is a direct sum of weight spaces. For a weight $w$, its support $S_w$ must be a matching contained in $T$, and its cost $c=\sum_e|w_e|$ must be at most $d$. The basis of this summand consists exactly of
$$
 t^w x_{S_w}x_U,\qquad |U|\le j_d(w)=\left\lfloor(d-c)/2\right\rfloor
$$
for $U$ a matching on the remaining $r-|S_w|$ rows and $s-|S_w|$ columns. To see necessity, a surviving edge with weight zero costs at least two target variables. To see sufficiency use $|w_e|$ copies with the required sign at each imbalanced edge, and one variable of each sign for each new balanced edge.

On this summand annihilate all complementary matching designs of degree $j_d(w)$. In detail, a coefficient vector $\sum_U a_U t^w x_{S_w}x_U$ belongs to $K_d$ if $\sum_U a_U\psi(U)=0$ for every such design. Take this condition separately for every weight. Throughout $d\le D$, the design lemma applies at every weight, because
$$
 2j_d(w)-1\le d-c-1\le r-|S_w|,\qquad j_d(w)<q .
$$
The side difference remains $s-r$. Restricting designs one degree and using their extension in the other direction shows that $K_D$ intersects the degree-$(D-1)$ image in exactly $K_{D-1}$. A weight new in degree $D$ has zero component in that intersection. This handles all degree falls.

Multiplication by the image of any target variable sends $K_{D-1}$ into $K_D$. Fix a weight $w$ and its edge $e$. Conflicts with another edge of $S_w$ give zero. The other possibilities can be checked on the dual design spaces.

- If $e$ is already in $S_w$ and its updated exponent stays nonzero, the support stays fixed. The residual polynomial is unchanged. The allowed residual degree stays fixed or increases by one, so design restriction suffices.
- If $e$ is disjoint from $S_w$ and newly acquires a weight, the new residual board omits its two endpoints. Its degree budget equals the old one. A design on the new board extends back to the old board by forcing $e$ present. Matchings conflicting with $e$ receive zero, and every other matching receives the value of the matching with $e$ removed if present. The row and column recurrences hold, including the two forced endpoints. This is exactly the transpose of the multiplication map on the coefficient vectors.
- If the last nonzero unit of weight on $e$ cancels, the new residual board includes its endpoints and has one extra degree of budget. The residual coefficients acquire the matching factor $x_e$. A design $\psi'$ on the new board pulls back to $U\mapsto\psi'(U\cup\{e\})$. This satisfies the required old recurrences since terms conflicting with $e$ vanish.

The weight of each product is $w$ plus the fixed signed unit vector of the multiplier. Addition preserves $K_D$. Every usable input maps into $K_D$ by the design recurrences, and the constant one lies outside it by normalization at weight zero. In an ordinary degree-$D$ PC proof a nonzero line legally multiplied by a variable has actual degree at most $D-1$. Its image therefore lies in the intersection just described. Induction over the proof now excludes a refutation of degree $D$. This proof uses only formal Laurent coefficients and works over finite fields without evaluating any of the $t_e$.

For the upper bound, the coefficient of $z^q$ in $(1+z)^s-(1+z)^r$ is nonzero in characteristic $p$. Comparing that elementary coefficient for $PQ$ and $QP$ gives zero identically by Cauchy–Binet, whereas their two identity matrices give different constants. Replace the product entries by the identity entries one at a time using the quadratic axioms in each expanded size-$q$ principal minor. This costs degree at most $2q$ (an out-of-range coefficient is zero).

The second upper bound uses $PQ=I_s$ alone. Assume that all $(k+1)$-minors of $P$ are derived zero, starting vacuously at $k=r$. Choose any set of $k+1$ rows and $k$ columns. Their signed $k$-minor cofactor row $v$, extended by zeros off the chosen rows, satisfies $vP=0$: each entry is an expansion of a $(k+1)$-minor or is identically zero through a repeated column. Then $(vP)Q=0$ and $v(PQ-I)=0$ give $v=0$ in degree at most $k+2$. Every $k$-minor occurs because $s>r\ge k$ supplies a spare row. Descend to the empty minor $1$. Multiplication by polynomial cofactors means multiplication by their individual monomials followed by addition, as ordinary PC permits. [Prior cofactor and coefficient bounds](https://github.com/Dugongue/MathProofs/blob/main/TensorSparsePCBounds/Proof.md)

## Passage to conjugacy in the original variables

The proof of the transfer is included to specify the small-degree exceptions. A constant change of bases induces homogeneous linear substitutions, and bounded-degree PC simulates multiplication by linear forms in the same degree. Extending the coefficient field preserves and reflects existence of a bounded-degree proof. Indeed the linear subspace of degree-$d$ consequences is constructed by iterating spans, intersections with degree at most $d-1$, and variable multiplication; all these operations commute with field extension. We may thus compute the degree over a splitting field. Similarity itself descends by rational canonical form.

A fact about disjoint systems will be useful. The minimum refutation degree of a union in disjoint sets of variables is the minimum of the individual degrees. For a proposed bound $d$ let $V_i$ be the vector space of local consequences derivable through degree $d$ inside the local polynomial space $W_i$ of degree at most $d$. Choose in $W_i$ a basis compatible with both $V_i$ and the ordinary degree filtration: at each degree first extend the basis for its intersection with $V_i$, then extend the whole basis up to that degree. Give each vector its actual degree. The tensor products of total weight at most $d$ form a basis of the global degree-$d$ space, by the degree filtration on the tensor product. The span of those with a factor in the chosen local $V_i$ basis contains the usable axioms. Its intersection with degree at most $d-1$ has the same description at that cutoff, by filtration compatibility. Multiplying any basis product in this intersection by a variable keeps the selected consequence factor or takes it to an allowed multiple in its own $V_i$. Thus the span contains every global consequence. If each local space misses one, choose the constant one as a complementary basis vector of degree zero in every block. Then the global constant misses the span as well.

In Jordan coordinates specialize both forward and reverse matrices to the direct sum of independent rectangular pairs tensored with the identity on the chain length, within each exact Jordan type. The forward intertwining equations vanish, and each nonzero inverse equation is the image of one rectangular inverse entry, read as that entry or its repetition. Equal multiplicities can be assigned identity blocks. Since each original variable specializes to a variable or constant, the degree does not increase. The disjoint-system fact gives the lower bound $\min_\tau D_\tau$.

Conversely, PC derives the reverse intertwining equations in degree three by
$$
 AY-YB=Y(XA-BX)Y+(I-YX)AY+YB(XY-I).
$$
Project $X$ and $Y$ linearly onto their actual intertwiner spaces. Each projection error is a scalar combination of available linear equations. Replacing the variables in the two inverse products by these projections changes the products by sums of linear multiples of those lines. The projected inverse equations are therefore available in degree three. For a fixed eigenvalue $\lambda$ and chain length $\ell$, apply the functor
$$
 M\longmapsto \ker (M-\lambda I)^\ell\big/
 \left(\ker(M-\lambda I)^{\ell-1}+(M-\lambda I)\ker(M-\lambda I)^{\ell+1}\right).
$$
It retains one coordinate precisely on each block of length $\ell$ at $\lambda$. Other lengths contribute zero, as is verified on a single chain. It respects intertwiners, identity maps, and composition. Linear coordinate functionals for this functor on the endomorphism spaces can be extended linearly to all matrices; apply them to the projected inverse equations. Their entries give a rectangular inverse system for $(a_\tau,b_\tau)$ in linear forms. The rectangular proof yields the upper bound $\max(3,\min_\tau D_\tau)$.

To decide between degrees two and three when the rectangular lower bound does not suffice, put $H=\{X:XA=BX\}$. The degree-two proof space is generated initially by the inverse equations, the intertwiner equations, and their variable multiples. If that span lacks a nonzero constant it already contains all degree-two consequences. Indeed its only possible degree-one lines are the original intertwiner span: inverse equations are of bidegree $(1,1)$ plus constants, and the other homogeneous components have bidegrees $(1,0),(1,1),(2,0)$. A derived constant would itself end the proof. Cancellation lowering a line to degree one supplies no further multiplication step. Degree one alone never suffices.

The span contains a nonzero constant exactly when matrices $C,D$ have $\operatorname{tr}C\ne\operatorname{tr}D$ and $XC=DX$ identically for $X\in H$. Indeed the general combination of the two inverse matrices is $\operatorname{tr}(C(YX-I))-\operatorname{tr}(D(XY-I))$. Its bilinear term restricted to $H$ is $\operatorname{tr}(Y(XC-DX))$. This vanishes exactly under the stated condition, and then each coefficient of $Y$ is a linear combination of the original linear equations.

To evaluate the trace test, take a source chain at $\lambda$ of length $l$ and a target chain at the same eigenvalue of length $m$. Number basis vectors by powers of the nilpotent, starting at zero. Intertwiners within this block pair are spanned by the shifts $u\mapsto u+t$ with $\max(0,m-l)\le t\le m-1$, dropping out-of-range positions. They can be turned on separately, with all other blocks zero. Each such shift forces the diagonal entries $C_{u,u}$ and $D_{u+t,u+t}$ to agree at every surviving position. Conversely any diagonal matrices constant on these links do satisfy $XC=DX$ for all $X\in H$ because these shifts span $H$.

For each chain pair its linked source positions are the first $\min(l,m)$ and its linked target positions the last $\min(l,m)$. All linked positions in this pair are connected: source position zero meets every linked target position, and each linked source position meets the target's last position. Across all block pairs at this eigenvalue these components meet, because each pair uses the first position of its source chain and the last position of its target chain. An eigenvalue occurring on only one side gives only isolated vertices. If both sides contain it, isolated positions exist exactly when their maximum block lengths differ. Thus the two minimal polynomials differ precisely when some position is isolated. Any isolated position yields a trace discrepancy by turning on that single diagonal entry. In the absence of isolated positions, the difference is an arbitrary linear combination of the differences of the two total algebraic multiplicities, one difference per eigenvalue. Off-diagonal entries never contribute to the trace. This proves the stated degree-two criterion and completes the conjugacy formula.

## Joint characteristic spectrum for integral Jordan pairs

For integer Jordan matrices with eigenvalues $0,1$, every reduction has the same Jordan data over its own field. More generally the following calculation holds whenever the Jordan multiplicities are preserved, up to relabeling of eigenvalues. Suppose no mismatch has zero smaller multiplicity, and set
$$
 u=\min_\tau r_\tau,\qquad G=\gcd_\tau g_\tau.
$$
The rectangular part of the exact degree in characteristic $p$ is $\min(u+2,2p^{v_p(G)})$. This follows by taking the minimum of the two terms separately. In particular for any threshold $d\ge4$, the attainable hard characteristics are exactly the primes with $u\ge d-2$ and $2p^{v_p(G)}\ge d$, provided the degree-two test fails. When $2p^{v_p(G)}\ge d\ge4$, each multiplicity gap is divisible by $p$, so all algebraic multiplicity differences vanish in the field. Positive smaller multiplicity on every mismatch also guarantees that the maximum lengths match for each eigenvalue. Hence the last proviso is automatic under these two inequalities. If a mismatch has zero smaller multiplicity the degree is at most three.

For a finite nonempty set of primes $S$ and thresholds $d_p\ge4$, the *least simultaneous matrix dimension* in this fixed-Jordan-data model is
$$
 n_{\min}=2\max_{p\in S}(d_p-2)+\prod_{p\in S}p^{e_p},
 \qquad e_p=\min\{a\ge0:2p^a\ge d_p\}.
$$
Indeed every discrepant multiplicity must be at least $u_0=\max_{p\in S}(d_p-2)$ on the smaller side, and every nonzero gap must be divisible by $G_0=\prod_{p\in S}p^{e_p}$. Equal total matrix dimensions force a positively discrepant type and a negatively discrepant type. On the side where the first is larger it contributes at least $u_0+G_0$ to the dimension; the second contributes at least $u_0$. Block lengths can only enlarge that sum. Conversely use the complementary idempotents $\operatorname{diag}(I_{u_0},0_{u_0+G_0})$ and $\operatorname{diag}(I_{u_0+G_0},0_{u_0})$. Their two types give the same rectangle and have equal maximum lengths. Their exact degrees attain all the required lower thresholds at once. The proof makes no assumption on prime distribution. For unrelated matrices allowed to vary independently with the characteristic, or for reductions at which Jordan data change, the quantifiers are different.

All general theorems here are written mathematical proofs. The matching extension argument uses the indicated integral construction from Riis's preprint. Sparse proof size for arbitrary conjugacy inputs and the separate matrix-congruence question retain their own scope.
