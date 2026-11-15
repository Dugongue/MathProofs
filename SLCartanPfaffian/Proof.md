# A Pfaffian determinant test from raw tensor coordinates

Informal proof. Fix a finite field $F=\mathbb F_q$. A *trilinear transporter* from $T_A$ to $T_B$ is a triple $G=(g_1,g_2,g_3)$ satisfying $T_B(g_1x,g_2y,g_3z)=T_A(x,y,z)$. The determinant triple in the covariant tensor convention is the inverse of the determinant triple of $G$.

We give a sufficient condition on a raw trilinear tensor for reducing total-determinant-one tensor isomorphism to ordinary tensor isomorphism. On a concrete growing family, we recover the entire determinant triple coset whenever ordinary isomorphism holds. This gives a reduction to one ordinary tensor isomorphism instance for every determinant character, including arbitrary truncation weights in the associated triangular multiplication algebras. The family contains tensors with all three pair-adjoint algebras scalar over every fixed finite field.

## 1. The Pfaffian cofactor polynomial

Let $Z=U_1\oplus U_2\oplus U_3$ have odd dimension $N\ge3$. Form an alternating three-form $\omega_T$ whose values on $U_1\times U_2\times U_3$ are $T$. It vanishes on triples with two entries in the same summand and is extended by alternation and linearity. This definition applies also in characteristic two. Write $\Omega_T(x)$ for the alternating matrix of $(y,z)\mapsto\omega_T(x,y,z)$ in a fixed basis. The signed Pfaffian cofactor vector is
$$
 C_T(x)_i=(-1)^{i-1}\operatorname{Pf}\bigl(\Omega_T(x)_{\widehat i}\bigr).
$$
There is a unique polynomial $P_T$, homogeneous of degree $(N-3)/2$ when nonzero, with $C_T(x)=P_T(x)x$.

Indeed $\Omega_T(x)x=0$, and expansion of the Pfaffian of an alternating matrix with a repeated row and column gives $\Omega_T(x)C_T(x)=0$. Over the rational function field, either $\Omega_T(x)$ has rank below $N-1$ and all these cofactors vanish, or its kernel is exactly the line $F(x)x$. In the latter case $x_i C_T(x)_j=x_j C_T(x)_i$. The relatively prime indeterminates $x_i,x_j$ show $x_i\mid C_T(x)_i$, and the quotients are equal. Each cofactor has degree $(N-1)/2$.

A trilinear transporter $G=g_1\oplus g_2\oplus g_3$ satisfies $\Omega_B(Gx)=G^{-\mathsf T}\Omega_A(x)G^{-1}$. The cofactor vector of $M^{\mathsf T}\Omega M$ is $\det(M)M^{-1}$ times that of $\Omega$. This is the exterior change-of-basis law on the highest Pfaffian minors and holds over all characteristics by the corresponding integral polynomial identity. Hence
$$
 P_B(Gx)=\det(G)^{-1}P_A(x).
$$
When $P_A\ne0$, a trilinear transporter has total determinant one exactly when it preserves $P$. Evaluation of $P_T$ at any nonzero point in any extension field takes one Pfaffian computation and division by a nonzero coordinate. At zero the answer is zero if the degree is positive, and a constant can be evaluated at any basis vector. Alternating matrix elimination computes the Pfaffian in polynomial time over any field.

## 2. A sufficient raw reduction

Suppose $P_A\ne0$ and has at most a fixed $J$ distinct absolute factors of degree at most a fixed $d$, with unrestricted multiplicities. Then there is a deterministic polynomial-time many-one reduction of total-determinant-one TI on this promise to ordinary TI over $F$. For balanced tensors of side $n$ coprime to $q-1$, this is also a reduction of SL-TI. Indeed scalar triples with product one correct any determinant triple with product one because raising to the $n$-th power is bijective on $F^\times$.

The Frobenius action on factors with leading coefficient one puts their coefficients in a single fixed extension $K/F$ of degree dividing $\operatorname{lcm}(1,\ldots,J)$. Factor recovery below gives $P_X=c_X\prod_i Q_{X,i}^{e_{X,i}}$. For each degree- and multiplicity-preserving bijection $\sigma$ of the factors, enumerate $\lambda_i\in K^\times$. Keep the branch if $c_B\prod_i\lambda_i^{e_{A,i}}=c_A$. Impose the original tensor equation and
$$
 Q_{B,\sigma(i)}(Gx)=\lambda_i Q_{A,i}(x).
$$
Every total-determinant-one transporter appears in a kept branch by unique factorization and covariance. Conversely the attached equations and the scalar test enforce preservation of $P$.

On the dual of $K\otimes_F Z$, retain symmetric degrees through $d$ with the multiplication maps between these grades. Products of degree-one vectors span each grade even in positive characteristic. This ties their actions to the actual extended dual action. Include each required pair of scaled factors as named vectors. The dual action is attached using a perfect pairing, the extension by the map $K\times Z\to K\otimes_F Z$, and the field basis is pinned pointwise. The systems consist of linear maps, bilinear maps, constant vectors and the original trilinear tensor. All dimensions are polynomial and there are only constantly many branches. The tensor-system compiler turns every branch into ordinary 3-TI. For completeness, constant disjunctions can be packed by a parity construction. For $k$ branch pairs $X_i,Y_i$, form all ordered tuples selecting $X_i$ or $Y_i$ at each index. Compile each tuple to one ordinary tensor using its named modes and apply the connected three-vertex triangular tensor-to-algebra construction with trivial character and no field padding. Each resulting algebra is directly indecomposable since every diagonal corner is local and the nonzero off-diagonal corners connect the vertices. Its isomorphism class determines the ordered tuple up to TI. Take the algebra direct products for the selections of even and odd parity, and output their multiplication tensors. If any branch is YES, toggling its index matches the two collections up to isomorphism. If all branches are NO, no tuple of one parity is isomorphic to a tuple of the other. Uniqueness of the central indecomposable factors and the equivalence of unital algebra isotopy with isomorphism give exactly the desired answer. All constructions have polynomial size for constant $k$. Zero branches can simply produce a fixed NO. Only $A$ requires the promise. A true ordinary match $B$ inherits it. A nonpromised $B$ passing partial extraction cannot give a false positive since the original ordinary tensor equation remains in the compiled instance. [Chen–Grochow–Qiao–Tang–Zhang, Sections 3–4](https://arxiv.org/html/2306.03135v2)

### Factor recovery from evaluations

For any fixed $D$, assign weights $w_i=\sum_{j=0}^{D}i^j b^j$ with an integer $b>D s^D$ for $s$ variables. Monomials of degree at most $D$ have distinct weights by the no-carry representation and the power-sum identities for multisets of at most $D$ indices. Substitution of $v_i=t^{w_i}$ yields a polynomial-size hitting set for a product of polynomially many polynomials of bounded degree by evaluating at every element of an extension of polynomial cardinality larger than the resulting degree bound. The same weights let us interpolate bounded-degree homogeneous polynomials from curve values.

Use this curve on the entries of $v,u$ to try restrictions to lines $x=v+tu$. A good restriction has full degree and each distinct absolute factor restricts to its full degree in distinct roots, disjoint from the roots of the other factors. Failure is the zero set of a product of leading coefficients, discriminants, and pairwise resultants of bounded degree. None vanishes identically. For a discriminant, choose a direction with nonzero top coefficient and nonzero directional derivative. There is such a direction because an absolutely irreducible positive-degree polynomial has a nonzero partial derivative over the perfect algebraic closure. The factor is coprime to its derivative of smaller degree. For a pairwise resultant use a direction where both leading coefficients are nonzero. The two factors remain coprime after localizing in the coordinates transverse to that direction. A full-degree restriction with the largest number of distinct roots is therefore good. Each individual factor is defined over the curve field and has bounded degree. The restrictions split over an additional extension of degree $\operatorname{lcm}(1,\ldots,d)$, still of polynomial cardinality. Root finding and multiplicity counting can use direct enumeration.

Write $P(v+tu+Cz)/P(u)$ as monic in $t$, using $u$ and the columns of $C$ as a basis. For every good-line root $a$ of multiplicity $e$, specialize $z=s\beta$ at the interpolation directions and compute the bivariate restriction by interpolation. Lift the coprime initial factor $(t-a)^e$ by monic Hensel lifting in $s$, separating the other initial roots. The lift is $(t-a_\beta(s))^e$, where $a_\beta(s)$ is the simple-root lift of the corresponding distinct factor. If $e=p^je'$ in characteristic $p$, with $p\nmid e'$, its coefficient of $t^{e-p^j}$ is $-e' a_\beta(s)^{p^j}$. Precision $dp^j+1$ and inverse Frobenius in the coefficient field recover $a_\beta(s)$ through degree $d$. Each Hensel correction uses the Bézout equations for the two coprime initial factors. For every subset of at most $d$ line roots, multiply its monic linear series factors through degree $d$ in $s$. Interpolate the degree-$i$ homogeneous component in $z$ from each coefficient of $s^i$ by the curve. The homogeneity follows by substituting $z=s\beta$ into the unique multivariate simple-root lifts. The subset of roots of each actual factor recovers it exactly since the total degree is at most $d$.

Discard candidates exceeding degree $d$. Retain candidates whose restrictions divide those of $P$ on a curve test set of lines, skipping zero restrictions of $P$. A candidate coprime to all true factors fails at a test line where all leading coefficients and all the bounded-degree pairwise resultants involving it are nonzero. Every survivor therefore shares a true factor, which has its own good-line root subset contained in the candidate's subset. The inclusion-minimal surviving sets give precisely the true factors. Equality of subsets gives equality of the monic polynomials by divisibility and equal degree in $t$. Multiplicities follow from the good restriction, and one evaluation where $P\ne0$ gives the scalar. All bounds are polynomial at fixed $d,J$. The field extensions used for these operations may be found by enumeration and irreducibility testing of univariate polynomials of degrees logarithmic in the dimensions over $K$. This is polynomial since $K$ has fixed cardinality.

## 3. Recovering all three determinants on a growing family

Let $n=2r+1$, $r\ge5$. The family consists of tensors having the following form in some bases:
$$
 T((a,x),(b,y),(c,z))=abc+a\,y^{\mathsf T}z+b\,x^{\mathsf T}z+c\,x^{\mathsf T}Cy.
$$
The three modes are $F\oplus F^{2r}$. Here $C$ is an arbitrary $2r\times2r$ matrix such that $C-C^{\mathsf T}$ is invertible. The bases need not be supplied. For a pair with first member in this family and any prescribed determinant character value, a deterministic polynomial-time procedure outputs the unchanged ordinary-TI instance or a fixed ordinary-TI NO instance. The output is YES exactly when the desired character value occurs.

**Recover the hyperplanes.** Order the three anchor coordinates first. On the remaining $6r$ coordinates the alternating matrix is
$$
 D=\begin{pmatrix}
 0&cC&-bI\\
 -cC^{\mathsf T}&0&aI\\
 bI&-aI&0
 \end{pmatrix}.
$$
Every matching in its Pfaffian has $r$ edges between each pair of mode slots, by counting the incidences at each slot. Hence $\operatorname{Pf}(D)=\kappa(abc)^r$. Over the rational function field the system $D(x,y,z)=(p,q,s)$ has the solution
$$
\begin{aligned}
 x &= \tfrac{a}{bc}Mp+\tfrac{1}{c}Mq+\tfrac{1}{b}MCs,\\
 y &= \tfrac{1}{c}Mp+\tfrac{b}{ac}Mq+\tfrac{1}{a}(MC-I)s,\\
 z &= \tfrac{1}{b}C^{\mathsf T}Mp+\tfrac{1}{a}(I+C^{\mathsf T}M)q
                   +\tfrac{c}{ab}C^{\mathsf T}MCs,
 \qquad M=(C-C^{\mathsf T})^{-1}.
\end{aligned}
$$
This proves $\kappa\ne0$ and $(abc)D^{-1}$ has homogeneous quadratic entries. Delete the row and column for $a$. Alternating block elimination yields the Pfaffian of $D$ times the Pfaffian of the remaining $2\times2$ alternating matrix. Its upper entry is $a+H/(abc)$, where $H$ is homogeneous of degree four since the entries adjoining $D$ to the axes are linear. The $a$-cofactor equals $\kappa(abc)^{r-1}(a\,abc+H)$.

In fact $a\mid H$. Use the cofactor identity for all three axes. Applying the same rational inverse formula after deleting $b$ or $c$ gives
$$
 C_T(x)_a=\kappa(abc)^{r-1}(a\,abc+H_a),\quad
 C_T(x)_b=\kappa(abc)^{r-1}(b\,abc+H_b),\quad
 C_T(x)_c=\kappa(abc)^{r-1}(c\,abc+H_c)
$$
for quartics $H_i$, absorbing any sign choices into them after taking signed cofactors. Since $b C_T(x)_a=a C_T(x)_b$ as polynomials, cancellation and relative primality of $a,b$ give $a\mid H_a=H$. Consequently
$$
 P_T=\kappa(abc)^{r-1} Q,\qquad Q=abc+H/a .
$$
At zero internal coordinates $Q=abc$. Thus $a,b,c$ are exactly the three factors of multiplicity at least four, and all other factors have degree at most three. There are at most six distinct factors. Section 2 recovers the three distinguished hyperplanes $H_i$ in raw coordinates, with the modes distinguishable by the factors' supports.

**Recover the axes.** Choose representatives $u_i$ at which a selected equation of $H_i$ is one. Seek $v_i=u_i+p_i$ with $p_i\in H_i$ satisfying
$$
 T(v_1,v_2,H_3)=T(v_1,H_2,v_3)=T(H_1,v_2,v_3)=0 .
$$
These are jointly affine-linear because $T(H_1,H_2,H_3)=0$. For existence in the original model, rescale the desired $v_i$ to have anchor coordinate one. If their internal coordinates are $w_1,w_2,w_3$, the constraints become $w_2=-w_1$, $w_3=-C^{\mathsf T}w_1=Cw_1$, and have the zero solution. Every solution comes from $w=w_1\in\ker(C+C^{\mathsf T})$. If the characteristic is two, this kernel is zero by hypothesis. Otherwise $w^{\mathsf T}Cw=0$, since $2w^{\mathsf T}Cw=w^{\mathsf T}(C+C^{\mathsf T})w$.

For every solution the axis anchors of the model can be shifted by $(w,-w,Cw)$ in their respective complements. The shift is a trilinear automorphism of determinant one in each mode. Indeed it preserves all terms with at least two complementary inputs since $T(H_1,H_2,H_3)=0$, the terms with exactly one complementary input vanish by the shift equations, and the value on the three shifted anchors is $1-w^{\mathsf T}Cw=1$. Its inverse subtracts the same shifts. Thus any two admissible triples of complementary lines are related by such an automorphism after separately normalizing the anchor coordinates. After finding any solution, rescale the representatives so $T(v_1,v_2,v_3)=1$. Choose a basis of $H_3$ and dual bases of $H_1,H_2$ using the nondegenerate pairings $T(-,v_2,-)$, $T(v_1,-,-)$. This writes the tensor in the displayed normal form again, with an explicit new $C$. Check the required equations and nonsingularity, returning NO if they fail on $B$ because an ordinary match inherits the promise.

**Compute the coset.** Every transporter maps the canonical hyperplanes to their counterparts, and sends any chosen axis triple to an admissible axis triple. Composing with a target shift as above makes it preserve the chosen axis triple without changing its determinant values. Such a transporter is block diagonal $(\lambda,X),(\mu,Y),(\nu,Z)$, with $\lambda\mu\nu=1$. Comparing terms gives
$$
 \lambda Y^{\mathsf T}Z=I,\quad
 \mu X^{\mathsf T}Z=I,\quad
 \nu X^{\mathsf T}C_B Y=C_A.
$$
It follows that $Y=(\mu/\lambda)X$, $Z=\mu^{-1}X^{-\mathsf T}$, and $X^{\mathsf T}C_BX=\lambda^2C_A$. Put
$$
 \pi=\operatorname{Pf}(C_A-C_A^{\mathsf T})/
          \operatorname{Pf}(C_B-C_B^{\mathsf T}).
$$
Covariance yields $\det X=\lambda^{2r}\pi$. The trilinear determinant triple in the adapted frames therefore lies in
$$
 \{(\lambda^n\pi,\;\mu^n\pi,\;\nu^n\pi^{-1}):
       \lambda,\mu,\nu\in F^\times,\ \lambda\mu\nu=1\}.
$$
If any ordinary transporter exists, multiplying it by scalar triples of product one shows that the whole displayed set occurs. Multiply each coordinate by the determinant of the target adapted basis divided by that of the source adapted basis to express the triple in raw trilinear coordinates. Invert the determinants for the covariant convention. Test the requested character on the resulting constant-size list. If the condition fails throughout the list, report NO. Otherwise ordinary TI of the original pair decides the character instance.

**Scalar pair adjoints.** For all $r\ge5$ take $C_j=\begin{pmatrix}0&1\\0&0\end{pmatrix}$. In the first mode the anchor slice is the identity and the complementary slices are $E_{j1,0}+E_{0,j2}$, $E_{j2,0}$. Their product gives $E_{00}$, so the common commutant preserves the anchor and complement. Acting on $e_0$ with these slices now forces the common commutant to act by the same scalar on each complementary vector. The second mode works with $E_{j1,0}$, $E_{j2,0}+E_{0,j1}$ and the opposite product. In the third mode the slices are $M_0=\operatorname{diag}(1,C)$, $M_i=E_{0i}+E_{i0}$. If $P M_i=M_i R$, the simultaneous kernel conditions force $Re_j\in Fe_j$ for every $j>0$. Applying the equations at $e_i$ gives $Pe_0=d e_0$ and a common diagonal value $d$ for $R$ on the complement. At $e_0$ the equations give $Pe_i=a e_i+w_i e_0$ where $Re_0=a e_0+w$. Now $P M_0=M_0 R$ implies $a=d$, $Cw=0$ and $w^{\mathsf T}C=0$. The two kernels intersect trivially. The examples are concise by their invertible anchor slices in the first two modes and by independence of the third-mode slices. For $q>2$, a nonidentity total-determinant twist gives an ordinarily isomorphic pair with no total-determinant-one transporter, since the displayed coset for automorphisms has total determinant one.

## 4. Raw extraction for triangular multiplication tensors

There is a deterministic polynomial-time normalization from a raw tensor ordinarily isomorphic to the multiplication tensor of a unital associative algebra to an actual algebra table. For its bilinear map $B:V_1\times V_2\to V_3$, use linear equations to compute the pair algebras defined by $B(Xu,v)=ZB(u,v)$ and $B(u,Yv)=ZB(u,v)$. In multiplication coordinates these consist of left and right multiplications, respectively. For example the first equation at $v=1$ gives $Z=X$, and then $X(uv)=X(u)v$ gives $X=L_{X(1)}$. Each input mode is a regular module for its pair algebra, so its cyclic vectors correspond to units. The algorithms for the radical and a generator of a cyclic module find these vectors deterministically in polynomial time over a fixed finite field. [Ivanyos, constructive finite algebra algorithms](https://real-d.mtak.hu/260/1/Ivanyos_Gabor-dr.pdf)

For cyclic vectors $u_0,v_0$ both slices $L_X(u)=B(u,v_0)$, $R_X(v)=B(u_0,v)$ are invertible. The table on $V_3$ is $\mu_X(z,z')=B(L_X^{-1}z,R_X^{-1}z')$. In multiplication coordinates this is $z b^{-1}a^{-1} z'$ for units $a,b$, so is isomorphic to the original algebra. For a raw pair $A,B$, put $u_X=\det L_X\det R_X$ in the fixed bases on each side. The normalized covariant determinant product equals the raw product multiplied by $u_A/u_B$. Every isotopism of unital associative algebras has form $(L_a\theta,R_b\theta,L_aR_b\theta)$ in bilinear variables, where $\theta$ is an algebra isomorphism and $a,b$ are units. Setting each input in turn to the identity proves the unit properties and shows that $\theta(x)=a^{-1}h(x)b^{-1}$ is multiplicative. Direct substitution gives the converse. The normalized covariant determinant product is therefore $(\det\theta)^{-1}$. In particular raw total determinant one is equivalent to $\det\theta=u_B/u_A$.

For the triangular algebra with diagonals $F[t]/(t^{M_i})$, corner modules $X_i\otimes F[t]/(t^{k_i})$ with $k_i\ge2$, and padding by fields of distinct bounded odd degrees, compute the radical $J$ and lift primitive quotient idempotents to an orthogonal system. The directed incidences order the three triangular idempotents. The remaining idempotents give the padding fields. One can find the quotient idempotents from simultaneous eigenspaces of basis multiplications in the commutative quotient over a fixed common splitting field, followed by grouping Frobenius orbits. To lift an idempotent, start at a representative $e$ and replace it by $e-(2e-1)^{-1}(e^2-e)$. The inverse exists since $(2e-1)^2=1+4(e^2-e)$, and the error moves into the square of its previous ideal, by multiplication of commuting terms. Lift the remaining idempotents in the complementary corner. Nilpotence gives the exact lifts in polynomial time.

Recover $W_{ij}=e_iAe_j/(e_iJe_i)(e_iAe_j)$ and their corner product by linear algebra. To calibrate determinants, choose diagonal radical generators $t_i$ subject to $t_i z=zt_j$ on each incident corner. Pin a $t_0$ nonzero modulo the square of its local radical and solve the linear equations. In model coordinates one can use the same polynomial in $t$ for all the generators, truncated to the respective lengths. Since $k_i\ge2$, equality of the corner actions forces the same nonzero first-order coefficient at every vertex.

Take adapted algebra bases from the powers of the chosen diagonal generators, powers of the corner generators applied to lifts of the residue bases, and arbitrary bases on the padding fields. An algebra isomorphism aligns the chosen idempotents up to conjugation by a radical unit, which has determinant one. In fact if $(e_i)$ and $(f_i)$ agree modulo the radical, $u=\sum_i f_i e_i$ is one modulo the radical and satisfies $ue_i=f_i u$. Left and right multiplication by $u$ are unipotent. After this alignment each diagonal map sends its parameter to $\lambda t+O(t^2)$, with a common $\lambda$ by comparison on each corner modulo $t^2$. On corner layer $t^jW_i$ the map is $\lambda^j a_i$, where $a_i$ is its residue map. On diagonal layer $t^jF$ the map is $\lambda^j$. The padding automorphisms have determinant one since Frobenius permutes the geometric coordinates in an odd-length cycle. Hence the algebra determinant in the raw bases is the known target-to-source adapted basis ratio times
$$
 \lambda^{\,\sum_i\binom{M_i}{2}+\sum_i\dim(W_i)\binom{k_i}{2}}
 \prod_i(\det a_i)^{k_i}.
$$
In the normalization for determinant characters the $\lambda$-exponent vanishes modulo $q-1$. Every residue transporter lifts, since one can choose any identifications with the respective triangular models and transport residue maps coefficientwise there. Thus the formula describes the exact algebra determinant values in arbitrary frames. On cores from Section 3, it reduces the raw normalized multiplication-tensor character problem to one ordinary TI instance. The basis ratios and $u_B/u_A$ give the prescribed value in the residue character test. On padded side length coprime to $q-1$ this also decides the SL test. The triangular construction uses Grochow and Qiao's tensor-to-algebra reduction with independent truncated corner lengths in the determinant-character normalization. [Grochow–Qiao](https://doi.org/10.1137/21M1441110)

## 5. Scope of the Pfaffian test

The Pfaffian polynomial of Section 1 vanishes identically on the full odd-dimensional alternating extension of the multiplication tensor of the normalized triangular algebra. At $(1,1,\ell)$ in $A\oplus A\oplus A^*$, the skew blocks are the pairing $B_\ell(a,b)=\ell(ab)$ and the two identity pairings. Eliminating the identity blocks identifies the radical with $\{a : \ell([a,A])=0\}$. It contains the center, which includes two independent elements, the unit and the common parameter $t$. Since the alternating matrix is odd dimensional, its radical has dimension at least three. Over the algebraic closure the points with invertible first two entries are dense. Left and right multiplication by these units gives an isotopism carrying a point of the displayed shape to each such point, for an appropriate initial $\ell$. Rank is preserved, so the maximal Pfaffian cofactors vanish identically. Padding only enlarges the center.

The raw normalization and calibration apply the determinant test to the recovered core. The family of Section 3 has exact character recovery from arbitrary bases in polynomial time. An unrestricted normalized triangular algebra can carry an arbitrary residue tensor, whose Pfaffian may vanish or have unbounded-degree factors. The reduction for the full multiplication-tensor class remains open. These arguments are informal. Publication priority has not been established.
