# Constructive tensor isomorphism from crossed invertible flattenings

**Theorem.** Let $d\ge 2$. For matched format
$$
 (n_1,\ldots,n_d,n_1,\ldots,n_d),\qquad n_i\ge 3,\qquad m=\prod_i n_i,
$$
there is an intrinsic, recognizable class of tensors on which ordinary tensor isomorphism is solvable constructively in $O(m^3+\sum_i n_i^6)$ field operations. No mode frames are supplied. The class is nonempty Zariski-open in every characteristic. Over $\mathbb F_q$ it contains a proportion at least
$$
 1-\frac{2m+3m\sum_{i=1}^d(n_i^2-1)}{q}
$$
of all tensors. This numerical bound is informative for growing $q$. For each fixed $q,d$, a polynomial-time relaxation of the class still contains infinitely many dimensions with at least $q^{\Omega(N^{2d}/(\log N)^{2d-1})}$ different accepted orbits, where $N$ is the common size of a mode. This includes $q=2$. All conclusions below are informal.

## 1. A transportable tuple of local matrices

View the tensor as its square flattening $F$ between the first $d$ and the last $d$ modes. Let $\Gamma$ exchange the row and column index for the last matched pair. Thus in the original flattening coordinates $\Gamma$ is partial transpose on the last factor. Require $F$ and $\Gamma(F)$ to be invertible. Define
$$
 H(F)=\Gamma((\Gamma(F))^{-1}),\qquad
 U(F)=F H(F)-I,\qquad
 A_{i,r}(F)=\operatorname{Tr}_{\{1,\ldots,d\}\setminus\{i\}}(U(F)^r)
 \quad (r=2,3).
$$
The trace here contracts each discarded mode with its dual.

Write $L=\bigotimes_i L_i$, $R=\bigotimes_i R_i$ for a candidate transporter, so a target flattening satisfies $F'=LFR^{\mathsf T}$. Its crossed flattening has the same form with the factors $L_d,R_d$ exchanged. Inversion swaps the left and right inverses, and undoing the crossing gives
$$
 H(F')=R^{-\mathsf T}H(F)L^{-1}.
$$
Thus $U(F')=L U(F)L^{-1}$, and partial traces show $A_{i,r}(F')=L_i A_{i,r}(F)L_i^{-1}$. This follows also directly from trace cyclicity on the factors being discarded. The two powers use the same crossed inverse. A single partial trace of $F H(F)$ on either side of the crossing is a scalar identity, by the crossed inverse identity, motivating higher powers.

## 2. Exact coordinate recovery and runtime

For every $i$ compute the dimension $c_i(F)$ of the simultaneous commutant of $A_{i,2}(F),A_{i,3}(F)$ by linear equations in $n_i^2$ unknowns. The main class requires $c_i(F)=1$ for every $i$. Membership uses only the raw tensor and is invariant under tensor isomorphism.

For two accepted tensors, solve the homogeneous intertwiner equations
$$
 X_i A_{i,r}(F)= A_{i,r}(F')X_i,\qquad r=2,3.
$$
If there is an invertible intertwiner, the solution space is that intertwiner times the source commutant. Therefore it has dimension one, and its nonzero basis vector is invertible. A space of another dimension, or a singular basis vector, rules out an isomorphism. Take the invertible representatives $X_i$ if they exist, form $X=\bigotimes_i X_i$, and compute
$$
 Q^{\mathsf T}=F^{-1}X^{-1}F'.
$$
The representatives differ from any true left factors by scalars, which can all be absorbed on the right. Thus a transporter exists exactly when $Q$ is a tensor product of $d$ matrices of sizes $n_i\times n_i$. Group its entry indices by matched mode, so this is an ordinary rank-one tensor test in dimensions $n_1^2,\ldots,n_d^2$. Recover the factors from a nonzero pivot entry and verify all entries. They are invertible because $Q$ is. The resulting factors give a directly checkable transporter.

Dense matrix inversion and products cost $O(m^3)$ field operations. Computing all partial traces costs at most $O(dm^2)$, and $d\le \log_3 m$. Each intertwiner or commutant system has $n_i^2$ unknowns and $2n_i^2$ equations and costs $O(n_i^6)$. The Kronecker check costs $O(dm^2)$. With a conventional finite-field representation supporting polynomial bit-cost field arithmetic this gives a deterministic polynomial-bit-time algorithm. The algorithm uses field arithmetic and Gaussian elimination, including in characteristic two.

A relaxation uses $\sum_i c_i(F)$ as a parameter. First compare dimensions on the source and target, rejecting a mismatch. If an invertible intertwiner exists, its solution space has dimension $c_i(F)$. In each mode of this dimension, enumerate the $q^{c_i(F)}$ possible intertwiners and retain the invertible ones. Run the same Kronecker test on each combination. The total field-operation bound is
$$
 O\!\left(\sum_i n_i^6+
          q^{\sum_i c_i(F)}\bigl(m^3+\sum_i n_i^3\bigr)\right).
$$
This is polynomial at fixed $q$ if the sum is $O(\log_q m)$.

## 3. Why the main class is open and nonempty

The statement needs a witness in every characteristic. The construction below proves the stronger property that each local pair generates the full matrix algebra. Work over a field of rational functions over the prime field, retaining independent variables throughout.

Use the decomposition into factors on the two sides of the partial transpose. Expand at $F=I+tX$. For $X=\sum_j B_j\otimes C_j$, multiplication of the inverse series gives
$$
 U(F)=t^2Y(X)+O(t^3),\qquad
 Y(X)=\Gamma((\Gamma X)^2)-X^2
     =-\sum_{j<k}[B_j,B_k]\otimes[C_j,C_k].
$$
Choose diagonal matrices $D_1,D_2$ with distinct formal entries in the two factors. With $X=D_1\otimes D_2+s Z$, the coefficient of $s$ in $Y(X)$ is
$$
 -(\operatorname{ad}_{D_1}\otimes\operatorname{ad}_{D_2})(Z).
$$
An off-diagonal matrix unit is an eigenvector of its respective adjoint map with nonzero eigenvalue. Consequently this coefficient can be set to any tensor of off-diagonal matrices on the two sides.

Fix a desired mode $i$, and choose a mode on the opposite side of the crossing. Let their dimensions be $a,b$, with $a$ belonging to $i$. On the $a$-dimensional side let $P$ be the cyclic shift and $D_\beta,D_\gamma$ diagonal with independent entries. On three coordinates of the $b$-dimensional side prescribe
$$
 Y_0=P\otimes E_{01}+(D_\beta P^{-1})\otimes E_{10}
       +P\otimes E_{12}+(D_\gamma P^{-1})\otimes E_{20}.
$$
Put a diagonal rank-one coordinate projector on every spectator mode. Each term remains off-diagonal on both sides of the crossing, so the preceding linearization applies. Each spectator contributes trace one to its powers, even when the characteristic divides its dimension.

The only closed two-step walks on the displayed three-coordinate directed graph use $01,10$. The only closed three-step walks are the three rotations of $01,12,20$. Taking the trace of the $b$-dimensional factor therefore gives
$$
 \operatorname{Tr}_b(Y_0^2)=P D_\beta P^{-1}+D_\beta,\qquad
 \operatorname{Tr}_b(Y_0^3)=
 (P^2D_\gamma P^{-2}+P D_\gamma P^{-1}+D_\gamma)P .
$$
The first is diagonal with pairwise different entries as rational functions, since $a\ge3$. The second is a weighted cyclic shift with all weights nonzero as rational functions, including in characteristics two and three. These two matrices generate all matrix units. More precisely if they are $A,B$, the $a^2$ words $A^uB^v$ for $0\le u,v<a$ are linearly independent. Fixed $v$ uses one cyclic diagonal and has a Vandermonde matrix of coefficients in $u$, and distinct $v$ have disjoint supports.

To apply this to $A_{i,2}(F),A_{i,3}(F)$, divide them by $t^4s^2,t^6s^3$, respectively, first set $t=0$ in the normalized expansion, and then set $s=0$. The limits are exactly the preceding two local matrices. Thus the determinant of the columns of the corresponding $a^2$ words is a nonzero rational function of the tensor entries. This argument applies to each mode separately. The product of the resulting finitely many nonzero witness polynomials is nonzero over every prime field. It gives simultaneous generation on every mode over the algebraic closure, so the weaker scalar-commutant condition is also nonempty open.

For the numerical density estimate, put $\delta=\det\Gamma(F)$. Entries of $U(F)$ have a common denominator $\delta$, with numerators of degree at most $m$. Each commutation matrix can be cleared by the common factor $\delta^3$, producing degree at most $3m$ in each entry. From the witness, some $(n_i^2-1)$-minor of that cleared matrix is a nonzero polynomial over the prime field. Multiply one for each $i$ and the two flattening determinants. The product has degree at most $2m+3m\sum_i(n_i^2-1)$. Its nonvanishing implies membership, so the polynomial zero bound gives the theorem. In equal four-way format one can also require the third balanced flattening to be invertible by multiplying its determinant and increasing the degree bound by $m$. Its determinant is a nonzero polynomial because balanced flattening is just a rearrangement of independent entries.

## 4. The small-field families

Fix $q,d$ and equal seed dimension $n\ge 3$. Choose an extension $K=\mathbb F_{q^e}$ with $e$ prime and $e=O(\log_q n+1)$. We choose $q^e$ larger than a constant times the polynomial degrees below. Bertrand's postulate gives such $e$, and $q^e$ is polynomial in $n$ for fixed $q,d$.

Require the seed to have the full generation property from §3 on each of its $d$ modes. The product of its generating-word determinants, after clearing denominators column by column, has polynomial degree in $n$. Indeed the column for $A_{i,2}^uA_{i,3}^v$ has numerator degree at most $m(2u+3v)$. Also require that for each $i$ the second characteristic polynomial coefficient of $A_{i,2}$ lies outside $\mathbb F_q$. This coefficient is a nonconstant rational function in every characteristic. To see this, use the two-parameter leading term above. The second coefficient of the limiting diagonal $P D_\beta P^{-1}+D_\beta$ is nonzero, as setting just one $\beta$ to a nonzero value gives two equal nonzero diagonal entries and second coefficient $\beta^2$. Before normalization by $t^4s^2$ the coefficient vanishes at $t=0$, but the nonzero leading term shows it is not identically zero. Thus none of its equations with target value in $\mathbb F_q$ is an identity. Clear by $\delta^4$, giving a polynomial of degree at most $4m$ for each forbidden value. A union bound now gives at least $|K|^{m^2}/2$ suitable seed tensors for a sufficiently large polynomial choice of $|K|$. Since $e$ is prime, the selected coefficient has $e$ distinct conjugates under $q$-Frobenius.

Work next over $\mathbb F_q$ and put $V_i=K^n$ with its base-field vector space structure. Let the last $d$ modes be the duals in chosen coordinates. Construct an endomorphism $F_0$ of $\bigotimes_{\mathbb F_q} V_i$ that applies the seed $F$ on the diagonal summand $\bigotimes_K V_i$ and acts as identity on its complementary summand. The projection onto this summand is the idempotent of $K^{\otimes_{\mathbb F_q}d}$ for its multiplication map to $K$. This idempotent exists because the tensor algebra is a product of fields. Equivalently, after extending scalars to $K$, each $V_i$ splits into copies indexed by embeddings $\sigma:K\to K$. On a sector with all embedding labels equal to $\sigma$, the restriction of $F_0$ is $F^\sigma$. On all other sectors it is identity. This operator descends since its sector description is invariant under the simultaneous Frobenius action. Choosing dual bases on the last $d$ modes, partial transpose preserves the sector decomposition and operates within each sector. Hence both flattenings are invertible.

After extension to $K$, $U(F_0)$ is zero on the sectors with unequal labels. For mode $i$, taking partial traces leaves exactly the corresponding conjugate $A_{i,r}(F)^\sigma$ on its $\sigma$ sector. Each pair generates a full matrix algebra, so defines a simple module for the algebra on two noncommuting generators. Different $\sigma$ define nonisomorphic modules, by the selected characteristic coefficient. There are no intertwiners between distinct simple modules. The commutant over $K$ thus has $e$ scalar blocks, and its dimension over $K$ is $e$. Its defining linear equations descend, giving $c_i(F_0)=e$ over $\mathbb F_q$. The relaxed algorithm therefore runs in polynomial time, including when $q=2$.

With $N=en$, the restriction map on seeds is injective and produces at least $q^{e n^{2d}}/2$ distinct raw tensors. Each can have at most $q^{2dN^2}$ tensors in its orbit. Subtracting that term in the exponent gives $q^{\Omega(N^{2d}/(\log N)^{2d-1})}$ accepted orbits in this infinite sequence of dimensions. This is an absolute family-size lower bound. The large-field numerical density estimate in §3 and the binary experiments below concern different coverage statements.

## 5. An objectwise canonical form using matrix-tuple canonization

For the dual modes use the transposes of the corresponding partial traces of $(H(F)F-I)^r$. These are genuine conjugation covariants under $R_i$. Their perturbation about $F=I+tX$ has the same leading $Y(X)$, now transposed on the retained mode after taking the partial trace. Thus the condition that all $2d$ local commutants are scalar is also nonempty open in every characteristic. The degree estimate from §3 applies with both sets of commutation minors.

Canonize each of the $2d$ ordered local covariant pairs by matrix-tuple conjugation canonization. Solve its intertwiner system to obtain a frame between the raw and canonical local pair. It is unique up to a scalar. Apply those frames to the input tensor and divide by its first nonzero entry in the fixed coordinate order. The result is a canonical tensor representative. If inputs are isomorphic, their local canonical pairs agree and the two framed tensors differ by only a scalar, which the normalization removes. Conversely the normalized tensor is itself isomorphic to its input, so equal outputs imply isomorphism.

This gives Las Vegas polynomial-bit-time canonical representatives on this stronger class using the published tuple canonizer. For a database of $B$ tensors, this uses one preprocessing for each input and then sorts the $B$ canonical arrays to group the orbits. Exhaustive pair matching would make $\binom B2$ separate pairwise solver calls. The canonical-form extension relies on the cited primitive, whereas the pairwise solver in §2 needs only linear algebra. [Canonical forms for matrix tuples in polynomial time](https://arxiv.org/abs/2409.12457)

## 6. Rational inputs and specified determinants

The pairwise algorithm in §2 runs in deterministic polynomial bit time over $\mathbb Q$. For each inverse or linear system, clear input denominators using their product and apply fraction-free elimination. The determinant bounds for integer minors give polynomial bit lengths for all entries of the inverse or a basis of solutions. There are a constant number of sequential linear-algebra stages. The modewise systems in a single stage are independent, and forming the Kronecker product adds the bit lengths of the factors. This preserves the polynomial bound even with $d$ part of the input. The nonzero witness polynomial from §3 also proves coverage of all but at most a fraction $[2m+3m\sum_i(n_i^2-1)]/(2B+1)$ in an integer tensor box $\{-B,\ldots,B\}^{m^2}$.

On the scalar-commutant class, every other transporter differs from a returned transporter by a scalar on every mode, and the product of all these scalars is one. For the first $d$ modes this follows from the one-dimensional intertwiner spaces. Once these scales are specified, the right product is forced by the invertible flattening equation. Uniqueness of a rank-one tensor's nonzero factors up to scalars of prescribed product gives the assertion on the remaining modes.

Let the returned transporter have mode determinants $\eta_i$, let $\nu_i$ be prescribed determinants, and let $a_i$ be the mode sizes over all $2d$ modes. Test whether the equations $z_i^{a_i}=\nu_i/\eta_i$ have roots whose product is one. Enumerate the root lists and test their Cartesian product, of size at most $\prod_i a_i=m^2$. Over $\mathbb Q$, exact integer root tests on reduced numerator and denominator compute each root list, including signs. At fixed finite field size enumerate the field, and over a varying finite field use Las Vegas univariate polynomial factorization. Thus determinant-one tensor isomorphism is constructively polynomial on the same class, deterministically over $\mathbb Q$ and every fixed finite field. The root checks allow repeated roots in small characteristic.
## 7. Scope, sources, and controls

The closest finite-field comparison is Li–Li–Qiao–Tao–Wang's 4-tensor algorithm, which extracts raw kernel matrix codes from a corank-three balanced flattening. The present method uses raw full-rank crossed flattenings, and simultaneously invertible balanced cuts already give a provably abundant regime over growing fields. The method is a polynomial-time replacement for enumerating independently changed mode bases and verifying the tensor identity on this class. The published kernel-based method and this method have different hypotheses. For fixed small $q$ our proof gives the explicit family above and exact finite controls. A uniform fixed-$q$ acceptance probability theorem is still open here. [Li–Li–Qiao–Tao–Wang, §4](https://arxiv.org/html/2604.00591v2#S4)

The parallel with the MathProofs channel construction is the use of partial traces to recover local coordinates. The channel construction uses a high spectral projector and orthogonality. Here the crossed inverse supplies a dual that transforms contragrediently under general linear actions, making the tensors and their exact local power traces available over finite fields. The project’s cyclic-quotient approach starts from a supplied computable cyclic covariant. The current formulas construct local covariants directly in the stated tensor formats, and the intertwiners can be recovered without factoring characteristic polynomials. Priority for these formulations has not been established. [MathProofs noisy Choi recovery](https://github.com/Dugongue/MathProofs/blob/main/FourIsomorphismResearchBets/QUANTUM.md) · [MathProofs cyclic quotient](https://github.com/Dugongue/MathProofs/blob/main/TensorFrameRecovery/CYCLIC-QUOTIENT.md)

The accompanying exact binary test sampled 200 dense raw tensors in each of six formats. It accepted 101 of the 108 with both prescribed flattenings invertible, and recovered all four hidden basis changes on 30 of those inputs after independent invertible scrambling. The samples used side lengths $3,4,5,6,8$, and the rectangular format $3\times7\times3\times7$. These are exact computational controls of the formulas and transporter. The uniform coverage and competing-solver timing on these formats are unmeasured. [Exact binary control](check_finite_recovery.py)
