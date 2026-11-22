# Polynomial Calculus degree under the Lovitz–Petrov condition

**Theorem.** Let $k$ be a field and let $T,S$ be explicit three-tensors inequivalent over $\bar k$. Suppose $T=\sum_{i=1}^{r}a_i\otimes b_i\otimes c_i$ over $\bar k$, all terms nonzero. For every $I\subseteq[r]$ with $|I|\ge2$ assume
$$
\dim\langle a_i:i\in I\rangle+\dim\langle b_i:i\in I\rangle+
\dim\langle c_i:i\in I\rangle\ \ge\ 2|I|+2 .
$$
Then the cubic three-tensor isomorphism equations with quadratic named inverses have a Nullstellensatz refutation, and hence an ordinary Polynomial Calculus refutation, of degree $O((r+1)^3)$, without field equations. There is no decomposition hypothesis on $S$. In fact $r$ is both the ordinary geometric rank and the geometric border rank. The good probe constructed below attains alternating contraction rank $2r$, whereas any rank-one summand contributes at most two to that matrix rank. The same inequality on border rank follows from closedness of the matrix rank condition for a fixed probe. This is a sufficient case of Question 7.1. [Literal equations and Question 7.1](https://arxiv.org/abs/2305.19320) · [Lovitz and Petrov](https://doi.org/10.1017/fms.2023.20) · [Sivan's alternating contraction construction](https://arxiv.org/abs/2609.13693)

For a concrete case outside the classical Kruskal inequality, take five summands and let the three factor lists in separate copies of $k^4$ be
$$
(e_1,e_2,e_3,e_1+e_2+e_3,e_4),\quad
(e_1,e_2,e_3,e_4,e_1+e_2+e_3+e_4),\quad
(e_1,e_2,e_3,e_4,e_1+e_2+e_3+e_4).
$$
The three Kruskal ranks are $3,4,4$, with sum $11<12$. The subset dimension inequality holds since any three columns of the first list are independent and any four of either other list are independent. For the whole set the sum of ranks is $12$.

## Polynomial certificates

Throughout, a degree-$D$ certificate of an equation expresses its difference as a linear combination of original equations, with each summand of degree at most $D$. The same convention applies with temporary branch equations. A polynomial substitution into a fixed polynomial identity is an exact identity; substitution of certified equalities into a polynomial follows by telescoping one factor at a time in each monomial. We track the total degrees of the substituted entries. All polynomial matrix identities below are interpreted entry by entry, and coefficients in formal parameters can be extracted from a certificate. In particular, symbolic basis changes and the use of a polynomial of many monomials do not impose any bound on proof size.

By cancelling the other actions with their named inverses in each flattening equation, the forward witness maps the source support in each mode into the target support. Indeed, the forbidden block multiplied by the full-row-rank supported flattening is zero, and a constant right inverse cancels this flattening. The reverse tensor equation follows from the three named inverses and yields the reverse block conditions. These have constant-degree certificates. On the support blocks the inverse identities are still valid. Unequal support dimensions then give a contradiction by taking a minor of one more than the smaller dimension on an identity factored through the smaller space. Thus we can assume the common mode dimensions are at most $r$. The zero case is immediate and the rank-one case follows already from support compression. The proof uses constants over $\bar k$. Finitely many suffice and a $k$-linear functional taking $1$ to $1$, applied coefficientwise to the final certificate, descends it.

Set $V=V_A\oplus V_B\oplus V_C$, and embed tensors in $\bigwedge^3 V$ using $a\otimes b\otimes c\mapsto a\wedge b\wedge c$. For $M$ a tensor and $p$ a covector, let $\Omega_p(M)$ be the alternating matrix of the contraction $\iota_p M$ in this exterior model. If $g$ is the block diagonal matrix of the three forward witnesses and $g'$ its named inverse, then
$$
\Omega_{p g'}(S)=g\Omega_p(T)g^{\mathsf T}.
\tag{1}
$$
There is a constant-degree certificate in the witness entries and the indicated relation is linear in $p$. This follows by wedge expansion of the literal tensor equation, using $g'g=I$. We also use its reverse.

## A good probe on the source

Write $F_i=\langle a_i,b_i,c_i\rangle\subset V$, of dimension three. There are two vectors in each $F_i$ whose joint span $L$ has dimension $2r$, whose span avoids each of the $3r$ individual factor vectors, and for which $F_i,F_j$ have independent images modulo $L$ whenever $i\ne j$. To prove this, use the linear Hall selection principle: a collection of subspaces admits an independent choice of one vector from each iff every subcollection spans at least its cardinality. The sufficiency follows by induction: split off a proper nonempty subcollection attaining equality and quotient its span, or, when all proper subcollections have strict inequality, choose a nonzero vector from the last member and quotient its line. Apply the principle to two copies of every $F_i$ and three copies for any designated pair. The required dimension conditions follow from the hypothesis, including the singleton condition. Thus the independence modulo $L$ for each designated pair is a nonempty open condition on the chosen vectors. Apply the principle also to the two copies after quotienting by any designated factor line. A singleton still has dimension at least two in that quotient, and larger subsets have the required rank by the hypothesis. The noncontainment of that factor line is another nonempty open condition. The finitely many such opens in the product of the vector spaces intersect over $\bar k$.

Now choose $p$ annihilating $L$ and nonzero on all the factor vectors. For $F_i$, the plane $F_i\cap\ker p$ is its selected two-plane in $L$. The corresponding individual contraction $\Omega_p(a_i\otimes b_i\otimes c_i)$ is an alternating bivector on that plane of rank two. Thus $\Omega_p(T)$ has rank $2r$. The ratio $\rho_i=q(v)/p(v)$ on each nonzero quotient line $F_i\bmod L$ is well-defined for $q$ annihilating $L$. Pairwise independence gives $q$ with distinct $\rho_i$. This is the alternating pencil construction. The two off-diagonal blocks $AB$ and $AC$ of each individual $\Omega_p(a_i\otimes b_i\otimes c_i)$ are nonzero because $p$ is nonzero on all factors. All arguments so far work in arbitrary characteristic.

## An equivariant polynomial test for probes on the target

Every contraction of $T$ has rank at most $2r$, identically in $p$, since it is a sum of $r$ alternating matrices, each factoring through a fixed three-dimensional subspace and of rank at most two. If a fixed $p_t$ makes $\Omega_{p_t}(S)$ have greater rank, transport a nonzero $(2r+1)$-minor in (1) using Cauchy–Binet. This refutes in degree $O(r+1)$. We can therefore assume every contraction of $S$ has rank at most $2r$.

For either tensor $M$, treat the entries of $p$, of an ambient-by-$2r$ matrix $B$, of a row $y$, and of two block linear functionals $u,v$ on $AB,AC$ as probe parameters. Suppress $M$ in $\Omega$. Set
$$
H=B^{\mathsf T}\Omega_p B,\quad \delta=\det H,\quad
q=y(\delta I-\Omega_p B\operatorname{adj}(H)B^{\mathsf T}),\quad
H_q=B^{\mathsf T}\Omega_q B.
$$
When $\delta\ne0$, $\Omega_p B H^{-1}B^{\mathsf T}$ is a projector onto $\operatorname{im}\Omega_p$, because the rank is $2r$, and $q$ ranges over its annihilator as $y$ varies. Let $\eta(t)=(-1)^r\operatorname{Pf}(H_q-tH)$. Define the matrix polynomial
$$
J(t)=\left.\delta^{r-1}\frac{\eta(z)-\eta(t)}{z-t}\right|_{z=H_q\operatorname{adj}(H)/\delta},
\qquad
D(t)=\widetilde P J(t)H\widetilde P^{\mathsf T},\quad
\widetilde P=\Omega_p B\operatorname{adj}(H).
$$
The displayed divided difference is a polynomial of degree at most $r-1$ in $z$ and in $t$; the prefactor clears all denominators. Define the probe polynomial
$$
\mathcal P_M=\delta\,
\operatorname{Res}(\eta,\eta')\,
\operatorname{Res}(\eta,u(D_{AB}))\,
\operatorname{Res}(\eta,v(D_{AC})).
$$
Resultants can be taken at the fixed degree upper bounds via Sylvester determinants. When the leading coefficient of $\eta$ is nonzero, these tests give that its $r$ roots are distinct and that both tested entries of $D(t)$ are nonzero at each root. This remains true if the second input polynomial drops degree at some probe values, by the resultant product formula with the extra leading-coefficient factor of $\eta$.

For the good source $p,q$, choose $B$ with $H$ invertible; this is possible by choosing representatives of a basis of the quotient by the radical of $\Omega_p$. The pencil $H_qH^{-1}$ has the $r$ eigenvalues $\rho_i$, each on the corresponding two-plane in the compressed coordinates. Also $\eta(t)=\operatorname{Pf}(H)\prod_i(t-\rho_i)$, since the alternating pencil is a direct sum of scaled two-dimensional alternating forms. At $\rho_i$, the divided difference evaluated on that pencil is $\eta'(\rho_i)$ on its $\rho_i$-eigenspace and zero on the others. The lift $\widetilde P/\delta$ is the inverse of $B^{\mathsf T}$ on the image of $\Omega_p$. Therefore $D(\rho_i)$ is $\delta^{r+1}\eta'(\rho_i)$ times the $i$-th individual contraction. Choose $u,v$ nonzero on each respective block. This gives constant probes with $\mathcal P_T\ne0$.

If $\mathcal P_S$ were identically zero, evaluate it at $p g',g'^{\mathsf T}B,y g'$, and at block tests transported by applying $g'$ on the left and $g'^{\mathsf T}$ on the right of their matrix inputs. Equation (1) and the inverse equations give $H,H_q,\delta,\eta,J$ equal to those at the fixed good source probes; they give $q_t=qg'$ and $D_t(t)=g D(t)g^{\mathsf T}$. Consequently the transported polynomial is equal to the nonzero source constant with a polynomial degree certificate. Each entry of $H,H_q,q,\delta,\operatorname{adj}H$ has probe degree $O(r+1)$. The fixed-degree coefficients of $\eta,J,D$ have probe degree $O((r+1)^2)$ by their formulas, and each resultant is the determinant of an $O(r+1)$-square matrix in such coefficients. Thus all substitutions and comparisons here have degree $O((r+1)^3)$, counting the additional degree at most two of each substituted probe. This also accounts for setting $S$'s maximum contraction rank strictly below $2r$, which would make $\delta$ identically zero. We can now choose a fixed target probe with $\mathcal P_S\ne0$, over $\bar k$.

## Certify that the fixed target pencil labels all source summands

Pull the fixed target $p_t,B_t,q_t$ back to $p=p_tg$, $B=g^{\mathsf T}B_t$, $q=q_tg$ on the source. Until the end of this section $H,H_q$ denote the fixed target compressed matrices, whose source versions agree by (1) with constant-degree certificates. The target relation $q_t\Omega_{p_t}(S)=0$ gives $q\Omega_p(T)=0$. Labels for the target are the $r$ distinct constant roots of $\eta$, denoted $\beta_1,\ldots,\beta_r$.

Let $F$ be the ambient-by-$3r$ constant matrix of the ordered triples $a_i,b_i,c_i$. Write $p_i$ for $p$ on those three coordinates and $\Pi$ for the $r$-by-$3r$ matrix with those rows in the separate blocks. Put $Q=B^{\mathsf T}F$ and $C=\binom{Q}{\Pi}$. Define the block diagonal $3r$-square alternating matrix $\Theta_p$ with $i$-th block the contraction with $p_i$ of the ordered coordinate three-vector. We have $\Omega_p(T)=F\Theta_p F^{\mathsf T}$ and $\Pi\Theta_p=0$. There is the exact polynomial identity
$$
\det C=\pm\operatorname{Pf}(Q\Theta_p Q^{\mathsf T}).
\tag{2}
$$
For example, expand the determinant along its last $r$ rows. Each term selects one of the three columns in each block, with its corresponding entry of $p_i$, leaving a $2r$-minor of $Q$. Expand the Pfaffian by wedging its $r$ rank-two contributions. In each contribution the selected $p_i$-coordinate gives the complementary pair of columns with the alternating sign. This gives the same coefficients up to a global sign. The exterior argument can be made over $\mathbb Q$ by dividing the top wedge power by $r!$; the resulting polynomial identity has integral coefficients and hence holds in all characteristics.

By (2), $C$ has determinant equal modulo the equations to the nonzero constant $c=\pm\operatorname{Pf}(H)$. Let its certified inverse be $c^{-1}\operatorname{adj}(C)=[R\ W]$, where $R$ has $2r$ columns. These entries, and all the ensuing matrix products of a constant number of such factors, have degree $O(r+1)$ certificates. We have $QR=I,\Pi R=0, RQ+W\Pi=I$, hence $RQ\Theta_p=\Theta_p$ and $\Theta_p=R H R^{\mathsf T}$. In particular
$$
F R=\Omega_p(T) B H^{-1},\qquad qF R=0 .
$$
Decomposing $qF=(qF R)Q+(qF W)\Pi$ now gives $q$ on the $i$-th triple equal to $\rho_i p_i$, with variable $\rho_i=(qF W)_i$ of degree $O(r+1)$.

Let $E_i$ be the constant coordinate projector of the $i$-th block of size three. The $K_i=Q E_iR$ are pairwise orthogonal projectors summing to one modulo our equations. Indeed $E_iR$ lies in the kernel of $\Pi$, on which $RQ$ acts as identity, and $E_iE_j=0$ for $i\ne j$. We have $H_q H^{-1}=\sum_i \rho_i K_i$, by the proportionality of the contraction blocks and $\Theta_p=RHR^{\mathsf T}$. The same expansion as in (2), with each block scaled by $\rho_i-t$, gives the certified polynomial identity
$$
\eta(t)=\operatorname{Pf}(H)\prod_i(t-\rho_i).
\tag{3}
$$
To justify degrees, $\eta$ is a degree-$r$ Pfaffian in matrix entries, and $\rho_i$ has degree $O(r+1)$. All substitutions in (3) have degree $O((r+1)^2)$. Substitution $t=\rho_i$ gives $\eta(\rho_i)=0$ within this degree.

Define selectors $e_{ji}=\prod_{h\ne j}(\rho_i-\beta_h)/(\beta_j-\beta_h)$. They have degree $O((r+1)^2)$; idempotence, orthogonality within each column, and sum one have bounded-degree certificates from the single equation $\eta(\rho_i)=0$ by polynomial division in one formal variable before substitution. Branch by taking one selector equal to one in each column. The relation $\rho_i=\beta_j$ follows in that branch because $(t-\beta_j)\prod_{h\ne j}(t-\beta_h)$ is a scalar multiple of $\eta(t)$. Equation (3) refutes a branch with any repeated label by comparison of constant coefficients after all the scalars are fixed. All remaining assignments are permutations $\sigma$.

Under such a branch $K_i$ equals the fixed $\beta_{\sigma(i)}$-projector polynomial in $H_qH^{-1}$, by summing the orthogonal $K_h$ and evaluating the Lagrange polynomial on each of them. The fixed matrix
$$
Z_j=\frac{D(\beta_j)}{\delta^{r+1}\eta'(\beta_j)}
$$
computed at the target probe now satisfies
$$
Z_{\sigma(i)}=g\Omega_p(a_i\otimes b_i\otimes c_i)g^{\mathsf T}.
\tag{4}
$$
Indeed the divided difference at $\beta_j$ divided by $\eta'(\beta_j)$ is the same Lagrange projector polynomial; $\widetilde P/\delta$ on the target is $gF R$ by covariance and the formula for $FR$. Then $R K_i H R^{\mathsf T}=E_i\Theta_p$ since $RQ$ acts as identity on $E_i R$. All comparisons involving multiplication powers up to $r$, the Pfaffian, or these selectors have degree $O((r+1)^2)$ in the branch.

## Resolve a branch by linear maps and scalar equations

Both of the selected blocks of $Z_j$ are nonzero by the probe test. Their respective expressions in (4) are the rank-one products
$$
p(c_i)(g_Aa_i)(g_Bb_i)^{\mathsf T},\qquad
-p(b_i)(g_Aa_i)(g_Cc_i)^{\mathsf T}.
$$
A nonzero $2$-minor refutes a block of rank greater than one. Otherwise factor the two fixed blocks as rank-one products. To obtain the line constraint on $g_Aa_i$, apply any constant row annihilating that block's column line and a constant column in the domain, chosen via $g_B'^{\mathsf T}$ or $g_C'^{\mathsf T}$, that cancels the second factor. One may cancel the scalar $p(c_i)$ or $p(b_i)$ using a certified polynomial inverse: a fixed nonzero entry of the corresponding block equals that scalar times two linear entries of the transformed factor vectors. The same procedure gives the line constraints on $g_Bb_i$ and $g_Cc_i$. If the two $A$-lines differ, the constraints imply $g_Aa_i=0$, contradicting its named inverse. The compatible branch therefore specifies fixed target vectors $a'_j,b'_j,c'_j$ in all the assigned lines.

For each mode the candidate matrices sending the given source lines into their assigned target lines form a constant linear space. If no invertible matrix exists in one such space, the determinant there is identically zero. Substitute the constant linear projection of that witness onto the space, compare determinants by telescoping using the branch linear line equations, and contradict the inverse identity. Otherwise choose an invertible $G_A,G_B,G_C$ in the three spaces. In each mode let the source basis consist of some factor vectors. Then $G_X^{-1}g_X$ fixes their lines and is diagonal in that basis. Each other factor vector forces equality of the diagonal entries on its support. Taking connected components of this equality graph gives one variable scalar per component. The component scalars $\lambda$ are linear functions of the original witness and each has a degree-one inverse function from $g_X'G_X$ by its diagonal inverse equation.

Consequently the tensor equation under this branch has the form
$$
S=\sum_{i=1}^r d_i\,\lambda_{A,i}\lambda_{B,i}\lambda_{C,i}
   \,\tau'_{\sigma(i)},\qquad
\tau'_j=a'_j\otimes b'_j\otimes c'_j ,
\tag{5}
$$
where all $d_i$ are fixed nonzero constants and each $\lambda_{X,i}$ is the scalar of the component containing that source factor. The source summands are linearly independent: contract a constant linear relation with a fixed good source $p$, which gives the independent rank-two bivectors on the distinct summand planes of the direct sum $L$. If the assigned target tensors in (5) are dependent, take a nonzero constant relation, transport it back by the inverses of the actions using the derived line equalities, and apply a fixed linear functional extracting an affected source coefficient. This makes a unit times a nonzero constant zero, refuting the branch. In detail, the forward action sends the $i$-th source summand to $d_i\lambda_{A,i}\lambda_{B,i}\lambda_{C,i}\tau'_{\sigma(i)}$; apply the inverse action and the product of the three scalar inverses to solve for the inverse of $\tau'_{\sigma(i)}$. This uses constant-many products. Similarly if $S$ lies outside the span of the $\tau'_j$, apply a fixed separating linear functional to (5). Otherwise coefficient extraction in (5) gives the equations $\lambda_{A,i}\lambda_{B,i}\lambda_{C,i}=k_i$. A zero $k_i$ directly contradicts the inverse identities. All these certificates have degree $O((r+1)^2)$, including the branch-dependent comparisons.

The residual equations with nonzero $k_i$ are inconsistent in the torus, because any torus solution rescales the component diagonals of the three fixed $G_X$ and yields an actual isomorphism by (5). We use the following general bound. For Laurent binomial equations $x^{v_i}=k_i$ in $m$ torus variables with $\|v_i\|_1\le L$, together with named inverses, any torus inconsistency over an algebraically closed field has a Nullstellensatz refutation of degree $O(mL+1)$. Indeed, if every integer relation among the $v_i$ gives the same multiplicative relation among the $k_i$, the latter define a character on the lattice generated by the $v_i$. Smith normal form and the existence of all roots in the field extend the character to the full lattice, a torus solution. Otherwise take an inconsistent relation and expand it as a finite list of signed copies of the $v_i$, summing to zero. The Steinitz rearrangement lemma in the norm $\|\cdot\|_1$ orders this list so the partial sums have norm at most $mL$. Encode each partial sum by its monomial in the variables and their named inverses. Each consecutive pair gives a derivation of $M_{\mathrm{next}}-k_i^{\pm1}M_{\mathrm{prev}}$: multiply the relevant original binomial by $M_{\mathrm{prev}}$, and cancel variable–inverse pairs. For a negative step the inverse binomial first follows by multiplication by the inverse monomial and the same cancellations. This takes degree at most $mL+2L+O(1)$. Sum the identities after weighting them by constants to telescope the monomials and obtain the nonzero constant $1-\prod_i k_i^{n_i}$. This is a degree bound independent of the length of the list. Here $L=3$ and $m\le3r$. Substituting the linear polynomials for the residual variables and their inverses, with the certified equations from the branch in place of the abstract equations, costs at most $O((r+1)^2)$. [Grinberg and Sevast'janov on the Steinitz bound](https://doi.org/10.1007/BF01086559)

## Assemble the unconditional refutation

Take every possible tuple of chosen selectors, including repeated target labels. Its branch degree is $O((r+1)^2)$. Multiply its certificate by the product of its $r$ selectors. Each branch axiom $e_{ji}-1$ is thereby absorbed into a certified idempotence $e_{ji}^2-e_{ji}$ times the other chosen factors. This consumes degree $O((r+1)^3)$. The sum of all these products is one by the selector column sums, with a certificate of the same degree. Summing gives the desired refutation. The coefficients descend as above. This is an informal polynomial degree certificate for the specified class, with no claim of bounded size or a formal kernel check.
