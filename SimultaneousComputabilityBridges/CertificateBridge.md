# Exact certificate transport for polynomial products

## 1. A product substitution theorem for ordinary polynomial calculus

Let $F$ be a field, $S_i\subset F[x_i]$ be polynomial systems in pairwise disjoint variable blocks, and $T\subset F[y]$ be another system. Write $d_F(S)$ for the minimum degree of a polynomial calculus (PC) refutation, with value $+\infty$ when no refutation exists. A sparse refutation has size given by the total number of nonzero monomials on its lines. Refutation conclusions may be any nonzero constant, equivalent by scaling to a conclusion of $1$; in the applications below no initial axiom is a nonzero constant. PC has scalar linear combination and multiplication by a variable as its inference rules.

**Theorem 1.** Suppose a polynomial substitution $\phi$ sends each $y$ to zero or a scalar times a product using at most one variable from each block. For every axiom $g\in T$, suppose $\phi(g)$ has an identity
$$
 \phi(g)=\sum_{i,\alpha} a_{i,\alpha}(x_i)s_{i,\alpha}(x_i)
                 \prod_{j\ne i} b_{j,\alpha}(x_j),
 \qquad s_{i,\alpha}\in S_i,
$$
where each block factor, including $a_{i,\alpha}s_{i,\alpha}$ in block $i$, has degree at most $\deg g$. Then
$$
 d_F(T)\ \ge\ \min_i d_F(S_i).
$$
Suppose additionally that each identity uses at most one term per $i$ and every $a_{i,\alpha}$ is a scalar. If $S_j$ has an $F$-solution for every $j\ne i$, the minimum sparse refutation size of $T$ is at least that of $S_i$. The same witness-specialized conclusion holds for the degree.

**Proof.** For a nonnegative integer $D$, let $P_i(D)$ be the degree-at-most-$D$ polynomials in block $i$, and $C_i(D)\subset P_i(D)$ the space of degree-$D$ PC consequences of $S_i$. Write $W_D=\sum_i P_1(D)\otimes\cdots\otimes C_i(D)\otimes\cdots\otimes P_k(D)$. The axiom identities place $\phi(g)$ in $W_D$ whenever $\deg g\le D$, since each monomial multiple of a local axiom can be derived within degree $D$. Cancellation within $a_{i,\alpha}s_{i,\alpha}$ does not affect that argument because the degree of a nonzero product in a polynomial ring is the sum of the degrees.

Choose bases of $P_i(D)$ adapted to the degree filtration and to $C_i(D)$, by extending a basis of $C_i(D)\cap P_i(t)$ at every filtration step and then adding a complement. If a global proof multiplies a nonzero parent by a variable in degree at most $D$, the parent has degree at most $D-1$. Its image belongs to $W_D\cap\bigotimes_i P_i(D-1)$. In the adapted tensor basis, this intersection is spanned by tensors with all factors of degree at most $D-1$ and at least one factor in $C_i(D)$. Multiplying by the image of the variable increases each factor's degree by at most one and preserves membership in $C_i(D)$ for the indicated factor. A zero parent or zero variable image is immediate. Scalar linear combinations preserve $W_D$. These steps account for arbitrary degree falls in the original proof. If $D=0$ only linear combinations are needed. When $1\notin C_i(D)$ for every $i$, the bases can include the constant $1$ as a complementary vector in every block, so $1\notin W_D$. This proves the degree claim.

For the sparse claim, specialize to the indicated solutions. Each fused variable now maps to zero, a constant, or a scalar times one local variable. Each fused axiom becomes zero or a scalar times one local axiom. Transport each nonzero line up to nonzero scalar, storing the factor in the coefficients of subsequent linear combinations. A multiplication by an image variable needs at most its original one line, and a multiplication by a scalar reuses the parent. Canceling images and zero lines can be omitted. Neither degree nor monomial count increases. This proves the witness-specialized bounds. $\square$

The first part applies even at a probe where several factors fail. The second requires witnesses in the probe's own field. It applies separately at all finite field probes when field equations are included in the axiom identities.

## 2. Exact ordinary PC degree under matroid 2-sum

For a matroid $M$ of rank $r$, let $S_F(M)$ be the full bracket presentation. For each basis $B$ use one bracket $p_B$ and its formal reciprocal $u_B$, with axiom $p_Bu_B-1$. Brackets on ordered tuples are extended by alternation and take value zero on nonbases or repeats. The remaining axioms are
$$
 G(I,J)=\sum_{j=1}^{r+1}(-1)^{j-1}p_{(I,J_j)}p_{J\setminus J_j},
 \qquad |I|=r-1,\quad |J|=r+1.
$$
For a finite probe $F=\mathbb F_q$ we may include $z^q-z$ for every variable. This is the previously studied full Plücker system with exact minor and duality substitution transports. A field representation gives a solution by its maximal minors and their reciprocals, and the Plücker characterization gives the converse. [Baker and Bowler](https://arxiv.org/abs/1601.01204)

**Theorem 2.** Let $M_1,M_2$ share exactly one element $e$ which is neither a loop nor a coloop in either. For their ordinary 2-sum $M=M_1\oplus_2 M_2$, over every field,
$$
 d_F(S_F(M))=\min\bigl(d_F(S_F(M_1)),d_F(S_F(M_2))\bigr).
$$
Over a finite probe, the same equality holds when all three presentations include the field equations. If factor $j$ has an $F$-representation, the minimum sparse size for $M$ equals the minimum sparse size for the other factor. In a tree of 2-sums the degree is the minimum over its pieces, and the size at a probe with one rejecting piece and all other pieces $F$-representable equals that of the rejecting piece.

**Proof.** Let $E_i=E(M_i)-\{e\}$, and $r_i=\operatorname{rk}(M_i)$. Order $E_1$ before $E_2$, with $e$ last in the first local order and first in the second. For a block-ordered tuple $K=(K_1,K_2)$ define
$$
 \phi(p_K)=
 \begin{cases}
 p^1_{(K_1,e)}p^2_{K_2},& (|K_1|,|K_2|)=(r_1-1,r_2),\\
 p^1_{K_1}p^2_{(e,K_2)},& (|K_1|,|K_2|)=(r_1,r_2-1),\\
 0,&\text{otherwise}.
 \end{cases}
$$
Extend by alternation. A nonzero product appears exactly for the bases in the 2-sum basis rule. Map each formal reciprocal to the product of the corresponding local reciprocals. For a reciprocal identity use $z_1z_2-1=(z_1-1)z_2+(z_2-1)$ with $z_i=p_i u_i$. For finite-field axioms use $(x_1x_2)^q-x_1x_2=(x_1^q-x_1)x_2^q+x_1(x_2^q-x_2)$. Each block degree is at most the global axiom degree, and the used local axiom is unmultiplied in its own block.

For a global Plücker polynomial take $I=(I_1,I_2)$, $J=(J_1,J_2)$ block ordered. Permuting internal orders only contributes common signs. Set $a=|I_1|-(r_1-1)$ and $b=|J_1|-r_1$. Terms indexed in $E_1$ can survive only for $a\in\{-1,0\}$, $b\in\{0,1\}$, and terms in $E_2$ only for $a\in\{0,1\}$, $b\in\{-1,0\}$. If neither condition holds, the image is zero. In the first-only cases, the result is a local $G_1$ times a fixed degree-two bracket product from block 2, up to one overall sign. The local tuple $I_1$ appends $e$ iff $a=-1$, and $J_1$ appends $e$ iff $b=0$. If $e$ is appended to $J_1$ in a first-only case, it is already in $I_1$ and the extra local term is zero. In the second-only cases the local polynomial is the corresponding $G_2$ with $e$ prepended to $I_2$ iff $a=1$ and to $J_2$ iff $b=0$. The two orders of the inserted entry have the same common sign across this sum, and the extra term is again zero whenever $e$ has been prepended to $J_2$.

Both types can survive only when $a=b=0$. Put $U_1=p^1_{(I_1,e)}p^1_{J_1}$ and $U_2=p^2_{(e,I_2)}p^2_{J_2}$. Then
$$
 \phi(G(I,J))=(-1)^{r_2-1}G_1(I_1,(J_1,e))U_2
       +(-1)^{r_1-1}U_1G_2(I_2,(e,J_2)).
$$
Indeed the $E_1$ terms acquire the sign of moving one entry across $I_2$, and the $E_2$ terms acquire the sign from the $J_1$ prefix and the initial $e$ in the local tuple. The $e$-term in the first displayed local polynomial is $(-1)^{r_1}U_1$, and that in the second is $(-1)^{r_2-1}U_2$. With their displayed external signs they cancel. Thus every axiom meets both parts of Theorem 1.

To recover $M_1$ as a minor of $M$, choose a circuit $C$ of $M_2$ containing $e$ and an element $f\ne e$. Extend $C-\{e\}$ to a basis by elements $L$. Set $K=(C-\{e,f\})\cup L$. Both $K+e$ and $K+f$ are bases of $M_2$. The 2-sum basis rule gives independence of $K$, and the same rule shows that contracting $K$ and deleting the remaining elements of $E_2-\{f\}$ gives $M_1$ with $e$ renamed $f$. Interchanging roles gives $M_2$ as a minor. For clarity, the existing minor transport from a minor proof to the original presentation substitutes a retained bracket by its signed original bracket padded by the chosen contracted set, plus elements completing rank if the restriction has lower rank. Every full local Plücker identity then maps to a full original identity by padding both tuples with the same elements, whose additional terms vanish by repetition. Reciprocals and field equations map to original axioms up to sign. This preserves line sparsity and degree and gives the reverse bounds. Induction on the tree proves the iterated claim. $\square$

For a field-equation example, $U_{2,4}\oplus_2 F_7$, where $F_7$ is the Fano matroid, inherits its exact $\mathbb F_2$ degree $3$ and sparse size from $U_{2,4}$. At every odd finite probe it inherits its degree and size from $F_7$, since four distinct points on a projective line exist even over $\mathbb F_3$. Both factors are representable over $\mathbb F_4$. Thus the same matroid exposes different local obstructions across probes.

The representability counterpart and the tensor-product formula for the foundation of a 2-sum are prior work. The extra conclusion here concerns the quantitative cutoff in ordinary PC and exact sparse size at witness-bearing probes. The foundation theorem is the closest structural predecessor located in this literature check. [Baker, Lorscheid, Walsh, and Zhang](https://arxiv.org/abs/2404.10656)

## 3. Matrix congruence products and an arithmetic spectator law

Use the congruence presentation with entries of $X,Y$ as variables and axioms from $XAX^{\mathsf T}=B$, $XY=YX=I$, plus field equations when specified. The arguments also apply to the equivalent presentation with forward and backward Gram equations if those equations occur in every factor.

**Theorem 3.** For forms $A_i,B_i$ of equal dimension within each factor, the exact PC degree for $\otimes_i A_i$ versus $\otimes_i B_i$ is at least the minimum of the factor degrees. If one factor $A,B$ is tensored on both sides with an arbitrary common symmetric nonsingular form $C$, the resulting proof degree and sparse size are each at least their values for $A,B$. Both statements hold over any field, and with field equations over finite fields.

**Proof.** Substitute the corresponding products of entries of $X_i$, respectively $Y_i$, into entries of the tensor $X$ and $Y$. The mixed-product law and telescoping of a difference of products give each tensor axiom as a sum of products with exactly one unmultiplied local axiom in its own block. Every nonconstant global Gram or inverse axiom has degree two, so the individual factor degrees have the required bound. If a global Gram axiom is a nonzero constant, its constant coefficient is a product of nonzero entries of the $B_i$. Its positive-degree part vanishes even after the tensor substitution. The corresponding product of local pure quadratic parts is zero, so one vanishes and the corresponding local Gram axiom is a nonzero constant as well. The lower bound is immediate in this case. Zero axioms can be discarded. For field equations use the same telescoping identity with factor entries raised to $q$. Apply Theorem 1. In the spectator case fix the witness $X_C=Y_C=I$. Every tensor Gram entry then becomes the local entry times the corresponding coefficient of $C$, and the other axioms specialize to local axioms or zero. $\square$

**Arithmetic application.** Let $A,B$ be nonsingular over a finite field $F$, geometrically congruent and incongruent over $F$. In odd characteristic assume they are symmetric. In characteristic two assume their asymmetries are unipotent and have the same single pure Jordan length. For a nonsingular symmetric spectator of dimension $e$, the tensor pair has exactly the original negative extension-degree probes when $e$ is odd and is congruent at every extension-degree probe when $e$ is even.

In odd characteristic, the determinant ratio of the tensor pair is $(\det A/\det B)^e$. Equal-dimensional nonsingular symmetric forms over a finite field are classified by determinant square class, so at each extension this gives the assertion. More generally, for two symmetric pairs of dimensions $n,e$, the resulting determinant mismatch bit is $e\epsilon_1+n\epsilon_2$ modulo $2$, where each bit denotes its pair's determinant square class quotient.

In characteristic two the asymmetry tensor is $T_A\otimes I_e$, and the canonical shortening commutes with tensoring because the powers, kernels and images of the nilpotent part are tensored with the full spectator space. Shortening leads to length two or three. At length two the residual quadratic form is $v\mapsto b(v,v)$ on the quotient with nonsingular polar form. If $C$ is nonalternating, over a finite field it is congruent to $I_e$, and the shortened quadratic form becomes the orthogonal sum of $e$ copies. Its Arf class scales by $e$. If $C$ is alternating, every spectator hyperbolic plane produces the quadratic form $Q(u,v)=H(u,v)$ for the nonsingular polar form $H$ of the original quadratic form. This is hyperbolic because it vanishes on the two complementary halves. At length three the residual symmetric form $H$ tensors with $C$. If $C$ is alternating, so is $H\otimes C$, and there is no characteristic-vector parameter. If $C\cong I_e$, the characteristic vector of the $e$ copies is the repeated characteristic vector, so its lift's self-pairing has an Artin–Schreier class scaled by $e$. The pure-length classification then gives the stated extension profile. Length one has no geometrically congruent arithmetic pair under these hypotheses. [Riehm](https://doi.org/10.1016/0021-8693(74)90004-0), [Szechtman](https://arxiv.org/abs/1311.0565)

For fixed odd $e$, the existing odd-characteristic symmetric hard family therefore retains its factorial scale $\exp(\Theta(n\log n))$ in sparse size and linear degree. The previous upper bounds for symmetric forms apply to the resulting side dimension $en$. For odd pure Jordan length in characteristic two, the field-axiom degree remains $\max(3,q)$ over a rejecting probe of order $q$, and the previous polynomial sparse upper bound still applies. The lower bound comes from the single spectator substitution in Theorem 3. This compares the two arithmetic obstructions under the same map of proof lines. The inherited estimates are from *Artin–Schreier certificates for characteristic-two matrix congruence* and the earlier odd-characteristic finite-field congruence theorem.

## 4. Sharp degree amplification under labelled tensor products

**Theorem 4.** For every odd prime power $Q=p^h\ge 9$, there are diagonal matrix pairs of side $Q$ whose raw conjugacy encodings have exact PC degree $2$ over every field, but whose two-labelled tensor comparison of side $Q^2$ has exact degree $2Q$ in characteristic $p$ and exact degree $2$ over every other field. Here raw means the equations $A_iX=XB_i,\ XY=YX=I$, with no field equations.

**Proof.** Take $r=(Q-1)/2$, $s=(Q+1)/2$, $A=\operatorname{diag}(I_r,0_s)$, and $B=\operatorname{diag}(I_s,0_r)$. Define two labelled comparisons by
$$
 (A\otimes I_Q,\ I_Q\otimes A)
 \quad\text{and}\quad
 (B\otimes I_Q,\ I_Q\otimes B).
$$
The four joint eigenvalue words $11,10,01,00$ have respective multiplicities $r^2,rs,rs,s^2$ on one side and $s^2,rs,rs,r^2$ on the other. For any diagonal tuple with entries in $\{0,1\}$, all off-word entries of $X$ are scalar multiples of linear axioms, as each differing word differs in at least one labelled entry. Each square corner of the inverse equations therefore gives a rectangular two-sided inverse system in degree $2$. Every discarded term has a zero off-word entry of $X$, yielding its monomial multiple in degree $2$.

Conversely, setting all off-word entries of $X,Y$ to zero sends every tuple axiom to zero or a rectangular inverse axiom. The resulting independent rectangular systems have exact degree equal to the minimum of their degrees by Theorem 1 and by using one factor's proof. Matching blocks have an identity solution. For unequal positive dimensions $a<b$, the previously established raw rectangular inverse degree is $\min(a+2,2p^{v_p(b-a)})$ in characteristic $p$ and $2$ in characteristic zero. For the original pair the gap is $1$; for the two unmatched tensor words it is $s^2-r^2=Q$ and $r^2+2\ge 2Q$. This gives the claimed degrees.

The corresponding sparse-size estimate in characteristic $p$ is $N^{\Theta(Q)}$ for $N=Q^2$ as $Q\to\infty$. For the lower bound specialize the two matched label blocks to identity. On the remaining blocks, the two labels coincide and the specialized instance is the complementary projection pair with smaller multiplicity $r^2$ and gap $Q$. The prior growing-gap bound applies since $Q=o(r^2)$. For the upper bound extract the single discrepant rectangular board as in the proof and use the prior sparse minors refutation for gap $Q$. The estimate is in the raw presentation, with the established scaling up to constants in the exponent. [Riis, rectangular design methods](https://arxiv.org/html/2611.07280v1#S14)

## Status and scope

The statements above have written proofs. An exact symbolic expansion checked 26,152 block-ordered Plücker axiom images, including 3,136 mixed cases, for all pairs of local ranks 1 through 4 with four nonshared elements in each block. The arguments use the project’s previously proved full-bracket minor transport, raw rectangular inverse degree and sparse bounds, and the prior pure-length arithmetic classification. The new quantitative statements are the ordinary PC product substitution bound, exact matroid 2-sum degree and witness-specialized size, the tensor congruence comparison with its arithmetic profile, and the explicit labelled tensor amplification. The claims are presentation-specific. A general sparse-size formula when both components of a matroid 2-sum reject, and a tensor profile for mixed Jordan lengths across characteristic-two congruence presentations, remain separate questions.
