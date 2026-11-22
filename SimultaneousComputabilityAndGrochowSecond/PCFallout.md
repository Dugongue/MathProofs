# Artin–Schreier certificates for characteristic-two matrix congruence

Let $F=\mathbb F_q$, where $q$ is a power of two. For nonsingular $n$-square matrices $A,B$, use ordinary Polynomial Calculus (PC) on the original entries of $XAX^{\mathsf T}-B,XY-I,YX-I$ together with $z^q-z$ for every original variable. The asymmetry of a nonsingular bilinear form with matrix $M$ is $T=M^{-1}M^{\mathsf T}$. Write $N=T-I$. This note considers the case where the two asymmetries are unipotent and all their Jordan blocks have the same length $m$, with the same length on both sides.

**Theorem.** Suppose that $A,B$ are congruent over an algebraic closure but not over $F$. If the common length $m$ is even, the minimum PC degree lies between $\max(3,q)$ and $2q$. If $m$ is odd, it is exactly $\max(3,q)$. The upper bounds give polynomial expanded size for fixed $q$. Each such pair is congruent over $\mathbb F_{q^s}$ exactly when $s$ is even. The case $m=1$ has no such arithmetic negatives.

This addresses a finite-field part of the matrix congruence problem in Question 7.3. The earlier characteristic-two PC theorem concerns refutations of geometric noncongruence without field axioms. The examples here require field axioms. The form-theoretic starting points are Riehm's reduction by the asymmetry and the length-two and length-three phenomena described by Szechtman. The new arguments are the uniform lifting correction in this equal-length sector and the degree-bounded PC derivation of the Artin–Schreier obstruction. [Question 7.3](https://arxiv.org/html/2305.19320#S7.SS3) · [Earlier geometric bounds](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/IsomorphismCohomologyCrossovers/char2-matrix-congruence.md) · [Riehm, equivalence of bilinear forms](https://doi.org/10.1016/0021-8693(74)90004-0) · [Szechtman, Sections 4–7](https://arxiv.org/pdf/1311.0565)

## 1. Shortening equal-length modules

Use the notation $b$ for a form with asymmetry $T=1+N$. The elementary identities
$$
 b(v,u)=b(u,Tv),\qquad
 b(N^i u,v)=b(u,T^{-i}N^i v)
$$
follow because $T$ is an isometry. In particular the induced form on $NV/N^{m-1}V$ is nonsingular, with asymmetry induced by $T$ and all blocks shortened by two. Indeed the orthogonal complement of $NV$ is $\ker N=N^{m-1}V$, on either side. More generally the iterated quotient is $N^jV/N^{m-j}V$. These constructions commute with all isometries and all extensions.

For $m\ge4$, two such forms are isometric if their shortened forms are isometric. An isometry downstairs is $N$-linear. Both modules upstairs are free over $F[N]/(N^m)$, so lift the downstairs matrix between free bases. The lift is invertible since its reduction modulo $N$ is invertible. Pull one form back by this lift to put two forms $b,c$ on one module with the same asymmetry and the same restriction to $NV\times NV$. Their difference $D=b-c$ satisfies $D(u,N^2v)=0$, by the second identity above and invertibility of $T$. It also vanishes when its first argument is in $N^2V$.

Choose free generators $u_1,\dots,u_r$ of the common module. Let $D_i=(D(u_a,N^iu_b))_{ab}$ for $i=0,1$. Then $D_0+D_0^{\mathsf T}=D_1$ and $D_1$ is alternating. Put
$$
 H=(c(u_a,N^{m-1}u_b))_{ab},\qquad
 L=(c(u_a,N^{m-2}u_b))_{ab}.
$$
The form $H$ is nonsingular and symmetric, and $L+L^{\mathsf T}=(m-1)H$, with the integer $m-1$ read in $F$. These follow respectively from the nondegenerate pairing of $V/NV$ with $N^{m-1}V$, and from the identities for $b$ applied to $c$. For $L$, the relevant expansion is $T^{1-(m-2)}N^{m-2}=N^{m-2}+(m-1)N^{m-1}$.

Make the $N$-linear correction $P=I+N^{m-2}U+N^{m-1}W$, with constant $r$-square matrices $U,W$ on the generators. It is invertible since its reduction modulo $N$ is the identity. Terms quadratic in the correction vanish because $2(m-2)\ge m$. On indices $1$ and $0$ the differences produced in $c$ are, respectively,
$$
 U^{\mathsf T}H+HU,\qquad
 LU+U^{\mathsf T}L+(m-2)U^{\mathsf T}H+HW+W^{\mathsf T}H.
$$
The diagonal of the second difference is $\operatorname{diag}(HU)$, using $L+L^{\mathsf T}=(m-1)H$. Choose $HU$ to realize $D_1$ by its sum with its transpose, and simultaneously choose its diagonal arbitrarily to match $\operatorname{diag}(D_0)$. The still-unmatched part of $D_0$ is alternating, since the asymmetry and $D_1$ are now matched. Choose $HW$ with that sum with its transpose. All indices $\ge2$ were unchanged. These matrix coefficients determine the entire form, by shifting powers of $N$ between the arguments. This proves the lifting claim. Thus it suffices to classify and certify length two for even $m$, and length three for odd $m\ge3$.

## 2. The arithmetic invariants at lengths two and three

At length two use the basis $(u_a,Nu_a)_a$, arranged with all generators first. The bilinear form has Gram matrix
$$
 \begin{pmatrix}G&H\\H&0\end{pmatrix},
 \qquad H=G+G^{\mathsf T}.
$$
Here $H$ is nonsingular and alternating. The quadratic form $Q(\bar v)=b(v,v)$ on $V/NV$ is well-defined and nonsingular, since shifting $v$ by $Nw$ changes its value by zero and its polar form is $H$. Any isometry of the bilinear form gives an isometry of $Q$. Conversely an isometry $P_0$ of $Q$ matches the polar forms. Lift it as an $N$-linear block map with diagonal blocks $P_0$ and an arbitrary lower-left block $R$. The remaining difference in the upper-left block is alternating, since the diagonal quadratic forms agree. The correction to it is $P_0^{\mathsf T}H_{\rm target}R+R^{\mathsf T}H_{\rm target}P_0$, which realizes every alternating matrix. Thus length-two forms are classified by $Q$. Over a finite field of characteristic two, a nonsingular quadratic form of fixed even dimension is classified by the Artin–Schreier class of its Arf invariant. [Elman–Karpenko–Merkurjev, quadratic forms](https://www.math.ucla.edu/~rse/book/Kniga.pdf)

At length three put $H(\bar u,\bar v)=b(u,N^2v)$ on $V/NV$. This is nonsingular symmetric. If $H$ is alternating, it gives the complete classification at this length. If $H$ is nonalternating, use its characteristic vector $c_0$, defined by
$$
 H(v,c_0)^2=H(v,v)\qquad\text{for every }v .
$$
This vector exists uniquely because $F$ is perfect and $H$ is nonsingular. The additional invariant is
$$
 a(b)=b(\widetilde c_0,\widetilde c_0)
       \pmod{\{z^2+z:z\in F\}},
$$
where $\widetilde c_0$ is any lift to $V$. In fact for any $w$ the change under $\widetilde c_0\mapsto\widetilde c_0+Nw$ is
$$
 b(\widetilde c_0,N^2w)+b(Nw,Nw)
 =H(c_0,\bar w)+H(\bar w,\bar w)
 =H(c_0,\bar w)+H(c_0,\bar w)^2.
$$
Thus the class is independent of the lift and invariant under an isometry.

To prove sufficiency, first align the same $H$ by an invertible $N$-linear lift of a residue isometry. Such a residue isometry exists when the two alternating flags agree, since over a finite field a nonsingular nonalternating symmetric bilinear form of any fixed dimension has a diagonal basis with all diagonal entries $1$. The aligned forms agree on $NV\times NV$. Use the correction calculation above with $m=3$. The only extra term is $U^{\mathsf T}HU$ in the difference at index zero. The diagonal to be prescribed is now
$\operatorname{diag}(HU+U^{\mathsf T}HU)$. If $H$ is alternating, its second summand has zero diagonal and the same correction succeeds.

For nonalternating $H$, take $H=I_r$. The required first-index equation is $U+U^{\mathsf T}=D_1$. Write $s_i=\sum_j U_{ji}$ for the column sums. The diagonal constraints at index zero are $U_{ii}+s_i^2=(D_0)_{ii}$. They can be solved provided there is $s\in F$ with
$$
 s^2+s=\sum_i (D_0)_{ii}+\sum_{i<j}(D_1)_{ij}.
$$
Indeed, take any $s_i$ summing to $s$. The required off-diagonal column sums are $(D_0)_{ii}+s_i^2+s_i$. Their total equals the sum of the prescribed pair sums $(D_1)_{ij}$. Every list of column sums with this total can be realized. Start with any assignment satisfying the pair sums and correct the column sums by changing both directed entries over each edge of a spanning tree by the same amount, working from the leaves. This also covers $r=1$, with no edges. Choose diagonal entries to make the full column sums $s_i$. Since $c_0=(1,\ldots,1)$ in this basis, the right side of the displayed equation is $D_0(c_0,c_0)$, the difference of the two representatives of $a(b)$. Thus equality of the invariant supplies $s$. The remaining alternating difference at index zero is removed using $HW+W^{\mathsf T}H$ as before. This proves sufficiency.

At length one the form is symmetric and the alternating flag is complete. At either other base length, the sole possible arithmetic distinction on a geometrically congruent pair is therefore a class represented by $\delta$ with $\operatorname{Tr}_{F/\mathbb F_2}(\delta)=1$. Under extension of degree $s$ its absolute trace becomes $s\bmod2$. This proves the extension profile in the theorem.

## 3. Preparing the induced transporter in the original variables

For column notation put $P=X^{\mathsf T}$ and $R=Y^{\mathsf T}$, so $P^{\mathsf T}AP=B$, $PR=RP=I$. The linear equations $N_AP=PN_B$ are derived in degree at most three. The two Gram equations for $A,A^{\mathsf T}$, available by transposing, give $P^{\mathsf T}A(N_AP-PN_B)=0$ in degree two. Multiply on the left by $A^{-1}R^{\mathsf T}$ and use $(PR)^{\mathsf T}=I$, correcting each term with an inverse axiom multiplied by a linear form. The reverse intertwiner is derived the same way using $R^{\mathsf T}BR=A$; that reverse equality follows in degree three by first deriving $AP-R^{\mathsf T}B=0$ and then multiplying by $R$ and using $PR=I$.

Project $P,R$ by constant linear maps onto their true $N$-intertwiner spaces. The projection errors are linear combinations of the derived linear equations. Substituting the projected maps in the Gram and inverse equations uses linear multiples of these errors, so preserves the degree-three preparation bound. The induced maps on $N^jV/N^{m-j}V$ are matrices of linear forms in the original variables. Their Gram and inverse equations are consequently available in degree three by constant linear combinations and restrictions. One can perform these restrictions directly for the final quotient without increasing degree with $m$.

## 4. A degree-four Arf identity in PC

At length two take the induced maps on $V/NV$ and use symplectic bases for the polar forms, so their common matrix is $J$, with $J^2=I$. Write $P_0,R_0$ for the forward and reverse maps. The induced quadratic-form transport and its polarization are available through degree three. Its reverse and both inverse equations are available as well. In particular so is $P_0JP_0^{\mathsf T}=J$: from $P_0^{\mathsf T}JP_0=J$ and $P_0R_0=I$ first derive $P_0^{\mathsf T}J=JR_0$, then multiply on the left by $P_0J$.

Here is a polynomial identity in the Clifford algebra of the target quadratic form, used only to organize scalar PC derivations. For a fixed symplectic basis $(e_i,f_i)_{i=1}^r$, put $\omega=\sum_i e_i f_i$. Use the relations $v^2=Q(v)$ and $[v,w]=b_Q(v,w)$ for vectors. Then $\omega^2+\omega=\sum_i Q(e_i)Q(f_i)$. Put $u_i=P_0 e_i,\ v_i=P_0 f_i$ in these coordinates and $\omega'=\sum_i u_i v_i$. Write $Z$ for the scalar coefficient of $\omega'$ in the ordered Clifford basis, a quadratic polynomial in the entries of $P_0$. The coefficient of a distinct-index product $g_a g_b$, where $g$ denotes the ordered symplectic basis, is $(P_0JP_0^{\mathsf T})_{ab}$. It follows that every coefficient of $\omega'-\omega-Z$ is a derived line of degree at most two, with the initial preparation through degree three.

Squaring this identity and using $\omega^2+\omega=\operatorname{Arf}(Q_{\rm target})$ derives the coefficients of
$$
 (\omega')^2+\omega'=\operatorname{Arf}(Q_{\rm target})+Z^2+Z
$$
through degree four. This uses the telescoping difference of the two products in a possibly noncommutative algebra. On the other hand
$$
 (u_i v_i)^2+u_i v_i
   = Q(u_i)Q(v_i)+(1+b_Q(u_i,v_i))u_i v_i.
$$
Each cross commutator $[u_i v_i,u_j v_j]$ for $i\ne j$ expands as a sum whose terms have a factor given by an off-pair polar value and at most two vector factors. The off-pair polar values are zero by the derived transport equations. Use the same equations for the on-pair value $b_Q(u_i,v_i)=1$ and for $Q(u_i),Q(v_i)$ to derive $(\omega')^2+\omega'=\operatorname{Arf}(Q_{\rm source})$ in degree four. Thus $Z^2+Z=\delta$ at that degree. All equalities here mean coefficientwise scalar derivations. Only ordered products of at most four basis vectors occur, and all coefficient multiplications expand into scalar monomial multiples in the original variables. No Clifford coordinates are added as PC variables. [Clifford description of the Arf invariant](https://www-fourier.univ-grenoble-alpes.fr/~peters/Books/QuadraticForms/QuadForms.pdf)

## 5. A linear Artin–Schreier witness at length three

At length three an arithmetic difference occurs only when both $H$'s are nonalternating. The induced $N$-linear maps preserve $H$ on $V/NV$, with both inverse equations, in degree at most three. Write $U,V$ for these residue maps and $c_S,c_T$ for the characteristic vectors. The diagonal of the reverse $H$-transport yields the squares of the entries of $V^{\mathsf T}H_Sc_S-H_Tc_T$. Derive the entries themselves through degree $q$ after preparation: for a linear form $l$, multiply $l^2$ by $l^{q-2}$, and use $l^q=l$ from the field axioms. The forward $H$-transport and the inverse equations give $V^{\mathsf T}H_S=H_T U$ in degree three by multiplying the forward equation by $V^{\mathsf T}$ and correcting by $UV=I$. Thus $Uc_S=c_T$ is derived through degree $\max(3,q)$.

Choose fixed lifts of the two characteristic vectors. For the prepared forward map $h$ on the shortened module, this last equality says
$$
 h\widetilde c_S=\widetilde c_T+N_Tw ,
$$
where $w$ is a vector of affine linear forms, obtained by a fixed right inverse of $N_T$ on its image. Indeed the difference of the two sides is a linear combination of the residue equations. Substitute this equality in
$b_T(h\widetilde c_S,h\widetilde c_S)=b_S(\widetilde c_S,\widetilde c_S)$.
The shift identity of Section 2 derives $Z^2+Z=\delta$ with $Z=H_T(c_T,\bar w)$ affine linear in the original variables. The substitution uses only linear multiples of the already derived linear equations, and stays in degree $\max(3,q)$.

## 6. Trace, sharpness, and scope

For either derived equation $Z^2+Z=\delta$, with $t=\deg Z\le2$, Frobenius gives $Z^q-Z=0$ from the original field axioms in degree at most $qt$. Expand $Z$ in monomials and telescope the products in each monomial's $q$-power difference. Also derive the sum
$$
 \sum_{i=0}^{\log_2(q)-1}(Z^2+Z+\delta)^{2^i}
 =Z^q+Z+\operatorname{Tr}_{F/\mathbb F_2}(\delta)
$$
by taking polynomial multiples of the derived Artin–Schreier equation. All these lines have degree at most $qt$. Since the trace is one, subtracting the Frobenius consequence gives a refutation. This proves the upper bounds. At fixed $q$, the space of polynomials in the original $O(n^2)$ variables of these bounded degrees has polynomial dimension. Compress the derivation by retaining independent lines and using scalar combinations to recover needed earlier lines. This gives polynomial expanded size. Any refutation must contain a field axiom since the raw equations have a geometric solution. Each field axiom has degree $q$.

For $q=2$, degree two is also impossible. Here $m\ge2$ and hence $A$ is nonsymmetric. No nonzero scalar combination of the Gram entries has a quadratic part consisting only of pure squares. For each row index the diagonal Gram entry has a nonzero cross term within that row because $A+A^{\mathsf T}\ne0$, and no other entry apart from that same diagonal contributes to this within-row cross term. For a pair of different rows, the two Gram entries on those rows have independent coefficient matrices $A,A^{\mathsf T}$ over $\mathbb F_2$. The inverse axioms have mixed $X,Y$ quadratic parts, and any cancellation of those parts also cancels their constants, by evaluation at $X=Y=I$. The field axioms have distinct pure-square quadratic parts. Combining these observations, the span of the original axioms has no nonzero line of degree below two. No multiplication step can stay in degree two until such a line is available, so degree two cannot refute. This proves the asserted lower bounds, including exactness in the odd-length case.

An explicit length-three example over every such $F$ is the pair of matrices
$$
 \begin{pmatrix}0&0&1\\1&1&0\\1&0&0\end{pmatrix},
 \qquad
 \begin{pmatrix}\delta&0&1\\1&1&0\\1&0&0\end{pmatrix},
 \qquad \operatorname{Tr}_{F/\mathbb F_2}(\delta)=1.
$$
Their shared asymmetry is $I+N$ for the lower Jordan shift, $H=(1)$, and their two lift values differ by $\delta$. At length two take $G$ representing the hyperbolic and anisotropic nonsingular binary quadratic forms and use $\begin{pmatrix}G&I\\I&0\end{pmatrix}$ for each. This version uses a different basis on the bottom half, with the same length-two asymmetry type. Over the same finite-extension probes these pairs and their higher-dimensional analogues carry the same even-degree existence profile. Their negative certificates have the dimension-independent bound above, contrasting with the factorial-scale hard examples for an even-degree profile in fixed odd characteristic. [Odd-characteristic arithmetic proof complexity](https://github.com/Dugongue/MathProofs)

These are written proofs. Exact finite controls checked 600 shortening-correction and characteristic-vector identities over $\mathbb F_2,\mathbb F_4$, across lengths 3 through 8 with supported multiplicities at most 3. The equal-length hypothesis is essential to the shortening argument. Mixed neighbouring Jordan lengths permit transporters to mix their primitive layers and remain outside this theorem. The bound is unconditional.
