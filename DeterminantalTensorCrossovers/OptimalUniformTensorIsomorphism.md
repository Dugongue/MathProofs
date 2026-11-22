# Tensor isomorphism inside one optimal uniform determinantal family

## Theorem 1. A fixed determinant and all affine matrix substitutions

Let $k$ be any field. Fix a three-tensor format, written as bilinear maps $T:B\times E\to F$ with positive dimensions $m,e,f$, and put $D=e+f$. There is a deterministic constant-free affine projection $T\mapsto\mathcal M_T$ of four-tensors with mode sizes
$$
D+1,\quad D+1,\quad 1+2D+m,\quad m+3 .
$$
For any field extension of $k$, two such four-tensors are ordinarily isomorphic exactly when the original three-tensors are ordinarily isomorphic. The four-tensors are the coefficient arrays of bihomogeneous matrix pencils. Every one has the same scalar determinant. Dehomogenizing gives uniform determinantal representations of exact minimum size $D+1$, all with the same scalar cokernel. After **every** standard matrix substitution in the coefficients, in every size, all the resulting matrices have isomorphic cokernels over the polynomial ring in the scalar arguments. Their determinants and determinantal ideals agree as well.

Thus testing equivalence of coefficient tensors of optimal uniform representations remains Tensor Isomorphism complete on one explicit fixed determinant family for each format, even when given all these scalar and matrix-valued module invariants.

### The fixed family and pencils

Put $V=E\oplus F$, and write $\widetilde T(b)\in\operatorname{End}(V)$ for the operator that is $T(b,-):E\to F$ on $E$ and zero on $F$. Products of any two such operators are zero. In fact their only possibly nonzero block is the lower-left block. Set
$$
N_T(c,b)=cI_D+\widetilde T(b).
$$
Use two independent variable groups
$$
(h,x,z,y)\in k\oplus k^D\oplus k^D\oplus B^*,\qquad
(c,a_0,a_1,b)\in k\oplus k\oplus k\oplus B.
$$
Here $x,z$ are columns and $\langle b,y\rangle=y(b)$. Define
$$
\mathcal M_T((h,x,z,y),(c,a_0,a_1,b))=
\begin{pmatrix}
hN_T(c,b)&N_T(c,b)x\\
-a_1z^{\mathsf T}&a_0h+\langle b,y\rangle
\end{pmatrix}.
\tag{1}
$$
The variable groups are independent homogeneous degree-one groups, and each matrix entry is bilinear across them. For coefficient arrays, ordinary isomorphism is exactly equality of the two matrices after independent invertible linear coordinate maps on those groups and constant invertible row and column maps. The possible use of transposes or inverses in the coefficient convention does not change the orbit relation.

The determinant is
$$
\det \mathcal M_T=c^D h^{D-1}
\bigl(a_0h^2+h\langle b,y\rangle+a_1 z^{\mathsf T}x\bigr).
\tag{2}
$$
Indeed $\det N_T=c^D$, and after inverting $c,h$ the Schur complement is $a_0h+\langle b,y\rangle+(a_1/h)z^{\mathsf T}x$. Localization is injective on the polynomial ring, giving (2) formally.

Dehomogenize at $h=c=1$. The coefficient family is the linear span of $1,y_1,\ldots,y_m,z^{\mathsf T}x$, on $n=2D+m$ scalar variables. The polar form of the quadratic part is hyperbolic and nondegenerate on $(x,z)$, also in characteristic two, with radical precisely the $y$-space. A linear space on which the quadratic part vanishes projects to a totally isotropic subspace of this polar form of dimension at most $D$. The subspace $x=0$ attains total dimension $D+m$. The exact uniform-size formula from the determinantal proof gives minimum $1+n-(D+m)=D+1$. The displayed matrix achieves it. [Exact uniform size theorem](https://github.com/Dugongue/MathProofs/blob/927d262c8992bd305b625ad56ca25564555700f0/DeterminantalGeometryAndModules/UniformQuadraticSystems.md)

For the module claim take a commutative coefficient ring over $k$ and replace $a_0,a_1,b_j$ by arbitrary square matrices of a common size $s$, with the unit replaced by $I_s$, leaving $x,z,y$ as scalar coordinates. The leading block of the dehomogenized pencil has identity diagonal and only one possible strictly lower block relative to $E\oplus F$. It is invertible of determinant one. Its right-hand column is exactly its product with $x\otimes I_s$, because the scalar coordinates commute with every entry. Block elimination transforms the evaluated presentation to
$$
\operatorname{diag}\!\left(
 I_{Ds},\ A_0+\sum_j y_j B_j+(z^{\mathsf T}x) A_1
\right).
\tag{3}
$$
Here $A_0,A_1,B_j$ are the substituted matrices. For example, first subtract from the last block column the leading block columns multiplied by $x\otimes I_s$, then clear the lower-left block with the inverse of the leading corner. Left-multiply its corner by its inverse to obtain (3). These operations are invertible over the polynomial ring, giving isomorphic cokernels and equal ideals of each size of minors. This proof applies also to the universal polynomial matrix with symbolic entries for all the substituted matrices. It applies under arbitrary further base changes. Size $s=1$ includes the claimed scalar cokernel.

### Forward transporter

Suppose
$$
T'(Sb,H u)=J\,T(b,u)
$$
for $S\in\mathrm{GL}(B), H\in\mathrm{GL}(E), J\in\mathrm{GL}(F)$. Set $G=H\oplus J$. Then $N_{T'}(c,Sb)=G N_T(c,b)G^{-1}$. Apply the argument changes $x'=Gx$, $z'=G^{-\mathsf T}z$, $b'=Sb$, $y'=S^{-\mathsf T}y$, leaving the other coordinates fixed. Formula (1) becomes left multiplication by $\operatorname{diag}(G,1)$ and right multiplication by $\operatorname{diag}(G^{-1},1)$. This gives an actual four-tensor transporter.

### Recovery of the original transporter

Write $p=a_0h^2+h\langle b,y\rangle+a_1z^{\mathsf T}x$. In the polynomial ring over the working field, the only linear factor of (2) involving only the first variable group is $h$, up to scalar. Indeed a factor of $p$ in just that group would have to divide both coefficients $h^2$ and $z^{\mathsf T}x$. Similarly the only linear factor involving only the second group is $c$. A linear factor of $p$ in that group would require $p$ to be its product with a scalar-argument polynomial because $p$ has coefficient degree one. The two independent coefficients $h^2$ and $z^{\mathsf T}x$ exclude that. The first assertion uses $D\ge2$, which holds because $E,F$ are positive dimensional. Thus a pencil equivalence sends the two covector lines of $h,c$ to themselves. Rescale the two independent coordinate changes to make $h'=h,c'=c$; their overall factor can be absorbed into a row map by bilinearity.

After cancelling these factors in (2), the determinant identity gives $p'$ pulled back equal to a nonzero scalar $\gamma p$. In the affine chart $h=1$ the affine argument transformation therefore preserves the fixed linear space of polynomials
$$
\operatorname{span}\{1,y_1,\ldots,y_m,z^{\mathsf T}x\}.
\tag{4}
$$
In particular $y'=Qy+v$ for some invertible $Q$. The homogeneous quadratic part of the remaining generator transforms by a nonzero scalar, so the linear part preserves its polar radical $Y=\{x=z=0\}$. The transformed active pair $(x',z')$ has the form $P(x,z)+t$ with invertible $P$ and no $y$-linear contribution. The active linear part in the pullback of $z'^{\mathsf T}x'$ is the nondegenerate polar form evaluated on $P(x,z)$ and $t$. It must vanish by (4), so $t=0$. This works in characteristic two because the polar form is hyperbolic.

Comparing coefficients of $y$ and of $z^{\mathsf T}x$ in the equality $p'=\gamma p$ gives $b'=\gamma Q^{-\mathsf T}b$ and $a_1'=\kappa a_1$ for some $\kappa\ne0$. Since $p'$ has no $c$ after substitution, linear independence of (4) also gives no $c$ term in any of $a_0',a_1',b'$. At the affine argument point $x=z=y=0$ restrict the coefficients to $a_0=a_1=0$. On the target point $x'=z'=0,y'=v$ we have $a_1'=0$ and $a_0'+\langle b',v\rangle=0$, by $p'=\gamma p$. Therefore the two row and column changes give
$$
\operatorname{diag}\bigl(cI_D+\widetilde T'(Sb),0\bigr)
=U\,\operatorname{diag}\bigl(cI_D+\widetilde T(b),0\bigr)\,W,
\qquad S=\gamma Q^{-\mathsf T}.
$$
At $c=1,b=0$, equality forces $U$ to preserve the rank-$D$ image and $W$ the one-dimensional kernel of $\operatorname{diag}(I_D,0)$. Restricting the row map to this image and passing to the quotient by that kernel on the column side yields two inverse $D\times D$ maps because the identity slice matches. Hence $\widetilde T(b)$ and $\widetilde T'(Sb)$ are simultaneously similar.

For clarity, simultaneous similarity of these square-zero maps suffices even for nonconcise $T$. Their common kernel is $F\oplus K_T$, where $K_T\subset E$ is the common kernel of $T(b,-)$. Their total image is $I_T=\sum_bT(b,E)\subset F$. A simultaneous similarity thus induces invertible intertwiners on the supported pair $E/K_T$ and $I_T$. The dimensions of the unused kernel and image complements in the matched input format agree. Choose arbitrary invertible lifts on these complements to recover intertwiners on all of $E,F$. The same $S$ transports the original $B$-labels. This proves the converse without changing the base field.

The construction uses only copied input coefficients, $0,1,-1$, and has linear mode dimensions. Its dense four-array can be written in polynomial time. Conversely every equivalence instance of the displayed kind is itself four-tensor isomorphism and reduces to three-tensor isomorphism by order reduction. These proofs concern the dehomogenized coefficient substitutions in (3). The projective boundary $c=0$ of (1) retains the data that distinguishes the four-tensors. [Grochow–Qiao, order reduction](https://arxiv.org/abs/1907.00309)

### Comparison with prior results

Earlier constructions hide tensor isomorphism from bounded-size substitution Jordan or Smith data, with a larger substitution eventually distinguishing examples. The conclusion here concerns determinant and cokernel data for the affine coefficient substitutions in *all* sizes and gains the fixed scalar determinant and proven minimum-size uniform presentation. It does not compare Jordan form of the evaluated matrices. [Earlier bounded-substitution theorem](https://github.com/Dugongue/MathProofs/blob/5c79909f4154482965afbd5348f4a3e4284c2d53/SliceSimilarityFour/Tensor.md)

## Theorem 2. Bounded border-rank TI and the literal equations in Open Question 7.4

For geometric border rank at most $b$, the algebraic-closure nonisomorphism problem has ordinary Polynomial Calculus degree at most $2^{O(b^2)}$ on the original cubic action and quadratic two-sided inverse equations, uniformly in ambient side sizes and characteristic. For inputs over a fixed finite field $\mathbb F_q$ the degree is $O(qb^2)$ if field equations are added, including negative instances that acquire a witness over the algebraic closure. For fixed $b$ the isomorphism decision problem takes polynomial time over fixed finite fields and in the algebraic arithmetic model for geometric isomorphism. These are the bounded-degree and polynomial-time conclusions posed in Galesi–Grochow–Pitassi–She Open Question 7.4 in those models. The fixed-parameter conclusion already follows from the known rank-versus-border-rank comparison and the original bounded-rank theorem. The direct argument here works on the literal equations and avoids the exponent loss of first bounding ordinary tensor rank. [Published question, §7.4](https://arxiv.org/abs/2305.19320) · [Earlier rank-versus-border-rank transfer](https://github.com/Dugongue/MathProofs/blob/5c79909f4154482965afbd5348f4a3e4284c2d53/GrochowHypoworlds/TRANSFERS.md)

A tensor of border rank at most $b$ has every flattening rank at most $b$. Indeed all $(b+1)$-minors vanish on tensors of ordinary rank at most $b$, and hence on their Zariski closure. If the mode supports are $U_i$, the tensor belongs to $\bigotimes_i U_i$: after choosing bases starting with the $U_i$, each flattening condition makes the entries zero when that mode lies outside $U_i$. Tensor equivalences carry these supports to the corresponding supports. Conversely an equivalence of the three compressed spaces extends by arbitrary invertible maps on complements when their matched dimensions agree. This gives the algorithm: do Gaussian elimination, reject unequal support dimensions, and solve TI for the compressed format, with at most $b$ on each side. Over fixed finite fields exhaust the $q^{O(b^2)}$ possibilities. For geometric comparison the effective Nullstellensatz reduces fixed-size polynomial feasibility to linear algebra over the coefficient field using a degree bound that depends only on $b$. If desired one may verify the geometric border-rank promise on the same compressed formats by fixed-format elimination on the sum-of-$b$-simple-tensors map. Compression preserves geometric border rank because projection onto the supports maps simple tensors to simple tensors or zero and preserves the smaller tensor.

To get the proof-degree bound on the literal equations, use bases with the supports first, separately for the two tensors. Invertible linear substitutions between the corresponding action variables preserve PC degree since multiplication by a linear form is implemented by variable multiplications and addition. Write $A_i,B_i$ for the action and specified inverse in mode $i$. From $(A_1\otimes A_2\otimes A_3)T=S$, multiply on the other two modes by their inverse variables and use $B_j A_j=I,B_kA_k=I$. This derives
$$
(A_i\otimes I\otimes I)T=(I\otimes B_j\otimes B_k)S
$$
with degree at most five. The order of modes in this display is $i,j,k$. The correction for cancelling the inverse factors is the telescoping expansion of $(B_jA_j)\otimes(B_kA_k)-I\otimes I$. It multiplies inverse axioms by factors of total degree at most three and fixed entries of $T$. In the rows outside the target support of mode $i$, the right side is zero. Contracting the remaining flattened coordinates with a fixed right inverse of the source tensor's full-row-rank supported flattening gives every linear equation asserting that $A_i$ sends the source support into the target support. For $B_i$, multiply the original action equation just on mode $i$ by $B_i$ and use $B_i A_i=I$; contract the rows outside the source support with the corresponding target right inverse. This derives the reverse support-containment equations in degree at most four.

Take the top-left supported blocks of $A_i,B_i$, allowing unequal supports. In the inverse equations for their top-left matrix entries, terms involving outside intermediate indices vanish after multiplying the just-derived containment equations by one variable. This yields both rectangular inverse equations for the supported blocks, in degree at most six. The supported action equations already equal the top-supported entries of the original cubic equations. So the literal input derivably contains the compressed system on at most $6b^2$ variables and degree at most three. If support dimensions are unequal, one of the two rank identities makes that system geometrically unsatisfiable. Otherwise it is the compressed TI instance.

For negative geometric instances the effective Nullstellensatz for constant-degree generators gives a compressed certificate of total-product degree $2^{O(b^2)}$. Derive the compressed axioms first, then implement that certificate by ordinary PC, keeping the stated bound with the additive constant from support derivation. Over $\mathbb F_q$ keep the field equations on just the chosen variables. The basis changes preserve those axioms since the $q$-power distributes over a linear form over $\mathbb F_q$. For $s\le6b^2$ variables the quotient by the field equations has monomial representatives with all exponents below $q$, and is the algebra of functions on $\mathbb F_q^s$. Unsatisfiability gives the unit in the ideal inside this algebra. Simulate ideal generation by repeated multiplication by a variable and addition. Intermediate lines can be reduced after each multiplication by subtracting monomial multiples of field axioms, so the degree never exceeds $\max(6,q,s(q-1)+1)$. This proves the finite-field result and uses no arithmetic hypothesis. [Effective Nullstellensatz, Kollár](https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/Kollar/kollarnullstellen.pdf)

A linear lower bound in $b$ already follows from the portfolio's sparse PC examples. In positive characteristic their hard diagonal tensors have ordinary rank at most $4q_0$ and degree $\Omega(q_0)$ for the prime powers $q_0$ used there. In characteristic zero the hard tensors have the $N$ diagonal slices and one adjacency slice, so have ordinary rank at most $N+\operatorname{rank}A\le2N$, with degree $\Omega(N)$. Ordinary rank bounds border rank in both cases. The gap in the quantitative dependence on $b$ remains: this does not prove a polynomial degree upper bound without field equations as requested separately in Question 7.1. [Positive characteristic examples](https://github.com/Dugongue/MathProofs/blob/5c79909f4154482965afbd5348f4a3e4284c2d53/TensorSparsePCBounds/Proof.md) · [Characteristic zero examples](https://github.com/Dugongue/MathProofs/blob/5c79909f4154482965afbd5348f4a3e4284c2d53/TensorSparsePCBounds/CharacteristicZero.md)

Both theorems have written proofs. Neither has been formalized in Lean. The exact fixed-polynomial equivalence theorem has provisional literature priority. The bounded-border-rank theorem is a direct consequence of the flattening support technique and known effective certificate bounds.
