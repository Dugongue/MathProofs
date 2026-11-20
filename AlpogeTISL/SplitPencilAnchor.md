# Special-linear tensor isomorphism for split Pfaffian pencils

**Theorem.** Fix a finite field $F=\mathbb F_q$ of odd characteristic. Consider raw $n\times 2n\times 2n$ tensors whose matrix pencils, after some left and right changes of bases, are alternating. Suppose the formal Pfaffian of an alternating presentation is nonzero and is a product of $n$ linearly independent geometric linear forms. Assume either that their Frobenius orbits have pairwise distinct lengths, or that the number of orbits is bounded by a fixed constant. On this promise class, deterministic polynomial time reduces prescribed-determinant tensor isomorphism, in particular SL-TI, to one ordinary 3-TI instance over $F$. The reduction uses the raw arrays. All three dimensions, the individual orbit lengths, and the dimension of the alternating form space can grow.

The proof uses the separable trace Gram construction in Alpöge's release. The released theorem $\mathtt{GlobalTheory.CompanionTheory.SW.CoordMat.traceGram\_det\_ne\_zero}$ applies to finite separable field extensions. With the identity involution and $1\times1$ matrix $(1)$, it gives nondegeneracy of $(x,y)\mapsto\operatorname{Tr}(xy)$. A product of these pairings gives the corresponding result for a finite étale algebra. Here the Gram matrix is computed directly from the logarithmic second derivative of the input Pfaffian. Its third derivative supplies the multiplication that the Gram matrix uniquely recovers. The trace lemma is part of the released proof's algebraic development. The reduction uses no analytic RH or GRH statement. [Alpöge release](https://alpo.ge/remark.pdf)

## 1. Recover an alternating presentation

Use the convention $G^{\mathsf T}M_S(fx)H=M_T(x)$ for the three input maps $f,G,H$, taking modes of a dual space by the corresponding inverse determinants when necessary. For each raw pencil $M$, compute the space
$$
\mathcal D=\{B:M(x)B\ \text{is alternating for every }x\}
$$
by linear equations on basis slices. A left and right equivalence to an alternating pencil guarantees an invertible $B_*\in\mathcal D$. Indeed, if $P M(x)Q$ is alternating, so is $M(x)Q P^{-\mathsf T}$. Write $N(x)=M(x)B_*$. The change from $P M(x)Q$ to $N(x)$ is a simultaneous congruence, which preserves the factor hypothesis. Then $\mathcal D=B_*\mathcal C$, where
$$
\mathcal C=\{A:N(x)A\ \text{is alternating for every }x\}.
$$

We show that $\mathcal C$ is a finite étale algebra. Work first over $\bar F$, take $a$ with $N(a)$ invertible, and put $\Omega=N(a)$ and $R_x=\Omega^{-1}N(x)$. Each $R_x$ is self-adjoint for $\Omega$. The equations for $\mathcal C$ say that $A$ is self-adjoint for $\Omega$ and commutes with all $R_x$. Write the Pfaffian as $c\prod_{i=1}^n\ell_i(x)$. Choose $b$ such that the $n$ numbers $s_i=\ell_i(b)/\ell_i(a)$ are distinct. The characteristic polynomial of $R_b$ is
$$
\det(tI-R_b)=\det(N(a))^{-1}\det N(ta-b)=\prod_i(t-s_i)^2.
$$
The generalized eigenspaces of a self-adjoint operator for distinct eigenvalues are mutually orthogonal, by the primary decomposition and self-adjointness of polynomials in the operator. Each of these spaces is therefore nondegenerate and two-dimensional. On a two-dimensional alternating space in odd characteristic a self-adjoint endomorphism is scalar, as follows by writing its matrix in a symplectic basis. Every element of $\mathcal C_{\bar F}$ preserves these spaces and is scalar on them. Products of such matrices still satisfy the original self-adjointness and commutation equations. Thus $\mathcal C_{\bar F}$ is a unital subalgebra of $\bar F^n$, so it is reduced. It follows that $\mathcal C$ is finite étale over the perfect field $F$.

To find a rational converter without knowing $B_*$, take any computed basis $D_1,\ldots,D_s$ of $\mathcal D$. Over $\bar F$, the determinant on $\mathcal D=B_*\mathcal C$ is a nonzero constant times a product of powers of nonzero linear forms in the $s$ coordinates, by the preceding diagonal description. Therefore
$$
\det(D_1+tD_2+\cdots+t^{s-1}D_s)
$$
is a nonzero polynomial of degree at most $2n(s-1)$. Evaluate along this curve over an explicit extension $K/F$ of cardinality above that bound and at most $q$ times the required size, to obtain an invertible $D$ over $K$. Such small extensions can be found deterministically, for example by enumerating and testing monic polynomials of degree $O(\log_q n)$. In the constant-size boundary case take $K=F$. Now $D^{-1}\mathcal D_K=\mathcal C_K$, because $B_*^{-1}D$ is a unit of $\mathcal C_K$. Intersecting the computed $K$-linear subspace with the rational matrices, by linear equations in a basis of $K/F$, recovers $\mathcal C$.

For any explicit finite étale algebra, its primitive rational idempotents can be computed by linear algebra. Solve $x^q=x$, obtaining a split algebra $F^k$. Refine simultaneous eigenspaces of multiplication by its basis elements using all $q$ possible eigenvalues. The final spaces are one-dimensional within this split algebra. The components of $1$ are its primitive idempotents, which are also the primitive idempotents of the original étale algebra. For each primitive idempotent $e$ of $\mathcal C$, select a nonzero vector of $\mathcal D e$ and sum these vectors. Under the unknown identification $\mathcal D=B_*\mathcal C$, this sum has a nonzero element in every field component, so it is invertible. It is the required rational converter $B$. Replace $M$ by $M B$. The second physical map in the new arrays is $B_S^{-1}H B_T$, so its prescribed determinant is adjusted by $\det B_T/\det B_S$. From now on use the alternating presentations.

## 2. Extract the label algebra and its rational factors

For an alternating pencil set $P(x)=\operatorname{Pf}(M(x))$. An invertible slice $a$ temporarily over an extension suffices for the next operations. Find one along the same moment curve in the parameter space. Since $P$ is a product of nonzero linear forms, this search is deterministic over an extension of polynomial cardinality. At this slice form
$$
\beta_a(x,y)=-D_xD_y\log P(a),\qquad
\gamma_a(x,y,z)=\tfrac12D_xD_yD_z\log P(a).
$$
These are logarithmic derivatives defined by differentiating $D P/P$. No logarithm or division by $3$ is required. For $R_x=M(a)^{-1}M(x)$, the identities $\det M=P^2$ and $D_x M^{-1}=-M^{-1}M(x)M^{-1}$ yield
$$
\beta_a(x,y)=\tfrac12\operatorname{tr}(R_xR_y),\qquad
\gamma_a(x,y,z)=\tfrac14\operatorname{tr}(R_xR_yR_z+R_xR_zR_y).
$$
Indeed the logarithmic first derivative of $\det M$ is $\operatorname{tr}(M^{-1}M(x))$, and the logarithmic derivatives of $\det M$ are twice those of $P$. These matrix traces give polynomial-time evaluations in every odd characteristic.

Let $s_i(x)=\ell_i(x)/\ell_i(a)$. In geometric normal coordinates the two forms are
$$
\beta_a(x,y)=\sum_i s_i(x)s_i(y),\qquad
\gamma_a(x,y,z)=\sum_i s_i(x)s_i(y)s_i(z).
$$
Thus $\beta_a$ is the separable trace Gram matrix with coordinates normalized at $a$. Solve $\beta_a(L_x y,z)=\gamma_a(x,y,z)$ for the multiplication operators $L_x$. In the same coordinates these are exactly all diagonal matrices as $x$ varies. Their span $\mathcal E$ is independent of $a$. It is Frobenius-stable, since Frobenius permutes the Pfaffian normal lines, and the matrix subspace over $K$ can again be intersected with the rational matrices. This yields a finite étale $F$-algebra $\mathcal E\subseteq\operatorname{End}_F(F^n)$.

The parameter space is a rank-one $\mathcal E$-module. This follows after scalar extension to the split algebra, where the primitive factors act on one-dimensional eigenspaces. In particular each rational field component $E_j$ acts on its summand with module dimension one. Choose a nonzero vector in each summand and let $a$ now denote their rational sum. Every geometric normal coordinate of $a$ is nonzero. With the identification $z\mapsto z a$ from $\mathcal E$ to the parameter space, one has
$$
P(z a)=P(a)\prod_j\operatorname{Norm}_{E_j/F}(z_j).
\tag{1}
$$
The degrees of the $E_j$ are precisely the Frobenius orbit lengths of the geometric factors. The factor $P(a)\in F^\times$ is computable by alternating elimination on $M(a)$.

For each primitive rational idempotent $e_i$ of $\mathcal C$, write $W_i=e_i F^{2n}$. The equations above make these summands mutually orthogonal for all $M(x)$. Each has a nondegenerate alternating restriction of $M(a)$, so $\dim_F W_i$ is even. Its restricted Pfaffian $P_i$ is nonzero and homogeneous of positive degree. Their product equals $P$ up to a known nonzero frame factor. Since the geometric factors of $P$ are distinct, the factors of each $P_i$ form a union of entire Frobenius orbits, and these unions partition the factors of $P$. Determine that partition directly. Compute the logarithmic Gram form $\beta_i$ of the restricted pencil at $a$ by the same matrix traces. Solve for the operator $J_i$ with $\beta_a(J_i x,y)=\beta_i(x,y)$. In the split coordinates $J_i$ is the diagonal projector onto the normals dividing $P_i$, so in $\mathcal E$ it is the sum of the corresponding primitive rational idempotents. Thus every $\mathcal C$-factor is identified by an explicit nonempty subset of the $\mathcal E$-factors.

## 3. Determinants of a linked transporter

Keep the three actual maps $f,G,H$ in the same tensor system. The determinant of the pencil identity implies $P_S(fx)^2=cP_T(x)^2$ with $c\in F^\times$. Over $\bar F$ this maps the two sets of geometric factor lines to each other. Hence $f$ conjugates the label algebra $\mathcal E_T$ to $\mathcal E_S$. It induces a matching of rational factors with the same degrees. In the parameter frames $z\mapsto z a_T$ and $z\mapsto z a_S$, the component map has the form $z\mapsto u_j\sigma_j(z)$, with $\sigma_j$ an $F$-field isomorphism. Set
$$
L=\prod_j\operatorname{Norm}(u_j),\qquad \rho=P_S(a_S)/P_T(a_T).
$$
Equation (1) gives $P_S(fx)=\rho L\,P_T(x)$ identically. In matched factor orders and chosen field bases, $\det f$ is the known ratio of adapted parameter basis determinants times $L\prod_j\det_F\sigma_j$.

The linear map $\alpha(A)=H A G^{-1}$ carries the source $\mathcal C$-space bijectively to the target $\mathcal C$-space. Indeed $M_S(fx)\alpha(A)=G^{-\mathsf T}M_T(x)A G^{-1}$ is alternating for every $x$ precisely when $A\in\mathcal C_T$. Put $u=\alpha(1)=HG^{-1}$, which is a unit of $\mathcal C_S$. Then $A\mapsto u^{-1}\alpha(A)=GAG^{-1}$ is an algebra isomorphism $\theta:\mathcal C_T\to\mathcal C_S$. The maps $G,H$ therefore carry each $W_{T,i}$ to the same $W_{S,i'}$, and the Pfaffian-factor subset identifying $i'$ is precisely the image of the subset identifying $i$, by restricting the pencil identity to these summands and taking determinants.

Let $C_i$ denote the $i$-th field component of $\mathcal C_S$, $d_i=[C_i:F]$, and $r_i=\dim_F W_{S,i}/(2d_i)$. The integer $r_i$ is well-defined. Over $\bar F$ the $d_i$ different embedding spaces have equal dimension, since $W_{S,i}$ is a vector space over $C_i$; each is nondegenerate for the fixed alternating $M_S(a_S)$, so that common dimension is even. For $V\in\mathcal C_T^\times$, the same splitting into orthogonal spaces shows
$$
\operatorname{Pf}(M_T(x)V)
 =P_T(x)\prod_i\operatorname{Norm}(V_i)^{r_i}.
$$
Here source factors are identified with the matched target factors, and the restriction holds for all $x$ by the block Pfaffian identity, including singular slices. Define $Z=\prod_i\operatorname{Norm}(u_i)^{r_i}$. Then $\det_F u=Z^2$. Set $V=H^{-1}G\in\mathcal C_T^\times$ so $\alpha(V)=1$; hence $\theta(V)=u^{-1}$. Applying Pfaffian congruence to $G^{\mathsf T}M_S(fx)G=M_T(x)V$ gives
$$
\det G=(\rho L Z)^{-1},\qquad
\det H=Z(\rho L)^{-1}.
\tag{2}
$$
This reads both matrix-mode determinants from the same transporter, even when $G$ and $H$ are genuinely independent.

## 4. Compile all readings into one TI instance

Fix a matching of the $E_j$ by degree. In the distinct-degree case it is forced. Otherwise there are at most $k!$ matchings for the fixed bound $k$ on the number of factors. The matching of the $C_i$ is forced by their factor subsets, and any unmatched subset or weight discrepancy rejects that branch.

Use the original tensor along with these maps as typed linear data of arity at most three. For the label algebra, include its multiplication and evaluation on the raw parameter mode. This forces $\sigma$ to be the algebra map induced by $f$, and the evaluation identifications $z\mapsto za$ force the semilinear maps on the field component copies. For $\mathcal C$, include its multiplication and evaluation on the first matrix mode, which forces $\theta$ to be the algebra map induced by $G$. Include an additional linear copy of $\mathcal C$ with evaluation regarded as maps from the first to the second matrix modes. Its linked map must then be $\alpha(A)=HAG^{-1}$. Component multiplication maps tie it semilinearly to $\theta$. All included maps are constructed from the displayed raw subspaces or their factored modules. On any genuine transporter they admit exactly the induced actions.

Read the norm of each semilinear map $x\mapsto u\,\sigma(x)$ on a degree-$e$ field component by $e$ copies linked through the $F$-linear $q$-Frobenius powers. Their maps are $x\mapsto u^{q^l}\sigma(x)$, for $0\le l<e$. A chain of multiplication tensors links these maps to the final product map $x\mapsto\operatorname{Norm}(u)\sigma(x)$. Each product map is forced because the multiplication map is surjective. Include the inclusion of the scalar field into the final copy to obtain the multiplier $\operatorname{Norm}(u)$ on a one-dimensional $F$-sort. To read $\det_F\sigma$, compute one reference $F$-isomorphism $\sigma_0$ between the explicit finite fields and compute its determinant in the chosen bases. A reference can be found deterministically by finite-field isomorphism algorithms. One can use the prime-field version and enumerate its at most $e[F : \mathbb F_p]$ Frobenius conjugates to select an $F$-linear map. The determinant of the $q$-Frobenius is $(-1)^{e-1}$, by its cyclic action on the geometric embeddings. For odd $e$ the reference determinant is therefore constant. For even $e$, mark the trace-zero line in the unique quadratic subfield, with reference frames $w,\sigma_0(w)$. On that line the $q$-Frobenius acts by $-1$, so the line multiplier times $\det\sigma_0$ is exactly $\det\sigma$. [Lenstra, Finding Isomorphisms Between Finite Fields](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf)

Multiply the scalar certificates, with powers $r_i$ as needed, by further one-dimensional multiplication tensors. Mark the resulting lines at the three required scalars after the known frame conversions. This enforces (1), (2), and the parameter determinant. The line for a constant is just a fixed one-dimensional sort with marked basis. Inverse powers and the reciprocal in (2) can be imposed by a multiplication link whose other two multipliers multiply to one. The construction uses polynomially many field-linear and field-bilinear coordinates; even the norm diagrams have only quadratically many field-space coordinates in their field degree before packing.

Apply the uniform mixed-system packing to the linked data in each branch. Their number, arity, and dimensions satisfy its polynomial bounds, so the fixed-signature tensor-system compiler gives one ordinary 3-TI pair per branch. Every branch-system isomorphism projects to an original transporter with the required determinants. A true transporter induces the matching in at least one branch and lifts by the indicated actions. If there is more than one matching, use the binary OR construction and combine the branches in a balanced tree. The compiled ordinary TI pair is a yes instance exactly when one branch has such an isomorphism. [Uniform tensor-system packing](TraceGramOrthogonalMarkers.md#4-size-and-ordinary-compilation) · [Binary OR of ordinary TI pairs](CentroidNormLines.md#repeated-descriptors-and-modes-with-a-radical)

## Scope and evidence

This is an informal proof for the indicated promised class. It builds on the earlier split-determinant trace reconstruction and finite-field semilinear norm circuits. The new step is the simultaneously linked alternating left-right calculation, which extracts both physical determinants from the small intrinsic étale action even when neither factor map is a congruence. The moment-curve descent supplies the raw alternating presentation and rational anchor. The proof does not use analytic GRH or settle unrestricted TI_SL versus TI. No claim of publication priority or independent Lean verification is made.
