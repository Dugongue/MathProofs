# A localization defect for symplectic subgroups and symmetric-form spaces

Let \(B\) be ordinary three-mode tensor isomorphism over \(\mathbb F_3\). There is a deterministic polynomial-time construction from two independent instances \(x,y\) of \(B\) of **one pair** of split, smooth, geometrically connected closed subgroup schemes
\[
H_0,H_1\subseteq\operatorname{Sp}_{6d,\mathbb Z}.
\]
Both are abstractly \(\mathbb G_m\times\mathbb G_a^{2d}\). Their conjugacy over \(\mathbb Z[1/2]\) holds exactly when \(x\in B\), and their conjugacy over \(\mathbb Z\) holds exactly when \(x,y\in B\). For every prime \(\ell\) they are conjugate over \(\mathbb Z_{(\ell)}\) and \(\mathbb Z_\ell\), on every input. They are also conjugate over \(\mathbb Q\) and \(\mathbb R\). Thus failure of integral conjugacy repaired by inverting \(2\) computes precisely \([x\in B]\wedge[y\notin B]\) inside a family satisfying all of these local comparisons.

The same construction yields two ordinary finite lists generating free direct-summand submodules of symmetric bilinear forms on a fixed symplectic lattice. Each list contains the same hyperbolic unimodular symmetric form. With the lists interpreted as unmarked spans and with change of basis symplectic, the same exact conjugacy and locality statements hold. Both assertions apply to subspaces or embedded groups without a preferred Lagrangian or specified action on the parameter group.

## A carrier over any domain

Let \(R\) be a commutative domain and \(T:X\times Y\to Z\) a bilinear map of finite free \(R\)-modules, each of positive rank. For two tensors in the same format write \(T\simeq_R T'\) for ordinary tensor isomorphism. In the bimap convention this means \(T'(P_Xx,P_Yy)=P_ZT(x,y)\) for invertible \(R\)-linear maps in the three roles.

There is an explicit polynomial-size, coefficient-copying functorial construction of a subgroup scheme
\[
H(T)\subseteq\operatorname{Sp}_{6d,R},\qquad
d=3+\operatorname{rank}X+\operatorname{rank}Y+\operatorname{rank}Z,
\]
such that \(H(T)\) and \(H(T')\) are symplectically conjugate over \(R\) exactly when \(T\simeq_R T'\). The conclusion also holds when the conjugating matrix is allowed to lie in \(\operatorname{GSp}_{6d}(R)\). The construction commutes with every scalar extension, and the equivalence applies over every domain obtained by scalar extension, including domains of characteristic two. All conjugacy of subgroup schemes is equality as embedded subgroup schemes after conjugation.

### A triangular associative algebra

Form a free unital associative \(R\)-algebra \(A(T)\) with underlying module
\[
R e_1\oplus R e_2\oplus R e_3\oplus X_{12}\oplus Y_{23}\oplus Z_{13}.
\]
The \(e_i\) are pairwise orthogonal idempotents with sum one. Each \(ij\)-corner has left identity \(e_i\) and right identity \(e_j\), with the other multiplications by vertex idempotents zero. The only possibly nonzero product of two off-diagonal corners is \(xy=T(x,y)\) in the \(13\)-corner. For associativity, products of three off-diagonal elements vanish in both associations. For two off-diagonal elements, compatibility with a vertex idempotent follows from the displayed corners, including the middle vertex \(2\). All remaining products are the standard diagonal bimodule actions.

The sum \(J\) of the three corners has \(J^3=0\). It is the largest nilpotent two-sided ideal, since \(A(T)/J=R^3\) has no nonzero nilpotents. Any \(R\)-algebra isomorphism \(f:A(T)\to A(T')\) maps \(J\) to \(J'\) and permutes the three diagonal quotient idempotents. Write \(f_i=f(e_i)\) and write \(e'_{\pi(i)}\) for the corresponding diagonal lift. Then
\[
c=\sum_i e'_{\pi(i)} f_i
\]
is \(1\) modulo \(J'\), so it is a unit. Orthogonality gives \(c f_i=e'_{\pi(i)}c\). After conjugating \(f\) by \(c\), it maps each vertex to the corresponding diagonal vertex exactly. The directed graph of nonzero corners has edges \(1\to2,\ 1\to3,\ 2\to3\), regardless of the entries of \(T\), since all modules have positive ranks. Its three outdegrees are distinct, so \(\pi\) is the identity. The three corner restrictions then supply a tensor transporter. Conversely any tensor transporter, together with the identity on the diagonal, gives an algebra isomorphism. This proves
\[
A(T)\cong_{R\text{-alg}} A(T')\quad\Longleftrightarrow\quad T\simeq_R T'.
\]

### A left-regular matrix space

For any unital associative \(R\)-algebra \(A\) of free rank \(d>0\) write \(L_a\) for left multiplication by \(a\). On \(V=A\oplus A\oplus A\) define
\[
N_{a,b}(x,y,z)=(0,0,ax+by),\qquad
\mathcal N_A=\{N_{a,b}:a,b\in A\},\qquad W=0\oplus0\oplus A.
\]
Every product of two operators from \(\mathcal N_A\) vanishes. The sum of their images and the intersection of their kernels both equal \(W\), using \(N_{1,0}\) and \(N_{0,1}\). On \(V^*\), the sum of the images of their transposes equals \(W^\perp\), the annihilator of \(W\). Indeed all images lie there, and the transposes of \(N_{1,0},N_{0,1}\) separately generate its two coordinate summands. In particular, the image sums on \(V\) and \(V^*\) have ranks \(d\) and \(2d\).

An invertible map \(q:V\to V'\) carrying \(\mathcal N_A\) to \(\mathcal N_{A'}\) by conjugacy carries \(W\) onto \(W'\). Let \(P:W\to W'\) and \(Q:V/W\to V'/W'\) be its restriction and quotient. Then \(P\mathcal M_AQ^{-1}=\mathcal M_{A'}\) for the rectangular matrix spaces
\[
\mathcal M_A=\{[L_a\ L_b]:a,b\in A\}\subseteq\operatorname{Hom}_R(A^2,A).
\]
Their left idealizers are precisely their left regular algebras. For if \(C\in\operatorname{End}_R(A)\) satisfies \(C\mathcal M_A\subseteq\mathcal M_A\), applying this to \([I\ 0]\) gives \(C=L_c\) for some \(c\in A\). Conversely, every \(L_c\) has the required property by associativity. The left regular representation is faithful, as \(L_a(1)=a\). Consequently conjugation by \(P\) induces an \(R\)-algebra isomorphism \(A\cong A'\). In the other direction an algebra isomorphism \(\phi:A\to A'\) gives \(q=\phi\oplus\phi\oplus\phi\) carrying the operators as required.

### Eliminating the Lagrangian marks inside the symplectic group

Give \(E=V\oplus V^*\) the alternating form
\[
\omega((v,\ell),(w,m))=m(v)-\ell(w).
\]
Define the following embedded subgroup scheme, with the matrix formula interpreted over every commutative \(R\)-algebra:
\[
H(A)=\left\{\begin{pmatrix}
\lambda(I+N_{a,b})&0\\
0&\lambda^{-1}(I-N_{a,b}^{\,T})
\end{pmatrix}:\ \lambda\in\mathbb G_m,\ (a,b)\in\mathbb G_a^{2d}\right\}.
\]
The second block is the inverse transpose of the first. Since all products of two \(N\)'s vanish, the formula is a homomorphism from the direct product of the scalar torus and the additive group. It is a closed immersion. A diagonal entry from each block recovers \(\lambda,\lambda^{-1}\). Multiplying the off-diagonal entries in the first block by \(\lambda^{-1}\) recovers \(N_{a,b}\). Evaluation on \((1,0,0)\) and \((0,1,0)\) recovers \(a,b\). These are polynomial operations in the ambient matrix entries, giving a surjection from the ambient coordinate ring onto \(R[\lambda,\lambda^{-1},a_1,\ldots,a_d,b_1,\ldots,b_d]\). In particular \(H(A)\) is smooth and geometrically connected, and the construction commutes with scalar extension.

Any scheme isomorphism between two such split products preserves their displayed torus and additive factors. A group scheme map \(\mathbb G_m\to\mathbb G_a\) would be a Laurent polynomial \(f\) with \(f(uv)=f(u)+f(v)\). The mixed Laurent coefficients force every nonconstant coefficient to vanish, and the identity forces the constant coefficient to vanish. A group scheme map \(\mathbb G_a^n\to\mathbb G_m\) would be an invertible polynomial. Over a domain it is a constant, which is one at the identity. Applying these facts to an isomorphism and its inverse proves the claim about factors. The automorphisms of the torus are identity and inversion, by the description of the units of \(R[\lambda,\lambda^{-1}]\) and the existence of an inverse morphism.

Suppose a symplectic conjugator carries \(H(A)\) to \(H(A')\). If it induces inversion on the torus, it exchanges the two weight spaces \(V,V^*\) with \(V'^*,V'\). To see this over any domain, equate the matrix identities in \(R[\lambda,\lambda^{-1}]\) and compare the independent Laurent monomials \(\lambda\) and \(\lambda^{-1}\). On the respective weight spaces, the sums of the images of unipotent operators minus the identity have ranks \(d\) and \(2d\). These sums must match under the conjugator because it preserves the additive factor. Hence inversion is impossible. The two weight spaces are separately preserved, and the restriction to \(V\) conjugates \(\mathcal N_A\) to \(\mathcal N_{A'}\). The left regular argument gives an algebra isomorphism. Conversely any such isomorphism yields \(q=\phi^{\oplus3}\) and the symplectic conjugator \(\operatorname{diag}(q,q^{-T})\). The proof of reflection used only the matrix conjugation identities and applies to a similitude as well. Taking \(A=A(T)\) proves the carrier theorem.

The proof also compares the actual \(R\)-point subgroups when \(R\) has infinitely many units. The displayed coordinates give a Zariski dense set of \(R\)-points in the generic fiber, since each coordinate ranges over an infinite subset of the fraction field. A conjugator of point subgroups therefore conjugates the generic subgroup schemes. For either embedded scheme its defining ideal is the contraction of its generic-fiber ideal, since its coordinate ring is \(R\)-torsion-free. For the given integral matrix, equality of the conjugated and target generic subgroup schemes therefore implies equality integrally. This applies, in particular, to \(R=\mathbb Z_\ell\) for every \(\ell\).

## An ordinary finite matrix presentation over domains with \(2\ne0\)

With \(V,E\) as above put
\[
D=\operatorname{diag}(I_V,-I_{V^*}),\quad
\widetilde{\mathcal N}_A=\{\operatorname{diag}(N,-N^T):N\in\mathcal N_A\},\quad
\mathcal L(A)=R D\oplus\widetilde{\mathcal N}_A\subseteq\mathfrak{sp}(E).
\]
This is a free abelian Lie subalgebra of rank \(2d+1\), given by \(D\) and the operators obtained from a coordinate basis for \(a,b\). The coefficient of $D$ can be recovered from a diagonal entry, and the $a,b$ coordinates can be recovered by evaluation of the upper block on $(1,0,0)$ and $(0,1,0)$. These readouts split the displayed free module off from the ambient module. Its square-zero elements are exactly \(\widetilde{\mathcal N}_A\). Indeed the diagonal entries of the square of \(cD+\widetilde N\) are all \(c^2\), whereas \(\widetilde N^2=0\). Domain cancellation forces \(c=0\) for a square-zero element.

A conjugator carrying \(\mathcal L(A)\) to \(\mathcal L(A')\) thus carries the nilpotent matrix spaces to one another. The image of \(D\) has the form \(cD+\widetilde N\) and squares to \(I\). The diagonal forces \(c^2=1\), while the remaining equation is \(2cD\widetilde N=0\), since \(D\) commutes with all such operators. In a domain with \(2\ne0\) this forces \(c=\pm1\) and \(\widetilde N=0\). Sending \(D\) to \(-D\) exchanges its \(+1\) and \(-1\) eigenspaces, which are exactly \(V,V^*\) even when \(2\) is a nonunit. This is impossible by their unequal image ranks for the nilpotent spaces. As before the restriction to \(V\) yields an algebra isomorphism, and an algebra isomorphism gives a symplectic conjugator.

The linear identification \(X\mapsto\omega(X\,\cdot,\cdot)\) identifies \(\mathfrak{sp}(E)\) with the space of symmetric bilinear forms on \(E\). It carries symplectic conjugacy to ordinary change of basis by a symplectic matrix. The element \(D\) gives the symmetric hyperbolic form \((v,\ell),(w,m)\mapsto m(v)+\ell(w)\). Under this identification \(\mathcal L(A(T))\) is therefore an unmarked space of symmetric bilinear forms containing the same standard hyperbolic unimodular form for every tensor in the format. It is symplectically congruent to the space of \(T'\) exactly when the tensors are ordinarily isomorphic.

## The arithmetic compositions

Use the two previous results in *Four consequences of the directional sign-gap theorem*, suggested ranks 2 and 3, with full proofs in its chapters *One directional query for an ordinary tensor-isomorphism difference* and *A directional gap is an exact one-localization defect of ordinary tensor isomorphism*. The arithmetic chapter uses ordinary free-tensor packing over the written domains. [Grochow–Qiao–Stange–Sun, Theorems 3.7 and 3.12](https://arxiv.org/html/2611.00735v1#S3.SS3)

First, the rank 2 construction sends \(x,y\) to a pair \(z\) of ternary tensors with a displayed ordinary transporter. Its proof gives the individual identities
\[
A_{(-1,1,1)}(z)=[x\in B],\qquad A_{(1,1,1)}(z)=[y\in B],
\]
where \(A_v\) asks for a transporter with prescribed determinant tuple \(v\). The rank 3 integral construction sends \(z\) to one ordinary free tensor pair \((F_0,F_1)\) over \(\mathbb Z\), ordinarily isomorphic globally exactly when both identities are positive, and over \(\mathbb Z[1/2]\) exactly when the first is positive. Its local assertion gives ordinary isomorphism over every \(\mathbb Z_{(\ell)}\), since \(z\) comes with an ordinary transporter. Apply either symplectic carrier to \(F_0,F_1\) and use the same written data over each ring. The equivalence at each base gives the two claimed answers. Base change gives conjugacy over \(\mathbb Z_\ell,\mathbb Q,\mathbb R\) as well. For an explicit family with a genuine integral obstruction, take \(x\) an identical pair and \(y\) the pair of a nonzero scalar tensor and the zero scalar tensor.

Second, for inputs over any explicitly presented finite field, including characteristic two, take
\[
S=\mathbb Z[t,s,r_1,r_2,r_3],\qquad S'=S[1/(r_1r_2r_3)].
\]
For every framed comparison \(z\) over that field and determinant tuples \(\alpha,\beta\), the same rank 3 arithmetic result followed by either carrier gives one pair of subgroup schemes or symmetric-form spaces with conjugacy conditions
\[
\begin{aligned}
\operatorname{Conj}_{S}&\ \Longleftrightarrow\ A_\alpha(z)\wedge A_\beta(z),\\
\operatorname{Conj}_{S'}&\ \Longleftrightarrow\ A_\alpha(z).
\end{aligned}
\]
The pair is conjugate at every prime localization of \(S\) of height at most five on every input. It is conjugate at all maximal localizations precisely when \(z\) is ordinarily isomorphic. These assertions follow by applying the carrier equivalence at each localized domain to the prior arithmetic theorem. In the fixed ternary case the input \(z\) from the first composition again makes every maximal localization positive. The distinction between the characteristic of the input field and the characteristic-zero carrier domains allows the symmetric-form version also for finite input fields of characteristic two.

These are deterministic polynomial-time constructions in the prior input encodings. The triangular multiplication table adds only zeros, ones and the original tensor entries. The matrices of the \(2d\) additive generators copy left multiplication coefficients and append fixed zero and identity blocks. The subgroup scheme can be written as the above polynomial parameterization with \(\lambda,\lambda^{-1}\) as coordinates satisfying \(\lambda\lambda^{-1}=1\), with no elimination required. The finite matrix version writes \(2d+1\) matrices of order \(6d\). The same construction gives explicit lift and reflection of transporters by the displayed formulas. In particular, for a supplied symplectic matrix its inverse is obtained by transposition and multiplication by the fixed symplectic form matrices. The inverse of its block on the intrinsic image sum is the corresponding restriction of that inverse. The inverse of the idempotent-aligning element uses the degree-two geometric sum in the cube-zero ideal. Thus the extraction uses only a polynomial number of ring operations. The reductions and identities above are paper proofs.
