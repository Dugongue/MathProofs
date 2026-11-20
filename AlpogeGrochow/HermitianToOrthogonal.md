# Hermitian tensors as single orthogonal three-tensors

The results below are informal proofs. The upstream trace-form declaration was inspected in the released source bytes. Neither that declaration nor these reductions have an independent local Lean audit. The reduction uses an internal trace-form theorem from the Alpöge release. It has no RH or GRH hypothesis, and the evidence here does not establish that the trace-form result is a novel analytic ingredient of the release.

## Theorem

Let $E/F$ be a CM quadratic extension with conjugation $\sigma$. Fix $E$-vector spaces $V_1,V_2,V_3$ of dimensions $n_1,n_2,n_3$ with nonsingular $\sigma$-Hermitian forms $h_i$. Let $H=\prod_i U(h_i)$, and let $L$ be the $F$-space of $E$-valued $E$-trilinear forms on the three spaces. There is a quadratic space $(W,B)$ of dimension $1+2\sum_i n_i$, a closed group embedding $H\to SO(B)$, and an explicit equivariant affine-linear map $\Phi:L\to (W^*)^{\otimes3}$ with the following properties.

1. For every commutative $F$-algebra $R$ and $S,T\in L_R$, restriction gives a natural bijection from $O(B)(R)$-transporters $\Phi_S\to\Phi_T$ to $H(R)$-transporters $S\to T$. All target transporters lie in $SO(B)(R)$.
2. Over $\bar F$, $\Phi$ preserves and reflects orbit-closure containment and intersection for either target group $O(B)$ or $SO(B)$.
3. Every source invariant of degree at most $d$ extends along $\Phi$ to an $O(B)$-invariant polynomial of degree at most $21d$. The induced map $L/\!/H\to ((W^*)^{\otimes3})/\!/O(B)$ is a closed immersion. The same conclusions hold with $SO(B)$ as the target group.

The orthogonal action is diagonal on all three positions. Over fixed number fields in exact coordinates, writing the target array and its Gram matrix takes polynomial time in the input bit size.

## Released dependency

The direct input is **GlobalTheory.CompanionTheory.SW.CoordMat.coord_orthogonal** in **lean/src/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean**. The archive SHA-256 is **9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc** and the member SHA-256 is **5da8355bcf4a434b8db6a3035e2a70249c52c71ce6acc831be1cd80504e3a112**. [Alpöge's release announcement](https://alpo.ge/remark.pdf)

~~~lean
theorem coord_orthogonal :
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F,
      B.IsSymm ∧ B.det ≠ 0 ∧
      ∀ (R : Type) [CommRing R] [Algebra F R] (h : HA R σ J),
      ∃ g : Matrix (Fin M × Fin d) (Fin M × Fin d) R,
        gᵀ * B.map (algebraMap F R) * g = B.map (algebraMap F R) ∧
        ∀ X : Fin 1 → Fin M → R ⊗[F] E,
          (fun p : Fin M × Fin d =>
            (Algebra.TensorProduct.basis R b).repr
              (actW R σ J h X 0 p.1) p.2) =
          g *ᵥ fun p : Fin M × Fin d =>
            (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2
~~~

The released proof chooses its explicit **traceGram σ J b**, with entries $\operatorname{Tr}_{E/F}(\sigma(b_r)J_{ij}b_s)$. It proves symmetry, nonsingularity and transport of the Hermitian action over any commutative $F$-algebra. Apply it for $M=n_i$, $d=2$ and the Gram matrix of each $h_i$. This gives the trace forms $B_i=\operatorname{Tr}_{E/F}h_i$ and the transported orthogonal actions. The new argument encodes these actions into one tensor and recovers the Hermitian group and its invariants.

## Construction and transporters

Choose $0\ne\theta\in E$ with $\sigma(\theta)=-\theta$. Put $\delta=\theta^2\in F^\times$ and $(a_1,a_2,a_3)=(1,2,3)$. Since $E=F[\theta]$, commuting with multiplication by $\theta$ is equivalent to $E$-linearity. Define
$$
W=Fe\perp V_{1,F}\perp V_{2,F}\perp V_{3,F},\qquad
B=\langle 1\rangle\perp B_1\perp B_2\perp B_3 .
$$
Here $V_{i,F}$ denotes restriction of scalars and $B(e,e)=1$. Let $J$ vanish on $Fe$ and act by $a_i\theta$ on $V_{i,F}$. It is $B$-skew-adjoint, because $h_i(a_i\theta x,y)+h_i(x,a_i\theta y)=0$ before taking traces. Set $e^\flat=B(e,-)$ and $\omega(x,y)=B(Jx,y)$.

The alternating extension $\widehat T$ of $\operatorname{Tr}_{E/F}T$ vanishes except on permutations of the three different $V_i$ summands, with the sign of the permutation. On $V_1,V_2,V_3$ in that order its value is exactly $\operatorname{Tr}_{E/F}T$. Set
$$
\Phi_T=(e^\flat)^{\otimes3}+e^\flat\wedge\omega+\widehat T,
$$
where $(l\wedge\omega)(x,y,z)=l(x)\omega(y,z)-l(y)\omega(x,z)+l(z)\omega(x,y)$.

For arbitrary $Z$, let $e_Z$ be the metric dual of the contraction of the first two slots of $\operatorname{Sym}Z$ against $B^{-1}$. Put $\omega_Z=\iota_{e_Z}\operatorname{Alt}Z$ and define $J_Z$ by $B(J_Zx,y)=\omega_Z(x,y)$. Symmetrization and alternation are the normalized sums over the six permutations. These operations are polynomial orthogonal covariants. At $\Phi_T$ they recover $e$ and $J$, since $\omega(e,-)=0$ and $\widehat T$ vanishes on $e$.

An orthogonal transporter $g$ over $R$ must fix $e$ and commute with $J$. Interpolating on $0,a_1^2\delta,a_2^2\delta,a_3^2\delta$ gives the projector onto each summand as a polynomial in $J^2$. The denominators are nonzero elements of $F$, so this works over every $R$, even with nilpotents. On each $V_{i,F,R}$ the restriction commutes with $\theta$, hence is $E_R$-linear for $E_R=R\otimes_FE$. The trace pairing on $E_R$ in the basis $1,\theta$ has invertible matrix $\operatorname{diag}(2,2\delta)$. Evaluating trace-form preservation on $(x,y)$ and $(x,\theta y)$ now implies preservation of $h_i$. Conversely, every Hermitian isometry preserves the trace form. This identifies the common stabilizer of $e,J$ with $H$ by equations in $O(B)$, and the construction is natural in $R$. The same trace-pairing test in one slot recovers the $E_R$-trilinear form from its trace. The remaining alternating payload equality is therefore precisely the original tensor isomorphism equation.

Every such $g$ has determinant one. After the faithfully flat extension $R\to R\otimes_F\bar F$, each $V_{i,F,R}$ splits into two eigensummands paired perfectly by $B_i$. Their matrices are inverse transposes under this pairing and have determinant product one. The line $Fe$ is fixed.

## Orbit closures

Work over $K=\bar F$ and put $\lambda_i=a_i\sqrt\delta$. The orbit of $(e,J)$ under $O(B)$ is the closed set defined by the following polynomial conditions.

- $B(e',e')=1$, $J'e'=0$, and $J'$ is skew-adjoint.
- The squarefree polynomial $t\prod_i(t^2-\lambda_i^2)$ annihilates $J'$.
- The spectral projector for 0 has trace 1, and those for $+\lambda_i,-\lambda_i$ each have trace $n_i$.

The traces specify the eigenspace dimensions because the annihilating polynomial is squarefree. Skew-adjointness permits pairings of nonzero eigenspaces only between opposite eigenvalues, where the pairings are perfect by nonsingularity. Match $e,e'$, then choose a basis and its paired dual on each of the three pairs of eigenspaces. Matching these bases gives an ambient isometry between the markers. For $SO(B)$ the orbit is also closed. The quotient $O(B)\to O(B)/H$ is open and its two $SO(B)$-cosets have disjoint images, since $H\subseteq SO(B)$. Their images are open and closed in the closed orthogonal orbit.

For either choice $G$ of target group, let $\mathcal O=G(e,J)$ and $\pi(Z)=(e_Z,J_Z)$. The closure of $G\Phi_T$ lies in $X=\pi^{-1}(\mathcal O)$. With $Y=\pi^{-1}((e,J))$, the pullback along the smooth surjection $G\to\mathcal O=G/H$ is isomorphic to $G\times Y$. Its map to $X$ is $(g,y)\mapsto gy$, and it is open as a base change of the smooth orbit map. The inverse image of $G\Phi_T$ is $G\times H\Phi_T$. For an open continuous surjection, inverse image commutes with closure, so
$$
\overline{G\Phi_T}\cap Y=\overline{H\Phi_T}.
$$
The right side lies in $\Phi(L_K)$, a closed affine subspace identified with $L_K$ by $\Phi$. This proves the containment equivalence. Any common point of two target orbit closures has marker in $\mathcal O$ and can be moved into $Y$. This proves the intersection equivalence.

## Invariant degree

Over $K$, the splitting $E_K=K\times K$ identifies $H_K$ with $\prod_i\operatorname{GL}(V_{i,+})$, with $V_{i,-}$ dual to $V_{i,+}$ through $B_i$. The trilinear form decomposes into $T^+$ on the three plus-sign eigenspaces and $T^-$ on the three minus-sign eigenspaces. By polarization and the tensor first fundamental theorem for GL, invariants are linear combinations of complete contractions pairing the two types within each leg. These dual-space pairings are the restrictions of $B^{-1}$. [Tensor first fundamental theorem in this setting](https://drops.dagstuhl.de/storage/00lipics/lipics-vol362-itcs2026/html/LIPIcs.ITCS.2026.32/LIPIcs.ITCS.2026.32.html)

Define the degree-at-most-three covariant $D(Z)=\operatorname{Alt}Z-e_Z^\flat\wedge\omega_Z$. It is $\widehat T$ at $\Phi_T$. For an endomorphism $U$, put
$$
P_i(U)=\prod_{j\ne i}\frac{U^2-a_j^2\delta I}{(a_i^2-a_j^2)\delta},
\qquad
P_{1,\pm}(U)=\tfrac12P_1(U)(I\pm U/\lambda_1).
$$
These select the required legs of $J$ apart from possible $e$-components. Put
$$
A^\pm(Z)(x,y,z)=D(Z)(P_{1,\pm}(J_Z)x,P_2(J_Z)y,z).
$$
At $\Phi_T$ the $e$-components disappear in $D$, alternation forces the third leg, and $E_K$-trilinearity forces the same sign on each leg. This makes $A^\pm(\Phi_T)$ exactly $T^\pm$ extended by zero on the respective ordered slots. The degrees of the two selectors in $U$ are 5 and 4, and $J_Z$ has degree 2 in $Z$. Thus $A^\pm$ has degree at most $3+2(5+4)=21$. Perform the same complete contractions on $A^\pm(Z)$ using $B^{-1}$. Each lifts to an ambient invariant of degree at most 21 times its source degree.

Restriction in bounded degree is a linear map over $F$. Invariant subspaces commute with field extension because invariance is a kernel condition on the coordinate coaction. If an invariant over $F$ has a preimage over $K$, it therefore has a preimage over $F$. Surjectivity of the invariant-ring restriction proves the closed immersion of the quotients.

## Narrow novelty comparison

Grochow–Qiao–Tang–Zhang establish equivalences among natural actions within fixed orthogonal or unitary families. Lysikov–Walter Theorem 5.31 reduces unitary tensor isomorphism to orbit equivalence and closure intersection for GL on a doubled representation via the compact-group theorem of Bürgisser and collaborators. The result here gives a single diagonal-orthogonal third-order tensor, works for exact transporters over all CM base algebras, and explicitly bounds the degree of invariant lifting. The targeted search does not establish priority. [Grochow–Qiao–Tang–Zhang](https://arxiv.org/abs/2306.03135) · [Lysikov–Walter](https://arxiv.org/html/2411.04639v1)

## One orthogonal third-order tensor is TOCI-complete

Lysikov–Walter Theorem 5.21 establishes TOCI-completeness for a pair of third-order tensors under diagonal complex orthogonal action. Theorem 5.24 gives completeness for a single tensor of order 7. The following pair-to-one reduction lowers the single-tensor target to order 3. Theorem 5.18 of their paper puts the target in TOCI. [Lysikov–Walter, Section 5.2](https://arxiv.org/html/2411.04639v1#S5.SS2)

### Pair-to-one proposition

Given two trilinear forms $T_1,T_2$ on the standard $n$-dimensional quadratic space, one can construct a single trilinear form $\Psi(T_1,T_2)$ on the standard $(12n+1)$-dimensional quadratic space. The map is rational affine-linear, preserves and reflects orbit equality over every commutative $\mathbb Q$-algebra, and preserves and reflects geometric orbit-closure intersection. Every degree-$d$ invariant of the pair extends to a degree-at-most-$243d$ invariant of the single form.

Use $F=\mathbb Q$, $E=\mathbb Q(\theta)$ with $\theta^2=-1$, and six copies $M_i$ of $E^n$ with Hermitian form $h(x,y)=\tfrac12\sum_j\sigma(x_j)y_j$. The release's trace-Gram construction gives the standard form on each restricted $2n$-dimensional $M_i$ in the $1,\theta$ basis. Put $W=Fe\perp\bigperp_{i=1}^6M_i$ with its standard metric $B$. Let $D$ be the self-adjoint map that vanishes on the unit vector $e$ and acts by $i$ on $M_i$. Write $b_D(x,y)=B(Dx,y)$ and $l=e^\flat$.

Define a skew-adjoint $J$ by the following blocks, with zero action on $Fe$.

- On each $M_i$, the diagonal block is multiplication by $\theta$.
- The block from $M_1$ to $M_i$ for $i\ge2$ is the identity in the common coordinates. The reverse block is minus the identity.
- The block from $M_2$ to $M_3$ is $\sigma$ entrywise. The reverse block is $-\sigma$. All other blocks vanish.

The diagonal blocks are skew-adjoint for the trace form, while $\sigma$ is self-adjoint. Thus $\omega=B(J-,-)$ is alternating. For $r=1,2$, let $\widehat T_r$ be the alternating extension of $T_r$ on $M_{3r-2},M_{3r-1},M_{3r}$, evaluating $T_r$ on the $1$-coordinates. Both extensions vanish on $e$. Set
$$
\begin{aligned}
\Psi(T_1,T_2)(x,y,z)={}&
l(x)l(y)l(z)+l(x)b_D(y,z)+l(y)b_D(x,z)+l(z)b_D(x,y)\\
&+(l\wedge\omega)(x,y,z)+\widehat T_1(x,y,z)+\widehat T_2(x,y,z).
\end{aligned}
$$

For arbitrary $Z$, define $e_Z$ by metric duality of the first-two-slot contraction of $\operatorname{Sym}Z$ against $B^{-1}$, divided by $1+42n$. At an image point this gives $e$, since $De=0$ and $\operatorname{tr}D=2n\sum_{i=1}^6i=42n$. Define $D_Z$ by raising the first slot of $\iota_{e_Z}\operatorname{Sym}Z-(e_Z^\flat)^{\otimes2}$, and $J_Z$ by raising the first slot of $\iota_{e_Z}\operatorname{Alt}Z$. These polynomial covariants of degree at most 2 recover $D,J$ at image points.

A transporter fixes $e$ and commutes with $D,J$. Interpolation on $0,\ldots,6$ recovers the summands of $D$. The blocks $M_1\to M_i$ force the six restriction maps to be equal in the common coordinates, the diagonal blocks force $E_R$-linearity, and the $\sigma$ block forces the entries to lie in $R$, the fixed subring. The common map is therefore scalar extension of a single element of $O_n(R)$. Conversely each such element preserves these covariants and the marked components. Equality of the two alternating payloads gives exactly the two original tensor isomorphism equations. All six repeated copy maps have determinant product one.

For closure intersection, set $Q_Z=\operatorname{Alt}Z-e_Z^\flat\wedge\iota_{e_Z}\operatorname{Alt}Z$, of degree at most 3. At an image point it is $\widehat T_1+\widehat T_2$. Interpolate on $0,\ldots,6$ to define $P_i$ as the spectral selector of $i$ evaluated at $D_Z$. It has degree at most 12 in $Z$. Define $C_1=P_1$ and $C_i=P_i J_ZP_1$ for $i\ge2$, of degree at most 26. These act at image points as identity transport from $M_1$ to copy $i$, extended by zero. The degree-at-most-54 operator
$$
R_Z=\tfrac12\bigl(P_1-P_1J_ZP_3J_ZP_2J_ZP_1\bigr)
$$
is the projector to the $1$-coordinates of $M_1$ at an image point, since the marked cycle $1\to2\to3\to1$ acts as $-\sigma$. Recover $T_r$ at image points by evaluating $Q_Z$ on $C_{3r-2}R_Z x,C_{3r-1}R_Zy,C_{3r}R_Zz$. This gives a covariant trilinear form on $W$ of polynomial degree at most $3+3(26+54)=243$. Its specialization is exactly $T_r$ extended by zero from the common standard $n$-dimensional subspace of $M_1$. The orthogonal tensor first fundamental theorem and polarization span source invariants by pairwise metric contractions. Performing each contraction on the recovered covariants lifts it to an ambient invariant of degree at most 243 times its source degree. [Orthogonal contractions in Lysikov–Walter, Section 3](https://arxiv.org/html/2411.04639v1#S3)

Polynomial invariants distinguish disjoint geometric orbit closures of reductive groups. The lifts reflect orbit-closure intersection and equivariance gives the forward implication. The construction has polynomial output size and a linear dimension increase. Composition with Theorem 5.21 proves TOCI-hardness, and Theorem 5.18 gives membership in TOCI. The same reduction gives TOCI-hardness with the diagonal special orthogonal target, since the embedded source group acts through determinant-one matrices and the orthogonal lifts are special orthogonal invariants. Priority for the exact single-third-order target remains subject to wider literature verification.

An exact rational calculation at $n=1,2,3$ checked metric-trace recovery, both recovered operator matrices, the conjugation cycle and all ordered entries of both payloads on nonsymmetric inputs. These calculations test the formulas. The universal proof is informal.
