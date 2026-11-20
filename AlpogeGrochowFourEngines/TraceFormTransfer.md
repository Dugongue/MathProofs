# Unitary tensor isomorphism over finite rings by a trace Gram construction

## Result

Let $R$ be a finite commutative local principal ideal ring with explicit arithmetic. Let
$$
 S=R[\theta]=R[X]/(X^2-uX+v),\qquad u^2-4v\in R^\times ,
$$
and write $\bar\theta=u-\theta$ for the nontrivial quadratic involution of this presented étale algebra. The split algebra $R\times R$, with the interchanging involution, is allowed. A unitary matrix is an $S$-linear isometry of a specified nonsingular Hermitian form, with the convention $h(x,y)=\bar x^{\mathsf T}H y$. For the standard form use $H=I$. We use ordinary tensor isomorphism on free modules, the problem denoted $3\mathrm{FTI}$ in Part V of Grochow–Qiao–Stange–Sun.

For each of the five ordered three-tensor actions with direct, repeated, or inverse-transpose variables defined by Chen–Grochow–Qiao–Tang–Zhang, there is a deterministic many-one reduction to $3\mathrm{FTI}_R$ from its unitary version over $S/R$. This includes degenerate tensors, arbitrary prescribed nonsingular Hermitian forms, and mixed characteristic with residue characteristic two. The reduction is polynomial in the input length and arithmetic cost. Its degrees in the side lengths are absolute constants, independent of the nilpotence length and residue field size. In particular,
$$
 3\mathrm{FTI}_S\ \le_m^p\ \mathrm{U}_{\mathrm{hyp}}\text{-}3\mathrm{FTI}_{S/R}
 \ \le_m^p\ 3\mathrm{FTI}_R .
$$
Here the first arrow doubles each representation-space dimension and uses the hyperbolic Hermitian form on it. More generally the first arrow takes each of the five general-linear actions to the corresponding hyperbolic unitary action and works over any commutative semilocal coefficient ring with an involution. The reverse projection preserves the same repaired transporter in every occurrence of a repeated variable, including an inverse-transpose occurrence.

The standard-form version of the first arrow follows by an explicit change of basis whenever a norm-minus-one scalar has been supplied. For unramified finite chain rings in fixed residue characteristic, given their ordinary chain-ring presentation, this scalar can also be constructed in deterministic polynomial time. Thus these statements apply to the standard unitary groups of Galois rings, including their mixed-characteristic members of arbitrarily large nilpotence length. The second arrow is already a standard-form reduction without solving any norm equation.

Part III poses unitary containment over finite fields as Open Question 1.10. The earlier MathProofs finite-field result already treats the fixed-characteristic field case through restriction of scalars and a Frobenius construction. This theorem extends the trace direction to the nonreduced rings of Part V. It proves the lower arrow with an argument valid for mode supports that fail to be summands, and with the same transporter on direct and dual occurrences. The target of the upper arrow is the base ring $R$. [Chen–Grochow–Qiao–Tang–Zhang, Part III](https://arxiv.org/html/2306.03135v2#S1.SS5) · [Grochow–Qiao–Stange–Sun, Part V](https://arxiv.org/html/2611.00735v1)

## 1. Trace perfection over the nonreduced base

The input from Alpöge's release is the construction of a scalar-restricted Gram matrix, and its base-change and recovery mechanism. The source declares it in $\mathtt{GlobalTheory.CompanionTheory.SW.CoordMat.traceGram}$, with the entries
$$
  \operatorname{Tr}_{E/F}(\sigma(b_r) J_{ij}b_s)
$$
in an $F$-basis $b$ of $E$. Its algebraic companions $\mathtt{trace\_expand}$, $\mathtt{trace\_hR}$, $\mathtt{traceGram\_isSymm}$, and $\mathtt{traceGram\_det\_ne\_zero}$ give the trace coordinate expansion, symmetry and nonsingularity for a finite separable field extension with involution. The proof of nonsingularity uses the nondegenerate trace pairing. The later $\mathtt{coord\_orthogonal}$ packages the action for the number-field setting. We take the same Gram entries and prove the ring version directly. The source is the archive member named $\mathtt{TraceGramDetNeZero.lean}$ under $\mathtt{src/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis}$, with member SHA-256 $\mathtt{5da8355bcf4a434b8db6a3035e2a70249c52c71ce6acc831be1cd80504e3a112}$. [Alpöge's release](https://alpo.ge/remark.pdf)

In the basis $(1,\theta)$, the algebra trace of a scalar $z$ is $z+\bar z$, as follows from the multiplication matrix of $\theta$, whose trace is $u$. Thus the ordinary trace pairing $(a,b)\mapsto\operatorname{Tr}_{S/R}(ab)$ has matrix
$$
  \begin{pmatrix} 2&u\\u&u^2-2v \end{pmatrix}
$$
and determinant $u^2-4v$. Its determinant is a unit, so the pairing is perfect over $R$. This remains true after any base change $R\to R'$, using the same trace matrix. In particular,
$$
 \operatorname{Tr}(za)=0 \ \text{ for every } z\in S
 \quad\Longrightarrow\quad a=0 .
$$
For a nonsingular Hermitian form $h$ on a free $S$-module, $B=\operatorname{Tr}_{S/R}\circ h$ is a symmetric perfect $R$-bilinear form. Symmetry follows from trace invariance under conjugation. For perfection, $h$ identifies the underlying $R$-module with the underlying $R$-module of the $S$-dual, by a semilinear map that is $R$-linear. The trace pairing then identifies that dual with the $R$-dual. In the product basis the matrix of $B$ is exactly the source trace Gram formula.

## 2. Faithful tensor data after restriction of scalars

Represent the input tensor as an $S$-multilinear scalar form on the appropriate evaluation spaces. For an ordinary tensor $t\in V_1\otimes V_2\otimes V_3$ the form is on $V_1^\vee,V_2^\vee,V_3^\vee$. For a dual occurrence of a role use its natural variable space for evaluation. Here $V^\vee=\operatorname{Hom}_S(V,S)$. There is a natural $R$-linear identification
$$
  \operatorname{Res}_{S/R}(V^\vee)
   \ \longrightarrow\ (\operatorname{Res}_{S/R}V)^\vee,\qquad
  \lambda\longmapsto \operatorname{Tr}_{S/R}\circ\lambda.
$$
The trace matrix proves this is invertible in coordinates. It commutes with the contragredient action, so direct and dual occurrences of one role stay linked.

On each original $R$-linear role $\operatorname{Res}_{S/R}V$, mark the operator $J_\theta$ of multiplication by $\theta$ and the traced Hermitian form $B$. Mark also the traced trilinear evaluation tensor $C_t=\operatorname{Tr}_{S/R}\circ t$ on the appropriate mixed roles. These are unary linear operators, bilinear forms and one trilinear form. Their coordinates in the product bases are computed by multiplication and trace in $S/R$. On each role, the requirement that a transporter intertwine the marked $J_\theta$'s is exactly $S$-linearity, because $S=R[\theta]$. The inverse of an invertible $R$-linear intertwiner also intertwines, so the resulting transporters are invertible over $S$.

If a linked set of $S$-linear transporters preserves the traced forms, consider a defect in the Hermitian equation at a pair $(x,y)$. Replace the linear slot $y$ by $zy$ for arbitrary $z\in S$. The transported Hermitian defect is multiplied by $z$, so its trace vanishes against every $z$, hence is zero by the perfect pairing. The same test in a single slot of $C_t$ recovers the full $S$-valued tensor equation. The reverse implication follows by taking traces. Repeated roles and inverse-transpose roles use the same maps in this argument. Thus the marked system is exact on transporters. This proof also gives exactness after a base change whenever the markings and free bases have been base changed. Omitting the $B$'s gives the ordinary restriction-of-scalars reduction $3\mathrm{FTI}_S\le_m^p 3\mathrm{FTI}_R$.

## 3. Compile the fixed mixed system over the base ring

For completeness, the linear and dual marks used above can be linked using only a constant number of partitions in a three-mode tensor. For each underlying role $V_j$ over $R$, put a labelled copy of $V_j$ and a labelled copy of $V_j^\vee$ in each of the three output modes. Put one anchor line $Rz_i$ in mode $i$, and put $z_1\otimes z_2\otimes z_3$ in its block. Provision an additional fresh copy for each actual slot of each tensor of the system, with the appropriate variance. Place each record in its distinct block triple, using anchor vectors in unused slots. A fixed unary operator counts as a mixed tensor of order two.

For a role $V_j$, and each pair of distinct modes $i,k$, put the identity copairing
$$
 \sum_a e_a\otimes e_a^\vee
$$
on the positive copy in mode $i$ and the negative copy in mode $k$, with the anchor in the third mode. Link each fresh copy to an opposite-variance base copy in a different mode by another identity copairing. All these blocks are distinct from one another and from the data blocks. Prescribe preservation of each coordinate block. The action on an anchor is a unit $a_i$, and the anchor product forces $a_1a_2a_3=1$. Divide the action in mode $i$ by $a_i$ on every block. Because the product is one this normalization preserves all equations. The identity copairing on a positive and a negative block now says that their actions $P,Q$ satisfy $P Q^{\mathsf T}=I$. The graph connecting the three positive and three negative base copies across distinct modes is a connected six-cycle. Hence all positive copies act by one $P_j$ and all negative copies by $P_j^{-\mathsf T}$. Each fresh copy has the correct linked action too. Conversely a mixed-system transporter extends using these block actions and anchor scalars one. This recovers both implications over $R$ with ring arithmetic and inverses of invertible matrices only.

Part V, Proposition 3.6, gives the diagonal-full property for the finite local principal ideal base. Its Theorem 3.12 removes a specified partition in one mode. The proof extracts the original-coordinate corners of the other two mode maps and lifts old maps by block-diagonal extensions on the auxiliary summands. Therefore partitions in those other modes can be retained through each step by assigning each entire auxiliary summand its own additional part. In the reverse direction the extracted original corners respect the retained parts. Apply the gadget successively in each of the three modes; any already unrestricted mode may remain unrestricted in later steps. The initial and intermediate partition counts are bounded by constants because the trace system has a fixed signature. The bound of Theorem 3.12 therefore gives polynomial dimensions for all three applications. Writing the output densely has polynomial cost. This proves the upper reduction to a single free tensor pair over $R$, rather than only the marked-system restriction. The proof uses no field-only cancellation theorem. [Part V, Proposition 3.6 and Theorem 3.12](https://arxiv.org/html/2611.00735v1#S3.SS3)

## 4. A repair lemma for simultaneous natural and dual actions

Let $A$ be any commutative semilocal ring. Let $W=A^n\oplus A^n$, and in the corresponding upper and lower blocks write
$$
 G=\begin{pmatrix}T&D\\B&E\end{pmatrix}\in \mathrm{GL}_{2n}(A),\qquad
 G^{-\mathsf T}=\begin{pmatrix}U&V\\P&Q\end{pmatrix}.
$$
Suppose direct support modules $M\subseteq A^n$ satisfy $BM=0$, and dual support modules $N\subseteq (A^n)^\vee$ satisfy $PN=0$. Then there is an invertible $L\in\mathrm{GL}_n(A)$ such that
$$
 L|_M=T|_M,\qquad L^{-\mathsf T}|_N=U|_N.
$$
No freeness or splitting hypothesis on $M,N$ is required.

To prove this, seek $L=T+DCB$. Modulo any maximal ideal work in the residue field. Put $K=\ker B$ there. Invertibility of $G$ makes $\binom{T}{B}$ injective and $[T\ D]$ surjective. Thus $T$ is injective on $K$ and $\operatorname{im}T+\operatorname{im}D=A^n$ in residue coordinates. Write $W_0=(A/\mathfrak m)^n/TK$ and let $D_0$ be the image of $D$ in $W_0$. The map induced by $T$ from $(A/\mathfrak m)^n/K$ to $W_0/D_0$ is surjective. Its kernel has dimension $\dim D_0$ because $\dim W_0=\dim((A/\mathfrak m)^n/K)$. Choose a basis of this kernel and a complementary basis. Alter the images of the kernel basis in $W_0$ to the members of a basis of $D_0$, keeping the complementary images. The required changes lie in $D_0$. They can all be realized by $DCB$: $B$ is injective on the quotient by $K$, so define $C$ on the independent images of those basis vectors and extend linearly. The resulting residue map is invertible on the quotient, and remains injective on $K$. It is therefore invertible. Lift the residue choices for $C$ simultaneously by the Chinese remainder theorem across the finitely many distinct maximal ideals. Then $T+DCB$ is invertible over $A$, since its determinant is outside all maximal ideals.

The correction $DCB$ vanishes on $M$. The block identities of $G^{\mathsf T}G^{-\mathsf T}=I$ give $T^{\mathsf T}U+B^{\mathsf T}P=I$ and $D^{\mathsf T}U+E^{\mathsf T}P=0$. On $N$, these give $T^{\mathsf T}U n=n$ and $D^{\mathsf T}U n=0$. Hence $(T+DCB)^{\mathsf T}U n=n$ on $N$, which proves the second property. Over an explicitly presented local quotient the residue linear algebra also constructs $L$ from $G$ in polynomial time. A supplied factor decomposition gives the same constructive bound in the semilocal case.

## 5. Hyperbolic doubling and descent of nonfree supports

Take an original $S$-role $S^n$ and double it to $S^n\oplus S^n$ with Hermitian matrix
$$
 H_{\rm hyp}=\begin{pmatrix}0&I\\I&0\end{pmatrix}.
$$
Put each direct tensor occurrence in the first summand. Put each dual occurrence in the first dual summand of the doubled dual. A general-linear action $L$ extends to the unitary $\operatorname{diag}(L,\bar L^{-\mathsf T})$, with action $L$ on the first direct summand and $L^{-\mathsf T}$ on the first dual summand. This constructs a unitary transporter from every original transporter.

Conversely suppose a unitary $G_j$ for each role sends the doubled source tensor to the doubled target. Each mode support is the $S$-span of the coefficient vectors obtained by contracting the other two modes by basis covectors. This definition works over rings and the submodule may be nonfree. For a direct occurrence the lower projection of the transported tensor vanishes. Invert the two other mode maps and restrict the split embeddings to see that the lower-left block $B_j$ of $G_j$ kills the source mode support. For a dual occurrence the same calculation uses $G_j^{-\mathsf T}$ and its lower-left block $P_j$. Take the sum of all direct supports of role $j$ as $M_j$, and the sum of all dual supports as $N_j$. Apply the repair lemma once to that role. The repaired $L_j$ and its inverse transpose agree on the relevant supports with the two upper-left blocks of the doubled actions. Projecting the doubled tensor equation to the three upper summands gives exactly the old tensor equation with those blocks. Replacing them by the repaired $L_j$'s and $L_j^{-\mathsf T}$'s leaves the equation unchanged, as each correction vanishes on the corresponding coefficient spans. This gives the original witness even for multiple direct occurrences or a mixture of direct and contragredient occurrences of one variable.

The construction writes $2n$ basis coordinates for each role of dimension $n$ and inserts only zeros around the original tensor. It works for every finite commutative coefficient ring with an involution since such a ring is semilocal. Projection and repair prove both implications for the orbit predicate. They also give polynomial recovery of a supported source witness over a local ring with explicit residue operations. This is the lower arrow in the theorem.

## 6. Identity forms in the unramified chain-ring model

If a residue extension is non-split and quadratic, the trace to its residue base is surjective, even in characteristic two. In a split étale residue extension the sum trace is also surjective. Lift a residue element of trace one to $\eta_0\in S$; its trace is a unit in the local base and $\eta=\eta_0/\operatorname{Tr}\eta_0$ has trace one. In a hyperbolic plane with basis $e,f$, the two vectors
$$
 e+\eta f,\qquad e-\bar\eta f
$$
are an orthogonal basis of norms $1,-1$. Their basis determinant is $-\operatorname{Tr}\eta=-1$. Multiplying the second vector by an element of norm $-1$ makes the Gram matrix the identity.

For a given norm-minus-one element in the residue algebra, lifting to the full chain ring is deterministic. If the current unit $\lambda_j$ has norm $-1\bmod\pi^j$ for a maximal ideal generator $\pi$, multiply it by $1+\pi^j x$. Modulo $\pi^{j+1}$, the norm of the correction is $1+\pi^j\operatorname{Tr}(x)$ because $2j\geq j+1$. Surjectivity of residue trace solves the single additive equation for the next digit. Iterate until the nilpotence length. Each step uses residue linear arithmetic and $\pi$-adic digit operations. This is polynomial for the usual presentations of Galois rings and truncated polynomial rings.

The split residue algebra has a norm-minus-one element $(-1,1)$. A nonsplit residue extension has fields $\mathbb F_{p^a}\subset\mathbb F_{p^{2a}}$. For residue characteristic two take $1$. For odd fixed $p$ find $\mathbb F_{p^2}$ by solving $x^{p^2}=x$ over $\mathbb F_p$. If $a$ is odd its restricted norm to the residue base equals $x^{p+1}$, so enumerate the constant $p^2$ elements to find norm $-1$. If $a$ is even this subfield lies in the residue base and contains a square root of $-1$; its norm to the residue base is its square. The same enumeration finds it. This fixed-characteristic operation followed by the trace lift supplies a uniform identity-form change of basis. Direct tensor occurrences use that basis change and dual occurrences use its inverse transpose.

The same base-ring upper claim extends componentwise to a finite product of local principal ideal rings with its Chinese remainder presentation. The quadratic presentation, trace argument and fixed-signature compiler are applied in each given component. The constructions use the same input-dependent dimensions in every component, so the resulting ordinary tensor entries recombine by Chinese remaindering. A tensor isomorphism over the product is exactly a tuple of component isomorphisms.

## Scope and verification

This is a written proof of the two reductions. It uses the algebraic trace Gram mechanism from the release and no analytic zero theorem. It preserves all input tensors, including ones whose mode supports are nonfree. The proof invokes Part V only for the indicated free-module partition compiler over the local principal ideal base. The lower arrow is a polynomial many-one reduction to hyperbolic, or in the stated constructible cases standard, unitary isomorphism. The upper arrow targets ordinary tensor isomorphism over the base $R$. A same-extension-ring upper arrow for general nonreduced $S$ is a separate assertion. No priority or whole-proof Lean verification is asserted.
