# Reducing even special-group isomorphism to ordinary tensor isomorphism

Work over $F=\mathbb F_3$ with special groups of class two and exponent three given by compact commutator coordinates. An input is an alternating bilinear map $\beta:X\times X\to Z$ whose image spans $Z$ and whose common radical is zero. Write $L\ge2$ for the joint dense input length, $n=\dim X$, and $z=\dim Z$. The group law on $X\oplus Z$ is
$$
 (x,a)(y,b)=(x+y,a+b+\tfrac12\beta(x,y)).
$$
Ordinary group isomorphisms induce precisely the bracket transporters $h\beta(x,y)=\beta'(gx,gy)$, and every such transporter lifts. The additive determinant is $\det g\,\det h$, since the ancillary central shear contributes determinant one. Over $F$ it is also the permutation sign on the group elements ordered by their additive coordinates. To see this, use the intrinsic Baer addition $u+v=uv[u,v]^{-1/2}$. A transvection is an even permutation of the vectors. Negating one coordinate exchanges $3^{\dim(X\oplus Z)-1}$ pairs, and transvections together with coordinate negations generate the general linear group. [Baer, Groups with Abelian Central Quotient Group](https://doi.org/10.1090/S0002-9947-1938-1501972-1)

## Polynomial many-one cases

There is a deterministic polynomial-time many-one reduction from even isomorphism to ordinary three-tensor isomorphism over $F$ on each of the following recognizable domains. Constants in the bounds are fixed.

1. The dimension $n$ is odd.
2. The kernel $K=\ker(\Lambda^2X\to Z)$ has dimension $O(\log L)$.
3. The center has dimension $z=O(\log L)$, and some scalar form $\lambda\beta$, $\lambda\in Z^*$, has radical of dimension $O(\log L)$.
4. The center has dimension $O(\log L)$, and for some fixed positive even number $s$ there are covectors $\lambda_1,\ldots,\lambda_s\in Z^*$ such that the sum map
   $$
    \Sigma:\bigoplus_{i=1}^s R_i\longrightarrow X,\qquad
    R_i=\operatorname{rad}(\lambda_i\beta)
   $$
   has both kernel and cokernel of dimension $O(\log L)$. Individual $R_i$ may be arbitrarily large.

The same reductions give ordinary isomorphism instances of compact special groups. Reject mismatched quotient and central dimensions before any construction. The algebraic equalities below use the same transporter $g,h$ in every condition.

### Kernel of the commutator

If $n$ is odd, $(-I_X,I_Z)$ is a bracket automorphism of determinant $-1$. It corrects any ordinary isomorphism. Otherwise let $g_K$ be the restriction of $\Lambda^2g$ to $K$, taking values in the kernel $K'$ of the target bracket. Choose bases on $K,K'$ and append lifts under the bracket maps of the raw bases of $Z,Z'$. Let $\kappa$ be the ratio of the target frame determinant to the source frame determinant in the exterior-square coordinates. The exact sequence gives
$$
 (\det g)^{n-1}=\det(\Lambda^2g)=\kappa\,\det(g_K)\det h .
$$
It follows that for even $n$ the required condition is $\det(g_K)=\kappa^{-1}$, which equals $\kappa$ in $F^\times$. Include the wedge map $X\times X\to\Lambda^2X$, the map from the wedge space to $Z$, and the inclusion of $K$ in one typed tensor system. The wedge map has spanning image, so it forces precisely $\Lambda^2g$. The exterior algebra of $K$ and the top-volume mark impose the displayed determinant condition. Its dimension is $2^{\dim K}$, polynomial under the stated bound.

### Scalar forms and sums of radicals

If $z=O(\log L)$, one can enumerate all covectors, or all ordered $s$-tuples for fixed $s$, in polynomial time. Find one qualifying source tuple if it exists. Try all target tuples, requiring the branch equations $\lambda_i' h=\lambda_i$. Keep the original bracket in each branch. These linear marks force $g$ to be an isometry between the scalar forms $\lambda_i\beta,\lambda_i'\beta'$. Accordingly it induces $g_i:R_i\to R_i'$. In chosen ordered bases on the radicals, append lifts of symplectic bases of the quotient $X/R_i$ and of $X'/R_i'$. Let $\kappa_i$ be the corresponding frame ratio. The quotient isometry is symplectic, of determinant one. Characteristic three causes no problem with the standard Pfaffian identity $\operatorname{Pf}(A^{\mathsf T}BA)=\det(A)\operatorname{Pf}(B)$; it is an integer polynomial identity. Thus
$$
 \det g=\kappa_i\det g_i .
\tag{1}
$$
For one small radical this reads $\det g\det h$ as $\kappa_i$ times the determinant on $R_i\oplus Z$, giving case 3.

More generally let $D=\ker\Sigma,\ Q=\operatorname{coker}\Sigma$. The determinant formula in the exact sequence
$$
 0\longrightarrow D\longrightarrow\bigoplus_iR_i
   \xrightarrow{\ \Sigma\ }X\longrightarrow Q\longrightarrow0
$$
gives
$$
 \det g=c_0\left(\prod_i\det g_i\right)
             \frac{\det(g_Q)}{\det(g_D)}
$$
with a computable frame ratio $c_0$. One way to calculate it is to first split the sequence into two short exact sequences at $\operatorname{im}\Sigma$, compute the target-to-source frame ratio in each, and divide the ratio for $X$ by that for $\bigoplus_iR_i$. For even $s$, the product of the determinants in (1) is $\prod_i\kappa_i^{-1}$ because $(\det g)^s=1$. Hence
$$
 \det g\det h
 =\frac{c_0}{\prod_i\kappa_i}
      \det(g_D)\det(g_Q)\det h .
\tag{2}
$$
The inverse on $\det(g_D)$ has disappeared because its value is a sign. Keep the scalar-form marks and the inclusions and quotient maps of the exact sequence in the same tensor system as $\beta$. In particular the system uses the actual sum map of the included $R_i$, and keeps the kernel and cokernel as those of that map. This forces all the actions in (2). A volume mark on $D\oplus Q\oplus Z$ enforces precisely the required sign. Discard a branch with incompatible dimensions before making the ordinary query.

For an example separating the two scalar-form cases, take $Z=F^2$ and $X$ a sum of four symplectic spaces of dimension $2r$, one for each projective line of $Z$. Value the form on each block in its corresponding output line, with cross brackets zero. Every nonzero scalar form has a radical of dimension $2r$, since the covector vanishes on exactly one of the four lines. Choose four covectors with those four distinct kernels. Their radicals are complementary and span $X$, so $D=Q=0$ in (2). This gives unbounded individual coranks and a kernel $K$ of quadratic dimension.

### Compilation and branch combination

On any small marked space $Y$, include the entire exterior algebra $\bigwedge Y$ as one sort, with its multiplication and the inclusion of $Y$. The algebra is generated by $Y$, so its induced map is forced on every grade. Put the nonzero volume vector in the source and the desired scalar times the volume vector in the target. This enforces exactly the scalar on the top line and uses a constant number of tensor marks of arity at most three. Any compatible original $g,h$ extends to the marked spaces by the induced maps. Conversely each system isomorphism satisfies the displayed equality for its own $g,h$. The fixed-signature tensor-system compiler outputs an ordinary three-tensor instance for a branch. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

Polynomially many possible branches can be joined by ordinary TI OR. Here is an explicit reason for the required linear side growth. Encode a positive-format bimap $T$ as a three-vertex upper triangular unital algebra $A_j(T)$ with its three sides in the directed corners and multiplication $T$ between the two consecutive corners. Put $F[t]/(t^j)$ at each vertex and let its positive powers kill the off-diagonal corners. The radical has nilpotent diagonal part and the quotient is $F^3$. An algebra isomorphism aligns radical lifts of the diagonal idempotents by conjugation, then the nonzero directed corners distinguish the vertices. The remaining conditions on the corners are exactly TI. The center is local, since a central idempotent is diagonal and its entries must agree on every incident corner. The dimension is $3j$ plus the three side lengths. For $j=2,3$, the diagonal corner dimensions distinguish the two types irrespective of the tensor formats. Encode an ordered pair as the product $A_2(T)\times A_3(S)$. An outer copy of the triangular construction applied to its multiplication tensor gives a centrally indecomposable algebra $C(T,S)$ with the same ordered-pair comparison. Multiplication-tensor isotopy of unital associative algebras is equivalent to algebra isomorphism by normalizing the images of the unit. Compare
$$
 C(T_0,S_0)\times C(T_1,S_1)
 \quad\hbox{and}\quad
 C(T_0,S_1)\times C(T_1,S_0).
$$
The straight matching requires $S_0\simeq S_1$, and the crossed matching requires $T_0\simeq T_1$. Convert their multiplication tables back to tensors. The side length grows by only a constant per binary gate, and a balanced OR tree has logarithmic depth. Ordinary inputs with zero side lengths can be replaced by fixed answer instances.

To produce compact special-group instances instead of ordinary TI, apply the ordinary TI reduction to alternating matrix-space isometry. Quotient the common radical of the alternating forms and use an independent basis of their span as the coordinate space of the bracket. Record and compare common radical dimensions before quotienting. An isometry induces one on the quotient, and every quotient isometry extends arbitrarily on radical complements. The remaining bracket has spanning image and zero common radical, so Baer's group construction gives compact special groups in the stated format. Degenerate cases with zero bracket can be settled directly. [Grochow and Qiao, Tensor Isomorphism-Completeness, Corollary 5.2](https://doi.org/10.1137/21M1441110)

## Probes over auxiliary finite fields

The single-probe test also works when a combination of a fixed number $b$ of central covectors has small radical after scalar extension to a finite extension $E/F$. The same applies to an even number of probes defined using a fixed total number of central covectors. On $X\otimes_F E$ all determinant calibrations and symplectic quotient bases can be taken over $E$. The determinant of $g\otimes1$ lies in $F^\times$, so its even power in (2) remains one. Keep the inverse determinant on $D$ in the exact-sequence calculation, since the determinant on that extension space need not be a sign. Use the dual of $D$, linked by its evaluation pairing, when forming the volume. Use exterior powers over $E$ on the small spaces, and extend the action on $Z$ to $Z\otimes_F E$ to combine determinants over $E$. The scalar extension maps are forced by the $F$-bilinear maps $(x,e)\mapsto x\otimes e$. The field action is fixed by its multiplication and a marked field generator, and the determinant and orientation checks take place in $E$, with the specified final scalar there.

In the single-probe case one can find such a witness with no supplied extension if the required high rank occurs over an algebraic closure in the span of $b$ covectors for fixed $b$. A nonzero rank minor has degree at most $n$. Take $E$ of size greater than $n$, and search the full $E^b$ grid. A nonzero polynomial of degree at most $n$ in each variable cannot vanish throughout this grid. Choose the least extension degree with size greater than $n$; an explicit field can be constructed by enumerating degree-$[E:F]$ monic polynomials and testing irreducibility. Both searches are polynomial for fixed $b$. Find a source span by enumerating its constituent $F$-covectors, then branch only over their target images and use the same chosen coefficients in $E$. This gives a polynomial many-one test within the logarithmic-center and logarithmic-radical bounds.

## All logarithmic centers by polynomial ordinary-TI oracle calls

The following independent procedure removes the probe condition at the expense of a polynomial-time Turing reduction. It also gives a deterministic polynomial-time decision algorithm when $z=O(\sqrt{\log L})$.

First compute the determinant image of the center-fixed bracket automorphisms. Form the adjoint algebra
$$
 \mathcal A=\{(a,b):\beta(ax,y)=\beta(x,by)\text{ for all }x,y\}
$$
with product $(a,b)(a',b')=(aa',b'b)$ and involution $(a,b)^*=(b,a)$. The alternating identity ensures that the involution preserves this algebra. Its unitary group projects bijectively onto the center-fixed isometry group, since a unitary element is $(g,g^{-1})$. Apply the finite-field semisimple quotient algorithm to the faithful matrix representation $(a,b)\mapsto\operatorname{diag}(a,b^{\mathsf T})$. Let $J$ be its radical. The subgroup $1+J$ has determinant one on $X$. Every quotient unitary lifts: for a unit lift $u$ let $v=u^*u\in1+J$. Choose $3^k$ at least the nilpotence index and $j$ with $2j\equiv-1\bmod3^k$. Then $v^{3^k}=1$, and $uv^j$ is unitary with the same image in the quotient.

For each simple component $M_d(E)$, let $\mu$ be the multiplicity of its natural simple on the $J$-grades of $X$ under the first projection. The first-projection determinant on that component is $N_{E/F}(\det)^\mu$. The exact unitary determinant image is therefore obtained by the following tests.

- A pair of exchanged components contributes an odd determinant exactly when the sum of the two multiplicities is odd. The second component is determined by the inverse adjoint of the first, and their norms are inverse.
- A fixed orthogonal component contributes an odd determinant exactly when $[E:F]\mu$ is odd. Its group has both determinants over $E$.
- A fixed symplectic or unitary component contributes determinant one. The symplectic determinant is one over $E$, and the unitary determinant has norm one down to the involution's fixed field and hence to $F$.

The semisimple factors, involution types, and multiplicities are computable by the standard finite-field algebra algorithms at fixed characteristic. Thus no oracle is needed for this kernel image. If an odd center-fixed automorphism exists, ordinary isomorphism suffices, with no bound on the center dimension. For a fixed candidate central map $h$, comparing ordered tuples of alternating forms computes one actual $g$ by the deterministic fixed-characteristic specialization of simultaneous form isometry. [Ivanyos and Qiao, Theorems 7 and 18 and Proposition 23](https://arxiv.org/html/1708.03495)

With an ordinary TI oracle, a marked bracket diagram decides whether a list of prescribed central basis-vector images extends to an isomorphism. For a list of length $b$, include one coordinate algebra $F^b$ with its unary shift sending each primitive idempotent to its successor and the last to zero. The shift forces its identity action. One linear map from $F^b$ to $Z$ sends its ordered idempotents to the pinned source vectors, and the corresponding target map sends them to their prescribed images. This packs all pins into a fixed number of tensor maps. For $z=O(\log L)$, every central vector has at most $3^z$ candidate images. Greedy pinning produces one relative central map $h_0$, or proves ordinary nonisomorphism. On the target itself, use the ordered central basis as a stabilizer chain. For every possible image of its next vector under the stabilizer of all earlier ones, use the oracle and greedy completion to obtain a full central map. The resulting maps generate the central permutation image, because the lifts at a position are a transversal for the next point stabilizer. Use ordered-form isometry to lift each completed central map and $h_0$ to $g$. The total determinant image of target automorphisms is generated by the lifted images together with the computed sign image of center-fixed automorphisms. Indeed every automorphism can be multiplied by inverses of the chosen lifts until its central map is the identity. The reference relative determinant from $h_0$ specifies the full relative sign coset. Decide whether it contains $1$. The oracle count is at most a polynomial in $z$ and $3^z$.

When $z=O(\sqrt{\log L})$, simply enumerate the at most $3^{z^2}$ invertible central matrices, compare ordered tuples for each, and recover its exact sign coset by the already computed center-fixed subgroup. This is a deterministic polynomial-time decision without TI calls.

## Scope

The many-one conditions are sufficient and can be recognized in the compact input model. The oracle procedure for all logarithmic centers has polynomially many adaptive calls. The proofs make no assumption about unrestricted even isomorphism. The determinant identities and their tensor encodings are informal mathematical proofs. Publication priority for these refinements is unverified.

Finite controls checked 350 exterior-square determinants, 370 determinant calibrations for even radical sums using independently chosen source and target frames, and 32 scalar-form counts in the four-line example. All passed.
