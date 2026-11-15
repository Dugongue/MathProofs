# Determinant characters from singular anchored slices

Informal proof. Fix a finite field $F=\mathbb F_q$. Write a tensor as $M:U\to\operatorname{Hom}_F(X,Y)$, with transport equation
$$
 M_B(fu)=hM_A(u)g^{-1}.
$$
All determinants below use this convention. For the primal tensor convention, invert the determinants in the dual modes. We consider a prescribed determinant triple or value of a character of $(F^\times)^3$. The dense input length is $L$.

**Anchored theorem.** Supply paired lists of first-mode vectors, called anchors, and require $f$ to carry them to their counterparts. The associated slices may be rectangular, singular or zero. Form the algebra $C$ of endomorphism pairs of the source ordered anchor slices. For a simple factor $\operatorname{Mat}_{d_i}(E_i)$ of $C/\operatorname{rad}C$, say it occurs on $X$ or $Y$ if its natural simple module occurs in that mode's radical layers. Put
$$
 b=\max_i d_i,\qquad w=\max\{d_i d_j :\ i\text{ occurs on }X,\ j\text{ occurs on }Y\},
$$
using zero for empty maxima. There is a deterministic many-one reduction to one ordinary 3-tensor isomorphism instance in time polynomial in $L,2^b,2^w$. The field degrees $[E_i:F]$ enter only polynomially. In particular it is polynomial when $b,w=O(\log L)$, and for every commutative semisimple quotient, with unrestricted center degrees, trace kernels and original mode dimensions. There is also a sharper bound using computed local algebras.

**Unanchored application.** For tensors formed from direct sums of left and right singular Kronecker blocks as in Section 5, with an arbitrary subspace of added strictly upper rectangular slices, the anchors are obtained up to a constant-size list from the raw pair. The same reduction applies when the block multiplicities give logarithmic $b,w$. With one block on each side there is an oracle-free deterministic polynomial-time algorithm for the full joint determinant coset.

## 1. Ordered anchor calibration

First reject unequal format. A zero-dimensional mode makes the slice tensor zero. In this case matching anchor linear relations determines the partial first-mode map. Its determinant is fixed if the marked span is the entire mode and otherwise can take any nonzero value, by scaling an unmarked direction. The other modes have independent arbitrary determinant values when positive-dimensional, and determinant one in dimension zero. This decides the requested condition directly. For the rest assume positive dimensions. Check that the anchor lists have matching linear relations. Treat each list of slices as a representation with vertices $X,Y$ and its labeled slices as arrows. Compute by linear equations the endomorphism algebra of the direct sum of the source and target representations. Compute its radical and explicit semisimple matrix factors. The two summand idempotents must have equal ranks in every factor. When they do, find inverse corner maps in the semisimple quotient and lift them to the corresponding corners. Their products are identities modulo a nilpotent ideal, so the lifts give an isomorphism $(g_0,h_0)$. Reject if none exists. These operations over a fixed finite field are deterministic polynomial time. The same procedure will be used for a subspace inclusion with an action on its ambient space, which is also a representation by linear arrows. [Chistov–Ivanyos–Karpinski](https://doi.org/10.1145/258726.258751) · [Ivanyos–Qiao, Theorem 18](https://arxiv.org/abs/1708.03495)

Use $(g_0,h_0)$ to identify the two $X,Y$ spaces. The target slice table in these coordinates is $h_0^{-1}M_B(-)g_0$. The remaining unknown maps on $X,Y$ form a common unit $c\in C^\times$ with components $c_X,c_Y$. The known determinants of $g_0,h_0$ give the conversion to the original bases.

For $V=X,Y$, compute the filtration $(\operatorname{rad}C)^r V$. Its quotients are semisimple modules. For each matrix factor $\operatorname{Mat}_d(E)$, take an $E$-basis of the image of a first diagonal matrix unit and act on it by the first-column matrix units. Each resulting simple copy is $E^d$. Choose and order these copies to refine the radical filtration to a composition flag. Every flag term is a $C$-submodule and is preserved by $C^\times$. On each simple copy the determinant is
$$
 \nu_i(c)=N_{E_i/F}(\det_{E_i}\overline c_i),
$$
where $\overline c_i$ is the projection to the semisimple factor. The determinant on the full mode is the product of these values raised to the simple multiplicities. Radical units contribute one. This is the triangular determinant formula together with the determinant of restriction of scalars.

## 2. A filtration of the slice space over extension fields

The flag on $X$ gives a reverse annihilator flag on $X^*$. Tensor it with the flag on $Y$ to refine $H=\operatorname{Hom}_F(X,Y)=Y\otimes_F X^*$. For the $j$-th flag step of $Y$, start from $Y_{j-1}\otimes X^*$ and successively add $Y_j\otimes X^*_i$ along the dual flag. These subspaces are stable under $A\mapsto c_Y A c_X^{-1}$. Their quotients are $S_j\otimes_F S_i^*$ for simple copies $S_j,S_i$ of dimensions $d_j,d_i$ over $E_j,E_i$. The trace pairing identifies the $F$-dual of $S_i$ with its $E_i$-dual compatibly with the action.

Each quotient is a module over $E_j\otimes_F E_i=\prod_\alpha K_\alpha$, a product of finite fields by separability. Its explicit decomposition is a polynomial-time finite algebra calculation over $F$. The action commutes separately with both center actions. Split the quotient into the images of its factor idempotents and refine the flag by the preimages. Each final quotient has the form $H_t\cong K_t^{k_t}$, $k_t=d_i d_j$, since the tensor product was free of that rank over $E_j\otimes_F E_i$. The induced map $a_t$ is $K_t$-linear, with identical prescribed field actions on the calibrated source and target copies.

Pull the $H$ flag back along the two full slice maps. Each successive label quotient above the kernel embeds by the slice map as an $F$-subspace $W_{A,t}$ or $W_{B,t}$ of $H_t$. These need not be $K_t$-linear. The full transport equation ensures that $a_t$ sends $W_{A,t}$ onto $W_{B,t}$ and induces the corresponding label action.

For $T=A,B$, let $K_T=\ker M_T$, and let $K_{T,0}$ be its intersection with the span of the anchors. The paired marks determine the action on $K_{A,0}$. If $K_A=K_{A,0}$, the kernel determinant is known in adapted bases. Otherwise it can be modified arbitrarily and independently of the other two determinants. Indeed on the source fix all anchors and the quotient by $K_A$, and scale one line complementary to $K_{A,0}$ in $K_A$. A basis adapted to these intersecting subspaces produces such an automorphism, which preserves the entire slice map. For a prescribed triple omit the condition on the first determinant in this case. For a character, enumerate the constantly many triples having the prescribed value. Corresponding kernel and quotient dimensions must agree, since any transporter induces isomorphisms on them.

## 3. Read the determinant on an arbitrary label subspace

For a final block write $K=K_t$, $H=H_t$, $W=W_{A,t}$, $W'=W_{B,t}$. Compute one invertible $K$-linear map $\gamma_0:H\to H$ sending $W$ to $W'$, or reject. The algorithm of Section 1 applies to the inclusion of $W$, with the multiplication maps of a field basis of $K$ as labeled loops on $H$. The loop equations enforce $K$-linearity. If an actual transporter exists, its induced map $a_t$ qualifies.

Compute $D_t=\{v\in\operatorname{End}_{K}(H):vW\subseteq W\}$ by linear equations. Every $K$-linear map carrying $W$ isomorphically onto $W'$ has the form $\gamma_0 u$ with $u\in D_t^\times$. An invertible ambient $K$-map preserving $W$ restricts bijectively to $W$ by dimension, so its inverse is in $D_t$. For the actual $a_t$, calibrate by $\gamma_0$. Its determinant on the label quotient is the known determinant of $\gamma_0|_W:W\to W'$ times the determinant character of $\gamma_0^{-1}a_t$ on $W$.

Each factor $\operatorname{Mat}_{e}(E')$ of $D_t/\operatorname{rad}D_t$ has $e\le k_t$. Its $e$ nonzero orthogonal diagonal idempotents lift to nonzero orthogonal $K$-linear idempotents on $H$. Their images are independent nonzero $K$-subspaces. To lift an idempotent representative $x$, successively replace it by $x-(2x-1)^{-1}(x^2-x)$. All terms commute, the error moves to the square of its ideal, and the inverse exists since $(2x-1)^2$ is one modulo the nilpotent radical. Then lift the remaining idempotents in the complementary corner. The radical-layer calculation of Section 1 applied to $D_t$ on $W$ now recovers its determinant character using widths at most $k_t$.

Alternatively apply the same calculation to $H/W$. The determinant on $W$ is the ambient determinant divided by the quotient determinant, using calibrated bases in the exact sequence. The actual $a_t$ has ambient determinant over $F$ equal to
$$
 \nu_j(c)^{d_i[K:E_j]}\nu_i(c)^{-d_j[K:E_i]} .
$$
This follows by taking the two tensor-factor determinants over $K$ and then the $K/F$ norm. One can choose the direct or quotient calculation separately for every block. Only factors with nonzero total exponent modulo $q-1$ are needed. A full or zero label subspace needs no exterior for a new $D_t$-module. If $k_t=1$ and $W\ne0$, $D_t$ is a subfield of $K$, since every nonzero allowed scalar is invertible on $H$ and on $W$. Its contribution is the norm to the multiplicity $\dim_{D_t}W$.

## 4. Encode the exact character in ordinary TI

Keep the original transport equation and the paired anchor marks. Attach all indicated flags, quotient maps and inclusions. These force the induced actions on the smaller modules. To tie the $K$-action on $H_t$ to the ambient maps, attach its field multiplication table with a pointwise fixed basis and the action $K\times H_t\to H_t$. To use $\gamma_0$, take the target copies of each selected local module term as its images under $\gamma_0$ or the quotient map induced by $\gamma_0$. For any actual map $a_t$, the action corrected by $\gamma_0^{-1}$ is in $D_t^\times$, so it transports every indicated term to its copy. The original maps together with inclusions and quotient maps force these auxiliary actions. No arbitrary choice of a simple summand then restricts an actual transporter.

For each semisimple factor of an algebra used here with nonzero required exponent, use one copy of its natural simple module $E^e$ occurring in a relevant radical layer. Preserve its action as an $E$-space with $E$ fixed pointwise. Attach its exterior algebra, generated by degree one with the exterior multiplication. Choose volume coordinates on its two top lines as bases, without marking their volume vectors. The top-line scalar in these coordinates is the $E$-determinant in the calibrated simple-module bases. Impose a vector pin only on the final scalar product. Its norm can be imposed using the power $(q^{[E:F]}-1)/(q-1)$. In detail, use a chain of one-dimensional $E$-spaces whose multiplication tensors multiply their map scalars and whose coordinates are identified through a prescribed product of basis vectors. Repeated squaring and binary powering use $O([E:F]\log q)$ lines and compute exactly the norm scalar, which belongs to $F^\times$. Attach the $F$-subline spanned by the final volume coordinate. Combine such lines by multiplication, use dual lines for inverse powers, and put a final vector mark with the requested scalar after the fixed frame and calibration factors. The same construction works for separate determinants or for one product character. Every genuine transporter with the requested determinants extends to the auxiliary system by its induced maps. Every auxiliary isomorphism gives a genuine transporter satisfying the same determinant equations.

Use a fixed signature even when the number of flag terms, fields, quotients and lines varies. An ordered coordinate algebra $F^I$ supplies primitive idempotents indexing the components. Fix a first idempotent and consecutive shift, so the labels are fixed pointwise. Combine spaces of each role in direct sums with the corresponding idempotent projections. Combine inclusions, quotient maps, multiplications and norm steps in separate block maps by their roles, using incidence labels and copies tied by identity maps when a space occurs more than once. Every local condition is linear or bilinear, except the original trilinear tensor. The label algebra action forces each block equation separately. Dual pairings tie input sorts to the appropriate primal sorts. Apply the fixed-component tensor-system compiler. If disjunction is needed, encode ordered pairs of isomorphism types by named component sides and unordered pairs by freely permuted component labels. The equality
$\{(a,c),(b,d)\}=\{(a,d),(b,c)\}$ of multisets expresses $a=b$ or $c=d$. A constant number of such operations packs the branch queries over the same field. [Chen–Grochow–Qiao–Tang–Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2)

The number and base-field dimensions of filtration terms, field decompositions, linear systems and algebra tables are polynomial in $L$. For a simple factor $\operatorname{Mat}_e(E)$, the only dimension exponential in $e$ is the exterior algebra of base-field dimension $[E:F]2^e$. Thus the complexity is polynomial in $L,2^b,2^w$. A sharper bound uses just the widths of factors with nonzero exponents in the chosen direct or quotient route. In particular arbitrary field degrees and large trace kernels can coexist with polynomial cost.

## 5. A raw class of everywhere-singular tensors

For each integer $m\ge1$, the right singular pair $R_m$ consists of the two shifted projections $F^{m+1}\to F^m$. For each $\ell\ge1$, the left singular pair $L_\ell$ consists of the transposes of the two shifted projections $F^{\ell+1}\to F^\ell$. Take any nonempty direct sums $R,L$ of these right and left pairs. Denote their vertex spaces by $X_R,Y_R,X_L,Y_L$, with $X=X_R\oplus X_L$ and $Y=Y_R\oplus Y_L$. Let $W$ be an arbitrary $F$-subspace of $\operatorname{Hom}_F(X_L,Y_R)$. Consider the tensors ordinarily equivalent to a slice map of the form
$$
 M(a,b,w)=
 \begin{pmatrix}
  R(a,b)&w\\
  0&L(a,b)
 \end{pmatrix},\qquad (a,b,w)\in F^2\oplus W .
$$
There are no supplied bases, Kronecker blocks, or chosen first-mode vectors. The label slice map is injective, and the combined slices have zero common kernel and images spanning $Y$. For square $X,Y$, every slice is singular even over the algebraic closure. In fact every nonzero $(a,b)$ gives an onto $R(a,b)$ and an injective $L(a,b)$, so the rank is $\dim Y_R+\dim X_L$, strictly less than $\dim X$ and $\dim Y$. At $(a,b)=0$ the rank is at most $\min(\dim Y_R,\dim X_L)$.

Thus $W$ is canonically the set of label vectors whose slice rank is less than the maximum. Compute the maximum by testing the coordinate basis, which contains a vector outside $W$. Then scan all label vectors of coordinate support at most three and collect those below the maximum rank. They span $W$. For this, take two coordinate basis vectors whose images give a basis of the quotient by $W$, and subtract combinations of them from each remaining coordinate vector to obtain a basis of $W$ of support at most three. This is a deterministic polynomial computation since $F$ is fixed. Any ordinary transporter sends this computed $W$ onto its counterpart. On each side choose any two anchors lifting a basis of the quotient. Enumerate the constant group $\operatorname{GL}_2(F)$ for the induced quotient action on a pair. Only the source needs the promise. On the target require equal format, an injective slice map, and a computed low-rank span of codimension two. A target equivalent to the source always passes these checks and inherits the promise. A nonpromised target passing these checks cannot give a false positive because the compiled branch retains the original tensor. In the oracle-free case below an accepted branch directly constructs an actual transporter.

Every two choices of lifts of the same quotient basis are related by an automorphism with all three determinants one. To obtain it, use upper-block shears on $X$ and $Y$ with off-diagonal entries $G:X_L\to X_R$ and $H:Y_L\to Y_R$. Their effect is to send $(a,b,w)$ to
$$
 (a,b,w+H L(a,b)-R(a,b)G).
$$
The map from $(G,H)$ to the two shifts at the standard quotient basis is onto the square of $\operatorname{Hom}(X_L,Y_R)$. It suffices to check each right-left pair of blocks. For $R_m,L_\ell$ one must solve, in zero-based indices $0\le i<m$, $0\le j<\ell$,
$$
 H_{ij}-G_{ij}=A_{ij},\qquad H_{i,j+1}-G_{i+1,j}=B_{ij}.
$$
Choose the first row of $G$ and the last column in its other rows freely. The equations
$G_{i+1,j}=G_{i,j+1}+A_{i,j+1}-B_{ij}$ for $j<\ell-1$ determine the remaining entries of each next row. The first equations now give the first $\ell$ columns of $H$, and the second equations at $j=\ell-1$ give its last column. Because a quotient basis change is invertible, arbitrary shifts in $W$ can be produced at the chosen quotient basis as well. They keep the label action a shear into $W$. All three maps are unipotent. Given any raw transporter with one of the enumerated quotient actions, compose it with the target shear carrying its anchor images to the chosen lifts. This preserves all determinants. Conversely every anchored match is a raw match. Therefore this constant disjunction implements exactly the raw determinant test.

For clarity, the simple sizes of the anchor endomorphism algebra are precisely the multiplicities of the various right and left Kronecker blocks. Here is one verification. Each single $R_m$ has endomorphisms only the common scalar. At the two slices, respectively the first $m$ and last $m$ rows of its $X$-map are of the form $[Q,0]$ and $[0,Q]$ for its $Y$-map $Q$. The overlap makes $Q$ constant along each diagonal and zeros every off-diagonal by the boundary. Transposing proves the assertion for $L_\ell$. These blocks are indecomposable and nonisomorphic across different types or sizes. For a finite direct sum of indecomposables the semisimple quotient of its endomorphism algebra is the product over the repeated isomorphism types of matrix algebras over their endomorphism residue fields. In this case all those fields are $F$. To see the radical formula, project the endomorphism ring to its blocks between copies of the same type. Composition through a distinct indecomposable vanishes on these projections, since a nonzero resulting scalar would make one a direct summand of the other. The kernel consists of cross-type block entries. A sufficiently long product repeats a type along each path of nonzero entries, giving a zero composite by the same splitting argument. This makes the kernel nilpotent and proves the formula. Thus bounded or suitably logarithmic multiplicities give the stated polynomial reduction. Any invertible change of the two anchor slices leaves their common endomorphism algebra unchanged.

For one $R_m$ and one $L_\ell$, there is a direct algorithm with no TI oracle. There are no morphisms $R_m\to L_\ell$. For a proposed such morphism with vertex maps $P,Q$, the two arrow equations give $[Q,0]=[P;0]$ and $[0,Q]=[0;P]$. They force the boundary entries of $Q$ to vanish and give $Q_{ij}=Q_{i+1,j-1}$ where both entries occur. Each entry propagates to a zero first column or last row. Hence the calibrated anchor algebra is upper block triangular with scalar diagonals. Write those diagonal values $r,s\in F^\times$. An anchor automorphism acts on the entire upper slice block by the scalar $r/s$, independent of its upper entries. After each anchor-only calibration $(g_0,h_0)$, test whether $h_0 W_A g_0^{-1}=W_B$ as slice subspaces. If it fails, the branch is impossible. If it holds, define $f_0$ on $W_A$ by this correspondence and on the two chosen anchor vectors by the branch marks. The exact determinant triples in this branch are
$$
 \left(\det(f_0)(r/s)^{\dim W},\
 \det(g_0)r^{m+1}s^{\ell},\
 \det(h_0)r^m s^{\ell+1}\right)
 \quad (r,s\in F^\times).
$$
The triangular matrices with those diagonal scalars and zero upper entries already realize every displayed triple. Conversely every anchored transporter has that determinant triple by the block action on $W$. Values $m,\ell$ used in the formula are computable as the block dimensions via the primitive factors of the anchor algebra, or by finding the ordered Kronecker type with the two dimensions. For the latter, try all polynomially many pairs $(m,\ell)$ with $m+\ell+1=\dim X=\dim Y$ using the exact constructive module isomorphism with the explicit $R_m\oplus L_\ell$ anchor pair. Changes of basis in the two arrows preserve each $R_m,L_\ell$ class, since their linear pencil families are dual to multiplication by linear forms on consecutive homogeneous binary polynomial degrees. This gives exact calibrations in standard coordinates. Union over the constant number of quotient matches gives the raw determinant coset.

This family also separates the filtration method from reverse-composition traces. On the two-block family, a map $P:Y\to X$ intertwining the two $C$-actions preserves the two diagonal idempotents. Thus every $P M(w)$ for $w\in W$ is strictly upper block triangular, while every $P M(u)$ is upper block triangular. Any product involving the former and all other such matrices remains strictly upper, and has trace zero. In particular the joint trace functionals and the alternating forms obtained from commutators of reverse compositions all vanish on $W$ in each argument. The label subspace $W$ can have dimension $m\ell$, while the anchored reduction above uses width one.

## 6. Transfer arbitrary concise tensors to singular pencils with two fixed anchors

For $q>2$, every fixed determinant character on an arbitrary tensor with injective slice map reduces to a determinant character on an everywhere-rank-deficient tensor of Section 5, with the two ordered anchors marked. Use $m,\ell\ge1$ with $m+\ell+1$ coprime to $q-1$. For example, take $m=1,\ell=q-2$. For $q=2$ the character is trivial and any positive lengths work. Write $M_0:U_0\to\operatorname{Hom}_F(X_0,Y_0)$ for either original tensor. Repeat $R_m$ with multiplicity $\dim Y_0$ and $L_\ell$ with multiplicity $\dim X_0$. Fix any nonzero linear map $B:F^\ell\to F^m$, and use the slice
$$
 \widehat M(a,b,u)=
 \begin{pmatrix}
 I_{Y_0}\otimes R_m(a,b)&M_0(u)\otimes B\\
 0&I_{X_0}\otimes L_\ell(a,b)
 \end{pmatrix}.
$$
The marks are the two ordered coordinate anchors from $F^2$. All mode dimensions are linear in the original dimensions at fixed $q$. The two matrix modes are square when $\dim X_0=\dim Y_0$.

There are no arrows from the right isotype to the left isotype in the anchor endomorphism algebra, by the boundary calculation of Section 5. On its two diagonal blocks the endomorphisms are arbitrary matrices on the multiplicity spaces tensored with the identity on the respective Kronecker block, since each block's endomorphisms are scalars. Thus every remaining pair of matrix transporters has arbitrary invertible multiplicity maps $g:X_0\to X'_0$, $h:Y_0\to Y'_0$, with arbitrary allowed upper blocks. The upper blocks act trivially on the upper rectangular slices. Acting on $M_0(u)\otimes B$ therefore gives $(hM_0(u)g^{-1})\otimes B$. The resulting label map on $U_0$ is exactly an original slice transporter, since $B\ne0$ and the slice maps are injective. Conversely, every original transporter lifts by its multiplicity-space actions with upper blocks zero and by the given label map fixing the two anchors.

In the new naturally ordered bases the joint determinant triple is exactly
$$
 (d_U,\ d_Y^{m+1}d_X^\ell,\ d_Y^{m}d_X^{\ell+1}),
 \qquad
 (d_U,d_X,d_Y)=(\det f,\det g,\det h).
$$
This follows from the multiplicities of the identity factors on the two matrix modes, and the fixed two-dimensional label quotient. The exponent matrix on $(d_Y,d_X)$ has determinant $m+\ell+1$, so it is invertible modulo $q-1$. Translate the requested character using its inverse modulo $q-1$. This gives a determinant-preserving character reduction with no queries. In particular high multiplicities of just these two singular isotypes suffice to encode the general concise input; the polynomial-width theorem above applies when the multiplicity-dependent or individual local width bounds hold.

The anchored theorem and the raw singular family are sufficient determinant terminals under their stated hypotheses. A polynomial bound on the relevant simple dimensions, or polynomial-size unanchored selection of such packets, is still unproved for arbitrary tensors. All arguments are informal. Publication priority is unestablished.
