# Cubic degenerations reduce to ordinary tensor degenerations

Fix an algebraically closed field $k$ of arbitrary characteristic. A point $y$ is a degeneration of $x$ for an algebraic group $G$ if $y\in\overline{Gx}$ in the Zariski topology.

**Theorem.** For each $n\ge1$ there is an explicit affine-linear map $\Phi$ from formal homogeneous cubics in $n$ variables to three-tensors with side lengths $O(n^2)$ such that
$$
g\in\overline{\operatorname{GL}_n(k) f}
\quad\Longleftrightarrow\quad
\Phi(g)\in\overline{(\operatorname{GL}\times\operatorname{GL}\times\operatorname{GL})\Phi(f)} .
\tag{1}
$$
The three tensor group factors are independent. In characteristic three this retains directional degeneration information carried by pure cubes, even for inputs with identical complete polarization.

The main geometric step works for arbitrary partitioned tensors. Its dimensions are polynomial even when the number of parts grows, and linear in the original lengths for a fixed number of parts. The proof uses products of linear factors of maximal minors to recover all added slice coordinates simultaneously along a degeneration.

## 1. Reflection at the partitioned stage

Let $V=k^n$ and let $M=\operatorname{Alt}^2(V,k)$, the space of alternating bilinear forms. Choose a linear lift $f\mapsto t_f$ from cubics to trilinear forms with $t_f(x,x,x)=f(x)$. For example, assign each cubic coefficient to a single ordered triple. The kernel of this diagonal map consists of the trilinear forms
$$
a(x)(y,z)+b(y)(x,z),\qquad a,b\in\operatorname{Hom}(V,M).
\tag{2}
$$
In each group of tensor coefficient positions with the same unordered multiset of indices, a diagonal coefficient is the sum of the entries. A zero sum is a sum of pair differences, and each such difference is a sum of differences across the transpositions $(2\,3)$ and $(1\,3)$. These differences are alternating in their respective pair. Conversely both terms in (2) vanish on the formal diagonal.

Put $U=V\oplus M$ and $W=V\oplus M$, with projections $\pi_U,\pi_W$ to $V$. Let $A,B$ be copies of $V^*$ and $L_1,L_2,L_3$ copies of $k$. Use the three partitioned argument spaces
$$
U\oplus A\oplus L_1,\qquad W\oplus B\oplus L_2,\qquad V\oplus L_3 .
$$
The tensor $K_f$ has the following six specified blocks, with all other blocks zero.
$$
\begin{array}{c|l}
(U,W,V)&t_f(x,y,z)+m(y,z)+l(x,z),\quad (x,m)\in U,\ (y,l)\in W\\
(U,B,L_3)&c\,\eta(\pi_U u)\\
(L_1,B,V)&s\,\eta(z)\\
(A,W,L_3)&c\,\xi(\pi_W w)\\
(A,L_2,V)&r\,\xi(z)\\
(L_1,L_2,L_3)&s r c .
\end{array}
$$
Here $\eta\in B,\xi\in A,s\in L_1,r\in L_2,c\in L_3$. For an invertible $h:V\to V$ and a form $g=f\circ h$, decompose $t_g(x,y,z)-t_f(hx,hy,hz)$ as in (2). On $U,W$ use the substitutions
$$
(x,m)\longmapsto(hx,h_*(m+a(x))),\qquad
(y,l)\longmapsto(hy,h_*(l+b(y))),
$$
where $(h_*m)(hv,hw)=m(v,w)$. Use $h$ on the third $V$, its inverse dual on $A,B$, and identities on the lines. Substitution into $K_f$ gives $K_g$. Thus regularity of $f\mapsto K_f$ proves the forward degeneration implication.

For reflection, there is a regular cubic readout near every encoded tensor. Given a tensor $T$ on the same partitioned spaces, use the fixed bases on the lines and the perfect dual pairings. Write $D_U:U\to V$ for its $(U,B,L_3)$ block and $E_U:V\to V$ for its $(L_1,B,V)$ block. Define $D_W,E_W$ using the two analogous blocks with $A$. Write $\gamma$ for the $(L_1,L_2,L_3)$ entry. On the open set where $E_U,E_W,\gamma$ are invertible and $p_U=E_U^{-1}D_U$, $p_W=E_W^{-1}D_W$ restrict invertibly to the fixed $V$ summands, let $i_U,i_W$ be the right inverses of $p_U,p_W$ landing in those summands. The regular readout is
$$
\mathcal R(T)(x)=\gamma^{-1}T_{U,W,V}(i_U x,i_W x,x).
\tag{3}
$$
Every $K_g$ belongs to this open set and $\mathcal R(K_g)=g$.

On the partition-preserving orbit of $K_f$, write $P,Q,S$ for the argument substitutions on $U,W,V$ and $\alpha_i$ for the three line substitutions. The evaluation blocks give
$$
p_U=(\alpha_3/\alpha_1)S^{-1}\pi_U P,\qquad
p_W=(\alpha_3/\alpha_2)S^{-1}\pi_W Q,\qquad
\gamma=\alpha_1\alpha_2\alpha_3.
$$
The alternating terms in the readout vanish because their two evaluating arguments are proportional to $Sx$. The main trilinear term and the factor $\gamma^{-1}$ give precisely $f(\alpha_3^{-1}Sx)$. Thus the readout sends the orbit points in its domain into the cubic orbit of $f$. Regularity on the open neighborhood of $K_g$ proves reflection for partition-preserving degeneration.

The partition sizes are $(3,3,2)$ and the total lengths before removing them are $2n+\binom n2+1$, $2n+\binom n2+1$, and $n+1$.

## 2. Removing a partition preserves and reflects degeneration

Use coefficient arrays, so a tensor is a family of matrices indexed linearly by a third-axis covector. Let $X=X_1\oplus\cdots\oplus X_a$, $Y$, and $Z$ be the axis spaces of ranks $p,m,\ell$. Other specified partitions on $Y,Z$ are allowed. For $a=1$ there is nothing to remove. For $a\ge2$ use two added slices for each $X_i$, with indices $j=1,\ldots,2a$ and part assignment $i(j)$. Put
$$
r_j=j.
$$
For each $j$ add private row spaces $Y_j,I_j$ and private column spaces $X'_j,J_j$, of respective ranks $m,r_j,\dim X_{i(j)},r_j$. The added slice $D_j$ has identity rectangles $(Y_j,Y)$, $(X_{i(j)},X'_j)$, and $(I_j,J_j)$, with zeros elsewhere. Embed each original slice in the $X,Y$ rectangle. The first axis of the resulting tensor is unpartitioned, and place all additions on each of the other axes inside its last existing part. Write $\mathcal D$ for this construction.

A partition-preserving change of the original axes extends to a change of the enlarged axes that fixes all added slices. Use inverse-transpose changes on $Y_j,X'_j$ for their paired spaces and identities on $I_j,J_j$ and the added third-axis coordinates. This proves the forward implication for orbits and, by regularity of $\mathcal D$, for their closures.

### Track all added slice coordinates by maximal minors

Write $A(z)$ for the old data combination. A contraction of $\mathcal D(A)$ has the form
$$
A(z)+\sum_j b_jD_j .
$$
Set $q=p+m+\sum_j r_j$. After deleting the private identity rectangles, support lies in the union of rows $X$ and columns $Y$, so the remaining rank is at most $p+m$ for all choices of $z,b$. Each $q$-minor, as a polynomial in $z,b$, is divisible by
$$
\prod_j b_j^{r_j}.
\tag{4}
$$
Indeed, a minor that omits a row or column of a private identity rectangle vanishes, since the available rank is then at most $q-1$. A minor retaining the private rows and columns factors by their determinants. There is a $q$-minor equal up to sign to
$$
\prod_j b_j^{r_j+c_j},\qquad c_j\ge0,\qquad \sum_j c_j=p+m .
\tag{5}
$$
Choose all private rows and columns, all old rows $X$ and columns $Y$, one copy $X'_j$ per old part, and one row copy $Y_j$. Ordering the latter rows and columns to align the identity rectangles leaves only a possible off-diagonal data block, so the determinant has the displayed monomial form. In particular the contraction pencil has maximal rank exactly $q$. For each fixed $j$, the chosen old column copy for its part can be its twin, and the chosen row copy of $Y$ can be taken from a different tag. This yields a monomial minor with $c_j=0$. The greatest common divisor of all nonzero $q$-minors is therefore exactly $\prod_j b_j^{r_j}$ up to a nonzero scalar. Indeed every such minor is divisible by this product, and the selected monomial minors admit no other common factors or greater common powers.

Suppose $\mathcal D(B)$ is in the orbit closure of $\mathcal D(A)$ for the remaining allowed partitions. Work over a discrete valuation ring $\mathcal O$ with residue field $k$ and fraction field $K$, with an enlarged tensor family specializing to $\mathcal D(B)$ and generically equal to $(P,Q,L)\mathcal D(A)$ for allowed invertible matrices over $K$. Such a family exists by taking a curve through the target in the orbit closure with generic point on the orbit, normalizing a branch, and, if needed, extending the function field so the generic transporter exists. The orbit is open in its closure, a transporter over the algebraic closure of the function field is defined over a finite extension, and normalization after that extension again supplies a DVR with residue field $k$. This use of a curve allows inseparable extensions.

The original tag covariate $b_j$ becomes a linear form $\lambda_j$ in the enlarged contraction coordinates under $L$. Rescale each $\lambda_j$ by a $K$-unit to have coefficients in $\mathcal O$ with at least one coefficient an $\mathcal O$-unit. The product $\prod_j\lambda_j^{r_j}$ divides every generic $q$-minor by (4) and Cauchy–Binet. Each $q$-minor of the family has coefficients in $\mathcal O$. The product is primitive over the DVR, so Gauss's lemma gives divisibility over $\mathcal O$. Thus its reduced product divides the target greatest common divisor. Both are nonzero and have degree $\sum_j r_j$, so they agree up to scalar. Every target factor $b_i$ must then occur among the reduced linear forms. There are precisely $2a$ forms and $2a$ distinct target factors. The matching is therefore bijective, and comparing exponents and using the pairwise distinct $r_j$ gives
$$
\overline{\lambda}_j\ \text{is proportional to }b_j\text{ for every }j.
\tag{6}
$$
In particular distinct tag hyperplanes remain distinct even if the generic third-axis transporter has poles.

### Align the recovered coordinates and subspaces

After unit rescaling, the primitive forms $\lambda_j$ reduce to $b_j$ exactly. Replace the corresponding coordinate rows of an identity coordinate map by $\lambda_j$. Its determinant is a unit since its reduction is the identity. The forms are supported in the last enlarged third-axis part, because $L$ respects the remaining partitions. Applying the inverse regular coordinate change to contractions preserves the special fiber. In the new generic slice equations, data combinations receive no tags, and tag $j$ is the transform of $\alpha_j D_j+C_j$ for $\alpha_j\in K^\times$ and $C_j$ in the $X,Y$ rectangle. The generic change on the old slice coordinates is invertible, by block triangularity of the full slicing map, and respects their original parts.

The generic column and row spans of these tag slices can be compared simultaneously. Over $K$, use the unipotent row shear $N$ fixing $X$ and $I_j$ and inserting $-\alpha_j^{-1}C_j$ from $Y_j$ to $X$. It sends each $\alpha_jD_j+C_j$ to $\alpha_jD_j$. The column spans of the actual generic tag slices are therefore
$$
PN^{-1}(X_{i(j)}\oplus Y_j\oplus I_j).
$$
The intersection of the two for a given part $i$ is $P X_i$, because $N$ fixes $X$. Their actual row spans are $Q(Y\oplus X'_j\oplus J_j)$. Two distinct tags have row-span intersection $QY$.

Every tag slice has generic rank $\dim X_{i(j)}+m+r_j$, equal to its target rank. A unit minor of that size makes its column and row spans direct-summand lattices of this rank, with the corresponding spans in the residue field. For example, row and column elimination using the minor leaves a zero lower block because its entries vanish over $K$. The saturated lattice of a generic subspace in a finite free $\mathcal O$-module is its intersection with that module, and it is a direct summand. Since a generic intersection is contained in both spans, its saturated lattice maps into both of their specializations. For the duplicate-tag intersections the generic and target intersection dimensions are equal. Hence $P X_i$ specializes to $X_i$ for every $i$, and $QY$ specializes to $Y$.

Use regular first- and second-axis changes congruent to the identity to align these subspaces. Concretely, choose bases of their saturated lattices lifting the given target bases and extend to bases by lifting a complementary target basis. The lift matrix is invertible over $\mathcal O$ since its reduction is invertible. The first-axis choices can be made simultaneously for all $X_i$, since their specializations are in direct sum. On the second axis only the last old part enlarged by auxiliary columns needs a choice, because $Q$ preserves the other parts exactly. Thus the regular changes respect the residual partitions and leave the special tensor unchanged.

After alignment, the original data block of the tensor family is generically obtained from $A$ by a change preserving every original part in all three axes. The old slice combinations are exact, the aligned row images of $X_i$ equal $X_i$, and the aligned restriction of $Q$ maps $Y$ onto $Y$ with the original parts preserved. These restrictions are invertible over $K$. The data block specializes to $B$. This proves the reverse implication.

The enlarged side lengths are
$$
p+2am+\sum_j r_j,\qquad m+2p+\sum_j r_j,\qquad \ell+2a.
$$
Repeat after permuting the axes until every partition has been removed. Since $\sum_j r_j=a(2a+1)$, each step has polynomial size even when the number of parts grows. A fixed number of parts per axis gives an increase linear in the sum of the original lengths. Taking the starting tensor to be $K_f$ proves (1). Adding the identity rectangles and taking the specified trilinear lift are affine-linear operations in the input coefficients, so the output can be written in polynomial time in the dense representation.

## 3. The characteristic-three branches give smaller instances

The same partitioned construction with $U=W=V$ and main block an arbitrary trilinear form $t$ reduces diagonal congruence degeneration of trilinear forms to ordinary independent-axis degeneration with side length $O(n)$. For this statement the diagonal group applies the same substitution to all three arguments. Keep all five evaluation and scalar blocks. An exact congruence extends by inverse duality on $A,B$ and identities on the lines. In (3) read instead
$$
\gamma^{-1}T_{U,W,V}(i_Ux,i_Wy,z).
$$
For an orbit point it equals $t(\alpha_3^{-1}Sx,\alpha_3^{-1}Sy,\alpha_3^{-1}Sz)$ by the same equations for $p_U,p_W,\gamma$. Thus the regular readout reflects degeneration. Removing the partitions as in Section 2 has linear cost in the side lengths. Denote this linear-length construction by $\Psi$.

Assume now $\operatorname{char}k=3$. Write $\pi(f)$ for the unnormalized complete polarization and $D_f=\operatorname{rad}\pi(f)$ for its contraction radical. Put $r=\dim D_f$ and $c=n-r$. The following conclusions apply to arbitrary targets $g$ of the same original dimension.

### Nonzero restriction to $D_f$

If $f|_{D_f}\ne0$, first compute the target radical $D_g$. If $\dim D_g<r$, degeneration fails. Otherwise choose any $r$-plane $S\subseteq D_g$. Write $\pi(f)_{V/D_f}$ and $\pi(g)_{V/S}$ for the induced trilinear forms on dimension-$c$ spaces. Then the degeneration test is one ordinary tensor closure query from $\Psi(\pi(f)_{V/D_f})$ to $\Psi(\pi(g)_{V/S})$, whose side lengths are $O(c)$. If $c=0$, the test simply asks whether $\pi(g)=0$.

To see the first reduction, in characteristic three the kernel of $\pi$ consists of pure cubes in the chosen coordinates. This follows by comparing the coefficient of $s_1s_2s_3$ on each degree-three monomial. In coordinates adapted to $D_f$, every mixed monomial involving its coordinates would contribute a nonzero contraction. Thus $f$ is a sum of a complement cubic and a pure-power polynomial on $D_f$. Over $k$, this last polynomial is the cube of a linear functional. Over a fixed polarization in the orbit of $\pi(f)$, all cubics with nonzero radical restriction are equivalent: match the nonzero radical functionals, and use a shear from the complement into the radical to absorb the complement's pure-cube discrepancy. Such discrepancies are exactly linear functional cubes over $k$. The nonzero restriction condition is dense in each affine fiber above the polarization orbit. Taking closures after splitting the linear map $\pi$ gives
$$
\overline{\operatorname{GL}(V)f}=\pi^{-1}\bigl(\overline{\operatorname{GL}(V)\pi(f)}\bigr)
$$
as reduced point sets.

For the quotient assertion on trilinear forms, take a DVR degeneration and extend the generic radical by its saturated lattice. Its specialization is an $r$-plane in the target radical, since the contraction equations extend over the DVR. Choose a regular basis taking this lattice to a constant summand. The family then factors through the complementary quotient and gives the required dimension-$c$ degeneration there. Conversely a quotient degeneration extends by an inert $r$-plane. Any other $r$-plane in $D_g$ gives the same test since the full linear group on $D_g$, extended by the identity on a complement, fixes the target polarization and carries one such plane to any other.

### Zero restriction to $D_f$

If $f|_{D_f}=0$, let $E_g=\{v\in D_g:g(v)=0\}$. The restriction of $g$ is the cube of a linear functional on $D_g$, so $E_g$ is a linear subspace. If $\dim E_g<r$, degeneration fails. Otherwise choose any $r$-plane $S\subseteq E_g$. Write $f_{V/D_f}$ and $g_{V/S}$ for the induced cubics. The test is one ordinary tensor closure query from $\Phi(f_{V/D_f})$ to $\Phi(g_{V/S})$ on side lengths $O(c^2)$. For $c=0$ this is the direct zero-form test.

Here $D_f$ is inert for $f$ as a formal polynomial. In a DVR degeneration extend the generic inert subspace of dimension $r$ by saturation. It stays inert at the special point because vanishing of the coefficients of every positive power of a translation parameter is a polynomial condition on the cubic and translation vector. In characteristic three the inert subspace of the target is exactly $E_g$: the linear coefficient of $g(x+sv)-g(x)$ vanishes if and only if the polarization contracts to zero with $v$, by polarization in the other two arguments using $2\in k^\times$. The coefficient of $s^3$ is $g(v)$, and the quadratic coefficient vanishes for radical $v$. Align the saturated plane as in the trilinear argument and take the quotient family. For the converse a quotient degeneration again extends by zero. The linear group on $E_g$ extends to the stabilizer in $D_g$ of the functional whose cube is $g|_{D_g}$. Extending these substitutions by the identity on a complement preserves $g$ and acts transitively on the eligible planes. This also explains why the earlier Grassmannian criterion needs a single quotient query once the dimension check is passed.

For example, the cubics $x^2y+z^3$ and $x^2y$ have identical complete polarization in characteristic three. Scaling $z$ gives a degeneration from the first to the second. In the reverse direction the source requires an inert line and the target has none, so degeneration fails. The ordinary tensors distinguish these two directions with the same fixed tags.

## 4. Literature and verification scope

Grochow and Qiao's partition gadget is a reduction for orbit equality. Its rank markers motivate the private identities above. Duplicate tags make the exact common divisor of maximal minors independent of the input tensor, recover the full factor arrangement throughout the degeneration, and identify the original direct summands by intersection. Distinct ranks suffice, so the dependence on the number of parts is polynomial. The cubic readout keeps the formal polynomial in every characteristic. In the nonzero-radical branch the shorter route uses polarization only after the separate closure argument proves that every pure-cube refinement is attained in the closure. [Grochow–Qiao, Theorem 5.1](https://arxiv.org/html/2306.16317#S5) · [Grochow–Qiao, STOC 2025](https://doi.org/10.1145/3717823.3718282) · [Garibaldi–Nakano, Proposition 3.5.1](https://arxiv.org/abs/1501.07515)

The results concern single-point membership in ordinary tensor orbit closures. Bläser, Ikenmeyer, Lysikov, Pandey and Schreyer prove hardness for ordinary tensor orbit-closure containment. Bläser and Lysikov give a separate degeneration relation for unital associative multiplication tensors. Doğan, Maar, Oliveira and Qiao address orbit-closure intersection for special-linear tensor actions with one fixed side over characteristic zero. These results give different reductions and algorithmic consequences from the explicit same-shape cubic-to-tensor map above. The valuative step uses ordinary curve selection and normalization, consistent with the classical characterization of orbits via discrete valuation rings. Proofs here are informal and publication priority remains unverified. [Bläser–Ikenmeyer–Lysikov–Pandey–Schreyer](https://epubs.siam.org/doi/abs/10.1137/1.9781611976465.152) · [Bläser–Lysikov](https://doi.org/10.4230/LIPIcs.MFCS.2016.19) · [Doğan–Maar–Oliveira–Qiao](https://doi.org/10.4230/LIPIcs.CCC.2026.32) · [Grunewald–O'Halloran](https://archive.mpim-bonn.mpg.de/id/eprint/3085/)

The companion [Tensor.py](Tensor.py) checks all 243 slice combinations over $\mathbb F_3$ in one $16\times15$ matrix pencil. It verifies the duplicate-tag support intersections and constructs four triangular $13\times13$ minors whose monomial determinants have exactly the common factor with exponents $(1,2,3,4)$.
