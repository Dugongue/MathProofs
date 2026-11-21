# Determinant-one tensor isomorphism and oriented isomorphisms of special groups

Fix an odd prime $p$. Write $F=\mathbb F_p$, $m=p-1$, and use deterministic polynomial-time many-one reductions unless stated otherwise. Group inputs below are succinct commutator coefficients in ordered bases. Their length is the number of written field coefficients, rather than the size of the Cayley table.

Let $\mathsf{G}_p$ be ordinary isomorphism of the finite special groups of nilpotence class two and exponent $p$ in these coordinates. Let $\mathsf{OG}_p$ ask for an isomorphism of determinant one on the underlying additive space defined by Baer's correspondence, using the displayed coordinates as bases.

**Theorem.** Ordinary three-tensor isomorphism over $F$ and $\mathsf{G}_p$ are polynomial-time many-one equivalent. There is a many-one reduction $\mathsf{OG}_p\le_m\mathsf{TI}_{\rm SL}(F)$, and $\mathsf{TI}_{\rm SL}(F)$ reduces to a fixed conjunction of at most $m^3$ instances of $\mathsf{OG}_p$. In particular,
$$
 \mathsf{TI}_{\rm SL}(F)\le_m\mathsf{TI}(F)
 \quad\Longleftrightarrow\quad
 \mathsf{OG}_p\le_m\mathsf{G}_p .
$$
For $p=3$, the orientation requirement is precisely an even isomorphism on the group elements ordered by their coordinate tuples.

## The compact group model and the reverse reduction

An input consists of an alternating $F$-bilinear map $\beta:X\times X\to Z$ whose values span $Z$ and whose common radical is zero. These conditions are polynomial-time tests. Its group has multiplication
$$
 (x,z)(x',z')=(x+x',\,z+z'+\tfrac12\beta(x,x')) .
$$
The group center is $Z$, the commutator is $\beta$, and $Z=[G,G]$. The resulting nontrivial groups are special of class two and exponent $p$. The group law and the operation $(g,h)\mapsto gh[g,h]^{-1/2}$ recover the additive law, so group isomorphisms are additive-linear. Each group isomorphism induces invertible maps $g$ on $X=G/Z$ and $h$ on $Z$ satisfying $\beta'(g x,g x')=h\beta(x,x')$. Conversely any such pair lifts by acting on the displayed coordinate summands. A central shear of the $X$ coordinates does not affect the determinant. The determinant on the additive space is therefore $\det g\det h$. [Baer, Groups with Abelian Central Quotient Group](https://doi.org/10.1090/S0002-9947-1938-1501972-1)

Use the associative algebra $B_\beta=F1\oplus X\oplus Z$, with $1$ a unit, $xx'=\beta(x,x')$, and all other radical products zero. This is associative since every triple radical product vanishes. The radical is $J=X\oplus Z$, with $J^2=Z$. Any algebra isomorphism induces the same data $(g,h)$ on $J/J^2,J^2$ and has determinant $\det g\det h$ in the displayed bases. Conversely every bracket transporter gives a blockwise algebra isomorphism.

For unital associative multiplication, an isotopy $R(ab)=P(a)Q(b)$ has
$$
 (P,Q,R)=(L_u\phi,R_v\phi,L_uR_v\phi)
$$
where $u=P(1)$, $v=Q(1)$ are units and $\phi(a)=u^{-1}R(a)v^{-1}$ is an algebra isomorphism. This follows by evaluating at the unit in each argument and substituting. The ratio $\det P\det Q/\det R$ equals $\det\phi$. Thus ordinary equivalence of the multiplication tensors is algebra isomorphism, and determinant-one equivalence of those tensors is determinant-one algebra isomorphism. This proves the reductions $\mathsf G_p\le_m\mathsf{TI}(F)$ and $\mathsf{OG}_p\le_m\mathsf{TI}_{\rm SL}(F)$. Dualizing the two input modes changes the determinant convention by inverses and leaves determinant one unchanged.

## An exact group construction for oriented algebra isomorphism

Let $A,A'$ be $n$-dimensional unital associative algebras with $n\equiv-1\bmod m$. The following polynomial construction sends $A$ to a compact special group $G(A)$, of additive dimension $O_p(n+1)$, with the exact relative determinant identity
$$
 \{\det_F \psi:\psi:G(A)\cong G(A')\}
 =\{\det_F\phi:\phi:A\cong A'\}.
\tag{1}
$$
The determinant on the left is the additive determinant just defined.

Take three copies $U,V,W$ of $A$, and use two further copies $P_1=U^*$, $P_2=V^*$, lines $L_1=F e_1,L_2=F e_2$, and alternating spaces $S_i$ of dimension $2r_i$ for $1\le i\le4$, each with a fixed nondegenerate alternating form $\omega_i$. The group quotient space is
$$
 X=U\oplus V\oplus P_1\oplus P_2\oplus L_1\oplus L_2\oplus\bigoplus_{i=1}^4S_i,
 \qquad Z=W\oplus\bigoplus_{i=1}^4 Fz_i.
$$
Use the corresponding ordered bases on both endpoints, taking each copy of $A$ in its input basis and the two duals in the dual bases. Define the alternating map by the following blocks, their reverse blocks by skew symmetry, and every other block by zero:
$$
 \begin{aligned}
 \beta(u,v)&=uv\in W,\\
 \beta(u,\alpha)&=\alpha(u)z_1,\qquad &\beta(v,\eta)&=\eta(v)z_2,\\
 \beta(e_1,\alpha)&=\alpha(1_A)z_3,&\beta(e_2,\eta)&=\eta(1_A)z_4,\\
 \beta(s_i,s_i')&=\omega_i(s_i,s_i')z_i.&&
 \end{aligned}
$$
Choose $r_i>n$ such that the four positive integers $r_1,r_2,r_3+1,r_4+1$, in that order, each exceed the sum of all earlier ones. Also require
$$
 n+r_1\equiv n+r_2\equiv r_3+2\equiv r_4+2\equiv0\bmod m .
\tag{2}
$$
Pick the first usable integer in the given residue class each time. There are only four choices, and the bounds are $O_p(n+1)$. The values of $\beta$ span $Z$, since multiplication is unital and each $\omega_i$ is nondegenerate.

To see how all transporters of $\beta$ act, the following spaces are recovered intrinsically.

1. The forms $\lambda\beta$ of rank at most $2n$ for $\lambda\in Z^*$ are exactly those vanishing on the marker space $Z_0=\bigoplus_i Fz_i$. Such a form is supported on $U\oplus V$. Any nonzero coefficient at $z_i$ gives on $S_i$ a nondegenerate restriction of rank $2r_i>2n$. These tests recover $Z_0$ and the common radical $X_0=P_1\oplus P_2\oplus L_1\oplus L_2\oplus\bigoplus_i S_i$ of the low-rank forms. The latter equality uses unital multiplication to detect any nonzero $U$ or $V$ coordinate.
2. On $X_0$ the bracket takes values in $Z_0$. The four coordinate forms have disjoint symplectic parts, of ranks $2r_1,2r_2,2(r_3+1),2(r_4+1)$. The additional rank two in coordinates three and four is the nonzero pairing of $L_1,L_2$ with the corresponding dual's evaluation on $1_A$. Every subset of the four rank weights has a distinct sum by construction. Hence the four dual axes in $Z_0^*$ are recovered by ranks on $X_0$. On $Z_0$ any target map acts by independent scalars $a_1,a_2,a_3,a_4$.
3. The common radical $R$ of forms one and two on $X_0$ consists of $P_1\oplus P_2\oplus L_1\oplus L_2\oplus S_3\oplus S_4$. Within $R$, the kernel $N$ of the first two marker pairings with all of $X$ is $L_1\oplus L_2\oplus S_3\oplus S_4$. The pairings factor through $R/N$ and $X/X_0$. They recover the two dual roles in $R/N$ and the two input roles in $X/X_0$ by taking the kernels of the other coordinate. The bracket $X/X_0$ into $Z/Z_0$ recovers the multiplication bimap on these roles. On $X_0/R$, the first two forms split the two symplectic roles $S_1,S_2$ by their radicals. On $N$, the common radical of forms three and four is $L=L_1\oplus L_2$, and on $N/L$ these forms split $S_3,S_4$. Finally their pairings of $L$ with $R/N$ recover the individual lines $L_1,L_2$. All pairings involving $X_0$ take values in $Z_0$, so the formulas do not require a fixed complement of $Z_0$.

The common radical of $\beta$ is zero. Any vector in it first lies in $X_0$, then in $R$ and $N$ by the first two forms, then in $L$ by the forms on $N$. The last two forms paired with the respective dual roles force it to be zero. This verifies the special-group promise for the constructed input.

Let the induced maps on $U,V,W$ be $f,g,t$. They satisfy $t(xy)=f(x)g(y)$. The induced map on $P_1$ is $a_1 f^{-\mathsf T}$ and on $P_2$ is $a_2g^{-\mathsf T}$, by the two evaluations. Preservation of the $L_1$-pairing forces $f(F1_A)=F1_{A'}$, and the $L_2$-pairing forces the corresponding condition on $g$. Write $f(1_A)=s_1 1_{A'}$, $g(1_A)=s_2 1_{A'}$. Since $(f^{-1})(1_{A'})=s_1^{-1}1_A$, comparing the third bracket gives the line scale $a_3s_1/a_1$ on $L_1$, and the fourth gives $a_4s_2/a_2$ on $L_2$. Unit normalization now gives $t=(s_1s_2)\phi$ for an algebra isomorphism $\phi:A\to A'$.

The ranks and kernels give the invariant flag $L\subseteq N\subseteq R\subseteq X_0\subseteq X$. Its quotient maps yield the full determinant by triangularity in the corresponding ordered frames. On $S_i$ the induced symplectic similitude has multiplier $a_i$ and determinant $a_i^{r_i}$, by the change-of-basis identity for the Pfaffian. The determinants of $f,g$ cancel against their dual maps. Multiplying the two line scales and the central determinant gives the total additive determinant
$$
 \det(t)\,s_1s_2\,
 a_1^{n+r_1}a_2^{n+r_2}a_3^{r_3+2}a_4^{r_4+2}
 =\det\phi .
$$
Here (2) kills the marker powers and $n+1\equiv0\bmod m$ kills the remaining scalar power. No permutation signs arise because the individual roles have been identified. Conversely, given $\phi$, use it on the three algebra copies, its inverse duals on the two duals, and the identity on $L_i,S_i,Fz_i$. This preserves the bracket and gives determinant $\det\phi$, proving (1).

The same argument gives a shorter group construction for the output-determinant problem on concise bimaps $T:U\times V\to W$, meaning that each input kernel is zero and the output is spanned. Omit $L_1,L_2$ and the last two markers. Choose distinct marker ranks $2r_1,2r_2>\dim U+\dim V$ with $r_1+\dim U+1$ and $r_2+\dim V+1$ divisible by $m$. The same flag without the two unit lines shows that total group determinants are exactly the determinants of the original $W$-maps.

## Compiling all determinant characters

For completeness the weighted algebra encoding used here works for all inputs of matching positive formats, including tensors with deficient support. The existing truncated-corner construction for a character with weights $w_1,w_2,w_3\in\mathbb Z/m$ uses an upper triangular three-vertex algebra. Its diagonal rings are $F[t]/(t^{M_0}),F[t]/(t^{M_1}),F[t]/(t^{M_2})$. The three off-diagonal corners are the three input tensor spaces tensored with $F[t]/(t^{k_i})$, with the map $T$ as multiplication from corners $01$ and $12$ into $02$. Use bilinear-map determinant coordinates, taking $k_i\equiv w_i\bmod m$, $k_i\ge2$, $k_3\le\min(k_1,k_2)$, and $M_i\ge\max(k_1,k_2,k_3)$. In covariant coordinates negate the first two weights.

All three corners are nonzero from their positive dimensions regardless of the bilinear map. The directed corner pattern distinguishes the vertices. Align the diagonal idempotents of an isomorphism by conjugation by a radical unit, which has determinant one. On the diagonal $t$ maps to $\lambda_i t$ modulo $t^2$. Its two incident actions on each corner agree, forcing all three $\lambda_i$ equal to a common $\lambda$ because each corner has length at least two. Modulo $t$, the three corner actions are exactly a bimap transporter $(f_1,f_2,f_3)$. At grade $j$ the action is $\lambda^j f_i$ on corner $i$ and $\lambda^j$ on a diagonal grade. The determinant is therefore
$$
 \prod_i(\det f_i)^{k_i}\cdot
 \lambda^{\,\sum_{j=0}^2\binom{M_j}{2}+\sum_i(\dim X_i)\binom{k_i}{2}} .
$$
Choose the $M_j$ so that the exponent of $\lambda$ is zero modulo $m$. Every residue is a sum of three triangular numbers modulo $m$. For $2^e$, the triangular numbers $\binom{j+1}{2}$ for $0\le j<2^e$ form a permutation: a collision makes $(a-b)(a+b+1)$ divisible by $2^{e+1}$, while exactly one factor is even and both have magnitude less than $2^{e+1}$. For an odd prime power, use $8\binom{M}{2}=(2M-1)^2-1$. Every residue modulo the prime is a sum of two squares by intersecting the two square-value sets. A third square ensures a representation with a nonzero coordinate even for zero. Lift in that coordinate using its invertible derivative. Apply the Chinese remainder theorem, and add multiples of $2m$ to make the lengths large enough. All lengths are bounded at fixed $p$.

Conversely, every tensor transporter lifts coefficientwise with the diagonal identity. Thus the exact set of algebra-isomorphism determinants is the character image of all original transporters. The original triangular algebra is centrally indecomposable: a central idempotent is diagonal, its entries are zero or one, and each nonzero corner forces equal entries on its endpoints. It has nonzero radical. Adjoin a product of at most two distinct odd-degree field factors to both algebras to make the dimension $-1\bmod m$. Odd residues are attained by one odd degree, and even residues by two unequal odd degrees, with degrees bounded at fixed $p$. These factors cannot swap with the original factor or with one another. Automorphisms on each field factor have determinant one because Frobenius is an odd-length cycle in a normal basis. This leaves the determinant set unchanged. Positive formats suffice for the construction. An unmatched format or a zero-dimensional format can instead be decided directly, since in the latter case the tensor is zero. The underlying triangular tensor-to-algebra idea is due to Grochow and Qiao. The weighted truncation calculation is from the existing MathProofs note *Every finite-field determinant character reduces to unit-side special-linear tensor isomorphism*, with the padding changed from $+1$ to $-1$ modulo $m$. [Grochow and Qiao, Tensor Isomorphism-Completeness](https://doi.org/10.1137/21M1441110)

Combining this construction with (1) gives a single $\mathsf{OG}_p$ instance per specified determinant character. The ordinary transporter determinant triples are either empty or a coset $dH$ in $(F^\times)^3$. A nonempty coset contains the identity if and only if its image under every character contains the identity. If the coset misses the identity, a character of the quotient by $H$ separates that coset from the identity. The trivial character also detects an empty transporter set. Thus the fixed conjunction over all $m^3$ characters is exactly the original determinant-one question.

The construction for the trivial character, with the orientation forgotten, gives $\mathsf{TI}(F)\le_m\mathsf G_p$. In the converse direction of the displayed equivalence of collapses, replace each group orientation test by ordinary group isomorphism and then by ordinary TI. Pack those ordinary TI instances into a single ordinary TI with ordered and tagged roles. This uses closure of ordinary TI under a fixed conjunction, supplied by the standard constant-signature tensor-system compiler. In the forward direction compose $\mathsf{OG}_p\le_m \mathsf{TI}_{\rm SL}(F)$ with the assumed reduction and then $\mathsf{TI}(F)\le_m\mathsf{G}_p$. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1 and Open Question 1.9](https://arxiv.org/html/2306.03135v2)

Ordinary TI always reduces to determinant-one TI by adding one unused coordinate to each mode. A transporter extends across each new coordinate with its determinant corrected, and an amplified transporter restricts to the original contraction supports. Thus the displayed reverse reduction is equivalently the equality of the two many-one degrees.

For the $p=3$ interpretation, the sign on the elements of $F^D$ of an invertible linear map is the quadratic character of its determinant. Elementary transvections act with cycles of odd length and thus even sign. A diagonal scaling on one coordinate acts by $p^{D-1}$ copies of multiplication on $F$, whose sign is the quadratic character of its multiplier. These transformations generate the linear group. In $F_3^\times$, the quadratic character equals the determinant itself as a sign.

The exact equality concerns an orientation variant of a classical group isomorphism domain in succinct coordinates. It supplies no equivalence to polynomial-time decidability of unrestricted Group Isomorphism or of Cayley-table Group Isomorphism. The field is a fixed odd prime field. The reductions and their proofs are informal, and publication priority for the group construction is unverified.

Bounded checks tested 480 explicit scalar lifts over four odd prime fields, comprising 29,340 bracket equalities. In addition, 486 independently computed matrix ranks confirmed the low-rank forms and marker-axis weights, and exhaustive tests found all residues as sums of three triangular numbers for each modulus from 2 through 50. These checks supplement the written proofs.
