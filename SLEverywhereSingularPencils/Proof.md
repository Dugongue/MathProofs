# Special-linear tensor isomorphism on everywhere-singular pencils

Informal proof. Fix a finite field $F=\mathbb F_q$. There is a deterministic polynomial-time many-one reduction from SL-TI of nonzero $n\times n\times n$ tensors with injective first-mode slice map and $\gcd(n,q-1)=1$ to SL-TI over the same field on a class of everywhere-singular square matrix pencils. The output tensors are raw. They come with no marked vectors, prescribed maps, or block decompositions. The first-mode dimension and both equal matrix-mode dimensions are $O_q(n)$, and all three are one modulo $q-1$. Ordinary isomorphism is preserved as well. The prescribed total determinant in the target is the literal product of the original three primal mode determinants.

Thus the balanced unit-side multiplication tensors from the triangular determinant-character normalization reduce to this class, since the presence of a unit gives an injective slice map. With that normalization and the constant conjunction construction for ordinary TI, an ordinary-TI reduction on the singular class below would settle the fixed-field restriction of Question 1.9. The result is a transfer to a structural class of raw SL-TI instances. [Chen–Grochow–Qiao–Tang–Zhang, Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

## 1. Conventions and Kronecker blocks

Use a slice map $M:U\to \operatorname{Hom}_F(X,Y)$. The transport equation is $M_B(fu)=hM_A(u)g^{-1}$. The corresponding covariant tensor mode maps are $f^{-\mathsf T},g^{-\mathsf T},h$, so the total determinant is
$$
 \chi(f,g,h)=(\det f)^{-1}(\det g)^{-1}\det h.
$$
If the three dimensions have the same unit residue modulo $q-1$, an ordinary transporter has total determinant one if and only if it can be adjusted by scalar triples to make each determinant one. Indeed, in covariant modes a scalar triple acts trivially on the tensor when its entries multiply to one. The required scalar in each mode is the unique root with exponent that mode's dimension. For dimensions all one modulo $q-1$, these three roots multiply to one. In the equal-dimensional input with $\gcd(n,q-1)=1$, the same conclusion follows since the root map is the same inverse power in every mode. These are the two cases used below.

Write $P_e=F[s,t]_e$ for the homogeneous polynomials of degree $e$ in two variables. The left block $L_\ell(a,b):P_{\ell-1}\to P_\ell$ multiplies by $as+bt$. The right block $R_m(a,b):P_m^*\to P_{m-1}^*$ is its transpose at length $m$. Thus over every extension the left block is injective at nonzero $(a,b)$, and the right block is surjective. For any $\alpha\in\operatorname{GL}_2(F)$ there are compatible changes of polynomial coordinates, given by the symmetric powers of its action on linear forms, taking the two slices to their linear combinations indexed by $\alpha$. On the right block these changes are the corresponding dual maps. We use these explicit isomorphisms as references after a quotient label change.

For the left blocks a morphism of ordered pairs $L_\ell\to L_j$ is multiplication on both vertices by one homogeneous polynomial of degree $j-\ell$, and is zero if $j<\ell$. Indeed if $A$ is its input map and $u_i=s^{\ell-1-i}t^i$, then $tA(u_i)=sA(u_{i+1})$ because $tu_i=su_{i+1}$. The last relation forces $s^{\ell-1}$ to divide $A(u_0)$. The other input monomials and all the output monomials then give exactly the asserted map. This also proves the statement for $\ell=1$ directly. Duality gives the reverse direction of nonzero morphisms among the right blocks. Each individual block has scalar endomorphism ring.

There is no nonzero morphism $R_m\to L_\ell$. Use the shifted projection bases for $R_m$ and the shifted injection bases for $L_\ell$. For a map with input matrix $P$ and output matrix $Q$, the two equations are $ [Q,0]=\left(\begin{smallmatrix}P\\0\end{smallmatrix}\right)$ and $[0,Q]=\left(\begin{smallmatrix}0\\P\end{smallmatrix}\right)$. With zero-based indices they force the first column and last row of $Q$ to vanish and give $Q_{ij}=Q_{i+1,j-1}$ whenever the indicated entries occur. Every entry propagates to one of those boundaries. Consequently the endomorphisms of a direct sum have upper block triangular form when the right family is placed before the left family, with the successive right sizes increasing and the successive left sizes decreasing. At a repeated isotype, its diagonal action is an arbitrary matrix on the multiplicity space tensored with the identity on the individual block.

## 2. A dual binary marker with only scalar stabilizers

For every sufficiently large $d$ depending only on $q$, there is a line $F B\subset P_d^*$ whose stabilizer in $\operatorname{GL}_2(F)$ consists of the scalar maps. To see this, choose $k$ large enough that $|\operatorname{GL}_2(F)|(q-1)<q^k$, and suppose $d\ge2k-1$. For each nonscalar $\alpha$, its projective transformation on the dual projective line over the algebraic closure is nonidentity. Choose $k$ point-image pairs pairwise disjoint, each with distinct endpoints. This is possible by excluding finitely many points at each choice. The $2k$ evaluation covectors on $P_d$ at these points are linearly independent. For example, put them in an affine chart and apply the Vandermonde determinant to the first $2k$ consecutive monomial degrees. The induced action of $\alpha$ on $P_d^*$ sends each first evaluation vector to a nonzero scalar times its paired vector. For every $\lambda\in F^\times$, the operator $\alpha-\lambda I$ on $P_d^*$ thus has rank at least $k$, first over the algebraic closure and therefore also over $F$. The union of its eigenspaces over all nonscalar $\alpha$ and all $\lambda\in F^\times$ has fewer than $q^{d+1}$ elements. Any vector outside the union is nonzero and has the desired projective stabilizer. At fixed $q,d$ it is found by finite enumeration. This argument uses the dual of the homogeneous polynomial representation, including in small characteristic.

Over $F_3$ one can take $d=4$. In the dual basis to $s^4,s^3t,s^2t^2,st^3,t^4$, the vector $(0,1,1,0,0)$ works. Here is a finite check. If the columns of $\alpha$ are $(a,c),(b,d_0)$, expand $(as+ct)^{4-i}(bs+d_0t)^i$ for $0\le i\le4$. The sum of coefficients of $s^3t$ and $s^2t^2$ gives the five entries of the transformed dual vector. Compute over $F_3$ for the 24 invertible $2\times2$ matrices whose first nonzero entry in row order is $1$. The entries are proportional to $(0,1,1,0,0)$ only for the identity. Equivalently this verifies the dual action without inversion, which gives the same line stabilizer.

## 3. The raw construction and its intrinsic quotient

Put $m_0=q-1$. For $q>2$, choose a positive integer $k\equiv -n^{-1}\pmod {m_0}$ of bounded size, and set $r=q-2$. There are $k$ separate copies of the original label space $U$, each used in $r$ pairs of blocks. Index the pairs by $j=1,\ldots,kr$, and write $i(j)\in\{1,\ldots,k\}$ for its label group. Choose positive lengths $m_1<\cdots<m_{kr}$ starting at $m_1=1$, and $\ell_1>\cdots>\ell_{kr}\ge1$. Put
$$
 D=\sum_j(m_j+\ell_j+1),\qquad nD\equiv kn+2\equiv1\pmod {m_0}.
$$
Choose $\ell_1$ sufficiently large for Section 2 and then in the desired residue class. It is still bounded in terms of $q$. For $q=2$ take $k=r=1$ and omit the congruences. Take one nonzero $B_j:P_{\ell_j-1}\to P_{m_j-1}^*$ for each pair. Since $m_1=1$, take $B_1$ to generate the marker line of Section 2 at degree $\ell_1-1$. The remaining $B_j$ can be any nonzero maps. Over $F_3$ take $k=r=1$, $m_1=1,\ell_1=5$ and the explicit quartic marker. Then $D=7$, giving the congruences for every odd $n$.

For a tensor with slice map $M$, the two matrix spaces are the direct sums of $\dim Y=n$ copies of each $R_{m_j}$ and $\dim X=n$ copies of each $L_{\ell_j}$, with all right blocks first. The label space is $F^2\oplus U^k$. At a label $(a,b,u_1,\ldots,u_k)$, use the slice
$$
 \widehat M(a,b,u_1,\ldots,u_k)=
 \begin{pmatrix}
  R(a,b) & W(u_1,\ldots,u_k)\\
  0 & L(a,b)
 \end{pmatrix},
 \qquad
 W(u_1,\ldots,u_k)=
 \operatorname{diag}_{j}\bigl(M(u_{i(j)})\otimes B_j\bigr).
$$
Here $R,L$ are the ordered direct sums of the repeated Kronecker blocks, and the diagonal upper blocks are ordered by the same pair index on the two families. This notation does not require the individual rectangular blocks to be square. Each matrix mode has dimension $nD$. Every slice is singular over the algebraic closure, since the subspace of right input coordinates has more dimensions than its entire output support on the right. A nonzero $(a,b)$ has rank exactly $\dim Y_R+\dim X_L$, where $Y_R$ is the right output space and $X_L$ the left input space. This uses surjectivity of $R(a,b)$ and injectivity of $L(a,b)$. At $(a,b)=0$ the rank is at most $\min(\dim Y_R,\dim X_L)$, which is strictly smaller. Therefore the label subspace $U^k$ is intrinsic as the locus of slices below maximum rank. Any transporter induces an invertible map $\alpha$ on the two-dimensional quotient. The two vectors lifting the quotient basis are used only in the proof. They are absent from the output instance.

## 4. Remove every quotient motion without changing the total determinant

Upper-block shears with off-diagonal maps $G:X_L\to X_R$ and $H:Y_L\to Y_R$ change the upper slice by $HL(a,b)-R(a,b)G$. Given any two prescribed shifts at the coordinate quotient basis, the pair $G,H$ can realize them independently. On a single right and left summand pair, call the shifts $A,B$. The equations in the shifted bases are
$$
 H_{ij}-G_{ij}=A_{ij},\qquad H_{i,j+1}-G_{i+1,j}=B_{ij}.
$$
Choose the first row and last column of $G$ freely. Set $G_{i+1,j}=G_{i,j+1}+A_{i,j+1}-B_{ij}$ for each interior $j$ in successive rows. The first equations determine all but the last column of $H$, and the second equations at the last column determine that column. This solves every summand pair separately, including the multiplicity coordinates. For an arbitrary quotient basis use the inverse change of basis on the two requested shifts and solve the same equations. If the shifts are in the image of $W$, the change of label lifts is an actual upper shear on $F^2\oplus U^k$, because $W$ is injective. Together the three shears are an automorphism of the constructed tensor and have all three determinants one. Compose with a target shear so that the two anchor images are the designated lifts of $\alpha$'s columns, with no $U^k$-components.

Now compare those two anchor maps with the symmetric-power changes of basis from Section 1. After calibration by these changes, the matrix maps belong to the unit group of the source ordered anchor endomorphism algebra. In the pure right and pure left diagonal parts they are upper block triangular by the chosen ordering of indices. Acting on an upper slice, the cross-type upper blocks of the matrix maps cancel. On its $j$-th matched diagonal block the remaining map sends the component $M_A(u_{i(j)})\otimes B_j$ to a map of the form
$$
 h_j M_A(u_{i(j)})g_j^{-1}\otimes B_j^\alpha,
$$
for invertible maps $h_j:Y_A\to Y_B$, $g_j:X_A\to X_B$. Here $B_j^\alpha$ is the natural action of the quotient change on the small block. The diagonal formula follows by multiplying the two upper triangular matrices and taking the diagonal of their product with the block diagonal upper slice. For $j=1$, the right output factor is $P_0^*=F$, so $B_1^\alpha=B_1(\operatorname{Sym}^{\ell_1-1}\alpha)^{-1}$, the dual representation of Section 2. Since the source slice map is nonzero, across all labels the equality of the first matched diagonal block forces the line of $B_1^\alpha$ to equal the line of $B_1$. Therefore $\alpha=\kappa I$ for some $\kappa\in F^\times$.

Compose the output transporter with the scalar target autotopism $f\mapsto\kappa^{-1}f$, $g\mapsto g$, $h\mapsto\kappa^{-1}h$. It changes the quotient action to the identity and multiplies the literal total determinant by
$$
 \kappa^{\dim U'-\dim Y'}=\kappa^{kn+2-nD}=1.
$$
After this correction the two anchors are fixed by the comparison of lifts. Every raw transporter has thus been replaced by an anchored transporter of the same literal total determinant. The reverse inclusion holds because an anchored transporter is itself a raw transporter. This proves equality of the raw and anchored total-determinant sets, including emptiness.

## 5. Exact determinant algebra on the anchored branch

When the quotient is the identity and the two chosen lifts are fixed, comparison of the $j$-th matched diagonal blocks gives
$$
 M_B(f_i u)=h_jM_A(u)g_j^{-1}
 \qquad (i=i(j)).
$$
Indeed the output component of the label map on the $i$-th group depends only on the corresponding input component, because the matching diagonal equation depends only on that input and $M_B$ is injective. Thus the map on $U^k$ is block diagonal with invertible maps $f_1,\ldots,f_k$. The equations are exactly the original tensor transport equations with a common first-mode map $f_i$ within its $r$ replicas. Their converse is also exact. Given any such collection, take zero strict upper entries in the matrix maps, and on each right multiplicity space use $h_j$, on each left one use $g_j$. These are genuine anchor transporters and give the required action on every full slice.

The two matrix determinants on this anchored branch are
$$
 d_{X'}=\prod_j(\det h_j)^{m_j+1}(\det g_j)^{\ell_j},\qquad
 d_{Y'}=\prod_j(\det h_j)^{m_j}(\det g_j)^{\ell_j+1}.
$$
Every upper block contributes only through this block triangular formula. The label determinant is $\prod_i\det f_i$, as the quotient action is the identity. Hence the literal total is
$$
 \prod_i\left((\det f_i)^{-1}
              \prod_{j:i(j)=i}\frac{\det g_j}{\det h_j}\right).
$$

For a fixed first-mode map $f$, the corresponding matrix determinant ratios $\det h/\det g$ for one original tensor pair form an empty set or a coset $\rho H$ of a subgroup $H\le F^\times$. This follows because any two matrix transporter pairs with the same $f$ differ by a unit of the endomorphism algebra of the full ordered slice list. If the set is nonempty, the products of $r$ independent inverted ratios form $\rho^{-r}H$. At $r=q-2$, $-r\equiv1\pmod{q-1}$, so the outcome is exactly $\rho H$. At $q=2$ the ratio is trivial. Therefore a single label group in the output has exactly the same possible total determinant values as the original pair. If that set is $C$, the whole output realizes precisely the set of products of $k$ elements of $C$. The set $C$ itself is empty or a coset in $F^\times$, by the same transporter-coset argument on the full three-mode group. Since $k$ is a unit modulo $q-1$, the product set is $\{c^k:c\in C\}$. It contains one exactly when $C$ contains one. Ordinary isomorphism is also equivalent by emptiness. More generally a prescribed total value $\eta$ can be translated to $\eta^k$. This verifies the determinant condition using the primal tensor determinants, without an inverse on just one of the matrix modes.

## 6. Complexity and converse reduction

All choices of lengths, block counts and markers depend only on $q$ and the residue of $n$ modulo $q-1$. At fixed $q$ they can be computed by constant-size searches before forming the slices. The output array is dense and has $O_q(n^3)$ entries. Each entry is an explicitly copied source coefficient, a source coefficient multiplied by a fixed field constant, or a fixed pencil coefficient. This gives a deterministic polynomial-time construction of one pair over $F$. At $q=2$ every determinant is one, so the same construction with $k=r=1$ proves both ordinary and special-linear preservation. The input is nonzero, allowing the marker to be read from its upper slices. A zero tensor pair of the source format has an immediate answer, and can be handled separately if admitted.

The converse one-instance reduction for the raw singular class with the stated unit residues follows from the triangular determinant-character normalization. All its dimensions are one modulo $q-1$, so checking SL-TI is exactly checking the one total-determinant character. Apply the single-character normalization to obtain balanced unit-side multiplication tensors, whose slice maps are injective by unitality. Thus these two restrictions are polynomial-time many-one equivalent over the same field. This equivalence leaves the determinant condition in the target. An ordinary-TI reduction for the unrestricted high-multiplicity singular class is still unproved.

This proof uses the earlier ordered singular-anchor construction and the triangular determinant-character normalization. The extra ingredients are the raw binary marker, the several isotype pairs that recover the literal matrix determinant ratio, and the independent label groups that bring all output dimensions to unit residues. The arguments are informal and publication priority is unestablished.
