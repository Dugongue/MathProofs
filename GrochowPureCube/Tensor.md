# A tensor isomorphism reduction for cubics over every commutative ring

**Theorem.** For every commutative unital ring $R$, formal homogeneous cubic equivalence in $n\ge1$ variables under $\operatorname{GL}_n(R)$ reduces to one instance of ordinary free three-tensor isomorphism over the same ring. Each output side has length $O(n^2)$. The map from a cubic to its tensor is explicit and uses a polynomial number of ring operations. Transporters can be recovered in either direction from witnesses. In particular the construction retains arbitrary pure-cube coefficients over every characteristic-three field, including imperfect fields. All arguments below are informal.

The proof has two steps. First, changes in the choice of trilinear lift are realized by shears in two alternating-form spaces. Evaluation blocks tie the three quotient maps and determine a common scalar. Second, two copies of each rank marker recover specified direct-sum parts over an arbitrary ring. This step extends the Grochow–Qiao approach from fields without a diagonal-full hypothesis.

## 1. Encode a formal cubic by a partitioned tensor

Let $V=R^n$ with the given basis. Use the argument convention $f(x)=g(hx)$ for a cubic transporter. For a trilinear form $t$ write $d(t)(x)=t(x,x,x)$ as a polynomial in the formal coordinates of $x$. Choosing one ordered triple for each degree-three monomial gives an explicit lift $t_f$ with $d(t_f)=f$.

Let $M=\operatorname{Alt}^2(V,R)$ be the free module of alternating bilinear forms. The kernel of $d$ is exactly the set
$$
\left\{(x,y,z)\longmapsto a(x)(y,z)+b(y)(x,z):
                    a,b\in\operatorname{Hom}(V,M)\right\}.
\tag{1}
$$
To prove this, group the coefficient positions of a tensor by the unordered multiset of their three indices. Each coefficient of $d(t)$ is the sum within one group. In such a group the zero-sum vectors are spanned by differences of positions, by subtracting multiples of a fixed position. The transpositions $(2\,3)$ and $(1\,3)$ generate all permutations of positions, so every difference telescopes along differences from these two transpositions. Each individual difference is alternating in the corresponding pair of arguments. This proves inclusion in the displayed set, and the converse follows by evaluating all three arguments at the same formal vector. The proof also works when two or three indices coincide and when the characteristic is two.

Put $U=V\oplus M$ and $W=V\oplus M$ with projections $\pi_U,\pi_W$ to $V$. Use the three based argument spaces
$$
(U\oplus A\oplus R_1),\qquad (W\oplus B\oplus R_2),\qquad
(V\oplus R_3),
$$
where $A$ and $B$ are copies of $V^*$ and each $R_i$ is a specified copy of $R$ of rank one. Treat the displayed direct summands as the parts for tensor isomorphism. Define the following six blocks and take all other blocks zero:
$$
\begin{array}{c|l}
\text{argument blocks}&\text{value}\\ \hline
U,W,V & t_f(x,y,z)+m(y,z)+l(x,z),\quad (x,m)\in U,\ (y,l)\in W\\
U,B,R_3&c\,\eta(\pi_U u)\\
R_1,B,V&s\,\eta(z)\\
A,W,R_3&c\,\xi(\pi_W w)\\
A,R_2,V&t\,\xi(z)\\
R_1,R_2,R_3&s t c .
\end{array}
$$
Here $\xi\in A$, $\eta\in B$, $s\in R_1$, $t\in R_2$, $c\in R_3$, and $z\in V$. Denote this partitioned tensor by $K_f$.

### Recover and lift a transporter

Suppose $K_f=K_g$ after invertible substitutions on the displayed parts. Write $S$ for the map on the third leg's $V$, $P,Q$ for the maps on $U,W$, and $\alpha_i\in R^\times$ for the map on $R_i$. The final block gives $\alpha_1\alpha_2\alpha_3=1$. The two blocks involving $B$ show that
$$
\pi_U P=(\alpha_1/\alpha_3)S\pi_U.
$$
Indeed their equations are $\alpha_3(B'\eta)(\pi_U Pu)=\eta(\pi_U u)$ and $\alpha_1(B'\eta)(Sz)=\eta(z)$, where $B'$ acts invertibly on the full dual $B$. The analogous two blocks involving $A$ give $\pi_W Q=(\alpha_2/\alpha_3)S\pi_W$.

Substitute $(x,0),(x,0),x$ in the main block, with $x$ formal. Each of the extra alternating forms vanishes because both of its evaluated vectors are scalar multiples of $Sx$. The equality is
$$
f(x)=\frac{\alpha_1\alpha_2}{\alpha_3^2}\,g(Sx)
    =g(\alpha_3^{-1}Sx).
$$
The recovered map is invertible and uses only the inverse of a witness unit.

Conversely suppose $f=g\circ h$. The difference
$$
t_f(x,y,z)-t_g(hx,hy,hz)=a(x)(y,z)+b(y)(x,z)
$$
has such a decomposition by (1). For $m\in M$ let $h_*m$ be the form with $(h_*m)(hv,hw)=m(v,w)$. Use the substitutions
$$
(x,m)\mapsto(hx,h_*(m+a(x))),\qquad
(y,l)\mapsto(hy,h_*(l+b(y)))
$$
on $U,W$, and use $h$ on the third $V$. On $A,B$ use the inverse dual of $h$ and on $R_1,R_2,R_3$ use identities. The main block gains precisely the displayed difference, and the evaluation blocks and scalar block are preserved. The substitutions are block triangular with invertible diagonals. The decomposition in (1) gives a direct coefficient algorithm to construct the shears.

The parts have counts $(3,3,2)$. The three total lengths are
$$
2n+\binom n2+1,\qquad 2n+\binom n2+1,\qquad n+1.
$$
Every operation in this first step uses only the original ring, irrespective of its characteristic.

## 2. Remove the partitions over an arbitrary commutative ring

The following procedure applies to any three-tensor on based free modules with prescribed direct-sum parts. Use coefficient arrays in this section. Transposing and inverting the argument maps when necessary converts between the two standard conventions for a transporter.

Let the first axis be $X=X_1\oplus\cdots\oplus X_a$, the second be $Y$, and the third be $Z$. Write their ranks as $p,m,\ell$. When $a=1$ no change is needed. Otherwise introduce $2a$ additional slices, ordered by their indices $j=1,\ldots,2a$. Each part $X_i$ has two indices, and let $i(j)$ be the part for index $j$. Set
$$
r_j=(p+m+1)2^{j-1}.
$$
For every $j$ add private row modules $Y_j$ and $I_j$ of ranks $m,r_j$, and private column modules $X'_j$ and $J_j$ of ranks $\operatorname{rank}X_{i(j)},r_j$. Embed each original slice in the $X,Y$ rectangle with every other entry zero. The new slice $D_j$ has three identity rectangles:
$$
(Y_j,Y),\qquad (X_{i(j)},X'_j),\qquad (I_j,J_j).
$$
All other entries in $D_j$ are zero. The first axis is now unpartitioned, and the new coordinates in each other axis lie in its last existing part. This defines one step of the reduction.

For the forward direction, extend a partitioned witness as follows. On the enlarged first axis use its original map on $X$, the inverse transpose of its map on $Y$ on each $Y_j$, and identities on the $I_j$. On the enlarged second axis use its original map on $Y$, the inverse transpose of its restriction to $X_{i(j)}$ on each $X'_j$, and identities on the $J_j$. On the enlarged third axis use its original map on $Z$ and fix the new slices. The three identities in each slice are preserved.

### Distinguish the added slices and recover the original maps

For the reverse direction let $(P,Q,L)$ be a witness for the enlarged tensors, where $P,Q$ act on rows and columns and $L$ combines the slices. Use the convention that the $k$th target slice equals $P$ times the $L_{k,*}$-combination of source slices times $Q^{\mathsf T}$.

First reduce the equations modulo an arbitrary maximal ideal of $R$. Over the residue field, the private rectangles of a slice combination with tag coefficients $\beta_j$ contribute exactly $\sum_{\beta_j\ne0}r_j$ to its rank. After removing these rectangles, the support lies in the union of the original rows $X$ and original columns $Y$, so its rank is at most $p+m$. Dividing rank by $p+m+1$ and taking the integer quotient reads the subset of tags in binary. A target data slice has quotient zero, and target tag $j$ has quotient $2^{j-1}$. Therefore the coefficient $\alpha_j=L_{\ell+j,\ell+j}$ of its own tag is nonzero in every residue field, and hence a unit in $R$. This uses only the nonzero ring case, since over the zero ring there is a unique array for each shape.

Next remove mixed tag coefficients over $R$ itself. The source combination for target $D_j$ contains a square invertible submatrix in rows $X_{i(j)},Y_j,I_j$ and columns $X'_j,Y,J_j$. In these orderings the submatrix is block triangular with diagonal entries $\alpha_j$ and a possible data rectangle in the $X_{i(j)},Y$ block. Let $s_j$ be its size. For any $h\ne j$, extend the submatrix by one corresponding row and column from the private block $I_h,J_h$. The enlarged minor is the unit determinant of the first submatrix times the coefficient $L_{\ell+j,\ell+h}$. The target $D_j$ factors through $R^{s_j}$. Every $(s_j+1)$-minor of its source combination also vanishes, since factorization through $R^{s_j}$ survives invertible row and column maps, and the Cauchy–Binet formula applies over a commutative ring. This forces the mixed coefficient to be exactly zero.

Each source combination for target $D_j$ now has the form $\alpha_jD_j+C_j$, where $C_j$ is supported in the original $X,Y$ rectangle. Use a simultaneous row shear $N$ fixing $X$ and all $I_j$ and having block $-\alpha_j^{-1}C_j$ from $Y_j$ to $X$, in addition to the identities. It is invertible and sends every $\alpha_jD_j+C_j$ to $\alpha_jD_j$. Replace $P$ by $P'=PN^{-1}$ while applying $N$ to the slice combinations. The new equations for the tags are
$$
P'(\alpha_jD_j)Q^{\mathsf T}=D_j.
$$
Since $\alpha_j$ is a unit, the column span of $D_j$, namely $X_{i(j)}\oplus Y_j\oplus I_j$, is preserved by $P'$ as an actual submodule. The row span, namely $Y\oplus X'_j\oplus J_j$, is preserved by $Q$ by transposing the equation. Intersect the two column spans for the duplicate tags for each part. Their intersection is exactly $X_i$, so $P'$ preserves each $X_i$ and $X$. Intersect the row spans of two distinct tags to see that $Q$ preserves $Y$. These conclusions also hold for the inverse maps.

For a target data slice the corresponding normalized source combination has row support in $Y$, since the target lies in the $X,Y$ rectangle and $Q^{-1}$ preserves $Y$. In particular it has no entries in any private tag rectangle $I_j,J_j$. The row shear fixes the entries there, which are its corresponding tag coefficient times an identity. Thus all tag coefficients in the data combinations vanish over $R$. The original-slice block $L_{11}$ is now invertible by block triangularity of $L$ with invertible diagonal tag block. As the row shear fixes the original data rectangles, the equations for the data slices give a transporter using the restrictions of $P'$ to $X$, of $Q$ to $Y$, and $L_{11}$ on $Z$. It preserves the original first-axis parts and inherits the other original partitions. This supplies explicit recovery in each direction.

One step produces shape
$$
\left(p+2am+\sum_j r_j,\ \ m+2p+\sum_j r_j,\ \ \ell+2a\right).
$$
Apply the procedure successively to each axis still carrying parts, permuting the axes between steps. The counts for the other axes stay fixed in each step. For a constant number of parts per axis the new lengths are linear in the original sum of lengths. Applied to $K_f$, this proves the asserted ordinary quadratic-side reduction. The final dense array has $O(n^6)$ entries. Construction of the array only places input coefficients, zeros, and signed identities. Transporter recovery, given matrices over the same ring, uses linear operations and inverses of units or supplied invertible matrices.

The two-tag intersections avoid needing full contraction span of the input. The only use of residue fields was to detect units in tag positions. The minors and the support comparisons then prove exact vanishing over $R$, including when the coefficient ring has nilpotents.

## 3. Compress the inert directions before encoding

There is a smaller instance when a characteristic-three cubic has many translation-invariant directions. Let $F$ be a field of characteristic three, let $T_f$ be the unnormalized complete polarization, and put $D=\operatorname{rad}T_f$. Write $c=\dim(V/D)$ and $e=\dim_{F^3} f(D)$. The dimension of the smallest linear quotient through which $f$ formally factors is exactly $c+e$.

Indeed, define the translation-invariant directions by the formal condition $f(x+sv)=f(x)$ in $x,s$. The coefficient of $s$ is $\frac12 T_f(v,x,x)$, so its vanishing implies $v\in D$ by polarizing in $x$, since $2$ is invertible. The coefficient of $s^3$ is $f(v)$. Conversely, for $v\in D$ the mixed coefficients vanish by the same polarized identities, so $f(v)=0$ suffices. Thus the intrinsic subspace to quotient by is $D_0=\ker(f|_D)$. In a basis on $D$, $f|_D$ is a sum of pure cubes. Applying coordinatewise Frobenius identifies its kernel with the kernel of the coefficient row acting $F^3$-linearly into $F$. Hence $\dim_F D_0=\dim_F D-e$. In a basis adapted to $D_0$, translation invariance means precisely that no monomial uses its coordinates. Every factorization through a linear quotient must kill only translation-invariant directions, which proves minimality.

For cubics on equally dimensional spaces, any equivalence descends to these quotients. Conversely an equivalence of quotients lifts by choosing complements and any isomorphism on the inert subspaces of equal dimension. Consequently one can first compare the two essential dimensions and then use the quadratic-side reduction on the quotient forms. This gives side length $O((c+e)^2)$ whenever linear algebra over $F^3$ and inverse Frobenius on $F^3$ are effective in the coefficient model. Over a perfect field $e\le1$. Over an imperfect field $e$ can reach $\min(\dim D,[F:F^3])$. The construction in Sections 1–2 uses no such extra coefficient operations or finiteness hypothesis.

For instance, over $\mathbb F_3(t)$ the pure cubes $x^3$ and $t x^3$ have zero complete polarization. They are inequivalent because the $t$-adic valuation of a cube is divisible by three. The ordinary output tensors retain that distinction. The same argument works with extra inert variables.

## 4. Precedents and priority

Grochow and Qiao use polarization to move from cubic polynomials to symmetric trilinear forms when the characteristic avoids two and three. Their STOC 2025 result gives a linear-length partition-to-ordinary gadget over fields. The present construction uses an arbitrary ordered lift and realizes its entire diagonal kernel by allowable shears. It retains the cubic itself and gives quadratic rather than linear side length. In good characteristic the earlier linear-length polarization route is stronger. [Grochow–Qiao, Part I](https://doi.org/10.1137/21M1441110) · [Grochow–Qiao, STOC 2025, Sections 1.3–1.4](https://doi.org/10.1145/3717823.3718282) · [Part IV full proof, Theorem 5.1](https://arxiv.org/html/2306.16317#S5)

Agrawal and Saxena reduce homogeneous equivalence to commutative algebra isomorphism over fields having the required scalar roots. Their cubic truncated quotient retains an order-$n^3$ dimensional space. The root-independent two-branch jet construction similarly uses cubic side length when passed through its multiplication tensor. The present construction gives an ordinary quadratic-side reduction directly and works over rings with nonunits and nilpotents. The polarization kernel in characteristic three is classical. The contributions shown here are the exact tensor use of ordered lift differences, the unit-based recovery over rings and the explicit bound on all three tensor sides. [Agrawal–Saxena, Theorem 2.3](https://www.cse.iitk.ac.in/%75sers/nitin/papers/cubic-forms.pdf) · [Drápal–Vojtěchovský](https://arxiv.org/abs/1509.05707)

Part V discusses why the field gadget has difficulties over general rings and proves a polynomial-length partition reduction in its diagonal-full framework. Our decoloring uses the field gadget's private ranks, with duplicated row supports and a determinantal argument using one unit minor and one extra entry. This produces a linear-length decoloring for a fixed number of parts over every commutative ring. The cited results establish the antecedent methods. Priority for the specific construction and general-ring claim remains unverified. [Grochow–Qiao–Stange–Sun, Part V, Sections 3.1–3.3 and Theorem 3.12](https://arxiv.org/html/2611.00735v1)

The companion [Tensor.py](Tensor.py) checks the alternating-shear decomposition for all 81 binary cubics and all 48 basis changes over $\mathbb F_3$. It also verifies unit tag cancellation in a $66\times65\times5$ example over $\mathbb Z/9$. A deliberately injected off-tag coefficient $3$ vanishes in the residue field, yet the appended minor equals $3$ modulo $9$. Placing the same coefficient in a data-slice combination leaves a nonzero entry in a private column. These controls exercise the two distinct exact vanishing arguments.
