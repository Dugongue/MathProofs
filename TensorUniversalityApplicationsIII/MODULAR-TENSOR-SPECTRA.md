# The exact modular threshold for forgetting tensor symmetries

Let $K$ have characteristic $p>0$. Fix order $d\ge2$ and a partition $\Pi$ of the tensor positions. Positions in one block use the same vector space. A block-symmetric tensor is invariant under permutations within each block. A tied restriction uses one linear map per block, repeated at all its positions. An ordinary restriction uses independent maps. Both terms allow singular and rectangular maps.

The semiring operations are direct sum and positionwise tensor product, with tensors identified under mutual restriction in their respective preorders. Write $D_r=\sum_{i=1}^r e_i^{\otimes d}$ for the diagonal. A **spectral point** is a normalized monotone semiring homomorphism to $\mathbb R_{\ge0}$, with $D_r$ sent to $r$. This definition does not require that the preorder satisfy Strassen's domination axiom.

**Theorem 1.** Forgetting the ties induces a surjective pullback from ordinary spectral points to tied spectral points exactly when either every block has size less than $p$ or $d=p$. In the exceptional case of one full order-$p$ block, the pullback is surjective even though some nonzero tensors have tied subrank zero at every tensor power. Whenever a block has size at least $p$ and $d>p$, an explicit flattening invariant after a Frobenius collapse gives a tied spectral point outside the image.

**Theorem 2.** Let $d=p$, with every position in one block, and let $T$ be a symmetric tensor. Suppose $K$ is algebraically closed, finite, or perfect with $p\in\{2,3\}$. Write $D_T(x)=T(x,\ldots,x)$ for diagonal evaluation on the dual space. If $D_T=0$, the tied subrank of $T^{\otimes n}$ is zero for every $n\ge1$. If $D_T\ne0$, the asymptotic tied subrank equals the ordinary asymptotic subrank. More precisely, for nonsimple $T$ there is a fixed $c$ such that
$$
 Q_{\Pi}(T^{\otimes(n+c)})\ \ge\ 1+\left\lfloor\frac{Q(T^{\otimes n})}{p-1}\right\rfloor\qquad(n\ge1).
$$
Here $Q$ and $Q_{\Pi}$ are the largest $r$ for which the respective restriction to $D_r$ exists, and their asymptotic versions are the exponential growth rates over tensor powers. The same bound holds over any perfect field of characteristic $p$ when $T$ is nonsimple and some tied power of $T$ restricts to $D_2$.

This addresses the asymptotic-spectrum direction of [Grochow–Qiao Open Question 7.5](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full). Christandl–Fawzi–Ta–Zuiddam prove the full-symmetry spectrum and subrank transfers over algebraically closed fields in characteristic greater than the order, with characteristic zero included. The earlier blockwise argument uses nonvanishing multinomial counts to discard labels. Here retaining the labels, and compensating a rank-one defect with mixed-orbit tensors, handles the first case where that count vanishes. [Christandl–Fawzi–Ta–Zuiddam, §§3–4](https://arxiv.org/html/2104.01130v2) · [Earlier blockwise symmetry transfer](https://github.com/Dugongue/MathProofs/blob/main/TensorUniversalityApplicationsII/TENSOR-SYMMETRY-TRANSFER.md)

## 1. Retaining the permutation labels

For a block of size $s$, set
$$
H_s=\sum_{\sigma\in S_s} e_{\sigma(1)}\otimes\cdots\otimes e_{\sigma(s)}.
$$
Let $H_\Pi$ be the product over blocks, with the positions assembled in their original order. These tensors are nonzero in every characteristic because each displayed label word appears once.

Suppose block-symmetric tensors satisfy $T\longrightarrow U$ by ordinary maps $A_i$. In one block, apply the tied map $x\otimes e_i\mapsto A_i(x)\otimes e_i$. For each permutation of labels the data in that term is $U$. Indeed, permuting the maps in the block is the same as permuting the resulting data and the original input is invariant. Both tensors are block-symmetric, so the result is unchanged. Thus
$$
T\otimes H_\Pi\longrightarrow_\Pi U\otimes H_\Pi.
$$
This identity uses neither averaging nor division. If a tied spectral point $\phi$ satisfies $\phi(H_\Pi)>0$, multiplicativity and cancellation give $\phi(T)\ge\phi(U)$ for every ordinary restriction. In particular $\phi$ is well defined on the image of the tied tensor semiring inside the ordinary tensor semiring, and there it is monotone for the ordinary preorder. The extension theorem for spectral points applies to that image subsemiring inside the ordinary Strassen preorder. It extends $\phi$ to an ordinary spectral point. [Zuiddam, *Asymptotic spectra*, Corollary 2.17](https://ir.cwi.nl/pub/28021/Thesis_J_Zuiddam)

If every block has size less than $p$, sending each label to $1$ gives $H_\Pi\longrightarrow_\Pi (\prod_{B\in\Pi}|B|!)D_1$. The coefficient is nonzero. Its scalar tensor is invertible for the semiring product, with the reciprocal scalar tensor as inverse. Its value under any spectral point is therefore positive. This proves the first sufficiency statement in Theorem 1 over every field of the given characteristic.

## 2. Rank-one compensation at order $p$

Now take one block of size $p$. For vectors $x,y$ in any target space, put
$$
C(x,y)=(x+y)^{\otimes p}-x^{\otimes p}-y^{\otimes p}.
$$
For each $1\le j<p$, map $p-j$ of the labels of $H_p$ to $x$ and the other $j$ to $y$. Each placement of the $j$ copies of $y$ has $(p-j)!j!$ preimages. That scalar is a unit in $K$. Scaling one label by its reciprocal normalizes every placement because all labels occur once in each word. Scaling it by the negative reciprocal gives the negative of that placement sum. Thus each of $C(x,y)$ and $-C(x,y)$ is a tied restriction of $p-1$ direct copies of $H_p$. The argument also works when $x,y$ are dependent, by composing this construction on two formal basis vectors with a linear map.

Let $u_i=e_1+\cdots+e_i$. Telescoping gives
$$
D_m = u_m^{\otimes p}-\sum_{i=2}^m C(u_{i-1},e_i).
$$
The first term comes from $D_1$ under the map $1\mapsto u_m$. Each other term uses $p-1$ more copies of $H_p$. The repeated linear map can have overlapping images on the distinct summands, since the input direct sum has no mixed summand terms. We have proved the exact family of restrictions
$$
D_1\oplus\bigoplus_{i=1}^{(p-1)(m-1)} H_p
\longrightarrow_\Pi D_m.
\tag{1}
$$
At $m=2$, monotonicity gives $2\le 1+(p-1)\phi(H_p)$. Hence $\phi(H_p)>0$. Section 1 now proves the exceptional surjectivity in Theorem 1. The argument only invokes the spectral extension theorem on the ordinary image semiring. In characteristic $p$ the tied preorder need not itself satisfy the usual domination axiom.

## 3. A new spectral point above the threshold

Suppose a tied block has at least $p$ positions and $d>p$. Reorder positions to select its first $p$ positions. On a coordinate presentation define a tensor with $d-p+1$ positions by
$$
R(T)_{i,j_{p+1},\ldots,j_d}=T_{\underbrace{i,\ldots,i}_{p\text{ times}},j_{p+1},\ldots,j_d}.
$$
If a tied map has matrix $A$ in those positions, the first output mode of $R(T)$ is acted on by the matrix $A^{[p]}$ of entrywise $p$th powers. The other output modes use their original maps. To verify this, expand the coefficient in which all $p$ selected output indices are equal. Rotate the $p$ input indices cyclically. The source coefficient and all matrix weights are constant on each orbit because the source is invariant under that rotation and the selected output row is repeated. Every orbit has size $p$ except the constant index words. Nonconstant words contribute zero in characteristic $p$. A constant word contributes the corresponding matrix coefficient to power $p$. This proves the stated formula, including for noninvertible maps. It also shows basis changes do not affect the flattening ranks of $R(T)$.

The construction commutes with direct sum and with positionwise tensor product, as seen by applying the selected coefficient rule on direct-sum indices and on paired tensor-product indices. Since there are at least two remaining modes after the selected positions are collapsed to one, the first flattening rank of $R(T)$ is additive, multiplicative and monotone under tied restriction. Also $R(D_r)$ is the diagonal of the reduced order and its first flattening rank is $r$. This gives a normalized tied spectral point. It sends $H_\Pi$ to zero because the selected positions in $H_\Pi$ have distinct indices. Every ordinary spectral point is at least one on $H_\Pi$, since an ordinary restriction reads off one nonzero term and produces $D_1$. The constructed point cannot extend to the ordinary semiring. This completes the exact classification.

## 4. From one visible diagonal to two tied diagonal entries

Assume from now on order $p$, full symmetry, and a perfect ground field. Write $T$ as a multilinear form on the dual. Expanding $T(x,\ldots,x)$, all mixed types vanish because cyclic rotation acts freely on the nonconstant words of length $p$. Thus $D_T$ is a sum $\sum_i a_i x_i^p$. If every $a_i=0$, the same is true of every tensor power: its diagonal coefficients are products of those of $T$. This proves the zero case in Theorem 2. Otherwise perfection gives $D_T=\ell^p$ for a nonzero linear functional $\ell$. A vector with $\ell=1$ supplies an exact tied restriction to $D_1$.

Suppose $T$ is nonsimple. Over an algebraically closed ground field, fix an integer $1\le j<p$ and consider
$$
P_j(x,y)=T(x^{p-j},y^j)
$$
on the affine product $\ell(x)=\ell(y)=1$. In this expression the exponents count the number of repeated input vectors. If the polynomial were constant there its value would be one by taking $x=y$. Homogeneity in the two groups would give the polynomial identity $P_j(x,y)=\ell(x)^{p-j}\ell(y)^j$. Comparing coefficients recovers all entries of $T$, since the two multinomial factors have totals $p-j$ and $j$, both less than $p$. All of those factors are units. The identity would force $T$ to be the pure tensor of $\ell$, contrary to nonsimplicity. Thus $P_j$ is nonconstant and has a zero on that affine product. To see existence directly, choose the other affine coordinates so that the polynomial still has positive degree in one coordinate, then use algebraic closedness in that coordinate.

For $p=2$ or $p=3$ the same zero-pair conclusion holds over any perfect field. It is enough to handle $j=1$, since interchanging $x,y$ handles $j=p-1$. For fixed $x$ the expression is affine linear in $y$. If it has no zero on the affine product, then for every $x$ this linear expression is constant on $\ell(y)=1$, and its value is one at $y=x$. The resulting function identity is a polynomial identity because each individual affine coordinate has degree at most $p-1$ and the field has at least $p$ elements. This follows by successive univariate root bounds. Homogenizing in $x,y$ gives the same pure tensor contradiction as before.

For each $j$ take a zero pair $(x_j,y_j)$ with both $\ell$ values equal to one. Put $X=\bigotimes_{j=1}^{p-1}x_j$ and $Y=\bigotimes_{j=1}^{p-1}y_j$. The two tied output coordinates of $T^{\otimes(p-1)}$ with rows $X,Y$ have pure values one. A mixed evaluation with exactly $j$ copies of $Y$ contains the zero factor $P_j(x_j,y_j)$. Therefore every mixed coefficient vanishes, giving an exact tied restriction to $D_2$.

## 5. The two-entry restriction over all finite fields

Now let $K=\mathbb F_q$ with $q=p^e$. The argument for $P_1$ in Section 4 gives $x,v$ with $\ell(x)=1$, $\ell(v)=0$, and $T(x^{p-1},v)\ne0$ for every prime $p$. Indeed, if all these evaluations vanished, then $P_1(x,y)=1$ on the normal affine product, and its degree in each affine coordinate is less than $q$. Interpolation and homogenization would again make $T$ simple.

Fix $1\le j<p$ and set $U=T(x^{p-j},-^j)$, a $j$-linear symmetric form. It has $U(x^j)=1$ and $U(x^{j-1},v)\ne0$. If $U$ is simple then $U=c\psi^{\otimes j}$ with $\psi$ not proportional to $\ell$. Choose $y$ with $\ell(y)=1$ and $\psi(y)=0$. For $j=1$ this always handles the problem. We now show how to find the required mixed zero in a tensor power whenever $j\ge2$ and $U$ is nonsimple.

### Diagonal directions for the lower-order form

We first show that powers of $U$ have arbitrarily large tied diagonal restrictions. Quotient its common radical in the covector domain. The quotient has dimension at least two by nonsimplicity, and one-mode flattening rank equals that dimension. Its $t$th tensor power has mode rank equal to its full dimension because flattening ranks multiply. For some $t$ the dimension $b$ of this concise power exceeds $j$. Its diagonal polynomial $f$ has degree at most $j$. The number of zeros in $K^b$ is divisible by $p$: in the field sum $\sum_z(1-f(z)^{q-1})$ the first term sums to zero, and every monomial of the second part has total degree less than $b(q-1)$. Some coordinate therefore has exponent less than $q-1$, whose powers sum to zero on $K$, including exponent zero. Since $f(0)=0$, there is a nonzero isotropic vector. Include it in a basis of the covector domain. Its pure coefficient vanishes, but some coefficient using it is nonzero by conciseness.

The maximum-multiplicity table construction in Section 6 now extracts a nonzero scalar multiple of $H_j$ from a fixed power. The construction only uses one basis letter whose pure coefficient vanishes and which occurs in a nonzero type. Normalize by scaling the image of one designated output basis label, which appears once in each word of $H_j$. Ordinarily $H_j$ restricts to $D_2$: at position $i$ retain labels $i$ and $i+1$ modulo $j$. A selected label word is a permutation exactly when every position makes its first choice or every position makes its second choice. The retained-label argument gives $H_j\otimes H_j\longrightarrow_\Pi D_2\otimes H_j$ at order $j$. Send all last tag labels to $1$, scaling one designated label by $1/j!$, to produce $D_2$ itself. This is possible since $j<p$. Powers of this restriction supply any requested diagonal size from a fixed power of $U$.

### A mixed zero with the correct normalization

Choose one such power $U^{\otimes m}$ with a tied $D_r$ restriction, for $r\ge p q(p-1)e$. On the $r$ row vectors realizing it, write $\ell_m=\ell^{\otimes m}$ and let $a_i$ be their values under $\ell_m$. The row vectors are independent since the diagonal has full one-mode rank. Put $M=(p-1)e$. Either $M$ rows have $a_i=0$, or at least $pM$ rows share one nonzero value. In the first case those $M$ individual rows give suitable directions in $\ker\ell_m$. In the second case take disjoint groups of at most $p$ rows from the repeated value. Choose $t_0\in\mathbb F_p$ with $t_0^j\ne t_0$, which exists because $2\le j<p$. In each group take the combination with one coefficient $t_0$ and $p-t_0$ coefficients $1$, using the standard representative of $t_0$. It has $\ell_m$ value zero, and its $U^{\otimes m}$ pure value is $t_0^j-t_0\ne0$. Disjoint groups have zero mixed evaluations since the original restriction was diagonal. In both cases there are $M$ directions $w_i$ in $\ker\ell_m$ for which the leading form on their span is $\sum_i b_i z_i^j$ with all $b_i\ne0$.

Take $Y_0$ with $\ell_m(Y_0)=1$. Evaluate $U^{\otimes m}$ on $j$ repetitions of $Y_0+\sum_i z_i w_i$ to obtain a polynomial $F(z)$ with leading form $L(z)=\sum_i b_i z_i^j$. If $F$ had no zero over $K$, then $F^{q-1}$ would be the constant-one function. Reduce its polynomial by the relations $z_i^q=z_i$. There is a monomial in $L^{q-1}$ of total degree $j(q-1)$ whose exponents are all less than $q$. To see it, partition the $M$ variables into $e$ groups of size $p-1$, and in group $h$ use exponent $jp^h$. In
$$
L^{q-1}=\prod_{h=0}^{e-1}\left(\sum_i b_i^{p^h}z_i^{jp^h}\right)^{p-1}
$$
its coefficient is nonzero: uniqueness of base-$p$ digits prescribes one occurrence of each variable in its own group, and $(p-1)!$ is a unit in each factor. Every exponent is less than $q$ since $j<p$. The monomial survives reduction with that coefficient. A reduction of any exponent at least $q$ strictly lowers total degree, and other terms of $F^{q-1}$ outside the leading part already have smaller total degree. The reduced polynomial is therefore not constant. Interpolation contradicts its being the constant-one function. Consequently there is a vector $Y$ in $\ell_m=1$ with $U^{\otimes m}(Y^j)=0$.

This gives a mixed zero for $T^{\otimes m}$ on the pair $x^{\otimes m},Y$, both with normal value one. Choose such a pair in some power for each $j$. Tensor the pairs as in Section 4. The combined power still has both pure evaluations one and every mixed evaluation zero. This proves the $D_2$ restriction over every finite field.

The mixed-zero points can first appear in a power. Over $\mathbb F_5$, take the symmetric binary tensor with coefficient $1$ in weights $0$ and $4$, and zero in all other weights. On $x=(1,s),y=(1,t)$ the mixed polynomial $P_2$ is $1+3s^2t^2+2s^3t$. At $s=0$ it is one. For $s\ne0$, set $u=t/s$ and use $s^4=1$ to get $1+3u^2+2u$, whose discriminant is a nonsquare. On the second tensor power, $x=(1,1)$ gives contraction matrix $\left(\begin{smallmatrix}1&1\\1&3\end{smallmatrix}\right)$ on the remaining two positions. Its Kronecker square has zero quadratic value at $(1,0,2,1)$, giving a normal-one mixed zero.

## 6. Extracting the catalyst and comparing subranks

Here is a direct proof that a nonsimple symmetric order-$p$ tensor over a perfect field with nonzero diagonal has $H_p$ as a tied restriction of some fixed power. Use a dual basis in which $\ell$ is the first coordinate. All pure diagonal coefficients vanish except that first one. Since the tensor is nonsimple, some nonzero coefficient involves a different basis letter $z$. Choose a nonzero type with the maximum number $b$ of occurrences of $z$ among all nonzero coefficients. Then $1\le b<p$.

Make a table whose rows are all distinct permutations of one word of this type, with $p$ columns and $L$ rows. The columns are distinct basis words in the coefficient space of $T^{\otimes L}$. Retain exactly these columns as the input basis on every mode. A selection of $p$ distinct columns yields a permutation of the chosen type in every row, and hence the same nonzero product coefficient. If a column is repeated, choose a row placing $z$ in that repeated column and in enough other selected columns to yield at least $b+1$ occurrences of $z$, counting multiplicity. If fewer than $b$ distinct columns were selected, put $z$ in all of them and in extra unused columns. Such a row exists because all permutations are present. The resulting product coefficient vanishes by maximality of $b$. The restricted tensor is therefore a nonzero scalar multiple of $H_p$. Scale one output label by the reciprocal scalar, since that label appears exactly once in every word. The same construction at any order only requires a letter with zero pure coefficient that occurs in a nonzero type. This is the support-extraction argument of [Christandl–Fawzi–Ta–Zuiddam, Lemma 3.9](https://arxiv.org/html/2104.01130v2#S3.SS2).

Let $T^{\otimes a}\longrightarrow_\Pi D_2$. For nonsimple tensors over the fields of Theorem 2, Sections 4 and 5 supply such an $a$. Then $T^{\otimes(a+L)}$ restricts to $H_p\oplus D_1$: multiply the $D_2$ restriction by the $L$th power and use $H_p$ on one summand and $D_1$ on the other. If $T^{\otimes n}\longrightarrow D_r$ ordinarily, the retained-label map on the first branch gives $D_r\otimes H_p$, a direct sum of $r$ copies of $H_p$. On the second branch use $T^{\otimes n}\longrightarrow_\Pi D_1$. Apply (1) to obtain the claimed finite bound with $c=a+L$. Taking exponential rates proves equality with the ordinary asymptotic subrank. If $T$ is simple and nonzero, both rates are one because both kinds of restriction to $D_1$ exist and every flattening rank stays one.

A nonzero $H_p$ itself has identically vanishing diagonal, so it cannot restrict to $D_1$ even after taking powers or adding any number of direct copies. Yet every normalized tied spectral point is the restriction of an ordinary spectral point by Theorem 1 and therefore has value at least one on $H_p$. Thus the spectral infimum fails to recover unassisted tied asymptotic subrank in this modular semiring.

## Verification

The full tensor and spectral arguments are written above. The Lean companion checks finite-fiber cancellation in characteristic $p$, vanishing of mixed binomial coefficients, and telescoping of the rank-one defects. The finite replay checks 1,427 compensation coefficients, 840 Frobenius collapse identities under rectangular tied maps over $\mathbb F_4$ and $\mathbb F_9$, 524 exact extractor coefficients over $\mathbb F_2$ and $\mathbb F_3$, and the mixed-zero example over $\mathbb F_5$. Historical priority remains open.
