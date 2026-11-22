# Special-linear tensor isomorphism over real closed fields

Let $K$ be any real closed field with its unique ordering. Complexity is measured in arithmetic operations and sign tests in $K$, with dense input tensors. The reductions output ordinary tensor-isomorphism instances over $K$ itself. We use independent changes in all three modes, with determinant one separately in each mode for $\mathrm{TI}_{\mathrm{SL}}$. The two statements below cover norm-balanced tensors with quadratic imaginary centroid, and all tensors with a mode of dimension two. [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

## 1. Norm-balanced tensors with quadratic imaginary centroid

**Theorem 1.** On nonzero norm-balanced tensors over $K$ whose centroid is isomorphic to $K[\mathrm i]$, where $\mathrm i^2=-1$, there is a deterministic polynomial-time many-one reduction $\mathrm{TI}_{\mathrm{SL}}\le_m\mathrm{TI}$. The promise is recognizable by polynomially many field operations and sign tests. The reduction computes no roots in $K$.

A tensor is norm-balanced if the three matrices of inner products of its slices, in the given standard coordinates, equal $(\|t\|^2/d_i)I_{d_i}$ in modes $i=1,2,3$. Here $\|t\|^2$ is the sum of the squares of its entries, and $d_i$ are its three dimensions. A nonzero norm-balanced tensor is concise, since all three matrices are invertible.

### The norm-balanced comparison

For norm-balanced $t,t'$, a general-linear transporter in the array convention $t'=(g_1\otimes g_2\otimes g_3)t$ implies
$$
 t'=\alpha(o_1\otimes o_2\otimes o_3)t,\qquad
 \det(o_i)=\operatorname{sgn}\det(g_i),\qquad
 \alpha=\prod_i|\det(g_i)|^{1/d_i}>0 .
 \tag{1}
$$
In particular $\|t'\|^2=\alpha^2\|t\|^2$. To prove this first over $\mathbb R$, take the polar decomposition in each mode. After taking out the displayed overall scalar, the positive factors have determinant one. Write these factors as $\exp(H_i)$ with $H_i$ symmetric of trace zero, and diagonalize each $H_i$ in an orthonormal basis. Put
$$
 F(s)=\left\|\bigotimes_i \exp(sH_i)t\right\|^2
     =\sum_I t_I^2 \exp(2s b_I), \qquad
 b_I=\sum_i (H_i)_{I_i I_i}.
$$
At $s=0$ the derivative is zero because the slice Gram matrices are scalar and each $H_i$ is traceless. At $s=1$ it is zero for the same reason: the vector there is an orthogonal change and scalar multiple of $t'$, so it is norm-balanced. If any $b_I\ne0$ has $t_I\ne0$, then $F''(s)>0$ throughout the interval, a contradiction. Thus the determinant-one positive factors fix $t$, proving (1). For each fixed format (1) is a first-order statement in the ordered field language: the roots in $\alpha$ are defined by positive solutions of equations $a_i^{d_i}=|\det(g_i)|$. Real closed field transfer gives (1) over $K$ without any analytic operation in the reduction. This is the norm-balanced tensor case of the minimum-vector principle. [Richardson and Slodowy, Minimum vectors for real reductive algebraic groups](https://doi.org/10.1112/jlms/s2-42.3.409)

Consequently special-linear equivalence of two norm-balanced tensors implies equal squared norms, and for equal norms the decision is exactly whether there is a general-linear transporter with all three determinant signs positive. If such a transporter exists, (1) produces an orthogonal one with all three determinants one. In the trilinear-form convention $t'(g_1x,g_2y,g_3z)=t(x,y,z)$, the corresponding array maps are $g_i^{-\mathsf T}$, with the same signs, so the conclusion is unchanged.

### Computing and comparing the complex orientations

Use the trilinear-form convention for the remainder of this proof. The centroid consists of triples of endomorphisms $C_i$ satisfying
$$
 t(C_1x,y,z)=t(x,C_2y,z)=t(x,y,C_3z).
$$
It is found by linear equations. Conciseness makes projection to any one endomorphism injective, and moving two commuting candidates through different slots proves that the centroid is a commutative algebra. Explicitly, if $C,D$ are two triples, transfer $C_1$ to the second slot and $D_1$ to the third in $t(C_1D_1 x,y,z)$, then move them back in the reversed order. This shows $C_1D_1=D_1C_1$ by conciseness, and likewise in the other modes. With this commutation, moving the product between any two slots gives closure under composition.

In a two-dimensional imaginary centroid, choose a nonscalar triple and subtract its scalar trace part, using its trace in one mode divided by that mode dimension. This gives a nonzero tuple $J=(J_i)$ with $J_i^2=-cI$ for one $c>0$. Indeed a nonscalar in $K[\mathrm i]$ has scalar part equal to its normalized trace in any module, and its traceless part has negative square. Conversely a centroid of dimension two with such a $J$ is the required field. This gives the stated polynomial recognition method. In each mode $d_i=2e_i$, and a frame
$$
                   v_1,J_iv_1,\ldots,v_{e_i},J_iv_{e_i}
$$
is found by adjoining one vector outside the current $J_i$-stable span at each step. Independence of its pair follows because every nonzero $aI+bJ_i$ is invertible. Define $\epsilon_i(t)$ to be the determinant sign of this frame in the standard coordinates. The sign is independent of the choices: a change of complex frame has real determinant the norm of its complex determinant, which is positive under the real ordering. For this proof one may set $J_i/\sqrt c$ equal to multiplication by $\mathrm i$, since the positive normalization does not change the frame orientation. The algorithm uses $J_i$ itself.

Any transporter conjugates the centroids, and preserves their common traceless lines. Hence for one $\lambda\in K^\times$,
$$
                  g_iJ_ig_i^{-1}=\lambda J_i'
                      \qquad(i=1,2,3).
$$
Transporting the paired frames from the source to the target gives
$$
 \operatorname{sgn}\det g_i
       =\epsilon_i(t)\epsilon_i(t')(\operatorname{sgn}\lambda)^{e_i}.
 \tag{2}
$$
When $e_i$ is even, the orientation discrepancy must be positive. When it is odd, (2) prescribes a sign for $\lambda$. Check the norms and these compatibility conditions, emitting a fixed ordinary negative instance if they fail. If no odd $e_i$ occurs and the checks pass, ordinary TI of the original pair suffices by (1) and (2).

Otherwise, let $\eta\in\{1,-1\}$ be the common required sign of $\lambda$. Add two named one-dimensional spaces $P,L$ to the tensor data. Attach the standard multiplication map $P\times P\to L$. For each mode attach a bilinear map $L\times V_i\to V_i$, given in the source by $(s,x)\mapsto sJ_ix$ and in the target by $(s,x)\mapsto \eta sJ_i'x$. An isomorphism of the named data must act on $L$ by the square of its nonzero scalar on $P$. The remaining equations say $g_iJ_ig_i^{-1}=\eta a^2 J_i'$ for that scalar $a$. This implies exactly the prescribed sign, and every transporter of the prescribed sign extends because every positive element of $K$ is a square. The standard linked-block compilation of named spaces, bilinear maps and a trilinear form gives a single ordinary TI pair with polynomial overhead over the same field. Its use here requires only these linked bilinear maps and scalar labels. [Grochow and Qiao, Part IV](https://arxiv.org/abs/2306.16317) · [Linked linear data and ordinary tensor encoding](https://github.com/Dugongue/MathProofs/blob/main/TISLPencilsAndOrbits/Encoding.md)

For unbounded examples take $t(X,Y,Z)=\operatorname{Re}\operatorname{tr}(XYZ)$ on three copies of $\operatorname{Mat}_k(K[\mathrm i])$. In the given real basis $(E_{ab},\mathrm iE_{ab})$, each slice has $2k$ entries equal to $1$ or $-1$, and distinct slices in the same mode have disjoint supports. Thus the tensor is norm-balanced. Nondegeneracy of $\operatorname{Re}\operatorname{tr}(XY)$ converts the centroid equations to $C_1(X)Y=XC_2(Y)$ and $C_2(Y)Z=YC_3(Z)$. Setting arguments to the identity shows that all three maps are multiplication by a single central matrix, giving precisely $K[\mathrm i]$. For odd $k$, conjugating only the first mode gives an ordinarily equivalent balanced tensor with no special-linear transporter, since (2) requires incompatible signs in the three modes.

## 2. All matrix pencils over a real closed field

**Theorem 2.** For all positive $a,b$, special-linear tensor isomorphism of $2\times a\times b$ tensors over $K$ has a deterministic polynomial ordered-arithmetic decision algorithm. In particular it reduces by a same-field many-one reduction to ordinary TI. The algorithm includes singular and rectangular pencils.

Write $P(v)=v_1 A+v_2 B$. The action is
$$
          Q(v)=L P(Mv) R,\qquad
 M\in\operatorname{SL}_2(K),\
 L\in\operatorname{SL}_a(K),\
 R\in\operatorname{SL}_b(K).
 \tag{3}
$$
An equivalence at fixed $M$ with arbitrary invertible side maps is a strict equivalence. We first preprocess the strict Kronecker decompositions into the regular square part and the singular summands. These decompositions and their uniqueness are the customary Kronecker theory of two arrows. [Ja’Ja’, An addendum to Kronecker’s theory of pencils](https://doi.org/10.1137/0137052) · [Pervouchine, Hierarchy of closures of matrix pencils](https://jolt.centre-mersenne.org/articles/10.5802/jolt.345/)

### Splitting singular blocks with field operations

For each singular block $S_j$ of format $(j+1,j)$ and its transpose, with $j\le a+b$, compute $\operatorname{Hom}(S_j,P)$ and $\operatorname{Hom}(P,S_j)$ as spaces of strict two-arrow intertwiners. The block $S_j$ is multiplication by $v$ from $\operatorname{Sym}^{j-1}K^2$ to $\operatorname{Sym}^jK^2$ for $j\ge1$. Its endomorphisms are scalar. For on degree-$(j-1)$ basis monomials $b_i=x^{j-1-i}y^i$, an endomorphism $U$ of the source of such an intertwiner satisfies $x U b_{i+1}=y U b_i$. Therefore $x^{j-1}$ divides $U b_0$, making $U$ scalar on all basis monomials. The two arrow equations then determine the same scalar on the target. The zero-index and transpose cases give the same conclusion.

The block is a direct summand precisely when the composition of some pair of members of those two Hom spaces is nonzero. It is enough to try basis pairs by bilinearity. Rescale the projection so that this composition is the identity, and split the kernel of that projection as complement using linear algebra in each vertex. Repeat to exhaustion for each block type. By Kronecker decomposition the leftover is regular. All sizes of the linear equations and all repetition counts are polynomial. This computes actual changes of basis in the two fixed pencils without factoring polynomials.

For $M\in\operatorname{SL}_2(K)$, the substitution on a tall block can be restored by
$$
 S_j(v)=\big(\operatorname{Sym}^{j}M\big)^{-1}
            S_j(Mv)\operatorname{Sym}^{j-1}M .
$$
All displayed side determinants are one, because $\det(\operatorname{Sym}^{u}M)=(\det M)^{u(u+1)/2}$. Transposition gives the wide case and the zero-index case is immediate. Hence only equal singular block lists need be compared, and arbitrary candidate slice maps in $\operatorname{SL}_2(K)$ preserve these lists. Write the fixed decomposition as $P=A_P\widehat P B_P$ and $Q=A_Q\widehat Q B_Q$, with the singular summands in identical order. The side determinant multipliers that undo these fixed decompositions are
$\delta_L=\det A_Q/\det A_P,\ \delta_R=\det B_Q/\det B_P$.

### Strict determinant profiles

The strict stabilizer's determinant pairs form the subgroup generated by the following sources.

- A tall or wide singular block of index $j$ contributes $t\mapsto(t^{j+1},t^{-j})$ or $t\mapsto(t^{j},t^{-(j+1)})$, respectively, with $t\in K^\times$.
- If the regular part is nonzero, it contributes every $(t,t^{-1})$ with $t>0$. It also contributes $(-1,-1)$ exactly when the regular part has some odd-size Jordan block for a real eigenvalue in a regular affine chart.

To justify accounting for all inter-block maps, the endomorphism algebra of a direct sum of Kronecker indecomposables maps onto a product of matrix algebras over the local residue fields of its isotypic components. In a same-type block discard the local radical, and discard all different-type blocks. A composite from an indecomposable through a different type back to itself is a nonunit, since an invertible composition would split the initial indecomposable off the other. This proves multiplicativity of the reduction. The kernel is nilpotent: in a sufficiently long summand path some isomorphism type is visited repeatedly, and each loop returning to that type belongs to its local nilpotent radical. The concatenated loops then vanish. Units lift through the nilpotent kernel, whose units act with determinant one. Thus the determinant profile is the product of the profiles of the isotypic components. Singular types have scalar residue field and give the stated exponents, since the right factor is the inverse of the source-vertex module map.

For the regular part, normalize at an invertible slice and use the matrix $Y$ in its affine chart. The two determinants are inverse to each other. Positive values are arbitrary by positive rescaling on the regular part. Nonreal conjugate primary parts have positive determinants, since conjugate complex determinants multiply to a positive norm. On a real generalized eigenspace, with nilpotent part $N$, use
$\operatorname{gr}_j=\ker N^j/\ker N^{j-1}$.
The injections $N\colon\operatorname{gr}_{j+1}\to\operatorname{gr}_j$ make the determinant of a commutant equal to the product of its determinants on $\operatorname{gr}_j/N(\operatorname{gr}_{j+1})$, each raised to the exponent $j$. This follows by taking determinants through the filtration and iterating the displayed injections. These quotients are the multiplicity spaces of size-$j$ chains. Thus even sizes give positive signs and an odd size allows sign change by negating one chain. To detect odd sizes, compute the invariant factors of $Y$ in Frobenius form, squarefree-decompose them by multiplicity using derivatives and gcds, and use Sturm signs at infinity to test whether any odd-multiplicity factor has a real root. This uses polynomial field arithmetic and sign tests. [Storjohann, Deterministic computation of the Frobenius form](https://doi.org/10.1109/SFCS.2001.959911)

The positive part and the sign part of this subgroup can be tested independently, since $K^\times=\{\pm1\}\times K_{>0}^\times$. The sign part is a subgroup of $\{\pm1\}^2$ generated by these contributions. For the positive part, the positive elements form a divisible group. In rank two the two-row exponent matrix has surjective positive image, by solving with the adjugate of a rank-two submatrix and taking positive roots. In rank one it is the one-dimensional subgroup cut out by $x^v y^{-u}=1$ for any nonzero column $(u,v)$, and in rank zero it is the identity. These are polynomial tests by repeated squaring. When there are both regular and singular parts the rank is two, because the regular vector is $(1,-1)$ and a singular column has coordinate sum $1$ or $-1$.

### Finding the slice map in fixed semialgebraic dimension

If the regular parts vanish, try $M=I$: all other determinant-one slice substitutions are absorbed on the singular blocks with determinant-one side maps. Test the fixed determinant pair $(\delta_L,\delta_R)$ against the above strict profile. If regular parts are present their sizes must agree, say with size $n$. Choose an evaluation $v_0$ at which the regular part of $Q$ is invertible. Among $v_0=(1,i)$ with $0\le i\le n$ at least one works. Fix $v_1$ independent of $v_0$. At a candidate $M$, abbreviate the regular evaluations by $P_i=P_{\mathrm{reg}}(Mv_i)$, $Q_i=Q_{\mathrm{reg}}(v_i)$, and require $\det P_0\ne0$. The regular strict equivalence is equivalent to
$$
                  X(M)=P_0^{-1}P_1\sim Y=Q_0^{-1}Q_1 .
 \tag{4}
$$
Indeed a similarity $X(M)R_r=R_r Y$ gives $L_r=Q_0R_r^{-1}P_0^{-1}$. The product of the two physical side determinants of this strict transporter is $\delta_L\delta_R\det Q_0/\det P_0$. When there are no singular blocks require this product to be one. The individual positive magnitudes can then be corrected by the regular part. When there are singular blocks, the positive part of the profile is all of $(K_{>0}^\times)^2$, so no additional magnitude equation is needed.

There is a polynomial-size semialgebraic formula in a fixed number of variables for (4). Universally quantify a complex scalar $z=u+\mathrm i v$ with two real coordinates. Test equality of the ranks over $K[\mathrm i]$ of $(X(M)-zI)^j$ and $(Y-zI)^j$ for $1\le j\le n$, for every $u,v$. These ranks encode the exact Jordan sizes for every eigenvalue, hence similarity over the algebraic closure $K[\mathrm i]$. That implies similarity over $K$ as invariant factors are unchanged by extension of fields. Clear the denominators in the ranks using $\det P_0$, and represent the complex matrices by real matrices of twice the size. For a real matrix $Z$, the coefficient of $T^j$ in $\det(I+T Z^\mathsf T Z)$ is the sum of squares of its $j$-minors. Thus these coefficients recover the rank without listing exponentially many minors. Their polynomial degrees and number are polynomial, and computing them by interpolation uses polynomially many operations because the variables are the four entries of $M$, $u,v$, and the auxiliary $T$. This gives a formula with a fixed number of variables and polynomial data, together with $\det M=1$, the invertible evaluation, and any required determinant product equation.

Use fixed-dimensional real quantifier elimination and semialgebraic sampling to obtain a sample in each semialgebraically connected component of the feasible locus of $M$. Equivalently one can sample cells of a cylindrical decomposition compatible with that locus. These algorithms over a real closed field take polynomially many ordered field operations for a fixed number of variables and produce polynomial-degree algebraic point representations. [Basu, Pollack and Roy, Quantifier elimination](https://doi.org/10.1145/235809.235813) · [Basu, Pollack and Roy, Algorithms in real algebraic geometry, Chapters 10–11 and 14–16](https://doi.org/10.1007/3-540-33099-2)

On that locus the coset of the strict transporter signs is locally constant. To see this at any $M$, take an invertible solution of $X(M)R_r=R_rY$. The solution dimension is constant throughout (4), equal to the centralizer dimension of $Y$. Choose a full-rank pivot minor in the linear system, hold the free coordinates fixed at their chosen values, and solve by that pivot near $M$. The dependent equations hold by the constant rank. This gives a continuous solution with unchanged determinant sign near $M$. The other side map and the singular block corrections are continuous as well. All strict transporters at the same $M$ differ by the fixed strict determinant subgroup, so the coset is well-defined and locally constant. The sign-coset classes are semialgebraic, because they are expressible by existence of side maps with one of a finite set of signs. This use of definability requires no algorithm in a growing number of matrix variables. A locally constant semialgebraic class is constant on a semialgebraically connected component, including over non-Archimedean real closed fields.

At each sample compute a similarity and its basis change by Frobenius form. Sign tests and arithmetic at an algebraic sample can be performed in its real univariate representation, using the selected root's Thom signs. For an inversion of a value nonzero at that root, remove from the squarefree defining polynomial the gcd with the operand and use extended Euclid modulo the remaining polynomial. The selected root is retained. Arithmetic and sign determination in this description have polynomial overhead in the representation degrees, without a root oracle. Transport back using the fixed decomposition and test the resulting sign pair against the strict sign subgroup. The locus was selected for possible positive-magnitude correction. Thus some sample passes if and only if (3) has a solution. This is a deterministic polynomial ordered-arithmetic decision algorithm. Emit fixed ordinary positive or negative instances over $K$ according to its result.

One sign-sensitive example is $P(x,y)=xI+yJ$ and $Q(x,y)=xI-yJ$ for $J=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$. Both have determinant form $x^2+y^2$. Any determinant-one slice map respecting this form is in $\operatorname{SO}_2(K)$, and its effect on $P$ is left multiplication by a complex scalar of norm one. Thus a special-linear witness would have to conjugate $J$ to $-J$ by a positive-determinant real matrix. Every such complex-antilinear matrix is $\left(\begin{smallmatrix}u&v\\v&-u\end{smallmatrix}\right)$, with negative determinant if invertible. Hence this pair has an ordinary transporter and fails special-linear equivalence.

An inline exact control checked 120 symmetric-power identities on singular blocks, 630 diagonal and off-diagonal slice Gram conditions for the imaginary matrix-multiplication examples of sizes $1,2,3$, and all 24 invertible complex-antilinear matrices in the integer box $[-2,2]^4$.

## Scope

The earlier moment-profile work uses the minimum-vector perspective and studies what density and marginal data retain. The balanced argument here uses the classical minimum-vector comparison to control only the magnitudes. The additional imaginary-centroid readout supplies the signs, which are then encoded by the scalar square map. An earlier determinant-character construction already treats certain odd-size three-slice tensors over real closed fields. The pencil result here uses fixed-variable semialgebraic sampling and sign propagation on the strict similarity locus. [Doğan, Sakabe and Walter, Convex optimization on moment polytopes](https://arxiv.org/abs/2609.06633) · [Earlier three-slice determinant characters](https://github.com/Dugongue/MathProofs/blob/main/TISLPencilsAndOrbits/Groups.md)

The first theorem uses a quadratic imaginary centroid to turn orientation into a scalar square condition inside ordinary tensor isomorphism. The second covers all pencils by a fixed-dimensional search and real determinant profiles. Pervouchine treats the literal three-factor special-linear action over $\mathbb C$, and earlier work in this series treats all pencils over finite fields. The real-closed decision theorem includes the real signs and does not require enumerating slice transformations or choosing eigenvalues. These are prose proofs on the stated classes. They leave the unrestricted reverse reduction open. [Pervouchine](https://jolt.centre-mersenne.org/articles/10.5802/jolt.345/) · [Earlier finite-field pencil theorem](https://github.com/Dugongue/MathProofs/blob/main/TISLPencilsAndOrbits/Pencils.md) · [Chen et al., Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)
