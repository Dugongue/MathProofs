# Exceptional regular pencils under the special-linear tensor action

## Theorem

Let $K=\mathbf F_q$ be represented as a prime field or by a polynomial basis over its prime field. Let $A,B\colon K^2\to\operatorname{Mat}_n(K)$ be regular pencils, each given by its two coefficient matrices. Suppose each has a rational nonsingular direction and each geometric determinant divisor has at most two distinct points. For any $(\delta_L,\delta_R,\delta_O)\in(K^\times)^3$, a deterministic algorithm with running time polynomial in the bit length decides whether there are
$$
(P,G,H)\in \operatorname{GL}_2(K)\times\operatorname{GL}_n(K)^2
$$
such that
$$
B(Pw)G=H A(w)\quad(w\in K^2),\qquad
(\det P,\det G,\det H)=(\delta_L,\delta_R,\delta_O).
$$
The special-linear action on the three tensor factors corresponds to $(1,1,1)$. Changing between tensor and bilinear map conventions uses inverse transposes on the appropriate factors and preserves determinant one. Thus the algorithm gives a same-field many-one reduction on this class by outputting the two one-entry tensors $(1,1)$ or $(1,0)$ according to the answer.

For $n>0$ the geometric determinant divisor of a regular square pencil has at least one point. If it has at most two, the rational nonsingular direction exists automatically, since $\mathbf P^1(K)$ has at least three points. The algorithm below can find it by testing at most three distinct directions on this class. A regular pencil of dimension zero is vacuous in the matrix modes and imposes only the determinant conditions stated for trivial zero-dimensional groups.

## Fixed-label strict equivalence and its determinant group

Pick a nonsingular source slice $A_0=A(w_0)$ and an independent direction $w_1$. Set $C=A_0^{-1}A(w_1)$. For a proposed invertible label $P_0$, set $B_0=B(P_0w_0)$. A singular $B_0$ rejects the label. Otherwise set $D=B_0^{-1}B(P_0w_1)$. The two slice equations are strictly equivalent precisely when $D$ and $C$ are similar. Given an invertible $G_0$ with $DG_0=G_0 C$, take
$$
H_0=B_0G_0 A_0^{-1}.
$$
A deterministic Frobenius form algorithm gives a similarity matrix in polynomially many field operations and zero tests. [Storjohann, *Algorithms for Matrix Canonical Forms*, Chapter 9](https://cs.uwaterloo.ca/~astorjoh/diss2up.pdf).

At label $I_2$, the stabilizer of the source pencil consists of
$$
(G,H)=(X,A_0 X A_0^{-1}),\qquad X\in C_{\operatorname{GL}_n(K)}(C).
$$
Let $e$ be the gcd of the positive exponents of the elementary divisors of $C$. The determinant image of this strict stabilizer is
$$
(1,c,c),\qquad c\in (K^\times)^e.
$$
Here is a proof valid in all characteristics. Regard $K^n$ as a $K[t]$-module with $t$ acting by $C$. An automorphism respects each primary summand $M_f=\bigoplus_j(K[t]/(f^j))^{m_{f,j}}$ for $f$ irreducible. Write $E_f=K[t]/(f)$. The quotient $f^k M_f/f^{k+1}M_f$ has one $E_f$-coordinate for each summand of length $j>k$. A map from length $j$ to length $\ell>j$ lands in $f^{\ell-j}$ times the target and hence contributes zero to each such layer. The action on the layer is thus block triangular in the lengths, and its diagonal block $U_{f,j}$ is the reduction modulo $f$ of the length-$j$ diagonal block, independently of $k<j$. The automorphism determinant is
$$
\det X=\prod_{f,j} N_{E_f/K}(\det_{E_f}U_{f,j})^j.
$$
Any collection of invertible $U_{f,j}$ lifts to a block-diagonal automorphism, because the quotient maps from the local rings $K[t]/(f^j)$ detect units. Finite-field norms are surjective by cyclicity. The products of all such norm powers are exactly the $e$-th powers.

Compute $e$ from the squarefree multiplicities of the invariant factors of $C$. This uses derivatives and gcd, with recursive $p$-th root extraction for the derivative-zero part in characteristic $p$. Each coefficient $p$-th root is exponentiation to $q/p$, as all computations are over $\mathbf F_q$. Over an algebra containing a particular root, block counts at that root can alternatively be computed from the successive nullities of $(C-\lambda I)^j$, $0\le j\le n$. The first difference counts the blocks of length at least $j$, and subtracting successive first differences gives the number of blocks of each exact length. The exponent $e$ is unchanged by finite extension because an irreducible polynomial is separable and each of its linear factors retains the same exponent.

## Reducing to the pointwise projective root stabilizer

Use affine coordinates $z$ on the source and target projective label lines with a rational nonsingular direction at infinity in each. Let $f_A,f_B$ be the monic squarefree parts of the affine determinant polynomials. The univariate determinants can be computed by polynomial Gaussian elimination over $K(z)$ with gcd reduction to keep degrees bounded, or by the division-free computation of the characteristic polynomial of the normalized slice $C$. A rational transporter must carry the geometric singular directions of the source to those of the target. Consequently one can reject unequal geometric point counts or unequal Frobenius types.

For a single root, which is rational, choose the affine translation from the source root to the target root as $P_0$. For each matching of two roots compatible with Frobenius, choose the unique affine map carrying both roots to their respective targets. These baseline maps are in $\operatorname{GL}_2(K)$ after choosing the affine bottom row $(0,1)$ and returning to original coordinates. For two roots the algorithm represents these baselines in a degree-at-most-four algebra.

Consider a fixed choice of matching. Every label inducing it has the form $P_0 S$, where $S$ fixes each source root individually. The formulas in the following sections show that every such $S$ has a lift to an automorphism of $A$. Therefore a transporter inducing the matching exists only if $P_0$ itself passes the strict equivalence test. Once a fixed-label witness $(P_0,G_0,H_0)$ exists, all witnesses inducing the matching are precisely its products with the source automorphisms whose labels fix each root. This follows by multiplying triples componentwise. The target determinant triple belongs to this coset precisely when its componentwise ratio to $(\det P_0,\det G_0,\det H_0)$ belongs to the source stabilizer determinant group described below.

## Symbolic baseline maps and arithmetic

For two split roots let $R_A=K[t]/(f_A)$ and $R_B=K[u]/(f_B)$. In $R_A\otimes_K R_B\cong K^4$, the other roots $t',u'$ are computed by subtracting $t,u$ from the corresponding sums of roots. The slope and intercept of the baseline affine map are
$$
s=(u-u')/(t-t'),\qquad h=u-st.
$$
Both differences are units, and all possible matchings occur in this calculation. The same algebra also supplies the two ordered source roots for the nullity computations determining their block data.

For nonsplit quadratic roots, form $R=E_A\otimes_K E_B$, with $E_A=K[t]/(f_A)$ and $E_B=K[u]/(f_B)$ the quadratic fields. In this case set $t'=t^q,\ u'=u^q$ in $R$. Both differences are again units, and $s,h$ are fixed by the $q$-power map, since interchanging both pairs leaves the slope and intercept unchanged. The $K$-subalgebra generated by $s,h$ is split, with dimension at most four. Its coordinates describe all Frobenius-compatible matchings. Compute a basis for this subalgebra by linear-algebra closure under multiplication by $s,h$. The nonsplit root block counts can be computed over $E_A$ separately and are independent of which root is chosen.

In a split coefficient algebra, test the witnesses and determinant conditions by doing field arithmetic simultaneously in every coordinate. To branch on a zero test, decompose the current algebra as the kernel and image of multiplication by the element being tested. The image is the factor where the element is nonzero, the kernel the factor where it is zero. Project all current data accordingly. Inversions are made only on summands where the input is a unit, by linear algebra. The resulting branches are the usual field computations coordinatewise. Their positive dimensions sum to at most four, so the procedure has polynomial bit cost without identifying or enumerating the field projections. Taking $q$-th powers has polynomial cost by repeated squaring.

## One geometric root

After a label-basis change and invertible row and column changes, the pencil has the form $A(x,y)=xI+yN$ with $N$ nilpotent, so the only root is $x=0$. Indeed one may choose the nonsingular direction as the first coordinate and the root direction as the second. This changes the source automorphism group by conjugation in the three groups and preserves its determinant image. For each nilpotent block of length $j$ use the model $K[t]/t^j$, with multiplication by $t$ as $N$. Write $E=\sum_j m_j\binom j2$.

The label matrix fixing $x=0$ has the form $S=\begin{pmatrix}a&0\\b&d\end{pmatrix}$, with $a,d\ne0$. In every block let $G_S$ act by substitution
$$
g(t)\longmapsto g\bigl(dt/(a+bt)\bigr).
$$
Its diagonal in the ascending monomial basis is $1,d/a,\ldots,(d/a)^{j-1}$, so it is invertible. The identity
$$
\bigl((a+bN)^{-1}dN\bigr)G_S=G_SN
$$
follows by applying multiplication by $t$ before substitution. Thus $H_S=(aI+bN)G_S$ provides an automorphism with label $S$. Its determinant triple is $(ad,(d/a)^E,a^n(d/a)^E)$. All other lifts for the same $S$ differ by strict source automorphisms. The full determinant image is therefore the image on $K^\times$ of the integer monomial matrix whose columns are
$$
(1,-E,n-E)^\mathsf T,\quad (1,E,E)^\mathsf T,\quad (0,e,e)^\mathsf T.
$$

## Two split geometric roots

A choice of order gives canonical coordinates for the two singular lines. Strict equivalence makes the pencil block diagonal of the form
$$
 (xI+yN_1)\ \oplus\ (yI+xN_2),
$$
where both $N_i$ are nilpotent. To see this, use the primary decomposition of $C$ at the two rational eigenvalues. The slice at the other root is invertible on each block, so it can be normalized to the identity. The ratio of the two slices is nilpotent at the block's own root. In particular the length data can be read from the nullities of the original normalized slice at its two eigenvalues. Changing the normalized slice by a fractional linear coordinate change maps the corresponding nilpotent variable to a nonzero linear coefficient times it plus higher powers. The kernels of all powers remain identical in dimension.

Write $n_i$ for the dimensions and $E_i$ for the sums of $\binom j2$ over the block lengths of the two summands, and set $E=E_1-E_2$. In these coordinates the pointwise label stabilizer consists of $\operatorname{diag}(a,b)$, $a,b\ne0$. The preceding substitution in the first summand uses $t\mapsto (b/a)t$, and in the second it uses $t\mapsto (a/b)t$. The lifts have blockwise output normalizations $a$ and $b$, respectively. Their determinant triples are
$$
(ab,(b/a)^E,a^{n_1}b^{n_2}(b/a)^E).
$$
Adjoin the independent strict contribution $(1,c,c)$ for $c\in(K^\times)^e$. The full determinant image has columns
$$
(1,-E,n_1-E)^\mathsf T,\quad(1,E,n_2+E)^\mathsf T,\quad(0,e,e)^\mathsf T.
$$

## Two quadratic-conjugate geometric roots

Work over the quadratic field $E_K/K$, with nontrivial automorphism $\sigma$. Over $E_K$ choose conjugate root direction vectors as a label basis, so that Galois acts by conjugation and swapping both coordinates. The primary subspaces for the two eigenvalues are exchanged by $\sigma$. Choose strict normalizing bases for one primary block and use their conjugates for the other one. This gives the preceding block forms over $E_K$ with $n_1=n_2=m=n/2$ and $E_1=E_2$. The $K$-rational pointwise label group in these coordinates consists precisely of $\operatorname{diag}(a,\sigma(a))$, $a\in E_K^\times$, since a diagonal matrix commutes with conjugation-and-swap exactly in this form.

Use the split blockwise lifts over $E_K$. The substitution constants are $\sigma(a)/a$ in the first block and its conjugate in the second. The row normalizations $a,\sigma(a)$ are also conjugate. The combined maps commute with the Galois action in the original coordinates and have entries in $K$. The determinant triples are therefore $(N(a),1,N(a)^m)$, where $N=N_{E_K/K}$. Since this norm is onto, the entire determinant image, including strict automorphisms, has columns
$$
(1,0,m)^\mathsf T,\quad(0,e,e)^\mathsf T.
$$

## Membership and bit complexity

For any integer matrix $M$ in the preceding cases, membership in its multiplicative image $(K^\times)^k\to(K^\times)^3$ is tested using a Smith normal form $UMV=D$ with integer unimodular $U,V$. Apply the row monomial map $U$ to the required determinant ratio. For every nonzero diagonal entry $d_i$, the associated coordinate must be a $d_i$-th power, which is equivalent to its power $(q-1)/\gcd(d_i,q-1)$ being $1$. Every zero row must have coordinate $1$. Unimodular transformations act invertibly on the finite multiplicative groups, which proves both directions of this test. The integers used to build $M$ are bounded by $O(n^2)$, and the fixed-size integer transformations and powers have polynomial bit cost. The tests require neither discrete logarithms nor integer factorization.

Computing the squarefree parts, root types, companion normal forms, and nilpotent lengths takes polynomially many field operations and polynomially many bit operations on small integers and exponents. The coefficient fields or algebras used for the at most two roots have dimension at most four over $K$, so the symbolic computations preserve the polynomial bound. For recognition, one may compute a binary determinant by a univariate characteristic-polynomial computation when an invertible slice exists and reject outside the class. Testing three distinct directions suffices to find an invertible slice or reject the promise for $n>0$. This proves the theorem.

## Control and broader pencil assembly

For a nonsplit nonsemisimple example let $K=\mathbf F_7$, $C$ be the companion matrix of $(t^2+1)^2$, $A(x,y)=xI+yC$, and $B(x,y)=\operatorname{diag}(3,1,1,1)A(x,y)$. The coefficients are over the input field, the two singular directions are conjugate and nonrational, and the elementary exponent gcd is $2$. Ordinary tensor isomorphism is witnessed by the output twist. But $\det A(x,y)=(x^2+y^2)^2$, so $\det B(Pw)$ is a nonsquare constant times a nonzero square polynomial for every invertible $P$. It cannot equal $\det A(w)$, as determinant-one row and column maps would force. Unique factorization in $K[x,y]$ proves this square-class obstruction.

For rectangular pencils with Kronecker blocks, the following determinant lifts provide the singular contribution to an exceptional-root test. A positive minimal-index block of size $(j+1)\times j$ can be written as $v\mapsto wv$ from $\operatorname{Sym}^{j-1}(K^2)$ to $\operatorname{Sym}^j(K^2)$. Every $S\in\operatorname{GL}_2(K)$ lifts as
$$
(G,H)=(\operatorname{Sym}^{j-1}S,\operatorname{Sym}^j S).
$$
Indeed multiplication in the symmetric algebra commutes with the action of $S$. The determinants are $(\det S)^{j(j-1)/2}$ and $(\det S)^{j(j+1)/2}$. For this determinant formula one may triangularize $S$ over the algebraic closure and multiply the diagonal eigenvalue monomials of each symmetric power, an argument valid in every characteristic. Transposed blocks lift with inverse transposes in reverse order, giving the two negative exponents in reverse order. Minimal-index-zero blocks have an identity lift on their sole nonzero mode. Direct sums add the exponent pairs, and the resulting contribution to the regular determinant lifts is a power of the label determinant in each matrix mode. With no regular blocks, every label $S$ has such a lift and every nonzero label determinant can occur. Combining these lifts with strict equivalence and the entire strict stabilizer determinant image gives the corresponding rectangular assembly.

The general reverse reduction remains [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5). Verification here is an informal proof. An independent exhaustive check enumerated the label and domain matrices for dimension-two nilpotent, split, and nonsplit examples over $\mathbf F_2,\mathbf F_3,\mathbf F_5,\mathbf F_7$. The computed groups agreed with the determinant formulas in all 12 cases. Bibliographic priority is unverified.
