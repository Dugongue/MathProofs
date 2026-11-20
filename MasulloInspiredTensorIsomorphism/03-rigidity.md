# Spectral refinement for balanced three-tensor isomorphism

**Theorem.** Let $A,B$ be nonzero, rational, explicitly given three-tensors of the same format $(d_1,d_2,d_3)$, with positive dimensions. Give each mode its standard Euclidean form. Assume that on each mode of each tensor the flattening Gram matrix is a scalar multiple of the identity. If one input passes the commuting mixed-moment test below, deterministic time polynomial in the input bit length suffices to decide whether the tensors are isomorphic under $\mathrm{GL}_{d_1}(\mathbb R)\times\mathrm{GL}_{d_2}(\mathbb R)\times\mathrm{GL}_{d_3}(\mathbb R)$ and to construct an exact transporter in factored algebraic form when one exists. The test succeeds on an explicit infinite set of pairwise nonisomorphic rational $8\times 8\times 8$ tensors. At the base tensor of the construction, every one-mode Gram matrix is scalar and every crossed quartic operator has repeated eigenvalues.

This is an informal proof for an effectively recognizable class of balanced inputs and for real transporters. The joint eigenspace criterion replaces simple ordinary Gram spectra, which are used by the exact algorithm in the [smoothed orthogonal and unitary isomorphism proof](https://github.com/Dugongue/MathProofs/blob/main/SmoothedOrthogonalUnitaryTI/Proof.md). That proof addresses a different input class. The bit complexity below uses [Basu, Pollack and Roy, *Algorithms in Real Algebraic Geometry*](https://doi.org/10.1007/978-3-662-05355-3).

Masullo's draft chooses a function-space topology from the geometric calculation, then asks which spectral evaluations the resulting topology retains. In the finite tensor setting, the contraction formulas give a computable family of test operators and the joint spectrum test certifies that all eigenlines are distinguishable. Masullo sets aside Weil's positivity criterion in §1.7.2. The positivity argument in §1 below is an independent convexity calculation in the tensor orbit. [Masullo, *The Music of the Primes*, §§1.4.8 and 1.7.2](https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=35).

## 1. Balance reduces real general-linear equivalence to orthogonal equivalence

Write $s_T=\|T\|_F^2$ and $T^0=T/\sqrt{s_T}$. Balance means that the mode-$i$ Gram matrix of $T$ equals $(s_T/d_i)I$. If $A$ and $B$ are real general-linear isomorphic, their normalized tensors are as well, since an overall scalar can be absorbed in the first factor.

Suppose that $B^0=(G_1\otimes G_2\otimes G_3)A^0$. In the polar decomposition factor each $G_i$ as $O_iP_i$ with $O_i$ orthogonal and $P_i$ positive definite and symmetric. Write $P_i=e^{c_i}e^{H_i}$ with $c_i=(\log\det P_i)/d_i$ and $H_i$ symmetric and traceless. For $x(t)=(e^{tH_1}\otimes e^{tH_2}\otimes e^{tH_3})A^0$, set $f(t)=\|x(t)\|_F^2$. Both $x(0)=A^0$ and $x(1)=e^{-\sum_i c_i}(O_1^t\otimes O_2^t\otimes O_3^t)B^0$ are balanced. At each of these endpoints,
$$
f'(t)=2\sum_i\operatorname{tr}\bigl(H_i\,x(t)_{(i)}x(t)_{(i)}^t\bigr)=0
$$
by the tracelessness and balance. Here $x(t)_{(i)}$ denotes the mode-$i$ flattening as a matrix with the $i$th index on the row side.

In orthonormal eigenbases for the $H_i$, write $a_{\ell mn}$ for the coefficient of $A^0$ and $\lambda_{\ell mn}$ for the corresponding sum of three eigenvalues. Then
$$
f'(1)-f'(0)=\sum_{\ell,m,n}2\lambda_{\ell mn}(e^{2\lambda_{\ell mn}}-1)|a_{\ell mn}|^2.
$$
Each summand is nonnegative and vanishes only when $\lambda_{\ell mn}=0$ or $a_{\ell mn}=0$. Hence $x(1)=A^0$. Unit normalization gives $e^{\sum_i c_i}=1$, so $B^0=(O_1\otimes O_2\otimes O_3)A^0$. Conversely such an orthogonal transporter gives a real general-linear transporter for the original tensors by multiplying $O_1$ by $\sqrt{s_B/s_A}$.

## 2. Construct the mixed-moment operators

On mode 1 define a crossed quartic operator for a normalized real tensor $X$ by
$$
C_1(X)_{ab}=\sum_{c,p,q,r,u}X_{apq}X_{bru}X_{cpu}X_{crq}.
$$
Define $C_2,C_3$ cyclically. These matrices are symmetric by relabeling $p,r$ and $q,u$. Every internal index occurs twice, so orthogonal changes in any mode cancel on internal indices. Accordingly $C_i((O_1\otimes O_2\otimes O_3)X)=O_iC_i(X)O_i^t$. Set $X=T^0$. Then $C_i(X)=C_i(T)/s_T^2$ is rational.

Let $(i,j,k)$ run through the three cyclic mode orders. Use the following finite ordered family on mode $i$, beginning with $C_i=C_i(X)$ and then listing pairs $(r,u)$ lexicographically:
$$
 C_i,\qquad
 M_{i;r,u}=X_{(i)}\bigl(C_j^r\otimes C_k^u\bigr)X_{(i)}^t\quad(0\le r<d_j, 0\le u<d_k).
$$
The columns of $X_{(i)}$ use the indicated order $(j,k)$. Each matrix is symmetric and orthogonally equivariant. Its entries are rational since the two factors $X_{(i)}$ contribute a total divisor of $s_T$. The associated test requires pairwise commutation in each mode and that all joint eigenspaces in that mode are one-dimensional.

The range of powers is sufficient to synthesize all partial contractions against spectral projectors of $C_j$ and $C_k$, over $\mathbb R$. Indeed the projector onto any distinct eigenvalue is a Lagrange polynomial in its operator of degree less than the dimension. The algorithm uses the rational mixed powers directly.

For a given mode, write its ordered family as $F_0,\ldots,F_{m-1}$, and form $L(t)=\sum_{h=0}^{m-1}t^hF_h$. Reject the commutation part if any commutator is nonzero. Commuting real symmetric matrices admit a simultaneous orthonormal eigenbasis. If every joint eigenspace is one-dimensional, the eigenvalue difference for each two basis lines, viewed as a polynomial in $t$, is nonzero of degree at most $m-1$. Thus among the $(m-1)\binom{d_i}{2}+1$ integers from $0$ to $(m-1)\binom{d_i}{2}$, one produces simple spectrum. Conversely a repeated joint eigenlabel forces repeated eigenvalues for every $L(t)$. Select the first such integer $t$ using the characteristic polynomial and its derivative. This implements the test, and the selection respects all orthogonal changes of basis.

## 3. Exact transporter and bit complexity

Apply the test to both normalized inputs. If only one passes, they have different orthogonal orbits and hence different real general-linear orbits. If both pass, the chosen integers and the three characteristic polynomials must coincide for an orthogonal isomorphism. Compare them, and reject mismatches. In each mode, any orthogonal isomorphism must then send the increasing-order eigenlines of the first chosen matrix to the matching lines of the second.

Choose an oriented unit eigenvector for each line. Denote the normalized tensor coefficients in these eigenbases by $a_{\ell mn}$ and $b_{\ell mn}$. Test $a_{\ell mn}^2=b_{\ell mn}^2$ for every triple. For each nonzero coefficient, let $\eta_{\ell mn}=0$ when the signs agree and $\eta_{\ell mn}=1$ when they differ. Solve over $\mathbb F_2$ the system
$$
x_\ell+y_m+z_n=\eta_{\ell mn}\quad\text{for every occupied position }(\ell,m,n).
$$
A solution defines the matched eigenline maps with signs $(-1)^{x_\ell}$, $(-1)^{y_m}$, $(-1)^{z_n}$. Their tensor product maps one normalized input to the other by the coefficient tests, including all positions where both coefficients vanish. Conversely all orthogonal transporters induce solutions by the matching of eigenlines. This proves exactness.

For the bit bound, the raw rational matrices have constant-degree contractions in the explicit number of tensor entries. The highest powers in the mixed operators and in the integer mixtures are polynomial in the input dimensions. Clearing common denominators before taking powers bounds all numerator and denominator bit sizes polynomially. Characteristic polynomials, rational commutators, simple-root tests, and rational isolating intervals for the real roots are computed in bit-polynomial time.

At each simple eigenvalue $\lambda$, choose the first nonzero column of the adjugate of $L-\lambda I$ as an oriented eigenvector $v$. Its entries are evaluations of univariate rational polynomials of polynomial degree and coefficient bit size, obtainable by interpolation of minors. The column exists since the nullity is one. Divide by the positive square root of $v^tv$ to normalize it. A single normalized core entry has the sign of a contraction of the original rational tensor with three such unnormalized $v$'s. Its squared value is the square of that contraction divided by $s_T$ and the three squared norms. Therefore a sign or squared equality test uses at most six real algebraic root parameters. Each parameter has its defining polynomial and isolating interval, and the needed tests are polynomial sign tests in a fixed number of real variables after clearing positive denominators. Fixed-dimensional real algebraic decision algorithms give bit-polynomial cost. The binary linear system has at most $d_1d_2d_3$ rows. The output represents each orthogonal factor as the sum of corresponding signed outer products of the oriented unit eigenvectors, with defining polynomials and isolating intervals for the eigenvalues. This format and the additional factor $\sqrt{s_B/s_A}$ have polynomial length.

## 4. A signed XOR example and a rational family

Index each mode by $0,\ldots,7$ under bitwise XOR $\oplus$. Put $T_{a,b,a\oplus b}=\sigma(a,b)$ and set all other entries to zero. The rows of $\sigma$, with signs listed in increasing $b$, are

```text
-+---+-+
++++--+-
--+----+
+--+--++
+--+-+-+
+--+---+
---+----
-+-+++++
```

All three unnormalized Gram matrices are $8I$. The support forces $C_i(T)$ to be diagonal. For example in the first mode a nonzero term for $a,b$ requires the two other slices to have a common first coordinate $c$, and the XOR equations imply $a\oplus b=c\oplus c=0$. More explicitly, for the three cyclic orders, set $S_1(a,b)=\sigma(a,b)$, $S_2(a,b)=\sigma(a\oplus b,a)$, and $S_3(a,b)=\sigma(b,a\oplus b)$. If $q_i(a)$ is the diagonal entry in mode $i$, then
$$
 q_i(a)=\sum_{c,b=0}^7 S_i(a,b)S_i(a,b\oplus a\oplus c)
                  S_i(c,b)S_i(c,b\oplus a\oplus c).
$$
It follows that every mixed-moment matrix is diagonal, since a fixed pair of indices on the column side belongs to a single mode-$i$ row of the flattening. The same diagonal conclusion holds with arbitrary real weights on the XOR support.

For each mode $i$, let $r_i(v)$ be the zero-based rank of $q_i(v)$ among its distinct values in increasing order. Compute the table of quartic diagonals and the residues
$$
 h_i(a) = \sum_{b=0}^7 9^{\,8r_j(b)+r_k(a\oplus b)}\pmod{65537},
 \qquad (i,j,k)\text{ cyclic}.
$$

| Mode | Quartic diagonal $q_i(0),\ldots,q_i(7)$ | Residues $h_i(0),\ldots,h_i(7)$ |
| --- | --- | --- |
| 1 | $16,-8,0,16,0,8,24,8$ | $59868,43947,31399,41065,64279,17506,57840,36654$ |
| 2 | $-8,0,8,16,24,0,16,8$ | $36057,28929,31506,33084,31064,16965,43470,38077$ |
| 3 | $0,0,8,24,0,8,0,24$ | $42659,49502,30765,60812,15214,21665,26455,37912$ |

For a pair of spectral projectors in the other modes, the unnormalized weighted marginal diagonal entry at $a$ counts the $b$'s with those two spectral labels at $b$ and $a\oplus b$. The residues in the table are weighted sums of these counts. Distinct residues within each row imply distinct profiles of projector contractions. Each projector contraction is in the real span of mixed powers, up to the common normalization factor. The mixed operators thus have distinct joint labels at all eight positions, even though each initial quartic diagonal has repeats.

There is an infinite rational family passing the same test. For a rational parameter $t>0$ sufficiently small, put
$$
 r(t)=\frac{1-t^2+2t}{1+t^2},\qquad
 s(t)=\frac{1-t^2-2t}{1+t^2}.
$$
In the sign table, multiply the magnitudes in the rows and columns $\{0,1\}$ by $r(t)$ on the diagonal and by $s(t)$ off the diagonal. In the separate subtable on rows and columns $\{2,3\}$ reverse these two roles. Keep every sign and all other magnitudes unchanged. Each affected row or column receives one $r(t)^2$ and one $s(t)^2$, summing to $2$. The XOR labels $0$ and $1$ each receive two $r(t)^2$ and two $s(t)^2$ across the two subtables. Hence all three Gram matrices remain $8I$. All operators still commute as diagonal matrices. For each mode take a fixed integer mixture that has simple spectrum at $t=0$. For sufficiently small $t$ the eigenvalues of this mixture remain distinct by continuity, so the test succeeds. The coordinate lines are always the recovered joint eigenlines. A real general-linear isomorphism between any two members would yield an orthogonal transporter as above, acting by signed permutations on those lines. The maximum absolute entry $r(t)$ varies strictly near $0$, so distinct sufficiently small positive rational parameters give distinct real general-linear orbits.
