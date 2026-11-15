# Recovering matched anchors from low-degree rank-one equations

Informal proof. Over each fixed finite field there is a deterministic polynomial-time algorithm that starts from raw coordinates and computes the exact determinant coset for a recognizable class of square concise 3-tensors. It extracts a rank-one frame and constructs a compatible short anchor list without enumerating frame permutations. The class contains an explicit growing family with scalar pair adjoints in every pair of modes, scalar full stabilizer, and an absolutely irreducible determinant pencil depending essentially on every slice coordinate.

Write the slice presentation as $M:U\to\operatorname{Hom}(X,Y)$ with $\dim U=\dim X=\dim Y=n$. All coordinates are over $F=\mathbb F_q$. For transporters use $M'(fv)=hM(v)g^{-1}$, where $f,g,h$ act on $U,X,Y$, respectively. The covariant tensor presentation inverts determinants on dualized modes. Identity determinants agree in either convention.

## Recover a rank-one frame from polynomial equations

Let $x_1,\ldots,x_n$ be the raw slice coordinates. For a fixed integer $D\ge q$, compute the span of all monomial multiples of the $2\times2$ minors of $M(x)$ and the field equations $x_i^q-x_i$ whose total degrees are at most $D$. Let $J_1$ be its intersection with homogeneous linear forms, and put $H=J_1^\perp\subset U$. This is polynomial time for fixed $D,q$, using explicit polynomials and Gaussian elimination. Every rank-one slice direction lies in $H$. The spaces $J_1,H$ are intrinsic. Cauchy–Binet gives equality of the minor spans under invertible row and column actions, and an invertible $F$-linear substitution maps the field equations to linear combinations of field equations. Substitution preserves the total-degree bound and expands monomials into linear combinations of allowed multipliers.

Suppose $M|_H$ consists, in hidden frames, of independently supported diagonal rank-one maps. Precisely, $\dim H=m=n-c$ and there is a basis $u_i$ of $H$ with $M(u_i)=y_i\lambda_i$, for independent $y_i\in Y$ and independent $\lambda_i\in X^*$. In the hidden $u_i$ coordinates the minors on $H$ span exactly the quadrics $a_i a_j$ for $i\ne j$. This follows by extending the $y_i,\lambda_i$ to bases and using Cauchy–Binet.

To extract the hidden lines, use coordinates in any computed basis of $H$. Pair quadratic coefficient vectors with the upper-triangular entries of symmetric $m\times m$ matrices so that $vv^{\mathsf T}$ pairs with a quadric by evaluation at $v$. This convention works in characteristic two. The annihilator of the computed minor quadrics is
$
\mathcal D=\left\{\sum_{i=1}^m d_i u_i u_i^{\mathsf T}:d_i\in F\right\}.
$$
Compute a basis $D_1,\ldots,D_m$ of $\mathcal D$. Over an extension with more than $2m^3+2$ elements, scan $D(t)=\sum_{j=1}^m t^{j-1}D_j$. Each hidden coefficient $d_i(t)$ is a nonzero polynomial of degree at most $m-1$. At most $m(m-1)$ values prevent invertibility. Having selected an invertible $D(t_0)$, choose $t_1$ so that the ratios $d_i(t_1)/d_i(t_0)$ are pairwise distinct. Each forbidden equality is a nonzero polynomial of degree at most $m-1$, because $d_i,d_j$ are independent linear functionals. The stated field size suffices.

The matrix $D(t_1)D(t_0)^{-1}$ has the $u_i$ lines as its eigenspaces. To extract them, scan the extension field for eigenvalues and solve linear equations. Each eigenspace is defined over $F$, so normalizing its first nonzero coordinate gives a base-field vector. Construct the extension by scanning irreducible polynomials of degree $O(\log n)$. Its cardinality and the search are polynomial at fixed $q$. The algorithm checks that the symmetric annihilator has dimension $m$, that the found eigenspaces are distinct lines defined over $F$, and that these form a basis of $H$ of rank-one slices with independent output lines and input-dual lines. With these checks, the list contains all rank-one lines on $H$, and the bounded-degree calculation certifies that every rank-one line of $M(U)$ lies there. The case $m=1$ uses its single line directly.

### A source of bounded-degree certificates

Suppose a hidden decomposition has diagonal rank-one span $H_0$ of codimension $c$. Put $K=\bigcap_{v\in H_0}\ker M(v)$ and $Y_0=\sum_{v\in H_0}\operatorname{im}M(v)$. The compressed map $M(v)|_K\bmod Y_0$ depends only on the $c$ quotient coordinates $z$ in $U/H_0$. Suppose it has rank at least two over $F$ for each $z\ne0$. Each of its $2\times2$ minors is a linear combination of original minors. For fixed $\alpha\in F^c\setminus\{0\}$, select one minor $p_\alpha$ with $p_\alpha(\alpha)\ne0$. Let
$
I_\alpha(z)=\prod_{j=1}^c [1-(z_j-\alpha_j)^{q-1}].
$$
The polynomial $I_\alpha p_\alpha-p_\alpha(\alpha)I_\alpha$ vanishes on $F^c$. Reduction by the monic field equations gives zero by uniqueness of interpolation in individual degrees below $q$, using products of degree at most $c(q-1)+2$. Thus $I_\alpha$ lies in the bounded-degree span. The identities $z_i=\sum_{\alpha\ne0}\alpha_i I_\alpha(z)$ are polynomial identities by the same interpolation argument. Therefore the annihilator of $H_0$ belongs to $J_1$ for $D\ge\max(q,c(q-1)+2)$. Conversely each element of $J_1$ vanishes on the diagonal rank-one frame. Hence $H=H_0$. The algorithm forms the span in raw coordinates. The hidden compression establishes completeness of the bounded-degree calculation.

## Construct a covariant section and enumerate anchors

Fix bounds on $c$ and on the number $k$ of additional rank-one marks, independent of $n$. From the recovered frame compute $K=\bigcap_i\ker M(u_i)$ and $Y_0=\sum_i\operatorname{im}M(u_i)$. For each projective direction $\bar b\in\mathbb P(U/H)$ on which the compressed map $K\to Y/Y_0$ is invertible, let
$
Y_1=M(b)K,\qquad X_0=\{x\in X:M(b)x\in Y_0\}.
$$
They depend only on $\bar b$, since $H$ kills $K$ and has image in $Y_0$. The compression test gives $Y=Y_0\oplus Y_1$ and $X=X_0\oplus K$. Inside $X_0$ the kernel hyperplanes of the $M(u_i)$ identify the frame lines $X_i=\{x\in X_0:M(u_j)x=0 \text{ for }j\ne i\}$. The matching output line is $Y_i=\operatorname{im}M(u_i)$. Define a projection $\operatorname{Hom}(X,Y)\to M(H)$ by retaining only the matching $X_i\to Y_i$ blocks. It restricts to identity on $M(H)$. Its kernel pulled back along $M$ gives a section $U_b\subset U$ of $U/H$ with dimension $c$. These operations respect transport of the tensor and the chosen quotient direction, regardless of the order of the rank-one lines.

List all ordered bases of each $U_b$, appending all lists of at most $k$ vectors from the nonzero elements of the recovered rank-one lines. This uses $q^{O(c^2)}(qn)^{O(k)}$ entries. A tuple qualifies if its first slice is invertible and the normalized remaining marked slices generate $\operatorname{Mat}_n(F)$ as a unital algebra. Compute the span of successive products with the generators, which stabilizes within dimension $n^2$. Every ordinary transporter maps the source list to the corresponding target list, also for the qualifying sublists.

For a source on which the algorithm finds a qualifying tuple, select it and try all qualifying tuples in the target. Normalize by $N(v)=M(v_0)^{-1}M(v)$, $N'(v')=M'(v_0')^{-1}M'(v')$. Solve $g N(v_i)=N'(v_i')g$ on the marks. A nonzero solution is injective because its kernel is invariant under the full source matrix algebra. Thus it is invertible, and all invertible solutions differ by a scalar. For a solution $g_0$, test whether the conjugated normalized source slice space equals the target slice space. If it does, the induced invertible label map $f$ is uniquely determined by injectivity of the original slice maps. It carries all the prescribed marks. Set $h=M'(v_0')g_0M(v_0)^{-1}$. Every branch transporter has this $f$ and replaces $g_0,h$ by $t g_0,t h$ for $t\in F^\times$. Compute their determinant triples directly. The union over target tuples is exactly the full relative determinant set. This is a deterministic polynomial-time algorithm for the recognized source class and arbitrary target, without a TI oracle. A target failing an invariant preliminary test has no ordinary transporter from a recognized source.

## A growing absolutely irreducible scalar-stabilizer family

Let $m=n-2\ge3$. Use standard indices $1,\ldots,m,m+1,m+2$ in both matrix modes, and let $P$ be the forward cyclic permutation on the first $m$ coordinates. Choose an irreducible quadratic $s^2-\tau s-\gamma$ over $F$ with $\tau\ne0$, and hence $\gamma\ne0$. Such a choice follows by taking an element of $\mathbb F_{q^2}\setminus F$ with nonzero trace. The trace is surjective, and the number of elements outside $F$ with nonzero trace is positive in both characteristics. Let
$
J=\begin{pmatrix}0&\gamma\\1&\tau\end{pmatrix},\qquad
N e_i=e_{i+1}\ (i<n),\qquad
N e_n=e_1+\gamma e_{n-1}+\tau e_n .
$$
Set $B_1=\operatorname{diag}(P,I_2)$ and $B_2=B_1 N$. Define $M$ by taking $E_{ii}$ for $i\le m$, $B_1$, and $B_2$ as the $n$ slices. They are independent by their bottom blocks, which are zero, $I_2$, and $J$, respectively. Both matrix modes are concise since $B_1$ is invertible.

The bottom block of a nonzero quotient combination is $bI_2+tJ$, invertible over $F$ for $(b,t)\ne(0,0)$ because $J$ has no eigenvalue in $F$. The rank-one frame is exactly the $m$ lines $F E_{ii}$. The bounded-degree method recovers it with $c=2$ and $D=2(q-1)+2$. Write $L e_i=e_{i+1}$ for $i<m$, $L e_m=0$ on the top $m$ coordinates. The cross-blocks of $B_2$ are $U=e_2 e_{\mathrm{bottom},2}^{\mathsf T}$ and $V=e_{\mathrm{bottom},1}e_m^{\mathsf T}$. Its top block is $PL$. Both $P$ and $PL$ have zero diagonal. Choosing the quotient direction $F\bar B_1$ yields the standard split and canonical section $\langle B_1,B_2\rangle$. In that section mark $B_1,B_2$, and append any $E_{ii}$ as a third mark.

After normalization the marks are $I,N,P^{-1}E_{ii}$, where the last is confined to the top block. Every coordinate column is cyclic for $N$ because $e_i=N^{i-1}e_1$ and $N$ is invertible. Each coordinate row $e_i^{\mathsf T}$ for $i\le m$ is also cyclic. Its iterates contain the earlier top rows, then $e_n^{\mathsf T}$, then $e_{n-1}^{\mathsf T}$ and $e_m^{\mathsf T}$ after subtracting their known last-column multiples. Iterating then gives every row. Thus the span of all $N^a(P^{-1}E_{ii})N^b$ is the full matrix algebra, since the rank-one products of the two cyclic bases span it. The algorithm succeeds on this family in arbitrary independently changed bases.

### Scalar stabilizer and pair adjoints

The rank-one lines and their simultaneous input-output labels are intrinsic. For a quotient direction $bB_1+tB_2$, examine the top block of its canonical lift using its own split $X_0\oplus K$, $Y_0\oplus Y_1$ and paired rank-one lines. This block is, in the evident $X_0,Y_0$ frames, the Schur complement
$
 bP+tPL-t^2U(bI_2+tJ)^{-1}V .
$$
The last term is supported at entry $(2,m)$, with nonzero coefficient if $t\ne0$, because $(bI_2+tJ)^{-1}_{2,1}=-t/\det(bI_2+tJ)$. The full block has zero diagonal for $m\ge3$. It is monomial exactly when $b=0$ or $t=0$. With both nonzero its first column gets distinct nonzero entries from $P,PL$. With $t=0$ it is a scalar multiple of $P$. With $b=0$, $tPL$ has one empty column and one empty row, which the correction entry $(2,m)$ fills.

Distinguish these two intrinsic quotient directions by looking at the other direction's canonical lift in each direction's split. In the $B_1$ split the other lift has top block $PL$, with exactly one zero column, $m$. In the $B_2$ split the other lift has top block $P+U J^{-2}V$, by substituting the defining graph subspaces into $B_1$. The extra term lies at $(2,m)$, leaving every column nonzero. Hence every automorphism fixes both quotient directions and preserves the standard split from $B_1$. It preserves the section $\langle B_1,B_2\rangle$ and acts on those lines by scalars. Its top rank-one labels have a common permutation preserving the directed cycle of $P$, so it is a rotation. The zero column $m$ of $PL$ forces the rotation to be the identity.

The domain map $g$ is diagonal on the top $m$ lines and preserves the bottom 2-space. If the scales on $B_1,B_2$ are $\alpha,\beta$, the two equations imply $gN=\lambda Ng$ for $\lambda=\beta/\alpha$. Applying this successively to the shift makes $g$ diagonal on all $n$ coordinates and gives $g_i=g_1\lambda^{i-1}$. Comparing the $e_n$ coefficient in the final column gives $\tau g_n=\lambda\tau g_n$, hence $\lambda=1$. Now $g$ is scalar, $h$ is scalar by the $B_1$ equation, and the slice equation forces $f$ to be their scalar ratio. Thus the full stabilizer consists exactly of the scalar triples.

The pair adjoints are scalar as well. For the two matrix modes this follows from the full matrix algebra of the normalized marks. An adjoint of the label and output modes is represented by an endomorphism $S$ in the left idealizer of the slice space, which determines its paired label map by injectivity. Each $S E_{ii}$ is zero or a multiple of $E_{ii}$, because its rank is at most one, its only possible nonzero column is $i$, and the recovered frame has only one line with that column. Thus $S$ has block form $\begin{pmatrix}D&W\\0&A\end{pmatrix}$ with $D$ diagonal. In $S B_1$ the bottom-left block is zero, ruling out a $B_2$ coefficient. Comparing the result with a multiple of $B_1$ plus a diagonal combination gives $D=\lambda I_m,W=0,A=\lambda I_2$. The right idealizer follows by transposing, using instead the top-right block of $B_2$. This verifies all three pair adjoints.

### Absolute irreducibility and essential dimension

Let $F_M(a,b,t)$ be the formal determinant in the displayed slice coordinates. It is multiaffine in the $a_i$, with coefficient of $\prod_i a_i$ equal to $\det(bI_2+tJ)$. At $t=0$ it is
$
 b^2\big(\prod_{i=1}^m a_i+(-1)^{m-1}b^m\big).
$$
The parenthesized polynomial is absolutely irreducible, since it is primitive of degree one in $a_1$ with relatively prime leading and constant coefficients. Any factorization of $F_M$ partitions the $a_i$ among the factors by multiaffinity. Each factor preserves its dependence on its assigned $a_i$ after $t=0$, since the coefficient of $\prod_i a_i$ stays nonzero. Thus at most one factor can depend on the $a_i$. Any remaining factor in $b,t$ divides $\det(bI_2+tJ)$.

On either root line of $\det(bI_2+tJ)$, both $b,t$ are nonzero away from the origin. The coefficient of $a_1$ with no other $a_i$ equals, on such a line, up to sign, $b^{m-2}t^3$. Indeed after deleting top vertex $1$, the directed entries of $bP+tPL$ on $2,\ldots,m$ point strictly forward. The top constant block has no cycle covering. Every determinant term must use both cross-blocks $tU,tV$, with a path from vertex $2$ to $m$. All the remaining top vertices lie on this path because they cannot form a directed cycle. The unique such path follows the adjacent entries and has weight $b^{m-2}$. The remaining bottom cofactor is $\pm t$, giving the displayed coefficient. Hence neither root line divides $F_M$, proving absolute irreducibility.

Suppose a direction $(d_1,\ldots,d_m,e,f)$ gives translation invariance of this formal polynomial. The top coefficient in the $a_i$ is the binary norm quadratic $\det(bI_2+tJ)$. Its polar form is nondegenerate because the two root lines are distinct and independent over the algebraic closure. The top coefficient under translation therefore forces $e=f=0$. With only the $a_i$ translated, the coefficient of $\prod_{j\ne i}a_j$ changes by the translation parameter times $d_i\det(bI_2+tJ)$, so every $d_i=0$. The determinant depends essentially on all $n$ label directions.

## Scope

The recovered section lets the algorithm choose short compatible anchors for this certified raw class. Coverage outside it remains open. The broader trace and centralizer compilation in the project can use such lists whenever the post-anchor residual sizes are logarithmic. The proof uses the determinantal equations for rank one and covariance of tensor slice spaces. [Ordinary tensor isomorphism and matrix spaces](https://arxiv.org/abs/1907.00309)
