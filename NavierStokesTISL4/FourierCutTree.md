# A third-sign reduction from low-rank cut trees

Work over $F=\mathbb F_3$. Let $L_T,L_S\subseteq M_n(F)$ be the slice spans of two square, label-concise three-tensors. The algorithm below works directly with dense entries. It computes a signed determinant character sum from a binary cut tree in polynomial time when the common matrix coupling ranks are bounded and the intrinsic label cut dimensions are logarithmic. It can compute the sum on either the slice span or its trace annihilator. A nonzero computed character sum gives a deterministic polynomial-time many-one reduction from full SL-TI to one two-sign TI comparison, even when all three modes and all three castling defects are large. The two other sign rows are tested on the same ordinary transporter from which the character relation is derived.

The local-to-global step adapts the child-front cancellation in Alpöge–Buckmaster's signed tree. Each node input uses its own cells and the two child fronts. Here a front records the entire determinant response to a low-rank boundary perturbation and the residual linear restrictions on label assignments. The finite projection of label constraints discards precisely the data whose effects survive through a child front. The determinant character transfer through trace annihilators uses the normalized harmonic projection underlying the same source's Fourier modes. The algebraic, finite-field transfers below are separate proofs. [SignedTree.nodeInput](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1269) · [signedTreeLowerBound](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertTreeLowerBound.lean#L34) · [torusMean_phase](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L126)

## 1. Cut and cell data

Take one square matrix space $L$, with any computed basis. Use row and column index set $[n]$ on both sides. A rooted binary tree of subsets has root $[n]$, and the two nonempty children of every internal node partition its subset. A tree can be supplied, or the algorithm can use the fixed ordered bisection tree with a prescribed leaf size. In particular the latter is a polynomial-time test on the displayed dense raw tensors and requires no supplied transporter. Choose an ordered tree so the index order obtained by concatenating its leaves is used on both rows and columns. This simultaneous reorder has determinant factor one.

For a tree subset $I$, let the columns of $P_I$ be a basis of the common column span of all cross blocks $M[I,\bar I]$ of all $M\in L$. Let the rows of $Q_I$ be a basis of the common row span of $M[\bar I,I]$. Both are computed from a slice basis by Gaussian elimination. Write $b$ for the maximum of either port rank over the tree. The root has both ranks zero.

The cells of the tree consist of each diagonal leaf square and each pair of directed sibling rectangles $A\times B,B\times A$ at a split $I=A\sqcup B$. They partition the matrix entries. Each entry is a linear functional in $L^*$. Let $E_I$ be the span in $L^*$ of the entry functionals from cells in the subtree at $I$, and $E_{\neg I}$ the span of the functionals from the other cells. Define $B_I=E_I\cap E_{\neg I}$. Let $w$ be the maximum of all $\dim B_I$ and all $\dim E_I$ at leaves. In particular the label width does not depend on which basis is used to describe $L$. Matrix entries can all depend on many displayed label coordinates while $w$ remains small.

At an internal split, write $C_I$ for the span of the two sibling rectangles' entry functionals. Then $E_I=E_A+E_B+C_I$. Also $\dim C_I\le 2b^2$. Indeed each $M[A,B]$ factors as $P_A Z_{AB}(M)Q_B$, and $M[B,A]$ similarly. A left inverse of $P_A$ and right inverse of $Q_B$ give each entry of the unique $Z_{AB}(M)$ as a linear functional in $C_I$. Conversely these coordinates determine the entries of the block, proving the dimension bound. The same statements cover empty port spaces.

## 2. Exact determinant fronts

For a matrix $M$ and a node $I$, the front of $M[I,I]$ is the formal determinant response
$$
D_I(Z)=\det(M[I,I]+P_I Z Q_I).
$$
For an $a\times d$ matrix of variables $Z$ this polynomial has the unique form
$$
D_I(Z)=\sum_{\substack{S\subseteq[a],\,T\subseteq[d]\\ |S|=|T|}}c_I(S,T)\det Z[S,T].
$$
Use the convention that the empty minor equals one. To see the form, apply Cauchy–Binet to $[M[I,I]\;\;P_I]\binom{\mathrm{Id}}{ZQ_I}$. Each selected minor from the second factor is, up to a sign, a minor of $ZQ_I$, since the remaining selected rows are rows of the identity. Apply Cauchy–Binet to that minor. Uniqueness follows by taking the coefficient of the matching monomial $z_{s_1t_1}\cdots z_{s_ht_h}$ for sorted $S=(s_1,\ldots,s_h)$, $T=(t_1,\ldots,t_h)$. This monomial occurs in exactly the indicated minor and has coefficient one.

The coefficients can be recovered from evaluations of $D_I$ on at most $2^b$ zero-one matrices for each $S,T$. Set other entries zero and use the mixed difference over the $h$ matching positions. Each variable appears with degree at most one. The coefficient length is at most $\binom{2b}{b}$, which is bounded by $4^b$.

At a split $I=A\sqcup B$, use $P=\operatorname{diag}(P_A,P_B)$ and $Q=\operatorname{diag}(Q_A,Q_B)$. The analogous coefficient system $c_0(S,T)$ for $M[A,A]\oplus M[B,B]$ with these ports follows exactly from the two child fronts. Split $S,T$ by child. If each child has equal source and target counts, $c_0(S,T)=c_A(S_A,T_A)c_B(S_B,T_B)$; otherwise $c_0(S,T)=0$. For the first assertion, evaluate the matching monomial variables alone. Their perturbation is block diagonal and its determinant is a product. In the unequal case the sorted matching crosses the block boundary only in one direction. The perturbed matrix is block triangular, so its determinant is independent of the crossing variables and their mixed coefficient vanishes. This proves the formula, including singular child matrices.

The child row spaces contain the restrictions of $P_I$ to each child, because external columns for $I$ are also external to each child. The analogous claim holds for $Q_I$. Thus there are computed matrices $R,S_0$ with $P_I=P R$, $Q_I=S_0 Q$. Assemble the two cross blocks into an off-diagonal port matrix $Z_{\rm cell}$ by their factorizations above. For every $Z$,
$$
M[I,I]+P_I Z Q_I
  = \bigl(M[A,A]\oplus M[B,B]\bigr)
       + P (Z_{\rm cell}+R Z S_0) Q.
$$
The product-coefficient formula therefore evaluates $D_I(Z)$ from the two child fronts and the cross cell. Recover the parent coefficients by the same mixed differences. This merges the entire matrix response, so two matrices inducing the same front are interchangeable at all parents.

## 3. Count the actual coherent assignments

A matrix in $L$ is equivalent to a linear functional on $L^*$. At $I$ count linear functionals on $E_I$ by their determinant front and by their restriction to $B_I$. At a leaf enumerate the at most $3^w$ functionals and evaluate the local response.

At an internal node enumerate one state from each child and one functional on $C_I$. There are at most $3^{2b^2}$ choices of the latter. To test consistency, test whether the sum of their three supplied boundary functionals vanishes on
$$
\ker(B_A\oplus B_B\oplus C_I\ \xrightarrow{\;\mathrm{sum}\;}\ L^*).
$$
This checks every dependency among $E_A,E_B,C_I$. In fact if $x_A+x_B+x_C=0$ then $x_A\in E_A\cap(E_B+C_I)\subseteq B_A$, and similarly $x_B\in B_B$. Consequently every pair of concrete child assignments of the indicated states glues uniquely if this test succeeds, and none glues if it fails. The uniqueness follows from $E_I=E_A+E_B+C_I$.

The same exposed boundary data determine the restriction to $B_I$. For $x\in B_I$ choose a decomposition $x=x_A+x_B+x_C$ in $E_A+E_B+C_I$. Since $x\in E_{\neg I}$, one has $x_A=x-x_B-x_C\in B_A$, and similarly $x_B\in B_B$. Evaluate the three boundary functionals on those components and sum. The consistency test makes the answer independent of the chosen decomposition. Use the exact determinant merge to compute the parent front. Multiply the two integer counts, accumulating the product at the resulting parent state. Each parent assignment has unique child and cell restrictions, so this counts every coherent assignment exactly once.

The root has $B_I=0$, $E_I=L^*$ and no ports. Its determinant response is the scalar determinant of the full matrix. Thus it gives the entire histogram for $L$. Counts have $O(\dim L)$ bits. The number of states, the enumeration of pairs, and their merges give the bound
$$
3^{O(w+4^b)}\operatorname{poly}(n+\dim L).
$$
All preprocessing is polynomial in the dense input length. Bounded $b$ and logarithmic $w$ suffice even for arbitrary-size leaf squares.

The same proof computes any fixed correlation
$$
\sum_{x_1,\ldots,x_t\in L}\prod_{j=1}^{u}\chi\!\left(\det\!\left(\sum_{i=1}^t\lambda_{ji}x_i\right)\right)
$$
for fixed $t,u$ and $\lambda_{ji}\in F$, where $\chi(0)=0,\chi(1)=1,\chi(-1)=-1$ are integers. Store the joint list of fronts of the $u$ linear combinations and the $t$ boundary assignments. Crossing values and parent boundaries are the componentwise linear combinations in the same glue, so the proof preserves correlations. The exponent in the time bound is multiplied by a constant depending only on $t,u$. Odd $u$ gives the same character as the single signed count.

## 4. Transfer to the trace annihilator and eliminate a sign

Write $f(M)=\chi(\det M)$ for $M\in M_n(F)$ and $\psi(a)=\exp(2\pi i a/3)$. Its unnormalized Fourier transform for the nondegenerate pairing $(M,N)\mapsto\operatorname{tr}(MN)$ is
$$
\widehat f(N)=\sum_M f(M)\psi(\operatorname{tr}(MN)).
$$
Changing $M$ by left or right multiplication shows that $\widehat f$ transforms by the same quadratic determinant character as $f$. Every singular $N$ is fixed by a determinant-negative row or column reflection, obtained from a basis of its image or kernel. Thus $\widehat f(N)=0$ there. On the invertible orbit, $\widehat f(N)=\widehat f(I_n)f(N)$.

The constant is $3^{n(n-1)/2}(\psi(1)-\psi(-1))^n$. To check it, split off the last row and column at $I_n$ and write $M=\left(\begin{smallmatrix}A&v\\w&d\end{smallmatrix}\right)$. If $A$ is singular, $\det M$ is independent of $d$, so summing $\psi(d)$ kills those terms. Otherwise $\det M=\det A(d-wA^{-1}v)$. The sum over $d$ contributes $(\psi(1)-\psi(-1))\chi(\det A)\psi(wA^{-1}v)$. Summing the last phase over $w,v$ retains just $v=0$ and gives $3^{n-1}$. Iterate the resulting recurrence, starting from the empty matrix. The matrix Gauss sum is classical; the proof here fixes the normalizations used in the complement test. [Li and Hu on matrix Gauss sums](https://www.sciencedirect.com/science/article/pii/S0022314X12002065)

Take $n$ even. For $W(L)=\sum_{M\in L}f(M)$, additive orthogonality gives the exact identity
$$
W(L)=(-1)^{n/2}3^{\dim L-n^2/2}W(L^\perp).
$$
If the exponent is negative, the equality gives the corresponding exact integer division. This permits using a suitable tree on either side, including different choices at the two endpoints. Alternatively a nonzero odd correlation can itself be computed on the dual and used with its own comparison rule below. The matrix-side character agrees for the dual, since the trace dual of $M\mapsto hMg^{-1}$ is $N\mapsto gNh^{-1}$, and a quadratic character is its own inverse.

Every raw tensor transporter $(g,h,k)$ between label-concise square pencils induces a bijection of slice spaces $M\mapsto hMg^{-1}$. Hence
$$
W(L_S)=\chi(\det g)\chi(\det h)\,W(L_T).
$$
The same relation holds for odd correlations on the slice spaces, or for the corresponding odd correlations on both trace annihilators. If the absolute values differ, reject ordinary isomorphism. If they are nonzero with opposite signs, reject SL-isomorphism. If they are nonzero and equal, every ordinary transporter already obeys the binary row $s_g+s_h=0$. Keep $s_g,s_k$ via the prior exact determinant projections. A single two-sign query on those rows accepts precisely when all three original signs vanish. In particular this is an explicit construction for the stated domain, with no use of a decision or search oracle in its preprocessing. Equal zero values give no inference from that particular observable. [Exact physical sign projections](https://github.com/Dugongue/MathProofs/blob/main/TensorSignProjections/SignProjections.md)

## 5. Dense examples with a genuinely fixed sign

Take $m\ge2$ size-two leaves in a binary interval tree and $n=2m$. Define $K\subset M_n(F)$ by the independent cells below.

- At leaf $i$, put $a_i I_2+b_iE_{12}$ with both parameters free.
- At every split $A\mid B$, put a cross block $u_A c_B$ in $M[A,B]$ and zero in $M[B,A]$. Here $u_A$ repeats the column $(1,0)^t$ across the leaves of $A$, and $c_B$ repeats the same freely varying row $(r,s)$ across the leaves of $B$.

At any cut, every outgoing cross column from that subtree lies in its repeated first-coordinate line. Every incoming cross row lies in its repeated two-coordinate row space. Thus $b\le2$. Label cells are independent, so $\dim B_I=0$ and $w=2$. The label dimension is $2m+2(m-1)=4m-2$. The global matrix is upper block triangular with determinant $\prod_i a_i^2$, which gives $W(K)=6^m3^{2m-2}\ne0$. Its trace annihilator $L$ has dimension $n^2-4m+2$ and also has nonzero signed count. Both matrix spaces give dense displayed support. At a balanced top split, their support graphs contain complete bipartite rectangles with both sides growing with $m$. This can violate the earlier bounded coordinate-support and bounded live-column conditions in these frames, while the common coupling ranks remain at most two on $K$. Neither the label width of $K$ nor its codimension is logarithmic. [Earlier coordinate-support determinant-count construction](https://github.com/Dugongue/MathProofs)

The three tensor modes are concise for either space. The identity belongs to $K$, and $L$ contains an invertible block-diagonal matrix with each leaf block $\operatorname{diag}(1,-1)$. Both label bases can be computed by linear algebra. Each of the three fixed-mode stabilizer groups has determinant-one action in all modes for $K$. For the fixed-label group, $I_n$ equates the two matrix-side maps. Commutation with the individual leaf identities forces a block diagonal map, and commutation with the leaf $E_{12}$ makes each block of the form $aI_2+bE_{12}$. Its determinant is $a^2=1$. For either one-sided idealizer, $I_n\in K$ implies that the acting matrix itself is in $K$. It is upper block triangular with those same diagonal forms and therefore has determinant one. Its induced determinant on $K$ can be read from a filtration. For left multiplication order the cell directions by their largest nonzero row leaf. Projecting a layer onto its last row leaf separates its cells by their disjoint column supports. Left multiplication on the projected cell equals its action by that leaf's $aI_2+bE_{12}$. The leaf cell gives an $a^2$ factor and each cross cell gives two copies of $a$, since its row column is $e_1$. For right multiplication order by the smallest nonzero column leaf in decreasing order. Projection onto that first column leaf separates the cells by row supports. The induced right action is again $aI_2+bE_{12}$ on both a local cell and the two-dimensional row carrier of any cross cell. Thus every layer contributes determinant one.

For $L$, trace duality carries one-sided idealizers to the other idealizers of $K$, with the matrix-side signs unchanged. Since $n$ is even, the ambient matrix-space map has determinant one for arbitrary row and column changes. The determinant on $L$ equals that on the contragredient complement $K$, by the exact sequence for a subspace and its quotient. The fixed-label stabilizer of $L$ is scalar: $L$ contains all strict upper coordinate matrices and each difference of the two coordinate diagonal matrices in a leaf. A fixed-label pair $A,B$ obeys $AE_{ij}=E_{ij}B$ for $i<j$, which fixes the first $n-1$ columns of $A$ and last $n-1$ rows of $B$ to one common scalar on the diagonal. The individual leaf differences force the remaining column and row to that same scalar. Their determinants are positive since $n$ is even. This verifies neutral pair-adjoint signs for the dual example too.

Rebase only one matrix side by a reflection, leaving the label coordinates unchanged. The resulting pair is an ordinary yes instance and satisfies the two retained signs if the reflected side is omitted. The signed count changes sign and every transporter has negative combined matrix-side sign. Thus the full SL comparison fails. This gives an explicit family in which the removed character tests an actual constraint, even though all fixed-mode stabilizer sign corrections vanish.

These are written proofs. The construction supplies a scoped reduction for the four-class problem over $F_3$. The width and nonzero-character hypotheses are part of the theorem.
