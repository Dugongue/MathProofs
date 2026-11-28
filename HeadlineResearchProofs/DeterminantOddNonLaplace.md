# Non-Laplace shortest decompositions of the odd determinant

For every odd \(n\ge5\) and every field, the column determinant has an optimal partition decomposition with one term of factor degrees \(1,n-1\) and \(n-1\) terms of factor degrees \(2,n-2\). For odd prime \(n\ge5\), this is also an optimal homogeneous strength decomposition. The degree profile distinguishes it from the Laplace decompositions under invertible linear changes of variables, reordering and rescaling of terms, or swapping factors. In the partition setting, permutations and invertible changes of basis in column blocks also preserve the profile. This answers the uniqueness question in Chen and Zhao's §7.2 in the negative for every prime \(n\ge5\); it does not classify the other optimal decompositions. [Chen–Zhao, Theorem 4.2 and §7.2](https://arxiv.org/html/2607.21015v1#S7.SS2).

## The construction

Let \(V=K^n\) be the first \(n\) coordinate directions of \(W=K^{n+1}\), and put \(w=e_{n+1}\). Choose a nondegenerate alternating form \(\omega\) on \(W\) with Pfaffian one; for example, choose the coordinates in consecutive symplectic pairs. For \(1\le i\le n\), let \(v_i\) be the column in \(V\) and put \(v_{n+1}=w\). With \(B_{ij}=\omega(v_i,v_j)\), the Pfaffian congruence identity gives

\[
\operatorname{Pf}(B)=\det_{n+1}[v_1,\ldots,v_n,w]=\det_n[v_1,\ldots,v_n].
\]

Expand along row 1, the position of the variable column \(v_1\). This gives

\[
\det_n=\sum_{j=2}^{n}(-1)^j\omega(v_1,v_j)\operatorname{Pf}(B_{\widehat1,\widehat j})
   +(-1)^{n+1}\omega(v_1,w)\operatorname{Pf}(B_{\widehat1,\widehat{n+1}}),
\]

where a hat means deletion of both the specified row and its column. For \(j\le n\), the Pfaffian factor contains the fixed column and precisely the \(n-2\) variable columns complementary to \(\{1,j\}\). Each of its matchings uses each such column once. The last term splits off column 1, with complementary factor multilinear on the other \(n-1\) columns. These polynomial identities hold in every characteristic. This construction uses the same Pfaffian family as the even formula, applied one dimension higher. [Krishnan–Moshkovitz, Theorem 4.8](https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf).

The known partition rank of \(\det_n\) is \(n\) for odd \(n\). Therefore none of the displayed terms is zero and the decomposition is optimal. For prime \(n\), Chen and Zhao's strength lower bound is also \(n\). Laplace expansions have only factors of degrees \(1,n-1\), whereas \(2,n-2\) is a distinct unordered degree pair for \(n\ge5\). Because the displayed factors are nonzero and homogeneous, these degrees are unchanged by every invertible linear substitution and inverse factor rescaling. This supplies optimal decompositions with a genuinely different degree profile. The argument shows the distinction both for blockwise transformations in partition rank and for arbitrary invertible linear substitutions in homogeneous strength.
