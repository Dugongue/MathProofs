# Exact minimum actions for thin central quotients of extraspecial products

Let \(P=\prod_{i=1}^m P_i\), where each \(P_i\) is an extraspecial \(p\)-group of order \(p^{2a_i+1}\). Suppose the factors and their central generator coordinates are given, either through disjoint faithful permutation generators or by standard compact symplectic coordinates. Let \(N\le Z(P)\) be an explicitly given central subspace of dimension \(r\). Then the minimum faithful degree of \(P/N\) and compact generators for stabilizers of a minimum action can be computed in
\[
p^r\operatorname{poly}(L)
\]
time in the permutation-generator input model of bit length \(L\). In symplectic coordinates the same method takes \(p^{r+O(1)}\operatorname{poly}(L)\) including the field-symbol loops. An explicit permutation action can be printed in additional output-polynomial time. This extends the earlier code formula for Heisenberg and dihedral powers to factors of arbitrary symplectic ranks and binary signs, and gives an exact algorithm parameterized by the dimension of the killed center. [Prior hardness and code formula](https://github.com/Dugongue/MathProofs/blob/main/MinimumDegreeCrossovers/Quotient.md)

## Exact costs of individual central marks

Use the selected central generators to identify \(Z(P)=\mathbb F_p^m\), and let \(A\) have a basis of \(N\) as rows. The characters on \(Z(P)/N\) are the code \(\mathcal C=\ker A\). The image of \(Z(P)\) in \(P/N\) can be smaller than the full center, so two kinds of marks must be considered.

Let \(I_0=\{i:z_i\in N\}\). If a vector in the abelianization of \(P\) is central modulo \(N\), its commutators with each factor lie in \(N\). Nondegeneracy in that factor says that its coordinate must vanish if \(i\notin I_0\). Conversely factors with indices in \(I_0\) become elementary abelian central groups of rank \(2a_i\). Since \(N\) contains the full coordinate lines on \(I_0\), the quotient splits as
\[
(P_I/N_I)\times E,\qquad
I=[m]\setminus I_0,\quad
E=\prod_{i\in I_0}P_i/Z(P_i),
\]
where \(N_I\) is the projection of \(N\) to the remaining central coordinates. The center of \(P_I/N_I\) is exactly its image center. All its central marks have cheapest cost at least \(p^2\), since that center is its derived subgroup. For a direct elementary abelian factor \(E\), the marks supported on \(E\) have cost \(p\), and a mark involving a nonzero projection onto the other center has exactly the corresponding cost there. To prove the latter assertion, let \(H_0\) be the least-index stabilizer for the first-factor mark \(\lambda\ne0\) and let \(D=\ker(\lambda+\delta)\) be the hyperplane of the full product center. Use \(H_0 D\) as the stabilizer for the combined mark. Its center trace is \(D\), since \(H_0\) has trace \(\ker\lambda\) inside \(D\). Also \([D:D\cap H_0]=|E|\), so its index in the product equals the index of \(H_0\) in the first factor. In the other direction, restricting any marked stabilizer to the first factor only reduces its index. Thus greedy first takes a basis of the \(E\)-marks and then optimizes the projected marks. The contribution of \(E\) is \(p\dim E\). In the computation that follows, delete the indices in \(I_0\) and use the row space for \(N_I\), of dimension at most \(r\).

For a nonzero codeword \(x\) in the remaining coordinates, let
\[
w(x)=\sum_{i:x_i\ne0}a_i,\qquad
\epsilon(x)=
\begin{cases}
0,&p\text{ odd},\\
\sum_i\alpha_i x_i\bmod 2,&p=2,
\end{cases}
\]
where \(\alpha_i\) is the Arf sign bit of the square form of \(P_i\). Its cheapest orbit has degree
\[
p^{\,1+w(x)+\epsilon(x)}.
\]
Indeed, quotient by the kernel of the mark on \(Z(P)\), which contains \(N\). The factors with nonzero coordinates give a central product whose cyclic center has order \(p\) and whose symplectic rank is \(2w(x)\). The factors with zero coordinates become separate elementary central directions. They can be included in the stabilizer, and cannot improve the cost on the active central product. In odd characteristic the power constraint is linear, giving a Lagrangian in its kernel, also for the exponent-\(p^2\) extraspecial type. In characteristic two the form is the orthogonal sum of the square forms of the active factors and hence has the displayed Arf bit. Its maximum totally singular dimension is \(w(x)-\epsilon(x)\). The corresponding complements lift by the cyclic-center construction in the earlier proof. [Constructing cyclic-center stabilizers](https://github.com/Dugongue/MathProofs/blob/main/GrochowGroupFrontier/MinimumAction.md#3-compute-an-optimal-stabilizer-when-the-center-is-cyclic)

## Minimum-weight basis without enumerating the code

Faithfulness requires a spanning set of marks. Hyperplane splitting and basis deletion give the minimum-weight basis objective with the above orbit costs. Greedy can be implemented by finding the least-cost word outside the current span \(U\). Compute a basis of linear forms annihilating \(U\). A word is outside \(U\) exactly when one of these forms \(l\) is nonzero on it. Scaling a nonzero word makes \(l(x)=1\) and preserves its cost. Thus test the system
\[
Ax=0,\qquad l(x)=1
\]
for each such \(l\).

Use a prefix dynamic program whose state is the accumulated syndrome in \(\mathbb F_p^{r+1}\), including the extra equation, together with one parity bit for the binary sign. Choosing coordinate \(x_i\) updates that syndrome by \(x_i(A_i,l_i)\) and adds \(a_i\) if \(x_i\ne0\). In the binary case update the sign bit by \(\alpha_i x_i\). For each state keep the least accumulated support cost and a predecessor. At the final syndrome take the minimum over available signs after adding the sign bit to the exponent. The least extension over the linear forms is exactly the greedy word, with reconstruction. The state and transition counts give the time bound. In the explicit permutation model \(p\) is bounded by the supplied permutation degree and the coefficient lengths are polynomial. Stabilizers are recovered as above and pulled back through the quotient using the supplied central coordinates.
