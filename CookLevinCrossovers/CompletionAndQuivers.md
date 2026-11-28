# Subexponential algorithms for completion and quiver subrepresentations

These theorems apply the bounded-width counting algorithm and the low-incidence circuit-CSP algorithm to rank completion and quiver subrepresentations. The external algorithmic inputs are [OpenAI, Theorem 1.1](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf) and [Strassle–Subercaseaux, Fact 1.3 and its counting version in Section 6](https://arxiv.org/pdf/2611.11832). All operation counts below refer to bit complexity. The input explicitly describes its rows, columns, vertices and prescribed data.

Put \(F(s)=s\log\log(s+16)/\sqrt{\log(s+16)}\) and \(G(s)=s/\sqrt{\log(s+16)}\). The dense counter counts Boolean assignments of a fixed-width CNF on \(s\) declared bits in time \(2^{O(F(s))}\operatorname{poly}(L)\). For \(O(s)\) clauses or circuit predicates with \(O(s)\) total input incidences and arity at most \(s^{9/10}\), the time is \(2^{O(G(s))}\operatorname{poly}(L)\). The latter bound applies to exact counting because the tensor contraction is computed modulo a power of two larger than the greatest possible count. Arity \(O(s^{9/10})\) can be accommodated by padding with a fixed constant factor of pinned variables. In a fixed finite domain each value uses a constant number of bits, with one code per value, and a forbidden tuple on a bounded number of variables is a clause on these bits. An explicit finite-domain variable domain or bounded-arity predicate thus takes a fixed number of bounded-width clauses.

## 1. Rectangular rank completion in the smaller dimension

**Theorem 1.** Fix a finite field \(k=\mathbb F_q\) and a rank limit \(d\). For an \(m\)-by-\(n\) matrix with arbitrarily many prescribed entries, rank-at-most-\(d\) completion is decidable in time
\[
2^{O_{q,d}(F(\min(m,n)))}\operatorname{poly}_{q,d}(L).
\]
The algorithm also counts all extendible \(d\)-dimensional factors on the smaller side, and can recover a completion within the same bound. The number of distinct completions of each rank at most \(d\) is computable in \(2^{O_{q,d}(F(m+n))}\operatorname{poly}_{q,d}(L)\). If the number of prescribed entries is \(O(m+n)\), the latter bound uses \(G\) in place of \(F\). The statements allow arbitrary field-valued prescribed entries.

Transpose if necessary so \(n\le m\). Give each column a proposed factor \(v_j\in k^d\). For a row whose prescribed column set is \(J\), completion requires consistency of the system \(u\cdot v_j=a_j\) for \(j\in J\). If that system is inconsistent, there is a minimal inconsistent subsystem of at most \(d+1\) equations. In fact, take a maximal independent set of coefficient vectors, and prescribe the unique values of their linear functionals supplied by their right sides. These independent equations are solvable. If every other row equation agrees with the induced linear combination of right sides, their solutions solve the entire system. Otherwise add one disagreeing equation to the independent set. This also handles a zero coefficient with a nonzero right side.

For every row and every subset of at most \(d+1\) exposed columns, impose the bounded-arity predicate that this subsystem is consistent. Enumerating these subsets and the allowed factor tuples costs polynomial time for fixed \(q,d\). The resulting CNF needs only \(n\lceil\log_2(q^d)\rceil\) assignment bits. It counts the extendible smaller-side factors exactly. Fix a factor code a bit at a time using exact conditional counts, then solve all row systems to recover a completion. The factorization exists for every matrix of rank at most \(d\), including rank less than \(d\), by padding a rank factorization with zeros.

For exact counts of distinct matrices use \(S_j\), the number of pairs \(U\in k^{m\times j}\), \(V\in k^{j\times n}\) satisfying the prescribed entries in \(UV\), for \(0\le j\le d\). The factor constraints are binary on row and column factors. Count these as bounded-width CNFs on \(O_{q,d}(m+n)\) bits. For sparse input they have \(O_{q,d}(m+n)\) clauses. For a fixed matrix of rank \(s\), the number of width-\(j\) factorizations is
\[
B_{j,s}=\sum_{a=s}^{\min(j,m)}
{m-s\brack a-s}_{q}\,
\prod_{i=0}^{a-1}(q^j-q^i)\,
q^{(j-a)n}.
\]
To see this, choose the \(a\)-dimensional image \(W\) of \(U\) containing the column image of the fixed matrix. This gives the Gaussian binomial factor. Choose a surjection \(k^j\to W\), which gives the second factor. Each of the \(n\) columns of \(V\) lifts the corresponding matrix column with \(q^{j-a}\) choices. All choices are independent. If \(N_s\) is the desired number of completions of rank exactly \(s\), then \(S_j=\sum_{0\le s\le j}B_{j,s}N_s\). Solve in increasing \(j\), up to \(\min(d,m,n)\), using \(B_{j,j}=|\mathrm{GL}_{j}(k)|>0\). All integer bit lengths and subsequent arithmetic are polynomial in the input size. For \(j=0\) the single candidate is the zero matrix.

There is no density hypothesis in the smaller-side bound. Its local consistency test avoids introducing witnesses for the larger side of the matrix. The bound does not assign a distinct completion to each extendible smaller-side factor. The separate exact-rank count handles multiplicities without such an assumption.

## 2. Completion as a projective coloring with cycle constraints

**Theorem 2.** Let a partial matrix over \(k=\mathbb F_q\) contain a completely specified \(I_2\), and suppose every row and column meets a nonzero prescribed entry. Let \(G_0\) and \(G_1\) be the bipartite graphs on rows and columns of zero and nonzero prescribed entries, respectively. Write \(c_i\) for their numbers of components, counting isolated vertices. There is an explicit assignment problem on \(c_0\) variables with domain \(\mathbb P^1(k)\). The number of distinct rank-two completions is
\[
\frac{(q-1)^{c_1}}{|\mathrm{GL}_2(k)|}\,\#\{\text{valid projective assignments}\}.
\]
Its constraints are a disequality for each \(G_1\)-edge after identifying its endpoints' \(G_0\)-components, plus one multiplicative gain condition for each fundamental cycle of \(G_1\). In particular, it reduces exactly to proper \((q+1)\)-colorings of the quotient graph when \(G_1\) is a forest. It reduces to proper \(3\)-colorings of that graph over \(\mathbb F_2\) for every \(G_1\). Loops exclude all assignments.

For fixed \(q\), combine constraints with the same support into one circuit. If the resulting predicates have \(O(c_0)\) total variable incidences and maximum support size \(O(c_0^{9/10})\), the number of completions is computable in time \(2^{O_q(G(c_0))}\operatorname{poly}(L)\). For forests and over \(\mathbb F_2\) there is an all-density bound \(2^{O_q(F(c_0))}\operatorname{poly}(L)\).

**Proof.** Every rank-two factorization gives a nonzero row vector at every row and a nonzero column functional at every column. Assign the span of the row vector and the kernel of the column functional as their projective colors. A zero edge forces equality, so the colors descend to \(G_0\)-components. A nonzero edge forces disequality. Fix a nonzero representative \(u_i\) of each line \(i\) and a nonzero functional \(f_i\) with kernel \(i\). Write row vectors as \(\alpha_r u_{i(r)}\) and column functionals as \(\beta_c f_{i(c)}\), with both scalars nonzero. A nonzero prescribed value \(a_e\) at \(e=rc\) requires
\[
\alpha_r\beta_c=g_e,\qquad
g_e=a_e/f_{i(c)}(u_{i(r)}).
\]
These denominators are nonzero. On any spanning tree of a component of \(G_1\), one arbitrary nonzero root scalar determines all the others. An edge outside the tree works exactly when the alternating product of gains around its fundamental cycle is \(1\), where alternating product means the products on odd and even positions agree. This follows either by computing the propagated scalars or by cancelling each vertex scalar in the two products. The choice of root scalar cancels out of each check. Thus each valid projective assignment determines \((q-1)^{c_1}\) factorizations. These exhaust the factorizations and count each once. The pinned \(I_2\) guarantees rank two. Each completion therefore contributes \(|\mathrm{GL}_2(k)|\) factorizations, by change of basis in its factor space. In the binary field every nonzero gain is \(1\). For a forest no cycle checks occur.

Compute gains by a lookup in the fixed field and check the products by a circuit taking one input code per distinct \(G_0\)-component on the cycle. The code-validity predicates and the grouped constraints are circuit-CSP inputs with the stated incidence and arity. Forest and binary instances use fixed-width dense counting on the quotient graph. Both methods first count projective assignments, then apply the displayed factor exactly. In particular, dense collections of zero pins do not enter the exponent. The classical cycle criterion for rank-one completion appears inside this proof only after the projective colors have been chosen. [Cycle criterion for prescribed rank-one entries](https://www.math.auckland.ac.nz/~waldron/Preprints/Tripleprods/M104214.pdf)

## 3. Exact counting of subrepresentations of a quiver

**Theorem 3.** Let \(Q\) be a finite quiver, with a representation \((V_v,A_e)\) over a finite field \(k=\mathbb F_q\). The dimensions \(d_v=\dim V_v\) and the requested subrepresentation dimensions \(e_v\in[0,d_v]\) may vary. Set
\[
b_v=\lceil\log_2 q\rceil\,d_v\min(e_v,d_v-e_v),
\qquad B=\sum_v b_v.
\]
Group arrows by their *unordered* endpoint sets \(S\), including singleton sets for loops, and set \(b(S)=\sum_{v\in S}b_v\). If \(\sum_S b(S)=O(B)\) and \(\max_S b(S)=O(B^{9/10})\), then the number of subrepresentations of the given dimension vector is computable deterministically in \(2^{O(G(B))}\operatorname{poly}(L+B+\log q)\). This in particular applies when the simple graph of distinct neighbors has bounded degree and adjacent basis scopes are \(O(B^{9/10})\). Arbitrarily many parallel arrows may be supplied. The representation matrices may be dense.

**Proof.** Use \(\min(e_v,d_v-e_v)\) columns of length \(d_v\) at each vertex. If \(e_v\le d_v/2\) the columns are an ordered basis of the proposed subspace. Otherwise they are a basis of its annihilator in \(V_v^*\). A local circuit checks valid unique field codes and full column rank. The cases \(e_v=0,d_v\) have empty certificates and represent fixed subspaces. For each endpoint set \(S\), one circuit first validates the local certificates, reconstructs actual subspace bases by Gaussian elimination where an annihilator was used, and for all arrows in that group tests \(A_e W_{\mathrm{tail}(e)}\subseteq W_{\mathrm{head}(e)}\) by linear algebra. Its arity is \(b(S)\), regardless of the number of arrows or matrix entries. Circuits of arity zero are decided directly. Finite-field elements are represented by distinct binary codes for the standard explicit model of the input field, for example coefficients in its given polynomial basis. Field arithmetic and elimination have uniform polynomial-size Boolean circuits in the explicit input length and \(\log q\).

Each valid subrepresentation contributes precisely
\[
\prod_v |\mathrm{GL}_{\min(e_v,d_v-e_v)}(k)|
\]
successful bit assignments, because each ordered basis is freely chosen and determines its own code. No witnesses for the arrow maps are added. The circuit-CSP has \(B\) bits, uses \(O(B)\) incidences by the hypotheses and vertex checks, and has maximum arity \(O(B^{9/10})\): if a vertex is isolated and its local basis block exceeds that limit, omit the vertex and multiply the final answer by its Gaussian binomial \({d_v\brack e_v}_q\). Vertices with positive \(b_v\) incident to an arrow automatically satisfy the arity bound. If all variables disappear the answer is obtained directly. In other cases pad to the original \(B\) as needed and apply exact circuit-CSP counting. Division by the basis multiplicities for the vertices still represented gives the result. Polynomial-time Gaussian elimination also implements a search version by conditioning on the certificate bits.

This supplies a quantitative finite-field counting result for the quiver subrepresentation branch. It permits large local dimensions, arbitrary field order and dense linear maps, subject to the explicit scope bounds. If local dimensions and field order are fixed, the same proof followed by bounded-width counting allows arbitrary incidence density with \(F(B)\) in the exponent.
