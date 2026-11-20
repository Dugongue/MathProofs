# Output-sensitive IPS refutations for separable equations

## Statement

Let \(K\) be any field, let \(n\ge 1\), let \(A_i\subset K\) be nonempty finite sets of size \(d_i\), and fix the displayed variable order. Let \(u_i\in K[X_i]\) have degree less than \(d_i\), and put
\[
f=b+\sum_{i=1}^n u_i(X_i),\qquad p_i=\prod_{a\in A_i}(X_i-a).
\]
Allow the zero polynomial among the \(u_i\). For \(0\le k\le n\), let \(P_k\) be the set of distinct sums of the first \(k\) summand values and \(S_k\) the set of distinct sums of the remaining values on their respective grids. Empty sums give singleton sets. Put \(r_k=\min(|P_k|,|S_k|)\) and \(r=\max_k r_k\).

There is a deterministic algorithm using \(O(r^2\sum_i d_i^2)\) field operations and equality tests which finds either a grid zero of \(f\), or a Hilbert Ideal Proof System (IPS) refutation of \(f=p_1=\cdots=p_n=0\). A refutation here is a polynomial \(C\) homogeneous linear in the placeholders \(Y,Z_1,\ldots,Z_n\) satisfying \(C(X,f,p_1,\ldots,p_n)=1\). The algorithm outputs its read-once oblivious algebraic branching program (ROABP) of width at most \(3r\), with one layer per variable in the order
\[
X_1,Z_1,\ldots,X_n,Z_n,Y.
\]
The refutation is unique among Hilbert refutations whose coefficient polynomials in the \(X\)'s have individual degrees less than \(d_i\). Every Hilbert refutation at any layer order inducing the given \(X\)-order has width at least \(r\). The factor \(3\) in the constructive bound is attained by the unique reduced certificate in the stated interleaved order for each \(r=2^m\), \(m\ge 1\), already on the Boolean grid.

The field operation bound treats an element of \(K\) as an exact field element and a field operation, inversion of a nonzero element, and equality test as unit cost. If two arrays of matrices differ only in layer dimensions, width means the maximum layer dimension. A ROABP is the scalar product of matrices of univariate polynomial entries with constant initial and final vectors.

## The reciprocal has exact width \(r\)

Suppose \(f\) has no grid zero. There is a unique reduced polynomial \(g\) agreeing with \(1/f\) on the grid. Reduced means individual degrees less than \(d_i\). Existence and uniqueness follow from tensor products of the univariate Lagrange evaluation isomorphisms. At the cut after \(X_k\), the evaluation matrix of \(g\) has the same rank as its coefficient flattening. Its entries are those of the Cauchy matrix
\[
\left(\frac{1}{b+s+t}\right)_{s\in P_k,t\in S_k}
\]
with repeated rows and columns. This matrix has full rank on its smaller side over every field. Indeed, for a square submatrix of size \(h\), a linear combination of the columns vanishing on its \(h\) distinct row values gives a rational function \(\sum_{t} c_t/(b+s+t)\) with \(h\) zeros off the poles. Clearing the denominator gives a polynomial of degree at most \(h-1\), which vanishes identically. Evaluating its numerator at each \(-b-t\) shows \(c_t=0\). Thus the rank at the cut is \(r_k\). The same evaluation matrix is obtained for every polynomial agreeing with \(1/f\) on the grid, irrespective of degrees. A width-\(W\) ROABP factors that matrix through its width-\(W\) layer. This proves the reciprocal lower bound. In a Hilbert refutation, set all \(Z_i=0\), \(Y=1\), and then restrict to the grid. The result is \(1/f\), proving the lower bound for refutations without degree constraints.

For the upper bound, use monotonicity. The sizes of the \(P_k\) are nondecreasing, and those of the \(S_k\) are nonincreasing, because adjoining one summand includes a translate of the previous set. Choose \(i\in\{1,\ldots,n\}\) with \(|P_{i-1}|\le r\) and \(|S_i|\le r\). For example, if all prefix sets have size at most \(r\), use \(i=n\). Otherwise use the first index where the prefix exceeds \(r\), at which the suffix must have size at most \(r\).

Use states indexed by \(P_k\) before \(X_i\) and \(S_k\) after it. Let \(L_{j,a}\in K[X_j]\) be the Lagrange basis polynomial for \(a\in A_j\). For \(j<i\), the entry from \(s\in P_{j-1}\) to \(t\in P_j\) is \(\sum_{a:s+u_j(a)=t} L_{j,a}\). For \(j>i\), the entry from \(s\in S_{j-1}\) to \(t\in S_j\) is \(\sum_{a:s=t+u_j(a)}L_{j,a}\). At \(j=i\), connect \(s\in P_{i-1}\) to \(t\in S_i\) by
\[
\sum_{a\in A_i}\frac{L_{i,a}}{b+s+u_i(a)+t}.
\]
With the initial and final singleton states, the matrix product reads the unique left and right sums on any grid assignment. It is reduced and therefore equals \(g\). Its width is at most \(r\).

## Output-sensitive synthesis

Compute the value sets \(\{u_i(a):a\in A_i\}\) and record a value witness \(a\) for each. Maintain prefix and suffix sum sets capped at \(B+1\) distinct values, where \(B=1,2,4,\ldots\). When a set reaches the cap, its exact cardinality can be replaced by \(B+1\), and all larger prefixes or suffixes in that scan get the same capped cardinality. Before overflow, keep one predecessor and one value witness for each sum. The maximum of the capped cut minima equals \(\min(r,B+1)\). Stop when it is at most \(B\), which gives the exact \(r\) and all needed sets for the bridge.

At the pivot, check each denominator for each of the \(|P_{i-1}||A_i||S_i|\) triples. Every grid assignment gives such a triple. If a denominator is zero, the stored predecessors recover an assignment producing it. Otherwise form the reciprocal layers described above. Each capped scan uses \(O(B^2\sum_i d_i)\) field operations and equality tests by naive linear-list deduplication. The sum of these bounds over the doubling sequence is \(O(r^2\sum_i d_i)\). Evaluating the summands and forming their Lagrange bases costs \(O(\sum_i d_i^2)\). One can form each layer entry in \(O(d_i^2)\) field operations by coefficientwise linear combination of the Lagrange bases. This gives the stated bound for the reciprocal and continues to hold for the refutation construction below.

## One marked local division gives the refutation

Write \(\rho_i\) and \(Q_i\) for the remainder and quotient, respectively, when multiplying a polynomial by \(u_i(X_i)\) and dividing by the monic \(p_i(X_i)\), treating the other variables as coefficients. Both operators are \(K[X_j:j\ne i]\)-linear. Thus
\[
f g=b g+\sum_i \rho_i(g)+\sum_i p_i Q_i(g).
\]
The first two terms together are reduced and evaluate to one on the grid, hence they sum to one. The certificate is
\[
C(X,Y,Z)=Yg(X)-\sum_i Z_i Q_i(g).
\]
Each \(Q_i(g)\) has individual degree at most \(d_i-2\) in \(X_i\) and is reduced in every other variable. Here a negative bound means the quotient is zero. For uniqueness, the \(Y\)-coefficient of any reduced certificate must be \(g\) by interpolation. If \(\sum_i p_i h_i=0\) with every \(h_i\) reduced, fix \(i\). All summands except \(p_i h_i\) have \(X_i\)-degree below \(d_i\). If \(h_i\ne0\), the \(X_i\)-degree of \(p_i h_i\) is at least \(d_i\), impossible. Thus the remaining coefficients are forced.

Write \(g=a G_1\cdots G_n v\), where the \(G_i\) are the reduced layers already constructed. Then \(Q_i(g)=a G_1\cdots G_{i-1}Q_i(G_i)G_{i+1}\cdots G_n v\) where the middle quotient is entrywise. Use two active lanes of the same dimension to retain the ordinary product and the sum with a single marked quotient. After reading each pair \(X_i,Z_i\), the row states \(A,D\) advance by
\[
(A,D)\longmapsto (A G_i,\ D G_i + (A Q_i(G_i)) Z_i).
\]
This uses univariate layers. At \(X_i\), send the two lanes to three lanes \((A G_i,\ A Q_i(G_i),\ D G_i)\). At \(Z_i\), send them to two lanes \((A G_i,\ (A Q_i(G_i))Z_i+D G_i)\). This is a matrix with constant entries except for the marked lane multiplied by \(Z_i\). Start with \((a,0)\). The last layer \(Y\) sends \((A,D)\) to \(Y A v-D v\). By induction, each marked term in \(D v\) has exactly one \(Z_i\) and its required quotient product. The width is at most \(3r\). Multiplying and dividing the entries of each \(G_i\) by the prescribed univariate polynomials uses \(O(d_i^2)\) field operations per entry.

## Exact ranks of the reduced certificate

Let \(L=\{1,\ldots,k\}\), write \(g=\sum_{j=1}^{r_k} a_j(X_L)b_j(X_{\bar L})\) with both lists linearly independent, and let \(V_L\) be the span of the \(a_j\). For any index set \(I\) define \(D_I a=\sum_{i\in I}Z_i Q_i(a)\). At the cut after the complete pair \(X_k,Z_k\), the right factors \(Yb_j-D_{\bar L}b_j\) and \(b_j\) are together independent, by taking coefficients in \(Y\) first. The left factors are \(a_j\) and \(-D_L a_j\), and the two spans are disjoint since only the latter has positive degree in the \(Z\)'s. Thus the rank is \(r_k+\dim D_L(V_L)\).

At the cut between \(X_k\) and \(Z_k\), there is a third independent family \(Z_k b_j\) on the right, since \(D_{\bar L}\) involves neither \(Z_k\) nor \(Y\). The three left families are \(a_j,-D_{L\setminus\{k\}}a_j,-Q_k(a_j)\). The middle family has positive placeholder degree and the other two are placeholder-free. Thus the rank is
\[
\dim\big(V_L+Q_k(V_L)\big)+\dim D_{L\setminus\{k\}}(V_L).
\]
These ranks characterize exact width by the coefficient-rank characterization of ROABPs. In the affine Boolean case \(Q_i(a)=\alpha_i\partial_i a\) when \(u_i=\alpha_i X_i\). All of \(V_L\) is independent of any variable with zero coefficient. Hence the kernel of \(D_L\) on \(V_L\) consists of the constants in \(V_L\). The constant \(1\) belongs to that span exactly when \(|S_k|\ge |P_k|\). Full rank proves the forward sufficiency. In the other direction, a linear combination of Cauchy columns giving \(1\) on \(|P_k|\) rows would yield, after clearing the \(|S_k|\) distinct denominators, a monic polynomial up to sign of degree \(|S_k|\) with more than \(|S_k|\) roots. The boundary rank is consequently \(2r_k-\mathbf{1}_{|S_k|\ge |P_k|}\).

## Sharpness of the factor \(3\)

Take \(K=\mathbb Q(t)\), the Boolean grid with \(n=2m+1\), and use the weights \(1,2,\ldots,2^{m-1}\) on both sides of a middle weight \(1/2\). Let \(r=2^m\) and \(b=-(r-1)+t\). The cut just before and the cut just after the middle variable both have \(r_k=r\), and all cuts have \(r_k\le r\). Denominators never vanish in \(\mathbb Q(t)\). At the cut between the middle variable and its placeholder, the left coefficient span, represented by its Boolean evaluations, has generators indexed by the suffix sums \(j=0,\ldots,r-1\). Evaluate at a prior sum \(s\in\{0,\ldots,r-1\}\) and middle value \(0\) or \(1\) to get the two \(r\times r\) matrices
\[
A_{s,j}=\frac{1}{s+j-(r-1)+t},\qquad B_{s,j}=\frac{1}{s+j-(r-1)+1/2+t}.
\]
Over the local ring of rational functions regular at \(t=0\), \(tA\) reduces to the reversal permutation matrix \(J\), and \(B\) is regular. In particular \(B-A\) is invertible over \(K\), because \(t(B-A)\) specializes to \(-J\). Hence no nonzero element of \(V_L\) is independent of the middle variable. The image under \(Q_k\) has dimension \(r\) and is independent of that variable, so \(V_L+Q_k(V_L)\) has dimension \(2r\).

An element of \(\ker D_{L\setminus\{k\}}\) must be independent of all the prior variables. Its coefficient column \(c\) would make both \(Ac\) and \(Bc\) constant vectors. If \(Ac=0\), invertibility gives \(c=0\). Otherwise scale \(c\) to have \(Ac=\mathbf{1}\). The vector \(B A^{-1}\mathbf{1}/t\) is regular at \(0\) and specializes to \(B(0)J^{-1}\mathbf{1}=B(0)\mathbf{1}\). Its rows 0 and 1 differ: shifting the sum through \(j=0,\ldots,r-1\) changes it by
\[
\frac{1}{3/2}-\frac{1}{1/2-(r-1)},
\]
which is nonzero for \(r\ge2\). The original vector is therefore nonconstant as well. So the kernel is zero and the internal coefficient rank is exactly \(3r\), proving sharpness.

## Relation to earlier work

Grochow and Pitassi introduced IPS and its connection to circuit complexity. Forbes, Shpilka, Tzameret and Wigderson give variable-by-variable telescoping multilinearization for ROABPs and a polynomial-width IPS lift in Propositions 4.5 and 4.6, along with special-case subset-sum upper bounds. Our additions are the exact subset-sum width parameter for arbitrary separable mixed-domain equations, the capped synthesis algorithm using that parameter, and a single shared marked transition that gives a sharp factor-three lift in the specified reduced certificate order. The degree restriction is essential to the uniqueness and factor-three sharpness statements.

The transfer from Davis and GPT-6.2 Astra's CUT arithmetic-periodicity proof is its exact finite-state treatment of possible partial values, with a state cap that preserves the desired terminal test. Here the finite states are field-valued prefix and suffix sums. They are spliced at one layer to avoid constructing both large state sets. A separate marked state implements local divisions without a sum of separate branching programs. The companion Lean file checks the generic single-mark scan identity. The theorem as a whole has the written proof above.

- Joshua A. Grochow and Toniann Pitassi, [Circuit Complexity, Proof Complexity, and Polynomial Identity Testing](https://arxiv.org/abs/1404.3820).
- Michael A. Forbes, Amir Shpilka, Iddo Tzameret and Avi Wigderson, [Proof Complexity Lower Bounds from Algebraic Circuit Complexity](https://theoryofcomputing.org/articles/v017a010/), §4.2 and §4.4.
- A. Dailly, É. Duchêne, U. Larsson and G. Paris, [Partition games](https://arxiv.org/abs/1803.02621), §3.3 and Open Problem 4.
- Cinna Davis and GPT-6.2 Astra, [An ultimate arithmetic-periodicity test for CUT](https://github.com/1337isnot1337/solved-conjectures/blob/892c04046aadc8731dd510bb9c9b3ca1a086bae1/results/cut-arithmetic-periodicity/PROOF.md).

## Fixed-parameter search for an optimal variable order

The exact reciprocal width also gives an order-search algorithm for this family. For a set \(I\) of variable indices write \(\Sigma(I)=\sum_{i\in I} U_i\), where \(U_i=\{u_i(a):a\in A_i\}\) is translated by any one of its elements so that \(0\in U_i\). These translations preserve the cardinalities of every sumset. Fix a positive integer \(B\). There is an order of reciprocal width at most \(B\) exactly when there are a pivot variable \(v\) and a partition \(L\sqcup R=[n]\setminus\{v\}\) with
\[
|\Sigma(L)|\le B \qquad\text{and}\qquad |\Sigma(R)|\le B.
\]
The pivot construction in the width proof gives necessity. Any order placing \(L\) before \(v\) and \(R\) after \(v\) proves sufficiency, since every prefix before \(v\) has sumset size at most \(|\Sigma(L)|\) and every suffix after \(v\) has size at most \(|\Sigma(R)|\).

Try each pivot and discard it temporarily. If the union of the remaining \(U_i\setminus\{0\}\) has more than \(2(B-1)\) elements, that pivot cannot work. Every element from a left variable is in \(\Sigma(L)\), every element from a right variable is in \(\Sigma(R)\), and both sets contain zero. There are therefore at most \(2^{2(B-1)}\) distinct types \(U_i\) for a feasible pivot. Ignore types equal to \(\{0\}\), since they change neither sumset.

For each remaining type truncate its multiplicity to \(2B+1\). Deleting copies preserves a feasible split. Conversely, for any clipped type \(U\), a viable split after clipping has some side with at least \(B\) copies of \(U\). Its bounded sumset contains \(BU\), the sum of \(B\) copies of \(U\), because all other types contain zero. The sizes of \(0U=\{0\},1U,\ldots,BU\) are nondecreasing. If \(|BU|\le B\), at least one of the \(B\) inclusions is equality, and then every later inclusion is equality by adding \(U\). Restore the omitted copies on a side that already has at least \(B\) copies. Its sumset remains the same. This can be done for every clipped type because each restoration preserves both sumsets.

For each type enumerate its left multiplicity from zero to its clipped count. The right count is the complement. Test the two side sumsets by the capped scan and restore the deleted copies for any passing split. This uses at most \((2B+2)^{2^{2(B-1)}}\) splits per pivot and a polynomial in the input size and \(B\) field operation count per split. In the Boolean affine case each nonzero type has one nonzero element. The union bound gives only \(2(B-1)\) types per pivot, and the running time is \(2^{O(B\log(B+1))}\) times a polynomial in the input size. The algorithm finds an optimal reciprocal order by increasing \(B\) until it succeeds. It then gives a refutation in the recovered order of width at most three times the minimum reciprocal width, or returns a grid zero when there is one.

This is an order-search result for separable inputs in their given grid coordinates. General circuit-input ROABP order finding can be NP-hard, as shown by [C. Ramya and Pratik Shastri](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSTTCS.2025.49).
