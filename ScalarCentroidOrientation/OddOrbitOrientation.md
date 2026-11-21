# Determinant tests from odd transporter orbits on bounded tuples

Work over \(F=\mathbb F_3\). A based symmetric bimap \(\beta:X\times X\to Z\) is transported by \((g,h)\) with \(h\beta=\beta'(g,g)\). The signed cube-zero question tests \(\det(g)\det(h)\) on this same pair. The earlier cube-zero reduction has even \(\dim X\), odd \(\dim Z\), zero common radical and spanning output. Its algebra determinant equals the indicated product, and its exact cubic lifts have that same sign in even algebra dimension. [Cube-zero normal form and exact cubic transporters](ExactCubicOrientationSeed.md)

## 1. One ordinary TI comparison from short-tuple orbits

Suppose that a specified ordinary comparison has finite label sets on both sides of polynomial cardinality. Each raw transporter induces a bijection of labels. A simultaneous prescribed image of a bounded tuple of labels is tested by one ordinary TI instance, by the fixed-signature tensor-system compiler with those marks. Assume that the sign to be tested, after a computable frame calibration, is the parity of a sum of polynomially many predicates, each depending only on the images of a fixed bounded tuple of source labels. Tuple length is independent of input size. For example the sign of the permutation of a based intrinsic line set is the parity of the inversion count. A signed monomial action has in addition a sum of one-label predicates for the negative scalars.

Assume the exact orbits of the target stabilizer on candidate tuples for these predicates are computable in polynomial time, and that the effective target stabilizer on the labels used for the sign has odd order. One sufficient way to compute these orbits is an explicit list of genuine automorphism generators whose short-tuple orbits agree with deterministically computed covariant color classes. Extra sign-neutral automorphisms in the kernel of the label action are unrestricted.

**Theorem.** On this domain the prescribed sign is decidable by one deterministic polynomial-size ordinary TI instance over \(F\). No bound is imposed on the number of transporters or on the size of a set of labels required to distinguish them.

**Proof.** Keep one ordinary guard for the raw comparison. When it is true the induced label bijections form the coset of the effective target stabilizer on these labels. This coset has odd cardinality. The sign character restricted to that stabilizer is trivial, since every homomorphism from an odd-order group to \(\{1,-1\}\) is trivial. Therefore the requested parity is constant on the coset and equals the sum of the parity over its members modulo two.

For each short tuple \(u\), its attainable images are exactly one target tuple orbit \(O\). Every element of \(O\) occurs equally often among the induced bijections, by the orbit–stabilizer theorem. That multiplicity is odd because the effective group has odd order. The contribution to the sum of parities is therefore the sum of the predicate over \(O\), computable from the explicit candidate tuple lists once its orbit is identified.

For every source tuple used and every target orbit, make the ordinary pin query taking that tuple to a representative of the orbit. This query is YES exactly when the orbit is attainable, because the generators in the target stabilize the raw instance. With the guard true, exactly one orbit query is YES in each tuple row. Introduce one binary variable for each orbit query, forced to be zero when the query is NO. Require their sum modulo two in every tuple row to be one. For every variable multiply its value in the final sum by the precomputed predicate parity on that orbit. Require the resulting sum modulo two to be the target parity after the known calibration. The linear-switch compiler gives one ordinary comparison for these equations. On a guarded YES input the variables are forced to select precisely the actual orbit in each tuple row, so the output has the claimed reflection and extension properties. There is no need for complementary ordinary queries, individual witnesses, or a chosen ordering among feasible transports. Conjoin the ordinary guard to discard all other inputs. [Linear switch compiler](https://github.com/Dugongue/MathProofs/blob/main/TISLWorlds500/prior/prior/earlier/baseline/baseline/LinearSwitchCompiler.md) [Fixed tensor-system signature](https://arxiv.org/html/2306.03135v2#S4)

For example, on a finite faithful permutation action it suffices that all ordered-pair orbits have odd size. If the group had even order it would contain a nonidentity involution. That involution swaps some two labels, so the orbit of that ordered pair is closed under reversal and has even size. This contradicts the stated test.

Polynomially many guarded branches can be combined if the short-tuple hypotheses are only used within branches, each with the corresponding stabilizer and a correctly tested raw comparison. For the ordinary OR gate, from two pairs \((A,B),(C,D)\) make the two unordered collections of ordered pairs \(\{(A,C),(B,D)\}\) and \(\{(A,D),(B,C)\}\). Ordered pairs are encoded by a fixed two-part typed mark and then by centrally indecomposable triangular multiplication algebras. Compare products of the two connected algebra factors, whose matching either asks for \(A\cong B\) or for \(C\cong D\). This gives the standard binary ordinary-TI OR with linear side-size overhead. Ordinary AND uses an ordered marked pair. Balancing polynomially many such gates gives logarithmic depth and polynomial blowup under linear side-length growth. In the application below there is a single branch. [Grochow–Qiao, linear-length reductions](https://arxiv.org/abs/2306.16317)

## 2. A scalar-centroid bimap with intrinsic edge labels

Let \(G\) be a connected triangle-free simple graph of minimum degree at least two. Use a vector \(x_v\) for every vertex and a label \(z_v\) for every vertex and \(z_{vw}\) for every edge. Define a symmetric bimap by
\[
 \beta(x_v,x_v)=z_v,\qquad \beta(x_v,x_w)=z_{vw}\quad(vw\in E(G)),
\]
and zero for distinct nonadjacent vertices. The displayed labels are independent. The bimap spans its label module and its common radical is zero, since evaluating on \(x_v\) detects the coefficient of \(x_v\) at \(z_v\).

The projective vertex basis is intrinsic. First solve for infinitesimal derivation pairs \((P,Q)\) by
\[
 Q\beta(x,y)=\beta(Px,y)+\beta(x,Py).
\]
For distinct nonadjacent \(i,j\), the equation on \(x_i,x_j\) forces \(P_{ij}=P_{ji}=0\) on the independent square labels. For an adjacent pair \(i,j\), take a neighbor \(k\ne i\) of \(j\). The triangle-free condition makes \(ik\) a nonedge. In its equation the edge label \(z_{jk}\) appears only through the coefficient \(P_{ji}\), forcing it to vanish. The reverse entry follows in the same way. Every diagonal \(P\) extends by its pairwise sums on the displayed labels, so the projected solution space is the full diagonal algebra. It is covariant under the actual transporter by conjugation. Recover its primitive idempotents by simultaneous refinement with the \(F\)-polynomials \(1-(P-aI)^2\), \(a\in F\), on a basis of this algebra. This recovers the vertex lines, and reading zero and nonzero products recovers the graph. Their square and edge lines are forced by the actual label map. These polynomial operations also verify the displayed graph-bimap model on raw inputs, by checking ranks and independence in the recovered lines.

The centroid of this bimap is scalar. In the centroid equations \(\beta(Px_i,x_j)=\beta(x_i,Px_j)\), the two separate square labels kill every off-diagonal entry of \(P\). Testing the edge labels then equates the two diagonal values along each edge. Connectivity makes them all equal, and spanning forces the same scalar on the label action.

Every transporter is thus monomial on the vertex lines and has scalar \(\lambda_v\in F^\times\) on the chosen representative of the line at \(v\), followed by a graph isomorphism \(\pi\). Conversely any such scalar choices and any graph isomorphism lift, by the displayed products. In the model vertex and label frames,
\[
 \det(g)\det(h)=
 \operatorname{sgn}(\pi_{E(G)})\prod_v \lambda_v^{\,1+\deg(v)} .
 \tag{1}
\]
Indeed the label permutation on square labels is the same vertex permutation, so its sign cancels the vertex sign. Each edge scalar is the product of its endpoint scalars, and the square scalars are \(1\) over \(F\). The raw comparison has the known ratio of the endpoint frame determinants as calibration. In particular if all graph degrees are odd the scalar symmetries disappear from the requested character. It is then an inversion parity on the induced edge permutation. A pin on an edge is a simultaneous pin on its intrinsic label line, with the scalar free. Keeping two such pins in one ordinary comparison uses the same \(g,h\). Thus the theorem of Section 1 applies whenever the graph has computable ordered edge-pair orbits and odd effective permutation group on its edges.

## 3. A recognizable family with exponentially many effective transports

Here is an explicit connected graph family meeting the previous conditions in the parity format of the cube-zero normal form. For the fixed decorations start with three cubic bipartite graphs on \(2m\) vertices, \(m=10,11,12\). With each part indexed \(0,\ldots,m-1\), join \(i\) in the first part to \(i,P(i),Q(i)\) in the other part, using these permutations:
\[
\begin{array}{c|l|l}
m&P&Q\\ \hline
10&(6,9,7,4,8,0,5,3,2,1)&(3,8,4,2,5,9,1,6,7,0)\\
11&(1,0,5,10,6,8,2,9,4,3,7)&(6,4,10,5,0,3,8,1,7,2,9)\\
12&(7,5,0,10,6,11,3,8,4,2,1,9)&(11,2,8,6,5,10,4,9,1,0,7,3)
\end{array}
\]
They are connected and asymmetric. A small exact verification uses the all-pairs distances in the displayed graphs. Start all vertices at one color, and replace the color of each vertex by its old color together with the multiset of pairs (distance, old color of the target vertex). On the three graphs the first rounds give \(7,13,8\) colors and the second rounds give \(20,22,24\) colors, respectively. Thus every automorphism fixes each vertex. The distance tables have no infinite entries. Each graph is bridgeless: a single bridge would give a cut component with bipartite degree difference divisible by three before subtracting the one missing edge, which is impossible. In each graph subdivide the edge joining the two zero-index vertices, call the inserted degree-two vertex its root, and call the three rooted graphs \(B,C,D\), of sizes \(21,23,25\). They are triangle-free and bridgeless. A rooted automorphism would contract to an automorphism of the original graph, so all are rooted-rigid. All their other vertices have degree three.

For \(s\ge2\), take a spine of \(s\) vertices in a path. At each spine position attach, by a bridge to a root, a 13-vertex block made of a 12-cycle and its root. Label the cyclic positions
\[
 A_i,B_i,C_i,D_i,A_{i+1}\qquad(i\bmod 3),
\]
and join the root to the three \(A_i\)'s. Attach a copy of the corresponding decoration \(B,C,D\) by a bridge at each of the nine vertices \(B_i,C_i,D_i\), using the degree-two root of each decoration as its endpoint. Attach one more \(B\)-decoration to the 13-vertex block's root. Finally put a \(B\)-decoration at the first spine endpoint and a \(D\)-decoration at the last.

After removing bridges, the nontrivial pieces are exactly the rigid decorations and the 13-vertex blocks. In each block the root is the degree-five vertex and the three padded colors preserve the forward pattern of the 12-cycle. There are three rotations by multiples of four positions and no reflection preserving that pattern. Each of the three rotations extends to the rooted decorations by their uniquely determined identifications. The two end decorations fix the spine orientation, so no two 13-vertex blocks can be interchanged. Hence the graph automorphism group is exactly the product of \(s\) cyclic groups of order three. These generators are explicit and recoverable in polynomial time. In a raw graph the same construction is recognized by bridge decomposition, testing the constant-sized rooted pieces, and checking the oriented remaining spine and the attachments. Thus the exact ordered edge-pair orbits are found by traversing the group generators on the polynomial-size set of ordered edge pairs. This does not enumerate the whole automorphism group.

The graph is connected and triangle-free. Each spine and decoration vertex has degree three after attachment, and the only degree-five vertices are the \(s\) cycle-block roots. The counts are
\[
 |V|=242s+46,\qquad |E|=364s+69.
\]
In particular \(\dim X=|V|\) is even and \(\dim Z=|V|+|E|\) is odd. The graph subgroup is faithful on its edge labels, since the incident edge sets determine all vertices of degree at least two. It has odd order \(3^s\). Section 2 therefore gives a scalar-centroid cube-zero family with full explicit short-tuple data. The large diagonal sign kernel on \(X\) is harmless by (1). Even the effective label action has exponentially many elements, so a branch that distinguishes all effective maps by pins would require exponentially many joint anchor images. The odd-orbit construction uses polynomially many short pins instead.

Every self-transporter has total sign one by (1) and the odd group. Applying a determinant-\(-1\) change of basis on the target label map produces an ordinarily equivalent bimap for which every transporter has total sign \(-1\) in the two original frames. Thus the sign constraint distinguishes instances in the same ordinary orbit on this family. The written proof is a sufficient class, with a separate general bounded-tuple criterion for other intrinsic finite actions.

## 4. A direct parity calibration when a covariant tournament is available

There is a related shortcut in any monomial situation where the relevant unsigned label set carries a computable covariant tournament. In raw orders let \(b_{ij}\in\{1,-1\}\) be the sign of the orientation for \(i<j\), and use \(b_{ji}=-b_{ij}\). An isomorphism \(\pi\) preserving the tournament satisfies \(b_{ij}=b'_{\pi(i)\pi(j)}\). Taking the product over all unordered pairs gives
\[
 \prod_{i<j}b_{ij}
   =\operatorname{sgn}(\pi)\prod_{i<j}b'_{ij}.
\]
So the parity of the permutation is known from endpoint data alone, with no short-tuple orbit calculation. For example it can be used in (1) when there is such an intrinsic tournament on the edge labels and the degree parity cancels the diagonal scalar signs. This is an explicit calibration on the actual transporter. [Tournament orientation parity](https://arxiv.org/abs/2204.01947)

The proofs here use ordinary TI and the earlier positive linear-switch reduction. They apply to the stated scalar-centroid cube-zero families and to any bounded-tuple setting satisfying the theorem's hypotheses. The unrestricted cube-zero comparison is not settled by these conditions.
