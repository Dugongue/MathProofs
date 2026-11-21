# Prescribing localization spectra of one ordinary tensor comparison

Let \(F=\mathbb F_3\), and let \(B\) be ordinary three-tensor isomorphism over \(F\). A monotone span program over a fixed finite field \(K\) consists of a matrix \(M\) with columns labeled by input bits and a target \(b\). It accepts when the columns whose labels are true span \(b\). Repeated labels, zero columns, and arbitrary rank are allowed.

## Exact spectrum with all prime localizations isomorphic

**Theorem.** Given such a program with \(m\) selection bits and any number of ordinary ternary TI input queries, one can deterministically construct, in polynomial time, distinct monic linear polynomials \(f_1,\ldots,f_m\) in the fixed ring \(R=\mathbb Z[t]\) and one pair \(P,Q\) of ordinary free three-tensors over \(R\). For every \(S\subseteq[m]\),
\[
P\cong Q\text{ over }R_S=R[f_i^{-1}:i\in S]
\quad\Longleftrightarrow\quad
M\text{ accepts the selection }S\text{ and the actual TI answers}.
\]
The same pair is isomorphic over \(R_{\mathfrak p}\) at **every** prime ideal \(\mathfrak p\) of \(R\), over every finite quotient of \(R\), and over the inverse limit of its finite quotients. The construction can also use supplied ordinary-positive ternary comparisons with prescribed determinant signs as input bits. The individual bits only condition span-program columns. The comparison itself has no prescribed determinants.

Consequently every upward-closed family of subsets of \([m]\) is realized, with polynomial construction size in its explicit minimal-set list. This includes the empty family. Every output pair agrees at every prime localization even when all of the selected localizations \(R_S\) reject.

### A graph diagram over a quotient and a pin

Use the free congruence diagram of the previous localization theorem. Here both the data quotient \(R/I\) and the pin quotient \(R/J\) are fields. In each mode take the original free module \(V\), a second free copy with its basis fixed, and the graph of the identity modulo \(J\) in their direct sum. This forces the mode map to be identity modulo \(J\). Add the graph of the residue tensor modulo \(I\), in the direct sum of the input product space and output space, with the input product action tied to the two mode maps. Implement the graph as the image of a free covering arrow rather than requiring the graph itself to be free. For a tensor value lift \(T\) and generators \(a_1,\ldots,a_\ell\) of \(I\), this arrow sends
\[
(x,z_1,\ldots,z_\ell)\longmapsto
\left(x,\;Tx+\sum_j a_jz_j\right).
\]
If the mode maps \(G_X,G_Y,G_Z\) satisfy the tensor equation modulo \(I\), the difference \(G_ZT-U(G_X\otimes G_Y)\) is a sum \(\sum_j a_jD_j\). The automorphism of the covering domain with diagonal maps \(G_X\otimes G_Y,G_Z,\ldots,G_Z\) and lower first-column blocks \(D_j\) then supplies the required linked arrow. Conversely an isomorphism of diagrams preserves the graph image and gives the residue equation. All these statements hold after base change, including when an ideal becomes the unit ideal. This also applies to the pin graph.

For \(R_S\) in the theorem, the data and pin ideals survive and are comaximal. The residual determinants that can occur in the data diagram are exactly reductions modulo \(I\) of units of \(R_S\) congruent to one modulo \(J\). Necessity follows by taking determinants. For sufficiency take a residue transporter with those determinants, remove one diagonal entry realizing the allowed unit in each mode, and express the remaining special-linear field matrices as products of elementary matrices. Lift the elementary entries so they vanish at \(J\) and have the given residues at \(I\), by the Chinese remainder theorem. The allowed unit has residue one at the pin. This gives the asserted lift, including rank one. [Free graph and pin diagrams](prior/transfer.md)

### Arithmetically independent selection bits

Choose distinct odd primes \(q_0,q_1,\ldots,q_m\), all different from three. A sieve through a polynomial bound in \(m+1\) suffices by the elementary prime-counting bounds. Choose integers \(a_i\), adding distinct multiples of the common modulus if needed, so that \(f_i=t-a_i\) satisfies
\[
 f_i(0)\equiv
 \begin{cases}
 -1&\pmod{q_i},\\
 1&\pmod{q_j}\quad(j\ne i,\ 0\le j\le m),\\
 1&\pmod3.
 \end{cases}
\]
The moduli are coprime, and the coefficients \(a_i\) have polynomial bit length. The polynomials \(f_i\) are irreducible and pairwise nonassociate. Since \(R\) is factorial, the units of \(R_S\) are exactly \(\pm\prod_{i\in S}f_i^{z_i}\) for integer \(z_i\).

Use the same pin ideal \(J=(q_0,t)\) in all selection tests. A unit congruent to one at \(J\) has positive leading sign, since all \(f_i(0)\equiv1\bmod q_0\). At data ideal \(I_j=(q_j,t)\), the permitted unit images are \(\{1\}\) for \(j\notin S\), and \(\{1,-1\}\) for \(j\in S\), independently of every other selected index. For bit \(j\), use the dimension-one residue tensor pair \(1,-1\) with this data ideal and pin every mode at \(J\). It has a linked isomorphism over \(R_S\) exactly when the negative sign is allowed.

At \(I_*=(3,t)\), the permitted unit image is always \(\{1\}\). Thus a ternary pair with the target pre-reflected by any prescribed sign gives its signed feasibility bit over **every** \(R_S\). For an ordinary query \(x\) use the earlier parity-rigid product construction. It gives a reflected self-pair with an explicit ordinary witness whose determinant-one answer is \(B(x)\), independent of whether \(x\) is ordinary YES. Put this signed atom at \(I_*\). This gives all ordinary ternary TI bits without requiring an ordinary solver. [Ordinary query to a signed test with displayed witness](https://github.com/Dugongue/MathProofs/blob/002a1088187a6f9e08e08b3c4fe5d20ba53bee15/TISLDirectionalGap/RESULTS.md#a-reduction-from-ordinary-nonisomorphism-into-the-promise)

Every bit diagram above has an isomorphism at every prime localization of \(R\). The data and pin ideals are comaximal, so at most one survives at any one prime. If only the pin survives, use identities on the original roles. At the data prime an ordinary residue witness lifts simply by lifting its matrix entries: its determinant lies outside the prime and is therefore a unit. Such a witness exists for every selection atom and for every reflected self-pair used for ordinary TI. For a signed input atom it is part of the ordinary-positive premise.

For later use make one permanently disabled atom, using \(1,-1\) over \(\mathbb F_3\) at \(I_*\) with the same pin \(J\). It is NO over every \(R_S\) and YES at every prime localization of \(R\).

### One free tensor assembly

All the preceding bit diagrams use finitely many free modules, linear maps, fixed vectors, and bilinear maps. The earlier two-tag packing followed by ordinary algebra-to-tensor compilation converts each to one ordinary tensor pair over \(R\). Its correctness and recovery also apply over every domain used here, and the same coefficients are used after change of base. This locality is important because no tensor is rebuilt when \(S\) varies. [Explicit diagram packing](prior/transfer.md) · [Ordinary free algebra and tensor reductions over domains](https://arxiv.org/html/2611.00735v1#S3.SS3)

For clarity, positive span-program compilation also works over these same domains. Associate a plain positive-format tensor \(T\) to its three-vertex associative triangular algebra \(\Lambda(T)\). Its diagonal is \(R^3\), its corners are the three tensor spaces, and its only nonzero strict-corner product is the tensor. For a domain the strict-corner ideal is the largest nilpotent ideal by the reduced quotient. Align idempotents by a unit of the form \(1+j\) with \(j\) nilpotent. The three nonzero ordered corner spaces then force the vertices in order, and the remaining equations are exactly the tensor transporter equations. Conversely every transporter extends. This proof works over all \(R_S\) and \(R_{\mathfrak p}\). The use of positive format ensures the three corners are present, and trivial instances can be normalized first.

For a bit comparison \(T,U\), take the product with one copy of \(\Lambda(T)\) in position zero and copies of \(\Lambda(U)\) in all other positions indexed by \(K\). Link the product-factor identities to the primitive basis idempotents \(e_x\) of \(R^K\). Mark all fixed translations \(e_x\mapsto e_{x+c}\) on that split algebra. A transporter on it must be a translation by some \(z\in K\). A zero translation is always available. A nonzero translation is available exactly when \(T\cong U\), and then all translations lift. Factor maps can be chosen independently.

Use one such coefficient variable for each program column. Multiplication of \(z\) by a fixed \(a\in K\) is imposed by a linear link \(e_x\mapsto e_{ax}\), and sum by a bilinear link \((e_x,e_y)\mapsto e_{x+y}\). Those maps force exactly the prescribed transformations of translation parameters. At the endpoint of each sum, mark the vector \(e_0\) in the source and the requested \(e_{b_j}\) in the target. This imposes \(Mz=b\). Intermediate \(R^K\) spaces again carry their split multiplication and marked translations; use fresh spaces for each term or sum. All these spaces and maps have polynomial total description length for fixed \(K\), and the same diagram packing converts them into one plain ordinary TI pair. [Positive switches and span programs over fields](https://github.com/Dugongue/MathProofs/blob/002a1088187a6f9e08e08b3c4fe5d20ba53bee15/TISLDirectionalGap/Aggregate.md)

Include an extra copy of the column \(b\), controlled by the permanently disabled bit. It never changes the span over any \(R_S\). At every \(R_{\mathfrak p}\) that column is enabled, so putting coefficient one on it and zero elsewhere gives the required isomorphism, even when the original full matrix does not span \(b\). This proves the theorem. For a finite quotient \(C\) of \(R\), decompose \(C\) into finite local factors. The map to each factor factors through \(R_{\mathfrak p}\) for the preimage of its maximal ideal. Reduce its transporter to that factor and combine the resulting maps by the product decomposition to get an ordinary \(C\)-transporter. In the inverse limit of the finite quotients, include inverse matrices in the witness tuples. Every finite collection of compatibility equations has a solution by taking a witness modulo the intersection of the finitely many finite-index ideals. Compactness of the product of the finite witness sets gives a compatible tuple and hence an isomorphism over the profinite completion.

### Consequences for localization problems

Reachability of two vertices in an undirected graph is a span program over \(\mathbb F_2\): the target is the sum of the endpoint vectors, and each enabled edge contributes its incidence vector. A series-parallel graph with series for AND and parallel for OR implements any monotone formula of the given size. In particular a disjoint path per minimal selected set realizes any upward-closed family in the theorem with complexity polynomial in the written antichain. A zero target supplies the constant-true case and the permanently disabled column allows the constant-false case.

On the annotated family with its displayed formula, finding a successful localization that inverts at most \(k\) listed factors is NP-complete already with all input atoms selection bits. Reduce Vertex Cover using \(\bigwedge_{uv\in E}(s_u\vee s_v)\). The same construction gives a count-preserving reduction from counting vertex covers to counting the successful subsets, so this counting problem is \(\#\mathrm P\)-complete under polynomial-time Turing reductions on the annotated family. The membership algorithms evaluate the given formula. The hardness maps output one pair that passes every prime-local and finite-quotient comparison. [Counting vertex covers](https://doi.org/10.1137/0212053)

The construction proves an exact simultaneous statement about one pair over a fixed ring. It does not assert polynomial compilation of arbitrary succinct monotone circuits into small span programs. All constructions in this chapter are written proofs.
