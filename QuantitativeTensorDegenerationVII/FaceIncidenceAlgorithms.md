# A sharp incidence threshold for exact Laurent cap optimization

A rank-three flag pair is an admissible thin Peirce pair with \(0/1\) constants, of a common type, with vertex ranks in \(\{0,1,2\}\). Each nonzero product of two strict corners has the form \(xy\cdot yz=xz\) with ranks \(0,1,2\). Only some such constants are deleted in the target. This includes the barycentric flag tables of two-dimensional simplicial complexes, with successor-only corners added to make reachability total. Call an edge active if it occurs in a source strict product. Its incidence is the number of such products containing it. Caps bound the entry poles in the three independent Laurent mode transformations. [Thin cap extraction](WitnessCircuits.md)

**Theorem.** Over every coefficient field, for these explicitly represented pairs:

1. If the maximum incidence is at most two, exact minimum polynomial order, the full forward cap region, and an optimal diagonal witness are computable in deterministic polynomial bit time. Binary lower or upper bounds on each marked contact, including exact prescribed contacts, can be imposed. This applies to triangulated surfaces without an orientability or genus restriction.
2. If the face rows can be oriented coherently, ordinary directed circulation suffices. The least integer order is the ceiling of the LP optimum, and a cut formula gives that rational optimum. For a feasible pair with \(M\) marks and no additional contact bounds, the minimum order is at most \(M\) in this coherent case, and at most \(2M\) without coherence.
3. At maximum incidence three, cap feasibility is NP-complete even at the fixed cap sum \(1048575\). This holds on sparse barycentric flag pairs admitting a constant-order witness with normalized image degree at most \(4\). Approximation within any fixed factor strictly smaller than \(3/2\) is NP-hard.

## 1. Reducing three caps to a box on the active weights

Use the arbitrary-map thin cap extraction. A scalar redistribution puts cap sum \(p\) in the form \((0,0,p)\). Every such witness gives integer corner weights \(w_{xy}\), including \(w_{xx}=0\), and vertex weights \(\alpha_x,\beta_x\) with
\[
 w_{xy}\le\alpha_x+\beta_x-\beta_y,\qquad
 w_{xy}\le\beta_x,\qquad
 w_{xy}\ge\alpha_x+\beta_x-p .
\tag{1}
\]
The defects \(w_{xz}-w_{xy}-w_{yz}\) are zero at retained products and in their prescribed positive ranges at the marks. These constraints are sufficient as well.

For the rank-three problem we can force \(\alpha=\beta=0\) with the same \(p\) and defects. On the active graph seek a vertex gauge \(u\) such that
\[
 -p\le w_{xy}+u_y-u_x\le0.
\tag{2}
\]
These are ordinary difference constraints, with costs \(-w_{xy}\) on a forward arc and \(p+w_{xy}\) on its reverse. The three-layer graph of (1) has reward edges \(B_x\to A_y,\ A_x\to C_y,\ C_y\to B_x\) with rewards \(w_{xy},w_{xy},-w_{xy}\). Every closed layered walk has reward at most \(p\) times its number of backward slots, by summing the three difference inequalities with potentials \(C=u,\ A=u+\beta,\ B=u+\alpha+\beta\).

In every closed signed walk of the active graph, the forward run between consecutive backwards has length at most two, since active edges strictly increase rank. Rotate the walk to start just after a backward step, and insert identity steps to make every such forward run have exactly two slots. This gives a layered closed walk with unchanged signed reward and unchanged backward count. Hence the difference constraints (2) have no negative cycle. Shortest paths from an extra root with zero-cost arcs to all vertices give a potential, integral for integer \(p,w\).

The gauge cancels in every defect. Set the weights on inactive edges to zero, since they affect no defect. In particular, putting \(x_{xy}=-w_{xy}\) in the new gauge, the exact problem is
\[
 0\le x_e\le p,\qquad
 (Dx)_f=x_{xy}+x_{yz}-x_{xz}\in[L_f,U_f]
 \quad(f=(x,y,z)).
\tag{3}
\]
Retained faces have interval \([0,0]\), and a marked face has \(L_f\ge1\) with an optional \(U_f=+\infty\). A solution gives polynomial input maps \(H^{-1},H^{-1}\) and output \(t^pH\), where \(H\) has corner entry \(t^{-x_e}\). All matrix degrees are at most \(p\). Conversely a polynomial presentation of order \(p\) gives a Laurent witness after dividing its output by \(t^p\). The proof works over the rationals as well for the LP relaxation.

## 2. Incidence two and capacitated matching

When every active edge is in at most two faces, \(D\) in (3) is a signed incidence matrix with at most two entries of magnitude one per column. To reduce (3) to capacitated undirected matching, at each endpoint of an edge column write \(y_{fe}=x_e\) for a positive sign and \(y_{fe}=p-x_e\) for a negative sign. The degree interval on \(\sum_e y_{fe}\) comes from \([L_f,U_f]\) by adding \(p\) per negative incidence. Clamp it to the natural range from zero to the number of its incidences times \(p\), rejecting empty intervals. A column with two equal signs has equal \(y\)-values at both ends, so it gives one graph edge of capacity \(p\). A column with opposite signs has values summing to \(p\). Represent it by two edges of capacity \(p\) through a fresh vertex of required degree \(p\). A singleton column uses an edge of capacity \(p\) to a fresh vertex with degree interval \([0,p]\). These constructions are bijective on feasible integer assignments after discarding irrelevant free weights.

To handle both bounds on vertex degree, add a private slack edge of capacity \(u-\ell\) at each constrained vertex with interval \([\ell,u]\). Give that vertex upper degree \(u\), and give its slack leaf upper degree \(u-\ell\). Maximize the sum of the degrees of the constrained vertices by weighting each edge by its number of constrained endpoints. Reaching the sum of all constrained upper degrees is equivalent to meeting every original interval. Capacitated \(b\)-matching with linear weights is polynomial in the binary input length by odd-cut separation and the ellipsoid method. Thus the algorithm does not expand a binary capacity into that many copies. [Edmonds–Johnson](https://www.math.uwaterloo.ca/~bico/co759/papers/edmonds_johnson1970.pdf) [Padberg–Rao](https://doi.org/10.1287/moor.7.1.67)

Feasibility is monotone in \(p\). For binary contact intervals, apply the ordinary small-solution bound for integer linear systems to (3), including \(p\) as an additional nonnegative integer variable and adding slacks. This gives a computable bound of polynomial bit length for any finite minimum. Binary search then gives the exact order or reports infeasibility, and one final matching yields the witness. With only positive marked contacts the smaller bound in Section 3 suffices. [Papadimitriou](https://dspace.mit.edu/entities/publication/9e3bac47-5459-4374-b9f2-2488412c6f05)

For a triangulated surface, \(v\subset e\) lies in as many flags as there are original faces at \(e\). Each \(e\subset f\) and \(v\subset f\) lies in two flags. Thus incidence two holds even on closed nonorientable surfaces with arbitrarily large first cohomology.

## 3. The coherent case and the linear cap bound

Coherence means multiplying each row of \(D\) by a sign makes its two incidences opposite in every two-incidence column. This holds when the flag faces form an orientable surface, and is also testable by sign propagation on any incidence-two input. Interpret the resulting matrix as directed incidence, with positive sign at a source and negative at a sink. Complete every singleton column at an exterior vertex \(*\) with the opposite sign. The bounds on net outflow at \(f\) are the signed interval \([\underline b_f,\overline b_f]\), obtained from \([L_f,U_f]\) by applying its sign. At \(*\) leave net outflow unrestricted.

For every set \(A\) of faces, let \(\partial^+(A)\) and \(\partial^-(A)\) be the outgoing and incoming dual arcs, including arcs to \(*\). The exact rational cap threshold \(\lambda\) is the least nonnegative \(p\) such that
\[
 \sum_{f\in A}\underline b_f\le p|\partial^+(A)|,\qquad
 -\sum_{f\in A}\overline b_f\le p|\partial^-(A)|
 \quad\text{for all } A .
\tag{4}
\]
For example a positive numerator with zero denominator gives infeasibility. Necessity follows by summing net outflows. For sufficiency, add an auxiliary arc between \(*\) and each face whose allowable imbalance is nonzero. Its direction offsets the permitted sign of that face's imbalance, and its capacity interval is the corresponding interval of absolute amounts. These signs are fixed because retained intervals are \([0,0]\) and all marked contacts are positive. The ordinary circulation theorem with lower and upper capacities gives (4) by applying the cut criterion to sets omitting \(*\) and to their complements. Infinite upper bounds can be truncated at the maximum outflow possible at the specified \(p\). At integer \(p\), all capacities and lower bounds are integral, so a rational solution gives an integral circulation. The integer optimum is therefore \(\lceil\lambda\rceil\).

For the cap bound with only positivity at the marks, omit the upper box in (3), introduce one nonnegative slack per mark, and write the retained and marked equations as \([D\ -I_J](x,s)=b\), \(b_f=1\) at the marks and zero elsewhere. If this nonnegative system is feasible, it has a basic feasible solution, obtained for example by minimizing the sum of all its variables. Retain independent rows and use a nonsingular square basis. Every column of the basis still has at most two nonzero entries, each a sign.

View the basis as a graph on its row vertices, with a two-ended edge for a two-entry column and a half-edge for a singleton. Every connected component has the same number of rows and columns by invertibility. Its two-ended edges connect the component, so it is either a tree with one half-edge or a unicyclic component with none. In a tree, successive elimination at leaves determines each variable as a signed sum of right-hand sides from a subtree. Its absolute value is at most the sum of the absolute right-hand sides on the component. In a unicyclic component, first eliminate the attached trees. On the cycle, solve the equations successively as signed recurrences in a starting variable. Nonsingularity forces the return equation to have coefficient \(2\) or \(-2\) on this variable. Its right-hand side is a signed sum of the adjusted cycle right-hand sides. Starting the recurrence at any cycle edge bounds every cycle variable by half the component sum of absolute original right-hand sides. Thus all basis values are half-integral and at most \(M\) in absolute value. Doubling gives an integral cochain with cap at most \(2M\) and positive integral defects. If the orientation is coherent, a unicyclic basis component is singular, since its columns sum to zero on that component. All surviving bases are integral, giving cap at most \(M\). This proof allows boundary edges, disconnected face graphs, and repeated dual adjacencies. It does not assume orientability for the \(2M\) assertion. [Oriented boundary matrices and total unimodularity](https://arxiv.org/abs/1001.0338)

## 4. Incidence three is already NP-complete

Start with the earlier NAE-3SAT reduction to marked contact lattices. Its simplicial core realizes positive contact vectors \(c_i\), one per output circle \(y_i\), and decides NAE by whether all \(c_i\le2\). A fixed fallback assignment supplies all \(c_i\le4\). The earlier cap reduction attaches a telescope at every output circle, and a length-\(L\) tail yields the lower bound \(p\ge 2^L c_i/3\) by the terminal signed cycle. To retain that separation with incidence at most three, two local changes suffice. [Contact lattice construction](ContactSeed.md) [Fixed-cap reduction](WitnessCircuits.md)

**Bounded occurrence in the attaching words.** Regard the original expression for each contact as a circuit of signed additions, copies, and doublings. Each generator gets its own three-edge bouquet circle. A gate is imposed by its defining word, of at most three letters including its output letter. Replace fanout beyond two by binary copy trees with fresh circles. Count repeated uses separately, including the two uses in a doubling. A free generator occurs in at most two downstream words, and a defined generator occurs once as output and at most twice downstream. Reserve each marked output \(y_i\) as a sink, using a final copy if needed, so it occurs in precisely one defining word and no downstream word. The extra copy equations eliminate their generators, so the contact lattice is unchanged. The number of letters and new generators remains polynomial, and all copy gates preserve the evaluation bound on intermediate generators.

For every occurrence of a generator letter, each edge of its bouquet circle appears once as a bottom edge of the attached strip. The strip adds exactly one triangle on that edge per occurrence. All other strip and relation-cone edges are in at most two triangles. In particular no nonmark bouquet edge is in more than three triangles. Each output circle so far has one triangle on each edge from its defining word, and the marked cap adds one more.

**A collar before each tail.** Attach a new triangulated annulus of circumference three between \(y_i\) and the first Möbius core. If \(b_j\) are the old vertices and \(a_j\) the new vertices, its triangles are \([a_j,b_j,b_{j+1}]\) and \([a_j,b_{j+1},a_{j+1}]\), with cyclic indices. Each edge of either boundary gains just one triangle. Thus the edge on \(y_i\) is in at most three triangles, and the new first core receives one from the collar and two from its Möbius band. Each later core likewise has one incident triangle from the previous annulus and two from the next band. The other edges of the band-and-annulus telescope have at most two incidences. The collar preserves the starting circle's homology class and admits the same angle construction by assigning \(a_j\) the lifted angle of \(b_j\). Each collar triangle has angle span at most \(c_i/3\).

After barycentric subdivision, a vertex-to-edge incidence has as many flags as the original edge's triangle incidences. An edge-to-face or vertex-to-face incidence has two flags. Added successor corners have no strict products. Hence the derived tensor type meets the incidence-three restriction. The mark is still in the interior of its own cap, and its alternate rank-one intermediate keeps the same radical square at both endpoints.

The numerical bounds from the fixed-cap reduction are unchanged. Every relation walk still has at most nine edges, and its generator evaluations on the yes and fallback assignments have magnitude at most \(45\). The core integer cochain bound \(5000\) holds by the same cumulative-potential construction and the same cap gauge. Each collar and telescope starts with circle weights of magnitude at most \(2\) for \(c_i\le4\). They admit normalized weights in \([-2^L c_i/3,0]\). Reconcile these with the core via the bounded integer gauge on the shared six-edge circle. The earlier estimate puts all normalized weights in
\[
 [-2^L\max_i c_i/3-\Delta,\ \Delta],\qquad
 \Delta=12(5000+2)+3=60027 .
\]
The constant vertex choice \(\alpha_x=\beta_x=\Delta\) therefore gives rational cap \(2^L\max_i c_i/3+3\Delta\), and integer difference potentials at its ceiling. Conversely the lower bound \(p\ge2^L c_i/3\) is unchanged for all \(i\). For completeness, the equations on the attached circles and collars introduce no new required positive defects; the marked contact vectors come from the original core, and every such vector extends over the tails.

With \(L=20\), a yes instance has cap at most \(879132\), and any no instance has cap at least \(1048576\). The fallback assignment gives cap at most \(1578183\) with normalized image degree at most \(4\), since there are no nonzero defects other than its marks in the monomial witness. The construction has size polynomial in the formula length, including all copy gates and collars. The integral certificate for (3), with all coordinates between \(0\) and the specified cap, proves membership in NP. This gives NP-completeness at the stated fixed cap. For any fixed approximation ratio less than \(3/2\), increasing the same constant \(L\) makes the yes upper bound, after multiplication by that ratio, strictly less than the no lower bound.

The matching and flow theorems solve the integer programs once the reduction (2) has removed the cap interactions. The geometric reduction uses the earlier Möbius degree doubling. The new bounded-occurrence steps account for every incidence at the gluing circles and make the tractability threshold sharp. [Filakovský–Franek–Wagner–Zhechev](https://doi.org/10.1007/s41468-018-0021-5)

These are written proofs without Lean kernel verification.
