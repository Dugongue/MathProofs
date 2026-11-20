# A matching-number criterion for parameterized subgraph polynomials

**Status.** Informal proof over any field of characteristic zero. The previous MathProofs result gave an equivalence with VFPT = VW[1] for the path family and for the unrestricted ordinary-circuit side of Grochow–Urisman Question 1.11. The theorem below refines it to every computably enumerable class of simple pattern graphs. The existence of small circuits in the unbounded case is equivalent to VFPT = VW[1]. This does not settle that equality.

## The theorem

For a finite simple graph H without isolated vertices, let

    S_H,n(X) = (1/|Aut H|) sum_{injective f: V(H) -> [n]} product_{uv in E(H)} X[f(u),f(v)],

where X is symmetric and X[a,a] = 0. For a pattern with isolates, delete the isolates, as in the edge-support convention of Grochow–Urisman. Let C be a computably enumerable class and let the parameter be h = |V(H)|. Consider ordinary division-free arithmetic circuits, with field constants allowed and no automorphism requirement.

1. If C has bounded matching number, all its subgraph polynomials have size g(h)n^c for a single constant c.
2. If C has unbounded matching number, size g(h)n^c for all its subgraph polynomials is equivalent to VFPT = VW[1].

This is a statement about circuit size. The reductions construct the oracle circuits in fixed-parameter time, using rational constants of parameter-bounded bit length. The statement does not require a VFPT circuit family to come with a uniform constructor.

## Upper bound from a vertex cover

Choose a maximal matching and put its endpoints in D. This is a vertex cover of size at most twice the matching number. Enumerate the at most n^|D| injective maps on D. For a fixed map, each unassigned pattern vertex is adjacent only to vertices in D. Its assignment to host vertex a therefore has a weight that is just the product of the corresponding edge variables into the fixed image of D.

Process the unused host vertices one by one. Keep a state for each subset of the as-yet-unmapped pattern vertices, representing the assignments that have used exactly that subset. For each host vertex, either skip it or assign it to one unused pattern vertex and multiply by its weight. This gives O(n h 2^h) operations for the extension of the fixed map. Multiply by the weights of edges internal to D, sum over its images, and divide by the fixed integer |Aut H|. The exponent is independent of H when the matching number is bounded.

## A quotient extractor for the hard direction

For a loopless multigraph F, write Hom_F,n(X) for the sum of edge-weight products over all maps to [n], counting parallel edges with their multiplicities. Zero diagonal means a collapsed edge makes the weight zero. Möbius inversion in the partition lattice of V(H) gives

    |Aut H| S_H,n(X) = sum_F c_F Hom_F,n(X).

The terms are obtained by identifying vertices of H, discarding quotients with a loop and grouping isomorphic loopless multigraphs. A partition rho contributes its coefficient

    mu(rho) = (-1)^(h - |rho|) product_{B in rho} (|B|-1)!.

The sign depends only on the vertex count of the quotient. Thus every loopless quotient has nonzero c_F in characteristic zero. Those quotients have no isolated vertices if H has none.

For fixed H, all the Hom_F,h(Y) occurring in the sum are linearly independent polynomials. If a relation existed, choose a graph F with nonzero coefficient of maximal vertex count. The monomial of an injective embedding of F into [h] has exactly |V(F)| vertices in its edge support. Graphs with fewer vertices cannot contribute, and graphs with the same number of vertices can contribute only via injective maps. Hence only F contributes, with multiplicity |Aut F|. This contradicts the relation.

Consequently there are finitely many fixed h-vertex symmetric zero-diagonal matrices B_j with rational entries such that the columns (Hom_F,h(B_j))_j have full rank. One can choose from the grid with entries 0 through |E(H)|, by interpolation coordinate by coordinate. For the weighted graph tensor product, whose entries are (X tensor B_j)[(a,i),(b,l)] = X[a,b] B_j[i,l], the homomorphism sums multiply. Thus queries to S_H,nh(X tensor B_j) give a fixed full-rank linear system for all the Hom_F,n(X). Inverting that system costs only a function of H. The cost of forming the substituted entries is O(h^2 n^2) per query.

## Recovering a clique polynomial from a quotient

Suppose a loopless quotient F has either a clique on t vertices with every edge of multiplicity one, or a K_{t,t} with every edge of multiplicity one. Each selected vertex gets its own copy of the n-vertex host set, and each remaining F vertex gets a singleton. The copies are distinguishable colors indexed by V(F). Use a host of this form, with no loops or edges within a color and no edges between colors whose pair is absent from F.

Assign a variable z_e to each allowed unordered pair of colors e and multiply all host weights of that type by z_e. For an input to Hom_F, inclusion-exclusion over deleting colors forces every color to be used. Since the number of vertices of F equals the number of colors, the color map is now a bijection. Extract the coefficient of the product over e of z_e^{m_F(e)}. An individual term has this exponent vector exactly when the color map is an automorphism of the multigraph F. Use fixed-grid interpolation with degree bound |E(F)| in each marker. The number of calls and all rescaling factors depend on F alone. For each automorphism the surviving weighted sum is the same (relabel the domain by that automorphism). Division by |Aut F| therefore returns the sum for the identity color map. Give every edge type outside the selected clique or biclique weight 1.

In the clique case, place the colors in order 1 through t. On the edge between colors i < j, allow host indices a < b only, and put the factor X[a,b] there. Assign the vertex weight Y_a of each color once, by multiplying it into any one incident edge type at that endpoint. A surviving assignment gives an increasing tuple of t host indices, its edge products, and exactly one copy of each of its vertex weights. This is the parameterized clique polynomial of Bläser and Engels.

For K_{t,t}, order its sides as L_i and R_i for i in [t]. Give edge type L_i R_i weight Y_a when its host indices agree at a, and weight zero otherwise. Edge type L_i R_j for i < j has weight X[a,b] when a < b, and zero otherwise. For i > j give weight 1. The diagonal types make the left and right choices agree, so again the output is the clique polynomial with vertex weights. The blocks and their marker variables have parameter-bounded size apart from the O(tn) host vertices. This gives a fixed-parameter c-reduction in the sense of Bläser and Engels.

## Finding the required quotient

Fix t >= 2 and choose a sufficiently large matching in H. List its edges as ordered endpoint pairs (u_i,v_i). Color an index pair i < j by the four bits of adjacency between u_i,v_i and u_j,v_j. Finite Ramsey theory supplies a homogeneous submatching of size L >= max(2t, binom(t,2)). There are four possibilities.

- If the u-u bit is 1, the selected u vertices contain K_t.
- If the v-v bit is 1, the selected v vertices contain K_t.
- If a cross bit is 1, take the first t matching indices and the last t. The indicated first-side endpoints and last-side endpoints form K_{t,t}.
- If all four bits are 0, the matching is induced. Assign binom(t,2) of its edges bijectively to the edges of K_t and identify their endpoints by clique labels. Keep all other vertices in singleton blocks. The quotient is loopless because there are no cross edges among the selected matching edges. Its selected clique edges have multiplicity one.

The first three choices use H itself as the quotient. Hence an unbounded-matching class supplies a suitable H_t for every t. A fixed-parameter reduction can find H_t by enumerating C until it encounters the required matching, then use the explicit Ramsey search. This work is a function of t alone. The quotient extractor and the colored host construction then turn one parameterized circuit-size bound for C into fixed-parameter-size circuits for the clique polynomial. Clique is VW[1]-complete under fixed-parameter c-reductions, so VFPT = VW[1].

Conversely, the clique polynomial can compute S_H,n by a simple substitution even if the matching number is unbounded. Use |V(H)| colors, with n host copies per color and no edges within any color. Between different colors, prohibit equal host indices. For a color pair that is an edge of H use weight X[a,b]; otherwise use weight 1. Set all clique vertex weights to 1. An h-clique picks exactly one vertex per color and gives each injective assignment once. Divide by |Aut H|. Thus if VFPT = VW[1], a uniform-in-H exponent exists for all S_H,n. The cost of constructing the substitution is O(h^2 n^2).

## Provenance and scope

AgentAlphaXiv's study of matched rule-count controls suggests asking what happens to a measured aggregate when one holds all other coordinates fixed. In the reduction here, small fixed weighted factors make that idea exact: changing only the auxiliary factor scales each quotient coordinate independently, and a full-rank system recovers the coordinates. The mathematical antecedent of this step is the graph motif interpolation of Curticapean, Dell and Marx. The AI study supplies no mathematical premise.

- [AgentAlphaXiv source, pinned manuscript](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a1a7cc-1603-7ea9-91af-5f051775f2f2.pdf)
- [Grochow and Urisman, Question 1.11 and Section 3.3](https://arxiv.org/html/2606.26244v2)
- [Bläser and Engels, Parameterized Valiant's Classes](https://arxiv.org/html/1907.12287)
- [Curticapean, Dell and Marx, Homomorphisms Are a Good Basis for Counting Small Subgraphs](https://arxiv.org/abs/1705.01595)
- [Dawar, Pago and Seppelt, symmetric subgraph circuit criterion](https://arxiv.org/abs/2502.06740)
- [Dwivedi, Pago and Seppelt, ordinary circuit bounds for homomorphism polynomials](https://arxiv.org/abs/2601.09343)
- [Earlier MathProofs path result](https://github.com/Dugongue/MathProofs/blob/main/GrochowQuestionEquivalences/Results.md)