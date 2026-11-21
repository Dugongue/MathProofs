# Symbolic subgraph counting at bounded matching-split number in characteristic two

Let \(H\) have \(h\) vertices and let \(s\) be the minimum number of vertices whose deletion makes its maximum degree at most one. Over every field of characteristic two, its unlabeled weighted subgraph polynomial on \(n\) host vertices has ordinary division-free circuits of size
\[
f(h)n^{3s+O(1)}.
\]
This extends the numeric matching-split method of Curticapean–Dell–Husfeldt to formal edge polynomials. The proof also improves the invariant splitting-set bound used there from \(O(s^2)\) to \(3s\), with equality possible. [Curticapean–Dell–Husfeldt, §4](https://arxiv.org/pdf/2107.00629)

## A small invariant splitting set

Equivalently, an \(s\)-vertex splitting set meets every triple forming a two-edge path, whether or not the endpoints are also adjacent. Average the indicators of a minimum splitting set over the automorphisms of the finite pattern, using rational arithmetic in this combinatorial preprocessing. The resulting weights are constant on automorphism orbits, sum to \(s\), and have total at least one on every such triple. Let \(R\) be the vertices of weight at least \(1/3\). It is invariant, meets every forbidden triple, and has at most \(3s\) vertices. Disjoint triangles achieve the factor 3, since an invariant splitting set must include all the vertices of each triangle. Thus there is an automorphism-invariant choice at a linear cost in the minimum size.

## Removing the automorphism normalization

The action of \(\operatorname{Aut}(H)\) on embeddings preserves the restriction domain \(R\). Enumerate injections from \(R\) into the host, retaining one representative \(\sigma\) per induced automorphism orbit of the injections. Representatives can be selected by comparing the finitely many pattern group translates using the host ordering. For a fixed representative, the only remaining redundancies are from automorphisms fixing each point of \(R\). On \(H-R\) these permute identical components and exchange the two endpoints of an edge if their respective neighborhoods in \(R\) coincide. Indeed every component is a vertex or an edge, and any such component permutation or type-preserving flip extends by identity on \(R\).

Give each singleton component its type \(T\subseteq R\), the set of its neighbors in \(R\). Give an edge component the unordered pair of endpoint types, allowing repetition. For each type record its component demand. For an unused host vertex \(u\) define \(a_T(u)=\prod_{r\in T}x_{\sigma(r),u}\). For a host vertex chosen as a singleton of type \(T\), use weight \(a_T(u)\) and a marker for that type. For a host edge \(uv\) used as an edge component, multiply \(x_{uv}\) by the marker for its unordered type. For distinct endpoint types \(T,T'\) the remaining factor is
\[
a_T(u)a_{T'}(v)+a_{T'}(u)a_T(v).
\]
For coincident types it is the single product \(a_T(u)a_T(v)\). This exactly chooses the endpoint assignments left after quotienting by pointwise stabilizer automorphisms.

## Demands from one Pfaffian

Make an old vertex and its private twin for every unused host vertex. Assign an edge between old vertices the sum of the old-edge weights just described. Assign an old vertex's edge to its own twin weight one plus the sum of all weighted singleton choices at that vertex. Assign weight one to every distinct twin pair. The Hafnian on this augmented graph gives the matching polynomial with demands marked. In fact, after selecting the old-old edges and deciding the singleton choices on the remaining private edges, there is an even number \(2j\) of unmatched twins. Their pairings number \((2j-1)!!\), which is one in characteristic two. This is the same completion identity used for the uncolored matching case. [Uncolored completion](matching-characteristics.md)

In characteristic two the Hafnian equals the Pfaffian of the alternating matrix with these entries. Compute it by any polynomial-size division-free Pfaffian circuit and track the coefficient at the demand vector in the truncated polynomial ring on the markers. Only finitely many marker coefficients are needed as a function of \(h\). The resulting polynomial thus counts all admissible extensions of this representative, with their full edge weights. Multiply by the weights of edges internal to \(R\) and sum over the at most \(n^{|R|}\) representatives. The circuit enumerates actual weighted copies with no division by the automorphism order. It works over every characteristic-two field and handles any pattern under the convention of either keeping its isolated vertices as demanded singleton types or deleting them. [Division-free Pfaffians over arbitrary rings](https://arxiv.org/abs/2302.12081)

For ordered arc variables, apply the same argument to a pattern whose underlying undirected graph has matching-split number \(s\). A singleton type records its incoming and outgoing neighborhoods in \(R\) separately. Edge-component types also record the internal arc pattern up to swapping the two typed endpoints. In the old-edge weight include each placement of the component's typed arc pattern into the two host endpoints once. There is one placement if the swap preserves the entire typed pattern, and two otherwise. The private-twin Pfaffian counts these weighted placements without changing the bound.
