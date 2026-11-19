# The five- and six-point bounds for even isomorphism of systems of partial bijections

**Status.** Informal proof. The theorem concerns explicit finite sets and explicit maps. It does not establish a strict separation between deterministic logspace and parity logspace.

## Theorem

The input gives a common signature of named sorts and named arrows with specified source and target sorts. An object assigns an ordered finite set to each sort and a partial injection to each arrow. Isomorphisms are families of bijections intertwining the arrows, including their domains. Orders serve only to define the sign of each bijection and to encode the input. Given two objects and prescribed signs on any subset of sorts, decide whether an isomorphism has exactly those signs.

1. The decision problem is logspace many-one equivalent to feasibility of binary linear equations, hence complete for parity logspace (⊕L).
2. If each constrained sort has at most five elements, decision is in deterministic logspace. Unconstrained sorts may be arbitrarily large.
3. Hardness already holds with an evenness requirement at every sort, at most six elements per sort, at most two domain points per map, and at most three elements per connected component of the underlying undirected graph. The two input objects in the reduction are always ordinarily isomorphic.
4. If every arrow is a total bijection, deterministic logspace suffices for arbitrarily large sorts and any number of sign requirements.

## An ordinary transporter in deterministic logspace

Make the graph of individual elements using the named maps in both directions. From an element, any specified arrow name and direction has at most one successor. For elements $u,v$ in two objects, build the implicit undirected graph of pairs of same-sort elements. Two pairs are adjacent if a common arrow, traversed in the same direction on both sides, takes one pair to the other. The undirected component of $(u,v)$ consists precisely of the pairs obtained by common words in arrows and partial inverses.

To test whether an isomorphism of pointed components sends $u$ to $v$, check whether this relation induces a total bijection of the two underlying components. For every paired point also check equality of outgoing and incoming domains for every name. These checks suffice since the relation is closed under simultaneous transitions. They are necessary since every point is reached from its root by a word and words have unique values. When the test succeeds the pointed isomorphism is unique and each value is obtained by scanning potential targets. Each test uses counters and Reingold's undirected reachability algorithm on polynomial-size graphs with logspace adjacency. [Reingold, Undirected connectivity in log-space](https://doi.org/10.1145/1391289.1391291)

Represent each component by its least encoded point. Component types are comparable for equality by trying all target roots. Match the components of each source type to the isomorphic target components in order of their representatives, after checking their multiplicities. For each paired component, choose the least admissible target root. This gives a particular ordinary transporter $g$ whose values can be emitted or recomputed in deterministic logspace. The sign of its restriction to a sort is obtained by counting inversions modulo two.

## One possible sign column per component type

Consider an isomorphism type with representative connected component $U$, multiplicity $m$, and automorphism group $H$ of order $h$. Write $r_i$ for the number of elements in sort $i$ of $U$. An automorphism fixing one element fixes all words from it, so $H$ acts freely and $h$ divides each $r_i$. Let $\chi:H\to\mathbf F_2$ be the parity character of the regular permutation action of $H$. Any $a\in H$ acts on sort $i$ with parity $(r_i/h)\chi(a)$, because that sort is a union of regular orbits.

Choose fixed identifications between the $m$ copies. Automorphisms act by independent internal automorphisms and permutations of the copies. Transposing two copies has sign bit $r_i\bmod 2$ at sort $i$. The full image of this type under all sort signs therefore has the following description.

- If $h$ is even, every $r_i$ is even. Copy permutations contribute zero. If $\chi$ is nonzero, the type contributes the one binary column $(r_i/h\bmod 2)_i$, realizable by acting in a single copy.
- If $h$ is odd, $\chi$ is zero. For $m\ge 2$, the type contributes the column $(r_i\bmod 2)_i$, realizable by transposing two copies.
- In the other cases the type contributes zero. A column may also vanish after restriction to the prescribed sorts.

These computations use logarithmic space. In particular $h$ is the number of admissible images of one root. To decide whether $\chi$ is nonzero, enumerate the corresponding pointed automorphisms and compute their sign on the root's $H$-orbit. That orbit is the set of admissible root images and carries a regular action. Membership and inversion parity follow by repeated scans. All calls have bounded nesting depth.

Different component types can be acted on independently. With their columns in $A$, requested sign vector $p$, and baseline transporter $g$, the answer is yes exactly when $Ax=p+\mathrm{sign}(g)$ is feasible over $\mathbf F_2$ on the specified rows. This is a deterministic logspace many-one reduction. For nonisomorphic ordinary inputs emit a fixed inconsistent equation. Binary feasibility is ⊕L-complete. [de Beaudrap, On the complexity of solving linear congruences](https://arxiv.org/abs/1202.3949)

Every type contributing a nonzero entry in row $i$ occupies at least two points of that sort across its copies. In the even-order case $r_i\ge h\ge 2$. In the odd-order case $m\ge 2$ and $r_i\ge 1$. Distinct types use disjoint points. A constrained sort of size at most five therefore yields an equation with at most two variables. Add a symbol for zero and express each such equation as a parity-labeled edge, handling constant equations directly. In the graph on two bit-labeled copies of each variable, an edge of label $b$ connects $(x,e)$ to $(y,e+b)$. The system is consistent exactly when no variable is connected to its opposite copy. Reingold gives the five-point bound.

## Six points realize arbitrary binary linear systems

In logspace replace long binary equations by width-at-most-three equations by introducing running XORs. Give every occurrence of each new or old variable its own copy, then force the copies for that variable equal along a chain of binary equations. Now every equation has at most three distinct variables and each variable occurs in at most three equations. Handle constant equations immediately. All output identifiers can be generated by rescanning the input and counting occurrences.

For each row form one sort. For each variable occurrence in that row put a pair of points there, provisionally labeled $0,1$. A private named partial identity on the pair distinguishes it as a set. For each variable, link its occurrence pairs in a path using a fresh named partial injection at each link, matching the two points by their provisional bit. Every automorphism fixes each pair as a set. The links force its swap bits at all occurrences of one variable to agree, and each variable can be swapped independently. Consequently the sign vector of its automorphisms is exactly the column span of the incidence matrix. Row sorts have at most six points, each partial map has rank two, and after the identity loops are ignored every connected component is a path on at most three points.

Given right-hand side $b$, choose a permutation $q$ of the underlying ordered sorts that transposes two positions in each nonempty row for which $b_i=1$, and fixes all other positions. Present the first object $X$ together with its relabeling $qX$. Every transporter is $qa$ for $a\in\mathrm{Aut}(X)$, so an all-even transporter exists precisely when $Ax=b$. Both objects have the stated restrictions. Exceptional constant instances can be represented on a two-point sort using separate private singleton loops and, for the no case, exchanging those two points in the second object.

## Total bijections

For an automorphism, the permutations on sorts joined by a total bijection are conjugate, so their signs are equal. On each connected component of the graph of sorts, all attainable sign corrections are thus constant. Use the transporter above to compute the requested correction on each specified sort, check it is constant on each base component, and enumerate the component-type columns to test if a one-bit correction on that base component occurs. A type is contained in one base component, so possible corrections on distinct base components can be chosen independently. This proves the unrestricted-size total-bijection claim.

## Relation to earlier work

Simultaneous conjugacy of a tuple of permutations is the one-sort, total-bijection case of ordinary isomorphism. Earlier algorithms use colored permutation digraphs. The graph-isomorphism literature also has class-size-sensitive logspace and modular hardness results for arbitrary relations. Here the arrows are named partial matchings and the parity is prescribed separately on each entire sort. The specific contribution is the one-column formula and its five/six threshold in this model. This argument does not determine the first publication of that threshold. [Brodnik, Malnič and Požar](https://arxiv.org/abs/2007.05870) · [Bounded color multiplicity graph isomorphism](https://eccc.weizmann.ac.il/eccc-reports/2004/TR04-121/index.html)
