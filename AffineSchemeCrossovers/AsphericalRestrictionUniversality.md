# Analytic-complete restriction into one closed aspherical four-manifold

There is one closed orientable smooth aspherical four-manifold \(M\) with virtually nilpotent fundamental group with the following properties.

1. One fixed locally finite two-dimensional simplicial pair \((K,A)\) of uniformly bounded vertex degree, with fixed \(M\), realizes every closed subspace of Baire space as its quotient space of relative homotopy classes, by varying only binary boundary values on a prescribed family of loops.
2. The same target realizes every closed finite-ary relation on closed subspaces of Baire space by literal inclusions and restriction maps of two-dimensional locally finite simplicial pairs. In particular it realizes graphs of continuous maps and finite limits of diagrams of these maps.
3. For one fixed computable inclusion of two such pairs with a common fixed boundary map, the image of restriction is analytic-complete under continuous reductions. Every analytic subset of Baire space is a section of this image. Both the domain and codomain of restriction are Polish spaces in their quotient topologies.

Each class in these constructions is represented by a weakly contractible component of the relative mapping space. The degree-coordinate maps to the indicated solution spaces are continuous weak equivalences with continuous sections.

## Fixed compact target and the integer gates

Use the integral Heisenberg group on triples with law

\[
(x,y,z)(x',y',z')=(x+x',y+y',z+z'+xy').
\]

Take the semidirect product \(G\) with one infinite cyclic generator \(s\) acting by \(\alpha(x,y,z)=(-y,x,z-xy)\). The multiplication law verifies that \(\alpha\) is an automorphism, and \(\alpha^2(x,y,z)=(-x,-y,z)\). The quotient of the real Heisenberg group by left integer translations is a compact smooth nilmanifold \(F\) with universal cover \(\mathbb R^3\). The automorphism \(\alpha\) descends to an orientation-preserving diffeomorphism of \(F\) of order four, since its derivative has determinant one. Its mapping torus is the required closed orientable manifold \(M\). Its universal cover is the real Heisenberg group times \(\mathbb R\), the action lifts with fundamental group \(G\) and \(G\) has the nilpotent subgroup \(H(\mathbb Z)\times4\mathbb Z\) of index four.

Use \([g,h]=ghg^{-1}h^{-1}\) and mark three based loops with prescribed elements \(s,e=(1,0,0),f=(0,1,0)\). The equations \([e,u]=1\) and \(s^2us^{-2}=u^{-1}\) select exactly \(P=\{(x,0,0):x\in\mathbb Z\}\). The latter equation forces the image of \(u\) in the torsion-free quotient \(\mathbb Z\) to vanish. The former then requires \(y=0\), and comparing central coordinates of \(\alpha^2(u)\) and \(u^{-1}\) requires \(z=-z\). Each element of \(P\) satisfies both equations. Use \([f,u]=1\) and the same inversion condition to select \(Q=\{(0,y,0):y\in\mathbb Z\}\). Represent a scalar \(a\) by two group variables \(p_a\in P\) and \(q_a\in Q\), equated by \([p_a,f]=[e,q_a]\). In these coordinates,

\[
[p_a,q_b]=(0,0,ab),\qquad p_ap_b=p_{a+b}.
\]

Thus \([p_a,q_b]=[p_c,f]\) and \(p_ap_b=p_c\) implement unique multiplication and addition gates. Use inverses or a marked zero loop for signed constants and zero, and mark \(p_a\) by a fixed based loop representing \(1_G\) or \(e\) to prescribe a binary scalar. All relator templates have bounded size, including the scalar membership equations. Large constants are built from these gates by doubling and addition.

## Countable, bounded geometry, and the topology of restrictions

Apply the countable circuit construction in [Closed path spaces and analytic sets as relative homotopy problems](CountableMappingUniversality.md), replacing each scalar sphere pair by the two loop variables above and each four-cell constraint by the required group relator two-cells. Every scaffold vertex is marked and the map on the scaffold is constant. For bounded vertex degree use the two-skeleton of the triangulated cubical scaffold, which contains every routing edge. Local anchors are marked loops at the same sites as before. Equality is checked across one marked edge as necessary, using the edge to transport each based loop to the constraint site. All attaching maps therefore have fixed-length templates or traverse a bounded number of edges. Replace attachments by simplicial mapping cylinders and cones of the fixed relator circle maps. This retains dimension two and preserves local finiteness and the uniform vertex degree whenever the underlying routing does. A common marked ray suffices in the constructions using literal coordinate subcomplexes. All those inclusions and their shared marked subcomplex survive the simplicial replacement.

On the cellular model, a map is specified on the one-skeleton by based loops once the marking is fixed. Their elements in \(G\) are precisely the variables. Such a map extends exactly when each relator is trivial in \(G\). In that case choose a filling disc for each attached two-cell. Two maps with the same variables are homotopic relative to \(A\): first choose based homotopies on all unmarked loops, then extend over the two-cells times the homotopy interval using \(\pi_2(M)=0\). These constructions work for all countable locally finite models by the CW gluing property. The simplicial replacement is homotopy equivalent over the marking by collapsing mapping cylinders. For all inclusions used here, the collapses commute with restriction.

Taking the homotopy class of a based loop in \(M\) is continuous into discrete \(G\), by compactness of the circle and the local contractibility of the smooth target. Conversely choose a based loop for each group element, respecting the given marking, and choose a filling disc for each allowed finite tuple for each relator template. This forms a continuous section of the coordinates for the compact-open topology, since every compact subset of the locally finite source meets only finitely many cells. In the simplicial model use the same section precomposed with the collapse. These coordinate maps identify the quotient topologies with the product topologies on the integer solutions. Gate witnesses and transported copies are uniquely determined. The path equations and forbidden-cylinder tests in the companion proof now give statements 1 and 2, and the same fixed second-path circuit gives statement 3. Its domain is the closed set of triples \((c,x,y)\) satisfying the prefix tests in \(2^{\mathbb N}\times(\mathbb N^{\mathbb N})^2\). Its codomain is the full parameter product \(2^{\mathbb N}\times\mathbb N^{\mathbb N}\). Both are Polish.

Finally, on the cellular model a spherical family of extensions with parameter \(S^i\), \(i\ge 1\), corresponds to a map on \(K\times S^i\) fixed on \(A\times S^i\). To fill it, prescribe the fixed boundary map on \(A\times D^{i+1}\). Every vertex of this cellular model is in \(A\), so the new relative cells for the product pair have dimension at least \(1+(i+1)\ge3\). Every obstruction to filling them vanishes by asphericity. The extended family proves that all positive homotopy groups of each component vanish. The exponential-law adjunction holds for the locally compact source. The homotopy equivalence over \(A\) induces a homotopy equivalence of relative mapping spaces for the simplicial replacement. Together with the bijection on components this proves the weak equivalence assertion.

## Relation to previous results

Systems of group equations can already interpret integer arithmetic in Heisenberg and more general nilpotent groups. Here the integer gates have unique wire values and are implemented inside a fixed closed orientable manifold, with bounded-geometry countable sources and continuous choices of topological representatives. In particular the restriction image consists of the actual admitting components with their quotient topologies. [Garreta, Miasnikov, and Ovchinnikov, Diophantine problems in solvable groups](https://arxiv.org/abs/1805.04085).
