# Undecidable boundary extension for a fixed hyperbolic three-manifold

**Theorem 1.** For every fixed closed three-manifold \(Y\) with Nil geometry there exist a closed orientable hyperbolic three-manifold \(M\), an embedded handlebody \(H\subset M\), and a fixed annulus in \(\partial H\), with the following properties.

1. The exterior \(C=M\setminus\operatorname{int}(H)\) is compact hyperbolic with connected totally geodesic boundary.
2. There is a computable sequence \(g_t\colon\partial C\to Y\), \(t\in\mathbb N\), of based maps which agree off the fixed annulus. The set of \(t\) for which \(g_t\) extends to \(C\) is \(\Sigma^0_1\)-complete.
3. Each \(g_t\) comes from a specified map \(h_t:H\to Y\). Every extension to \(C\), glued to \(h_t\), has degree \(+1\) as a map \(M\to Y\).

The only varying datum is the winding number on a single target circle. The target is aspherical. Theorem 2 below gives an example with totally geodesic boundary of genus two.

## 1. Fixed group words for integer arithmetic

Write \(G=\pi_1(Y)\). The action on the Euclidean base of the Nil fibration gives an exact sequence from the infinite cyclic fiber translations to \(G\) and a plane crystallographic group. The preimage \(L\) of the plane translation lattice is the subgroup acting by Nil translations. It has finite index in \(G\) and is a central extension of \(\mathbb Z^2\) by \(\mathbb Z\). Choose an ordered translation basis and lifts \(p,q\in L\), and let \(z\) generate the fiber translations. Then every element of \(L\) has a unique expression \(p^a q^b z^c\), and \([p,q]=z^e\) for \(e\ne0\). The commutator is nontrivial because \(p\) and \(q\) project to independent horizontal translations in the real Heisenberg group. The convention is \([u,v]=uvu^{-1}v^{-1}\). All Nil isometries preserve the orientation of the total space. Their conjugation action on real fiber translations has sign equal to the determinant of the action on the horizontal plane. In particular \(G\) is solvable, since it is an extension of \(L\) by a finite subgroup of \(O(2)\). [Peter Scott, *The geometries of 3-manifolds*, Nil discussion and Theorem 4.16](https://www.maths.gla.ac.uk/~mpowell/Scott%20-%20Geometries_of_three-manifolds.pdf)

An element of \(G\) commuting with both \(p,z\) projects to a plane isometry whose linear part has determinant \(+1\) and fixes the nonzero translation vector of \(p\). Its linear part is therefore the identity and the element lies in \(L\). Commuting with \(p\) in \(L\) cuts out \(\langle p,z\rangle\), since the commutator with \(p\) of \(p^a q^b z^c\) is \(z^{-eb}\). Thus
\[
C_G(p)\cap C_G(z)=\langle p,z\rangle,\qquad
C_G(q)\cap C_G(z)=\langle q,z\rangle.
\]

By the Davis–Putnam–Robinson–Matiyasevich theorem and the four-square theorem, fix \(P\in\mathbb Z[T,U_1,\ldots,U_m]\) such that solvability of \(P(t,u)=0\) in integer \(u\) is \(\Sigma^0_1\)-complete as \(t\) varies in \(\mathbb N\). Fix an arithmetic circuit for \(P\), with gates for addition, multiplication and fixed integer constants, input wires \(T,U_1,\ldots,U_m\), and output wire \(O\).

Use unknowns \(X_i,Y_i\in G\) for every wire. Require \(X_i\) to commute with \(p,z\) and \(Y_i\) with \(q,z\), and impose \([X_i,q]=[p,Y_i]\). Then \(X_i=p^{a_i}z^{c_i}\) and \(Y_i=q^{a_i}z^{d_i}\) for a common integer \(a_i\). Conversely any \(a_i\) is represented by taking \(c_i=d_i=0\). The other word constraints are as follows.

| Circuit constraint | Group constraint |
| --- | --- |
| \(a_k=a_i+a_j\) | \([X_iX_jX_k^{-1},q]=1\) |
| \(a_k=a_i a_j\) | \([X_i,Y_j][X_k,q]^{-1}=1\) |
| \(a_k=b\) for a fixed integer \(b\) | \([X_k,q]=z^{eb}\) |
| \(a_O=0\) | \([X_O,q]=1\) |
| \(a_T=t\) | \([X_T,q]=z^{et}\) |

The commutator of \(X_i,Y_j\) is \(z^{ea_ia_j}\), so these equalities are precisely the circuit constraints. All the left-hand words are fixed. All right sides are fixed except the last.

## 2. Closed hyperbolic source and degree

Let \(\ell\) be the number of group unknowns and set \(P_0=Y\#(\#^\ell(S^1\times S^2))\). Its fundamental group is \(G*F_\ell\), with the free generators labeled by those unknowns. The hyperbolic perfect-kernel replacement gives a closed orientable hyperbolic \(M\) and a degree-\(+1\) map \(f\colon M\to P_0\) inducing an epimorphism with perfect kernel. Every homomorphism \(\pi_1(M)\to G\) factors uniquely through \(f_*\), since the image of a perfect group in a solvable group is trivial. [Derived hyperbolic transfer, Theorem 1](DerivedHyperbolicTransfer.md)

Choose a lift in \(\pi_1(M)\) of each left-hand word of §1 and of each member of a fixed finite generating set of its \(G\) factor. Here equality conditions such as \([X_i,q]=[p,Y_i]\) are put in the form \([X_i,q][p,Y_i]^{-1}=1\). There are finitely many lifts, independent of \(t\). Realize them as based loops meeting only at their common basepoint by PL general position for a finite graph in dimension three. Their union is a bouquet \(A\). Prescribe a map on \(A\) by realizing every required right side as a based loop and pinning the generators of the factor \(G\) to their namesakes in the target. Use the \(et\)-fold fiber loop for the single variable right side.

Suppose the prescribed map extends to \(M\). Its homomorphism factors through \(G*F_\ell\), and the pinning forces its restriction to \(G\) to be the identity. The free-letter images then satisfy exactly the word system of §1. Conversely, a solution gives a homomorphism \(G*F_\ell\to G\) by taking the identity on \(G\) and the prescribed free-letter images. The target is a \(K(G,1)\). Precomposing this homomorphism by \(f_*\) gives a based map \(M\to Y\) whose restriction to \(A\) is based homotopic to the prescribed map. The graph inclusion is a cofibration, so homotopy extension gives a map restricting exactly to the prescribed map.

The degree of every such extension is \(+1\). Model its factored homomorphism \(G*F_\ell\to G\) by pinching \(P_0\) to a wedge, using the identity on \(Y\), and sending the \(S^1\times S^2\) summands through their \(S^1\) factors with the required free-letter values. The fundamental class maps under the pinch to the sum of the classes of the summands. The \(S^1\)-factoring summands contribute zero, so the map \(P_0\to Y\) has degree \(+1\). Its composite with \(f\) is homotopic to the given extension by asphericity of \(Y\), and has degree \(+1\).

## 3. Entire totally geodesic boundary

We use the following construction for any of the marked bouquets in this note. Represent the probes first by disjoint arcs in \(M\setminus\operatorname{int}(B)\) for a small basepoint ball \(B\), giving each loop two distinct endpoints on \(\partial B\). Inside \(B\) join those endpoints to its center by radial edges disjoint except at the center. The union of the exterior arcs can be homotoped relative to the endpoints to have excellent exterior by Myers's theorem, since the sphere boundary of \(M\setminus\operatorname{int}(B)\) meets the arcs in at least two points. Joining back to the center preserves the based words. A regular neighborhood \(H\) of the resulting bouquet is \(B\) with one \(1\)-handle for each arc, and its exterior \(C\) is the excellent arc exterior up to collars and rounding corners. With at least two probes, \(C\) has connected boundary of genus at least two. It has no torus boundary. Hyperbolization for compact excellent orientable three-manifolds supplies its metric with totally geodesic boundary. [Myers, Theorem 1.1](https://doi.org/10.1016/0166-8641(93)90038-F) · [Kent and Souto, §1](https://people.math.wisc.edu/~aekent2/Excellent%20Graphs.pdf)

Define \(h_t\colon H\to Y\) by sending the \(0\)-handle constantly to the basepoint and sending each \(1\)-handle \(D^2\times[0,1]\) through its prescribed path in \(Y\), independently of the \(D^2\) coordinate. Its graph restriction equals the prescribed graph map, using the interval coordinate on the handle and constant paths on the radial arcs. Because only one prescribed graph path varies, the restriction \(g_t=h_t|_{\partial C}\) varies only on the annulus \(S^1\times[0,1]\) of that handle. Every extension on \(C\) glues to a map on \(M\) extending the graph data, since its values equal \(h_t\) pointwise on the common boundary. Conversely, a map on \(M\) extending the graph data restricts to a map on \(H\) homotopic to \(h_t\) relative to the graph, by deformation retraction onto the graph. The inclusion \(H\subset M\) is a cofibration, so homotopy extension changes the map on \(M\) to one with restriction exactly \(h_t\). It then restricts to an extension of \(g_t\) on \(C\).

Every boundary probe can be read on a path traversing its annular handle in the interval direction and returning along the punctured sphere bounding the \(0\)-handle. The return path maps constantly. This realizes the prescribed loop with its full winding number. The meridian circles map constantly. The full boundary itself carries every probe, including the normalization commutator in Theorem 2.

The maps on the handles can be made piecewise linear on finite subdivisions by using fixed piecewise-linear paths in a target triangulation and factoring each handle map through its interval coordinate. The variable path is computed by concatenating a fixed fiber loop or its reverse. One can subdivide the resulting piecewise-linear maps to obtain simplicial input, allowing subdivisions of the fixed underlying spaces. The proof in §1 identifies the extension parameter set with the fixed complete Diophantine set. The degree condition follows from §2. This proves Theorem 1.

## 4. Genus two suffices

**Theorem 2.** Fix a closed principal circle bundle \(Y\) over \(T^2\) with nonzero Euler number. There is a fixed compact hyperbolic three-manifold \(C\) with connected totally geodesic boundary of genus two and a fixed annulus in that boundary such that extension of a given map \(\partial C\to Y\) is \(\Sigma^0_1\)-complete in a computable family varying only on this annulus. In the associated closed orientable hyperbolic manifold, the two fixed bouquet words are both commutators.

**Proof.** Write \(G_e=\pi_1(Y)\) using normal coordinates \((u,v,w)\in\mathbb Z^3\) with multiplication
\[
(u,v,w)(u',v',w')=(u+u',v+v',w+w'+euv'),
\qquad e\ne0.
\]
A character pair \(u,v\) of a group \(\Gamma\) lifts to \(G_e\) exactly when \(e\,u\smile v=0\) in \(H^2(\Gamma;\mathbb Z)\). This follows from the multiplication law, whose extension cocycle is \(e\,u(g)v(h)\).

Use the fixed polynomial circuit of §1. Let \(W\) be the free abelian group whose coordinates are \(a,b,P_i,Q_i\), with \(P_i,Q_i\) two labels for each wire. For two vectors \(u,v\in W\), write \(D_{rs}(u,v)=u_rv_s-u_sv_r\) for the alternating form on coordinate labels \(r,s\). Include the following tests in a fixed list \(\beta_1,\ldots,\beta_m\) of alternating forms:
\[
D_{a P_i},\qquad D_{Q_i b},\qquad D_{P_i b}-D_{a Q_i}
\]
for every wire. For an addition gate \(k=i+j\), add \(D_{P_i b}+D_{P_j b}-D_{P_k b}\); for a multiplication gate \(k=ij\), add \(D_{P_i Q_j}-D_{P_k b}\). A constant gate with value \(c\) adds \(D_{P_k b}-cD_{ab}\), and the output test is \(D_{P_O b}\). When the two columns at \(a,b\) are \((1,0)\), \((0,1)\), the first three tests force the columns at \(P_i,Q_i\) to be \((w_i,0),(0,w_i)\). The remaining tests then give exactly the circuit relations, omitting the parameter equation \(w_T=t\).

Put \(V=W\oplus\bigoplus_{j=1}^m\mathbb Z r_j\) and \(\mu=\sum_j\beta_j\wedge r_j^*\). Sullivan's realization theorem gives a closed oriented \(P_0\) with torsion-free integral first homology, \(H^1(P_0;\mathbb Z)=V\), and triple cup form \(\mu\). Apply the degree-one hyperbolic replacement, which preserves integral homology. Naturality of cup evaluation gives the identical form on \(H^1(M;\mathbb Z)\) for the resulting closed orientable hyperbolic \(M\). For every coordinate label choose a based loop \(g_r\) dual to that coordinate. Mark only the two based words \([g_a,g_b]\) and \([g_{P_T},g_b]\); prescribe right sides \(z^e\) and \(z^{et}\), respectively, where \(z=(0,0,1)\) in \(G_e\). General position and §3 give the excellent genus-two bouquet exterior with exactly these markings. [Sullivan, *On the intersection ring of compact three manifolds*](https://www.math.stonybrook.edu/~dennis/publications/PDF/DS-pub-0019.pdf)

Let \(u,v\) be the two horizontal projections of a representation. The first prescribed commutator value gives \(D_{ab}=1\). Applying the integral inverse of its column matrix to all columns gives normalized characters and preserves every \(D_{rs}\), including the second marked value. Since \(\mu\) is alternating, this operation also preserves \(\mu(u,v,-)\). By Poincaré duality and torsion-free first homology, \(H^2(M;\mathbb Z)\) is free and \(u\smile v=0\) exactly when \(\mu(u,v,-)=0\). The central extension obstruction implies this vanishing. Its evaluations on the \(r_j\) give all \(\beta_j(u,v)=0\), regardless of the \(r_j\) coordinates of \(u,v\). The second prescribed commutator then gives \(w_T=t\).

Conversely, from a solution of \(P(t,w)=0\) take the normalized columns on \(W\) using its circuit values and set all \(r_j\) coordinates of \(u,v\) to zero. All the tests vanish. For \(u,v\in W\), the function \(\mu(u,v,-)\) is zero on \(W\), and its evaluations on \(r_j\) are precisely the vanishing tests. Thus \(u\smile v=0\) on \(M\). As \(M\) is hyperbolic it is a \(K(\pi_1(M),1)\), so the group cup class is zero as well. The extension cocycle criterion produces a representation. In any such lift, commutator values are \(z^{eD_{rs}}\) and are independent of the three-coordinate lift choices. This gives exactly the two prescribed words. Use asphericity of \(Y\) and the cofibration arguments of §§2–3 to obtain a map extending the whole boundary. As before, the parameter changes the path on one handle and hence on one annulus. The equivalence with the fixed complete Diophantine set proves the asserted complexity. \(\square\)

## 5. Comparison with Euclidean targets

**Theorem 3.** If \(Y\) is a fixed closed Euclidean three-manifold, extending a prescribed simplicial map from a connected subcomplex of a finite connected simplicial complex to \(Y\) is decidable. For a fixed source pair the decision is polynomial time in the total length of the prescribed generator words.

The target is aspherical, so the same based-homomorphism criterion applies. By Bieberbach's theorem its group is an extension of a free abelian lattice of rank three by a finite group \(D\). A section gives forms \((v,\delta)\) with multiplication
\[
(v,\delta)(w,\varepsilon)
=\bigl(v+A_\delta w+c_{\delta,\varepsilon},\,\delta\varepsilon\bigr)
\]
for fixed integral matrices \(A_\delta\) and vectors \(c_{\delta,\varepsilon}\). Take a finite presentation of the source group and generator words of the subcomplex. Enumerate assignments of elements of \(D\) to the source generators, discarding failures of quotient relators or prescribed values. With those coordinates fixed, word multiplication and inversion express every translation coordinate by an integral affine linear formula in the unknown generator translations. The relators and prescribed images give a finite linear system over \(\mathbb Z\), decidable by Smith normal form. For a fixed source pair the number of quotient assignments and the sizes of the fixed source words are constant, so the computation is polynomial in the lengths of the prescribed words.

Theorems 1 and 3 give a Euclidean/Nil dichotomy for the boundary-extension problem on compact hyperbolic three-manifolds with connected totally geodesic boundary. There is also a one-probe decision result in the free-quotient version of the construction. Let \(M'\) be a hyperbolic perfect-kernel replacement of \(\#^\ell(S^1\times S^2)\), and let the marked subspace be one embedded based circle. For a fixed Nil target the image of this circle under \(\pi_1(M')\to F_\ell\) gives a single group equation with the prescribed image as its right side. It is decidable by Levine's theorem because the target group is virtually class \(2\) nilpotent with virtually cyclic derived subgroup. This one-probe statement concerns the indicated free-quotient sources. [Levine, *Equations in virtually class 2 nilpotent groups*](https://arxiv.org/abs/2009.10651)

## 6. Exact geometric transfer of integral Manin systems

**Theorem 4.** For every nonzero bilinear map \(B:U_0\times V_0\to W\) between finite-rank free abelian groups, there is a fixed compact two-step nilmanifold \(Y_B\) and an effective reduction of the Manin bilinear equation problem for \(B\) to extending graph maps in closed orientable hyperbolic three-manifolds. There is also an effective reduction to extending from the whole connected totally geodesic boundary of a compact hyperbolic three-manifold to \(Y_B\). Both preserve existence and all integral values of the quotient variables below.

The radicals of \(B\) are saturated, as kernels of linear maps to free abelian groups. Form the free quotient lattices \(U,V\) and write \(\beta:U\times V\to W\) for the induced pairing. Projection takes solutions to solutions and every projected solution lifts. Define
\[
G_B=U\times V\times W,\qquad
(u,v,w)(u',v',w')=(u+u',v+v',w+w'+\beta(u,v')).
\]
The same formula over \(\mathbb R\) defines a simply connected two-step nilpotent Lie group. Its discrete subgroup \(G_B\) is cocompact because one can translate the first and second coordinates into fixed unit boxes, then translate the central coordinate into a unit box. The quotient \(Y_B\) is compact and aspherical. Direct multiplication gives
\[
[(u,v,w),(u',v',w')]=(0,0,\beta(u,v')-\beta(u',v)).
\]
Fix basis elements \(p_i=(e_i,0,0),q_j=(0,f_j,0)\). Commuting with every \(p_i\) forces a left unknown \(X_a\) to have zero \(V\)-coordinate, by zero right radical. Commuting with every \(q_j\) forces a right unknown \(Y_b\) to have zero \(U\)-coordinate. The Manin equation
\[
\sum_{a,b}c_{ab}^{(r)}\beta(u_a,v_b)=w_r
\]
is precisely the single probe
\[
\prod_{a,b}[X_a,Y_b]^{\,c_{ab}^{(r)}}=(0,0,w_r).
\]
All factors are central. Every solution of the projected equation system gives matrices \((u_a,0,0)\), \((0,v_b,0)\) meeting the probes. Conversely, read the \(U\)- and \(V\)-coordinates of any assignment meeting the probes.

Use separate free letters for the elements \(p_i,q_j\) and pin them by additional probes. Let \(\ell\) be the total number of variables and pinned letters, and consider a hyperbolic perfect-kernel replacement \(M_\ell\) of \(\#^\ell(S^1\times S^2)\). Every homomorphism to \(G_B\) factors through its quotient \(F_\ell\), since \(G_B\) is solvable. Represent the probes in an embedded bouquet as in §2, applying §3 for the full-boundary variant. The aspherical-target criterion and the cofibration arguments prove preservation of solutions in both directions.

Here the source varies with the instance, so effectivity takes a separate argument. For each \(\ell\), enumerate finite triangulations of closed orientable hyperbolic three-manifolds and homomorphisms of their fundamental groups to \(F_\ell\) carrying \(\ell\) specified words to its basis. Closed hyperbolicity is decidable by three-manifold recognition algorithms and the assigned word images can be checked in the free group. The search halts by the replacement theorem. The displayed basis lifts give a section \(F_\ell\to\pi_1(M_\ell)\). A verified free retraction suffices here, even when the enumerated map has a different kernel. Every homomorphism to \(G_B\) restricts to a probe assignment on the chosen section, and every assignment on \(F_\ell\) gives a homomorphism by composition with the retraction. In this implementation write all probe words in the section. Enumerate disjoint PL arcs in the punctured triangulated manifold, with fixed endpoints and based closures homotopic to the probes. The required homotopies can be recognized by enumeration of van Kampen proofs. For the boundary version, require that the double of the arc exterior be closed hyperbolic. This test halts successfully by Myers and hyperbolization, and success gives the required hyperbolic metric on the exterior by equivariant geometrization of the doubling reflection. This provides effective constructions, including triangulated markings. [Aschenbrenner, Friedl and Wilton, *Decision problems for 3-manifolds and their fundamental groups*](https://arxiv.org/abs/1405.6274) · [Dinkelbach and Leeb, equivariant geometrization](https://msp.org/gt/2009/13-2/gt-v13-n2-p15-p.pdf)

By the integral Manin bilinear theorem, the fixed-target problems produced by this theorem are \(\Sigma^0_1\)-complete for every nonzero \(B\). Membership follows by enumerating tuples of images of source generators in \(G_B\), and checking the source relators and the prescribed restrictions using its coordinate word problem. [Manin, Conjecture 7.2 and Theorem 8.1](https://arxiv.org/abs/2007.10632) · [Koymans and Pagano, arithmetic input to the integral bilinear theorem](https://arxiv.org/abs/2412.01768)

## Prior work and proof status

Theorem 1 uses classical integer Diophantine representation. Undecidability for systems of equations over Heisenberg and other Nil groups is already established. The genus-two proof uses the two-commutator reduction from the earlier affine-universality construction. The fixed marked-graph version follows from that construction by fixing the circuit of a universal polynomial. Here the excellent-exterior construction makes the prescribed subspace the entire connected totally geodesic boundary, with variation on one annulus. Theorem 1 extends this conclusion to every closed Nil target and fixes the degree of the glued map. These are informal proofs. A targeted search found the group-equation precedents. Publication priority for the geometric conclusions remains unverified. [Duchin, Liang and Shapiro](https://arxiv.org/abs/1401.2471) · [Gray and Levine](https://arxiv.org/abs/2512.07690)
