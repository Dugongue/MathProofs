# Every affine scheme of finite presentation is a relative four-dimensional mapping functor

Let \(S\) be an affine scheme of finite presentation over \(\mathbb Z\). There is a finite simply connected simplicial pair \((K_S,A)\), with \(K_S\) of dimension at most four and \(A=S^2\vee S^2\) a single fixed triangulated boundary, having the following properties.

1. The coordinate ring of \(S\) is isomorphic over \(\mathbb Z\) to the ring defined by the degree equations for the pair. The construction uses no localization and preserves nilpotents. The system is obtained in deterministic polynomial time from an arithmetic-circuit presentation with binary integer constants.
2. There is one fixed finite simplicial target \(Y\) and one fixed boundary map \(A\to Y\) such that \(S(\mathbb Z)\) is naturally bijective to relative homotopy classes of maps extending that boundary.
3. There is a functorial family of simply connected targets \(Y_R\), for all commutative rings \(R\), such that \(S(R)\) is naturally bijective to relative homotopy classes with target \(Y_R\). Thus, for a ring homomorphism \(R'\to R\), lifts of a point are exactly relative homotopy-class lifts along \(Y_{R'}\to Y_R\). If \(R\) is finite, a finite target with the same relative mapping classes can be constructed explicitly.
4. Every affine morphism can be represented by restriction along an inclusion of these pairs after replacing the source presentation by an equivalent one. Every finite composable chain can be represented simultaneously by nested inclusions. Fiber products of two affine morphisms can then be represented by gluing along the common smaller pair.

## Cup-product presentation and the circuit

Begin with a wedge of two-spheres with one common base point. Two of its spheres, denoted \(a,b\), are the fixed boundary \(A\). For every wire \(t\) of the arithmetic circuit add two spheres \(P_t,Q_t\). All other cells to be attached have dimension four, with attaching maps given by sums of Whitehead products of the inclusion maps of these spheres. In particular \(H^1(A;R)=H^3(A;R)=H^4(A;R)=0\) and \(H^3(K_S,A;R)=0\) in this CW model for every coefficient ring \(R\). The second cohomology has one coordinate for each sphere. Replacing the resulting CW pair by the simplicial pair constructed below preserves these facts.

For \(x,y\in H^2(K_S;R)\), write \((x_D,y_D)\) for their coordinates on a sphere \(D\). Fix \((x_a,y_a)=(1,0)\) and \((x_b,y_b)=(0,1)\). The evaluation of \(xy\) on the cell attached by \([D,E]\), for distinct source spheres \(D,E\), is

\[
x_Dy_E+x_Ey_D .
\]

Indeed the product attachment is the attaching map of the top cell of the oriented product of the two spheres. In the product, the two mixed cup evaluations are \(1\) and both individual squares vanish. Pull back or push out along the inclusion of that two-sphere wedge to obtain the claimed formula in the larger wedge. The evaluation is additive in the attaching class by the pinch map defining addition in \(\pi_3\), and changes sign on inversion of that class. Equivalently one can use the mixed coefficients of the Hopf matrix of the attachment. These formulas are integral, so they remain valid over every \(R\).

For each wire \(t\), attach cells along

\[
[P_t,a],\qquad [Q_t,b],\qquad [P_t,b]-[a,Q_t].
\]

The three cup equations say that \((x_{P_t},y_{P_t})=(t,0)\) and \((x_{Q_t},y_{Q_t})=(0,t)\) for one free scalar \(t\). This is elimination using coefficients \(1\) and \(-1\). The gates and output constraints now use the following attachments.

| Circuit equation | Attaching class |
| --- | --- |
| \(t=0\) | \([P_t,b]\) |
| \(t=1\) | \([P_t,b]-[a,b]\) |
| \(v=t+s\) | \([P_t,b]+[P_s,b]-[P_v,b]\) |
| \(v=-t\) | \([P_v,b]+[P_t,b]\) |
| \(v=ts\) | \([P_t,Q_s]-[P_v,b]\) |

The product case uses two distinct spheres even when \(s=t\), so its coefficient is \(1\) in every characteristic. Integer constants are computed by binary doubling and addition from \(0,1\), with a negation when needed. For a polynomial presentation, use arithmetic-circuit gates with fresh output variables and set all defining outputs to zero. Since each gate equation is monic linear in its fresh output variable, eliminating these in circuit order recovers the original polynomial ideal, not its radical. In particular the displayed degree equations give an isomorphism of affine schemes over \(\mathbb Z\).

## Relative homotopy and changes of coefficient ring

For a commutative ring \(R\) let \(B_R=K(R_{\mathrm{add}},2)\times K(R_{\mathrm{add}},2)\). Let \(c_R:B_R\to K(R_{\mathrm{add}},4)\) represent the cup product of the two tautological classes, using multiplication in \(R\). One can make the construction strictly natural in \(R\) using the simplicial cocycle models \(K(G,n)_k=Z^n(\Delta^k;G)\) and the usual cochain cup product. Put \(Y_R=\operatorname{hofib}(c_R)\). A map to \(Y_R\) means a map to \(B_R\) together with the nullhomotopy of its composite with \(c_R\). The boundary takes values \((1,0)\) and \((0,1)\) on its spheres. Over \(\mathbb Z\), choose representatives to \(B_{\mathbb Z}\) and choose a nullhomotopy on \(A\), which exists since \(H^4(A;\mathbb Z)=0\). Fix their images for every \(R\) under the unit map.

A degree assignment \((x,y)\) with these restrictions is represented by a map \(u:K_S\to B_R\) extending that fixed boundary. Cohomology represents maps to the Eilenberg–Mac Lane spaces. The homotopy extension property makes the boundary agree exactly, and \(H^1(A;R)=0\) ensures that two assignments with the same absolute second cohomology classes give the same relative homotopy class of \(u\).

The relative obstruction to extending the chosen boundary nullhomotopy for \(c_Ru\) lies in \(H^4(K_S,A;R)\). Its image in \(H^4(K_S;R)\) is \(xy\). The map of these fourth groups is an isomorphism because \(H^3(A;R)=H^4(A;R)=0\). Thus the lift exists exactly when \(xy=0\). For a fixed \(u\), the relative nullhomotopy classes, if nonempty, form a torsor for \(H^3(K_S,A;R)=0\), so the class is unique. Homotopies of \(u\) relative to \(A\) lift to the path-space fibration, keeping the fixed lift on \(A\). Together these facts give the asserted bijection, natural in \(R\).

In particular, a point \(S(k)\) over a field \(k\) has first-order deformations precisely given by relative homotopy-class lifts to \(Y_{k[\varepsilon]/(\varepsilon^2)}\) over \(Y_k\). Higher and mixed-characteristic finite-ring lifts have the same interpretation. This concerns relative homotopy classes, without asserting that each component of the full mapping space is contractible.

For finite \(R\), the cocycle models are finite in each degree. The simplicial path construction has the same property, since a map out of \(\Delta^k\times\Delta^1\) is determined by its values on finitely many nondegenerate simplices. Hence a finite \(5\)-skeleton of the resulting homotopy fiber is computable from the ring table. Its map into the full realization induces isomorphisms on \(\pi_i\) for \(i\le4\) and a surjection on \(\pi_5\) by cellular approximation. Thus it gives the same relative classes for a \(4\)-dimensional source. To maintain the exact boundary map when truncating, take a cellular representative of the integral boundary in the \(2\)-skeleton of the integral model before applying the coefficient maps. A finite simplicial complex homotopy equivalent to the finite CW skeleton gives a finite target version.

## One fixed finite integral target

There is also a fixed finite model for the integral target in the range used here. Start with \(U=\mathbb{CP}^2\vee\mathbb{CP}^2\), whose bottom sphere inclusions are denoted \(a,b\). The cross product of their two cohomology classes is zero. Therefore the map representing those classes into \(B_{\mathbb Z}\) lifts to \(Y_{\mathbb Z}\). One can take the boundary map for the preceding construction to be the restriction of this lift.

The two Hopf attachments kill precisely the two individual Hopf generators of \(\pi_3(S^2\vee S^2)\). The remaining free basis is \([a,b]\), by the Whitehead-product description of this wedge. Its image generates \(\pi_3(Y_{\mathbb Z})\cong\mathbb Z\): attaching a cell along this bracket evaluates the cup product of the two classes to \(1\), so the obstruction in \(K(\mathbb Z,4)\) is a generator. This argument also fixes the possible sign. The map \(U\to Y_{\mathbb Z}\) induces an isomorphism on \(\pi_2\) by construction.

Attach finitely many 5-cells to \(U\) to kill \(\pi_4(U)\); it is finitely generated because \(U\) is a finite simply connected CW complex. One can choose the attached classes explicitly. The map from the bottom wedge to \(U\) is surjective on \(\pi_4\), since the relative \(\pi_4\) is identified with the two relative \(4\)-cells and its boundary is injective into \(\pi_3\) of the wedge by independence of the two Hopf generators. The Hilton decomposition of \(\pi_4\) of the wedge has the two individual \(\pi_4(S^2)\) generators, \([a,b]\) composed with the suspended Hopf map, and the two basic triple Whitehead products. The first two are already killed by the Hopf attachments. The remaining three classes therefore suffice as the attaching maps of 5-cells. All their images in \(Y_{\mathbb Z}\) vanish since \(\pi_4(Y_{\mathbb Z})=0\), so the comparison map extends. The resulting \(Y\to Y_{\mathbb Z}\) induces isomorphisms on homotopy through degree four and surjects in degree five since the target group is zero. Its homotopy fiber is \(4\)-connected. Relative obstruction theory on \(K_S\) and on the homotopy cylinder consequently gives bijections on relative classes. Replace this finite CW construction by a finite simplicial one, retaining the bottom wedge and its fixed boundary map, using simplicial attaching maps and mapping cylinders.

## Size and relative simplicial complexes

Fix one triangulation of each bottom sphere, with the same chosen base vertex. A gate has at most three Whitehead terms, so it has a constant-size triangulated \(3\)-sphere and a simplicial representative into a wedge of a bounded number of the fixed spheres. Such a finite collection of templates exists by simplicial approximation to the Whitehead attachment of a product of spheres and to the pinch sums, using joins with a sphere copy or connected sum for the latter. Each is chosen once. Naming the bottom spheres, including repetitions, is a simplicial map and costs no subdivision. Use a disjoint copy of the source vertices for each attaching map.

For completeness, if \(f:L\to W\) is such an attachment, put a linear order on the vertices of \(L\). Use the simplicial mapping cylinder defined by adjoining, for each ordered simplex \(v_0,\ldots,v_j\) of \(L\), the simplices with vertex lists

\[
f(v_0),\ldots,f(v_i),v_i,\ldots,v_j\qquad(0\le i\le j)
\]

and their faces, allowing repeated image vertices to collapse. Collapse each bottom-copy vertex \(v\) to \(f(v)\), in increasing order. Consecutive maps are contiguous, since their union on each simplex is contained in the staircase simplex whose cut is the changed vertex. This deforms the cylinder to \(W\) relative to \(W\). Cone off the disjoint source copy. The resulting map to the ordinary CW attachment is a homotopy equivalence relative to \(W\): it is a relative homology isomorphism after collapse, and both spaces are simply connected. Since \(j\le3\), the resulting simplicial construction has dimension at most four. Separate cones and source copies allow all attachments simultaneously and preserve every earlier subcomplex. There are a bounded number of simplices per sphere or elementary gate and hence polynomially many in the input presentation. No subdivision or change is made to the fixed boundary \(A\).

## Affine morphisms and gluing

Let \(f:T\to S\) be an affine morphism between schemes presented by variable lists \(s,t\) and equation lists \(F_S(s),F_T(t)\). Specify \(f\) by circuits \(f_j(t)\) for the images of the target coordinates \(s_j\) in \(\mathbb Z[T]\). Start with the constructed pair for \(S\). Add the spheres and gate cells for \(T\) and for these coordinate circuits, then add equality cells for \(s_j=f_j(t)\). The resulting pair \(K_T'\) contains \(K_S\) literally as a simplicial subcomplex. Its degree ring is

\[
\mathbb Z[s,t]/(F_S(s),F_T(t),s-f(t))\cong\mathbb Z[T],
\]

since \(F_S(f(t))=0\) in \(\mathbb Z[T]\). The restriction map on degrees and on relative homotopy classes is exactly \(f\), for every \(R\). Iterating this operation gives literal nested inclusions for any given finite composable chain. The restrictions along the composites agree because the intermediate coordinate substitutions are the coordinate formulas for the composed morphisms.

For two such graph presentations over \(K_S\), identify their copies of \(K_S\) and keep all other spheres and cells disjoint. Their union has the two equation systems with their \(S\)-coordinates identified, exactly the tensor product of the two affine coordinate rings over \(\mathbb Z[S]\). It is still a simply connected four-dimensional simplicial model with the same boundary. Thus fiber products and their induced relative homotopy restrictions are preserved, even over nonreduced schemes.

## Prior work and scope

The Whitehead-product reduction of Čadek, Krčál, Matoušek, Vokřínek and Wagner already encodes arbitrary systems of quadratic equations in low-dimensional extension problems. That technique is an input. The claims here concern an exact coordinate-ring presentation over \(\mathbb Z\), uniqueness of the relative homotopy class for each solution, functorial coefficient-ring changes, and restriction and fiber-product constructions. These are distinct from an undecidability reduction. Priority for the refinements has not been established. [Extendability of continuous maps is undecidable](https://arxiv.org/abs/1302.2370) · [Whitehead products and the wedge calculation, Hatcher §4](https://pi.math.cornell.edu/~hatcher/AT/AT-doublepage.pdf) · [Binary simplicial cup-table realization](https://github.com/Dugongue/MathProofs/blob/main/HigherOrderUniversality/SharpFourDimensionalHomotopy.md)
