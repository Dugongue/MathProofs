# Every affine scheme of finite presentation is realized by maps out of a closed six-manifold

Let \(S\) be an affine scheme of finite presentation over \(\mathbb Z\). There is a closed simply connected oriented smooth stably parallelizable six-manifold \(M_S\) with torsion-free integral homology and \(H^3(M_S;\mathbb Z)=0\), together with a marked connected subcomplex \(A_S\) homotopy equivalent to a finite wedge of two-spheres, with the following property. The degree-equation scheme for the prescribed relative map to the cup-product target is exactly \(S\) over \(\mathbb Z\). Its \(R\)-points are bijective to relative homotopy classes with target

\[
Y_R=\operatorname{hofib}\bigl(K(R_{\rm add},2)^2
\xrightarrow{\ \smile\ }K(R_{\rm add},4)\bigr)
\]

for every commutative ring \(R\), naturally in \(R\). There is a single finite integral target \(Y^{(6)}\) for all the manifolds in the construction. The marked subcomplex lies inside the closed manifold and prescribes degree coordinates. Its number of spheres varies with the presentation.

## The quadrics become cup tests

Use the circuit construction in [the four-dimensional theorem](UniversalRelativeMappingSchemes.md). Its fixed pins are \(a,b\) with respective values \((1,0),(0,1)\), and its equations are an explicit list of integral expressions

\[
g_j(x,y)=\sum_{\{D,E\}}m_{jDE}(x_Dy_E+x_Ey_D)=0.
\]

Each unordered pair in a summand has distinct sphere labels, even in a square gate, because the two copies \(P_t,Q_t\) of a wire are separate. Add one new degree coordinate \(z_j\) for each equation. Define an integral symmetric trilinear form \(\mu\) on the basis of all the degree coordinates by

\[
\mu(D,E,z_j)=m_{jDE}
\]

and its permutations. Give it value zero on every other basis triple. Its diagonal cubic is

\[
\mu(\xi,\xi,\xi)=6\sum_{j,\{D,E\}}m_{jDE}\xi_D\xi_E\xi_{z_j}.
\]

Realize this exact cup cubic on a manifold as below. Prescribe the two anchor values on retained representative spheres for \(a,b\), and value \((0,0)\) on each sphere for \(z_j\). Poincaré duality then says that \(xy=0\) if and only if \(\mu(x,y,D)=0\) for every degree-two basis vector \(D\). This holds over every commutative coefficient ring, by integral dual bases and the torsion-free homology. Under the pins all tests on the original coordinates vanish identically. The test on \(z_j\) is precisely \(g_j=0\). Thus these degree equations preserve the original coordinate ring, including nilpotents and at the primes two and three. The exactness comes from realizing the trilinear form, rather than merely the cubic up to a scalar.

## Framed realization retaining the marked spheres

Start with an oriented connected sum of one \(S^2\times S^4\) for each coordinate in the final form and one \((S^2)^3\) for each signed summand in \(\sum m_{jDE}\xi_D\xi_E\xi_{z_j}\), repeating a summand as necessary. The circuit presentation above has a bounded number of signed terms per equation, so this produces only a linear number of summands. The first kind of summand has zero cubic. On each summand of the second kind, call its three coordinates \(u,v,w\); its diagonal cubic is \(6uvw\). For each signed summand impose \(u=\pm \xi_D\), \(v=\xi_E\), \(w=\xi_{z_j}\), placing the sign in the first equality.

In homology each of these equalities is the annihilation of a primitive difference or sum of two coordinate sphere classes. The relations are independent with primitive span, because each equation has its own one of the temporary coordinates \(u,v,w\) with coefficient one and only original coordinates elsewhere. The quotient of the original \(H_2\) has basis precisely the original coordinates. Take disjoint parallel copies of all the coordinate spheres needed for the relations. Embedded representatives in different factors of \((S^2)^3\) can be chosen disjoint by using distinct fixed coordinates in a common fixed factor. A relation is represented by the connected sum of its two signed sphere copies along a thin tube. The tube cores can be chosen disjoint and disjoint from all other sphere copies by general position in dimension six. Retain another disjoint sphere copy in its original \(S^2\times S^4\) for each anchor or \(z_j\).

The initial manifold is stably parallelizable. The individual products are stably parallelizable and the connected-sum trace extends the stable framings over oriented 1-handles. Each relation sphere has stably trivial oriented normal bundle because the ambient tangent bundle and the tangent bundle of the sphere are stably trivial. An oriented rank-four bundle over \(S^2\) is determined by its clutching loop, and \(\pi_1(SO(4))\to\pi_1(SO)\) is an isomorphism, so its normal bundle is trivial. Perform the framed surgeries replacing \(S^2\times D^4\) by \(D^3\times S^3\). The stable framing extends across the 3-handles since \(\pi_2(SO)=0\). Surgery in codimension four preserves simple connectivity by general position for loops and disks and van Kampen.

Let \(W\) be the surgery trace, and let \(r\) be the number of relations. Its relative homology from the initial side is generated by \(r\) three-handles. Their boundary map takes them to the displayed primitive independent relations. In degree two \(H_2(W)\) is therefore the free quotient by those relations. From the other side the relative handles have index four, so \(H_2(M_S)\to H_2(W)\) is an isomorphism. Each surgery decreases the Euler characteristic by two and the second Betti number by one. Poincaré duality over \(\mathbb Q\) gives \(b_3(M_S)=0\), since the initial third Betti number is zero. Integral duality and the universal coefficient theorem, using that \(H_2(M_S)\) is free, give \(H_3(M_S)=0\) and torsion-free homology in all degrees.

Under restriction from \(W\) the degree-two cohomology on the initial side is exactly the annihilator of the relation spheres. The cubic evaluations on the two ends of \(W\) agree for these extended classes. Substituting the displayed equalities into the initial cubic therefore gives \(\mu(\xi,\xi,\xi)\) on \(M_S\). This equality identifies the trilinear forms over \(\mathbb Z\): over \(\mathbb Q\) it follows by polarization, and both forms take integral values on the same free integral basis. The resulting integral identity may then be extended to all coefficient rings. For the original coordinates each retained sphere represents its intended basis class, as no surgery touches it and the trace identifies its homology class with the original coordinate modulo the relations.

Join the retained spheres by disjoint arcs forming a tree away from their interiors and from the surgery neighborhoods. The union is a finite marked subcomplex of a common triangulation of the pair. For instance the explicit PL scheme in the cited framed realization allows the retained spheres in fixed product charts and the arcs in general position in the complements of the relation tubes. Its homotopy type is a wedge of two-spheres, and its \(H_2\) maps to the direct summand generated by the marked coordinate classes. Give the tree constant boundary value and use the prescribed sphere maps. The surgery argument is the square-free special case of the existing cubic realization. Its added requirement here is keeping these specified sphere copies in the complement. [Framed surgery and triangulation](https://github.com/Dugongue/MathProofs/blob/main/ManinGrochowCrossovers/IntegralTensorManifolds.md)

## Relative maps and finite integral target

For the pair \((M_S,A_S)\), \(H^1(A_S;R)=H^3(A_S;R)=H^4(A_S;R)=0\), and the map \(H^2(M_S;R)\to H^2(A_S;R)\) is onto because the marked classes are a subset of a basis. Since \(H^3(M_S;R)=0\), the relative third group \(H^3(M_S,A_S;R)\) vanishes as well. Thus the relative lifting argument for the cup-product target applies verbatim. The absolute cup \(xy\) identifies the relative obstruction, and its vanishing gives one relative homotopy class for each satisfying assignment.

For the fixed integral comparison, take the finite model in the four-dimensional proof and attach finitely many 6-cells and then 7-cells to kill its fifth and sixth homotopy groups. At each step the group being killed is finitely generated because the space is finite and simply connected. Its comparison to \(Y_{\mathbb Z}\) extends over these cells and is an isomorphism on homotopy in dimensions at most six, with surjection in dimension seven. The comparison has \(6\)-connected homotopy fiber, which suffices for equivalence on relative homotopy classes on all six-dimensional pairs and their homotopy cylinders. The fixed bottom two sphere maps and the constant based sphere map provide all boundary pins in the integral model. For finite \(R\), truncate the finite-per-degree cocycle homotopy fiber construction to its \(7\)-skeleton to get the analogous finite model in this range.

## A fixed closed smooth integral target

The finite integral comparison target can itself be chosen to be a simply connected closed smooth stably parallelizable \(14\)-manifold. Take a finite simplicial model of dimension at most seven for the finite target just constructed and embed it linearly in \(\mathbb R^{15}\), choosing vertices in affine general position. The convex hulls of any two simplices intersect exactly in their common face because their union uses at most sixteen vertices. A smooth regular neighborhood \(W\) deformation retracts onto this embedded model and has handles of index at most seven. Turning the handle decomposition upside down describes \((W,\partial W)\) by relative handles of index at least eight. Thus \(\partial W\to W\) is \(7\)-connected. In particular \(\partial W\) is simply connected, and it is stably parallelizable since \(TW\) is trivial as a codimension-zero Euclidean domain and \(T\partial W\oplus\mathbb R=TW|_{\partial W}\). [Smooth regular neighborhoods, Wall, Proposition 7.2](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/wall.pdf)

Composing to \(Y_{\mathbb Z}\) gives the same relative classes for all the marked six-manifolds. Choose based representatives of the two anchor sphere classes on \(\partial W\) and the constant based representative for the remaining pins. Their compositions to \(Y_{\mathbb Z}\) are based homotopic to the corresponding prescribed pins, so transporting the boundary map by that homotopy gives the required correspondence of relative classes. This target is chosen once. Thus the integral result admits both a closed smooth source of dimension six and a fixed closed smooth target of dimension fourteen.

## Six is the first possible closed-source dimension for these targets

For the same cup-product targets and two-dimensional marking spaces, no smaller closed simply connected source dimension works for exact scheme universality. Over an algebraically closed field of characteristic zero the assignments satisfying the prescribed second-cohomology restrictions form an affine space whenever they are consistent. For a closed simply connected source of dimension at most three or dimension five, the fourth cohomology vanishes. In dimension five this follows from Poincaré duality and \(H_1=0\). The degree-assignment scheme is therefore affine space or empty. For a closed simply connected four-manifold, fourth cohomology has rank one, so the scheme is cut out by one polynomial of degree at most two on that affine space. If nonempty and zero-dimensional, it has length at most two by the hypersurface dimension theorem and the degree bound in one variable. Thus even three disjoint points cannot be represented in these source dimensions. The six-dimensional construction attains the threshold for this target and degree model.
