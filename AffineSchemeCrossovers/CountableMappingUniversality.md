# Closed path spaces and analytic sets as relative homotopy problems

Let \(\mathcal N=\mathbb N^{\mathbb N}\) with its product topology. The following results use the same finite integral cup-product target as the four-dimensional affine-scheme realization.

**1. A fixed bounded-valence source for all closed path spaces.** There is one connected simply connected locally finite simplicial pair \((K,A)\), of dimension at most four and uniformly bounded vertex degree, and one fixed finite simply connected simplicial target \(Y\). For each tree \(T\subseteq\mathbb N^{<\mathbb N}\), a boundary map \(f_T:A\to Y\), varying only independent binary degrees on fixed marked spheres, has the property that its relative homotopy-class space is homeomorphic to \([T]\). This is the quotient of the compact-open topology on extensions by relative homotopy. The degree map has a continuous choice of representatives. The pair and dependence on the binary tree code can be made effective.

**2. Exact continuous relations by restriction.** Given a closed relation \(C\subseteq X_1\times\cdots\times X_m\), where the \(X_i\) are closed subspaces of \(\mathcal N\), there is a locally finite simplicial diagram with common marking and target \(Y\). The relative homotopy-class space of its large member is \(C\), those of its small members are the \(X_i\), and the restriction maps are exactly the coordinate projections. For the graph of a continuous map \(g:X\to Z\), one restriction is a homeomorphism and the other gives \(g\). Finite diagram solution spaces for such graphs can also be realized directly, with the projections to all their objects. Computable presentations give an effective construction whenever the closed sets and relations are effectively closed.

**3. A single restriction map with universal analytic image.** There is a fixed inclusion of locally finite simply connected four-dimensional simplicial pairs, with one fixed boundary map and finite target \(Y\), whose image on relative homotopy classes is a universal analytic set. In particular the image is not Borel. Every analytic subset of \(\mathcal N\) is a section of this one image as the first parameter varies. The complexes, the inclusion and the boundary map can all be chosen computable.

## A locally finite countable form of the affine realization

Start with any countable system of polynomial equations in countably many integer variables. Each equation uses finitely many variables. The equations may contain parameters which will be prescribed degrees on marked spheres. Use addition and multiplication circuits with fresh wires to replace each equation by elementary gates. For integer constants use binary doubling and addition. A signed constant can also be imposed by a negation gate.

First build a locally finite, possibly unbounded-valence version. Use a ray with vertices \(v_0,v_1,\ldots\), include it in the marking, and map it constantly to the base point. At vertex \(v_n\) include copies of named variables whose index is at most \(n\), and the local wires of finitely many gates that can be scheduled there once their named inputs have appeared. Schedule every gate at some finite stage. For each variable present at neighboring stages join its two copies by an equality gate. Each site has just finitely many attachments, and every attaching sphere lies at one site or at two neighboring sites joined by their scaffold edge. Thus only finitely many cells touch each site. At each site use the two anchor spheres with fixed degrees \((1,0)\) and \((0,1)\).

The elementary gates are precisely those in the affine realization. Each scalar wire has two two-spheres \(P,Q\) with degrees forced to \((u,0),(0,u)\). Whitehead products impose the required equations in degree four. For example equality between a scalar \(u\) at one site and \(v\) at its neighbor is the single cup constraint on the difference \([P_u,b]-[P_v,b]\), where \(b\) is the anchor at the first site and the base point for \(P_v\) is transported along the intervening marked edge. Marking a wire sphere \(P\) with degrees \((c,0)\) pins that variable to \(c\). Monic gate relations determine every auxiliary gate wire uniquely. Equality relations determine every copy of a named variable uniquely. This gives a homeomorphism of the coordinate solution spaces, each taken with the subspace topology of its product of discrete coordinates: for every individual wire, its value is a polynomial in finitely many original coordinates.

Here is a bounded-valence realization. Within every stage split a variable's incidences into separate ports, linked by a chain of equality relations. Separate gate sites from wire sites. Each resulting site has a bounded number of wire ports and incident edges, since only elementary gates are used. This is an effectively locally finite graph: each stage circuit is finite, and links between different stages only go to the two adjacent stages, whose finite lists determine every star. Use the standard cubical half-space lattice \(z\ge0\) in dimension three as the scaffold, triangulated compatibly and marked in its entirety. Put successive sites at \((Mi,0,0)\), with one port column at \((Mi+j,0,z)\) for each possible port \(1\le j<M\) and a fixed \(M\) larger than every site's valence. Join the site to its port bases by the short horizontal paths at height zero. Overlaps here are confined to one site and have bounded multiplicity. Give each incidence edge its own positive height, by a computable injection from its two labeled ports to integers, with a computable inverse on its range. At that height connect the two port columns by a path along \(y=1\), using the two \(y\)-edges at the ends. Vertical columns lie in \(y=0\), and horizontal paths have distinct heights. Thus away from the finite site gadgets these routes have uniformly bounded multiplicity. Route an edge carrying a scalar by a fresh copy at every lattice step, tying neighboring copies by the equality constraint. At each used lattice point only boundedly many spheres and constraints occur. Use the fixed finite simplicial templates for attachments on a wedge or across one scaffold edge, with disjoint domain copies for different four-cells. These triangulations have a uniform bound on vertex degree. The scaffold is contractible and contributes no extra coordinate.

The construction is effective for a computable list of equations, or for a computably enumerable list by using finite time stages. At each time stage perform a bounded amount of enumeration and output the gates that have appeared, carrying all already introduced named variables to the next stage. A fixed stage can be recovered by replaying finitely many steps. For the grid construction a vertical port is associated to at most one computable edge and length. At a positive horizontal height decode its edge label and check its endpoints. These tests compute the local structures in finite time.

In both versions the relative cellular model, with the scaffold and all marked spheres removed, has cells only in degrees two and four. The scaffold is contractible. Thus \(H^3(K,A;R)=0\), \(H^1(A;R)=H^3(A;R)=H^4(A;R)=0\), and \(H^2(K;R)\) is the product of one copy of \(R\) for each sphere. Ordinary cellular cochains are products for countable CW complexes. All cup tests are the stated finite expressions, since the attaching maps meet only a finite number of sphere summands and scaffold edges. The relative lifting argument for
\[
Y_R=\operatorname{hofib}\bigl(K(R_{\rm add},2)^2\longrightarrow K(R_{\rm add},4)\bigr)
\]
therefore applies in full to the countable pair. It identifies the solutions over \(R\) with relative homotopy classes. In the integral case the fixed finite target \(Y\) still suffices: its comparison map to \(Y_{\mathbb Z}\) suffices for obstruction theory on the source and its relative homotopy cylinder, which have dimension at most four and five respectively. The argument is skeletal and applies to arbitrary CW pairs in those dimensions.

For integral points the identification is topological. Each degree is continuous on the extension space with discrete target for that coordinate, by restricting to its compact sphere. A finite simplicial target is locally an absolute neighborhood retract, so sufficiently close maps on the compact sphere have the same homotopy class. Conversely, for each pair of degrees choose a fixed map on an associated sphere and fix the scaffold map to be constant. For each attaching template and feasible local list of degrees choose one extension over its closed four-cell. These maps agree on the attaching boundaries and form a continuous map on the CW complex. They give a section continuous in the coordinate solution, since on any finite group of cells it depends on finitely many degrees. Compact subsets of a locally finite model meet finitely many cells. For the simplicial mapping-cylinder model precompose with the collapse to the cellular attachment. The quotient topology on relative classes is therefore exactly the topology of the coordinate solution space.

## Exact integer encoding of a path

Fix a rooted tree alphabet \(\mathbb N\). Use variables \(t_\sigma\), \(u_{\sigma,j}\), and \(w_{\sigma,j}\) for every finite word \(\sigma\) and \(j\ge0\), with \(t_\sigma\) independent of \(j\). Use parameters \(b_\sigma\in\{0,1\}\), where \(b_\sigma=1\) means that \(\sigma\) is allowed to occur on the path. Require
\[
\begin{aligned}
t_\varnothing&=1,& t_\sigma(1-b_\sigma)&=0,\\
t_\sigma^2&=t_\sigma,& u_{\sigma,j}^2&=u_{\sigma,j},\\
u_{\sigma,0}&=t_\sigma,& u_{\sigma,j}&=t_{\sigma^\frown j}+u_{\sigma,j+1},\\
u_{\sigma,j}&=w_{\sigma,j}-2^{j+1}w_{\sigma,j+1}.
\end{aligned}
\]
All terms involving the growing scalar \(2^{j+1}\) can be realized by a fixed syntactic family of doubling circuits of finite length for each \(j\). The templates, including the tests with \(b_\sigma\), do not depend on its prescribed values.

Over the integers \(t,u\) are bits. If \(t_\sigma=0\), the recurrence forces all \(u_{\sigma,j}\) and all children to be zero. If \(t_\sigma=1\), either exactly one child is active, or the remainder \(u_{\sigma,j}\) stays equal to one forever. The latter is impossible. Write \(B_0=1\), \(B_{j+1}=2^{j+1}B_j\). An all-one remainder would require
\[
w_{\sigma,0}\equiv \sum_{j<N}B_j\pmod {B_N}
\quad\text{for every }N.
\]
Since \(\sum_{j<N}B_j\le N B_{N-1}\) and \(N B_{N-1}/B_N\to0\), for large \(N\) this congruence would force equality over the integers. The prefix sums increase strictly, a contradiction. Hence the active nodes are exactly the prefixes of one infinite sequence, all of whose prefixes are allowed.

Conversely, a sequence of allowed prefixes determines \(t,u\). Every \(u_{\sigma,\bullet}\) is then finitely supported, so \(w_{\sigma,j}=\sum_{i\ge j}u_{\sigma,i}B_i/B_j\) is an integer. This solution is unique because differences between two such \(w\) solutions give a homogeneous recurrence with arbitrarily high divisibility. The map from paths to solutions is continuous: for any one node, its activity and, if active, its chosen child are determined by a finite prefix of the input sequence. These determine all individual \(t,u,w\) coordinates at that node. In the other direction the condition that a path begins with \(\sigma\) is \(t_\sigma=1\), a clopen coordinate condition. Thus the encoding is a homeomorphism.

The lacunary remainder device is adapted from the earlier linear phantom-extension reduction. The Boolean constraints here make every witness unique, which is what allows an exact topological realization rather than a test of existence. [Earlier arithmetic encoding](https://github.com/Dugongue/MathProofs/blob/main/Top100InformalProofs/96/infinite-complex-extension.md).

This proves Theorem 1 by applying the bounded-valence compiler to the fixed system and using \(b_\sigma\) as marked degrees. A boundary assignment of bits for any tree now gives precisely its closed path space. In particular each closed subspace of Baire space occurs, since it can be recovered from its finite prefixes. For a computable tree, its boundary map on the fixed triangulation is computable. Marked bit spheres use one of two fixed maps, chosen by evaluating the corresponding tree bit.

## Relations and graphs

For each coordinate introduce an independent copy of the unrestricted path equations. For each basic cylinder disjoint from \(X_i\), impose \(t^{(i)}_\sigma=0\) in the \(i\)-th small complex. It suffices to use any family of cylinders covering the complement. For any finite tuple of prefixes \((\sigma_1,\ldots,\sigma_m)\) of equal length whose product cylinder is disjoint from \(C\), add
\[
t^{(1)}_{\sigma_1}\cdots t^{(m)}_{\sigma_m}=0.
\]
The new equations retain precisely \(C\), since the complements of its closed cylinders are described by forbidden prefixes. Each coordinate path encoding is unique, so there are no additional classes over any retained tuple. Reserve all anchors in a common marked ray. Place the independent coordinate circuits at each stage before adding new copies and gates for the relation. The large pair literally contains the smaller coordinate subcomplexes, and the common marking is unchanged. If an effectively closed subset is specified by an enumeration of open cylinders, convert each cylinder with different prefix lengths to the countably many equal-length extensions and enumerate their product tests. The finite-stage compiler can then run that enumeration. Relative restriction forgets exactly the other coordinates and has the announced topology.

For a continuous \(g:X\to Z\), its graph is closed in the product with the stated closed spaces. Its projection to \(X\) is a homeomorphism, so the two restrictions realize \(g\). For a finite diagram use all its vertices as coordinates and intersect the finitely many graph relations for the arrows. The resulting closed relation is exactly the ordinary limit of that diagram, and the same construction gives its projections. This proves Theorem 2.

## Universal analytic image on one fixed inclusion

Set every allowed bit of a first path to one. Add independent Boolean variables \(c_{\sigma,\tau}\), one for each pair of words of equal length. The smaller pair realizes the unrestricted parameter product \(2^{\mathbb N}\times\mathcal N\). These Boolean variables are free coordinates of the smaller pair rather than prescribed values in the boundary. In the larger pair add a second unrestricted path and require
\[
t_\sigma s_\tau(1-c_{\sigma,\tau})=0
\]
for every pair of equal-length prefixes; \(t\) and \(s\) are the two path indicators. The construction and its boundary are now fixed. On the topological coordinate spaces the restriction projection has image
\[
\mathcal U=\bigl\{(c,x):\exists y\in\mathcal N\
  \forall n,\ c_{x|n,y|n}=1\bigr\}.
\]
It is analytic because the relation before projection is closed. Conversely take any analytic set \(E\subseteq\mathcal N\) and express it as the projection of a closed \(F\subseteq\mathcal N^2\). Let \(c_F\) mark the finite prefix pairs of \(F\). Then \(x\in E\) exactly when \((c_F,x)\in\mathcal U\). The map \(x\mapsto(c_F,x)\) is continuous. Thus \(\mathcal U\) is analytic-complete and non-Borel, using the classical projection characterization and existence of analytic non-Borel sets. With a recursive tree presentation of an effective analytic set the same reduction is effective. This proves Theorem 3.
