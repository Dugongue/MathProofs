# Kapovich–Millson Problem 4.3 and the number of projective-plane cone points

**Theorem 1.** Let \(Y\) be a connected closed 3-dimensional pseudomanifold whose nonmanifold points are exactly \(2k>0\) cone points with link \(\mathbb{RP}^2\), and put \(\Gamma=\pi_1(Y)\). For every field \(F\), write \(\beta_i(\Gamma;F)=\dim_F H_i(\Gamma;F)\). Then

\[
k\ \ge\ \beta_2(\Gamma;F)-\beta_1(\Gamma;F)+1-\mathbf 1_{\operatorname{char}F=2}.
\]

In particular, \(\mathbb Z^4\) requires at least six cone points. Kapovich and Millson’s Problem 4.3 asks if every finitely presented group can be realized with exactly two such points. The answer is negative. [Kapovich–Millson, Problem 4.3](https://www.math.ucdavis.edu/~kapovich/EPR/char.pdf)

**Proof.** Remove open conical neighborhoods to obtain a connected compact 3-manifold \(P\) with \(2k\) projective planes as boundary. The double of \(P\) has Euler characteristic zero by mod-2 Poincaré duality. Additivity gives \(2\chi(P)=\chi(\partial P)=2k\). Capping a projective plane with its cone preserves Euler characteristic, so \(\chi(Y)=k\).

Let \(A\) be the disjoint union of the closed cone neighborhoods. Each component is contractible, and the pair sequence and excision give \(H_3(Y;F)\cong H_3(Y,A;F)\cong H_3(P,\partial P;F)\). A connected orientable manifold has orientable boundary, so \(P\) is nonorientable. Poincaré–Lefschetz duality gives \(\dim_F H_3(P,\partial P;F)=\mathbf 1_{\operatorname{char}F=2}\). Consequently

\[
\dim_F H_2(Y;F)=k-1+\beta_1(\Gamma;F)+\mathbf 1_{\operatorname{char}F=2}.
\]

A classifying space for \(\Gamma\) is obtained from \(Y\) by attaching cells of dimension at least three. Thus \(H_2(Y;F)\to H_2(\Gamma;F)\) is surjective. For \(\Gamma=\mathbb Z^4\), the 4-torus is a classifying space and \(\beta_2=6\), \(\beta_1=4\), giving \(k\ge3\) over \(\mathbb Q\). The same bound holds for \((\mathbb Z/2)^3\) over \(\mathbb F_2\), where \(\beta_2=6\) and \(\beta_1=3\) by the Künneth formula for \((\mathbb{RP}^{\infty})^3\). \(\square\)

**Local-coefficient version.** For a finite-dimensional \(F[\Gamma]\)-module \(V\) of dimension \(d\), put \(\beta_i(\Gamma;V)=\dim_F H_i(\Gamma;V)\) and write \(V^\Gamma\) for the invariant subspace. The bound is

\[
dk\ \ge\ \beta_2(\Gamma;V)-\beta_1(\Gamma;V)+\beta_0(\Gamma;V)
-\mathbf 1_{\operatorname{char}F=2}\dim_F V^\Gamma.
\]

Indeed, \(\chi(Y;V)=d\chi(Y)\), and the same pair argument computes \(H_3(Y;V)\) from \(H_3(P,\partial P;V)\). By duality this is the space of invariants in \(V\) tensored with the orientation character of \(P\). An orientation-reversing boundary loop acts trivially on \(V\) because it is null-homotopic in \(Y\), so the invariant space vanishes in characteristic different from two. In characteristic two the orientation character is trivial and \(\pi_1(P)\to\Gamma\) is surjective, yielding \(V^\Gamma\). Attaching classifying cells preserves degree zero and one homology and gives a surjection in degree two with these coefficients as well. \(\square\)

## Hyperbolic realization with a presentation-size bound

**Theorem 2.** A group with a finite presentation having \(s\) relators is the fundamental group of the underlying space of a compact hyperbolic 3-orbifold with exactly \(2(s+1)\) nonmanifold points, each with topological link \(\mathbb{RP}^2\). More generally, any positive number of such points realized by a closed 3-pseudomanifold for that group is realized by the underlying space of a compact hyperbolic 3-orbifold for the same group.

The same presentation bound holds if the group is obtained from the fundamental group of a closed connected 3-manifold by imposing \(s\) relators.

**Klein-bottle filling lemma.** Let the interior of a compact 3-manifold \(E\) with nonempty Klein-bottle boundary admit a complete finite-volume hyperbolic metric. Then there is a compact hyperbolic 3-orbifold obtained by filling each end with a simply connected topological piece containing exactly two nonmanifold points, each a cone on \(\mathbb{RP}^2\). In particular, its underlying fundamental group is the quotient of \(\pi_1(E)\) by the normal closure of its boundary subgroups.

For the lemma, use the simultaneous real holonomy coordinates of Durán Batalla and Porti, Theorem 3.10. On each Klein bottle take the distinguished element \(a^2\) of \(\langle a,b\mid aba^{-1}=b^{-1}\rangle\). The coordinate is \(I_{a^2}=\operatorname{tr}^2(\rho(a^2))-4\). Taking all these coordinates equal to \(-4\sin^2(\pi/m)\) for a sufficiently large odd integer \(m\) gives type-II deformations by their Lemma 4.5. In the type-II normal form of Theorem 4.2, \(a^2\) is the rotation and \(b\) is the translation along its axis. Thus \(a^2\) is the primitive meridian of the orientation double of the cap in Theorem 5.15. The cone angle \(\theta\), which tends to zero at the complete metric, satisfies \(I_{a^2}=-4\sin^2(\theta/2)\), giving \(\theta=2\pi/m\). The completion is locally an orbifold along the interior of its singular interval, with cyclic group \(C_m\). The two endpoint models of Definition 5.5 quotient further by a half-turn in the angular parameter together with reversal of the axis. On the smooth cover of the cone this lifts to rotation by \(\pi/m\) followed by reversal of the axis. For odd \(m\), composing with a power of the order-\(m\) rotation gives central inversion at the endpoint. Thus the local group is finite, generated by the order-\(m\) rotation and central inversion. The cap is topologically two cones on \(\mathbb{RP}^2\) joined by one 1-handle, so it is simply connected. The quotient description now follows from van Kampen. The interior of each interval is topologically regular even though it has cyclic orbifold isotropy. [Durán Batalla–Porti, Sections 3–5](https://arxiv.org/pdf/2011.01027)

**Proof of the presentation bound.** Write \(\Gamma=\langle x_1,\dots,x_g\mid r_1,\dots,r_s\rangle\), and take the connected sum of the nonorientable \(S^2\)-bundle over \(S^1\) with \(g\) copies of \(S^2\times S^1\). Its fundamental group is free on \(t,x_1,\dots,x_g\), with \(t\) orientation reversing and each \(x_i\) orientation preserving. Represent the \(s+1\) conjugacy classes \(t,r_1t,\dots,r_st\) by a disjoint embedded link, using general position. Myers’s excellent 1-manifold theorem replaces this link by a homotopic excellent link. Each component remains orientation reversing and has a twisted disk-bundle neighborhood with Klein-bottle boundary. Its excellent exterior \(E\) has complete finite-volume hyperbolic interior by hyperbolization. [Myers, Theorem 1.1 and introduction](https://doi.org/10.1016/0166-8641(93)90038-F)

Replacing the removed disk bundles with the caps from the lemma kills the whole peripheral group of each Klein bottle. Restoring a removed disk bundle instead kills only its meridian and identifies its longitude with the corresponding link class. More precisely, boundary inclusion into a disk bundle surjects onto its infinite cyclic fundamental group, with kernel generated by the meridian. Thus, after killing all boundary subgroups of \(E\), the resulting quotient is

\[
F(t,x_1,\dots,x_g)/\langle\!\langle t,r_1t,\dots,r_st\rangle\!\rangle\ \cong\ \Gamma.
\]

There are two nonmanifold points per cap, which gives the stated count. For the more general case, replace the connected sum of \(g\) products \(S^2\times S^1\) with the given closed 3-manifold, and still adjoin the nonorientable bundle summand with core \(t\). Represent each relator by \(r_i t\) if it preserves orientation and by \(r_i\) if it reverses orientation. Include \(t\) itself in the link. All link components reverse orientation, and killing \(t\) and their other cores again imposes exactly the prescribed relators on the given 3-manifold group. \(\square\)

**Proof of preservation of a realized count.** Take the same compact manifold \(P\) obtained by excising the cone neighborhoods of a given model with \(2k>0\) cone points. Pair the boundary components. Join each pair by a properly embedded arc with one endpoint on each component, choosing all the arcs disjoint. Because every projective-plane boundary component meets an arc, Myers’s theorem applies relative to the endpoints. The excellent exterior of the new arcs has \(k\) boundary components, each made of two punctured projective planes joined by the lateral annulus of an arc neighborhood. Each component is a Klein bottle. Give the interior its complete finite-volume hyperbolic metric and apply the lemma.

To compare the groups, first recover the given cone model by attaching to the same exterior the union of each closed arc neighborhood with its two adjacent projective-plane cones. Each such piece is two contractible cones joined by a 1-handle and is simply connected. Its boundary is the corresponding Klein bottle. The two constructions therefore give the same quotient of \(\pi_1(E)\) by the peripheral groups, and both have exactly \(2k\) cone points. \(\square\)

## Exact cone count for high-rank free abelian groups

**Corollary.** Let \(c(\Gamma)\) be the smallest positive number of projective-plane cone points in a realization. It is unchanged by restricting to underlying spaces of compact hyperbolic 3-orbifolds. For \(n=3\) and every \(n\ge5\) one has

\[
c(\mathbb Z^n)=(n-1)(n-2).
\]

For \(n=4\), one has \(6\le c(\mathbb Z^4)\le 8\).

**Proof.** Theorem 2 gives equality of the topological and hyperbolic minima, and Theorem 1 gives \(c(\mathbb Z^n)\ge2\bigl(\binom n2-n+1\bigr)\). Let \(n=2g+1\) be odd with \(g\ge1\), and use the closed manifold \(\Sigma_g\times S^1\), where \(\Sigma_g\) is the closed orientable genus-\(g\) surface. Its standard group presentation uses \(n\) generators \(x_1,y_1,\dots,x_g,y_g,z\). It enforces the \(n-1\) commutators involving \(z\) and the surface relation \(\prod_{i=1}^g[x_i,y_i]=1\). Impose every remaining pair commutator except \([x_1,y_1]\), which then follows from the surface relation. The resulting group is \(\mathbb Z^n\), with exactly \(\binom n2-n\) added relators. For even \(n\ge6\), write \(n=3+(n-3)\) and take the connected sum of the two corresponding odd-rank manifolds. Impose the indicated commutators in each block and every cross-block commutator. The total number of added relators is again \(\binom n2-n\). Applying the version of Theorem 2 for a closed manifold group gives the matching upper bound. For \(n=4\), start with \(T^3\#(S^2\times S^1)\) and impose the three cross commutators. \(\square\)

For any closed connected 3-manifold group one has \(c(\Gamma)=2\). Take the connected sum of the manifold with the suspension of \(\mathbb{RP}^2\) at regular balls. The suspension is simply connected and has two cone points. The connected sum preserves the group by van Kampen. More generally, connected summing with this suspension adds two cone points while preserving the fundamental group.

The hyperbolic claims count the nonmanifold points of the underlying topological space. They allow the indicated rotational axes and stronger endpoint isotropy. The elementary negative answer in Theorem 1 requires no hyperbolic or orbifold hypotheses. The proofs are informal and use the cited published topology and holonomy theorems.
