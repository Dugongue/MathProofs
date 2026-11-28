# Bounded infinitesimal probes cannot detect integral homotopy extension

Fix \(M\ge 1\). There exist a single finite simply connected simplicial pair \((K,A)\) of dimension at most four, a single finite integral target \(Y\), and boundary maps \(f_e:A\to Y\) for \(e\in\mathbb N\) with these properties.

1. Only one degree coordinate of \(f_e\) varies. The integral extension problem for \(f_e\) is computably enumerable complete as a problem in \(e\).
2. For every finite product \(R=\prod_i R_i\) of commutative local rings whose maximal ideals satisfy \(\mathfrak m_i^M=0\), the set of relative extension classes to the coefficient target \(Y_R\) is naturally \(R^N\), for one fixed \(N\) and every \(e\). This includes every field and every finite ring of bounded nilpotence order. The identification is natural for all ring maps within this class.
3. Every instance comes with the same two solution-coordinate tuples over \(\mathbb Z[1/2]\) and over \(\mathbb Z[1/3]\), respectively. In particular it has a compatible profinite solution, with an explicit point over \(\widehat{\mathbb Z}\) inducing compatible points over every \(\mathbb Z/n\).
4. For any allowed \(R\), the full relative mapping space to the coefficient-natural \(3\)-type \(Y_R\) is weakly equivalent to a disjoint union, indexed by \(R^N\), of \(K(H^2(K,A;R),1)\). Thus the same indistinguishability holds for all homotopy groups of each of those relative mapping spaces. The weak equivalence is asserted separately for each \(R\); assertion 2 is the natural identification across \(R\).

The integer \(M\) is fixed before constructing the pair. For fixed finite rings the coefficient target has a finite comparison model for the relative homotopy **classes**. Assertion 4 uses the \(3\)-type itself.

## An affine construction

Let \(F(e,x)\in\mathbb Z[e,x_1,\ldots,x_n]\) be a fixed Diophantine polynomial such that \(\exists x\in\mathbb Z^n,\ F(e,x)=0\) holds exactly when the machine of index \(e\) halts. Such a polynomial follows from DPRM, converting natural-number witnesses to integer witnesses using four squares. Put \(N=n+3\), and set
\[
G(e,x,z,t,u)=z^2(F(e,x)^2+u^2)+(z-1)^2+t^2,\qquad
H=(u^2+2)G .
\]
Over \(\mathbb A^N_\mathbb Z\), define \(S_e\) to be the disjoint union of the closed subscheme \(H^M=0\) and the principal open \(D(H)\). This is affine and has a fixed finite-presentation template in \(e\). For instance introduce an idempotent \(b\) and an inverse witness \(w\), impose
\[
b^2=b,\quad bH^M=0,\quad (1-b)(wH-1)=0,\quad bw=0.
\]
The closed piece has \(b=1,w=0\) and the open piece has \(b=0,w=H^{-1}\). The other coordinates are \(x,z,t,u\).

Over the integers the open piece has no point: the factor \(u^2+2\) is never a unit. On the closed piece the sum of squares gives \(z=1\), \(t=u=0\), and \(F(e,x)=0\). Thus \(S_e(\mathbb Z)\) is precisely the witness set for the universal polynomial, with no extra integral choices. Enumeration of possible \(x\) gives the computably enumerable upper bound.

For the local assertions, on any local ring in scope each value of \(H\) is either a unit or lies in the maximal ideal. In the first case there is a unique lift to the open piece and in the second case \(H^M=0\) gives a unique lift to the closed piece. In a finite product of such rings apply this to each factor using the corresponding idempotent. The projection \(S_e(R)\to R^N\) is therefore bijective. Since the projection is induced by a scheme map, these componentwise bijections and their inverses are natural even for maps between rings with different product decompositions.

The construction also preserves the motivic class. Over the parameter line, the reduction of the closed piece and the principal open are complementary strata of the affine space \(\mathbb A^N\). The scissor relation gives its affine-space class in the relative Grothendieck ring of reduced finite-type schemes. In particular the Hasse–Weil zeta function of every fiber at a finite field is that of affine \(N\)-space, as also follows from the field case of the point-functor bijection.

For the sections set \(x,z,t=0\). Then \(G=1\), independent of \(e\). Setting \(u=0\) gives \(H=2\), hence the open point with \(w=1/2\) over \(\mathbb Z[1/2]\). Setting \(u=1\) gives \(H=3\) and \(w=1/3\) over \(\mathbb Z[1/3]\). Take the first point at odd primes and the second at \(2\). Since solutions of polynomial equations commute with direct products of coefficient rings, this gives the asserted \(\widehat{\mathbb Z}\)-point and its compatible finite reductions. This conclusion has no depth restriction on the individual rings of the profinite system.

## Realization by one fixed pair

Use the cup-product construction for exact affine realization. Include a third marked \(2\)-sphere alongside the two constant anchor spheres, and prescribe its degrees \((e,0)\). It acts as the left coordinate copy for the parameter wire \(e\); add the usual unmarked right copy and the equality gate. Run the \(2\)-sphere wire and \(4\)-cell gate construction on the single presentation above with \(e\) as that parameter wire. Because both the universal polynomial and \(M\) are fixed, the finite pair stays fixed. The other marked coordinates have the standard constant values. Over each ring \(R\), the degree assignments satisfying the extensions are exactly \(S_e(R)\) in the sense of the exact affine realization. The homotopy class of the boundary can be represented by a degree-\(e\) map on the third sphere. A subdivision for a simplicial representative is allowed; it changes the presentation, not the source space. The finite integral comparison target from that theorem gives the same extension classes on this pair. [Exact affine realization](https://github.com/Dugongue/MathProofs/blob/main/Top10CrossoverProofs/UniversalRelativeMappingSchemes.md).

Finally work in the CW model, which relative to \(A\) has cells only in degrees two and four. Put \(B_R=K(R_{\mathrm{add}},2)^2\) and \(E_R=K(R_{\mathrm{add}},4)\), so \(Y_R\) is the homotopy fiber of the cup map \(B_R\to E_R\). In the simplicial cocycle model this cup map is zero on the two-dimensional boundary, where we may take the constant nullhomotopy. The space of extensions to \(B_R\) is weakly discrete, since all \(\pi_i\) for \(i>0\) are sums of \(H^{2-i}(K,A;R)\), which vanish. The space of extensions to \(E_R\) has in each component weak type \(K(H^2(K,A;R),2)\) because its only possibly nonzero positive group is \(\pi_2\), since \(H^3,H^1,H^0\) of the pair vanish. These formulas follow from representing relative cohomology on the suspension of \(K/A\). Any single extension translates its component to the zero one in the abelian cocycle model. The relative mapping space to \(Y_R\) is the homotopy fiber of the induced map of extension spaces, based at the constant map to \(E_R\). Over every allowable discrete base component it has the type of the loop space of the corresponding \(E_R\) component. Its components are indexed by \(S_e(R)\) and each has the weak type stated in assertion 4.

The fixed coprime-denominator witnesses build on the earlier integral local-promise construction. Here the additional assertions are simultaneous indistinguishability as point functors on all bounded-nilpotence local rings, exact integral witnesses, and the full relative mapping-space type on those probes. [Earlier coprime-denominator construction](https://github.com/Dugongue/MathProofs/blob/main/PortfolioTop30/ManinExtensions.md#4-integral-halting-completeness-with-two-supplied-rational-solutions).
