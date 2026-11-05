# ONE BALANCED QUARTIC TENSOR IS TOCI-COMPLETE

A closed-tag construction for all three concrete cases of Lysikov--Walter Question I.12.
Informal proof, November 4, 2026. No Lean verification or publication-priority claim.

THEOREM
Over the complex orbit-closure model and efficiently represented coefficient subfields of Lysikov--Walter, each of the following fixed tensor sequence problems is TOCI-complete under their efficient algebraic reductions:

  OCI(End(W tensor W); GL(W)),
  OCI(End(W tensor W) directsum End(W); GL(W)),
  OCI(End(W tensor W tensor W); GL(W)).

These are exactly the three concrete balanced cases in Question I.12, with the canonical identification End(W^tensor a)=W^tensor a tensor (W*)^tensor a. The first reduction doubles the underlying vector-space dimension and is affine-linear in the tensor data. It preserves and reflects ordinary orbit equality, orbit closure intersection, and orbit closure containment. The TOCI-completeness conclusion concerns orbit closure intersection.

The broader question about ALL tensor tuple sequences, including unbalanced and product-group actions, is not answered by this theorem. No unrestricted TI versus TI_SL conclusion is asserted.

1. SOURCE PROBLEM AND EXACT MODEL

Theorem V.12(2) of Lysikov and Walter, arXiv:2411.04639v2, gives TOCI-completeness for two labelled copies of End(V tensor V) under one GL(V), acting on each by conjugation with h tensor h. The source representation is X=End(V tensor V)^2, V=C^n, and H_0=GL(V).

Definition III.3 requires a uniform sequence of polynomial maps, with polynomially bounded output parameter, defined over the coefficient subfield F of C, efficiently evaluable on F-coordinates, preserving and reflecting closure equivalence for ALL complex points. The reduction below meets that stronger complex-point condition. Group elements and Zariski orbit closures are taken over C; the coefficient subfield is the input representation, not a restriction to F-rational transporters.

Primary source:
https://arxiv.org/html/2411.04639v2
Question I.12, Theorem I.2, Definitions II.4 / III.2 / III.3 / IV.21, Theorem V.12(2).

2. THE AFFINE ENCODING AND ITS RETRIEVABLE TAGS

For n>=1 let W=C^2 tensor V, N=2n, G=GL(W), and Y=End(W tensor W). Let E_ab be the usual 2 by 2 matrix units. Write

 P_0=(E_11-E_22) tensor I_V,
 Q_0=(E_12+E_21) tensor I_V,
 Z_0=(P_0 tensor I_W + I_W tensor Q_0)/N.

Let L be the fixed shuffle W tensor W -> (C^2 tensor C^2) tensor (V tensor V), sending (c tensor v) tensor (c' tensor v') to (c tensor c') tensor (v tensor v'). Define

 Phi(R_1,R_2)=Z_0
   + L^-1[(E_12 tensor E_12) tensor R_1]L
   + L^-1[(E_21 tensor E_21) tensor R_2]L.                   (2.1)

The first data channel maps color (2,2) to color (1,1), and the second maps (1,1) to (2,2). The channels are disjoint and neither overlaps the constant tag terms. Thus Phi is injective, and its inverse on its affine image reads the two corresponding matrix blocks.

For arbitrary Z in Y put P(Z)=Tr_2 Z and Q(Z)=Tr_1 Z, the unnormalized partial traces over the second and first W factors respectively. Both maps are equivariant from conjugation by g tensor g to conjugation by g. This follows on elementary operators A tensor B from Tr_2(A tensor B)=A Tr(B), Tr_1(A tensor B)=Tr(A) B, and invariance of ordinary trace under conjugation; extend linearly.

The two data channels have zero partial trace over either factor. For example expand R_1 as a sum of elementary A tensor B on V tensor V: after undoing the shuffle, each contribution is (E_12 tensor A) tensor (E_12 tensor B), whose partial traces vanish because Tr(E_12)=0. The other channel is the same with E_21. Also Tr(P_0)=Tr(Q_0)=0, so

                  P(Phi(R_1,R_2))=P_0,
                  Q(Phi(R_1,R_2))=Q_0.                    (2.2)

The simultaneous centralizer of P_0,Q_0 in G consists exactly of I_2 tensor h with h in H_0: commuting with P_0 forces a block diagonal matrix diag(h_1,h_2), and commuting with Q_0 forces h_1=h_2. Denote this subgroup by H, identified with H_0. It fixes Z_0 and acts on the two channels by the original conjugations with h tensor h. Hence Phi is H-equivariant under this identification.

Equations (2.2) already prove ordinary orbit reflection: any g carrying Phi(x) to Phi(y) must centralize both tags and therefore lie in H. This alone would NOT prove closure reflection. The next sections address that missing boundary argument.

3. THE TAG ORBIT IS CLOSED, WITH EXPLICIT LOCAL FRAMES

Let B be the subset of End(W)^2 cut out by

           P^2=I_W,  Q^2=I_W,  PQ+QP=0.                   (3.1)

This is closed. Every pair in B is simultaneously conjugate to (P_0,Q_0). Indeed P is diagonalizable with eigenvalues +1 and -1, and Q interchanges its two eigenspaces because PQ=-QP. Since Q^2=I, the interchange is a linear isomorphism, so both eigenspaces have dimension n. Given a basis u_1,...,u_n of the +1 eigenspace, the vectors Qu_1,...,Qu_n form a basis of the -1 eigenspace. The matrix with those two ordered column blocks conjugates the standard tags to P,Q. This also proves Tr(P)=Tr(Q)=0. In particular B is precisely a single CLOSED G orbit, not an open orbit that could develop degenerate tags.

We need a regular local version of the basis choice. Write E_+(P)=(I_W+P)/2. It has rank n on B. For each fixed choice of n columns and n rows, take the open subset U of B where that minor of E_+(P) is nonzero. These charts cover B. The chosen columns u_i=E_+(P)e_{j_i} then form a basis of the +1 eigenspace for every point of U. Put

                    s(P,Q)=[u_1 ... u_n | Qu_1 ... Qu_n].

Its entries are polynomial in P,Q and its determinant is nonzero throughout U. Thus s and s^-1 are regular on U, and s(P,Q) conjugates both standard tags to the given pair. No global section, rational limit of an unbounded conjugator, or choice of eigenbasis with discontinuous signs is assumed.

4. The closed ambient encoding space

For arbitrary Z in Y set (P,Q)=(Tr_2 Z,Tr_1 Z) and
D(Z)=Z-(P tensor I_W+I_W tensor Q)/N. Let S consist of points whose tags lie in B and which satisfy

                 D(Z)=F_+ D(Z) F_- + F_- D(Z) F_+,
                 F_±=((I_W ± P)/2) tensor ((I_W ± P)/2).

These are polynomial equations in the entries of Z, so S is closed in Y. They are covariant under simultaneous conjugation; hence S is G-stable. Every encoded point belongs to S.

The fiber of the tag map S→B over (P_0,Q_0) is exactly Φ(X). In this fiber the displayed projections are onto color subspaces 11 and 22. Therefore D(Z) is the sum of two arbitrary off-diagonal blocks between these subspaces and has no other blocks. These two blocks are exactly the two elements of End(V tensor V) that define Φ. Conversely arbitrary blocks have zero partial traces, by Section 2, so there is no additional condition in this fiber. The inverse Φ^(-1) there is the regular map reading these two blocks. By the equivariance of the tag map and transitivity on B, every other fiber is a translate of this one.

Fix a chart U from Section 3. Writing S_U for the inverse image of U, the map

                 U × X → S_U,    (b,x) ↦ s(b)·Φ(x)

is an isomorphism of varieties. Its regular inverse sends Z to (b,Φ^(-1)(s(b)^(-1)·Z)), where b is its tag pair. Indeed the conjugated point lies in the standard fiber and the formula for its inverse holds by the fiber description.

5. Exact reflection of all orbit degenerations

The chart identifies (G·Φ(x)) intersect S_U with U × (H·x). For the forward direction write b for the tags of g·Φ(x); then s(b)^(-1)g stabilizes both standard tags and therefore belongs to H. Conversely every point of U × (H·x) arises from s(b)h acting on Φ(x).

The closure of G·Φ(x) in Y is contained in the closed S. Taking its intersection with the open S_U is the same as taking the closure in S_U of the corresponding orbit piece. In the chart the resulting subset is exactly

                      U × closure_X(H·x).

One inclusion holds because the right-hand side is closed in U × X and contains the orbit piece. The reverse holds on each fixed b fiber, where the closure of {b} × (H·x) is {b} × closure_X(H·x). Thus every possible target degeneration, over every tag point, is accounted for.

If two source orbit closures meet at u, the two target orbit closures meet at Φ(u). If two target orbit closures meet at Z, take a chart U containing the tags of Z. Its X-coordinate lies in both source orbit closures. This proves the required biconditional for all complex points. The formula also reflects orbit-closure containment; the same argument works with inclusion in place of intersection. No appeal to an invariant generator bound, numerical matrix decompositions, or effectiveness of an algebraic degeneration is needed.

6. Uniform reduction and the other two balanced cases

The affine map Φ is defined over the rationals, hence over any coefficient subfield F of C allowed by the paper. Its target dimension parameter is 2n. In the fixed bases its (2n)^4 output coordinates are source coordinates or constants from {0,1/(2n),-1/(2n)}: the affine tag terms have zero entries in the two data channels. The map can therefore be evaluated by scanning the dense output coordinates and copying entries or emitting these constants. The rational constants have O(log(n+1)) bits, and the map has polynomial evaluation cost under the paper's efficiently encoded field convention. The proof of correctness concerns all complex inputs, independently of that field convention. The construction includes n=1. If the convention for the parameter includes n=0, the zero-dimensional source has just one point; send it to Φ for n=1 evaluated on its zero pair, with q(0)=2.

To add the matrix summand use the equivariant linear embedding Z ↦ (Z,0). To reach the balanced sextic use Z ↦ Z tensor I_W, under the endomorphism identification. Its equivariant linear left inverse on the ambient sextic space is the partial trace over the third W, divided by N. The first embedding has the first-coordinate projection as left inverse. In each case the embedding is a homeomorphism to its closed linear image and maps the entire orbit onto the orbit of the image. Hence it preserves and reflects closure intersection. Both maps are polynomial-time in the same encodings (the sextic has (2n)^6 entries). TOCI membership of all three targets follows from Definition IV.21, since they are fixed tensor tuple types. By Theorem V.12(2) and composition these three targets are TOCI-complete.

7. Further exact scope

For any fixed one-group tuple of balanced mixed tensors, if a summand has at least two covariant and two contravariant factors, the same identity-padding embedding in that summand, with all others zero, proves TOCI-completeness. If every summand is a scalar or an endomorphism, the scalar coordinates are unchanged by the action and the endomorphism coordinates give simultaneous matrix conjugation; the latter orbit-closure problem is in P as recalled in Section I of the source paper. This yields the proposed alternative for fixed balanced one-group tuples. It does not establish the entire Question I.12 alternative for arbitrary tensor tuple actions.

For each of these balanced one-group actions over C, scalar matrices act trivially. Given any g in GL(W), choose a scalar λ with λ^N det(g)=1. The action of λg in SL(W) is exactly the action of g. Thus the GL and SL orbits, and their closures, coincide pointwise in these balanced cases. This does not identify GL and SL orbits on pure covariant tensors, nor over the rational points of the input field, and makes no claim about those other reduction problems.

Primary reference: Vladimir Lysikov and Michael Walter, "Complexity theory of orbit closure intersection for tensors: reductions, completeness, and graph isomorphism hardness", arXiv:2411.04639v2, https://arxiv.org/html/2411.04639v2. Relevant locations: Question I.12, Definitions III.2–III.3 and IV.21, and Theorem V.12(2). The two-copy completeness theorem is theirs. Our contribution here is the explicit two-tag compression and proof of closure reflection. Informal proof; no Lean certificate or publication-priority assertion.
