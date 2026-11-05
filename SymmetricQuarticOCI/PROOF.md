# TOCI-COMPLETENESS OF A SINGLE SYMMETRIC QUARTIC

Informal proof. No Lean verification or first-publication claim.

THEOREM. For W=C^m, the orbit closure intersection problem for the GL(W) action on

                    Sym^2(W) tensor Sym^2(W*)

is TOCI-complete under efficient algebraic reductions. This is one mixed tensor, symmetric in the two vector slots and independently in the two covector slots. The target has no separate marker components or promise about the input tensors. The reduction has m=4n and O(n^4) dense output coordinates.

This answers Lysikov--Walter Question I.14, and it implies completeness for the three explicit tensor spaces in their Question I.12. The more general dichotomy asked in I.12 is not proved here.

1. Source problem and colored data

By Lysikov--Walter Theorem V.12(2), the source is the TOCI-complete OCI problem for GL(V) acting diagonally on two copies of V^tensor2 tensor (V*)^tensor2, V=C^n. Write its data as (x_1,x_2). Take W=V^direct sum 4 and call the summands W_1,...,W_4. A color means the corresponding copy of V for a vector and its dual copy for a covector. Write P_a for the projection onto W_a and E_ba for the identity transfer W_a->W_b, zero on the other summands. These matrices commute with the diagonal embedding beta(g)=g^direct sum 4.

Let S be the unnormalized symmetrization of the two vector and the two covector slots independently, the sum of four permutations. We use its image in the full mixed tensor space as the model of the symmetric mixed space, canonically isomorphic over C to Sym^2(W) tensor Sym^2(W*). Embed x_1 at the ordered color signature (1,2 ; 3,4), and x_2 at (1,3 ; 2,4), then symmetrize each. Let Z(x_1,x_2) be their sum. The two signatures have different unordered vector/covector color sets, so their symmetrized supports do not intersect. Each ordered component recovers exactly its original data, with no multiplicity: the colors on each side differ. Each block has disjoint vector and covector color sets. All these maps are beta-equivariant.

Let tau be the partial trace pairing the second vector slot with the second covector slot, leaving the first slots as an element of End(W). This linear map is GL(W)-equivariant. Since the vector and covector colors in each data block are disjoint, tau(Z)=0.

2. Two kinds of internal marker coefficients

For each a define H_a=S(P_a tensor P_a), rearranging the endomorphism slots to the mixed tensor order before symmetrization. Directly,

                      tau(H_a)=2(n+1) P_a.                   (1)

Indeed the unswapped and doubly swapped terms each contribute tr(P_a) P_a=n P_a. Each term that swaps exactly one side contributes P_a^2=P_a.

For every ordered pair a!=b choose c_ab,d_ab to be the two colors in {1,2,3,4} other than a,b, in increasing order. For c distinct from a,b set

                   M_(b,a;c)=S(E_ba tensor P_c).

Its unordered vector colors are {b,c} and unordered covector colors are {a,c}. These sets intersect in exactly c. In the partial trace only its ordered component (b,c ; a,c) contributes: in each of the other three arrangements the second vector and covector colors differ. The contribution is tr(P_c) E_ba = n E_ba. Thus

                 tau(M_(b,a;c)) = n E_ba,                    (2)

and the same identity holds after projection to this ordered component. In particular the difference for c_ab and d_ab has zero partial trace.

For n>=1 form the single tensor

 T(x_1,x_2) = Z(x_1,x_2) + sum_a [a/(2(n+1))] H_a
             + sum_(a!=b) [M_(b,a;c_ab)-M_(b,a;d_ab)]/n.      (3)

Every marker is beta-invariant, since it is constructed from commuting color transfers and projections. So T is an affine beta-equivariant map, and it preserves OCI by continuity. Equations (1)--(2) imply

                      tau(T(x_1,x_2)) = sum_a a P_a = D.     (4)

3. Polynomial recovery of the transfers

For any target tensor Y define

 U_a(Y)=product_(e=1,...,4, e!=a) (tau(Y)-e I)/(a-e).

These are polynomial maps equivariant for conjugation, with rational coefficients and no input-dependent denominator. Equation (4) gives U_a(T)=P_a.

For a=b put Q_aa(Y)=U_a(Y). For a!=b and c=c_ab, project Y by U_b(Y),U_c(Y) in its first and second vector slots, and precompose its first and second covector slots with U_a(Y),U_c(Y). Define Q_ba(Y) as tau of the result. This is again a polynomial covariant for conjugation. Precomposing a covector with a matrix is a linear operation, with no matrix inverse. Covariance follows by cancellation of the g and g^(-1) factors on every pairing.

On Y=T(x_1,x_2), the projectors select the ordered color signature (b,c ; a,c). No data survives because the two variance color sets of each data block are disjoint. No H_a survives because it has only one color. In any M marker the common color of its two variance sets is its spectator, and the two remaining colors uniquely determine the ordered pair. Thus precisely the positive c_ab marker for (b,a) survives; the negative d_ab marker and all other pairs are excluded. By (2) and (3), its filtered trace is E_ba. Therefore

                       Q_ba(T(x_1,x_2))=E_ba                 (5)

for all a,b, including a=b. The total partial trace exposes the fixed color operator; the trace after color selection exposes the off-diagonal identity transfers. All of these operations are defined on the entire target module.

4. Reflection of OCI by lifting contractions

By Lysikov--Walter Lemma IV.26, every source invariant is a linear combination of complete contraction invariants. Such an invariant F uses any numbers of copies of the two labelled source blocks, pairing all vector slots bijectively with covector slots. For a copy of block 1 use port colors (1,2 ; 3,4); for a copy of block 2 use (1,3 ; 2,4). To define a polynomial F_hat on the single target module, replace every source copy by the same target variable Y. On an edge from a vector port of color a to a covector port of color b, contract w,ell as ell(Q_ba(Y)w). This is GL(W)-invariant because each Q_ba is a conjugation covariant and evaluation is natural. This construction also permits edges within a copy, edges between different blocks, and a=b on a cross-block edge.

After substituting Y=T(x_1,x_2), (5) requires exactly the specified color at each vector and each covector port. Every port belongs to an edge, so in each copy only its prescribed ordered signature can contribute. This eliminates every internal marker because all markers have a common color between vector and covector sets, whereas each data signature has none. The two data blocks have different unordered signatures, so for each copy the surviving component is the chosen block, with multiplicity one. The identity transfer E_ba contracts exactly the original V* with V, even when a=b. Consequently

                          F_hat(T(x_1,x_2))=F(x_1,x_2).       (6)

Thus every source invariant extends to a target invariant on the whole single symmetric module. Intersecting target orbit closures force equality of every target invariant, hence by (6) equality of every source invariant. Reductive invariant separation over C (Lysikov--Walter Theorem II.7) forces intersection of the source closures. This proves reflection for all input pairs, including nonclosed data orbits. No inference from ordinary orbit equality alone is used.

5. Efficiency, target membership, and the stated questions

The map (3) is affine with rational coefficients, and the dimension substitution is m=4n. There are binom(4n+1,2)^2 target entries. Every data coordinate is copied a bounded number of times, and a marker uses at most n^2 elementary terms followed by four permutations. Denominators in (3) have O(log(n+1)) bits. Passing to symmetric monomial coordinates uses only fixed-degree rational factors. This gives a polynomial-bit-time map in the coefficient encoding of Definition III.3. The separating polynomials are used only for correctness; they are not computed by the reduction. If n=0 is part of the size convention, its unique source pair can be sent to an identical fixed target pair.

The rational equivariant linear inclusion of the symmetric mixed space in W^tensor2 tensor (W*)^tensor2 is an OCI reduction. Its image is an invariant closed linear subspace, so its orbits and closures computed in the full module are exactly those in the image (Corollary III.8). This proves target membership in TOCI, which together with (3)--(6) and Theorem V.12(2) gives completeness. It answers the existential Question I.14 even with one mixed symmetric tensor.

The same inclusion proves TOCI-hardness of the single ordinary balanced quartic. Its equivariant injection x->(x,0) gives hardness of the balanced quartic plus End(W), and x->x tensor I_W, with slots reordered, gives hardness of the balanced sextic. These are all tensor tuple sequences, so membership is immediate. Hence all three explicit completeness questions in I.12 have affirmative answers, while its general dichotomy is untouched. No implication about unrestricted special-linear containment or TI versus TOCI is asserted.

PRIMARY CREDIT
Vladimir Lysikov and Michael Walter, Complexity theory of orbit closure intersection for tensors: reductions, completeness, and graph isomorphism hardness, FOCS 2025, arXiv:2411.04639v2:
https://arxiv.org/html/2411.04639v2
Relevant locations: Questions I.12 and I.14; Theorem II.7; Definition III.3; Lemma III.7 and Corollary III.8; Lemma IV.26; Theorem V.12(2). Their Lemma V.10 uses external shift/projection markers and lifts complete contractions. Classical partial traces, color-projector polynomials, and symmetric powers are credited ingredients. The present construction uses trace-cancelling internal spectator pairs to make all transfer matrices recoverable from one symmetric quartic. Companion drafts retain simpler larger-target reductions. No exact prior result was identified in the bounded status check, but first-publication priority is unestablished.
