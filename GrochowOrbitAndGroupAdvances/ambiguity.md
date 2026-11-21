# Exponentially many groups with identical marginal orbit Gram graphs

For each integer \(b\ge2\) let \(r=(3^b-1)/2\). There are at least
\[
\frac{2^r}{|\operatorname{GL}_b(\mathbb F_3)|}
\]
pairwise nonisomorphic finite groups with faithful orthogonal actions on the same \(\mathbb R^{36r}\) and identical orbit Gram graphs at every common seed. Consequently for all sufficiently large \(d\) a single \(\mathbb R^d\) admits \(2^{\Omega(d)}\) such groups. This also gives ambiguity for any collection of within-orbit Gram graphs, even with the seed of each graph supplied. It uses the nine-point configuration in [the counterexample](invariants.md). [Mixon–Vose, Conjecture 2.7 and Theorem 2.12](https://arxiv.org/pdf/2411.17434#page=6)

## Construction and preserved observations

Use \(N\), \(B\), \(q\), \(\theta\), the Hermitian space \(W\), and the chiral projective configuration \(S\) from the counterexample. Put \(Q=\mathbb F_3^b\). Take exactly one nonzero linear form \(\chi_i\) on each of the \(r\) projective points of \(Q^\vee\). For each choice \(\epsilon_i\in\{1,-1\}\), let \(\lambda_i=\epsilon_i\chi_i\) and set
\[
G_\epsilon=\{(g_1,\ldots,g_r)\in B^r\mid \exists t\in Q,\ q(g_i)=\lambda_i(t)\text{ for all }i\}.
\]
The linear forms span \(Q^\vee\), so the displayed \(t\) is unique. The map to \(Q\) is surjective, with kernel \(N^r\), and the latter is the unique Sylow \(2\)-subgroup. The quotient acts on the \(i\)-th copy of \(U=N/Z(N)=\mathbb F_4^4\) by \(\omega^{\lambda_i(t)}\). This follows using the coordinate lift \(s_{\rm diag}^{\lambda_i(t)}\), with inner actions on \(N/Z(N)\) trivial.

All \(G_\epsilon\) act faithfully by coordinatewise left multiplication on \((\mathbb H^9)^r\). For two sign choices take the bijection that inverts \(g_i\) precisely when the two signs disagree at \(i\). It preserves every orbit inner product at each fixed common seed by the quaternion coordinate identity from the counterexample. In particular it preserves zero distances, so it gives a Gram-graph isomorphism also at seeds with nontrivial stabilizer.

## Identifying the blocks before comparing orientations

An abstract isomorphism \(G_\epsilon\to G_\eta\) takes the characteristic Sylow \(2\)-subgroup and its center to their counterparts. It induces binary linear isomorphisms on both, modulo the center in the case of the Sylow subgroup, and intertwines their square maps. Each copy of \(U\) has an intrinsic family of \(2\)-dimensional binary subspaces in \(U^\vee\) obtained as follows. In the space of quadratic forms produced by dualizing the square map, take every form whose polar form has binary rank \(2\). To such a form attach the annihilator of its polar radical, viewed inside the binary dual. For \(N\) these are exactly the subspaces
\[
L_v=\{x\mapsto \operatorname{Tr}_{4/2}(a v^*x):a\in\mathbb F_4\},\qquad [v]\in S .
\]
Indeed the polar rank is twice the Hermitian matrix rank, the rank-one matrices are precisely the \(vv^*\) from \(S\), and the radical of the corresponding form is the kernel of \(v^*\). The same construction on \(N^r\) gives the disjoint union of these families in the \(r\) dual summands. A block diagonal matrix of rank \(1\) has exactly one rank-one block.

A subset of this family is declared independent when the dimension of the sum of its binary subspaces is twice the number in the subset. The trace pairing identifies each binary dual with the underlying binary space of the \(\mathbb F_4\)-dual, and this criterion is exactly linear matroid independence of the projective points. The components of that matroid are the \(r\) copies of \(S\), because each copy is connected and the copies are in direct sum. Thus a binary linear isomorphism preserving the square maps permutes the spans of these dual families. By duality it also permutes the original summands of \(N^r/Z(N^r)\). On each summand it gives a binary linear isomorphism \(L\colon U\to U\) preserving the intrinsic space of quadratic forms by pullback.

## Isomorphism classes

Let \(T\in\operatorname{GL}(Q)\) be the map on the order-three quotient and let \(j\) be the target summand for \(i\). Put \(\nu_j=\eta_j\chi_j\). The summand map \(L\) intertwines multiplication by \(\omega^{\lambda_i(t)}\) with multiplication by \(\omega^{\nu_j(Tt)}\) for every \(t\in Q\). Invertibility of \(L\) gives equality of the kernels of the two nonzero linear forms. Consequently \(\nu_j\circ T=\lambda_i\) or \(-\lambda_i\). The negative case makes \(L\) Frobenius-semilinear, since \(L(\omega x)=\bar\omega L(x)\) and \(L\) is binary linear. Its pullback of forms of polar rank \(2\) would induce a Frobenius-semilinear permutation of the marked projective points. More explicitly, writing \(L(x)=M\bar x\), precomposition sends \(x\mapsto|\!v^*x\!|_{\mathbb F_4/\mathbb F_2}\) to the norm of the linear functional represented by \(\overline{M^*v}\), using invariance of the norm under field conjugation. This contradicts the nine-point result. Hence \(\nu_j\circ T=\lambda_i\) for every \(i\).

Conversely if one such \(T\) carries the two sets of oriented linear forms to each other, permuting the \(B\)-coordinates gives an abstract isomorphism of their groups. Thus the isomorphism classes are exactly the orbits of the \(2^r\) oriented sets of linear forms under \(\operatorname{GL}(Q)\). The order of this group is less than \(3^{b^2}\). For large \(b\), \(2^r/3^{b^2}\ge2^{r/2}\). For any sufficiently large \(d\), choose \(b\) maximal with \(36r\le d\) and add trivial real coordinates. Since \(r_{b+1}=3r_b+1\), this still gives \(r=\Omega(d)\). Adding trivial coordinates preserves faithfulness and adds the same constant to every Gram entry on both sides. This proves the asserted exponential ambiguity.

The argument is a written proof. The nine-point finite calculations have an accompanying independent certificate.
