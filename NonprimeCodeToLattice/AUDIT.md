# Independent AI-Worker Audit of Field Descent and Lattice Encoding

**Status:** AI-assisted informal proof; separate AI-worker review and exact finite checks where supplied. No Lean certificate; independent human review and publication-priority assessment remain pending.

Date: 2026-10-31
Status: full informal reduction proved. No Lean verification and no novelty priority claim.
Construction proposed by the parent worker; this file records an independent proof audit and a direct lattice simplification.

## Target And Source

Cheraghchi, Shagrithaya, Veliche, Reductions Between Code Equivalence Problems, arXiv:2502.07916v1, Section 1 explicitly identifies extending CE-to-LIP reductions to nonprime fields as open:
https://arxiv.org/html/2502.07916v1
The same paper separately asks for replacing poly(n,q) closure costs by poly(n,log q), so these are distinct targets.
The July 2026 survey, arXiv:2607.12870v2, Section 4.4, still identifies the prime-field restriction:
https://arxiv.org/html/2607.12870v2

Exact achieved statement: for every prime power q = p^s, with the field explicitly represented, linear/monomial equivalence of linear codes over F_q reduces to ordinary Euclidean lattice isomorphism by a deterministic many-one construction of bit cost polynomial in n,k,q. For each fixed q this is polynomial in the usual code-input length. The construction also recovers a monomial equivalence from any explicit lattice isometry. It does not establish the separate uniform poly(n,k,log q) target.

## The Field-Descent Frame

Consider two full-row-rank k by n generators G,G' over F_q, with no zero columns; write their columns g_i,g'_i. Zero columns can first be counted and removed. Unequal counts or ranks are NO instances, represented by fixed nonisomorphic lattices. Rank-zero inputs are direct YES cases.

Assume s > 1 and choose alpha with F_p[alpha] = F_q. Such an alpha is nonzero and different from 1. The polynomial-basis generator works in the usual irreducible-polynomial representation. More generally enumeration and checking the degree gives a deterministic poly(q) procedure, within the claimed complexity.

Set U = F_q^k and Y = F_q^n with coordinate basis e_i. Regard V = U direct_sum Y as an F_p-space of dimension R = s(k+n), using fixed F_p coordinates Gamma. For every i form four F_q-lines:
 X_i = {(g_i a,0): a in F_q},
 Y_i = {(0,a e_i): a in F_q},
 Z_i = {(g_i a,a e_i): a in F_q},
 W_i = {(alpha g_i a,a e_i): a in F_q}.

Make an F_p-generator H(G) whose columns are Gamma of all nonzero vectors of each line, with multiplicity 1 for X_i, n+1 for Y_i, n+2 for Z_i, n+3 for W_i. Construct H(G') identically.

All cross-role intersections are zero: the Y projection separates distinct i, X has zero Y projection, Y has zero U projection, and Z_i intersect W_i only at zero because alpha != 1 and g_i != 0. Only the X_i may coincide with each other. Therefore each actual nonzero X-vector has multiplicity at most n; Y,Z,W vectors have respectively n+1,n+2,n+3 copies. Ordinary permutation equivalence of these p-ary codes forces preservation of the four roles by actual-vector multiplicity.

The columns span V over F_p: the X columns span U because G has rank k over F_q, and the Y columns span Y. Thus H has full row rank R. Its length is
 L = n(q-1)(3n+7).

## Soundness Of Field Descent

Suppose H(G),H(G') are permutation equivalent. Since both have full row rank, this means an invertible F_p-linear map S takes one column multiset to the other. Role preservation and spans force S(U)=U and S(Y)=Y. Hence S = A direct_sum B, with no off-diagonal blocks.

Elementary direct-sum union lemma. If E_1,...,E_n are nonzero independent additive subspaces, then every additive subspace contained in their union lies in one E_i. Otherwise vectors from two distinct E_i have a sum outside the union. Thus the maximal nonzero additive subspaces in the union are exactly the E_i. This remains valid in characteristic two; it does not rely on the false general assertion that a vector space cannot be a finite union of proper subspaces.

Apply the lemma to the independent subspaces Y_i. Their image permutation gives pi and invertible F_p-linear maps B_i:F_q->F_q with
 B(a e_i) = B_i(a)e_pi(i).
Apply the lemma separately to the Z_i; their independence follows from their independent Y projections. The image of each Z_i has Y projection Y'_pi(i), so its target index must be pi(i), not a new permutation. Therefore
 A(g_i a) = g'_pi(i) B_i(a)                       (1)
for every a. The same argument for W gives
 A(alpha g_i a) = alpha g'_pi(i) B_i(a).          (2)
Using (1) at alpha a and comparing with (2), and using g'_pi(i) != 0, proves
 B_i(alpha a) = alpha B_i(a).
Since B_i is F_p-linear and F_p[alpha]=F_q, it commutes with multiplication by every field element. Hence B_i(a)=d_i a, where d_i=B_i(1) is nonzero. Equation (1) becomes
 A(g_i a)=d_i g'_pi(i) a.
As the g_i span U over F_q, every u is a sum of g_i a_i; additivity now proves A(cu)=cA(u) for every c in F_q. Thus A belongs to GL_k(F_q) and
 A g_i = d_i g'_pi(i).
This is exactly a monomial equivalence of the original codes, up to the conventional orientation of the coordinate scalars.

## Completeness

Conversely, given A in GL_k(F_q), a permutation pi and d_i != 0 with A g_i=d_i g'_pi(i), extend A on U by B(ae_i)=d_i a e_pi(i). This is an invertible F_q-linear map of U direct_sum Y, hence F_p-linear. It maps X_i,Y_i,Z_i,W_i onto the respective target lines and preserves every multiplicity. Thus it gives permutation equivalence of H(G),H(G').

This proves full equivalence over every nonprime field. In prime fields no alpha constraint is needed: every additive map F_p->F_p is already multiplication by a scalar. The three families X,Y,Z suffice for all prime p, including p=2.

DIRECT LATTICE OUTPUT: NO PCE-TO-SPCE BLACK BOX NEEDED

The actual column multiset of H is centrally symmetric: for every vector v the multiplicity of v equals that of -v. This follows because each entire nonzero F_q-line is included with constant multiplicity. Any F_p-linear image has the same property.

Central symmetry lemma. For two full-row-rank matrices H,H' with centrally symmetric actual column multisets, signed permutation equivalence is the same as permutation equivalence. In odd characteristic, signed equivalence preserves the total multiplicity at the pair {v,-v}. Symmetry says both counts are half this total, forcing equality of the individual counts. In characteristic two signs are trivial. This argument works for arbitrary repeated columns and requires no projective-normalization choice.

Let t=p^2+1 and repeat EVERY column of H exactly t times, obtaining J. Repetition preserves the symmetry above, and its nonzero codewords have Hamming weight at least t. The original H and H' are permutation equivalent if and only if J and J' are signed permutation equivalent: the forward implication is direct, and the converse follows from the symmetry lemma followed by dividing all actual-vector multiplicities by t.

For the p-ary code C generated by J, output the Construction A lattice
 Lambda(C) = {z in Z^N: z mod p belongs to C},
where N=tL. An explicit integer basis is obtained by systematic form. After a column permutation J=[I_R | E], use rows of
 [ I_R  E ]
 [  0  pI ]
with E represented by integers in [0,p-1], then undo the column permutation. This requires only Gaussian elimination and integer arithmetic of polynomial bit size.

Every nonzero lattice vector whose reduction modulo p is zero has length at least p. The vectors of length exactly p in p Z^N are precisely +/-p e_j. If reduction is nonzero, its support is a nonzero codeword support, so its squared Euclidean length is at least its support size, which is at least t > p^2. Thus the shortest nonzero lattice vectors are EXACTLY +/-p e_j.

Any orthogonal isomorphism between the two output lattices must permute these shortest vectors. Hence it is a signed coordinate permutation. Reduction modulo p gives signed permutation equivalence of J,J', and the preceding symmetry/repetition argument yields permutation equivalence of H,H'. Field-descent soundness yields original F_q monomial equivalence. Conversely any original monomial equivalence induces a permutation equivalence of J,J', which is an integer orthogonal equivalence of their Construction A lattices.

This proves the final lattice equivalence directly. It is the standard shortest-vector argument underlying the published prime-field SPCE-to-LIP construction, with the minimum-distance promise supplied explicitly rather than assumed.

## Size, Field Cost, And Witness Recovery

For s>1, N=(p^2+1)n(q-1)(3n+7)=O(n^2 q p^2), hence O(n^2 q^3). Lattice rank is N; a dense basis has O(N^2 log p) bits. The field-descent rank R=s(k+n), the vector enumeration, and the final systematic basis construction all have cost polynomial in n,k,q. There is no hidden vector search of size q^k, no primitive-element oracle, and no discrete-logarithm step.

Given an explicit orthogonal lattice isometry, it is a signed coordinate permutation by the shortest-vector characterization. Reduce modulo p and solve the full-row-rank generator equation to recover an F_p row map S. The symmetry/repetition argument ensures S maps the original H multisets exactly. Read its Y block, identify pi from its independent coordinate subspaces, read d_i=B_i(1), and read the U block as the F_q-linear A established above. All recovery costs are polynomial in the output size.

## Source And Novelty Limits

The cited 2025 paper Corollary 1.3 states an unconditional prime-field PCE-to-LIP reduction. The 2026 survey Theorem 20 presents the prime-field SPCE-to-LIP theorem with an explicit distance >=p^2+1 hypothesis. Our final construction does not depend on reconciling any parameter accounting in that corollary: it supplies distance by t-fold repetition and proves the lattice statement directly, at the deliberately stated poly(n,k,q) cost.

The Construction A and shortest-vector pieces are established prior machinery (Bennett-Win 2024, as credited by Cheraghchi et al and the survey). The proposed contribution is the four-family field-descent frame that forces all coordinatewise F_p-linear maps to commute with a full field generator, together with its direct composition to lattices. Novelty of that field-descent gadget has not been established by this audit. No claim of an unconditional new literature-first result is made.

Audit verdict: no hidden block-mixing, finite-union, characteristic-two, zero-column, or distance-promise gap remains in the construction as stated here. It supplies the full nonprime-field reduction direction at polynomial alphabet-size cost, while leaving the separate polylog(q) uniformity problem untouched.
