# Determinant Coset Assembly for Tensor Direct Sums

MathProofs, AI-assisted informal proof, 4 November 2026.

Theorem. Fix a finite field F_q. There is a deterministic polynomial-time
truth-table reduction from arbitrary special-linear three-tensor isomorphism
over F_q to special-linear three-tensor isomorphism on concise tensors with
local centroid over the SAME field. All oracle questions are generated before
any answer is read. No ordinary TI oracle, transporter search, supplied flag,
isotypic ordering, or stabilizer generators are assumed. In fact the algorithm
computes the attainable determinant triples of the full GL transporter set.
For presented finite fields with varying q the same algorithm costs poly(L,q),
not polynomial in log(q), where L is the dense input bit length.

This closes the direct-sum/permutation assembly question for polynomial-time
Turing reductions at fixed q. If the primitive problem reduces to ordinary TI
at fixed q, so does the full problem by a polynomial-time Turing reduction.
This is not a many-one reduction to ordinary TI, and the primitive oracle is
still an SL-TI oracle. It does not settle unrestricted TI versus SL-TI.

1. Trim the three minimal supports and retain the required determinant data.

For T in V_1 tensor V_2 tensor V_3, let U_i(T) be the image of its mode-i
flattening (span of all contractions in the other modes). Then T belongs to
the product tensor of these supports and is concise there. They are computed
by Gaussian elimination. A GL transporter maps each U_i(T) onto U_i(S).
Unequal support dimensions give NO. Zero tensors are handled directly.

For a proper support in a mode, any invertible support map can be extended
to the ambient space with ANY prescribed nonzero determinant: choose any
complement isomorphism and rescale one complement coordinate. This is
independent in the three modes. For a full support, the determinant of the
support map, in original ambient coordinates, is compulsory. Thus we solve
the problem on concise support tensors with the determinant constraints
retained exactly in the original full-support modes. At the end, missing
modes contribute unrestricted F_q^* coordinates. This includes arbitrary
original deficiencies and does not require a choice of flag respected by an
unknown transporter.

2. Compute primitive blocks of the intrinsic centroid.

For a concise nonzero three-tensor T define its centroid C(T) to be triples
(a_1,a_2,a_3) of linear endomorphisms whose three single-mode actions on T
are equal. It is a vector space given by linear equations. Conciseness makes
each of its three coordinate projections injective: an endomorphism acting
as zero on T vanishes on every mode contraction and hence on the full mode.

The centroid is a commutative unital algebra under componentwise composition.
For a,b in C(T), write a_i T for their single-mode actions. Operators in
distinct modes commute. Thus

  a_1 b_1 T = a_1 b_3 T = b_3 a_1 T = b_3 a_2 T
              = a_2 b_3 T = a_2 b_2 T,
  a_1 b_1 T = a_1 b_2 T = b_2 a_1 T = b_2 a_2 T.

Injectivity in mode 2 shows a_2 b_2 = b_2 a_2. Cyclically all three
coordinates commute, and the equality of the three product actions proves
closure under multiplication. Identity endomorphisms give the unit. All
products and the multiplication table in a computed basis are explicit.

There is a direct deterministic primitive-idempotent algorithm at fixed q.
The map Phi(a)=a^q is F_q-linear on C(T) and can be evaluated on basis
elements by binary exponentiation. Compute E=ker(Phi-I). A finite-dimensional
commutative algebra modulo its nilpotent radical J is a product of finite
fields. On this quotient the fixed algebra is a product of copies of F_q,
one per local factor. The map E to that fixed algebra is injective because
a nilpotent element fixed by all iterates of Phi is zero. It is surjective:
lift a fixed residue x arbitrarily, then replace x by Phi^s(x), where q^s is
at least dim C(T). The difference x^q-x lies in J and its q^s power is zero;
thus the new lift is fixed and has the same residue. Consequently E is
isomorphic to F_q^k, and its primitive idempotents are exactly those of C(T)
(idempotents are automatically q-fixed and primitive factors lift uniquely).

To split E, begin with the idempotent 1. For each basis element b of E,
split each current idempotent e into the nonzero idempotents

             e_lambda = e (1 - (b-lambda 1)^(q-1)),   lambda in F_q.

In product coordinates this selects the entries of e on which b equals
lambda. The basis separates distinct product coordinates, so after every
basis element is processed the nonzero pieces are exactly the primitive
idempotents. The number of pieces is at most dim C(T). This costs polynomial
in L and q and does not rely on an assumed factoring or splitting oracle.

For a primitive centroid idempotent e_b, put U_(i,b)=e_(b,i) U_i. The three
orthogonal idempotent decompositions give

       T = directsum_b T_b,    T_b in U_(1,b) tensor U_(2,b) tensor U_(3,b).

Indeed applying distinct block idempotents in two modes kills T by the
centroid equality and orthogonality. The block supports are exactly the
indicated images, by conciseness and contraction, and each block is nonzero.
A centroid endomorphism of a block extends by zero on the other blocks,
so the centroid of T_b is e_b C(T), a local algebra. Choose explicit bases
of every image and compute the block tensors by linear algebra.

A transporter conjugates all three centroid actions, hence permutes the
primitive idempotents and induces block isomorphisms. Conversely every
bijection of blocks together with block GL transporters assembles into a
GL transporter of the direct sums. The block relation is intrinsic; no
computed block ordering is imposed as an isomorphism constraint.

3. Query every local determinant coset without a transporter.

Let T_b and S_c be the two block lists, in the chosen ordered bases. Put
D=(F_q^*)^3. For every pair of identical block formats and delta in D, form
S_(c,delta) by applying diag(delta_i^(-1),1,...,1) in mode i of S_c. The
primitive SL oracle on (T_b,S_(c,delta)) says YES exactly when delta is the
determinant triple of a block GL map from T_b to S_c. This follows by
composing an SL witness with the inverse of the applied scaling, in each
mode; conversely undo any GL map's determinant by the applied scaling.
All queries retain conciseness and local centroid. Incompatible formats
need no query and have empty determinant set.

Collect the YES triples as D_(b,c). Their nonemptiness gives the ordinary
GL block-isomorphism relation across the two lists. Every nontrivial
connected component of this bipartite graph is complete bipartite: edges
join objects of the same GL isomorphism type, and transitivity fills all
cross pairs in a component. Reject isolated vertices and components with
unequal side sizes. Otherwise choose any fixed bijection pi_0 within every
component. No additional oracle is needed, and all answers used here were
queried nonadaptively.

4. The exact determinant set for arbitrary matchings.

For each common isotype C choose a reference tensor U_C, ONLY for the
proof. Choose any GL maps r_b:T_b -> U_C and s_c:U_C -> S_c in the block
bases. Let H_C be the determinant image of Aut(U_C) in D. Then

       D_(b,c) = det(s_c) det(r_b) H_C.

Every block transporter is s_c h r_b with h in Aut(U_C), so this equality
holds even when H_C is not a direct product of three subgroups. For ANY
matching pi within these isotypes, the product of all D_(b,pi(b)) is the
same set as for pi_0: the r_b factors occur once each, the s_c factors
occur once each, and a nonempty product of copies of H_C is H_C. This uses
the joint determinant triples and loses no inter-mode correlation.

Let c_i be det(B_(S,i))/det(B_(T,i)), where B_(T,i),B_(S,i) are the square
change-of-basis matrices from concatenated block bases to the chosen
support coordinates. For the full-support modes these coordinates are the
original ambient coordinates. Let s_(0,i) be the sign of the coordinate
permutation sending the ordered source block bases to the target block
positions of pi_0 (preserving order inside each block). It can be computed
by inversions or by explicitly listing the permutation. For any isotype
C with at least two blocks on each side, let its mode sizes be d_(C,i) and
put epsilon_C=((−1)^d_(C,1),(−1)^d_(C,2),(−1)^d_(C,3)).

Swapping two target blocks of the same type has determinant (−1)^d_(C,i)
in mode i: it exchanges d_(C,i) pairs of basis positions. This is true
even when the blocks are separated by other blocks. Every permutation
within C is a product of transpositions, and odd and even permutations
are both possible exactly when its multiplicity is at least two. Choices
in distinct isotypes are independent. Thus the set of all permutation
sign triples relative to pi_0 is precisely the subgroup E_sign generated
by those epsilon_C. In characteristic two it is trivial.

It follows that the attainable support-coordinate determinant triples are
EXACTLY the finite set

      c * s_0 * (product_b D_(b,pi_0(b))) * E_sign.            (4.1)

Every factor in this product is genuinely attainable: choose a matching
giving the requested relative signs, and use the just-proved matching-
independence of its product of local cosets to obtain the requested local
determinant product. Conversely a transporter gives exactly such a
matching, block determinant product, and basis calibration. There is no
assumption that each individual block map is special linear.

5. Complexity and connection to TI versus SL-TI.

There are at most (#T blocks)(#S blocks)(q−1)^3 primitive oracle questions.
Their total dense size is polynomial in L and q. Products of subsets of
the finite group D are computed by ordinary enumeration, for example in
O(number of blocks times (q−1)^6) field operations. The sign subgroup has
at most 8 elements. All preprocessing, basis calibration and postprocessing
are deterministic, with polynomial bit cost at fixed q; no transporter or
block-aut generator is extracted from a decision answer. Test whether
some support triple in (4.1) is one in every compulsory mode, and then
apply the arbitrary-determinant extension on proper supports from Section 1.
Equivalently take (4.1) in the compulsory coordinates and allow all units
independently in the remaining ambient coordinates to recover the full
determinant set. This proves the theorem.

In particular if an ordinary-TI decision reduction is available for
concise centroid-local SL-TI at fixed q, composing it with these finitely
many nonadaptive block queries removes all direct-sum and deficiency cases.
The remaining hard inputs can therefore be taken concise and centroid-local
for the Turing question. A polynomial-size single ordinary-TI instance
still needs a way to encode both the local special-linear condition and the
global decision combination. Oracle calls to the local problem cannot
simply be replaced by a claimed polynomial-time ordinary computation.

Attribution and scope. The relative determinant-coset identity, centroid
decomposition, and transposition signs on structured direct sums were
developed in prior MathProofs work and classical algebra. The contribution
here is the exact unrestricted block assembly using ONLY local decision
queries, including automatic initialization and joint determinant labels.
The prior norm compiler explicitly left arbitrary primitive-block matching
and determinant products outside its guarantee. No first-publication claim
is made. The motivating parent question is Chen–Grochow–Qiao–Tang–Zhang,
ITCS 2024, Open Question 9 (arXiv:2306.03135v2, Question 1.9):
https://arxiv.org/html/2306.03135v2
No Lean verification or result about unrestricted special-linear OCI over
the complex numbers is claimed by this finite-field exact-orbit theorem.
