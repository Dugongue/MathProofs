# An affine cocycle theorem for a symplectic point stabilizer

Status: informal proof. This is an actual classical-isometry-group theorem, not a relaxation to the units of the spanned matrix algebra. No claim of publication novelty or unrestricted closure is made.

## Theorem 1: natural-module cohomology of a single fixed symplectic vector

Let E be any explicitly presented finite field of characteristic two. Let V be a symplectic E-space of even dimension n at least 10, let G = Sp(V), and let P be the pointwise stabilizer of one specified nonzero vector v. Then restriction

    H^1(G,V) -> H^1(P,V)

is an isomorphism of one-dimensional E-spaces. The statement also holds with the squared-dual natural module, by Frobenius and polar duality.

Consequently, given a genuine affine cocycle of P on any explicitly presented direct sum of natural modules, affine transport is polynomial-time reducible to one ordinary quadratic-form isometry with vector markings, or to symplectic vector matching. The old vector v is retained as an additional marking. Arbitrary degeneracy of the new marked span is allowed for this one affine test. The same conclusion holds for a quotient known to be invariant under the full ambient Sp(V), because that quotient is again a sum of ambient natural modules.

This does not assert the conclusion for every quotient invariant only under P. That distinction is essential.

## Proof of the cohomology statement

Choose a symplectic partner w with B(v,w) = 1, and let W be their perpendicular complement. Write a vector of V as a v + x + b w, with x in W. Let H = Sp(W), acting trivially on v,w. The stabilizer P is Q semidirect H, where Q consists of the following maps for u in W and t in E:

    n(u,t): v -> v,
            x -> x + B(u,x) v for x in W,
            w -> w + u + t v.

Direct multiplication gives, up to the fixed choice of right-action convention,

    n(u,t) n(u',t') = n(u+u', t+t'+B(u,u')).

The polar form is alternating and characteristic is two, so Q is commutative and every element has square one. Its center includes Z = {n(0,t): t in E}; the quotient Q/Z is the additive natural module W. Conjugation by H sends u by the natural action and leaves t unchanged.

Let d be a right cocycle P -> V. Its restriction to H has zero components on E v and E w, because H is perfect. On the natural summand W, the known symplectic H^1 calculation makes it a sum of a coboundary and a scalar multiple of the quadratic-refinement cocycle. The rank of W is at least 8, so all the earlier safe-rank hypotheses hold. The ambient symplectic quadratic-refinement cocycle restricts to exactly this class: choose the ambient refinement as the hyperbolic form on E v + E w plus a refinement on W. Subtract a suitable ambient cocycle and a coboundary from d. We may now assume

    d(h) = 0 for all h in H.

The restriction of d to Q is then H-equivariant. Write d(n) = (a_n,x_n,b_n) in the above decomposition. For z_t = n(0,t), H-equivariance gives x_{z_t} = 0. Commutativity of Q and the cocycle identity give

    (n(u,s)-1) d(z_t) = (z_t-1) d(n(u,s)).

The W-coordinate of this identity is b_{z_t} u = 0 for every u, hence b_{z_t} = 0. Its v-coordinate then gives t b_n = 0 for every t, hence b_n = 0 for every n in Q.

The map n -> x_n is therefore additive, since the Q action on v-perpendicular modulo E v is trivial. It vanishes on Z and is H-equivariant on Q/Z = W. The binary endomorphism ring of the natural H-module is E, so

    x_{n(u,t)} = lambda u

for some lambda in E. The coboundary of lambda w has precisely W-coordinate lambda u and v-coordinate lambda t. Subtract it. The remaining restriction to Q is an H-invariant additive homomorphism Q -> E v.

Identify this homomorphism with a function a(u,t) = A(t) + f(u), where A is an additive binary-linear map E -> E. Additivity for the displayed twisted group law says

    f(u+u') = f(u) + f(u') + A(B(u,u')).

H-invariance and transitivity on nonzero vectors of W make f equal to one value b on every nonzero u, with f(0) = 0. Choose distinct perpendicular nonzero u,u' with u+u' nonzero; these exist in dimension at least 4. The equation forces b = 0. It then forces A(B(u,u')) = 0 for every pair, so A = 0 because B takes every E-value. Thus the remaining cocycle is zero on Q and H, hence on P.

This proves surjectivity of restriction. Injectivity follows by restricting further to H: the ambient symplectic generator restricts to the nontrivial symplectic natural-module class on W. Both classes are nonzero and the ambient H^1 is one-dimensional. This proves the theorem.

## Constructive affine transporter

All cocycle parameters are recovered with polynomially many evaluations, not by enumerating P or E^n. Restrict to H and use the separating transvection equations from Round2Matrix.md to recover the natural W coboundary and the coefficient of the ambient quadratic-refinement class. The trivial v,w components on H are zero. Subtract these terms. The preceding proof says the remaining cocycle is the coboundary of one scalar multiple of w. Evaluate n(0,1); its value is that scalar times v, recovering the scalar. The coefficient of v in the coboundary basepoint is immaterial because v is P-fixed. This determines a correct global normal form by the proved classification.

For several natural copies, do this independently in each coordinate. Express the affine matching equations as quadratic forms with proportional common polar B, exactly as in OriginalMatrix.md. If the quadratic-refinement coefficient is nonzero, retain one quadratic equation and subtract multiples from the others to obtain only vector markings. If it is zero, there are only vector markings. Add the old marking g v = v. Use classical constructive Witt extension to solve the full system. This constructs an element of P, not merely an invertible linear map commuting with a subset of the action. Degenerate marked spans are allowed in this extension step; the issue is future closure, not the correctness of this one test.

For an ambient-Sp-invariant quotient of natural copies, first extract its natural multiplicity-space presentation by binary and E-linear algebra as in OriginalMatrix.md. Then use the same algorithm. Testing that a proposed radical-image subspace is ambient-invariant is direct linear algebra on a polynomial-size standard symplectic generating set. This is a checkable sufficient condition, not an assumed extension oracle.

## Corollary 2: a two-grade actual norm algorithm passing through a degenerate line

Use the algebra-with-involution setup of OriginalMatrix.md, with one symplectic simple quotient Sp(V), n at least 10. Permit arbitrary radical length, but suppose the graded Tate defects are nonzero at at most two grades k_1 < k_2. At the first active grade suppose the recovered symplectic cocycle has no quadratic-refinement component and its target vector markings span exactly one nonzero line. Then its exact residue stabilizer is P = Sp(V)_v. This marking span is polar-degenerate, so Round2Matrix.md deliberately did not cover it.

At the second active grade impose the additional check that the radical correction image, modulo the trace subspace, is invariant under the full original Sp(V), not just under P. Its remaining obstruction module is therefore an ambient natural quotient. Apply Theorem 1, preserving g v = v, to obtain the exact second-grade affine transporter and physical radical correction. All subsequent Tate defects are zero, so trace corrections finish every remaining grade regardless of the newly obtained stabilizer. There is no third affine stabilizer problem hidden in the corollary.

As before, solve and normalize the residue norm equation first, use the faithful regular plus congruence representation for physical fixed-residue calls, and multiply actual witnesses throughout. The first-grade image is proved to be P. Hence every prescribed P element required by the second-grade cocycle evaluation has a physical preimage through the previous grades, found by the existing fixed-residue unipotent algorithm. Rejection by the actual P-affine test rules out every legal residue continuation. The algorithm is Las Vegas polynomial time in explicit structure constants and the finite-field presentation.

This is a sufficient norm/isometry theorem with a genuinely degenerate intermediate marked span. It does not assert ambient invariance of the second radical-image quotient for arbitrary inputs, and does not claim unrestricted characteristic-two tuple isometry.

## Transfer audit: what the marked-module epimorphism count does and does not supply

The exact marked-module count from Groups.md can solve prescribed module homomorphisms and compare their head ranks by polynomial linear algebra. In the present argument it can assist with multiplicity-space quotients and fixed linear marks. It cannot replace P by the unit group of its spanned algebra, nor may a surjective module map be declared a quadratic isometry. The sufficient advance above instead proves the missing cocycle classification for the actual group P and retains Witt extension as the exact isometry test.

The universal next obstacle remains the arbitrary P-invariant quotient of ambient natural copies. Such a quotient may have a nonsemisimple flag module. This proof does not identify its affine transporter with a relaxed ring-unit transporter. No conclusion is drawn from that relaxation.

## Inherited sources and status

The only non-elementary cohomology input is the natural symplectic H^1 calculation, as recorded by Kantor–Liebler Theorem 2.14(i), https://pages.uoregon.edu/kantor/PAPERS/KantorLiebler.pdf . The parabolic restriction calculation above is proved explicitly rather than quoted as a new black-box theorem. Classical Witt extension and Sun's physical unipotent transport remain the exact inherited algorithmic inputs; see OriginalMatrix.md and https://arxiv.org/pdf/2611.05920, Appendix A. Source priority for the point-stabilizer cohomology lemma has not been checked. No claim that it is a new classical cohomology theorem is made.

## Addendum: a split parabolic quotient is enough

The ambient-Sp-invariance condition in Theorem 1 and Corollary 2 may be replaced by this more general, directly testable sufficient condition: the actual P-equivariant quotient map

    pi: V^r -> W

has a P-equivariant binary-linear section. Testing this condition and constructing the required natural-copy presentation both take polynomial time. No unit group is substituted for P.

Here is an explicit proof. In the decomposition V = E v + W_0 + E w used above, the endomorphism ring of V as a binary P-module consists exactly of

    a I + N_B,

where a is in E and B:E -> E is an arbitrary binary-linear map, and N_B sends b w to B(b) v and kills E v + W_0. To verify this, first commute with H = Sp(W_0). Its natural module has no trivial constituents and endomorphism field E. Therefore an endomorphism has scalar lambda on W_0 and arbitrary binary-linear blocks A,B,C,D on the two trivial E-coordinates. Commuting with n(0,t) for all t forces C = 0, A = D, and A(bt) = t A(b), so A and D are multiplication by one a in E. Commuting with n(u,0) then forces lambda = a. The block B remains arbitrary, since the bottom coordinate is unchanged by P and the top line is pointwise fixed.

The maps N_B form a square-zero two-sided ideal, and the quotient of this endomorphism ring by that ideal is E. In particular the endomorphism ring is local and its radical is exactly the maps N_B. The argument applies to binary-linear endomorphisms; it does not impose E-linearity on B.

Suppose s:W -> V^r is a P-equivariant section of pi. The idempotent p = s pi is in the matrix ring Mat_r(End_P(V)). Its reduction modulo the square-zero radical is an idempotent matrix over E. By E-linear Gaussian elimination, choose an invertible E-matrix U taking its image and kernel to the standard coordinate subspaces, so that the conjugate p' reduces to q = diag(I_h,0). Regard U as a P-module automorphism of V^r by scalar multiplication on each block. Put

    c = p' q + (1 - p') (1 - q).

Then p' c = c q, and c reduces to the identity modulo the square-zero radical. Hence c is invertible by a finite exact inverse, and p' = c q c inverse. The map pi U c on the first h copies of V is a P-module isomorphism V^h -> W. This gives the required natural-copy presentation constructively.

A section s is found or proved not to exist by the equations pi s = identity and s g_W = g_{V^r} s on a polynomial-size generating set of P. Such a set is explicit: standard elementary symplectic generators of H together with n(u,t) for binary basis vectors u of W_0 and t of E generate P. All equations are binary-linear. If the quotient does not split, this sufficient test returns OUTSIDE_SCOPE, not NO. If it splits, the preceding conjugation and the actual P-affine solver apply.

Consequently the two-grade norm corollary remains polynomial whenever the second actual obstruction quotient is split as a P-module, even if its radical-image kernel is not ambient-Sp invariant. Ambient invariance remains a sufficient special case. The improvement transfers a projective/direct-summand module idea into the actual isometry problem while retaining its full P-action and cocycle. A generic nonsplit parabolic quotient is still outside this result.

## Addendum 2: the nonsplit natural quotient V / E v

The quotient by the fixed line has an exact polynomial affine solver even though the quotient map does not split as a P-module. This removes the section condition for a concrete nonsplit module, rather than replacing the acting group by ring units.

### Theorem 3

Retain P = Sp(V)_v and n at least 10. Put N = V / E v, as a binary P-module with its explicit E-coordinates. Every right cocycle P -> N is a coboundary plus an E-scalar multiple of the projected ambient symplectic quadratic-refinement cocycle. Its H^1 is one-dimensional over E. Affine transport on an arbitrary direct sum N^r, and on N^r plus explicitly trivial binary modules, is polynomial-time decidable and constructible under the actual P-action.

The natural quotient V -> N is genuinely nonsplit. For example, with n(0,t) acting on V it takes w to w + t v, whereas that element acts identically on N. A P-equivariant section would have an image fixed by every n(0,t), which is contained in v perpendicular and has dimension n - 1. It would also have to surject onto N, whose w-coordinate cannot be obtained from that perpendicular hyperplane. Thus this new case is outside the split-quotient addendum.

### Cohomology proof

Use the established P = Q semidirect H, with H = Sp(W), and identify N with W plus E w. Write its coordinates as (x,b). The central subgroup Z = {n(0,t)} acts trivially on N, and a general n(u,t) acts by

    (x,b) -> (x + b u, b).

Its H-action is (x,b) -> (h x,b), with the fixed choice of equivalent left/right coordinate convention.

Choose the ambient quadratic refinement

    Q_0(a v + x + b w) = a b + q_W(x),

where q_W refines the symplectic form on W. Under n(u,t), its difference is (t + q_W(u)) b squared. The resulting natural cocycle lies in E v and therefore projects to zero in N. On H the projected cocycle is exactly the natural quadratic-refinement cocycle kappa_H.

Let d:P -> N be a genuine cocycle. On H its bottom component is zero because H is perfect, and its middle component is a coboundary plus a multiple of kappa_H. Subtract that coboundary and the projected ambient cocycle, so d vanishes on H.

On Q its bottom component is now an H-invariant additive homomorphism Q -> E. The preceding proof that Hom_H(Q,E) = 0 applies verbatim: write A(t) + f(u), use transitivity to make f constant on nonzero u, use distinct perpendicular vectors to force that constant to zero, then the twisted Q law forces A = 0. Thus the bottom component of d on Q vanishes.

The middle component is consequently additive and H-equivariant. It vanishes on Z because W has no H-fixed vector. It factors through Q/Z = W and is lambda u by End_H(W) = E. This is precisely the coboundary of the class lambda w in N. Subtract it and d vanishes on Q and H. This proves the claimed cohomology classification. Restricting to H proves that the projected quadratic-refinement class is nonzero and that its scalar is unique.

The parameters are recovered polynomially. Use the H separating transvections to recover the W-coordinate coboundary and quadratic-refinement coefficient. After subtraction, evaluate any n(u,0) with u nonzero to recover the remaining scalar multiplying w. This is a globally correct normal form by the proof, not an assumption that arbitrary generator values extend.

### Exact affine elimination

Absorb the recovered coboundary into the source and target points. In copy i write them as (a_i,b_i) and (c_i,d_i). Let lambda_i be the quadratic-refinement coefficient. Every actual P element can be parametrized on N as

    (x,b) -> (h x + b u,b), with h in Sp(W), u in W,

and the remaining cocycle value is lambda_i kappa_H(h). The central parameter t is free and acts trivially on N. The affine transporter equations first require b_i = d_i for every i and then become

    h a_i + b_i u + lambda_i kappa_H(h) = c_i.

If all b_i vanish, set u = 0 and invoke the previously established full-symplectic affine natural-module solver for h.

Otherwise choose an anchor j with b_j nonzero and eliminate u using its equation. For every other i this leaves

    h (a_i - (b_i/b_j) a_j)
      + (lambda_i - (b_i/b_j) lambda_j) kappa_H(h)
      = c_i - (b_i/b_j) c_j.

This is exactly one full-Sp(W) affine natural-copy test. Solve it polynomially and recover

    u = b_j inverse times (c_j - h a_j - lambda_j kappa_H(h)).

Choose the central parameter t = 0 and the corresponding actual n(h inverse u,0) h in P. It satisfies every original equation; in particular it still fixes the original v. Conversely every actual affine transporter yields such an h and hence passes the reduced test. This proves exact decision and construction, with no relaxed isometry requirement and no group enumeration.

For additional trivial binary summands, their cocycle is zero because P is perfect. Indeed H is perfect and the established vanishing of Hom_H(Q,E), in particular Hom_H(Q,F_2), makes Q have zero H-coinvariants. Therefore require equality of those trivial source and target coordinates, and apply the preceding algorithm independently. The actual P-action on N remains in force throughout.

### Norm-lifting consequence

In Corollary 2 the second-grade remaining obstruction module may therefore be N^r plus trivial modules, with a supplied and checked P-module presentation, even though V -> N is nonsplit. In particular the explicit quotient of r ambient natural copies by the direct sum of their fixed E v lines is covered. Such a presentation can be checked by its linear maps and the explicit polynomial-size P generators. The same physical preimage, radical correction and zero-later-Tate arguments finish the exact norm theorem in polynomial time.

This statement does not cover arbitrary mixed copies of V and N or arbitrary nonsplit parabolic flag modules. No assertion is made that every abstract quotient kernel occurs as an actual norm correction image. The theorem applies when the actual computed second-grade obstruction has the stated checked presentation.
