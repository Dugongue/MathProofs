# Characteristic-two norm lifting when each symplectic block appears at one obstruction grade

Status: informal proof; no Lean certification; no priority claim. This is a sufficient polynomial-time theorem, not the unrestricted matrix-tuple isometry solution.

## Campaign contract and comparison of routes

Root problem: given an explicit finite-dimensional algebra A over a finite characteristic-two field, an involution *, and c = c* in A^times, construct u with u* u = c or reject. The equivalent ordered matrix-tuple problem uses the standard adjoint-algebra norm reduction.

Route A: classify affine actions of a full classical group on the natural obstruction modules. This has a concrete classical cohomology theorem and an explicit quadratic-form solver. It succeeds while the relevant residue factor is still full.

Route B: after a vector or quadratic marking is installed, split the marked stabilizer into its unipotent radical and a smaller classical quotient, solve the former by unipotent transport, and recurse. A general proof was not obtained. The quotient of the current defect module by the radical image need not remain a direct sum of natural modules of the smaller classical quotient. Assuming that it does would conceal the outstanding problem. This route is not used below.

The sufficient theorem below permits many obstruction grades but ensures no simple factor must be processed after it has acquired markings. It maintains one accumulated residue candidate through every grade; it never chooses unrelated fresh quotient witnesses.

## Theorem 1: constructive affine transport for full symplectic natural modules

Let E be an explicitly presented finite field of characteristic two. Let V be a symplectic E-space of dimension 2m, with m at least 3, and let G = Sp(V). Let W be an explicitly presented direct sum of copies of the natural Frobenius-twisted module, or an explicit G-module quotient of such a sum. Given a genuine right 1-cocycle d: G -> W through its values on a standard polynomial-size generating set, and x,y in W, the problem

    x^g + d(g) = y

has a polynomial-time decision and witness-construction algorithm. The polynomial is in the written module dimensions and log |E|. A cocycle supplied by a physical lifting procedure is allowed; evaluating it on the standard generators suffices.

The linear action, its natural-copy presentation, and the fact that d is a cocycle are part of the mathematical input contract. This theorem does not assert that arbitrary generator values are a consistent cocycle. In the norm application below consistency is proved from actual lifts.

### Proof

The natural binary representation of Sp(V) is simple, has no nonzero fixed vector, and has endomorphism field E. Frobenius twists are normalized by field automorphisms. A submodule of an isotypic direct sum of simple modules is a direct summand and the quotient is again isotypic. An explicit decomposition is obtained by computing Hom_G(V,W) with linear equations on generators and extending a direct-sum basis. The domain dimension is polynomial. Thus it suffices to handle W = N^r, where N is the module of zero-polar quadratic forms on V. Identifying a form sum a_i X_i^2 with its coefficient vector gives the squared dual natural action. Symplectic duality and a field Frobenius identify this with the stated module.

Fix a quadratic form Q_0 with polar B, the defining symplectic form. Put kappa(g) = Q_0 composed with g minus Q_0. It is a right cocycle with values in N. The established natural-module cohomology calculation says H^1(Sp(V),N) is one-dimensional over E and is represented by kappa. Consequently every coordinate cocycle has the form

    d_j(g) = z_j^g - z_j + lambda_j kappa(g),

for z_j in N and lambda_j in E. The rank restriction avoids small-group exceptions. This is classical group cohomology, not a new claim of this note. The exact symplectic dimension statement is recorded in Kantor–Liebler, Theorem 2.14(i), which summarizes Pollatsek, Cline–Parshall–Scott, Jones and others. The geometric quadratic-refinement representative is also described in Cherlin–Hrushovski, Fact 3.3.6.

The unknown coefficients of z_j and lambda_j are recovered by linear equations from the supplied generator values. These equations have a solution by that cohomology theorem. Both sides are genuine cocycles, so equality on the generating set proves equality on every group element. This avoids enumerating G, a discrete logarithm, or a table of cocycle values.

Now write

    P_j = lambda_j Q_0 + x_j + z_j,
    Q_j = lambda_j Q_0 + y_j + z_j.

The requested affine equality is exactly P_j composed with g = Q_j for all j. If every lambda_j is zero, these are linear-function markings after taking square roots of coefficients. Match their linear relations and the symplectic pairings on their dual marked vectors; Witt extension constructs g exactly when these tests hold.

Otherwise choose j with lambda_j nonzero and divide that equation by lambda_j. It specifies one quadratic-form isometry with the fixed nondegenerate polar B. Subtract lambda_i/lambda_j times this equation from the other equations. Every remainder has zero polar and therefore gives only a linear marking. Test the two ambient quadratic types and the induced quadratic isometry on the spans of marked vectors. Witt extension for nondegenerate quadratic spaces extends it to g. Marked subspaces may be degenerate; the ambient polar is nondegenerate. Classical elimination implements all these tests and extensions in polynomial time over the explicit finite field.

This proves the theorem. The description also supplies an explicit representation of the stabilizer as a symplectic group with vector markings, or as one quadratic orthogonal group with vector markings. The theorem makes no claim about arbitrary subsequent affine actions of this marked subgroup.

## Theorem 2: arbitrary-depth norm lifting with one obstruction grade per symplectic factor

Let A, *, J and c be as above. Suppose the semisimple algebra with involution S = A/J is a direct product of first-kind symplectic matrix factors. Write their unitary groups as

    C_i = Sp_{2m_i}(E_i), with m_i at least 3.

The center fields E_i may be arbitrary finite characteristic-two extensions of the base field. Let

    T_k = Fix_*(J^k/J^{k+1}) / {v + v*: v in J^k/J^{k+1}}.

Use the canonical decomposition of T_k by the simple involution orbits of S. Suppose that for each i, its summand T_{k,i} is nonzero for at most one k. Some factors may be inactive at every k. Then norm decision and construction of one norm witness take Las Vegas polynomial time in the explicit structure-constant input. Radical nilpotency length, matrix ranks, center degrees and the number of factors are unrestricted. The hypothesis is computable by finite-algebra and vector-space operations.

This theorem also applies to the ordered matrix-tuple isometry instances whose adjoint algebra satisfies these conditions. It does not cover a symplectic block contributing nonzero Tate defects at two different grades.

### Shared lifting objects

Solve the residue norm equation first by classical bilinear isometry. If it has no solution, reject. Choose a lift a of a residue solution and replace c by (a*)^{-1} c a^{-1}; now c is 1 modulo J. A solution w for the normalized problem gives w a for the original problem.

Let U = 1 + J, acting by congruence v: b -> v* b v. At grade k set

    K_k = {v in U: c^v = c modulo J^k},
    delta_k(v) = c^v - c modulo J^{k+1},
    R_k = image delta_k.

The map delta_k is an additive homomorphism, its kernel is K_{k+1}, and R_k contains all traces v + v*. These claims use that elements of U act trivially on J^k/J^{k+1}. Kernel, image and prescribed-preimage calculations are polynomial by a binary central series for 1 + J, equivalently by Sun's unipotent affine transporter. This is established machinery, not the new part of this proof.

For an allowed residue subgroup C' and its congruence stabilizer H_k modulo J^k, let C_k be its actual residue image. Set W_k = Fix_*(J^k/J^{k+1}) / R_k. Actual lifts define a right cocycle

    d_k(s) = [c^g - c], where g lifts s in H_k,
    d_k(st) = d_k(s)^t + d_k(t).

Changing g changes its defect by R_k, so the cocycle is well defined. A source b already matching c modulo J^k advances precisely when

    [b-c]^s + d_k(s) = 0 in W_k.

After finding s, lift it physically, and use a prescribed-preimage calculation in K_k to cancel the remaining error in R_k. Every accepted grade therefore updates an actual element of A^times, not just formal residue data.

### Why unused factors remain full

Before factor i reaches its unique active grade, it acts trivially on all preceding T_l and hence on W_l. Restricting d_l to C_i therefore gives a homomorphism from C_i to a binary additive group. The groups C_i under the rank hypothesis are perfect, so this homomorphism is zero. Thus every element of C_i continues to lift through all preceding congruence stabilizers. In particular the full factor, not a hidden subgroup, is available at its active grade.

To construct the necessary lifts of standard generators, use the fixed-residue unipotent lifting algorithm through the preceding grades. The preceding paragraph proves each such call succeeds. Thus this fullness assertion is algorithmic and does not assume a residue-preimage oracle.

### Why old factors cannot contaminate a new grade

At grade k, let I_k consist of factors active at k. The other factors have zero summand in T_k. Write D for the product of previously constrained stabilizers and the other factors. The current residue group has the form

    D x product_{i in I_k} C_i.

The module T_k, and consequently W_k, is supported only on the current factors and is a sum of their nontrivial natural modules. A full current C_i has no fixed vectors on its summands. The invariant subspace R_k is a submodule for this full product, so W_k decomposes by the same factors into natural isotypic quotients.

For t in D and s in a current C_i, their residue classes commute. Applying the cocycle identity in the two orders, and using that D acts trivially on W_k, gives

    d_k(t)^s = d_k(t).

The simultaneous fixed space of all current factors in W_k is zero. Hence d_k(t) = 0. Thus old marked groups and inactive factors neither move the current defect nor translate it. Distinct current factors also have no cross-cocycle components by the same calculation. This is the precise independence statement; commutativity of the underlying factors alone would not suffice without the no-fixed-vector argument.

The current affine problem therefore splits into independent instances of Theorem 1, one for each i in I_k. Solve them, install the physical radical corrections, and keep those chosen residue components fixed. The leftover stabilizer of a processed factor can be discarded for future search: its linear action and its cocycle contribution vanish at every future grade by the same argument. In the unrestricted stabilizer it remains a direct factor. Consequently discarding it loses no possible successful continuation.

At a grade with T_k = 0, the trace image already fills the fixed space and ordinary radical correction suffices.

### Induction, soundness and completeness

Initially the full residue product is available. At each active grade the previous paragraphs prove the availability of all current factors, the absence of cross-translations from old factors, and exact sufficiency of the affine tests. After solving them, the residue image becomes the previous direct factors times the new affine stabilizers times untouched future factors. A current block never reappears in later T_l by hypothesis. The same invariant is therefore valid at the next grade.

Every success supplies a physical element correcting the source one further radical power, so the final element satisfies the exact norm identity. If a grade rejects, Theorem 1 rules out every current residue choice, old factors have zero effect on that defect, and the radical image R_k includes every allowable identity-residue correction. Hence no global norm solution exists.

There are at most dim A grades. All vector spaces, standard generator sets, linear systems and algebra products have polynomial size. Theorem 1 and the unipotent transporter use polynomial time, and no semisimple group is enumerated. Finite-algebra decomposition can be Las Vegas; subsequent steps are exact. This proves the stated complexity bound.

## Failed universal extrapolation and the exact remaining frontier

Theorem 1 cannot simply be reapplied after its first test. Its output stabilizer may be an orthogonal group with marked vectors or a parabolic subgroup with a nontrivial unipotent radical. A later R_l is then invariant under that smaller group, not under the original full Sp. Natural isotypic semisimplicity no longer follows. The quotient may acquire extensions and fixed constituents; a new affine cocycle may then involve the previous markings.

The one-grade-per-factor condition above is an explicit sufficient hypothesis eliminating exactly that revisit. It is not a claim that arbitrary adjoint algebras satisfy it. The remaining universal affine-stabilizer lemma has not been proved in this campaign checkpoint.

## Sources, ownership and retrieval

The new proposed contribution is the multi-grade assembly under the stated single-grade-support hypothesis. The H^1 calculation, Witt extension, adjoint norm reduction, and fixed-residue unipotent solver are existing mathematics. Publication novelty of the assembly has not been established.

- Kantor and Liebler, The rank 3 permutation representations of the finite classical groups, Transactions AMS 271 (1982), Theorem 2.14(i): https://pages.uoregon.edu/kantor/PAPERS/KantorLiebler.pdf . This primary paper explicitly records the one-dimensional natural-module H^1 for characteristic-two symplectic groups and its low-rank exceptions.
- Cline, Parshall and Scott, Cohomology of finite groups of Lie type, I, IHES 45 (1975), pp. 169–191: https://numdam.org/item/PMIHES_1975__45__169_0/ . The paper treats q > 3 and credits Pollatsek's earlier characteristic-two work; the broader small-field table is the preceding source.
- Jones and Parshall, On the 1-cohomology of finite groups of Lie type (1976), pp. 313–328: https://doi.org/10.1016/B978-0-12-633650-4.50022-9 . No new computation of their cohomology tables is claimed.
- Cherlin and Hrushovski, Finite Structures with Few Types, Fact 3.3.6: https://sites.math.rutgers.edu/~cherlin/Paper/2003FSFT.pdf . This explicitly connects the nontrivial symplectic affine class to quadratic refinements.
- Sun, Appendix A, especially Lemma A.24: https://arxiv.org/pdf/2611.05920 . Supplies the polynomial unipotent affine transporter underlying the fixed-residue calls.
- Ivanyos and Qiao, https://arxiv.org/abs/1708.03495 . Supplies the classical adjoint norm formulation and odd-characteristic context.
- Grochow–Qiao–Stange–Sun, Part V, section 1.4: https://arxiv.org/html/2611.00735v1 . The unrestricted characteristic-two matrix-tuple isometry problem is the published frontier, not closed by the sufficient theorem here.

Federated Lookup-DAG searches used GroupCohomology, Pollatsek, symplectic cocycle, and FirstCohomology. They returned source-only Mathlib representation-cohomology material, the external FLT cokernel/short-exact infrastructure, and Physlib affine symplectic cocycle definitions. No retrieved Lean declaration supplied the finite-classical natural H^1 theorem or the universal affine stabilizer lemma. No source-only search result is represented as a new kernel check.

## Constructive Witt extension used in Theorem 1

The finite-field extension call can be implemented directly; it is not a new oracle. First check the linear relations among marked vectors and the restricted bilinear or quadratic values. Choose a basis of their span S and split off a maximal nondegenerate polar summand H by paired Gaussian elimination. The remaining R is the polar radical of S. Perform the same operations on the specified image; the coefficients and Gram data agree. Remove the matched H on both sides.

For alternating spaces, R is totally isotropic. Choose dual partners by linear equations, eliminate cross-pairings by triangular corrections, and complete the resulting matched hyperbolic pairs to symplectic bases of the complements.

For quadratic spaces with nondegenerate ambient polar, q restricted to R is the square of one linear functional. Choose a basis so that all but at most one basis vector have q-value zero. Match the totally singular subspace R_0 first: choose dual partners by linear equations, and make each partner singular by adding a suitable multiple of its singular paired vector. Cross-pairings can be eliminated by the usual triangular operations. If a nonsingular marked vector r remains, require the chosen partners of R_0 also be perpendicular to r; these are consistent independent linear conditions, because r is independent of R_0. Remove these matched hyperbolic pairs.

It remains to extend an isometry on at most one nonsingular vector r in a nonsingular ambient quadratic space. Pick a polar partner on the source and find a partner on the target with the same quadratic value. This is one affine quadratic equation on the hyperplane B(r,w) = 1. Existence follows from the ordinary Witt extension theorem; finding it requires no group search. In characteristic two, one scalar affine quadratic equation over an explicit finite field is solved in polynomial time: split off its polar nondegenerate part and translate away the linear term there. If that part is nonzero, it contains a nonsingular binary quadratic form, and every such form over a finite field represents every field element (or use its norm-form presentation). If the polar part is zero, the entire polynomial is an additive binary-linear map plus a constant, so solve by binary Gaussian elimination. This constructs the required partner. The matched two-space is nondegenerate. Match its orthogonal complements by ordinary quadratic-space elimination, which is applicable because their ambient types agree.

Thus all prescribed images are extended using polynomially many linear equations, finite-field square roots, binary Artin–Schreier equations, and quadratic-form elimination. The argument also explains why the marked subspace itself need not be nondegenerate. An explicit implementation reference for the underlying classical extension routines is https://docs.magma-maths.org/v2.30-1/MatricesLinearAlgebra/PolarSpaces/isom-sim.html . No measured software benchmark or Lean verification is claimed here.

## Audit supplement: exact Tate blocks, binary quotients, and physical lifts

This gives the block justification used above in the stated symplectic-only theorem. Put M = J^k/J^{k+1}. Since every quotient factor is self-dual of first kind, star takes e_i M e_j to e_j M e_i. If i differs from j, a fixed element of the paired sum is x + x* and contributes zero to T_k. Only e_i M e_i survives.

Let E be the center of this factor M_n(E). Split e_i M e_i as a bimodule using the factors of E tensor_F E. Its summands M_theta have right scalar action x a = theta(a) x for an F-automorphism theta of E. Star exchanges M_theta and M_{theta^{-1}}. Distinct inverse summands give zero fixed/trace quotient. If theta = theta^{-1} is nonidentity, star is theta-semilinear and there is a in E with a + theta(a) = 1. Every fixed x is then the trace of a x. Thus that summand also has zero Tate quotient. This uses ordinary finite-field relative trace and works in characteristic two.

The remaining untwisted bimodule is Mat_n(E) tensor_E P for an E-vector space P. Matrix units construct this presentation. On this block star is matrix adjoint for the residue symplectic form, tensor an E-linear map j on P with j squared equal to 1. To see this, compose star with the known matrix adjoint; the resulting bimodule map commutes with both full matrix actions, so acts on P only. In characteristic two j has Jordan blocks of sizes 1 or 2. A size-2 block is a swapped pair in a suitable basis and has fixed part equal to the trace image. A size-1 block leaves the adjoint-fixed matrices modulo adjoint traces. Multiplication by the residue Gram matrix identifies these with symmetric matrices modulo alternating matrices. The diagonal map identifies that quotient with the squared dual natural module. Congruence sends a diagonal coefficient vector by the entrywise-squared matrix because off-diagonal cross terms cancel in characteristic two. Taking square roots of coefficients normalizes the Frobenius twist as a binary module.

All these changes of coordinates are computed by field-linear equations and matrix units. They establish the precise natural-copy claim for T_k; they do not assert that an arbitrary quotient invariant under a later marked subgroup has the same form.

Although R_k is only binary-linear, this creates no gap at a full symplectic stage. The natural binary representation is simple: a nonzero invariant binary subspace contains one nonzero vector and hence its entire Sp orbit, which is every nonzero vector. Its binary endomorphism ring is E. Indeed, an endomorphism commuting with each transvection preserves the image of transvection minus identity, namely every E-line. Additivity on independent vectors then forces the same scalar on every line, hence the endomorphism is multiplication by one scalar of E. Thus an isotypic sum of natural copies has all its submodules and quotients isotypic, with multiplicity spaces over E, even when supplied only as binary subspaces.

The resulting quotient presentation is effective. Compute Hom_G(V,W_k) by binary linear equations on a standard generating set. Every nonzero map is injective. For each chosen copy solve the binary intertwiner equations for a retraction with prescribed composite identity; such a retraction exists by semisimplicity of the isotypic sum. Split it off and repeat. The number and dimensions of these linear systems are polynomial. No enumeration of module elements or group elements is needed.

For physical preimage and stabilizer computations, represent 1 + J faithfully by its regular multiplication action, and take its direct sum with the congruence action on A. Test the vector (c,0), or the corresponding source and target pair. The regular summand is tested at zero, so it imposes no new condition, but prevents a nonfaithful congruence representation from silently discarding group elements in its kernel. Every regular matrix of 1 + J is unipotent. Apply Sun's unipotent transporter to this faithful representation. Its stabilizer and transporter outputs then recover actual algebra elements and include the full kernel; this is essential for later R_k images. Standard generators of a still-full residue symplectic factor are lifted by these actual fixed-residue calls, rather than by an assumed section of the unitary group.
