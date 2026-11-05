# EXPLICIT LIFTING OF CONTRACTION INVARIANTS

Supplement to "One balanced quartic tensor is TOCI-complete"

The geometric proof already handles all complex orbit degenerations. This supplement gives an independent invariant proof of closure reflection and an explicit degree bound.

Use the notation of PROOF.md. On the entire target Y define
P(Z)=Tr_2 Z, Q(Z)=Tr_1 Z, and F(Z)=((I+P(Z))/2) tensor ((I+P(Z))/2).
These are polynomial covariants for conjugation by g tensor g (on the single-factor P,Q use g). Set

    A_1(Z)=F(Z) Z (Q(Z) tensor Q(Z)) F(Z),
    A_2(Z)=F(Z) (Q(Z) tensor Q(Z)) Z F(Z).

They are polynomial covariants of degree at most 7. No projector or invertibility assumption is needed at arbitrary Z: covariance follows from equivariance of partial trace and the product identity for conjugation.

For Z=Φ(R_1,R_2), F is the projection onto W_+ tensor W_+, with W_+=e_1 tensor V, and Q tensor Q swaps color 11 with color 22. Reading the color channels gives A_1(Z)=R_1 on W_+ tensor W_+ and zero on other input/output blocks; likewise A_2(Z)=R_2 there and zero elsewhere. In particular the affine background contributes neither, since it has no maps between color 11 and color 22. This proves the identities by block multiplication; it does not require finding a basis from an arbitrary target input.

Let f be any complete contraction of d labeled input quartics, allowing each occurrence to be either R_1 or R_2. Take the same index-pairing contraction over W on the corresponding A_1(Z),A_2(Z), obtaining ƒtilde. It is G-invariant by covariance and contraction, and is a polynomial of degree at most 7d in Z. On the encoded point all summands with any contracted color other than 1 vanish, so ƒtilde(Φ(R_1,R_2))=f(R_1,R_2) exactly, with no dimension factor. Every contraction is a sum over labels attached to tensor entries, so this support argument applies to disconnected contractions too.

By the tensor first fundamental theorem (Lysikov–Walter Theorem I.10, and the mixed tensor contraction formulation in Section IV), all H-invariant polynomials on the source are linear combinations of such contractions and constants. In particular an invariant of degree at most d is a combination of contractions of at most d entries, using the grading. Thus pullback by Φ is surjective on invariant rings, and an invariant of degree ≤ d on the source has an invariant lift of degree ≤ 7d on the target. Invariants are also preserved on pullback by H-equivariance. Consequently target closure equivalence implies source closure equivalence by Lysikov–Walter Theorem II.7; the opposite implication follows directly by H-equivariance and continuity, or by invariant pullback. This is independent of the local-chart proof of containment.

The lift is an algebraic expression. It does not assert polynomial-time dense expansion of high-degree contractions, nor that TOCI has a polynomial-time decision algorithm.
