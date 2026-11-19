# Exact complexity of probing a determinant profile

This is a theorem about access through affine probes. The algorithm sees a hidden affine set only through those probes. The upper bounds give tensor-isomorphism reductions using existing sign projections. The lower bounds have this explicit access hypothesis.

Let V be a k-dimensional vector space over a finite field with q elements. A profile is either empty or a nonempty affine subspace D of V. The decision asks whether 0 belongs to D. A probe chooses any affine subspace L of codimension at most c, with 1≤c<k, and asks whether D meets L. The choices may be adaptive and may include translates. Define M_t to be the largest possible number of covered **nonzero** vectors of V* in a union of t linear subspaces of dimension c.

**Theorem.** The exact deterministic worst-case number of probes equals the smallest t with M_t=q^k−1. For a t-probe algorithm with no false negatives, the optimal worst-case false-accept probability is

    1 − M_t/(q^k−1).

The optimal worst-case success probability with two-sided error and t probes is

    1/(2 − M_t/(q^k−1)).

Both randomized optima are attained by nonadaptive probes with no translation. The statements apply to t≥1. Computation of M_t itself is a finite subspace covering problem and is independent of the unknown profile.

## Upper bounds by separating functionals

For a nonempty affine subspace D with 0 outside D, write D=x+H for a linear space H. Then x is outside H. There is a nonzero linear functional a vanishing on H and with a(x)=1. In particular D is contained in the affine hyperplane a=1.

Choose direction spaces W_1,…,W_t of codimension c whose annihilators realize M_t. Use W_i itself as a probe. All these probes accept any D containing 0. If the annihilator union is all of V*, every D omitting 0 is rejected by at least one probe, since some W_i is contained in the separating hyperplane a=0. The empty profile is rejected by any probe.

For the randomized bounds, apply a uniformly random element of GL(V) to the whole probe family. Its induced contragredient action on V* is transitive on nonzero vectors. The probability that a fixed separating functional lies in the annihilator union is exactly s=M_t/(q^k−1). Accepting precisely on the all-positive transcript therefore rejects every negative profile with probability at least s, and never rejects a positive profile. For a negative affine hyperplane a=1, a linear probe W is disjoint exactly when a vanishes on W. Thus a hyperplane attains the error bound.

For two-sided error accept the all-positive transcript only with probability p=1/(2−s), and reject every other transcript. Every positive profile is accepted with probability p, and every negative profile is accepted with probability at most p(1−s)=1−p. This proves the claimed success guarantee.

## Lower bounds including adaptive and translated probes

Run a deterministic algorithm on the positive profile D=V. Its transcript consists entirely of positive answers. Write each affine probe on this path as x_i+W_i. If a nonzero functional a lies outside the union of the W_i annihilators, then it takes every field value on each x_i+W_i. Thus the negative profile D_a={y:a(y)=1} answers positive on the same entire path. This contradicts correctness. Every direction annihilator has dimension at most c and can be embedded in a c-dimensional linear subspace. Fewer probes than a covering family therefore cannot suffice.

Now let a randomized algorithm have at most t probes, and choose a uniform nonzero a∈V*. Fix one random tape. The decision tree on D=V follows its all-positive path. Among the negative profiles D_a, the fraction with a different path is at most s, since a different path requires a in the annihilator of some direction on the all-positive path. This bound allows the affine translates x_i to vary and does not require that they contain zero. If the tape accepts D=V, it therefore accepts at least a fraction 1−s of the D_a as well. If the probability of accepting D=V is p, averaging over tapes gives false acceptance at least p(1−s) on some negative profile.

In the one-sided model p=1. In the two-sided model the worst success is bounded by min(p,1−p(1−s)), whose maximum is 1/(2−s). These are exactly the success probabilities of the constructions above. Uniform GL can be replaced by comparisons sampled from the finite orbit of the chosen test family. For fixed q and k this random choice has constant cost.

## Apply the theorem to three signs and a two-sign oracle

Over the field of three elements use V=F_2³ to record the three determinant signs of transporters from T to S, with zero recording determinant +1. For an ordinary-positive pair the profile is a translate of the determinant image of its stabilizer. Otherwise the profile is empty. A two-sign comparison with arbitrary linear sign projections and target reflections is exactly a probe for an affine subspace of codimension at most two. The prior sign-projection construction realizes such probes in polynomial time. [Exact sign projections and conjunction criteria](https://github.com/Dugongue/MathProofs/blob/main/TensorSignProjections/SignProjections.md)

All profiles used in the lower bounds do occur for actual tensor pairs. Let T_0 be the diagonal tensor e_1⊗e_1⊗e_1+e_2⊗e_2⊗e_2. A diagonal reflection of the first basis vector in any two modes gives an automorphism and realizes a nonzero sign of even total parity. These generate the two-dimensional even-total plane. The common swap of the two basis vectors in all three modes gives the odd-total sign (1,1,1). Thus the stabilizer sign image is all of F_2³. Apply any exact sign projection with image H to the pair (T_0,T_0), obtaining a pair with profile H. To realize x+H reflect the resulting target in precisely the modes specified by x. The ordinary transporter set is translated by this reflection, so its sign profile is exactly x+H. The source and target format can be fixed for each projection. The oracle lower bound concerns algorithms whose information consists of the answers to the probes. It does not treat inspection of formats or entries as another probe.

Every two-dimensional dual subspace in F_2³ contains three nonzero points. Two different ones intersect in one nonzero point and hence cover five. The three planes through a fixed dual line cover all seven. Thus

    M_1=3,    M_2=5,    M_3=7.

Exactly three deterministic probes are needed. One probe with one-sided error has optimal false acceptance 4/7. Two probes with one-sided error achieve 2/7 and cannot improve on it in this access model. In particular a uniform choice of two distinct through-zero lines followed by conjunction gives a bounded-error nonadaptive reduction from SL-TI to two two-sign comparisons. With two-sided error a single probe has optimal worst-case success 7/11, below 2/3. Thus no single probe achieves worst-case success two thirds in this model, even with translated tests and arbitrary processing of the answer.

If the ordinary-positive pair is promised to have a singleton sign profile, two distinct through-zero lines already suffice deterministically. A singleton lying in both must be the origin. One probe still cannot decide even this promise. A line containing zero contains a nonzero point giving the same positive answer, and an affine line omitting zero leaves a nonzero point giving the same negative answer. Arbitrary codimension-at-most-two affine tests obey the same argument.

The three-probe deterministic upper bound specializes to the existing three-test construction. What the theorem adds is its exact optimality under affine-profile access, including adaptivity, shifted tests, and randomized error. This identifies precisely which information must come from a tensor-specific construction to achieve a single two-sign comparison. It does not separate the unrestricted computational problems. The proofs are informal.
