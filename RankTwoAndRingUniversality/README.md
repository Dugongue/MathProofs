# Rank two completion and tensor universality over rings

Informal proofs and reproducible finite checks. These results have undergone internal mathematical review, not Lean certification or external peer review. They comprise connected theorem families, not four independently established first solutions to major open problems.

| Result | Exact scope | Relation to prior work |
| --- | --- | --- |
| Rank two completion universality | Ordinary partial matrices with specified entries only 0 and 1; every blank independent. Over every fixed field, deciding a rank-at-most-two completion is polynomially equivalent to the existential ring theory with constants 0 and 1. | Sharpens the rank-three completeness theorem of Shitov. The broader Compendium A16 questions were already answered by that theorem. |
| Binary positive semidefinite completion | Rank-two PSD completion is existential-real complete even with a bipartite observation graph, binary specified entries and every diagonal free. | A consequence of the ordinary-completion theorem. General rank-constrained PSD hardness was already known; the precise restrictions matter. |
| Tensor universality over arbitrary commutative rings | The five free-module tensor actions, formal cubic equivalence, and associative and commutative associative unital algebra isomorphism are polynomially equivalent. Mixed systems have bounded component order and may have polynomially many named components. | Extends the diagonal-full-ring equivalences of Grochow, Qiao, Stange and Sun, Theorem 3.7, to arbitrary commutative base rings in the finite-free basis model. |
| Smaller form reductions in small characteristic | Fixed-degree formal forms reduce to ordinary 3-TI with largest mode at most poly(d) times n^(floor(d/2)+1), over every field. Cubics use O(n^2) modes even in characteristics 2 and 3. | Improves the full symmetric-power construction. No exact named open question or best-runtime claim is made for this size bound. |

Read the full [completion proof](RankTwoCompletion.md), [PSD corollary](PSDCompletion.md), [ring universality proof](RingUniversality.md), and [form reduction](FormReduction.md). The [scope and audit record](ScopeAndAudit.md) distinguishes proved implications from priority claims.

## Why the completion result matters

The completion theorem places full existential real feasibility in the smallest nontrivial rank beyond the easy binary rank-one case. The input contains no complicated numerical constants. Over each fixed finite field the same rank-two problem is NP-complete by an explicit projective-line coloring reduction. Its rank gap of two versus at least three also yields existential-real hardness for feasible multiplicative approximations with factor strictly below 3/2. This concerns arbitrary exact instances; it does not invalidate recovery algorithms under additional sampling or distribution assumptions.

Over the rationals it gives an unconditional reduction from rational polynomial solvability. Any conclusion of undecidability requires, separately, a negative answer to Hilbert's tenth problem over the rationals. No new proof of that arithmetic theorem is supplied here.

## Why the ring result matters

The reductions preserve isomorphism over the original ring, including rings with zero divisors and nilpotents. They require no decomposition oracle, division, rank oracle, or diagonal-full assumption. They concern finite free modules supplied by bases. They do not decide isomorphism of arbitrary presented modules, supply a new unrestricted tensor-isomorphism runtime, or enforce special-linear determinant constraints.

## Reproduce the bounded check

Run `python audit_rank_two.py` with Python 3.8 or later. It checks scalar-copy uniqueness, explicit arithmetic-gate pins, and the finite-field coloring relation over the prime fields of orders 2, 3, 5 and 7. These computations support the written proofs; they are not exhaustive proofs over all fields.

## Attribution and priority

The main precedents are [Shitov on tensor rank and completion](https://arxiv.org/abs/1611.01559), [Futorny, Grochow and Sergeichuk on tensor-system universality](https://arxiv.org/abs/1810.09219), [Grochow and Qiao on tensor reductions](https://arxiv.org/abs/2306.16317), and [Grochow, Qiao, Stange and Sun on commutative rings](https://arxiv.org/abs/2611.00735). The [existential-real compendium](https://arxiv.org/abs/2407.18006) supplies context for the matrix-completion questions.

The targeted literature search did not locate the exact rank-two binary theorem or the arbitrary-ring extension. That is not certification of publication priority. These are independently written arguments, not copied upstream Lean proofs; no external source code is included. Scientific attribution appears in each proof.
