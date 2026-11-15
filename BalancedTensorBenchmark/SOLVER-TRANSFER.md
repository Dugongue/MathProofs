# Exact covector filtering for the binary balanced pipeline

The binary solver compares ordered tensors of shape $2\times\cdots\times2$ over $\mathbf F_2$. It uses Problem 1.8’s strategy of extracting intrinsic data, restricting the transporter, and verifying an actual basis change. Here the intrinsic data are exact counts on binary covectors. The existing Gram algorithm applies to the orthogonal and unitary problems named in Problem 1.8. [Problem 1.8, original statement](https://arxiv.org/html/2604.00591v1#S1.SS5) · [Lean proof of Problem 1.8](https://github.com/Dugongue/MathProofs/blob/main/Problem18-statement-trimmed.lean).

## A false negative from the standard Gram invariant

Over $\mathbf F_2$, take a tensor $A$ supported on the all-zero coordinate tuple, with coefficient 1. A shear sending the first basis vector to the sum of both basis vectors gives an ordinarily isomorphic tensor $B$ with two entries equal to 1. The balanced encoding puts the payload once in its own block and uses fixed gadget coefficients elsewhere. Thus the two encoded tensors have opposite coefficient parity. This is their squared norm in the standard symmetric bilinear form. Orthogonal transformations of the three modes preserve that norm. For example, in order six the compiler produces $363155613939801455$ versus $363155613939801456$ nonzero entries with the geometric tags, and $11278732$ versus $11278733$ with the arithmetically spaced tags. The counts are exact sums of compressed coordinate runs.

## Exact binary solver

Let $Q=\{(1,0),(0,1),(1,1)\}$. Write $T(u_1,\ldots,u_d)$ for contraction of $T$ against these covectors. For a mode $i$ and $u\in Q$, define
$$
h_{i,T}(u)=\#\{(u_j)_{j\ne i}\in Q^{d-1}:T(u_1,\ldots,u_d)=1,\ u_i=u\}.
$$
If $S=(P_1\otimes\cdots\otimes P_d)T$, contracting $S$ at a tuple of covectors equals contracting $T$ at the tuple obtained by applying $P_i^{\mathsf T}$ in each mode. The actions in the other modes merely permute their nonzero covectors, so
$$
h_{i,S}(u)=h_{i,T}(P_i^{\mathsf T}u).
$$
Every genuine transporter survives requiring these three equalities in each mode. There are six local possibilities. Every permutation of $Q$ is induced by an invertible binary $2\times2$ matrix because any two distinct nonzero covectors form a basis, and their sum is the third. The counts are also the degrees of the mode vertices in the colored projective-evaluation graph used by the independent nauty baseline.

The implementation expands each binary coordinate axis into a ternary evaluation axis. Multilinearity gives the third entry of each fiber as the XOR of the first two. The expansion takes $O(3^d)$ work, since each step increases the table size by $3/2$. To compute all marginals, take the three sums along the fastest axis and simultaneously collapse that axis by storing the sum of each triple. Every remaining marginal is preserved by this collapse. The size drops by a factor of three at each step, giving another $O(3^d)$ operations. The experimental executable limits the supported order to fourteen.

To resolve ambiguous signatures, partition the modes into two sets with comparable products of surviving domain sizes. Enumerate one set of effects on $T$, with a hash table keyed by the entire transformed tensor. Enumerate the inverses of the candidate maps from the other set on $S$. A shared tensor is equivalent to an isomorphism since transformations in disjoint modes commute. The hash table compares complete bit vectors. Finally apply the assembled invertible factors to the original tensor and check every coefficient. Exhausting both searches gives a definitive negative answer. The memory limit produces a separate *budget-exhausted* status. The *mitm* ablation uses the same packed implementation and retains all six candidates in each mode.

## Adversarial control

The base pair of order five has coefficient bit masks **0x5D96E218** and **0x95895EFC**, with the least significant bit the first coefficient in C order. Their unordered per-mode tables $h_{i,T}$ agree, and their flattening ranks agree for every bipartition. The reference control exhaustively checks all $6^5=7776$ transformations of the first tensor and confirms the second is absent. Taking the tensor product of both tensors with the same nonzero tensor on additional modes extends the control to orders six, eight, ten and twelve. Corresponding flattening ranks multiply, as do the covector-count marginals for the first five modes. The marginals for the remaining modes match because the full projective weights of the two base tensors agree. A genuine isomorphism of tensor products would give $P(T)\otimes Q(C)=S\otimes C$. Equality of nonzero decomposable tensors forces the first factors to agree up to a scalar, and $\mathbf F_2$ has only one nonzero scalar.

The pair-contraction rank solver has a distinct exact invariant. When two covectors are fixed, the remaining modes act invertibly on both sides of each fixed flattening, so the rank is unchanged after pulling back both covectors. Its pair constraints and repeated local pruning preserve every genuine transporter. All positive outputs are verified on the original coordinates.

## Compact rank tag audit

For the original rank-gadget construction, write $c$ for the old column dimension, $d_i$ for the row-block dimensions, and $t_i>0$ for auxiliary tag dimensions. The rank formula for any nonempty support $I$ of tag coefficients is
$$
c+\sum_{i\in I}(d_i+t_i).
$$
The old slices have rank at most $c$. The old front subspace is therefore an intrinsic low-rank subspace. The compact policy sets $d_i+t_i=b+i$ with $b\ge\max(s,1+\max_i d_i)$, where $s$ is the number of row blocks and $i=0,\ldots,s-1$. The single tags have distinct ranks with offset at most $2b-1$, while every multiple-tag support has offset at least $2b$. These two rank consequences suffice to replace the large geometric tags in the existing subtraction, shear, and quotient-recovery argument. [Lean construction and recovery proof](https://github.com/Dugongue/MathProofs/blob/main/BalancedOrdinaryReduction.lean).

The second property can be weakened to $d_i+t_i>0$ pairwise distinct. Set $\rho(0)=0$ on the quotient by the old front subspace, and define $\rho(q)$ for nonzero $q$ as slice rank minus $c$. The rank formula makes this independent of the lift. Then $\rho(x+y)=\rho(x)+\rho(y)$ holds exactly when the supports of $x,y$ are disjoint. Overlap decreases the sum by at least the positive weight of each overlapping coordinate. Thus the nonzero points of singleton support are exactly those admitting no decomposition into two nonzero vectors attaining equality. Distinct weights identify their named lines. The benchmark timings here use the implemented compact policy. This further reduction in tag size is an informal proof.

## Measurements and scope

[The benchmark driver](solver_transfer_pipeline.py) runs five repetitions of each variant on the same input pair in warmed persistent solver processes, with fixed randomized interleaving. [The raw output](solver_transfer_pipeline_results.json) includes input, source and executable hashes, per-stage wall times, and aggregate medians. File reading, interpreter startup and native launch are outside each pair timing. Each total includes validation, construction of the selected tensor representation when applicable, wire encoding, communication and solving, and independent verification of every positive witness. [Separate controls](solver_transfer_controls.py) give solver-kernel timings and finite checks without compiler costs.

Across 77 shared all-side-two instances and five adversarial pairs, all seven variants agreed with the corpus labels and checked every positive witness. Timings below are median milliseconds on shared known-positive inputs. First take a median across five repeats per case, then take a median across cases.

| Order | Positive cases | Direct MITM | Direct pair ranks | Direct covector counts | Compact balanced + covector counts | Compact half + covector counts | Published encoding + covector counts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 6 | 13 | 0.378 | 0.394 | 0.324 | 5.489 | 5.714 | 0.490 |
| 8 | 10 | 0.819 | 0.728 | 0.462 | 7.268 | 6.903 | 0.769 |
| 10 | 10 | 3.389 | 1.639 | 0.908 | 7.688 | 7.609 | 1.306 |
| 12 | 8 | 37.261 | 5.006 | 2.325 | 9.543 | 9.678 | 3.093 |

The covector filter survives this measured end-to-end accounting. At order twelve, the complete compact balanced run beat tuned direct MITM by about 3.9 times, while the direct covector path was faster than either compiled path. The balanced and half timings are close. On the four shared negative order-twelve cases, totals were 43.855 ms for MITM, 3.531 ms for direct pair ranks, and 1.799 ms for direct covector counts. The pair-rank decision kernel took 0.067 ms, while the covector-count kernel took 0.842 ms. The reported direct totals include each backend’s request parsing and communication costs. Both variants used one persistent process, and total time is the user-facing metric for these adapters.

The compressed pipeline solves the exact leaf-action problem using the product-tree constraints in data it just compiled. Its answer carries to the ordinary encoded tensors by the reduction theorem. Arbitrary three-tensor inputs lack that metadata. A speedup shared by the balanced and half-partition encodings measures the backend improvement. The smaller ambient dimensions of the balanced encoding give a separate space bound. The binary implementation and timings are experimental.
