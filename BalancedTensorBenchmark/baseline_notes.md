# Independent exact reference solvers

The two adapters start from the original tensor pair. They use established external solvers with independent encodings of the general-linear action over GF(2). Positive witnesses are checked directly against the original tensor. The benchmark harnesses preserve timeouts as unresolved attempts.

## Traces from nauty 2.7r1.p1

[McKay–Piperno, Practical Graph Isomorphism, II](https://doi.org/10.1016/j.jsc.2013.09.003) and the [nauty/Traces manual](https://users.cecs.anu.edu.au/~bdm/nauty/nug27.pdf) describe the external canonical-labeling solver. The tested executable is the one bundled with SageMath 9.3 for Windows. Supply the executable directly with '--dreadnaut' or the extracted runtime root with '--runtime'.

For each mode of an order-d tensor with every side two, put the three nonzero covectors of GF(2)^2 in a separate color class. Add one support vertex of another color for every ordered pure covector tuple at which the tensor evaluates to one. Join a support vertex to the chosen covector vertex of each mode. Any tuple of invertible binary 2×2 matrices produces a graph isomorphism under its dual action. Conversely, a color-preserving graph isomorphism gives an arbitrary permutation of each mode's three covectors. The faithful action of GL(2,2), of order six, is all of S3. Hence those permutations induce linear maps. Graph isomorphism preserves every one position and every zero position in the evaluation transform. Those pure covectors include the standard coordinate basis, so the induced tensor action is the required general-linear isomorphism. The adapter decodes the covector correspondence as an inverse transpose and verifies the result on the original tensor.

The corpus run used 77 input pairs and three repeats. All 231 reported decisions matched their independently established or planted labels. The run uses a persistent external process and accounts for warm startup separately. Per-case time includes input reading, graph construction, serialization and pipe transfer when needed, full graph comparison, and witness verification. Different support cardinalities give an immediate rigorous negative decision after graph construction. The row-level ledger records which inputs reached the graph solver and includes its own coarse CPU timer.

| Tensor order | Cases | Median end-to-end wall, ms |
| --: | --: | --: |
| 3 | 4 | 0.690 |
| 4 | 12 | 0.849 |
| 6 | 19 | 4.365 |
| 8 | 15 | 47.244 |
| 10 | 15 | 577.698 |
| 12 | 12 | 7262.416 |

## CaDiCaL 2.1.2

The second adapter uses the release of [CaDiCaL](https://github.com/arminbiere/cadical) bundled with Lean 4.33.1. For each input mode it allocates an independent invertible matrix, enforcing determinant one in dimensions at most three and existence of an inverse matrix at larger dimensions. Binary mode transforms are AND/XOR circuits with exact Tseitin constraints. The final bits must equal the target tensor, so satisfiability is equivalent to tensor isomorphism. SAT witnesses are reconstructed and verified with independent binary matrix arithmetic. An UNSAT verdict comes from the external solver.

The fixed sample includes 28 distinct corpus cases across nine formats, including sides three. It returned 64 completed repeat decisions and seven timeout attempts at a two-second per-process cap. The median completed end-to-end times range from 17.5 ms for the smallest shape to 1.80 s at order ten. The per-case ledger records the formula size, time spent on formula production, solver process wall time, and witness verification time. Each CaDiCaL attempt starts a fresh native process. Small-case timings include that startup cost.

These are end-to-end comparisons against exact adapters for a general graph-isomorphism solver and a general SAT solver. The results depend on these encodings, the specific solver builds, their startup conventions, and the finite corpus. They give measured baselines for this implementation.

## Isolating the effect of the balanced grouping

For either layout partition the input modes into three contiguous groups. On an active group, evaluate at each tuple of nonzero local covectors. Regard each resulting tensor in the other two groups as a matrix, and record the rank of each of these matrices as an indexed table. Any tensor isomorphism preserves these ranks and relabels table indices by the independent dual maps in the active group. The code first filters maps by conditional histograms, which are preserved by this relabeling. It then checks the complete rank table against each candidate tuple of maps. A group with no surviving candidate forces nonisomorphism. If each group has a unique candidate, their product is the only possible witness and can be tested on the original pair. If some group remains ambiguous, the algorithm uses the same exact direct-rank search for both layouts.

The measured pipeline reads the original pair, builds the sparse ordinary coordinate encoding, extracts the payload using the encoder's tags, applies this backend for the selected grouping, and independently verifies positive witnesses. The half-style control uses the same implementation and rank tags with group sizes floor(d/2), d−floor(d/2)−1, and 1. One warm worker per grouping ran all 77 equal-side-two inputs at seven repeats, with randomized interleaving. All 1,078 verdicts matched. Median times below include file reading, sparse compilation, communication, decisions, and verification. The fallback columns count unique cases.

| Order | Cases | Balanced wall, ms | Half-style wall, ms | Balanced fallback cases | Half-style fallback cases |
| --: | --: | --: | --: | --: | --: |
| 3 | 4 | 3.39 | 3.40 | 4 | 4 |
| 4 | 12 | 3.98 | 3.97 | 8 | 8 |
| 6 | 19 | 4.78 | 4.79 | 9 | 12 |
| 8 | 15 | 5.79 | 5.89 | 10 | 13 |
| 10 | 15 | 7.19 | 7.51 | 10 | 15 |
| 12 | 12 | 9.61 | 11.77 | 0 | 12 |

At order 12, the median measured native algorithm times were 0.82 ms and 2.84 ms. The wall result is a 1.22× speedup for the balanced layout on those twelve inputs. The backend never fell back in the 84 balanced repetitions, and it fell back on all 84 half-style repetitions. Both arms use the same sparse tag representation. The older grouping is a controlled change of group sizes, using this project's compiler for both arms.

For the warm graph baseline, run 'python baseline_benchmark.py --runtime <Sage runtime root> --output baseline_traces_results.json'. For the SAT sample, run 'python baseline_benchmark_sat.py --cadical <CaDiCaL executable> --output baseline_cadical_results.json'. To reproduce the isolated comparison, compile 'g++ -O3 -std=c++20 baseline_group_rank.cpp -o baseline_group_rank.exe' and run 'python baseline_benchmark_group_rank.py --executable baseline_group_rank.exe --output baseline_group_rank_pipeline.json' from the benchmark root after installing NumPy. The grouped benchmark imports the shared 'pipeline.py' and 'encoder.py' and includes the shared 'native_ti.cpp' for its exact fallback.
