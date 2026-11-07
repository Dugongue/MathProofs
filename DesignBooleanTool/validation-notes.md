# Independent validation notes

Version 0.2 passes 34 unittest methods and three checkpoint-transport tests. The suite includes all eight shipped fixtures, label permutations, native/Python dispatch, dense and packed input, typed element buffers, Unicode JSON round trips, malformed inputs, resource caps and certificate corruption. These are test-method counts, not counts of all input instances.

An exhaustive structured check covers all 65,536 four-variable truth tables converted to normalized-rank-pass candidate incidence matrices: native certificate-first, native explicit and Python agree with independent Walsh expectations computed from truth-mask Hamming distances. There are 896 recognized cases and 64,640 rejections. This does not enumerate all binary incidence matrices. See tests/exhaustive-results.json.

The independent checker derives Walsh coefficients by direct character sums and verifies every incidence entry, the coordinate bijection, exact support/sign correspondence and affine span. Actual upstream M4RI rank arithmetic passed 110 separate validation cases. Fifteen positive Sage outputs were independently checked after timing. The GAP wrapper verifies positive outputs before checkpoint acceptance; transport tests cover timeout preservation, resume and changed-contract rejection.

Full pipelines were benchmarked against actual Sage 9.3/M4RI, upstream M4RI 20260122 with independent reconstruction, and GAP 4.16.1/ DESIGN 1.8.2. Eleven Sage/M4RI-adapter cases and ten GAP cases completed. A prior 11-case GAP job exceeded a 600-second overall deadline; no per-call lower bound is inferred. Startup-inclusive CLI measurements include a small-input slowdown. See benchmarks/README.md for versions, raw samples and limitations.

The offline source-containing wheel, isolated installation, explicit native compilation and recognition from an unrelated directory were tested. No external runtime or compiled native binary is bundled in the publication source. The certificate-first design implication is proved informally in VALIDATION-THEOREM.md and independently reviewed. Neither this executable nor that new informal argument is Lean-kernel verified.
