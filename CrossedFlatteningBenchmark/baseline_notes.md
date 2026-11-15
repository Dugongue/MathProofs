# Reference solvers and exact witness checks

The baseline adapters take the original tensor pair. No basis change used to produce a planted comparison is passed to a solver. Each pair is a JSON object with keys 'id', 'field', 'dims', 'src' and 'dst'. The field is a prime integer or the string 'Q'. Entries are flat row-major arrays. Rational inputs use integers or exact fraction and decimal strings.

A positive answer includes one matrix per mode, in the original axis order. Every solver witness is checked for nonsingularity and applied directly to the source tensor using exact arithmetic. A negative answer comes from an exact invariant or a sound unsatisfiability result. An unresolved attempt stays 'unknown'.

## CaDiCaL and Z3

The direct encoding partitions the tensor modes in half. It applies invertible variables to the source on the first half and to the target on the second half, then equates the arrays. A solution to this equation yields the source-to-target maps by inverting the target-side matrices. For four modes the tensor equations are quadratic. Each variable matrix is constrained to be invertible by a determinant condition or by an explicit inverse. This is an independent adapter for established solver engines. It uses no crossed covariants.

The binary encoding uses exact Tseitin definitions for XOR and AND. The native build used in the benchmark reports CaDiCaL 2.1.2. The Z3 adapter uses bounded bit-vector arithmetic for prime fields and nonlinear real arithmetic for Q. Its build reports Z3 5.4.1. On Q, a real UNSAT result gives a rational no, and a real model provides a yes only when exact rational matrices verify. An algebraic model with non-rational entries stays unresolved. Before invoking an engine, the adapter can rule out pairs by exact flattening ranks. [CaDiCaL](https://github.com/arminbiere/cadical) · [Z3](https://github.com/Z3Prover/z3)

For an executable path held in the PowerShell variable '$Cadical', the two CLI forms are

    python baseline_external.py --backend cadical --executable $Cadical --timeout 10 pair.json
    python baseline_external.py --backend z3 --timeout 10 pair.json

The Z3 binding can be installed with 'python -m pip install z3-solver==5.4.1.0'. The driver reports parsing, rank-filtering, encoding, solver launch and completion, and exact verification separately when applicable. The paired cold benchmark measures both adapters with the surrounding caller wall clock. CPU or solver time on its own does not include process and input overhead.

## Rational witness search by modular lifting

The 'hensel' adapter starts from an exact CaDiCaL model modulo two. It fixes a scalar gauge for the first three modes and applies Jacobian corrections to the tensor polynomial equations modulo increasing powers of two. At selected precisions up to 64 bits it rationally reconstructs the candidate and verifies it against the original tensors over Q. A failed binary search, nonlifting seed or unsuccessful rational reconstruction is recorded as an unresolved attempt. Its exact no filter is the same flattening-rank test. The adapter was written for this benchmark and does not claim completeness over Q.

    python baseline_external.py --backend hensel --executable $Cadical --timeout 10 pair.json

## Published corank-three method

The binary reference implementation follows the algorithm in Section 4 of Li, Li, Qiao, Tao and Wang. It forms the two matrix codes from the left and right kernels of a balanced flattening. If the common corank is three, it searches for invertible kernel-code matrices, enumerates target code bases, solves the corresponding tuple intertwiners and checks the product of the two resulting transporter lists. It enforces the published limit on pointwise stabilizer size. The implementation declines with an explicit code-space enumeration cap if the dimension of a centralizer exceeds 14. The optional all-cuts mode repeats the procedure on all three balanced partitions. The paper's fixed-cut procedure is the default. [Published 4-TI algorithm, Section 4](https://arxiv.org/html/2604.00591v2#S4)

    python baseline_corank.py --timeout 2 pair.json
    python baseline_corank.py --timeout 2 --all-cuts pair.json

The per-pair ledger covers 33 published-data binary comparisons. The fixed cut and all-cut versions each returned 11 negatives by exact flattening ranks and declined 22 pairs. No measured positive pair reached a successful witness in this particular sample. Controls separately found exact witnesses on 16 of 30 planted binary corank-three examples, declined the other 14, and gave one exact same-main-rank negative. The control inputs were generated for algorithm verification. [Pair-level ledger](baseline_corank_results.json)

The published Magma TensorSpace implementation requires a local Magma installation. The reports give no Magma timing. [TensorSpace repository](https://github.com/thetensor-space/TensorSpace)
