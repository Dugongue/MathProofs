# Experimental AVX2 backends for MEDS and miniMEDS

These are separate implementation experiments for MEDS and miniMEDS. On an Intel Core i7-10700F running Windows with MinGW GCC 15.2.0, each final candidate beat its own pinned comparison implementation in the stated benchmarks. They are not a universal speed improvement, a new cryptographic security theorem, or a production-ready release.

## Repository contents

- implementations/legacy: corrected historical AVX2 MEDS baseline, hybrid 32-bit row arithmetic candidate, packed-dot control, and differential harness.
- implementations/official: old official MEDS reference and arithmetic candidate for six historical parameters.
- implementations/rectangular: GPL reference fork, packed AVX2 backend, inverse-cancellation variant, and differential harness.
- implementations/minimeds: our added code, exact upstream source lock, source setup script, and differential harness. Upstream miniMEDS files are fetched separately because the inspected upstream commit has no license file.
- proofs: Mathlib-only Lean algebra theorem and independent axiom audit receipt.
- evidence: raw JSONL observations and summaries for the final measured campaigns.
- patches: inspectable MEDS changes relative to their pinned source trees.

Read THIRD_PARTY_NOTICES.md before redistributing. Do not merge these code trees into a single cryptographic API: they are distinct versions and schemes.

## Measured results

Corrected historical AVX2 MEDS baseline versus hybrid candidate; ratio is baseline median divided by candidate median (9 measured trials plus one excluded warm-up per parameter):

| Parameter | Sign | Verify |
|---|---:|---:|
| MEDS13220 | 1.172x | 1.180x |
| MEDS134180 | 1.161x | 1.166x |
| MEDS167717 | 1.160x | 1.173x |
| MEDS41711 | 1.185x | 1.188x |
| MEDS55604 | 1.184x | 1.190x |
| MEDS9923 | 1.171x | 1.175x |

Separate rectangular MEDS result against its portable reference: signing 2.58–3.44x and verification 2.60–3.45x over three levels. Separate miniMEDS result against pinned upstream: signing 1.24–1.31x, verification 1.32–1.53x, and key generation 3.93–6.11x over three levels. The rectangular inverse-cancellation step accounts for only a small fraction of the combined arithmetic speedup. The miniMEDS result does not use that cancellation step. The official MEDS reference arithmetic experiment is yet another baseline, not an extra multiplier for the numbers above.

These are benchmark measurements on one CPU and compiler, not a claim of a fastest implementation on all machines. The parameter names are historical and do not certify current security strength. The miniMEDS authors report 22–24% smaller signatures in their paper; this package does not independently establish a packed wire-size comparison. See evidence/README.md for exact provenance and raw data.

## Build and check

Required: Windows x86-64 with AVX2, Python 3, GCC, and binutils. Set MEDS_CC and MEDS_NM to absolute executable paths if they are not on PATH. Run each command from any directory:

    python implementations/legacy/run.py MEDS13220 2 build hybrid
    python implementations/legacy/run.py MEDS13220 2 build packed
    python implementations/official/run.py MEDS13220 2 build
    python implementations/rectangular/run.py level1 native 2 build
    python implementations/minimeds/setup.py
    python implementations/minimeds/run.py 1 2 build

To use a local pinned miniMEDS checkout without downloading, pass --local-source PATH to setup.py, where PATH contains the ref source files. setup.py verifies each source file against source-lock.json and creates an ignored .deps directory. Never commit .deps; clarify its upstream license before redistributing it. Benchmark harnesses use deterministic test RNG and are not a production signing interface.

The C tests compare outputs, cross-verification, and rejection of modified signatures. Their result files are written in implementation-specific build directories, which are gitignored. Passing tests does not prove C memory safety, constant-time execution, security, or correctness on every input.

## Lean theorem

In proofs/MEDSCancellation.lean, if A*C = P*R, R*B = 1 and P*E = 1 over a commutative ring, then C*B*E is a two-sided inverse of A. This is the algebra used by the rectangular inverse-cancellation candidate. It does not certify the C implementation or the miniMEDS/hybrid arithmetic edits.

Lean 4.33.0 and Mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d are pinned in proofs. From proofs, run:

    lake exe cache get
    lake env lean MEDSCancellation.lean
    lake env lean Audit.lean

The packaged source was checked with the pinned cached Mathlib on 2026-09-19; the audit reports only propext, Classical.choice, and Quot.sound. See proofs/packaged-verification.json.

## Corrected baseline

The historical AVX2 code required three correctness repairs applied identically to both arms before comparison: mask the final row load; bound rectangular identity initialization by row count; and return before consuming an inverse after failure. The earlier reported 14–22% slowdown figures for the packed replacement were based on the unrepaired baseline and are superseded. The corrected packed control and hybrid evidence are included. No claim is made that the existing broadcast AVX2 kernel is our invention.
