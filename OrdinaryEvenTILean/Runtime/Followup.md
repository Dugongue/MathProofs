# Binary runtime follow-up for ordinary even-order tensor isomorphism

This Lean update concerns the ordinary even-order tensor isomorphism theorem over each fixed finite field. The listed modules passed Lean with the earlier project dependencies. They reuse the existing Problem 1.7 and Problem 1.8 machine proofs, the two oriented cut kernels, the checked Smith certificate, and Claude’s earlier tensor and callback work.

- The spectral evaluator reads a serialized anchor matrix, initializes its field workspace, and computes the exact characteristic-polynomial repeated-factor budget within a polynomial RAM bound. The complete single-anchor binary machine also checks malformed input and agrees exactly with the shared solver on all numbered anchors. Its binary cap test uses bounded repeated division. A verified packed scan reuses pre-attempt comparison requests through the self-pair diagonal. The two projections of the length-prefixed pair codec have binary polynomial-time proofs on arbitrary inputs.
- Comparison initialization reads and validates the raw tensor words and supplies the field arithmetic workspace. The cut programs compute and preserve all four kernel bases, one for each orientation of each input tensor. The checked RAM cost is polynomial in the original input length.
- The scalar scan works with any complete cut-kernel basis. The spectral gate implies retained full rank, eliminating a separate rank scan. The scalar assembly takes a paid preparation and trial callback.
- The recovery proof uses one Smith call per coordinate and reads the diagonal and row-transform banks of the actual Smith machine. Checked extended-gcd and unary congruence programs return the coefficients used by modular recovery. One checked Smith call also supplies the scalar cap test from diagonal and row-transform entries. Character recovery is invariant on feasible input under the choice of a valid extension.

The earlier checked runtime modules are included in this upload. The sources use the existing ordinary even-order TI, Problem 1.7 and Problem 1.8 Lean modules.

The end-to-end theorem still depends on the binary runtime for the full recognition function and the full comparison preparation and recovery routines. The checked shared assembly supplies the binary anchor evaluator and still takes the nested trial-framing bridge as a premise. Both counting endpoints use the same established comparison machine.

## Modules

- `EvenP12ComparePrepBounds`
- `EvenP12ComparePrepCodecPair`
- `EvenP12ComparePrepCut`
- `EvenP12ComparePrepField`
- `EvenP12ComparePrepFour`
- `EvenP12ComparePrepInit`
- `EvenP12ComparePrepKernel`
- `EvenP12ComparePrepKernelLayout`
- `EvenP12ComparePrepNativeRoot`
- `EvenP12ComparePrepPairPlan`
- `EvenP12ComparePrepRaw`
- `EvenP12ComparePrepShape`
- `EvenP12ComparePrepSpectral`
- `EvenP12CompareRecoverBezout`
- `EvenP12CompareRecoverCap`
- `EvenP12CompareRecoverCharacters`
- `EvenP12CompareRecoverLinear`
- `EvenP12CompareRecoverPhysUnary`
- `EvenP12CompareRecoverSmithRun`
- `EvenP12CompareRecoverUnary`
- `EvenP12ScalarDriver`
- `EvenP12ScalarPackedAll`
- `EvenP12ScalarProbe`
- `EvenP12ScalarSelfPair`
- `EvenP12ScalarSemantics`
- `EvenP12ScalarSpectralDriver`
- `EvenP12ScalarSpectralRank`
- `EvenP13SharedTrialRuntime`
- `EvenP13SpectralAnchor`
- `EvenP13SpectralAnchorAgree`
- `EvenP13SpectralAnchorBody`
- `EvenP13SpectralAnchorCore`
- `EvenP13SpectralAnchorDigits`
- `EvenP13SpectralAnchorIO`
- `EvenP13SpectralAnchorLayout`
- `EvenP13SpectralAnchorLoad`
- `EvenP13SpectralAnchorMachine`
- `EvenP13SpectralAnchorRaw`
- `EvenP13SpectralAnchorShape`
- `EvenP13SpectralDivision`
- `EvenP13SpectralRoute`
- `EvenP13SpectralScore`
- `EvenP13SpectralSum`
