# Executable proof components for ordinary even-order tensor isomorphism

This update extends the fixed-finite-field solver development. It reuses the previous MathProofs runtime proofs, Problem 1.7, Problem 1.8, and the earlier Claude contributions to the tensor and word-codec development.

- Step 1 has a binary polynomial-time proof for the exact spectral pair projection on arbitrary input words.
- Step 2 sizes the four cut banks from the original input bits and executes the shared cut initializer at the resulting bound. The decoded-input runner derives the array allocations directly from the raw input.
- The installed cut bases have the proved form membership used by the trial provider.
- Step 3 runs cut-form enumeration from the original tensor words. The checked order-four nonzero and higher-order rank-filtered scans emit the coefficient indices for exactly the eligible forms. This interface supplies the candidate codes for trial serialization.
- Step 7 runs the full coordinate recovery on the live padded system, including empty systems and inconsistent right-hand sides. The output agrees with the reference solver and the cost has a fifth-degree word-operation bound.

The final theorem remains conditional on the binary trial producer, scalar callback, and full comparison attempt. The precise verified runtime interfaces are given in the Lean statements.

The earlier checked runtime files accompany this update. The sources use the existing ordinary even-order TI, Problem 1.7, and Problem 1.8 environments.

## Newly checked modules

- `EvenP12CompareLiveCRTDot`
- `EvenP12CompareLiveCRTFrame`
- `EvenP12CompareLiveCRTInstall`
- `EvenP12CompareLiveCRTMachine`
- `EvenP12CompareLiveCRTPadding`
- `EvenP12CompareLiveCRTRow`
- `EvenP12CompareLiveCRTScan`
- `EvenP12CompareLiveCRTStep`
- `EvenP12CompareLiveCRTTable`
- `EvenP12ComparePrepCoeffDigits`
- `EvenP12ComparePrepDecodedCut`
- `EvenP12ComparePrepFourBudget`
- `EvenP12ComparePrepTrialProvider`
- `EvenP14CRTComplete`
- `EvenP14CRTConstraints`
- `EvenP14CRTCoordinate`
- `EvenP14CRTEmpty`
- `EvenP14CRTLoop`
- `EvenP14CRTLoopCost`
- `EvenP14CRTLoopStore`
- `EvenP14CRTPositive`
- `EvenP14CRTProbe`
- `EvenP14CRTReference`
- `EvenP14CutCandidate`
- `EvenP14CutChoiceCap`
- `EvenP14CutCoeffInstall`
- `EvenP14CutDot`
- `EvenP14CutNonzero`
- `EvenP14CutProviderAssembly`
- `EvenP14CutRankConfigure`
- `EvenP14CutRankControl`
- `EvenP14CutRankFrame`
- `EvenP14CutRankInit`
- `EvenP14CutRankLayout`
- `EvenP14CutRankMeaning`
- `EvenP14CutRankOne`
- `EvenP14CutRankSweep`
- `EvenP14CutRawBudget`
- `EvenP14CutRawClock`
- `EvenP14CutRawNonzero`
- `EvenP14CutRawRank`
- `EvenP14CutRawRankClock`
- `EvenP14CutRawSetup`
- `EvenP14CutRecombine`
- `EvenP14CutRunLift`
- `EvenP14CutScan`
- `EvenP14CutScanBudget`
- `EvenP14CutScanEngine`
- `EvenP14CutScanMeaning`
- `EvenP14CutScanRank`
- `EvenP14CutScanSetup`
- `EvenP14CutVisit`
- `EvenP14ProjectionEngine`
- `EvenP14ProjectionReplay`
- `EvenP14ProjectionWindow`
- `EvenP14TrialExecutionRoot`
