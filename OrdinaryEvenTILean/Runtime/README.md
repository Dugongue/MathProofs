# Binary runtime components for ordinary even-order tensor isomorphism

This Lean source update extends the ordinary even-order tensor isomorphism formalization over each fixed finite field.
It reuses the verified Problem 1.7 and Problem 1.8 machine libraries and the earlier Lean development, including Claude’s callback and tensor encoding work.

- The comparison controller runs a serialized trial callback and returns the first successful transporter.
- The recognition controller preserves the original input and runs the second gate only after success of the first.
- The count-query controller sends the exact comparison input and preserves the context used to emit the queries.
- The count-result controller normalizes the comparator result and answers to a fixed-field convolution table. The convolution and the singleton-answer classifier have binary polynomial-time proofs.
- The retained-mode rank program loads a flattening from the original dense field slots, then executes the exact rank test.
- The assembly wires the verified controllers into the unchanged solver contract, given binary time bounds for the exact remaining word-level routines.
- The actual right-cut kernel machine loads either dense input block from its original field labels and returns a checked spanning basis.
- Truncated polynomial determinant recursion recovers the entire characteristic polynomial, including repeated spectra. This theorem certifies the algebraic recursion.
- The exact serialized count-query driver has a binary polynomial-time proof given the comparator runtime.
- The exact serialized count-result driver has a binary polynomial-time proof given the comparator runtime.

The unconditional theorem still needs end-to-end binary time proofs in recognition, comparison.

Build dependencies include the earlier ordinary even-order modules, the local Problem 1.7 and Problem 1.8 libraries, and Mathlib.

## Checked modules

- `EvenP12CompareAssembly`
- `EvenP12CompareBankLoad`
- `EvenP12CompareBasisIndependent`
- `EvenP12CompareDigitLoad`
- `EvenP12CompareLeftKernel`
- `EvenP12CompareNativeScan`
- `EvenP12CompareRawLayout`
- `EvenP12CompareRetainedLayout`
- `EvenP12CompareRightKernel`
- `EvenP12CompareSelector`
- `EvenP12CompareSmithCoordinate`
- `EvenP12CompareSmithSweep`
- `EvenP12CountPostAssembly`
- `EvenP12CountPostBanks`
- `EvenP12CountPostClassify`
- `EvenP12CountPostEmitGrid`
- `EvenP12CountPostGate`
- `EvenP12CountPostGrid`
- `EvenP12CountPostLoop`
- `EvenP12CountPostMachine`
- `EvenP12CountPostNormalize`
- `EvenP12CountPostPadding`
- `EvenP12CountPostRoute`
- `EvenP12CountPostRow`
- `EvenP12CountPostRuntime`
- `EvenP12CountPostSource`
- `EvenP12CountPostSuccess`
- `EvenP12CountPreAssembly`
- `EvenP12CountPreDispatcher`
- `EvenP12CountPreEmit`
- `EvenP12CountPreFrame`
- `EvenP12CountPreHeaders`
- `EvenP12CountPreInput`
- `EvenP12CountPreModes`
- `EvenP12CountPreOneQuery`
- `EvenP12CountPrePayload`
- `EvenP12CountPrePrefix`
- `EvenP12CountPreRoute`
- `EvenP12CountPreSegments`
- `EvenP12CountPreTape`
- `EvenP12RecognizeAnyTrial`
- `EvenP12RecognizeAssembly`
- `EvenP12RecognizeBudget`
- `EvenP12RecognizeGuardMachine`
- `EvenP12RecognizeGuarded`
- `EvenP12RecognizeLoadRank`
- `EvenP12RecognizeRankLoad`
- `EvenP12RecognizeRetainedRank`
- `EvenP12RecognizeSchur`
- `EvenP12RecognizeTruncated`
- `EvenP12RuntimeAlgebra`
- `EvenP12RuntimePorts`
