# Controller runtime proofs for ordinary even-order tensor isomorphism

These checked modules extend the fixed-finite-field solver and reuse the existing MathProofs implementations of Problems 1.7 and 1.8, prior even-order TI proofs, and their original attributions.

- The capped coefficient scan retains a shared basis and emits a complete block at each visited code.
- The per-code command constructs and emits exact dense form words.
- A binary machine constructs the entire coefficient-indexed form list, including zero, for a selected cut within the cap. The program emits no records if the cap fails.
- A paid row update implements the exact elementary multiplication used by order-four normalization.
- A paid Gaussian pass clears a pivot column across the whole augmented matrix.
- The reciprocal anchor computation preserves the cut banks for subsequent modes.
- The reciprocal-trial header emits the exact tag, payload length and anchor count.
- The request parser opens both trial anchor lists and form sections from the preserved raw pair request.
- The paid seek finds a supplied anchor index using the literal block lengths.
- The scalar probe loop visits the prescribed coordinates on live CRT banks.
- A paid chart product connects installed matrix data to the scalarity test.
- The complete raw request front end initializes the field workspace. The serialized request size has a checked polynomial bound in the original dense pair bits.
- A selected anchor is decoded from the raw request directly into native field slots.
- The selected serialized anchor is loaded and its characteristic polynomial is computed by the checked Problem 1.7 routine.
- Under the checked chart invariance and coordinate map, homogeneous scalarity is equivalent to equality of the active residue words.
- The exact scalar test on an installed matrix packet runs with private input and output arrays and preserves the host state.
- A reciprocal visit computes and emits the literal anchor block, preserves the protected cut banks, and admits a polynomial bound for all mode visits.
- The two concrete reciprocal passes emit every anchor in the reference order from installed cut and inverse banks.
- The installed reciprocal banks produce the exact complete serialized trial record, including its header and both anchor passes.
- From the serialized tensor pair, two prepared trials and one index, the checked program computes the selected anchor characteristic polynomial in the live coefficient bank.
- A selected anchor reaches the checked full factor archive using the prepared caller memory layout.
- The paid active-slot scan decides residue equality while preserving every array and both tapes.

The full fixed-field theorem still requires the complete raw trial-record producer, the singular order-four branch and the execution of the full scalar and recovery controllers. Statements on prepared or live internal banks state those assumptions explicitly.

## Newly checked modules

- `EvenP15ScalarStorage`
- `EvenP16RecoverCrop`
- `EvenP17ExecutionCells`
- `EvenP17ReciprocalRecord`
- `EvenP17ReciprocalTrial`
- `EvenP17ReciprocalVisit`
- `EvenP17RecoverAnchorLoad`
- `EvenP17RecoverArchive`
- `EvenP17RecoverCharpoly`
- `EvenP17RecoverCharpolyGate`
- `EvenP17RecoverDigitWindow`
- `EvenP17RecoverFormLoad`
- `EvenP17RecoverFront`
- `EvenP17RecoverRawCharpoly`
- `EvenP17RecoverSeek`
- `EvenP17RecoverWindows`
- `EvenP17RowTransvection`
- `EvenP17ScalarActiveCrop`
- `EvenP17ScalarActiveLoop`
- `EvenP17ScalarActiveRead`
- `EvenP17ScalarActiveSlotVisit`
- `EvenP17ScalarActiveWords`
- `EvenP17ScalarChartSink`
- `EvenP17ScalarIsolatedWord`
- `EvenP17ScalarProbeLoop`
- `EvenP17ScalarProbeVisit`
- `EvenP17ScalarRouted`
- `EvenP17ScalarSelfMeaning`
- `EvenP17TransposeSlots`
- `EvenP17TrialBlockScan`
- `EvenP17TrialCapturedFilter`
- `EvenP17TrialFormVisit`
- `EvenP17TrialRawForms`
- `EvenP17TrialRawFormsBinary`
- `EvenP17TrialReciprocalSweep`
- `EvenP17TrialRoutedForms`
- `EvenP17TrialTwoCapturedCuts`
