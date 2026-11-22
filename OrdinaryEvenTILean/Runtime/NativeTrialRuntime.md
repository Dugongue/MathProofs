# Native trial runtime proofs for ordinary even-order tensor isomorphism

These checked modules extend the fixed-finite-field solver and reuse the existing MathProofs implementations of Problems 1.7 and 1.8, prior even-order TI proofs, and their original attributions.

- From an installed nonsingular cut, the composed program computes the inverse, initializes constants, and produces the exact anchor for one supplied retained mode.
- The paid inverse produces the reciprocal in the same mixed-radix coordinate order used by the anchor routines.
- The complete reciprocal anchor is computed from its installed cut and inverse banks by a crossed contraction, square, and diagonal-block trace.
- The composed square and trace programs install every anchor entry and preserve the computed square and other protected field slots.
- The crossed, square and trace calculation has an explicit polynomial bound in the original dense input bits.
- The higher-order form emitter converts native cut order to the exact public field-word output by a verified mixed-radix reversal.
- The paid retained projection installs the exact coefficients in their native cut order, sharing the original candidate bank.
- The checked matrix product and shuffle identify the full higher-order covariant contraction from live matrices.
- The original chart site is recovered by two actual Problem 1.8 matrix products, with exact width casts.
- The recovery emitter produces the literal forward matrices and stabilizer-count word, including the failure packet.
- Over an extension of a fixed q-element field, the bounded-root pass reuses the framed kernel routine for the linearized equation x^q = u x.
- The scalar test consumes an installed field matrix directly and preserves the surrounding caller state.
- The scalar probe controller runs the live constraint reset, prefix installation, feasibility check, and CRT continuation in the same banks.
- The compiler word length is polynomial in the original bits even for the large integer exponent used by the paid inverse.
- From the literal balanced tensors and a single admitted coefficient index, the selected-form program computes and emits the exact form with an original-input polynomial IMP step bound.
- The admitted-index selected-form program compiles to a finite binary machine.
- The alternate Frobenius recovery procedure has the full correctness and coverage contract required by the outer solver.
- The paid multiplication and power operations build the Frobenius kernel column and run the root solver in the same field workspace.

The full fixed-field theorem still requires the raw trial producer and execution of the complete scalar and comparison controllers. Statements on prepared or live internal banks state those assumptions explicitly.

## Newly checked modules

- `EvenP15ScalarActiveDiagonal`
- `EvenP15ScalarBaseUnits`
- `EvenP15ScalarKernelRow`
- `EvenP15ScalarLabelVector`
- `EvenP15ScalarLabels`
- `EvenP15ScalarLoadedMatrix`
- `EvenP15ScalarProbeCheck`
- `EvenP15ScalarProbeDriver`
- `EvenP15ScalarProbeReset`
- `EvenP15ScalarProbeRows`
- `EvenP15ScalarProbeSuffix`
- `EvenP15TrialAnchorProduct`
- `EvenP16AnchorCosts`
- `EvenP16AnchorCrossGrid`
- `EvenP16AnchorCrossMeaning`
- `EvenP16AnchorSquareTrace`
- `EvenP16AnchorTraceGrid`
- `EvenP16AnchorUnits`
- `EvenP16AnchorWordClock`
- `EvenP16DigitAddress`
- `EvenP16FrobeniusControllerRoot`
- `EvenP16InvertCutBank`
- `EvenP16ReciprocalAnchorGrid`
- `EvenP16ReciprocalFullCell`
- `EvenP16ReciprocalSquare`
- `EvenP16RecoverChartProduct`
- `EvenP16RecoverFrobeniusAttempt`
- `EvenP16RecoverFrobeniusRoot`
- `EvenP16RecoverOutput`
- `EvenP16RecoverRootAssembly`
- `EvenP16RecoverRootChoice`
- `EvenP16TrialAnchorEmit`
- `EvenP16TrialContractionMeaning`
- `EvenP16TrialContractionProducts`
- `EvenP16TrialCrossShuffle`
- `EvenP16TrialFormInit`
- `EvenP16TrialHigherEmit`
- `EvenP16TrialNativeProjection`
- `EvenP16TrialNativeProjectionMeaning`
- `EvenP16TrialProjectionFormula`
- `EvenP16TrialProjectionGrid`
- `EvenP16TrialRawForm`
- `EvenP16TrialRawFormBinary`
- `EvenP16TrialRawFormClock`
- `EvenP16TrialRectangular`
- `EvenP16TrialRectangularCall`
- `EvenP16TrialReverseDigits`
- `EvenP16TrialTraceLast`
