# Two consequences of cross-branch mathematical research

These are complete informal arguments, not Lean certificates. Four-worker audits checked the proofs; publication priority and external peer review remain unconfirmed.

- [Complex Hanner inequality](HANNER.md): the full reverse Steinhaus inequality for arbitrary finite families of complex Lp functions, 1 ≤ p ≤ 2, using a positive-semidefinite regularized Hessian. This addresses the missing range explicitly stated by Jenkins and Tkocz.
- [Loewy-length counterexample](LOEWY.md): a connected principal block of the characteristic-2 A5 group algebra has a J-preorder witness through the Klein-four group algebra, but their Loewy lengths are 5 and 3. This refutes Jonsson's Conjecture 43. Tensor powers give an unbounded additive discrepancy.
- [Stronger equivalence supplement](LOEWY-EQUIVALENCE-SUPPLEMENT.md): an exact finite computation supplies the reverse preorder witness as well, giving connected J-equivalent algebras with unequal Loewy lengths. The main refutation does not depend on this supplement.

[Audit and attribution](AUDIT.md) distinguish prior results, the new arguments, numerical diagnostics, and exact finite checks.

## Reproducing the computations

With Python 3.10 or newer, run from this directory:

```console
python tools/verify_a5_radical.py
python tools/check_hanner.py
```

Both programs use only the Python standard library and write their result JSON beside themselves. The group-algebra calculation is exact over finite fields. The Hanner calculation is a floating-point diagnostic; the universal proof is analytic and does not rely on it.

The original text and code in this folder are supplied under the Apache License 2.0. Prior mathematical results remain attributed to their authors; no external proof source code is reproduced here.
