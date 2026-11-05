# Attribution and reproducibility

This is AI-assisted MathProofs work. The complete informal proof has three
separate internal AI reviews; independent human validation, publication priority
and Lean formalization remain pending. No first-publication claim is made.

The proof credits Gross and Van den Nest's classical minimal-support and
semi-Clifford results, Zhang's recent graph-state and k=1 code algorithm,
Wang and Krastanov's local-projector propagation method, Bichmann, Schmid and
Wille's code-equivalence study, and Webster, Quintavalle and Bartlett's
diagonal-operator machinery. Full citations and links are in PROOF.md.
The known 27-qubit configuration is prior work, not a new counterexample here.

To replay the exact diagnostics with Python 3.10 or newer:

```powershell
python -m pip install -r requirements.txt
python controls.py
python full_controls.py
python branch_controls.py
python modular_controls.py
python known27_control.py
python traced25_control.py
python code_flags_check.py
```

Run these from this directory. They rewrite their corresponding JSON receipts;
timings may vary. Small-case exhaustive enumeration is part of the test oracle,
not the claimed polynomial theorem algorithm. Successful finite checks do not
replace the universal proof. SymPy is a dependency and is not vendored here.
No external Lean library or upstream paper source code is bundled.
