# LinearToSemilinearCodeEquivalence

See [PROOF.md](PROOF.md) for the complete informal argument and exact scope, and [ATTRIBUTION.md](ATTRIBUTION.md) for credits and status.

Run the included exact finite checks with Python 3.10 or newer:

```text
python verify_reference_stabilizers.py
python verify_wrapper.py
```

The scripts work from any current directory and write their JSON receipts beside themselves. They require no third-party packages. Finite checks supplement the written proofs; these are not Lean certificates.
