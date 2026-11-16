# Reingold reader on Lean 4.33

The `Complexity` modules are the dependency closure of the undirected connectivity reader from Samuel Schlesinger and contributors to CSLib Frontier, at revision `51c60ccb7f1e0143470b487cc059c0cb307db3c2`. The original closure and license were matched to that revision. The redistributed sources retain the upstream authorship notices. [CSLib Frontier](https://github.com/cslib-community/cslib-frontier/tree/51c60ccb7f1e0143470b487cc059c0cb307db3c2) · [Apache 2.0 license](LICENSE-CSLIB-FRONTIER.txt) · [Notice](NOTICE-CSLIB-FRONTIER.txt)

The port updates the Mathlib import in `Quantile` and adapts conditional rewrites in `Connected`, `SlotGraph`, and `Reader.Correct`. It trims `Reader.Invariant` to the invariant needed by the addressed reader. The bundle pins the same Mathlib and CSLib revisions used to check the port.

The MathProof adapter invokes the actual upstream reader with a generated cell source on each input request. Its correctness and encoded-state bounds apply before composing the reader with the physical signed-generator callback. The binary machine that performs that composition from a raw Cayley table remains to be checked. [Adapter](Mathproof/MinimumGenerationReingoldNative.lean)
