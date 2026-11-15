# Cayley-table input and quotient access for Question 8.1

This collection extends the checked Lean components for minimum-generator search on arbitrary finite Cayley-table groups. The target `Mathproof.MinimumGeneration.CayleyMinimumGeneratorSearch` specifies a finite-control transducer with read-only input, write-only output, and logarithmic workspace. The proof of that target is currently informal. [Question 8.1](https://arxiv.org/html/2402.00133#S8)

| Roadmap step | Lean 4.33 results in this bundle |
|---|---|
| 1. Table input and output | The unary order header, multiplication entries, identity and inverses are decoded exactly from the binary input. Includes register-width bounds for entry reads and a finite-control macro that emits a prepared label with a checked work-head bound. |
| 2. Connectivity and witness words | A correct undirected connectivity decider yields a streaming signed Cayley word with fewer than the number of group elements in letters. The proof uses a prefix forest and includes bit-level access to the virtual adjacency encoding expected by Complexitylib. |
| 3. Subgroup and chief queries | Executable subgroup and normal-closure searches, the chief-series scan, and least-representative quotient multiplication have correctness proofs. The callback versions use scalar scans with a supplied correct membership routine. |
| 4. Residual replay | An ambient socle criterion and the quotient residual tests justify using the ordinal replay controller to answer exact tower membership queries with certified source residual generator lists. |

Open machine work in these four steps includes loading and manipulating the read registers on physical work tapes, interfacing the Lean 4.36 connectivity implementation with the virtual input and the active machine model, and executing the subgroup calls and residual list producer in that model. The general rank, generator count, and lifting routines also remain to be assembled into the final transducer. [Complexitylib](https://github.com/cslib-community/complexitylib)

The bundle retains the earlier checked group-theoretic and space-accounting components. Use `lake build` with Lean 4.33.0. The library sources used in this bundle retain their attribution and Apache 2.0 license notices.
