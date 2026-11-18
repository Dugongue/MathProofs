# Grochow question hypothesis ledger

This audit starts with the 82-row MathProofs catalog of published questions. It records an exact Boolean proposition for each tracked claim. Broad questions have separately scoped directions, variants or thresholds. Every catalog row is represented, including rows with no decisive implication in the current ledger. The published evidence profile uses published results and direct logical or definitional consequences. The local profile adds available informal MathProofs proofs and the new proofs in this packet.

## Replay results

The 82 rows expand to 186 precisely scoped claims, including background hypotheses. Each evidence profile checked all 68,820 signed pair assignments. A pair-only conflict has two individually viable literals that become inconsistent when assumed together. Anchored claims are counted separately from pair-only conflicts.

| Evidence profile | Rules | Forced true | Forced false | Satisfiable signed pairs | Pair-only conflicts | Nonconstant equivalences |
|---|---:|---:|---:|---:|---:|---:|
| Published and direct logic | 173 | 9 | 0 | 65,269 | 257 | 2 |
| With the local proofs | 211 | 25 | 28 | 50,363 | 225 | 4 |

The local profile has fewer pair-only conflicts because additional proofs exclude some formerly viable literals on their own. The total number of excluded pairs increases. The four nonconstant equivalences are the rank versus border-rank polynomial-degree claims, and the paired versus arbitrary-source formulations in G06, G07 and G08. For example, the positive depth-three polynomial-size circuit claim is the exact opposite of the depth-three lower-bound claim. Uniform constant-depth membership can still coexist with a depth-three lower bound, since the former can use a larger depth. The whole-ledger and componentwise scans produced byte-identical reports, and 1,200 small satisfiability instances agreed with exhaustive truth tables.

## Mathematical results from this run

- **Song–Grochow's sixteen-rule census.** The all-size light-cone proof eliminates the positive branch of every one of the 16 historical cases at block size at least two. The finite rule-table replay verifies their identities and the full existence census of 240 positive and 16 negative sources. It also reproduces explicit block-size-nine witnesses for four extra rules that the paper's search had left unresolved at size seven. [Proof and scope](CELLULAR-AUTOMATA.md)
- **Fixed-block complexity.** The elementary unary-length problem is in EXP via expanded tables and the Boolean homomorphism result. A separate sparse-hardness contradiction rules out NEXP-completeness under deterministic polynomial-time many-one reductions in this precise encoding. It would give both \(P=NP\) and \(EXP\subseteq P/poly\), hence \(EXP=MA\subseteq PH=P\). Variable alphabets and other block-size encodings use different languages. [Proof and scope](CELLULAR-AUTOMATA.md)
- **Exact oracle reductions.** An adaptive high-power oracle can be eliminated when the proposed output has small degree relative to the powers. In characteristic zero this refutes the degree-independent division-free constant-depth determinant extraction formulation in Dey–Guo Conjecture 2. The same argument refutes the degree-unrestricted exact oracle version of the Factor Conjecture, with unrestricted-depth division-free circuits and even multiple admissible polynomial indices. The explicit-input Factor Conjecture and the known border results have their own hypotheses. [Proof and scope](POWER-ORACLES.md)

## Cross-question conclusions

- The polynomial rank-degree and polynomial border-rank-degree claims for geometric tensor-isomorphism PC are equivalent when the proof system and field agree. Either would imply a subexponential sparse proof bound in balanced dense input length. A statement about field-specific no-instances with separate field equations must keep those equations in its scope.
- The three paired promises G06, G07 and G08 are equivalent to allowing an arbitrary source while keeping their respective target families. Each equivalence uses a different universal quotient step. The reductions preserve epimorphisms, so they also give the corresponding scope reductions for counting and search.
- A positive logspace subquasigroup membership answer would yield logspace counting and search for constant-generated quasigroup isomorphism. A positive colored-abelian WL answer would imply bounded ordinary WL dimension for the abelian coprime semidirect case. The existing local negative colored-abelian result leaves that consequent open.
- The finite/rational field comparison would imply the cross-characteristic comparison in each composable direction. Fixed finite-ring comparisons reduce to checked obligations on the source characteristic primes jointly. This describes the known dependencies while leaving the individual cross-characteristic reductions open.
- A low-degree Boolean IPS size separation from unrestricted IPS at the particular linear degree threshold in the ledger would imply a VP versus VNP separation. Also, a Boolean matching decision projection lower bound would imply the matching exact-count projection lower bound. The existing exact-count result does not give the reverse arrow, because Boolean decision allows additional monomial supports.
- A false branch for the literal implication from \(\mathsf{Ker}=\mathsf{PEq}\) to PH collapse forces \(\mathsf{Ker}=\mathsf{PEq}\) and \(\mathsf{CF}\ne\mathsf{Ker}\), using the known collapse consequence of \(\mathsf{CF}=\mathsf{Ker}\). The relative-oracle question is separate.

[Proofs of the new cross-question implications](TRANSFERS.md) · [Complete rules with reasons and sources](rules.txt) · [Claim registry](claims.txt)

## Replaying and extending the worlds

Python 3 is sufficient. The scan checks both signs of every claim and all four assignments for every distinct pair. It uses exact propositional satisfiability, including rules with multiple premises and disjunctive conclusions. The pairs.csv file records every outcome. The implications.csv file records consequences where the two excluded literals are each separately satisfiable. Thus fixed facts do not make unrelated claims appear equivalent.

    python worlds.py --profile published --output replay/published
    python worlds.py --profile local --output replay/local
    python worlds.py --assume CA01_30
    python worlds.py --assume G06 !G06_raw
    python worlds.py --assume G09 G10
    python check_elementary.py

Under the assume option, a contradictory branch returns a deletion-minimal set of ledger rules explaining it. A satisfiable branch returns a complete Boolean assignment satisfying the entered rules. This means those rules do not exclude the branch. Every complete Boolean world is represented implicitly by the clauses, and arbitrary multi-claim assumptions can be queried without listing the exponentially many assignments. To add a branch, record its exact proposition, model and quantifiers in claims.txt. Add a rule with a mathematical justification and an evidence source. The exclamation mark negates an atom, an ampersand joins premises, commas give an alternative conclusion, and a standalone signed atom is a fact. The proof discoveries remain informal. Literature priority for the new arguments has not been established.
