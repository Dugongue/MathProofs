# Proofs by exhaustive case crossing

These AI-assisted informal proofs follow the Hypoworlds approach of comparing explicit assumptions and checking which combinations survive. The conclusions follow from the mathematical arguments in the linked notes. Publication priority remains provisional.

1. [Group Isomorphism circuit separation](GroupIsomorphismDepthSeparation.md). On one valid canonical Cayley-table promise, ordinary DNF requires $2^{(2/27)(\log_2 n)^3+O((\log n)^2)}$ terms, while ordinary depth-three circuits have size $2^{O((\log n)^2)}$. The DNF lower bound extends to unrestricted valid tables. The depth-three upper bound uses the canonical labelling.
2. [Sharp symmetric-group padding](SharpSymmetricGroupPadding.md). In the converse after Grochow–Urisman Lemma 6.11(2), padding by $k-2$ points recovers all original occurrences, and this positive threshold is exact for every even $k\ge4$. If both subgroups lie in $A_k$, $\lfloor(k+1)/2\rfloor$ points suffice.
3. [Monophonic Position Colouring](MonophonicPositionColouring.md). Both the ordinary and independent variants are $\Theta_2^{\mathrm P}$-complete even at diameter two. An exhaustive threshold identity turns a computable baseline plus an NP answer bit into a baseline minus that answer bit.
4. [Hasse counterexample for absolutely simple evolution algebras](EvolutionAlgebraHasseCounterexample.md). Explicit 12-dimensional algebras are isomorphic at every completion of $\mathbb Q(\sqrt{-3})$ and inequivalent over that field. The number field has no real place, in accordance with Liu's positive theorem for fields with a real place.
5. [Simple evolution-algebra automorphism maxima](SimpleEvolutionAutomorphismMaxima.md). Determines the maximum over every field and describes all equality types. Credits the previous Lean proof of the complex maximum. The binary field has exceptional odd-dimensional maxima.

## A full case split for the Hasse example

Write $K=\mathbb Q(\sqrt{-3})$ and use the classes of $\alpha,\beta$ modulo $4095$-th powers from the Hasse proof. Over any extension $E/K$, the orders of the two classes divide $3$ and $13$, respectively. If the $\alpha$-class survives, a matching cycle rotation must have odd step. If the $\beta$-class survives, its step must be a multiple of $12$. If either class dies, the other condition alone suffices.

| $\alpha$ survives | $\beta$ survives | Cycle isomorphism | A number field realizing the case |
| --- | --- | --- | --- |
| Yes | Yes | No | $K$ |
| No | Yes | Yes, step $0$ | $K(\zeta_{13})$ |
| Yes | No | Yes, step $1$ | $K(p^{1/13})$ |
| No | No | Yes, step $0$ | The compositum of the preceding two extensions |

Here $p=13183$. In $K(\zeta_{13})$, the prime $p$ splits completely since $p\equiv 1\bmod 39$, so the valuation $315$ still detects $\beta$. In $K(p^{1/13})$, adjoining the displayed root kills $\beta$. The extension has degree $13$ by Eisenstein at a prime of $K$ over $p$. If the $\alpha$-class died there, taking its norm would make $\alpha^{13}$ a $4095$-th power over $K$, contrary to its order $3$ class. The Hasse proof shows that each completion occupies one of the last three rows.

## Checking the cross-products

A bounded replay used 11 explicitly scoped propositions and 12 implications from the padding and Hasse proofs. The recovered forward-chaining engine detected 10 impossible pairs. Exhaustive evaluation of all 2,048 Boolean assignments against the same 12 implications found an eleventh impossible pair: the extension is a completion and the cycles fail to be isomorphic. The contradiction needs the two cases of whether the order-three class survives. Assignments surviving the finite implication ledger only satisfy those implications. The table above claims realizability where the proof supplies actual fields.
