# A reduction for Fortnow–Grochow Question 5.11

Uses the anchor construction in the [published canonical-forms proof](../../CanonicalFormsAndPNP/PROOF.md).

## Conventions

- Notation is FG Def 1.1. PEq ⊇ Ker ⊇ CF ⊇ LexEq. $\mathcal C_=$ means length-restricted and $\mathcal C_p$ means polynomially bounded.
- **"CI" (complete invariant) is the same as Ker.** Ker *is* the class of relations with a polynomial-time complete invariant. "CF vs CI" therefore means CF vs Ker throughout.

### The anchor relation $\mathcal A_V$ (from PROOF)

Fix a verifier $V$ with witnesses of length at most $(|x|+2)^e$. Put $\gamma(x)=1^{|x|}0x$.

- Anchor: $a(x,d)=0\gamma(x)1^d0\,0^{(|x|+2)^d}$.
- Witness strings: $b(x,d,w)=1\gamma(x)1^d0w$ with $V(x,w)=1$.
- Each $(x,d)$ gives one class. All other strings are singletons.

The invariant "header, or $1z$" is computable in P relative to $V$'s oracle. For 3SAT it is even in FL (CFI §1).

**Padding Lemma (PROOF).** Let $c$ be any canonical form of $\mathcal A_V$ such that $|c(z)|\le C(|z|+1)^k$ on witness strings, and fix $d$ with $2^{d-ek}>C(d+10)^k$. Then for all $x$:

- $x\in L(V)$ implies that $c(a(x,d))$ is a witness string;
- $x\notin L(V)$ implies $c(a(x,d))=a(x,d)$.

*Only an output-length bound on witness strings is used.* The output is not required to be computable in any particular way. Everything below exploits this.

---

## 1. FG Open Question 5.11 (reduction theorem)

**Theorem 1.1.** For every oracle $A$:

$$\mathsf{CF}^A\ne\mathsf{Ker}^A=\mathsf{PEq}^A\iff \mathsf P^A\ne\mathsf{NP}^A\ \text{ and }\ \mathsf{Ker}^A=\mathsf{PEq}^A .$$

*Proof.* (⇒) If P$^A$ = NP$^A$, then the shortlex argument (FG §3, relativized) gives CF$^A$ = PEq$^A$. (⇐) By PROOF, P$^A$ ≠ NP$^A$ implies CF$^A$ ≠ Ker$^A$. ∎

So OQ 5.11 needs **no canonical-form diagonalization at all**. It is exactly the question of whether Ker = PEq relativizably forces P = NP. LPO spent half its construction diagonalizing CF$_=$ against Ker$_=$. In the unrestricted setting that part is now free.

**Corollary 1.2 (what is already known about such an $A$).**

1. Any such $A$ has UP$^A$ ⊆ BQP$^A$. FG Thm 4.3 relativizes, and its relation $R_L$ is length-restricted. So only $\mathsf{Ker}_=^A=\mathsf{PEq}_=^A$ is needed, and LPO's oracle already satisfies this constraint.
2. Relative to the LPO oracle, P ≠ NP (because CF$_=$ ≠ Ker$_=$) and $\mathsf{Ker}_==\mathsf{PEq}_=$. Whether Ker = PEq holds there for *unrestricted* relations is open.
3. Relative to FG's oracle $B$ (Thm 5.5): CF$_p$ = Ker$_p$ and P ≠ NP. Hence CF ≠ Ker by PROOF. **The polynomially bounded collapse provably does not relativizably lift to the unrestricted one.** PROOF already noted the comparison with Thm 5.5, but not this explicit separation of the two notions relative to one oracle.

**Obstruction to lifting LPO (precise).** One could try LPO's label rows, with variable-length labels in which class members of different lengths receive the label of their first-appearing member. Consistency is fine. Comparisons between $u$ and shorter $v$ query only words of length at most $\sqrt{L(|u|)}$, below $u$'s block.

The failure is in the P ≠ NP diagonalization. To keep the label bits that $M$ read fixed under a change at the test length, one must preserve the equivalence pattern on all pinned strings of a row. A pinned *short* string $z$ must therefore be compared with a pinned *long* string $u$. That comparison pins further words, of length up to $\sqrt{L(|u|)}$ and not $\sqrt{L(|z|)}$, and these again contain label words compared with $u$. LPO's "tiers" strictly descend only for same-block comparisons. Here the recursion can stay inside one tier, and no polynomial bound on the pinned set follows.

A proof of 5.11 needs either a label scheme in which long–short pairs are certified without simulating $D_i$, or a different P ≠ NP witness. Note that a plain UP-generic sparse set over PSPACE does **not** work: FG Lemma 5.7's forcing argument applies to it and gives Ker ≠ PEq.

Novelty: Theorem 1.1 and Corollary 1.2(3) are new; Corollary 1.2(1) is FG Thm 4.3 plus the observation. Confidence: 0.97.

---
