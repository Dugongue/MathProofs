# An oracle separating canonical forms from complete invariants for length-preserving equivalence

Fortnow and Grochow ask in Open Question 5.11 whether there is an oracle relative to which `CF ≠ Ker = PEq`. The following answers the restriction to length-preserving equivalence relations. In these relations every class consists of strings of one length. Complete invariants can be arbitrary strings. Canonical forms must output equivalent strings. The unrestricted question also allows classes with members of different lengths. [Fortnow–Grochow, *Complexity Classes of Equivalence Problems Revisited*, §5](https://arxiv.org/html/0907.4775v2#S5)

**Theorem.** There exists an oracle $A$, computable in the halting problem, such that

$$
\mathsf{CF}_{=}^A\subsetneq\mathsf{Ker}_{=}^A=\mathsf{PEq}_{=}^A.
$$

The separating equivalence relation has classes of size at most two. Its complete invariant is explicitly read from the oracle. Moreover, no randomized polynomial-time oracle transducer computes any of its canonical forms with probability at least $2/3$ on every input.

## Oracle blocks

Use a binary oracle with two disjoint kinds of word. Every block has a fixed query length, so all bits associated with one block occur at that length. The encodings below are uniquely parsable, with cost polynomial in their data. For example, use a prefix for the kind, self-delimiting index fields followed by the indicated string and a bit index, and padding to the stated length. Other words may have arbitrary values.

- For each $n\ge 1$, a block gives bit access to a map $F_n : \{0,1\}^n\to\{0,1\}^n$. All its bit queries have the same length $B(n)=10(n+2)^2$. Each map is either injective or exactly two-to-one onto its image.
- A block for an invariant row $(i,c)$ at an input length $m\ge 0$ gives bit access to an $m+1$-bit label $\ell_{i,c,m}(x)$ for each $x\in\{0,1\}^m$. The index $i$ names a clocked deterministic polynomial-time oracle decider $D_i$ on pairs. Normalize every $D_i$ to reject different-length pairs. Choose the block length $L_{i,c}(m)$ polynomial in $m+1$ for each fixed row, with $L_{i,c}(m)\ge 4$, large enough that the entire clock bound for $D_i(x,y)$ at $|x|=|y|=m$ is at most $\sqrt{L_{i,c}(m)}$. The clock and the pair encoding give this bound uniformly over all oracle answers. The encoding length is at least the length of the row identifier, so infinitely many choices of $c$ use only words above any given finite cutoff.

A row starts inactive. Once activated, its label equality in each block must be exactly $D_i$'s equivalence relation on that block's inputs. No row restriction compares two different lengths. Every block has more than enough labels, since at most $2^m$ classes can occur.

## Finite commitments and activation

The construction keeps a finite complete prefix of the oracle, consisting of all words up to a cutoff, and a finite sequence of activated rows. Call a total completion admissible if it extends this prefix, every base block obeys its map promise, and all activated rows satisfy their label restrictions. Inactive rows are free apart from fixed prefix bits. A longer finite complete prefix is locally admissible if it agrees with the fixed prefix and meets the same requirements at the blocks it contains. Local checking is possible because a restricted block at length $L$ only uses decider queries of length at most $\sqrt L<L$.

Maintain the following extension property. Every locally admissible prefix can extend to a total admissible oracle. Initially simply fill unassigned base blocks by injections and other bits arbitrarily.

Process each $D_i$. If some admissible oracle makes it fail to define an equivalence relation, fix a finite complete prefix of such an oracle determining that failure. A failure of reflexivity, symmetry or transitivity has a finite tuple and finite computation transcripts. The extension property survives fixing the new prefix. Otherwise $D_i$ is an equivalence relation in every currently admissible completion. Activate an unused row $(i,c)$ whose encoding sits above the fixed prefix. Its restriction can be imposed while retaining the extension property.

Here is the verification of the last assertion, including simultaneous dependencies between rows. Start from a locally admissible longer prefix under the new restrictions. Fill blocks at successive word lengths. The current shorter prefix satisfies the old restrictions, so the old extension property supplies an old admissible completion of that shorter prefix. Every old-row decider for a block at the next length has the same answers as in that completion, because all its computation queries lie in the shorter prefix. Its relation is therefore an equivalence. The new-row decider is an equivalence relative to the same completion by its activation test, and its queries also lie in the shorter prefix. Give each of these blocks any injective naming of its classes, complete the other bits at this length, and continue. This preserves every local restriction. The union satisfies all rows. In particular, subsequent activations and commitments narrow the admissible completions, so an earlier decision that a machine always gives an equivalence stays valid.

Thus every machine in the final oracle that actually decides a length-preserving equivalence relation has an activated row. The invariant on $x$ is its row label, of length $|x|+1$. Distinct lengths yield distinct label lengths. Reading its bits takes polynomial time, with constants and degree depending on the chosen row.

## Diagonalizing against a canonical form

The designated relation $R^A$ equates strings of length $n$ with the same $F_n$-value and makes the empty string a singleton. For example $x\mapsto 1F_n(x)$ on nonempty inputs and the empty output on empty input is a polynomial-time complete invariant. We interleave activation stages with diagonalization against clocked randomized polynomial-time transducers $M$, including deterministic ones.

For such a stage, choose a large $n$ beyond the fixed prefix cutoff. Extend that prefix up to length $n-1$ by the extension property. It cannot fix any $F_n$-entry because $B(n)>n-1$. Set $M_0=\max\{B(n),p(n),n\}$, where $p(n)$ bounds the time of $M$ with every oracle and coin sequence at length $n$. Define a distribution on admissible prefixes through $M_0$.

1. Sample $F_n$ from a uniformly random perfect matching of the $2^n$ strings, giving its pairs uniformly assigned names without replacement from $\{0,1\}^n$.
2. Complete unfixed base blocks other than $F_n$ with fixed injections. Fix unused bits other than activated rows to zero.
3. In increasing query length, independently give each activated block a uniformly random injective labeling of the classes determined by the shorter bits. Every such choice is admissible by the extension property and its block-filling proof.

Suppose $R^A$ had an exact canonical form computed by $M$ in every sampled prefix. On a uniform $x\in\{0,1\}^n$, $M$ would output the other member of its pair with probability exactly $1/2$ in each prefix. For a randomized transducer computing a fixed valid canonical form with probability at least $2/3$ on each input, the same probability, over both the input and the coins, would be at least $1/3$. We bound it below $1/3$ for the distribution, which guarantees some finite prefix where $M$ fails the required canonicalization guarantee.

### Lazy generation of the oracle answers

When asked for an activated label, expose the full label. To resolve a new queried input $u$ in that block, run $D_i(u,v)$ for all previously exposed inputs $v$ of the same block. Recursively resolve the oracle bits needed by those runs. Each recursive query has strictly shorter length, at most the square root of the block query length. If $u$ is equivalent to a previous input, reuse its assigned code. Otherwise draw uniformly from the unused codes of that block. For a base bit at length $B(n)$, expose the entire $F_n$-value at its argument. The remaining bits come from the fixed prefix or the fixed choices of the distribution.

To verify the sampling law, augment a query history by all of these internal comparison transcripts and the full exposed labels. Fix values of the base maps and of the deterministic bits. In the distribution computed by increasing length, a proposed history can occur exactly when its deterministic transcripts check using the exposed bits, the exposed base map values match, and the observed equalities and inequalities between labels in a block agree with the comparisons recorded in the history. Every pair of exposed inputs of a block has a recorded comparison. Its computation is forced by recorded shorter answers. For any completion of the shorter blocks consistent with the history, the probability of the prescribed values on the $r$ exposed classes of an unfixed block is

$$
\frac{1}{C(C-1)\cdots(C-r+1)},\qquad C=2^{m+1}.
$$

It is independent of unexposed class data. This follows by restricting the uniform injective assignment in that block to those $r$ distinct classes. Applying this fact in decreasing block length integrates out all unexposed choices in longer blocks without imposing any further condition on shorter blocks. Pending higher-block operations during a recursion contribute only already disclosed shorter comparisons and impose no constraint from a label that has yet to be given. The conditional laws are therefore those of the lazy process, including when a class identification and its code are revealed after an adaptive series of queries. Equivalently one can obtain the same finite-history probabilities by multiplying the successive uniform unused-code probabilities. This establishes the marginal law seen by $M$.

### Polynomially many probes of the random matching

All query lengths below $n$ can be answered from the fixed prefix. For lengths at least $n$, partition the query range into tiers

$$
(M_0^{1/2},M_0],\ (M_0^{1/4},M_0^{1/2}],\ (M_0^{1/8},M_0^{1/4}],\ldots .
$$

Every comparison triggered in a tier only issues queries in strictly lower tiers. For fixed $M$, $M_0\le n^d$ for a constant $d$ and large $n$, so only a constant number of tiers reach length $n$. The first tier receives at most $p(n)$ calls from the transducer. If $Q$ calls in the higher tiers have been counted, their blocks can create at most $Q^2$ pair comparisons. Each comparison makes at most $M_0$ direct oracle queries under the clock for that block. Thus through the next tier the cumulative call count is at most $p(n)+Q+M_0Q^2$. Repeating this for the constant number of relevant tiers gives a polynomial bound $T(n)$ on all probes of $F_n$. The bound is uniform over $x$, the transducer coins, the earlier prefix and the simulated answers. The simulation may use lengthy computation on fixed bits. The bound charges calls to the random matching, which is sufficient.

Grant the matching query algorithm the $F_n$-value of its input $x$ at the outset. Conditional on all probes so far that have failed to find the partner, that partner is uniform over the unprobed locations other than $x$. A permutation of those locations leaves the random matching distribution and the observed $F_n$-responses unchanged. The adaptive simulator uses only those responses and independent randomness, so the same symmetry applies to the next probe or final output. A union bound gives probability of outputting the partner at most

$$
\frac{T(n)+1}{2^n-T(n)-1}.
$$

For sufficiently large $n$ this is less than $1/3$. Since the query simulation has the sampled marginal law, some sampled prefix defeats $M$. Fix that prefix. Its entire length-$n$ computation behavior is fixed, for every possible coin string, and $F_n$ itself is fixed. The same failure therefore holds in all further admissible completions.

## Construction and effectiveness

Alternate the preceding stages for all clocked deterministic pair deciders and all clocked randomized transducers. Cutoffs tend to infinity, so the union determines a total oracle. Every activated row satisfies its restrictions in that union. Every diagonalization is permanent. This proves the asserted equality and the strict inclusion.

The choices can be made computably using the halting problem. At a finite activation stage, search for a finite locally admissible prefix together with a certified violation. Checking local admissibility runs finitely many block tests and is decidable. A violation in a total completion appears in such a finite prefix, and any such prefix extends by the extension property. The halting problem answers whether this search will find a violation. At a diagonalization stage, enumerate finite locally admissible prefixes and check finite computations at fresh lengths, trying larger lengths until a failure is found. Testing the randomized guarantee on a length is finite. Within each two-element class, test whether one representative is printed with probability at least $2/3$ from both inputs. The lower bound guarantees termination of this search. Across the construction this yields a halting-oracle algorithm for computing each final bit.

The proof uses the length-preserving condition in two places. Label strings can have the same prescribed length for all members of a class, and every comparison used to decide a label within a block only queries strictly shorter words. The oracle equality established here covers all length-preserving polynomial-time equivalences. Question 5.11 for arbitrary equivalences remains open.
