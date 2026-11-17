# Mixed relative orientation and source-automorphism tests

Fix F₃ and ordered three-tensors. Let O,A,B,S be the four problems, and F ask whether one raw tensor has an automorphism with determinant −1 in a prescribed first mode. For a raw pair let D be its relative sign profile in F₂³, and H the stabilizer sign group of the source. If D is nonempty it is a coset with direction H. Each class below means the downward closure of the indicated language under deterministic polynomial-time many-one reductions. Proofs are informal.

## Preparations

Use the prior exact projection and distinct-format direct-sum compiler: it can recover any fixed linear projection of D, keep it on one or more axes, and add the projected profiles of a fixed number of separate comparisons. Neutral ordinary comparisons can be added without changing any surviving sign. For a self-comparison the transformations can be performed identically on its two endpoints. In the instances here the compiler is used only with at most three independent live axes. The construction preserves emptiness in the presence of a relative ordinary failure.

We have O ≤ F ≤ A. For F ≤ A, reflect the target in the tested mode of the self-pair. A positive relative sign is now exactly a negative source automorphism. For O ≤ F use the existing optional-swap marker. Transform the two compared objects into concise, absolutely indecomposable objects with the same odd side lengths and with trivial total determinant on their individual automorphisms. In their direct sum a block transposition is available exactly when the original ordinary comparison succeeds. Its total determinant is negative, because the local maps cancel using inverse witnesses and there are three odd sides. In the absence of such an exchange the total determinant is always positive. Apply the total-to-one-character encoding to this self-comparison. These are the optional-swap and unary odd-automorphism constructions from the earlier work, not new in this note.

## A homogeneous stabilizer ladder

For r=1,2,3, let F_r ask whether the projected source stabilizer contains a specified nonzero vector v in r selected sign coordinates. The choice of nonzero v has no effect on the degree because the exact linear projection allows invertible change of determinant coordinates. The case r=1 is F.

The following hold.

1. $F^r\le_m^p F_r$, with $F^r$ denoting a conjunction of r independent F instances. Isolate the i-th source stabilizer on axis i, use distinct formats and direct sum the resulting objects, then ask for the sum of the r unit vectors. The axes are independent and a negative bit must be available on each.
2. $F_r\le_m^p F^{2^{r-1}}$. For every linear functional l with l(v)=1 ask whether l is nonzero on H. If v is outside H, separation in the binary quotient produces an l with l(v)=1 and l(H)=0. Conversely if v is in H then all the required tests succeed.
3. $F_2\equiv_m^p F^2$ follows immediately. For $F_3$ this gives $F^3\le_m^p F_3\le_m^p F^4$. Lowering $F_3$ to $F^3$ would improve the same-source test beyond the four character probes. For F_r with a specified nonzero v the 2^(r−1) upper bound is sharp for adaptive queries of the form “is l nonzero on H?” in the abstract stabilizer model. On H equal to the whole space every nonzero l returns yes. Each hyperplane ker l with l(v)=1 differs from the whole space on just the query l, so all those queries must be made on the all-yes path. This is a probe statement.
4. $F_r\le_m^p$ the r-sign tier by reflecting exactly those target modes in which v has a negative bit. Hence F_r is genuinely sandwiched, and the upper bound uses one query with one common source automorphism.

Closures of F are also concrete. Polynomial-length **disjunction** of F instances reduces to F by summing the independent homogeneous profiles on a single tagged axis. An OR of many such questions therefore does not add a tier. The proofs do not give any conjunctive compression for F.

## Add a relative comparison on unused axes

There are concrete single-pair representatives for the following mixed degrees.

| Raw test on a single pair | Exact degree |
| --- | --- |
| First sign is attainable positively and a source automorphism has negative second sign | $A\land F$ |
| First sign is attainable positively and a source automorphism has sign vector (1,1) on the last two bits | $A\land F^2$ |
| Two positive signs are jointly attainable and a source automorphism has negative third sign | $B\land F$ |

In every row, the upper reduction reads the indicated relative comparison and the source self-comparison. Use $F_2\equiv F^2$ in the middle row. For the reverse use the axis compiler to put the relative instance on the indicated relative axes, then put each independent F instance in a self-comparison on its own remaining axis. The source of the combined relative pair includes exactly those self-comparison objects. Its stabilizer projection on the remaining axes is therefore the product of their sign images, independently of the relative comparison. This proves both directions though the raw language uses the source of a single displayed pair.

The following diagram gives the positions that follow without further assumptions.

    O ≤ F ≤ A ≤ A∧F ≤ A∧A ≤ B ≤ B∧F ≤ B∧A ≤ S
        F² ≤ A∧F ≤ A∧F² ≤ B∧F
        F³ ≤ A∧F²
        F³ ≤ F₃ ≤ S

For $A\land F^2\le B\land F$, pack the A instance with one F instance viewed as its reflected signed comparison on the other relative axis. For $B\land F\le S$, place the reflected F comparison on the third axis. These are unconditional comparisons, even when the different Karp degrees eventually coincide. In particular $B\land F$ is a test of whether two live relative constraints can absorb one purely homogeneous constraint. If $B\land F\le B$, it also absorbs every fixed number of independent F tests, by iteration. It then absorbs F₃, using the four character tests. No uniform polynomial-number conjunction statement is needed for this conclusion. If $F\le O$, ordinary conjunction packing already gives $B\land F\equiv B$.

There is also a fixed-arity catalogue of mixed conjunction forms without counting repeated coordinate permutations. Choose a nonzero count vector (i,j,k) of independent A,F,B queries with i+j+2k≤3, and ask for their conjunction, with at least one relative query when the ordinary comparison is to occur inside it. For purely homogeneous queries one can append a neutral ordinary comparison. This grammar has twelve forms before removing benchmarks and coincidences. It includes e.g. independent third-mode flexibility on the source of a two-sign comparison, which differs from the distinct relative third sign used by full SL-TI. The most informative named degrees and many-one comparisons are those above, including the exact compression of two homogeneous signs to F².

These reductions reuse previous MathProofs projection, direct sums and optional-swap constructions. The underlying problem of special-linear containment is Open Question 1.9 of the cited preprint. [Chen, Grochow, Qiao, Tang and Zhang](https://arxiv.org/html/2306.03135v2#S1.SS5)
