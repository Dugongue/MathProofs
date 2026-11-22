# A finite score certificate for separated orbit closures

A single real 1-Lipschitz observable gives a certified lower bound on the distance between *all* pairs in two metric orbit closures using finite orbit samples. The score can vary along each orbit. The estimate uses the sample gaps and two explicit approximation radii.

## Blind retrieval

Scanned 590,787 declaration records in the v6 Covenant term bank. The selector read numeric records from `decls.bin` and `binders.bin`. For every theorem with a nonempty telescope, it indexed its conclusion node and all explicit input nodes. It joined an output node to an identical input node if the product of their occurrence counts was at most 100. It retained edges across distinct opaque module IDs. There were 2,918 distinct producers of retained edges and 1,831 distinct length-two paths across three pairwise distinct modules with different successive port nodes. Sorting the integer tuples `(producer, middle, consumer, firstPort, secondPort)` by the SHA-256 digest of their Python tuple representation froze a shortlist of 70. Only then were names opened. The path developed here ranked 66 on that shortlist. The later choice among its members and invention of the application were human-readable mathematical judgments.

| Declaration record | Port role | Revealed result |
|---:|---|---|
| 571832 | Produces node 727747 | Nonemptiness of the closure implies nonemptiness of the original set. |
| 472749 | Consumes 727747 and produces 3197074 | Finite extended Hausdorff distance transports nonemptiness between sets. |
| 64885 | Consumes 3197074 | An arbitrary real score attains a maximum on a nonempty finite set. |

The two joins had producer/explicit-input occurrence counts 5/19 and 2/3. The corresponding Lean declarations are `Set.Nonempty.of_closure`, `Metric.nonempty_of_hausdorffEDist_ne_top`, and `Set.exists_max_image`. The application additionally uses `Metric.hausdorffEDist_closure_left`, `Metric.exists_dist_lt_of_hausdorffDist_lt`, and `Set.disjoint_left`. The bank's hashes are `c513f93e7071d3969d64b1eb19855fbd2a4f6ed6375b24f6769d477c20a504f1` for declarations and `02e86aca916469fd85cf11e727de4825e96cfaaf155f03f69735fff77ca88286` for binders. The 70 tuples serialized by Python one per line with a final LF have digest `4f66f63a8f02f144b019573b5676fa159c1f13c44c91366d75d2a992989b86c8`.

## The quantitative estimate

Let $S,T$ be sets with nonempty metric closures. Let $A,B$ be finite sets at finite extended Hausdorff distance from $S,T$, respectively. Write $r=d_H(S,A)$ and $s=d_H(T,B)$. Given a real 1-Lipschitz score $f$, put $M=\max_A f$ and $m=\min_B f$. For every $x\in\overline S$ and $y\in\overline T$,
$$
d(x,y)\ \ge\ m-M-r-s .
$$

The three retrieved nodes establish nonemptiness of the samples and supply a maximizing witness. For $x\in\overline S$ and any $r'>r$, some $a\in A$ has $d(x,a)<r'$. Hence $f(x)\le M+r$ by taking the infimum in $r'$. Applying the same argument to $-f$ gives $f(y)\ge m-s$. The Lipschitz inequality now bounds $f(y)-f(x)$ by $d(x,y)$. In particular $m-M>r+s$ certifies disjoint closures. Equality permits intersection, as shown by $S=T=\{0\}, A=\{-1\}, B=\{1\}$ in the real line with $f(x)=x$. The Lean file treats pseudometric spaces and proves the one-sided score bound and the strict-gap disjointness consequence. The displayed quantitative distance bound and group application have the written proof here. [Lean source](Joint.lean)

## From a Cayley graph covering to an orbit certificate

Let a group act isometrically on a metric space. Take a finite set of sample elements $C$ and a symmetric generating set $U$ such that every group element is a product $c u_1\cdots u_j$ with $c\in C$ and $j\le k$. In a finite Cayley graph this condition and the least such $k$ can be computed by multi-source breadth-first search. If every generator moves a starting object $z$ by at most $L_z$, the displacement between $cz$ and $c u_1\cdots u_j z$ is at most $k L_z$: telescope along prefixes and cancel the common prefix by isometry. Thus $Cz$ has Hausdorff distance at most $k L_z$ from the entire orbit. For two starting objects $z,w$, the explicit sufficient score test is
$$
\min_{c\in C} f(cw)-\max_{c\in C} f(cz)>k(L_z+L_w).
$$
This applies, for example, to permutation conjugation of real matrices with Frobenius distance. Adjacent transpositions give explicit generator displacements, and any Frobenius-unit linear functional gives an admissible score. The test makes a one-sided certification from sampled conjugates, with no assertion of completeness or a worst-case speedup. The metric inequalities are elementary, and this run makes no priority claim.
