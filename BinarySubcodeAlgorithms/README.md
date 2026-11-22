# Counting epimorphisms of two-prime groups via binary subcodes

Given binary codes $C,D$ of length $r$, count the coordinate permutations $p$ satisfying $pC\subseteq D$, and return one when the count is positive. **When either code has bounded matroid branchwidth, this takes deterministic $2^{O(r)}$ bit time, with no restriction on the dimension gap or on the other code.** The algorithm finds its own decomposition. This gives polynomial Cayley-table-time counting and construction of epimorphisms for the corresponding family of two-prime groups. The unrestricted $2^{O(r)}$ bound remains open here. [Counting proof](Structure.md) · [Implementation](subcode.py)

### Why the dimension gap drops out

Let $g_i$ be the source generator columns and $h_j$ the target parity-check columns. The containment condition is $\sum_i g_i h_{p(i)}^{\mathsf T}=0$. If a partial permutation sends positions $S$ onto $T$, its matrix sum must also be obtainable from the complementary positions. Its column space must therefore lie in $\mathrm{span}(g_S)\cap\mathrm{span}(g_{S^c})$, and its row space in the corresponding intersection for $h_T$. Call the dimensions of these spaces $a$ and $b$. Only $2^{ab}$ partial matrices can survive. A dynamic program counts the bijections for each such matrix along a binary tree. Bounded branchwidth gives a tree with one of $a,b$ bounded everywhere. The proof gives the stronger, instance-dependent running time and recovers a witness by tracing a nonzero count. [Theorem and recurrence](Structure.md)

### Other regimes

| Hypothesis | Result |
| --- | --- |
| Dimension gap $g=\dim D-\dim C$ is fixed | Exact count and witness in $2^{r+o(r)+g\min(\dim C,r-\dim D)}$ time. The fixed-gap milestone follows from published subcode enumeration and code equivalence. Short dependencies and repeated columns give further sufficient conditions at growing gaps. [Proofs](Gap.md) · [Subset algorithm](gap.py) |
| Repeated columns in the generator of $C$ and the parity check of $D$ | A binary parity table lifts to an integral table with prescribed margins. Under the stated multiplicity thresholds, two tests involving the all-ones word are necessary and sufficient, and a witness is computable in polynomial time in $r$. A separate character sum counts solutions. [Proof and implementation](Counting.md) |
| The weights of the smaller code constrain its image | Intersect the spans in the host for every weight set that generates the source, then apply the dual rule. This preserves every witness and can identify a unique image even when no individual weight set does. A finite probability formula proves high-probability recovery in explicit random extensions, including examples with linear gaps and logarithmic host redundancy. [Proof and example](Spectrum.md) · [Lean pruning lemma](Filter.lean) |

### The group consequence

Here $G(C)=\mathbb F_3^r\rtimes((\mathbb Z/4)^r/2C)$, where reduction of the second factor modulo two acts by coordinate sign changes. For groups of this form at the same $r$, the established correspondence multiplies the code-permutation count by $6^r2^{r(r-\dim D)}$ to count all epimorphisms $G(C)\to G(D)$. A witness permutation gives one epimorphism by relabeling both factors. The codes are recoverable from promised raw group tables, and $|G(C)|=12^r/2^{\dim C}$. This is why $2^{O(r)}$ is a polynomial table-time bound. Grochow, Srivastava and Thakkar's question covers general abelian Sylow towers. [Group correspondence, §5](https://github.com/Dugongue/MathProofs/blob/main/SylowTowerActionRanks/PROOF.md) · [Open Question 3(4)](https://arxiv.org/html/2609.07429v1#S7)

For example take $r=4m$. Generate $C$ by the indicators of $2m$ disjoint pairs. Let $D$ impose even parity on each of two blocks of size $2m$. A permutation is admissible precisely when each source pair lands wholly in one block. Choosing which $m$ pairs go into the first block and arranging the labeled coordinates gives $\binom{2m}{m}((2m)!)^2$ permutations. Changing the two block sizes to $2m-1$ and $2m+1$ gives zero. The gap is $2m-2$ in both cases. The executable checks both group counts for $m=1,2,3$.

### Reproduction, verification and prior work

Use Python 3.10 or later. The inputs below are generator rows encoded as binary integers. Coordinate zero is the least significant bit. The tuple returned by the tree solver contains the exact count, a source-to-target permutation (or `None`), and the optimal tree cost used.

```python
from subcode import count_embeddings, count_group_epimorphisms, dual

source = [3, 12, 48, 192]
target = dual(8, [15, 240])
count, permutation, cost = count_embeddings(8, source, target)
assert count == 3456
group_count, witness = count_group_epimorphisms(8, source, target)
assert group_count == 3456 * 6**8 * 2**16
```

Run `python check.py` and `python gap.py`. The controls compare counts and recovered witnesses with exhaustive permutations for all 4,775 ordered pairs of binary codes at lengths zero through four. They also test longer pairs and the finite random-extension formulas. The full algorithms have written proofs. Lean independently checked the linear-span pruning equivalence and the algebraic identity that characterizes zero total syndrome through partial sums on complementary coordinate cuts. [Test source](check.py) · [Weight-span lemma](Filter.lean) · [Boundary lemma](Boundary.lean)

Santini, Baldi and Chiaraluce give the subcode-enumeration algorithm and identify the permuted-kernel formulation. Babai, Codenotti, Grochow and Qiao give the simply exponential code-equivalence primitive. Kashyap develops tree realizations for individual linear codes. The structural result proved here uses the product of two boundary dimensions to count coordinate containments. Publication priority for the structural bounds has not been established. [Subcode equivalence, §4](https://doi.org/10.1109/TIT.2023.3323068) · [Code equivalence](https://doi.org/10.1137/1.9781611973082.107) · [Tree realizations](https://arxiv.org/abs/0711.1383)
