# Independent and common changes of basis for split diagonal tensors

For weights $a=(a_i)$ in a field $K$, use the symmetric trilinear form
$$
T_a(x,y,z)=\sum_i a_i x_i y_i z_i .
$$
It represents a tensor on three copies of the same coordinate space. The independent action lets each copy have its own linear change of basis. The common action uses one change of basis on all copies.

If all entries of $a$ and $b$ are nonzero, the independent action carries $T_b$ to $T_a$ by scaling its first slot coordinatewise by $a_i/b_i$. A common transport between the forms forces a permutation of the coordinates under which the two weights differ by nonzero cubes. To see this, evaluate both transported forms at $(x,y,z)$ and $(xy,1,z)$. Point separation in the final slot gives $T(x)T(y)=T(1)T(xy)$ with all multiplications coordinatewise. Surjectivity forces $T(1)$ to be a unit. Dividing by it gives a unital algebra equivalence of the split product. Every homomorphism from the split product to the field is evaluation at a coordinate. Comparing the transported values on those coordinate vectors gives the required cube relation.

For a prime $p$ with $p\equiv1\pmod 3$, the cubic character $x\mapsto x^{(p-1)/3}$ is invariant under multiplication by a nonzero cube. Thus a difference in the sums of characters gives a finite certificate that no common transport exists. For example, over $\mathbb F_7$ the profiles $(1,1)$ and $(1,2)$ have sums $2$ and $5$. [Lean proofs](C.lean)

The generator groups nonzero field elements by cubic class, enumerates ordered profiles modulo coordinate permutations, and removes repeated pairs under exchange of left and right and common weight scaling. It keeps 25 split diagonal contrasts over each of ten prime fields. Each of the 250 statements certifies independent equivalence and common-action inequivalence for a concrete pair. Its final residue computation is checked by Lean kernel reduction. The finite instances instantiate the same general proof. [Generator](C-gen.py)

The structure of separable higher-degree forms, including the field-level weight classification, goes back to Harrison and Pareigis. The application here is a uniform Lean construction and independent test data for comparing two tensor actions. The relevant structural prompts were the finite sum producer 85646 in motif 46, the separator motif 49, and primitive-root injectivity and divisibility producers 484851 and 79498 in motifs 91 and 168 of the frozen third list. These matches inspired a single-position test followed by an aggregate character test. [Frozen third list](queues/worker-3.json) · [Harrison and Pareigis](https://epub.ub.uni-muenchen.de/7099/1/7099.pdf) · [Grochow and Qiao](https://arxiv.org/abs/1907.00309)
