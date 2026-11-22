# Single-tensor reductions for cubics in characteristic three

Let $f$ be a formal homogeneous cubic on $n$ variables over an explicitly given finite field of characteristic three. Can one construct, in deterministic polynomial time, one ordinary three-tensor with all sides $O(n)$ from each input, such that equivalence is preserved in both directions and every tensor isomorphism yields a cubic change of variables? The unrestricted question remains open in this work.

## A linear-side theorem for entire polarization fibers

Write $P=\pi f$ for the polarization and put $J_P(A)(x)=P(Ax,x,x)/2$. Two tests on coefficient matrices suffice. Check that $P$ belongs to the image of $\pi J_P$ and that $\ker(\pi J_P)=\ker J_P$. Whenever these hold, **every cubic with polarization $P$ has a single ordinary tensor of side exactly $n+c+9\le 2n+9$**, where $c$ is the rank of $v\mapsto P(v,-,-)$. An arbitrary isomorphism of these tensors yields an explicit invertible substitution $S$ with $f=g\circ S$. [Fiber theorem](Fibers.md) · [Dimension bound and transporter proof](Compact.md)

The tests pick out a unique cubic $u_P$ with polarization $P$ among the infinitesimal linear substitutions of $f$. Every refinement then has the unique expression $u_P+\ell^3$. Recovering the missing linear form $\ell$ takes inverse Frobenius on coefficients. A triangular algebra encodes $(P,\ell)$ in its multiplication tensor. In the example $F=\sum_i y_i(x_i^2+x_ix_{i+1})$ with cyclic indices and at least four pairs, the theorem covers every $F+\ell^3$. It distinguishes $F$ from $F+y_1^3$ even though they have identical polarizations. With four pairs the tensors have shape $25\times25\times25$. A small example outside the tests is $x^2y$, since the infinitesimal substitution $y\mapsto y+tx$ gives the nonzero pure cube $x^3$. [Example and proof](Fibers.md) · [Python encoder and decoder](compact.py)

## Further sufficient conditions and a second target

| Inputs | Target and bound |
| --- | --- |
| Cubics whose polarization has intrinsic blocks of dimensions $d_i$ over a splitting field | One ordinary tensor with sides $O(n+\sum_{i\text{ active}}\binom{d_i}{2})$. A block is active if its internal polarization is nonzero. The bound is linear on all $xQ(w)+\ell^3$ with $Q$ nonsingular on at least three variables. [Proof](Blocks.md) |
| Cubics with an intrinsic, efficiently computable spanning family of $O(n)$ subspaces of bounded dimension | One ordinary tensor of linear side. This includes a recognizable class $\sum_i y_ix_i^2+h(x)+\sum_i b_i y_i^3$ for arbitrary cubic $h$. [Proof and recognition algorithm](Frames.md) |
| Nonzero cubics $f$ in the image of $J_P$ | One ordinary tensor with sides $O(n+\dim\ker J_P)$. The construction records the entire affine space of preimages. [Proof](Euler.md) |
| Every formal cubic | One matrix **subgroup conjugacy** instance. The matrix degree is $2n+2$ for $q\ge9$ and at most $4n+4$ for $q=3$. For fixed $q$ and $n\ge2$ the groups are all abstractly isomorphic. A conjugating matrix recovers the cubic substitution. A linear-side reduction from these subgroups to ordinary tensor isomorphism is still missing. [Proof](Groups.md) · [Implementation](groups.py) |

## Verification and related results

The reduction theorems have written proofs. Lean independently checked the block comparison lemma with the standard axioms. It shows that a pure-cube discrepancy vanishes when its restrictions agree in sum along maps summing to the identity. The executable controls check the finite-field encoders and witness recovery, including independent tensor legs, a nonzero mark on the radical, and conjugators involving Frobenius. From this directory run `python check_compact.py`, `python check_euler.py` and `python check_groups.py`. [Lean source](Split.lean) · [Compact tensor checks](check_compact.py) · [Refinement checks](check_euler.py) · [Group checks](check_groups.py)

Grochow and Qiao supply the linear-length removal of tensor partitions used in several constructions here. The earlier project reduction over characteristic three uses an exterior-square space of quadratic dimension. The exact side bound and witness-recovery claims above concern the stated classes. Publication priority has not been established. [Grochow and Qiao, Part IV](https://arxiv.org/abs/2306.16317) · [Grochow and Qiao, STOC](https://doi.org/10.1145/3717823.3718282) · [Earlier characteristic-three construction](https://github.com/Dugongue/MathProofs/blob/main/GrochowPureCube/Tensor.md)
