# Graph isomorphism encoded in graph-state local-unitary transport

## GP-0973

Labeled graph-state local-unitary transport with an arbitrary common qubit permutation is at least as hard as ordinary graph isomorphism under a linear-size mapping of the graphs. There is an explicit restricted family on which the decision problems are polynomial-time equivalent. The reduction preserves a graph as a graph-state rather than passing through arbitrary state amplitudes.

Given a finite simple graph $G$ on $n$ vertices, attach two private leaves to every vertex, writing $G^+$ for the resulting graph. In the graph state $|G^+\rangle$, apply a Hadamard to every private leaf. The transformed state in computational coordinates is
$$
|\Psi_G\rangle = 2^{-n/2}\sum_{x\in \mathbb F_2^n}
(-1)^{q_G(x)}\bigotimes_{i=1}^n|x_i,x_i,x_i\rangle,\qquad
q_G(x)=\sum_{ij\in E(G),\,i<j}x_ix_j\pmod2 .
$$
Indeed, the leaf bits occur only through the controlled sign with their own core bit, and applying the Hadamard maps the corresponding $|+\rangle$ or $|-\rangle$ to that core bit. This change of basis is the two-private-leaf case of the core-graph state representation. [Core-graph representation, Proposition 2.3](https://arxiv.org/html/2610.26814v1#S2.SS2)

Applying local Clifford changes separately to the input and target leaves preserves LU equivalence even when a qubit permutation is allowed, since such permutations normalize the group of products of one-qubit unitaries.

For a pair of qubits in the same triple, the two-site reduced density matrix is $(I+Z\otimes Z)/4$. For a pair in different triples it is $I/4$. The diagonals follow because $x$ is uniform. An off-diagonal term vanishes on tracing out the complement, since any change of an $x_i$ changes three qubits and a given pair misses at least one. The spectra therefore identify the triple partition from the state in a way invariant under local unitaries and a global qubit permutation. Every equivalence maps each triple to a triple. Moreover preservation of the rank-two marginal fixes the product $Z\otimes Z$, and hence each local unitary maps $Z$ to $Z$ or $-Z$. Thus each factor is monomial in these coordinates. Within each triple the mask of bit flips must be constant in order to preserve the support with equal triple bits. The accumulated phases are a scalar times $\prod_i e^{2\pi i\theta_i x_i}$ for real turns $\theta_i$.

After relabeling triples by the induced permutation, an equivalence now implies that the mixed second differences of $q_G(x)$ and $q_H(x+b)$ agree modulo two for every pair of distinct coordinates, where $b$ is the common triple flip mask. To see this directly, divide the amplitude relations at $e_i+e_j$ and $0$ by those at $e_i$ and $e_j$. Global and single-coordinate phases cancel and the result is exactly $(-1)^{A_{G,ij}}=(-1)^{A_{H,ij}}$. A constant binary translation $b$ affects only lower-degree terms of the Boolean quadratic form. Hence the induced triple permutation is a graph isomorphism. Conversely a graph isomorphism extends to a qubit permutation matching the two graph states with identical local factors. The core graph can be extracted from a displayed leaf-gadget input by retaining vertices having at least two degree-one neighbors, giving the reverse decision reduction on this family.

This is an exact lower reduction and a complete classification on the indicated image class. It leaves the upper reduction on unrestricted graph states open. The two-qubit axis recovery is also used in the accompanying exact algorithms for prescribed monomial transport. [Graph-state local equivalence and foliage invariants](https://arxiv.org/abs/2305.07645) · [Labeled LU equivalence](https://arxiv.org/abs/2610.00527)
