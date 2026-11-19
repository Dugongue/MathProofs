# Halting in the entanglement of a commuting matrix-product family

**Informal theorem.** There are fixed local and bond dimensions, one fixed rational open-boundary matrix-product bulk tensor with pairwise commuting transfer matrices, and one fixed rational right end tensor with the following property. From a machine index $t$ one can compute a rational left end tensor. The chain with two endpoint qubits and $m\geq1$ internal sites defines a positive definite density matrix $\rho_{t,m}$ at every length. It is invariant under all permutations of its internal sites. Every proper physical-site marginal is exactly maximally mixed. Nevertheless, the set of indices for which the first qubit is entangled with the remaining sites at some length is computably enumerable complete under computable many-one reductions. If $t$ halts, this cut has negative partial transpose at all sufficiently large lengths. Otherwise every state in the family is fully separable.

At each length, $\rho_{t,m}$ is within $2^{-m}/4$ in trace norm of an explicit fully separable reference state independent of $t$. The decision problem concerns exact entanglement at an unbounded finite length. The chains have fixed site dimensions and a growing number of sites. Their marginals do not have to reproduce the shorter chains.

### Encoding a witness in a letter count

Let $K$ be the halting set. The Davis–Putnam–Robinson–Matiyasevich theorem gives a single integer polynomial $U(t,x_1,\ldots,x_s)$ such that $t\in K$ exactly when $U(t,k)=0$ for some $k\in\mathbb N^s$, where $0\in\mathbb N$. Both $s$ and the degree are fixed. This uses the established Diophantine representation over nonnegative integers. [Jones, Universal Diophantine Equation](https://doi.org/10.2307/2273588)

Fix the alphabet $\{0,\ldots,s\}$. For a word $w$ of length $m$, let $k_i(w)$ be the number of occurrences of the letter $i$ for $1\leq i\leq s$. A vector $k$ occurs at every positive length $m\geq\sum_i k_i$ by padding with the letter $0$. Put
$$
J_t(x)=1-2U(t,x)^2,\qquad L_t=\max\left(1,\sum_\alpha |[x^\alpha]J_t|\right).
$$
Take a fixed nonnegative upper bound $D$ on the degree of $J_t$ in $x$, and put $b=2^{D+1}$. Define
$$
F_{t,w}=\frac12+\frac{J_t(k(w))}{8L_t b^m}.
$$
Since $m\geq1$ and each $k_i\leq m$, we have $|J_t(k)|\leq L_t m^D\leq L_t2^{Dm}$. Consequently $|F_{t,w}-1/2|\leq 2^{-m}/8$, and $F_{t,w}>1/2$ exactly when $U(t,k(w))=0$. The integer square supplies a strict inequality on both sides.

### A full-rank state with a separability threshold

Let $P$ be the rational projector onto $(|00\rangle+|11\rangle)/\sqrt2$ and set
$$
\sigma(F)=F P+\frac{1-F}{3}(I_4-P).
$$
Its eigenvalues are $F$ and $(1-F)/3$ with multiplicities one and three, so it is positive definite on the whole interval used here. Each one-qubit marginal is $I_2/2$. Since $P^{T_1}$ is half the swap, the partial transpose has eigenvalues $1/2-F$ on the antisymmetric line and $(1+2F)/6$ on the three-dimensional symmetric subspace. The two-qubit PPT criterion therefore gives separability exactly when $F\leq1/2$. Separability here has its usual meaning on complex Hilbert spaces, even though the matrix entries are rational. [Horodecki, Horodecki and Horodecki, Separability of Mixed States](https://arxiv.org/abs/quant-ph/9605038)

### Hiding the witness from every proper marginal

Each internal site has orthogonal basis labels $(a,g)$ with $a\in\{0,\ldots,s\}$ and $g\in G=(\mathbb Z/2)^2$. Write $q=4(s+1)$ for the site dimension. Choose all $m$ pairs independently and uniformly. Conditional on the classical basis string with letter-word $w$ and keys $g_1,\ldots,g_m$, put the endpoints in the state
$$
(I\otimes V_h)\sigma(F_{t,w})(I\otimes V_h)^*,\qquad
h=\sum_i g_i,\qquad V_{(u,v)}=X^uZ^v .
$$
Thus $\rho_{t,m}$ is block diagonal in the middle string with each conditional endpoint state multiplied by $q^{-m}$. The real Pauli representatives give rational entries. The formula proves normalization, strict positivity and internal permutation invariance. Tracing out either endpoint leaves a maximally mixed remaining endpoint for every classical string. Tracing out an internal site averages over one uniform independent key, which completely depolarizes the right endpoint qubit. For each fixed value of the erased letter the two endpoints become $I_4/4$, since the left endpoint already has marginal $I_2/2$. The remaining flags retain their uniform product law. Erasing any single site therefore yields the maximally mixed state, which proves the same for every proper marginal.

Partial transpose on the first endpoint acts independently on each flag block. If one letter string encodes a witness, its conditional endpoint state has a negative partial-transpose eigenvalue and so does the full state. If no string encodes a witness, each conditional endpoint state is separable by the two-qubit criterion. Tensoring each separable decomposition with its product of classical basis projectors gives a fully separable decomposition of the entire chain.

Let $\tau_m$ be the same flag-and-key mixture with $F$ replaced everywhere by $1/2$. Its full separability follows from that argument. In each flag block the unweighted trace-norm difference is $2|F-1/2|$, by the two common eigenspaces. The global trace norm is the uniformly weighted average of these differences, hence $\|\rho_{t,m}-\tau_m\|_1\leq 2^{-m}/4$.

### Explicit fixed commuting bulk

Use the column $v(x)$ of all monomials of total degree at most $D$, in a fixed order, with $v(0)$ its value at zero. Let $A_a$ be the fixed rational matrix satisfying $v(x+e_a)=A_a v(x)$, with $e_0=0$ and $e_1,\ldots,e_s$ the coordinate increments. These matrices commute because translations commute and monomials are linearly independent. If $c_t$ is the row of coefficients of $J_t/(8L_t)$, then
$$
c_t A_{a_1}\cdots A_{a_m}v(0)/b^m=F_{t,w}-1/2 .
$$
Keep a four-state virtual register with commuting permutation matrices $S_g$ acting on row basis vectors by $e_h^\top S_g=e_{h+g}^\top$. On the constant branch use $S_g/q$ and on the polynomial branch use $(S_g\otimes A_a)/(qb)$. Use their direct sum for the diagonal physical entry $(a,g)$, and zero for all off-diagonal physical entries. All virtual matrices commute. Make four identical copies indexed by the ordered pair $i,j\in\{0,1\}$ of left endpoint matrix indices. The left tensor for $(i,j)$ selects its copy, with constant row $e_0^\top$ and polynomial row $e_0^\top\otimes c_t$.

To specify the right tensor, write $C=\sigma(1/2)$ and $E=P-(I_4-P)/3$, so $\sigma(F)=C+(F-1/2)E$. For $H\in\{C,E\}$ denote by $H_h$ its conjugate by $I\otimes V_h$. Given right endpoint row and column indices $r,l$, the terminal column on copy $(i,j)$ has constant-branch entries $(C_h)_{ir,jl}$ at key $h$ and polynomial-branch vector $(E_h)_{ir,jl}\,v(0)$ at that key. This column is fixed and rational. Contraction yields exactly the required endpoint matrix entry times $q^{-m}$. The dimensions of every bulk matrix depend only on $s$ and $D$. Only $c_t$ in the left tensor varies with the input.

### Decision classification and scope

If $t$ halts, choose a witness $k$ and pad it at every $m\geq\max(1,\sum k_i)$. At all these lengths $\rho_{t,m}$ has a negative partial transpose. If $t$ never halts, every length gives a fully separable state. Conversely, lengths and words can be enumerated and $U(t,k(w))=0$ is exactly testable. This proves computable enumerability and completeness for the indexed family. It also rules out any computable upper bound on the first entangled length for halting inputs as a function of the description size. At a given finite length the question can be decided by the explicit rational tests above.

Earlier results established undecidability of testing positivity over unbounded MPO lengths and limitations on uniform local purifications. The result here promises strict positivity and decides where entanglement occurs in a commuting bulk with identical proper marginals. This is an informal deduction. Publication priority for this particular set of restrictions has not been established. [Kliesch, Gross and Eisert](https://doi.org/10.1103/PhysRevLett.113.160503) · [De las Cuevas, Cubitt, Cirac, Wolf and Pérez-García](https://arxiv.org/abs/1512.05709)
