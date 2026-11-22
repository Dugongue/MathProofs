# The cost of a determinant-one correction

The Ceva construction lets one supplied-transporter correction use ordinary tensor-isomorphism witnesses on several edges. The minimum cost of those witnesses is exactly a graph deletion optimum with one condition per relevant prime. One prime gives a deterministic exact algorithm. Two prime-modulus conditions give an exact randomized algorithm. Three primes already allow NP-completeness over the fixed field $\mathbb F_{31}$, even when every ordinary witness is the identity. [Ceva determinant-image and witness theorem](https://github.com/Dugongue/MathProofs/blob/main/PolyhedralTensorDeterminants/A.md)

## Exact optimization

Use the Ceva graph construction with a fixed finite commutative local ring $R$, a subgroup $\Gamma\le R^\times$, a connected graph $G=(V,E)$, integral vertex charges $b_v$ summing to zero, and a target determinant $\delta\in\Gamma$. Each edge $e$ has a nonnegative rational cost $c_e$. A feasible assignment $g:V\to\Gamma$ is constant on every ordinary no-edge and satisfies
$$
 \prod_{v\in V}g_v^{b_v}=\delta.
$$
Its cost is the sum of $c_{vw}$ on edges with $g_v\ne g_w$. In the algebra this is the cost of the nonidentity side ratios. A correction matrix recovers those ordinary witnesses, and those witnesses implement the assignment by the Ceva theorem. Thus minimizing this cost minimizes the ordinary-witness support of a genuine determinant-one correction in the given construction.

Contract the connected components of the ordinary no-edge graph. Sum the charges in each component, discard loops, and sum costs on parallel edges. In the resulting undirected graph, every edge is available. The ordinary edge statuses are supplied to the algorithm below. Alternatively, one call per edge to an ordinary tensor-isomorphism decision oracle determines them. A search witness is needed only on the crossing edges used by the returned correction.

Write $m=\exp\Gamma$, and for each $p\mid m$ put $s_p=v_p(m)$. Let $\delta_p$ be the $p$-primary component of $\delta$ in the Sylow subgroup $\Gamma_p$. Define
$$
 a_p=\max\{a\in\{0,\ldots,s_p\}:\delta_p\in\Gamma_p^{p^a}\}.
$$
Call $p$ active when $a_p<s_p$, and set $q_p=p^{a_p+1}$ for an active prime. These group calculations are constant size for fixed $R$. For a subset $C$ of contracted vertices write $b(C)=\sum_{v\in C}b_v$.

**Theorem.** The minimum correction cost equals
$$
 \min\left\{\sum_{e\in F}c_e:
   F\subseteq E,\quad
   \forall p\text{ active},\
   \exists C\in\pi_0(G-F)\text{ with }b(C)\not\equiv0\pmod{q_p}
   \right\}.                                                     \tag{1}
$$
Both optima are $+\infty$ when the common feasibility test fails. A feasible deletion set gives a correction supported on a subset of the deleted edges.

**Proof.** If $g$ is feasible, delete its crossing edges. Every remaining component has a constant label. Conversely, prescribing a label freely on each component of $G-F$ gives a possible determinant exactly in $\Gamma^d$, where
$$
 d=\gcd\bigl(m,\{b(C):C\in\pi_0(G-F)\}\bigr).
$$
To see this directly, express $d$ as an integral combination of $m$ and the $b(C)$. For $t^d=\delta$, with $t\in\Gamma$, assign $t$ raised to the coefficient of $b(C)$ on that component. The product is $\delta$ because $t^m=1$. Conversely each $b(C)$ is divisible by $d$, so every product belongs to $\Gamma^d$.

On $\Gamma_p$, an exponent coprime to $p$ induces an automorphism. Therefore $\delta\in\Gamma^d$ holds exactly when $v_p(d)\le a_p$ at every active prime. This is equivalent to the component nondivisibility test in (1). The component labels just constructed cross only deleted edges. Together with deletion of the crossing edges from any assignment, this proves equality of the optima. $\square$

## One active prime and simultaneous bounds

For one active prime with modulus $q_p$, (1) reduces to a minimum cut $\partial S$ with $b(S)\ne0$ in $\mathbb Z/q_p$. From a feasible deletion choose a component with nonzero charge. Its boundary has cost at most the deletion cost. Conversely, deleting the boundary of a nonzero-charge set leaves at least one nonzero-charge component within that set.

One Gomory–Hu tree for the contracted capacitated graph yields an optimum. Root the tree at $r$, and write $C_e$ for the child side of a rooted edge $e=(u,v)$. For every vertex subset $S$, there is the integer indicator identity
$$
 1_S=1_S(r)\,1_V+\sum_{e=(u,v)}
       \bigl(1_S(v)-1_S(u)\bigr)1_{C_e}.
$$
The equality follows by telescoping on the tree path from the root to each vertex. Multiplying by the vertex charges and summing drops the constant term, since $b(V)=0$. Thus if $b(S)$ is nonzero modulo $q_p$, some tree edge crossing $S$ has $b(C_e)$ nonzero modulo $q_p$. Its fundamental cut has cost at most $c(\partial S)$, because it is a minimum cut between the endpoints of that edge. Minimize the cost among all such tree cuts. This proof works over any abelian charge group. In the parity case it recovers the minimum odd-cut method of Padberg and Rao. [Gomory and Hu](https://doi.org/10.1137/0109047) · [Letchford, Reinelt and Theis on odd cuts](https://arxiv.org/abs/math/0607088)

With $k\ge1$ active primes, compute a minimum one-prime cut for each prime using the same tree and delete their union. The corresponding condition continues to hold after further deletion. A formerly nonzero component is a disjoint union of new components, at least one of which must remain nonzero in that modulus. Each one-prime optimum lower-bounds the joint optimum, so the returned correction is a deterministic $k$-approximation. If a one-prime cut is missing, the joint problem is infeasible. If there are no active primes, $\delta=1$ and a constant assignment has cost zero.

## Two active primes

For two active primes the exact optimum in (1) is the minimum cost of a single cut with
$$
 b(S)\not\equiv0\pmod{q_1}
 \quad\text{and}\quad b(S)\not\equiv0\pmod{q_2}.
$$
Indeed, given a feasible deletion, use a component with both charges nonzero if one exists. Otherwise choose a component with the first charge nonzero and one with the second nonzero. Each has zero charge in the other's modulus, so their union has both charges nonzero. In either case its boundary lies among the deleted edges. Conversely a cut satisfying both conditions admits a two-label correction. Its two sides have charges $b(S)$ and $-b(S)$, and (1) supplies a label ratio yielding $\delta$.

If the two thresholds are primes, $q_1=p$ and $q_2=q$, reduce to a constant number of congruency-constrained minimum cuts modulo $pq$. Use one instance for each residue that is nonzero modulo both primes, replacing each signed charge by its residue in $\{0,\ldots,pq-1\}$. Nägele and Zenklusen prove randomized polynomial-time exact optimization with high probability for the product of two primes. Their input includes nonnegative rational edge costs and integer vertex multiplicities. Taking the best computed feasible cut and lifting the labels gives the claimed randomized exact algorithm. For arbitrary prime-power thresholds, the same reduction uses modulus $q_1q_2$, and the characterization by one cut and deterministic factor-2 bound still apply. [Nägele and Zenklusen, Theorem 2](https://doi.org/10.1007/s10107-020-01498-x)

## Three-terminal hardness over a fixed field

Take $R=\mathbb F_{31}$, $\Gamma=R^\times$, and $\delta=3$, which has order 30. The three active primes are 2, 3 and 5, with $a_p=0$. Given a weighted three-terminal multiway cut instance with terminals $u,v,w$, assign charges
$$
 b_u=9,\qquad b_v=25,\qquad b_w=-34,\qquad
 b_x=0\quad (x\notin\{u,v,w\}).
$$
For every edge use identical scalar multiplication tensors, so the ordinary witness is known. Use the original costs. Modulo 2 the charges are $+1,-1$ at $u,v$, modulo 3 they are $+1,-1$ at $v,w$, and modulo 5 they are $-1,+1$ at $u,w$. In each modulus there is a nonzero-charge component exactly when the corresponding pair of terminals is disconnected. Therefore (1) is exactly three-terminal multiway cut, with the same optimum and a direct witness conversion. Parallel edges may be combined, and disconnected graphs can be made connected with zero-cost edges.

For a direct algebra witness in the reverse direction, use exponents $0,1,6$ on the three respective terminal components, and exponent zero on every remaining component. The determinant exponent is $9\cdot0+25\cdot1-34\cdot6\equiv1\pmod{30}$. Conversely a correction cannot assign equal labels to any terminal pair. The determinant exponent would be divisible by the prime dedicated to that pair. The algebra and the supplied ordinary transporter have polynomial size by the Ceva theorem over the fixed field.

Three-terminal multiway cut is NP-hard even with unit edge costs. Hardness holds on connected instances, because an instance with terminals in different components reduces to at most one ordinary two-terminal cut, and components without terminals may be discarded. Parallel unit edges can be replaced by separate paths of length two. Each path contributes optimal crossing cost 1 when its endpoints have different labels, and 0 otherwise. Thus the reduction also works for simple connected graphs with all costs 1. The budgeted problem for this explicitly presented Ceva family is in NP because the label assignment, its product and its weighted crossing sum are checkable in polynomial time. Thus the budgeted problem is NP-complete already for the all-yes $\mathbb F_{31}$ family. Ordinary correction existence is automatic on these instances, since the three terminals can always be separated by deleting enough edges. A finite optimum always exists. More generally the same reduction works for any fixed $\Gamma$ whose exponent has at least three distinct prime divisors. Pick three primary components of maximal order, pick a generator in a maximal cyclic factor of each, and use the identity on other primary components to define the target. The three chosen thresholds are the three primes. Apply CRT to the two positive terminal weight choices, and define the third as minus their sum. [Dahlhaus, Johnson, Papadimitriou, Seymour and Yannakakis](https://doi.org/10.1137/S0097539792225297)

These are written proofs for the Ceva algebra family with its graph, charges, costs and target provided. The cut algorithms and multiway cut hardness are established. The contribution is the exact cost-preserving correspondence and the distinction between one, two prime-modulus, and three active primes for this determinant-one witness problem. Bibliographic priority for that combination remains open. The finite control checks 126 label/deletion comparisons, with a binary-cut comparison for each case with at most two active primes. It also checks 64 three-terminal cut instances and all 27,000 triples of terminal exponents modulo 30. [Finite control](BCheck.py)

Lean checks the two-coordinate merging step and the exact three-terminal character, including separation and its converse. The cost identity, cut algorithm and complexity statements use the written proofs above. [Lean source](B.lean)
