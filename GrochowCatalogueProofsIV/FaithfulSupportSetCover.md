# Weighted faithful support with listed stabilizers

## GP-0389

For a compact direct power of one fixed nonabelian simple group, deciding whether a faithful union of listed coset types has cost at most a binary budget is NP-complete, even when every candidate subgroup is given as a normal product of whole factors. On these instances the optimization is cost-preservingly equivalent to weighted Set Cover, and the number of selected orbit types is preserved.

Take a weighted Set Cover instance on $[m]$, with allowed sets $A_i$ and weights $w_i$, and fix $S=A_5$. Use $G=S^m$, represented by separate faithful constant-degree blocks for its factors. For each allowed set use the normal candidate
$$
   H_i=\prod_{j\notin A_i} S_j
$$
with cost $w_i$. The kernel of the coset action on $G/H_i$ is $H_i$ itself, and the kernel of a union is the intersection of the selected subgroups. For the selected indices $I$ this intersection is $\prod_{j\notin\bigcup_{i\in I} A_i}S_j$. It is trivial exactly when the sets cover $[m]$. All permutations and subgroup generator lists are polynomial in the Set Cover input. Nonnegative costs permit one copy of each chosen orbit type, since further copies cannot change the kernel.

Membership in NP for this class follows directly from the subset cover equivalence. If $G$ is supplied by a Cayley table, membership of each element in a normal core is checked by enumerating its conjugates. More generally, whenever the minimal normal subgroups $N_j$ of $G$ are explicitly listed, the exact candidate set for a subgroup $H_i$ is $\{j:N_j\not\le H_i\}$. Indeed $N_j$ is normal, so containment in $H_i$ is equivalent to containment in the core, and an intersection of cores is trivial exactly when it contains no minimal normal subgroup. This recovers Set Cover for any such input representation, including Fitting-free groups with supplied simple direct factors of the socle, whose minimal normals are the products over the conjugation orbits on those factors.

In the Cayley-table model with Fitting-free socle, the number of minimal normal subgroups is at most $\log_2|G|$. The exact Set Cover dynamic program over subsets of them is thus polynomial once they are identified. For an explicit table they can be identified by taking all normal closures of individual nonidentity elements and retaining the inclusion-minimal ones. Every minimal normal subgroup is the normal closure of any of its nonidentity elements. This explains why the compact lower bound need not apply under the table encoding.

This reduction uses the kernel-intersection criterion from the portfolio's faithful-action work and allows arbitrary listed costs. [Earlier minimum-action model](https://github.com/Dugongue/MathProofs/blob/d7366c4348bc03f0e93cb8674db191de32ba58bf/GrochowGroupFrontier/MinimumAction.md) · [Source context](https://arxiv.org/html/2501.16039v3)
