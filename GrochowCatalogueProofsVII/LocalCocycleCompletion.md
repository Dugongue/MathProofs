# Completing compact modular cocycles from local restrictions

## GP-0412

Fix a prime $p$. Let $Q=(C_p)^r$ be specified by a basis, and let an arbitrary finite-dimensional $\mathbb F_pQ$-module $M$ be given by the commuting action matrices of its basis generators. Given explicitly tabulated normalized cocycles on any displayed family of subgroups of $Q$, one can decide whether their exact restrictions come from a common normalized cocycle on $Q$. If they do, one can output a polynomial-size evaluator that computes its value on any pair of vectors of $Q$. Time is polynomial in the compact module presentation and the total local-table sizes. The algorithm makes no semisimplicity assumption and does not enumerate $Q$. [Cohomological extension data](https://arxiv.org/abs/1309.1776)

### Local consistency of a collector

Let $T_i$ denote the actions on $M$ and let $x_i$ denote chosen lifts of the basis elements. Encode an extension by unknowns $a_i,c_{ji}\in M$ for
$$
x_i^p=a_i,\qquad x_jx_i=c_{ji}x_ix_j\quad(j>i),\qquad x_i m=(T_i m)x_i.
$$
Here juxtaposition with an element of the kernel means a kernel letter, and consecutive kernel letters are added. The normal forms are one kernel element followed by $x_1^{b_1}\cdots x_r^{b_r}$ with $0\le b_i<p$. Direct the displayed identities toward those forms and delete zero kernel letters. The reductions terminate: first measure the number of lift letters, then the number of inverted pairs of lift letters, then the number of lift letters to the left of kernel letters summed over all kernel letters, and finally the number of kernel letters. Each directed reduction strictly decreases this tuple lexicographically.

It is sufficient that the displayed relations be realizable on every coordinate subgroup on at most three basis elements, using that subgroup's restricted action. Indeed disjoint reductions commute. An overlapping pair of left sides can involve at most three distinct lift indices, since the only nontrivial left sides for lift letters alone are descending adjacent pairs and pure powers. Overlaps involving kernel moves, addition or deletion also involve at most three lift indices. In each such coordinate subgroup the two resulting words reduce to identical normal forms: the stipulated local realization has exactly one kernel element with each quotient word of the specified form, once the word's evaluation is fixed. Therefore every overlap is joinable. Termination and the local confluence lemma give unique normal forms. These forms define an associative monoid via the presentation, and each generator is invertible, since each $x_i^p$ is in the invertible kernel and this power commutes with $x_i$. The monoid is a group with the stated kernel, quotient and action. Conversely any extension gives all the required local realizations by restriction.

### Linear constraints and the exact restrictions

Introduce variables for the $a_i,c_{ji}$ and for one normalized cochain on each coordinate subgroup on at most three basis elements. Impose the cocycle equation on each such cochain. In the local crossed product
$$
(m,u)(n,v)=(m+u\cdot n+d(u,v),\,u+v),
$$
evaluate the power and ordered-product differences of the zero-kernel basis lifts. Require the resulting power and swap parameters to agree with the global variables $a_i,c_{ji}$. These constraints are linear over $\mathbb F_p$: multiplication has a fixed quotient projection, and the action matrices are fixed. Equivalently the swap parameter is the difference of the two local cocycle values at $(e_j,e_i)$ and $(e_i,e_j)$. There are $O(r^3)$ coordinate subgroups of sizes at most $p^3$.

For any parameter vector, define $f_\theta(u,v)$ by collecting the concatenation of the two ordered section words using a fixed deterministic sequence. The normal-form quotient exponents and every chosen swap or power-reduction position can be determined without reading the values of the kernel letters. Move new kernel letters immediately to the left using known actions, combining them into one vector. Thus the resulting coordinate in $M$ is linear in the parameter vector $\theta$. Its computation uses polynomially many field operations: the initial word has at most $2r(p-1)$ lift letters, every swap decreases inversions, and each kernel contribution crosses at most the word length. For solutions of the local constraints above this evaluator is precisely the cocycle of the ordered section.

For each element $u$ in the union of the supplied subgroups introduce one shared unknown $t(u)\in M$, with $t(0)=0$. Impose for all supplied pairs inside one subgroup $U$
$$
f_\theta(u,v)+t(u)+u\cdot t(v)-t(u+v)=d_U(u,v).
$$
Use one unknown per element even when several tables overlap. All constraints form one polynomial-size linear system. A solution gives the exact desired cocycle by the displayed coboundary correction, taking $t$ to be zero outside the union. Conversely a global cocycle determines an extension. Take its basis lifts, its collector parameters and its local cocycles, and compare its original section with the ordered section. Their section difference gives the shared $t$ and satisfies the system. This proves correctness in both directions and supplies a compact output even when the quotient has exponential order.
