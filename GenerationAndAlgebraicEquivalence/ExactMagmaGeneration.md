# Exact Minimum Generating Set for finite magmas is DP-complete

**Status.** Informal proof. This answers the explicit exact-generation question at the end of Section 7 of Collins, Grochow, Levet, and Weiß, *On the Constant-Depth Circuit Complexity of Generating Quasigroups*. The input is a finite magma specified by its full multiplication table, together with an integer $k$. The question is whether the smallest generating set has size exactly $k$. [Published paper](https://theoretics.episciences.org/16387/pdf) · [Section 7, HTML](https://arxiv.org/html/2402.00133#S7)

**Theorem.** Exact Minimum Generating Set for finite magmas is $\mathsf{DP}$-complete under polynomial-time many-one reductions. Hardness holds even if the multiplication is commutative, there is an absorbing zero, and every square equals zero.

Write $r(M)$ for the smallest cardinality of a subset of $M$ whose closure under multiplication is all of $M$. For a proposed generating set, repeatedly include all products of pairs already present. At most $|M|$ strict increases can occur, and each round uses at most $|M|^2$ table lookups. Thus $r(M)\le k$ is an NP predicate. The exact predicate is the difference of the NP predicates $r(M)\le k$ and $r(M)\le k-1$, so it belongs to $\mathsf{DP}$.

## A one-unit gap for satisfiability

Let $F$ be a CNF formula on $n$ variables with $m\ge 1$ nonempty clauses. This is an NP-complete form of satisfiability, and SAT–UNSAT for pairs of such formulas is $\mathsf{DP}$-complete. Indeed, for every difference $A\setminus B$ of two NP languages the two Cook–Levin reductions give a pair of such formulas encoding membership in $A$ and $B$. Formulas can be taken in ordinary 3-CNF with a fresh satisfiable clause on new variables if needed. [Papadimitriou and Yannakakis, *The Complexity of Facets (and Some Facets of Complexity)*](https://doi.org/10.1145/800070.802199)

Define $M_F$ with the following elements, all distinct except for the declared notation $a_1=s_1$ and $q=a_m$.

- An absorbing zero $0$.
- Two literal elements $t_i,f_i$ for each variable $i\in\{1,\dots,n\}$.
- A clause element $c_j$ and a satisfaction element $s_j$ for each $j\in\{1,\dots,m\}$.
- Prefix elements $a_2,\dots,a_m$ when $m\ge 2$.

The nonzero products are the following, together with their reversals.

1. $t_i c_j=s_j$ when variable $i$ occurs positively in clause $j$, and $f_i c_j=s_j$ when it occurs negatively.
2. $a_{j-1}s_j=a_j$ for $2\le j\le m$.
3. $qt_i=f_i$ and $qf_i=t_i$ for every $i$.

Every other product is zero. The three families of unordered input pairs are disjoint, and every listed pair has distinct entries. This includes $m=1$, when $q=s_1$ and the second family is empty. The table has $2n+3m$ elements and can be written in polynomial time. The literal-switch and clause structure adapts the satisfiability construction in Collins et al., Section 7.3. Here the prefix chain records exactly the conjunction of all clause successes. The one-unit gap also follows from their original interval construction, by adding its literal-switch element to the mandatory seeds when necessary.

Every generating set contains $c_j$ for each $j$, since no product has output $c_j$. It also contains at least one of $t_i,f_i$ for each $i$. The only products yielding a literal of variable $i$ require the other literal of that variable as an input. So $r(M_F)\ge n+m$, and any generating set of size $n+m$ consists of all clause elements and one literal per variable. Read those literals as an assignment.

If the assignment satisfies $F$, each $s_j$ is obtained from its clause element and a chosen literal. The prefix chain yields $q$, which gives all remaining literals. The square of any clause element gives zero. This generates the full table.

Conversely, suppose a set of size $n+m$ generates the table. Run the closure in rounds, using only elements from earlier rounds to obtain products at each round. No new literal can appear before $q$ appears, since its production requires $q$. If $m=1$, the first occurrence of $q=s_1$ already requires a chosen literal satisfying the clause. If $m\ge 2$, the only products yielding $a_j$ require both $a_{j-1}$ and $s_j$, so the first occurrence of $q$ entails the arrival of every $s_j$ strictly earlier. Each came from a chosen literal since $q$ was absent at all those steps. The assignment therefore satisfies $F$.

Finally, one can always generate the table using the clause elements, any one literal of each variable, and $q$ as an extra generator. The switch rules yield all literals, and each clause has at least one literal with which to produce its $s_j$. The prefix chain and a clause square give all remaining elements. Consequently,

$$
r(M_F)=n+m+\mathbf 1[F\text{ is unsatisfiable}].
$$

## Summing ranks

Take any positive number of disjoint copies of these magmas and identify their zeros. Within a copy preserve its products and set every cross-copy product to zero. The new multiplication is commutative and all squares are zero.

For each copy, adjoining zero to a subset cannot help generate a nonzero element. In the combined magma, an induction on closure rounds shows that nonzero elements of a copy can arise only from the seeds in that copy. For a generating set of the combined magma, those seeds include every clause element of the copy. They can therefore also produce zero by squaring a clause element. The restriction to each copy is a generating set for its whole magma, so the combined rank is at least the sum of the ranks. Conversely, a minimum generating set in each copy can omit zero, since the square of a mandatory clause element produces it. The union of these generating sets shows that the combined rank is the sum.

## The reduction to exact rank

On a SAT–UNSAT instance $(F,G)$, combine one copy of $M_F$ and two copies of $M_G$ by identifying their zeros as above. Put $b(F)=n_F+m_F$ and $b(G)=n_G+m_G$, and set

$$
k=b(F)+2b(G)+2.
$$

The combined rank minus $b(F)+2b(G)$ equals

$$
\mathbf 1[F\text{ is unsatisfiable}]+2\mathbf 1[G\text{ is unsatisfiable}].
$$

This value is 2 exactly when $F$ is satisfiable and $G$ is unsatisfiable. The table and $k$ are produced in polynomial time. This gives hardness for the specified restricted class, and together with membership resolves the exact problem for arbitrary finite magmas.
