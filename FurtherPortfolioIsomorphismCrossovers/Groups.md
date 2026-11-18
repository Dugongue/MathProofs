# Quasipolynomial-time minimum generation of finite semigroups

**Theorem.** A deterministic algorithm given the complete Cayley table of any finite semigroup $S$ outputs a minimum-cardinality generating set in $|S|^{O(1+\log |S|)}$ time. The algorithm takes polynomial time when the orders of the nonabelian chief factors of the maximal subgroups are bounded by a fixed constant. This includes every finite semigroup with solvable maximal subgroups, with no bound on their orders or derived lengths. Here a maximal subgroup is the Green $\mathcal H$-class of an idempotent, and generation uses nonempty products. The theorem allows arbitrary nonregular classes and arbitrarily many regular classes. It gives an upper bound for [Collins–Grochow–Levet–Weiß, Question 8.3](https://arxiv.org/html/2402.00133#S8).

For finite inverse semigroups both runtime conclusions also hold when the generating operation includes inversion. Fleischer, Stober, Thumm, and Weiß study that generation convention in the succinct partial-bijection model. [Membership and Conjugacy in Inverse Semigroups, Sections 2 and 8](https://doi.org/10.4230/LIPIcs.ICALP.2025.156).

The algorithm uses a more general group problem. Its input is a Cayley table for $G$, a list of subgroups $H_1,\ldots,H_c$ given as element lists, and a nonnegative integer $r$. It seeks $g_1,\ldots,g_c,x_1,\ldots,x_r\in G$ satisfying

$$
G=\left\langle g_iH_i g_i^{-1}\ (1\le i\le c),\ x_1,\ldots,x_r\right\rangle .
\tag{1}
$$

**Group theorem.** For a finite $G$ whose nonabelian chief factors have order at most a fixed $M$, (1) can be decided and witnesses found in deterministic polynomial time. The algorithm also gives the exact number of ordered witnesses $(g_1,\dots,g_c,x_1,\dots,x_r)$. Runtime is polynomial in the table and list lengths and in $r$, which accounts for the $r$ output positions. It suffices to use $r\le \lceil\log_2 |G|\rceil$ when finding the smallest feasible value.

## 1. Group algorithm at an abelian chief factor

The trivial group is the base case. Find a minimal nonidentity normal subgroup $A$ by taking the smallest nonidentity normal closure of a single group element. Normal closures and quotients are computable directly from the table. When $A$ is abelian, it is an elementary abelian $p$-group. Conjugation gives an action of $K=G/A$ on this vector space.

Recurse on $K$ with the images of the $H_i$ and the same $r$. If the quotient call fails, (1) is impossible. Otherwise fix its witnesses $k_i,y_j\in K$. Any lift of them gives a subgroup $W$ surjecting onto $K$. Then $W\cap A$ is normal under $W$ and under $A$, hence under $G=AW$. By minimality of $A$, a proper $W$ must have $W\cap A=1$ and is a complement. Thus any lift works if the extension does not split or if any $H_i\cap A\ne 1$.

Splitting is decidable and a splitting computable by linear algebra. From a table section $\sigma$ with $\sigma(1)=1$, compute the factor set $t(u,v)$ defined by $\sigma(u)\sigma(v)=t(u,v)\sigma(uv)$. A splitting consists of vectors $d(u)\in A$ satisfying

$$
d(uv)=d(u)+u\cdot d(v)+t(u,v) \qquad(u,v\in K).
$$

For the remaining case write $G=A\rtimes K$ using such a splitting, with multiplication $(a,u)(b,v)=(a+u\cdot b,uv)$. Let $K_i$ be the image of $H_i$. Each $H_i$ is the graph of a cocycle $b_i:K_i\to A$. The complements of $A$ in $G$ are exactly the graphs of cocycles $f$ on $K$, where $f(uv)=f(u)+u\cdot f(v)$.

For fixed quotient witnesses $k_i,y_j$, write the lift variables as $(a_i,k_i)$ and $(z_j,y_j)$. The lifts fail exactly when there exists a complement cocycle $f$ containing every conjugated $H_i$ and free element. This condition is the projection onto the variables $a_i,z_j$ of the affine linear equations

$$
\begin{aligned}
 f(k_i h k_i^{-1}) &= k_i\cdot b_i(h)+(1-k_i h k_i^{-1})\cdot a_i
                        &&(h\in K_i),\\
 f(y_j)&=z_j .
\end{aligned}
\tag{2}
$$

If the projection is empty, take any lift. If the projection is a proper affine subspace, Gaussian elimination supplies a vector outside it. If the projection is the entire space, we must establish that choosing different quotient witnesses cannot help.

To do so, let $\mathcal F$ consist of the cocycles $f$ on $K$ such that, for every $i$, $f|_{K_i}-b_i$ is of the form $h\mapsto (1-h)\cdot u_i$ for some $u_i\in A$. This set is independent of the quotient witnesses. The identity

$$
f(k_i h k_i^{-1})
= k_i\cdot f(h)+(1-k_i h k_i^{-1})\cdot f(k_i)
$$

shows that the first line of (2) is solvable in the $a_i$ exactly for $f\in\mathcal F$. For any such $f$, the number of tuples $(a_i,z_j)$ satisfying (2) is $\prod_i |A^{K_i}|$. Indeed, the $a_i$ each vary by the fixed space of the conjugated $K_i$ and every $z_j$ is fixed. Distinct cocycles cannot share a tuple of lifts because their difference would vanish on $k_iK_ik_i^{-1}$ and all $y_j$, a generating collection for $K$, and the cocycle identity would make the difference zero everywhere.

Consequently the number of bad lift tuples is $|\mathcal F|\prod_i |A^{K_i}|$ for every generating tuple of quotient choices. The total number of lift tuples is always $|A|^{c+r}$. The result of the projection test therefore determines existence at this layer for *all* quotient witnesses. The exact number of good lifts can also be read directly from the dimension of the projection in (2), or is all of $|A|^{c+r}$ in the immediate cases. All actions and vector coordinates can be found by multiplication and greedy basis extension in the table of $A$.

## 2. Group algorithm at a nonabelian chief factor of bounded order

For any finite $G$ and normal subgroup $A$, let $\pi:G\to K=G/A$. Assume we are given generating quotient choices $k_i,y_j$. For a subgroup $W\le G$ with $\pi(W)=K$, let $F(W)$ count the lifts of this tuple that satisfy $g_iH_ig_i^{-1}\le W$ and $x_j\in W$ for every slot. This count is a product of separate slot counts. A different prescribed quotient conjugator $k_i'$ gives the same count, since $g_i\mapsto wg_i$ is a bijection between the eligible lifts when $w\in W$ projects to $k_i'k_i^{-1}$. There are always $|W\cap A|$ possible lifts in $W$ of each prescribed $y_j$. If $E(V)$ counts lifts generating exactly $V$, then

$$
F(W)=\sum_{\substack{V\le W\\\pi(V)=K}}E(V).
$$

Solving this recursion in increasing order of subgroup size shows that $E(G)$ is independent of the choice of generating quotient witnesses. This is the mixed subgroup-and-element version of the counting argument behind [Efrat's subgroup lifting theorem](https://doi.org/10.1090/S0002-9939-97-03917-8).

The requisite subgroups $W$ can all be listed. Enumerate subgroups $B\le A$ by enumerating generating lists of length at most $\log_2|A|$ and closing them under the group operation. This suffices because adjoining an element outside a subgroup at least doubles its order. If $W\cap A=B$, then $W\le N_G(B)$ since $B$ is normal in $W$. Discard $B$ if $N_G(B)$ does not surject onto $K$. Otherwise the desired $W$'s are exactly the preimages of subgroups of $N_G(B)/B$ which project isomorphically to $K$. Obtain a list generating $K$ with at most $\log_2|K|$ entries by the same doubling argument. Enumerate all lifts of that list in $N_G(B)/B$. There are at most $|A|^{\log_2|K|}$, because the kernel has order at most $|A|$. For each lift, generate its subgroup and retain it if its intersection with the kernel is trivial. Every subgroup projecting isomorphically to $K$ occurs because it supplies unique lifts of the chosen list. Remove duplicates. The number of candidates in both enumerations together is at most $|G|^{O(1+\log |A|)}$.

Compute the slot counts by inspecting the respective $\pi$-fibers, then obtain $E(G)$ by the displayed recursion on the explicitly listed subgroups. With the quotient choices fixed, the same recursion works if any prefix of lift slots is fixed, by updating the corresponding slot counts. Thus whenever $E(G)>0$, fixing one lift at a time and testing whether it still permits a positive $E(G)$ produces witnesses. At every chief layer the good lift count multiplies the count for the quotient, by independence of quotient choices. The arithmetic is exact with integers of at most $1+(c+r)\log_2 |G|$ bits. The recursive algorithm has at most $\log_2 |G|$ layers. If $M$ is the maximum of 2 and the orders of the nonabelian chief factors, the time is $L^{O(1+\log M)}$, where $L$ is the table and list input length plus $r$. This gives both the quasipolynomial and polynomial bounds.

## 3. Decomposition along Green classes

Write $J$ for a Green $\mathcal J$-class and $U=\{u\in S:J<_\mathcal J J(u)\}$. A product in $J$ can use only letters from classes at least $J$, because the principal two-sided ideal of a product lies in that of every factor. Define $B=J\cap\langle U\rangle$. The minimum number of generators that must be selected in $J$ is exactly the minimum size of $X\subseteq J$ such that $J\subseteq\langle U\cup X\rangle$. Lower bounds follow by applying the product observation to any generating set. Upper bounds follow by processing the classes from larger to smaller, with all the elements of $U$ already generated before each class. Thus the local objectives add.

All Green classes and their partial order can be read from the principal ideals in the table. The set $B$ can be found by closure following table multiplication. In a nonregular class, any product of two class elements drops to a strictly smaller class, by the principal-factor theorem. Build the directed graph on $J$ with arcs $x\to ux$ and $x\to xu$ whenever $u\in U$ and the product lies in $J$. A product landing in $J$ and containing a letter of $J$ can contain only one such letter. Otherwise, splitting the word between two such letters gives a product of two elements of $J$. The graph therefore computes exactly the elements generated from $B$ and a set of chosen class elements. Mark the vertices reachable from $B$ and choose a representative of each source strongly connected component of the remaining graph. Each such component requires a seed and these seeds generate every remaining component.

## 4. Regular classes as labelled digraphs

For a regular $J$, the Rees theorem describes its principal factor as a completely zero-simple Rees matrix semigroup. Let $I,\Lambda$ index the $\mathcal R$- and $\mathcal L$-classes, let $G$ be a maximal subgroup in $J$, and write the elements of $J$ as $(i,g,\lambda)$ with multiplication

$$
(i,g,\lambda)(j,h,\mu)=(i,gP_{\lambda j}h,\mu)
$$

when $P_{\lambda j}\in G$, with the product dropping from $J$ when $P_{\lambda j}=0$. Every row and column of $P$ has a nonzero entry. These coordinates are constructive from the table. Choose an idempotent $e$ in cell $(i_0,\lambda_0)$, use its group cell as $G$, and choose elements $a_i$ in $(i,\lambda_0)$ and $b_\lambda$ in $(i_0,\lambda)$, using $e$ for both distinguished choices. The coordinate bijections are $g\mapsto a_i g b_\lambda$. The sandwich entry is $b_\lambda a_j$ when it stays in $J$, and is zero otherwise. The bijections follow directly by multiplying in any Rees coordinates with the distinguished idempotent as identity in its cell.

Use disjoint vertex sets $I,\Lambda$, and weighted directed arcs as follows.

| Arc | Condition and label |
|---|---|
| $\lambda\to i$ | $P_{\lambda i}\ne0$, with label $P_{\lambda i}$ |
| $i\to\lambda$ | A triple $(i,g,\lambda)$ is in $B$, with label $g$ |
| $i'\to i$ | Some $u\in U$ acts on row $i$ by $(i,g,\lambda)\mapsto(i',d g,\lambda)$ inside $J$, with label $d$ |
| $\lambda\to\lambda'$ | Some $u\in U$ acts on column $\lambda$ by $(i,g,\lambda)\mapsto(i,g d,\lambda')$ inside $J$, with label $d$ |

The multiplier rules are uniform on a row or column as stated. By finite semigroup stability, if $u(i,1,\lambda_0)$ stays in $J$, it has the same $\mathcal L$-class, so it is $(i',d,\lambda_0)$. Every $(i,g,\lambda)$ is a product of $(i,1,\lambda_0)$ with a suitable element to its right, by a nonzero entry in row $\lambda_0$. Multiplying this equality by $u$ proves the uniform rule. Conversely, if the distinguished probe drops, every row element drops by the same equality and monotonicity. The right rule is symmetric. For stability on the left, if $ux$ and $x$ belong to the same $\mathcal J$-class, write $x=a u x b$ with $a,b\in S^1$; iterate and take an exponent making $b^m$ idempotent. Then $x b^m=x$, so $x=(au)^m x\in S^1(ux)$, and $x$ and $ux$ belong to the same $\mathcal L$-class.

A selected generator $(i,g,\lambda)$ adds an arc $i\to\lambda$ with label $g$. The generated triples in $J$ are exactly the $(i,g,\lambda)$ for which the resulting graph contains a directed path from $i$ to $\lambda$ with ordered label product $g$, allowing walks that repeat vertices. For the forward implication, a word with no class letters gives an element of $B$. Otherwise the class letters act as their chosen arcs, and all intervening upper letters can be attached on the applicable side of a class letter by the multiplier rules. A factor of a word producing an element in $J$ cannot drop below $J$ if it contains a class letter. When adjacent class elements multiply, the sandwich arc is exactly the extra label in their product. Conversely, cut any path $i\leadsto\lambda$ at its sandwich arcs. Each segment consists of row arcs, one arc for an element of $B$ or a chosen generator, and column arcs. It gives a generated element by the left and right multiplier rules. Sandwich arcs multiply the segment elements in $J$.

Generating all triples first requires the unlabelled graph to become strongly connected. In fact, reachability of every $\lambda$ from every $i$, together with the fact that every $\lambda$ has an outgoing sandwich arc and every $i$ an incoming one, gives strong connectivity. Once the graph is strongly connected, the labels of all closed directed walks at a base vertex form a subgroup $D\le G$, since they form a finite monoid in $G$. All labels occur between every $i$ and $\lambda$ if $D=G$, by inserting a suitable closed walk between routes to and from the base vertex. Conversely, when all labels occur from $i$ to $\lambda$, append a fixed path from $\lambda$ to $i$. Closed-walk labels at $i$ then cover $G$.

For calculating $D$, one can allow each arc to be reversed with inverse label. To verify this, choose directed paths from the base vertex to each $v$, with labels $\alpha_v$, and paths back, with labels $\beta_v$. An arc $u\to v$ with label $d$ has $\alpha_u d\beta_v,\alpha_v\beta_v\in D$, so its normalized label $\alpha_u d\alpha_v^{-1}$ is in $D$. Inverting those normalized labels and telescoping shows that permitting reversed arcs adds no closed-walk labels. In a weakly connected labelled graph with both directions allowed, normalizing along an undirected spanning tree shows that the group of closed-walk labels is generated by the normalized labels of the non-tree arcs.

## 5. Exact regular-class formula

Let $a$ be the minimum number of unlabelled arcs required for strong connectivity of the base graph, and let $c$ be its number of weakly connected components. For each weak component use an undirected spanning tree to compute its group of closed-walk labels $H_i\le G$, permitting inverses as above. Let $r$ be the least value for which (1) holds for these $H_i$. Then the local optimum is

$$
\boxed{\max\{a,\ c-1+r\}.}
\tag{3}
$$

The unrestricted strong-connectivity optimum $a$ can be obtained using the required arc types $I\to\Lambda$. Unless the graph is already strongly connected, let $s,t$ be the counts of source and sink strongly connected components, counting isolated components in both. Then $a=\max(s,t)$. Every sink component has an $I$-vertex and every source component has a $\Lambda$-vertex because of the sandwich arcs. Thus an arc from a sink to a source can always be implemented by a class element. For a constructive proof of the optimum, match sources to sinks in the bipartite reachability graph. A maximal matching suffices. Cyclically link each matched sink to the next matched source to make a strongly connected core. Every unmatched source reaches a matched sink, and every unmatched sink is reached by a matched source. Pair as many unmatched sinks with unmatched sources as possible, adding an arc from each paired sink to its source. Attach any remaining unmatched sources from the core or remaining unmatched sinks to the core. This uses $\max(s,t)$ arcs, and the lower bound follows by separately counting each source needing an incoming arc and each sink needing an outgoing arc.

For the other lower bound in (3), any feasible augmentation must include $c-1$ arcs joining the base weak components in a tree. Take these arcs and the within-component spanning trees as a global undirected spanning tree. The normalized labels of base arcs generate a conjugate of $H_i$ from each component, according to the transport from the global root to that component. All remaining new arcs contribute at most one additional label each. To generate $G$, (1) then requires at least $r$ such arcs.

For the upper bound, first select an unlabelled optimal augmentation, then add additional arc slots $I\to\Lambda$ until the count in (3) is met. Parallel slots are allowed. Keep the base spanning trees and choose a tree of $c-1$ added arcs between base weak components. The labels on these arcs can independently set the path transport from the global root to the local root of each other component. Hence they can realize the conjugates from (1) simultaneously. The conjugation of the global root's group can be set to the identity by simultaneously conjugating the witnesses in (1). Each other added arc has an arbitrary label, so its normalized label may be set to any desired $x_j$ or to the identity. The normalized labels now generate $G$, and the strongly connected graph gives all triples in $J$. Identical arc slots, if any, can be merged without changing the generated triples, preserving the upper bound.

## 6. Runtime and scope

For each class the graph, its labels, its reachability, and its spanning trees have polynomial size in the Cayley table. Solve (1) for successive $r$ up to $\lceil\log_2|G|\rceil$ to compute (3) and the generators. The bound on $r$ follows by adjoining elements outside the generated subgroup, which at least doubles its size each time. The group algorithm in Sections 1–2 then gives the claimed time bounds and witnesses. For the unrestricted search bound there is also a direct method. From any successful tuple of slot choices, select subgroup or element slots that strictly enlarge the subgroup generated so far, stopping at $G$. At most $\lfloor\log_2|G|\rfloor$ slots are needed. Enumerate those slots and their values in $G$, test generation, and fill any unused slots arbitrarily. In the nilpotent case $r$ can instead be computed as the maximum codimension across Sylow Frattini quotients of the spans of the projected $H_i$. Conjugation is trivial in these quotients and generators for distinct Sylow factors can be combined into the same $r$ slots.

## 7. An unrestricted equivalence

For arbitrary inputs, the Cayley-table minimum-generation decision problem is polynomial-time Turing equivalent to the decision problem in (1) with $r\ge1$.

In one direction use (3). If a regular class has $c\ge2$, making its graph strongly connected requires at least $c$ added arcs, since every weak component needs a new outgoing arc. Thus the formula only needs $\max(1,r)$, which is recoverable from a decision oracle restricted to positive $r$. If $c=1$, the zero case is equivalent to $H_1=G$, which can be tested directly. The nonregular classes require no oracle. These operations determine the minimum rank and hence answer any threshold query. A query with positive $r>\lceil\log_2|G|\rceil$ is automatically positive.

For the converse, append trivial subgroups to an instance of (1) so that $c\ge2$, which preserves feasibility. Use weighted partial bijections on the $2c$ points $1,\dots,c,1',\dots,c'$, where weights are in $G$ and the weight along a composition is the ordered product of weights. Consider the semigroup consisting of the empty map, every weighted single arrow $i\to j$ with $i,j$ among the unprimed points and weight in $G$, and for each $i$ the weighted partial identities on $\{i,i'\}$ whose weight at $i$ belongs to $H_i$ and whose weight at $i'$ is the identity. Multiplication composes left to right. Closure follows because products of the partial identities from different $i$'s are empty, products within one such group use its group law, and multiplying a single arrow by one of the partial identities keeps at most a single unprimed arrow.

The $c$ external groups are incomparable top classes, each requiring its positive-word group rank $\max(1,d(H_i))$. All the single arrows form one regular class with every external group strictly above it. The empty map is a product of unmatched single arrows because $c\ge2$. For the single-arrow class its base graph has $c$ weak components, each consisting of one row vertex and one column vertex. Each component has one sandwich arc from column to row and multipliers acting as loops, with precisely the weights from $H_i$. Products of external group elements never produce a single arrow, so the base graph has no arc from row to column. Thus $a=c$ and the local groups of closed walks in (3) are exactly the given $H_i$. If $r_0$ is the least feasible number of free generators, the semigroup's rank is

$$
\sum_i\max(1,d(H_i))+c-1+\max(1,r_0).
$$

All the $d(H_i)$ are polynomial-time computable by the Cayley-table minimum-generation algorithm for groups. One threshold query, with $r$ in place of $\max(1,r_0)$, decides the given positive-$r$ group problem. The semigroup table has polynomial size in the input. The constructed semigroup is inverse closed, so the same Turing equivalence holds restricted to finite inverse semigroup inputs with the positive-word convention. In fact the weighted partial bijections act on pairs $(i,x)$ with $x\in G$ by right-multiplying $x$ by the arrow weight, and their inverses belong to the listed set. Adjoining a global identity also gives the equivalence for inverse monoid inputs with that convention: the new identity must be selected, and otherwise leaves the minimum unchanged. [Lucchini–Thakkar, *The minimum generating set problem*](https://arxiv.org/abs/2306.07633).

## 8. Inverse-semigroup generation

Suppose now that selected generators may also be inverted. The general classwise reduction still holds: inversion preserves $\mathcal J$-classes, and $U$ is closed under inversion. Every class is regular. Its Rees matrix has exactly one nonzero in each row and column. Indeed, two nonzero entries $P_{\lambda i}$ and $P_{\lambda j}$ in the same row would yield two distinct idempotents whose ordered products are the two different idempotents, contradicting that idempotents commute. The column argument is symmetric. Relabel and normalize to take $P$ to be diagonal with entries $1$. Thus the index sets are paired, elements are weighted arrows $(i,g,j)$, and inversion reverses arrows and inverts labels.

Build a labelled graph on one copy of the index set. Include the arcs for all $B$ arrows and for the right actions of higher elements in $U$. For example, if $(i,g,j)u=(i,g d,j')$, include $j\to j'$ with label $d$. The arcs from $B$ have their inverses because $B$ is inverse closed. If $xu$ stays in $J$, stability gives $x\mathrel{\mathcal R}xu$, so $(xu)(xu)^{-1}=xx^{-1}$. Right multiply by $x$ and commute the idempotents $uu^{-1}$ and $x^{-1}x$ to obtain $(xu)u^{-1}=x$. Hence the action of $u^{-1}$ reverses the arc with inverse label. Left actions in the paired graph correspond to reversing right actions by the inverse law $(ux)^{-1}=x^{-1}u^{-1}$. Each selected generator contributes one arbitrary weighted arc together with its reverse.

The generated elements of $J$ are the labels of paths containing at least one arc from $B$ or a selected generator or its inverse. Such a path is interpreted as a product by applying upper actions on the left of its first such arc and on the right between consecutive such arcs, then using ordinary labelled composition for matching endpoints. Conversely any word producing an element of $J$ either lies in $B$ or produces a path of this form by the multiplier rules. If the graph is connected and contains any such arc, one can insert a detour of label $1$ through that arc and its reverse at any vertex. Thus all elements are generated precisely when the graph is connected, the closed-walk labels at a base vertex generate $G$, and either $B$ or the selected generator set is nonempty.

Let $c$ be the number of base components and define the $H_i$ and $r$ by their closed-walk labels as before. The same spanning-tree normalization and free choice of weights now give the exact inverse-generation count

$$
\max\{c-1+r,\ \boldsymbol 1_{B=\varnothing}\}.
$$

The $c-1$ joining arcs already make the underlying graph connected, and each additional arc gives one arbitrary normalized group label. If $c-1+r=0$ and $B$ is empty, a single arc with identity label supplies the required element of $J$. The group algorithm therefore gives the asserted polynomial-time inverse-generation algorithm under the same chief-factor promise.

The unrestricted inverse-generation decision problem on Cayley tables is polynomial-time Turing equivalent to (1) **with $r=0$ allowed**. The formula just given proves the forward reduction. In the weighted partial-bijection construction of §7 with $c\ge2$, the single-arrow class now contributes $c-1+r_0$ and each external group contributes $\max(1,d(H_i))$, since for elements of a finite group taking inverses preserves the set of elements obtainable by nonempty words. So one inverse-generation threshold query decides (1) even at $r=0$. The runtime is measured in the full table length. [Fleischer–Stober–Thumm–Weiß, *Membership and Conjugacy in Inverse Semigroups*, Sections 2 and 8](https://doi.org/10.4230/LIPIcs.ICALP.2025.156).

The unrestricted quasipolynomial bound and the bounded-chief-factor polynomial bound give upper bounds for Question 8.3. The NP-completeness question remains open. Gray's Theorem 7 gives the formula for a Rees-matrix semigroup in isolation and identifies the same conjugate-relative rank as the required group subroutine. Formula (3) generalizes that graph calculation to simultaneous multipliers and products from all higher classes. [Gray, *The minimal number of generators of a finite semigroup*](https://arxiv.org/html/1307.8280). [Eswaran–Tarjan, *Augmentation Problems*](https://doi.org/10.1137/0205044).

**Status.** Informal proof. The closest papers located establish the isolated Rees-matrix formula and the original Cayley-table group algorithm. The 2025 paper by Fleischer, Stober, Thumm, and Weiß records the arbitrary semigroup complexity as open and analyzes the inverse-generation problem in the succinct partial-bijection model. [Membership and Conjugacy in Inverse Semigroups, Section 8](https://doi.org/10.4230/LIPIcs.ICALP.2025.156).
