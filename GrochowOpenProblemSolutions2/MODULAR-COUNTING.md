# Modular counting separates Fitting-free groups from an abelian family

**Theorem.** First-order logic with unary counting modulo three has strictly greater distinguishing power than first-order logic on finite group tables. Each Fitting-free group of order $N$ is identified in this logic by a sentence using $O(\log\log(N+2))$ variables. There are infinitely many finite abelian groups of order $N$ for which any identifying sentence in this logic needs at least $\frac13\log_3 N$ variables. This answers Grochow–Johnson–Levet Problem 10.2. [Grochow–Johnson–Levet, Theorem 9.1 and Problem 10.2](https://arxiv.org/html/2504.19777#S10)

We use the group language with the ternary multiplication relation. The extension $\mathrm{FO}+\mathrm{MOD}_3$ adds a quantifier $Q_a x\,\varphi$ for each $a\in\{0,1,2\}$. The quantifier holds if the number of values of $x$ satisfying $\varphi$ is congruent to $a$ modulo three. Variable bounds count distinct variable symbols, and symbols can be reused. To identify a finite group means to define its isomorphism class among finite groups.

## Matched direct summands for bounded variables

For a prime $p$, write $R_1=\mathbb F_p$, $R_2=\mathbb Z/p^2\mathbb Z$, and
$$
A_p(r,s)=R_1^r\oplus R_2^s
$$
as an additive group. Fix $k\ge1$ and two such groups, with both ranks at least $k$ in each group. A pair of assignments to $j\le k$ distinct variable symbols will be called matched if there are free direct summands $S_1,S_2$ of the first group's two displayed components and $T_1,T_2$ of the second group's components, of rank at most $j$ each, such that the assigned elements lie in $S_1\oplus S_2$ and $T_1\oplus T_2$, respectively. The match also requires $R_i$-linear isomorphisms $S_i\to T_i$ whose sum takes each assigned value to its partner.

The empty assignment is matched. Restricting to fewer symbols preserves the match. Indeed, after retaining $j'$ symbols, their $i$-th components in $S_i$ lie in a free direct summand of $S_i$ of rank at most $j'$. For $R_1$, extend a basis of the span. For $R_2$, take Smith normal form of the matrix whose columns are the retained components. Over $\mathbb Z/p^2\mathbb Z$, pivot first on units and then on nonzero multiples of $p$. Row and column operations place all nonzero entries on at most $j'$ diagonal positions. The inverse row operation carries the span of those coordinate positions to a free direct summand containing the given components. Its image under $S_i\to T_i$ is the required summand for the other group.

To extend a match with a fresh value for one symbol, start with at most $k-1$ assigned symbols. Pick free complements of the four summands in their respective components. Every complement has rank at least one. In the first group, partition the possible new values according to their exact $S_1\oplus S_2$ component and the type of their two complement components. For $R_1$, the types are zero and nonzero. For $R_2$, the types are zero, nonzero in $pR_2^d$, and primitive, where $d$ denotes the rank of the complement. Partition the second group in the same way, using the corresponding $T_1\oplus T_2$ values.

Every class is nonempty. Its complement types are transitive under the automorphism groups of the free complements. A nonzero vector over $R_1$ and a primitive vector over $R_2$ can be taken to a basis vector. A nonzero vector in $pR_2^d$ can be taken to $p$ times a basis vector by applying a change of basis to a primitive lift. All these automorphisms extend to group automorphisms fixing the previous assignment. For each pair of corresponding classes, choose representatives with each complement component supported on one basis vector. Extend the prescribed isomorphism of summands by pairing these basis vectors. The resulting assignments are matched and the new ranks are at most the new number of assigned symbols.

## Formula equivalence with modular quantifiers

For $p=3$, corresponding classes also have cardinalities congruent modulo three. A complement of rank $d\ge1$ over $R_1$ has type sizes $1$ and $3^d-1$. Over $R_2$ it has type sizes $1$, $3^d-1$, and $3^{2d}-3^d$. Modulo three these are $1,-1$ and $1,-1,0$, respectively, regardless of $d$. The size of each assignment class is the product of the two relevant type sizes.

We now prove by induction on formulas that a matched assignment gives the same truth value in both groups to every formula with at most $k$ variable symbols in $\mathrm{FO}+\mathrm{MOD}_3$. A match preserves all atomic formulas because it is an isomorphism on the summands containing the assigned values. Boolean operations preserve agreement. For a bound variable $x$, drop its previous value if any and restrict the matched summands. Partition the new values as above. The formula inside the quantifier is constant on each class by automorphism invariance. It gives the same truth value on corresponding classes by induction applied to the matched representatives. Each pair of classes is nonempty, which handles existential quantification. The paired classes have cardinalities equal modulo three, so summing over true classes handles $Q_a$ quantification. This also proves the first-order-only assertion for every prime $p$, since in that case only nonemptiness is needed.

In particular, the nonisomorphic groups
$$
G_m=A_3(m+2,m),\qquad H_m=A_3(m,m+1),\qquad m\ge1,
$$
agree on all $\mathrm{FO}+\mathrm{MOD}_3$ sentences with at most $m$ variables. Their orders are both $N=3^{3m+2}$, while their images under multiplication by three have sizes $3^m$ and $3^{m+1}$. Thus a sentence identifying $G_m$ uses at least $m+1=(\log_3 N+1)/3$ variable symbols.

## Strictness and the Fitting-free upper bound

For the strictness assertion, use
$$
G'_m=A_2(m+2,m),\qquad H'_m=A_2(m,m+1).
$$
They have equal orders and agree on first-order sentences with at most $m$ variables by the first-order part of the argument. The numbers of elements satisfying $2x=0$ are $2^{2m+2}$ and $2^{2m+1}$, respectively. These are 1 and 2 modulo three. The single sentence saying that the number of such elements is 1 modulo three distinguishes all these pairs. The identity is first-order definable in the relational language, so this is a sentence with a fixed finite number of variable symbols. It has no first-order equivalent on finite groups, since any proposed equivalent uses some fixed number of symbols and fails on a pair with sufficiently large $m$.

Theorem 9.1 of Grochow, Johnson and Levet already identifies every Fitting-free group using a first-order sentence with $O(\log\log(N+2))$ variables. The same sentence works in the extension. To compare fixed-variable distinguishing power with full counting, fix an order $N$. Any modular quantifier on groups of that order can be expanded as the disjunction of the exact counting quantifiers for the counts in $[0,N]$ with the required residue. This expansion uses the same variable symbols. Full counting distinguishes $G_m$ and $H_m$ with a fixed number of variables by counting solutions of $3x=0$, so the modular extension is strictly weaker in this fixed-order, bounded-variable sense. [Grochow–Johnson–Levet, Theorem 9.1](https://arxiv.org/html/2504.19777#S9)

The argument is a written proof.
