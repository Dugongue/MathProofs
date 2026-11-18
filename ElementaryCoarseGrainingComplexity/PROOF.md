# A singly exponential algorithm for elementary cellular-automaton coarse-graining

**Theorem.** Given two elementary cellular automata $A,B$ and a positive supercell size $N$, one can construct a nonconstant exact coarse-graining from $A$ to $B$, or report that none exists, in deterministic $2^{O(N)}$ bit time. More generally, if a finite algebra with one operation $F$ is supplied by its complete table, there is a deterministic polynomial-time algorithm to find a nonconstant homomorphism to any two-element algebra with an operation $G$ of the same arity. This permits an arbitrary finite source alphabet for a binary target automaton. For ternary operations on a source of size $m$, the abstract algorithm can be implemented in $O(m^6\operatorname{polylog}(m+2))$ bit operations using table lookups and linear-time forward chaining.

Song and Grochow ask whether their fixed-supercell problem is NEXP-complete and give a nondeterministic exponential-time upper bound. For the elementary model explicitly used in the paper, the theorem gives deterministic single-exponential time in numeric $N$. It puts the task in $\mathsf{EXP}$ when $N$ is charged in the input length, for example encoded in unary. Thus NEXP-completeness for this model under polynomial-time reductions would imply $\mathsf{EXP}=\mathsf{NEXP}$. This argument allows every positive $N$ and every elementary source and target. Allowing arbitrary multistate targets is a broader question. [Song–Grochow, An Improved Algorithm for Coarse-Graining Cellular Automata, §§I.A and II](https://arxiv.org/abs/2012.12153).

## 1. The complete block table

For elementary rules, put $U=\{0,1\}^N$. Run the fine rule for $N$ steps on a concatenated triple of blocks, and take the middle output block. Its value is determined by precisely the supplied input window, because the radius-one light cone after $N$ steps can extend at most $N$ cells in either direction. The result is a ternary operation $F$ on $U$. The table has $2^{3N}$ entries and can be computed in $O(N^2 2^{3N})$ elementary updates by shrinking the known window by one cell at each end after each step. Let $G$ be the elementary local operation of the coarse rule $B$. By the paper's Equation (1), a valid map $h$ has exactly the following properties:
$$
 h:F \longrightarrow G,\qquad h(F(x,y,z))=G(h(x),h(y),h(z))\quad(x,y,z\in U),
$$
where the first notation means a homomorphism between the two operation tables and the underlying map is $h:U\to\{0,1\}$. The map must take both values. The rest of the proof works directly on the two finite operation tables.

## 2. Affine target rules

For a target of arity $k$, first determine whether $G$ is affine over $\mathbf F_2$, using its unique multilinear polynomial or its truth table. If
$$
 G(a_1,\ldots,a_k)=\gamma_0+\sum_{i=1}^k\gamma_i a_i,
$$
use one $0/1$ unknown $Y_u$ per source element $u$. Each homomorphism identity is a linear equation
$$
Y_{F(u_1,\ldots,u_k)}=\gamma_0+\sum_{i=1}^k\gamma_iY_{u_i}.
$$
Gaussian elimination finds the affine solution space. If it is empty or contains only constant maps, reject. Otherwise return a nonconstant solution. For instance, a particular solution and its translates by individual vectors of a homogeneous basis suffice: if all these vectors are constant maps, so is every point in the affine solution space. This includes constant, projection, negated-projection, and parity targets.

## 3. A binary term for nonlinear target rules

Suppose $G$ is nonlinear. Choose two variables of a nonzero nonlinear monomial in the multilinear polynomial of $G$. The mixed finite difference in those variables, viewed as a polynomial in the other variables, is nonzero: distinct monomials containing the chosen pair yield distinct monomials after removing the pair. Consequently some $0/1$ assignment to the other variables leaves a binary restriction $g$ with a nonzero coefficient on $xy$.

A nonlinear binary Boolean function has an odd number of ones in its truth table, so it has exactly one exceptional input, with its other three outputs equal. If its support is exactly $(1,1)$, it is AND. If its zero set is exactly $(0,0)$, it is OR. In every other case some one-variable restriction is NOT: choose an axis through the exceptional input on which the exceptional output is at the endpoint 0 if that output is 1, or at the endpoint 1 if that output is 0. Otherwise both axes would place the exceptional input in exactly the AND or OR case just described. With NOT and constants available, input flips put its exceptional input at $(1,1)$, and a possible output flip makes the resulting operation AND. Thus a term in $G$ and the two named constants computes AND or OR. For a fixed ternary $G$, the term can be taken from a fixed finite repertoire. For a displayed higher-arity table, the same construction gives a term with a constant number of calls to $G$, and finding the binary restriction takes time polynomial in the displayed table size.

Any nonconstant homomorphism $h$ sends some ordered pair of distinct source elements $(u_0,u_1)$ to $0,1$. Enumerate all such pairs. For one pair, interpret the term just found in the source algebra, with $u_0,u_1$ substituted for the constants. This gives a concrete binary operation $t$ on $U$, which need not be associative or commutative. Every homomorphism having these pinned values sends $t$ to AND or OR, as appropriate. If the term gives OR, work with complemented output bits in the next step, so the required preservation of $t$ is always the AND identity. The candidate map is uncomplemented before testing the original equations.

## 4. Recover a nonempty true fiber from one generator

The AND identity for a proposed true fiber $S\subseteq U$ is equivalent to closing $S$ under the following Horn rules, for every $x,y\in U$:
$$
 \{x,y\}\longrightarrow t(x,y),\qquad
 \{t(x,y)\}\longrightarrow x,\qquad
 \{t(x,y)\}\longrightarrow y.
$$
Closure under the first rule gives the forward implication of $h(t(x,y))=h(x)\land h(y)$, and closure under the other two gives its reverse.

Every nonempty set $S$ closed under these rules is the least closed set generated by **one** of its elements. In fact choose any list $s_1,\ldots,s_\ell$ of its elements, and form $c$ by nesting $t$ on that list, or taking $c=s_1$ if the list has only one element. Forward closure keeps every intermediate value, including $c$, in $S$. From $c$, the backward rules recover the two subvalues used in its last binary combination, and recursion recovers all the leaves $s_1,\ldots,s_\ell$. Thus the closure of $c$ contains $S$, and the reverse containment follows from closedness. The proof uses the actual nesting and does not require a semilattice law on the source.

This gives a complete search. For each pair of pins, and each $c\in U$, compute the least Horn closure of $\{c\}$. Interpret the closure as the 1-fiber in AND mode and as the 0-fiber in OR mode. Check that the resulting map has the pinned values and satisfies every original operation-table equation. Return a verified map if found. If there is a true map, its pins are tried, and the argument above supplies a seed whose closure produces exactly its relevant fiber. Conversely every returned map is a nonconstant homomorphism by the final check. No search over all partitions or all truth assignments is required.

For each pair of pins, the term table and rule list have $O(m^2)$ entries, where $m=|U|$. The least closure of one seed uses $O(m^2)$ rule-incidence operations with an agenda and counters for the unfilled premises. Each derived value is enqueued only once, and each premise occurrence is processed at most once. Verifying one candidate takes $O(m^k)$ table lookups. Thus all $O(m^3)$ pin and seed choices use $O(m^3(m^2+m^k)\operatorname{polylog}(m+2))$ bit time for fixed arity $k$. If the arity is part of an explicitly tabulated input, the same loops are polynomial in the combined table lengths. The affine case also takes polynomial table time. For elementary automata put $m=2^N$ and $k=3$, and add the table construction in §1. This proves the stated $2^{O(N)}$ bound and gives a witness whenever one exists.

## 5. Exact counts within the same time bound

In the affine case, if the system is consistent with homogeneous nullity $d$, it has $2^d$ solutions. Subtract whichever of the two constant maps pass the original homomorphism check. In the nonlinear case, the algorithm produces every nonconstant map among at most $m^3$ pin-and-seed candidates. Store the verified maps as bit strings, sort and remove duplicates. This gives the exact number of nonconstant coarse-grainings in the same $2^{O(N)}$ bit time. The integer has at most $2^N+1$ bits. This count does not require writing the complete affine solution list.

## 6. Polynomial space in the numeric block size

The decision problem also uses only $\operatorname{poly}(N)$ deterministic space. In particular it belongs to $\mathsf{PSPACE}$ for unary input $N$. Here we do not store the block table or the entire set of map values. The algorithm can recompute an individual block-table value from its three inputs in $\operatorname{poly}(N)$ space.

### Nonlinear rules

Fix the pins and the derived binary term table $t$, interpreted on demand. Let $\sim$ be the congruence of the binary algebra $(U,t)$ generated by all pairs from the commutative, associative and idempotent laws. Every map preserving $t$ into AND factors through this congruence. The quotient is a finite meet-semilattice. Every nonempty 1-fiber of a homomorphism to AND is upward closed and meet closed, hence is the upset of the meet of all its members. Conversely each such upset defines an AND homomorphism. Thus for each $\xi\in U$ it suffices to test the function $u\mapsto\mathbf 1[t(\xi,u)\sim \xi]$, interpreting this as the 0-fiber in OR mode. The same preliminary and final checks apply.

For a pair $(a,b)$, an elementary translation means applying $t(-,c)$ or $t(c,-)$ to both entries, with the same $c\in U$. Take the undirected graph on $U$ with edges the pairs obtainable by a sequence of elementary translations from any instantiated identity pair. Its connectivity relation is $\sim$. Each edge belongs to every congruence containing the identity pairs. Conversely connectedness is stable under elementary translations, because applying one to a path gives another path, and stability in both arguments gives congruence compatibility with $t$. Every identity pair is present by a translation sequence of length zero.

To compute one adjacency bit in this graph, enumerate the instantiated identity pairs and use directed reachability in the implicit graph on $U^2$ of elementary translations. Savitch's algorithm, with vertex names of length $O(N)$, uses polynomial space and evaluates one translation on demand. A second application of the same reachability algorithm computes connectedness of the outer graph. Enumerating pins, candidates, and original rule triples and calling these procedures uses polynomial space because their workspaces are reused.

### Affine rules

An affine rule whose output uses at most one coordinate imposes only constant assignments or pairwise parity equations on the block values. Add the chosen pins for 0 and 1. Interpret each equation as a parity-labeled edge between its two unknowns, using a new vertex for the constant zero when needed. The constraints are consistent exactly when no closed walk has odd total parity. This is ordinary reachability between the two copies of a vertex in the graph on pairs (variable, accumulated parity), with each edge toggling the parity by its label. The graph is implicit and Savitch's algorithm uses $O(N^2)$ space.

If at least two coefficients of the affine rule are nonzero, the rule with constants defines XOR as a binary term. Pin all but two active inputs to zero to obtain $x+y+\delta$ over $\mathbb F_2$. If $\delta=1$, also pin all but one active input to zero to obtain NOT, then apply it to this binary term. Try every ordered pair of distinct block states $u_0,u_1$ as the preimages of 0 and 1. Interpret the XOR term as a binary operation $t$ on the source with these pins. Use the same implicit congruence construction as in the nonlinear case, now with identity pairs from commutativity, associativity, $t(x,u_0)=x$, and $t(x,x)=u_0$. The quotient is an abelian group of exponent dividing two, hence a vector space over $\mathbb F_2$. Write $[x]$ for the class of $x$.

Every homomorphism satisfying the pins induces a linear functional on this quotient. Conversely a linear functional there gives a desired map exactly when it sends $[u_1]$ to $1$ and annihilates every defect
$$
[F(x,y,z)]+\gamma_1[x]+\gamma_2[y]+\gamma_3[z]+\gamma_0[u_1],
$$
where $\gamma_i$ are the coefficients of the affine target rule. Such a functional exists exactly when $[u_1]$ is outside the linear span of the defects. They are represented on demand by nesting $t$. To test span membership, use reachability from $u_0$ to $u_1$ on source block names, with an edge from $a$ to $b$ whenever $t(a,d)\sim b$ for some defect representative $d$. Every walk corresponds to a sum of defects, and every such sum gives a walk. Each adjacency test enumerates triples and calls the earlier congruence test. Another nested Savitch traversal costs $O(N^2)$ space in total.

In all cases an implicit vertex name, a triple counter, and each block calculation use $O(N)$ bits. Each reachability recursion stores $O(N)$ names and counters of $O(N)$ bits, and only a constant number of such recursions is nested. The decision bound is therefore $\mathsf{DSPACE}(N^2)$ in addition to the separate $2^{O(N)}$-time algorithm.

## 7. A multistate extension

The single-seed argument also gives a deterministic exponential-time algorithm for **surjective** coarse-graining when the explicit target algebra has a binary term with named constants defining some meet-semilattice on its $b$ states. Enumerate preimages for the constants. For each target state $c$, the indicator of the principal upset of $c$ is a meet homomorphism into AND. Composing with the proposed map gives either an empty 1-fiber or one of the at most $m$ fibers enumerated by single-seed closure on the interpreted source term. Guess one such fiber for each $c$. The resulting membership vectors identify target elements uniquely, by antisymmetry. Recover the map on each state and check it against the original equations and the surjectivity condition. One can find the term by saturating the binary operation tables on the target, starting from the projections and constants and retaining the term as a circuit. There are at most $b^{b^2}$ tables. For ternary rules the bound is $2^{O(b^2\log(b+2))}(m+1)^{O(b)}$, polynomial overhead included. With $m=|S_A|^N$ this is exponential in a polynomial of the explicit input length when $N$ is unary. This covers semilattice-term targets of variable alphabet size.

## 8. Relation to earlier constraint algorithms

Barto, DeMeo and Mottet's general theorem for Boolean structures gives another route to the elementary upper bound. If the target operation is not essentially unary, their Theorem 1.3 gives a polynomial-time CSP algorithm even after adding unary relations $\{0\},\{1\}$. Try all ordered source pairs, requiring their images to lie in these two relations. The fixed finite set of elementary target templates makes these polynomial bounds uniform. Essentially unary Boolean operations are affine and the linear equations above apply directly. Their paper also develops semilattice homomorphism enumeration and efficient enforcement of identities in the input algebra. The EXP conclusion for elementary coarse-graining therefore follows from prior general machinery together with the block-table reduction. The proof here gives a self-contained specialized algorithm and the explicit closure from a single seed. No priority claim is made for the general Boolean algebra result. [Barto–DeMeo–Mottet, Constraint Satisfaction Problems over Finite Structures, Theorem 1.3 and §§3–4](https://arxiv.org/html/2010.04958).

An independently written [C++ check](verify_coarse.cpp) compares the linear and Horn algorithms against brute-force enumeration of nonconstant maps for all 65,536 ordered elementary rule pairs at each of $N=1,2,3$. All 196,608 cases agree. These arguments are informal.
