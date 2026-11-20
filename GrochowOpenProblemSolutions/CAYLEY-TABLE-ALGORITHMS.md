# Shallow simplicity recognition and epimorphisms onto Fitting-free groups

These are written proofs for two Cayley-table problems. The inputs are explicit multiplication tables of finite groups, with the order parameter denoted by $n$. A simple group is nontrivial and has no nontrivial proper normal subgroup. A Fitting-free group is one whose solvable radical is trivial.

## GP030. Simplicity, minimal normal subgroups, and the socle in FOLL

**Theorem.** Simplicity of a Cayley-table group is in uniform FOLL. Uniform FOLL circuits also output the list of all its minimal normal subgroups as membership masks, output its socle as a membership mask, and recognize groups with trivial solvable radical.

Collins–Levet ask the simplicity question in their Question 8.2. The crucial quantitative ingredient is the Liebeck–Shalev bound on products of normal subsets of finite nonabelian simple groups. We use the bound inside each simple factor of a minimal normal subgroup. [Collins–Levet, Question 8.2](https://arxiv.org/html/2212.11247#S8) · [Liebeck–Shalev, Theorem 1.1](https://annals.math.princeton.edu/articles/11021)

### Bounded generation inside minimal normal subgroups

For $x\in G$, define
$$
D_x=\{g x^j g^{-1}: g\in G,\ 0\le j<n\}.
$$
The set is invariant under all conjugations, is inverse-closed, and contains $1$. Its generated subgroup is the normal closure of $x$.

There is an absolute constant $b$ such that for every minimal normal subgroup $M$ of $G$ and every $1\ne x\in M$,
$$
D_x^{\,\lceil b\log_2 n\rceil}=M.
$$
To prove this, recall that a minimal normal subgroup is characteristically simple. If it is abelian then it is elementary abelian, say of order $p^d$. The conjugates of $x$ span $M$ because their span is nonzero and normal in $G$. Choose $d$ of these conjugates as a basis. Each of their powers is in $D_x$, so any element of $M$ is a product of at most $d\le\log_2 n$ elements of $D_x$.

Otherwise $M=T_1\times\cdots\times T_s$ for isomorphic nonabelian simple groups $T_i$, permuted transitively by conjugation by $G$. For every $i$, a conjugate $y$ of $x$ has nonidentity $i$-th projection. That projection fails to commute with some $h\in T_i$, since $T_i$ is centerless. Then $y^{-1}h^{-1}yh$ is nonidentity, lies in $T_i$, and is a product of two elements of $D_x$. Its entire $T_i$-conjugacy class is in $D_x^2$. Liebeck–Shalev show that for a nontrivial normal subset $D$ of a finite nonabelian simple group $T$, powers of length at most a constant times $\log |T|/\log |D|$ cover $T$, with identity padding when $1\in D$. Apply this to $D=\{1\}$ union the conjugacy class of the displayed commutator. Thus every element of $T_i$ is a product of at most $b_0\log_2|T_i|$ elements of $D_x$, with an absolute $b_0$. Products over all factors require at most $b_0\log_2|M|$ factors from $D_x$. Identity padding gives the stated bound.

### Circuits

Decode the table to the relation $T(a,b,c)=[ab=c]$, using one constant-depth equality to the binary label $c$ per triple of elements. Identity, inversion, and conjugation are constant-depth relational operations. The direct connection uniformity can be taken in the standard relational table encoding. Binary entries are converted to that encoding by the same uniform equality layer.

All predicates $[x^j=z]$ with $0\le j<n$ can be computed in FOLL. This is the power predicate of Barrington–Kadau–Lange–McKenzie, Proposition 3.1. One construction starts with powers up to 2 and increases the exponent cap $a$ to $a^2$ per stage. For $j=ab'+c$ with $0\le c<a$ and $0\le b'\le a$, read $x^a$, its $b'$-th power, and $x^c$ from the previous table. Computing those three values as relations and joining them with the multiplication table has constant depth per stage. The caps $2,4,16,\ldots$ are powers of two, so the quotient and remainder of $j$ by a cap are taken by splitting its bit string. Clip exponent indices at $n$ and stop upon passing the required range. The construction uses a polynomial number of gates and $O(\log\log(n+2))$ stages. [Barrington–Kadau–Lange–McKenzie, Proposition 3.1](https://www.sciencedirect.com/science/article/pii/S0022000001917647)

Compute the masks of $D_x$ for all $x$ by taking all conjugates of these powers. Set $P_0(x,z)=[z\in D_x]$. Use unbounded-fan-in gates for the update
$$
P_{i+1}(x,z)=\bigvee_{u,v\in G}
\bigl(P_i(x,u)\wedge P_i(x,v)\wedge T(u,v,z)\bigr).
$$
By induction, $P_i(x,z)$ tests $z\in D_x^{2^i}$. Use
$$
r=\left\lceil\log_2\bigl(b\lceil\log_2(n+2)\rceil\bigr)\right\rceil
$$
stages and let $B_x=D_x^{2^r}$. Each layer has $O(n^4)$ gates including fan-in terms, and the layers are uniformly indexed by the stage and element tuples. The total depth is $O(\log\log(n+2))$. The argument uses one absolute integer at least the Liebeck–Shalev constant and does not need a parameter chosen separately at each input size.

For simplicity, accept precisely when $n>1$ and $B_x=G$ for every $x\ne1$. Correctness on a simple group follows from the minimal-normal-subgroup bound with $M=G$. Conversely a nontrivial proper normal subgroup contains some $x\ne1$, and then contains $B_x$, so the circuit rejects. Associativity, closure, and the identity and inverse axioms can also be checked in uniform constant depth if invalid tables are required to reject.

For minimal normal subgroups, output the masks $B_x$ for those $x\ne1$ satisfying both of the following constant-depth predicates. First, $B_x$ is closed under multiplication. Second, $B_y=B_x$ for every $1\ne y\in B_x$. Each $B_x$ already contains $1$ and is inverse-closed and normal as a subset, so the first predicate makes it a normal subgroup. If $B_x$ is minimal normal then the quantitative bound proves the second predicate. Conversely, a nontrivial smaller normal subgroup $L\lneq B_x$ would contain some $1\ne y$, and then $B_y\subseteq L$, contrary to the second predicate. Every minimal normal subgroup occurs since it contains a nonidentity element $x$ with $B_x=M$. If a list without repetitions is desired, select the least index of every equal-mask class in constant depth.

The socle is generated by the union of the selected subgroups and the identity. A product of normal subgroups is a subgroup. Starting with the trivial subgroup, if the current product is smaller than the socle, there is a selected subgroup which is not contained in that product. Multiplying by it increases the order by a factor of at least two. Hence the socle is a product of at most $\lfloor\log_2 n\rfloor$ selected normal subgroups. Repeated squaring on the union, with identity padding, computes its mask in $O(\log\log(n+2))$ further depth.

Finally, a nontrivial solvable radical contains a minimal nontrivial normal subgroup of $G$, which is abelian. Conversely an abelian minimal normal subgroup is a nontrivial solvable normal subgroup. Testing whether any selected subgroup is abelian therefore recognizes a nontrivial solvable radical, and complementation recognizes Fitting-free groups.

## GP049. Epimorphisms to a Fitting-free target

**Theorem.** Given Cayley tables for $G,H$ with $H$ Fitting-free, existence, construction, and exact counting of epimorphisms $G\twoheadrightarrow H$ are deterministic polynomial-time tasks. Existence is also in uniform $\mathsf{AC}^3$. One can enumerate all normal subgroups $K$ of $G$ for which $G/K$ is Fitting-free, without repeats. In fact
$$
\#\{K\lhd G:G/K\text{ Fitting-free}\}
\ \le\
|G/\operatorname{Rad}(G)|^{\log_{60}2}.
$$
Equality holds for a direct product of copies of $A_5$. This gives the Fitting-free answer to Grochow–Srivastava–Thakkar Open Question 3(1), and a counting result for the same family in Open Question 2. [Open Questions 2 and 3](https://arxiv.org/html/2609.07429v1#S7)

### Enumerating quotient kernels

Write $\operatorname{Rad}(X)$ for the solvable radical. If $X/K$ is Fitting-free then $K$ contains $\operatorname{Rad}(X)$, because its image would otherwise be solvable and normal in $X/K$. Reduce to $X/\operatorname{Rad}(X)$, keeping the pullback map for output. The radical is computable in polynomial time by ordinary Cayley-table operations. For example, compute all minimal normals by normal closures or by the preceding theorem. Generate the subgroup from the abelian ones, pass to its quotient, and repeat until there are none. This only takes logarithmically many proper quotient operations, and it gives the radical because each removed subgroup is solvable and every nontrivial solvable normal subgroup contains an abelian minimal normal subgroup.

After radical reduction, fix any chief series
$$
1=X_0\lhd X_1\lhd\cdots\lhd X_s=X
$$
of the reduced group $X$, so all the $X_i$ are normal in $X$ and each $X_i/X_{i-1}$ is a minimal nontrivial normal subgroup of $X/X_{i-1}$. One can construct the series from the table by taking the preimage of a minimal normal subgroup of each successive quotient. For every nonabelian chief factor, form its conjugation kernel
$$
C_i=\{g\in X:[g,x]\in X_{i-1}\text{ for every }x\in X_i\}.
$$
The kernel $C_i$ is normal in $X$. The chief-section method extends the construction for direct products of nonabelian simple targets. [Earlier chief-section construction for direct-product targets](https://github.com/Dugongue/MathProofs/blob/6b091c10bce8f1f3fca282e739f4bbb1790615b3/FourAlgebraicIsomorphismTransfers/Epimorphisms.md)

Suppose $\pi:X\twoheadrightarrow Y$ and $Y$ is Fitting-free. Write $Y_i=\pi(X_i)$. A nontrivial factor $Y_i/Y_{i-1}$ is equivariantly isomorphic to $X_i/X_{i-1}$, since the induced surjection has a proper $X$-invariant kernel in a chief factor. In particular it is a minimal normal subgroup of $Y/Y_{i-1}$. For each minimal nontrivial normal subgroup $M$ of $Y$, take the first $i$ with $M\le Y_i$. The intersection $M\cap Y_{i-1}$ is trivial by minimality of $M$. The image of $M$ in $Y_i/Y_{i-1}$ is nontrivial and normal in $Y/Y_{i-1}$, so it is the whole chief factor. This gives an equivariant isomorphism $M\cong X_i/X_{i-1}$. The factor is nonabelian because $Y$ is Fitting-free, and equivariance gives $C_i=\pi^{-1}(C_Y(M))$.

The centralizer of $\operatorname{Soc}(Y)$ in $Y$ is trivial. Otherwise this centralizer would be a nontrivial normal subgroup, containing some minimal normal subgroup of $Y$. That subgroup would be in the socle and centralize itself, so it would be abelian, contrary to $Y$ being Fitting-free. Thus intersecting the $C_i$ selected by the minimal normal subgroups of $Y$ gives exactly $\ker\pi$. This includes $Y=1$, with the empty intersection equal to $X$.

The algorithm enumerates the intersections of subsets of the $C_i$, retaining distinct kernels with Fitting-free quotient. Every nonabelian chief factor has order at least 60, so there are at most $\log_{60}|X|$ such factors and at most $|X|^{\log_{60}2}$ candidates. All table operations, equality tests, and filtering take polynomial time. When $G=A_5^k$, every product of a subset of the factors is a distinct kernel with Fitting-free quotient. There are $2^k$ such products, attaining the bound.

### Parallel decision

For decision, a chief series of $G$ itself suffices. Represent elements of a quotient by the least table label in each coset, with a bit mask marking the active labels. The test that two labels have the same coset, the choice of each least representative, and the relational quotient table have constant-depth formulas. The minimal-normal circuits above work on an active domain by guarding the element quantifiers and using $n$ as a bound on the quotient order and exponents. Given the current $X_i$, choose the first minimal normal mask in $G/X_i$ and pull it back. When no such mask exists, the series has reached $G$. This takes at most $\lceil\log_2 n\rceil$ rounds of depth $O(\log\log(n+2))$.

For each nonabelian chief factor, membership in $C_i$ is a constant-depth test from the series masks. Use every subset of the at most $\lceil\log_2 n\rceil$ positions in parallel, ignoring positions with a trivial or abelian factor. There are at most $2n$ such subsets. Intersect the selected masks, and compute each candidate quotient on its coset representatives. To reindex the quotient to consecutive labels, count for each representative the number of earlier active labels. A balanced tree of binary additions computes all such counts in parallel in $O(\log n\log\log(n+2))$ depth. The branch is eligible when the number of representatives equals $|H|$. Compare eligible quotients with $H$ by the uniform $\mathsf{AC}^3$ algorithm for Cayley-table isomorphism of Fitting-free groups, which also checks the Fitting-free promise, and OR the answers. All the preceding operations have polynomial size and uniform depth $O(\log n\log\log(n+2))$; thus the decision depth is $O(\log^3(n+2))$. [Grochow–Johnson–Levet, Theorem 1.1](https://arxiv.org/html/2504.19777)

### Independent kernel enumeration by socle recursion

Now let $X$ be Fitting-free. If $X=1$, output the single kernel $1$. Otherwise, let
$$
S=\operatorname{Soc}(X)=T_1\times\cdots\times T_k
$$
be the decomposition of its socle into nonabelian simple factors. Compute the socle and then find the minimal normal subgroups of $S$ considered as a group in its own right. These are exactly the $T_i$. Elements of $X$ under conjugation permute the factors, so their invariant subsets can be found by scanning the table. Distinguish minimal normal subgroups of $X$ from individual simple factors of $S$, since one minimal normal subgroup of $X$ can be a product of several $T_i$. [Babai–Codenotti–Qiao, §5.1](https://people.cs.uchicago.edu/~laci/papers/icalp12.pdf)

For each invariant subset $J\subseteq\{1,\ldots,k\}$, define
$$
A=\prod_{i\in J} T_i,\qquad M=\prod_{i\notin J} T_i,\qquad C=C_X(A).
$$
The groups $A,M,C$ are normal in $X$, $M\le C$, and
$$
C\cap S=M,\qquad |C/M|\le |X/S|.
$$
The first identity uses that each $T_i$ has trivial center. The second follows from the injective map $C/(C\cap S)\to X/S$.

Recurse on $C/M$, enumerate its kernels with Fitting-free quotient, and pull those kernels back to subgroups $K\le C$. Output the candidates that are normal in $X$ and have Fitting-free quotient in $X$. These final checks use only Cayley-table computations.

To show completeness, suppose $X/K$ is Fitting-free. A normal subgroup of a direct product of nonabelian simple groups is a product of some of the factors. In fact, if an element of the normal subgroup has nontrivial projection on $T_i$, its commutator with a suitable factor element gives a nontrivial element of its intersection with $T_i$, forcing the entire factor into the subgroup. Thus $K\cap S$ is the group $M$ from exactly one invariant $J$. Since $K$ and $A$ are normal in $X$ and have trivial intersection, they centralize each other. Hence $K\le C_X(A)$. In $X/K$, the subgroup $C/K$ is normal and therefore Fitting-free. Indeed, its solvable radical is characteristic in $C/K$, and so would be solvable and normal in $X/K$. Thus $K/M$ occurs in the recursive output. The final checks retain it. Conversely every output passes the two final properties. Within one branch the pullback is injective. Distinct branches cannot return the same kernel since $M\le K\le C$ forces $K\cap S=M$.

### Socle recursion complexity

Let $\eta=\log_{60}2$. Each simple factor has order at least 60. An internal node of order $m$ after radical reduction has at most $2^k\le |S|^\eta$ children. Every child, after its own radical reduction, has order at most $m/|S|$. The sum of the $\eta$-powers of the child orders is therefore at most $m^\eta$. The depth is logarithmic, since every nontrivial recursive step shrinks the order by at least 60. At each depth there are at most $|G/\operatorname{Rad}(G)|^\eta$ nodes. Each node performs polynomial table work, including lifting and testing all candidates from its children. This gives polynomial total time. Equivalently the number of leaves is at most $|G/\operatorname{Rad}(G)|^\eta$, and each output corresponds to one leaf. For $G=A_5^k$ every product of a subset of the factors is a kernel with Fitting-free quotient. These are all the normal subgroups in that case, so the exponent is sharp.

### Decision, witness, and exact count

For each enumerated $K$ with $|G/K|=|H|$, compare $G/K$ with $H$ by the Babai–Codenotti–Qiao polynomial-time Cayley-table isomorphism algorithm for Fitting-free groups. Every epimorphism factors uniquely as the quotient map followed by an isomorphism, so the number of epimorphisms is
$$
|\operatorname{Aut}(H)|\cdot
\#\{K\lhd G:G/K\cong H\}.
$$
To find a witness, take a matching kernel and one isomorphism from its quotient to the target. For the automorphism count, the cited algorithm fixes one source diagonal and computes the isomorphism cosets respecting each possible target diagonal in §§5.1–5.3. There are polynomially many target diagonals. Distinct target diagonals give disjoint cosets because the source diagonal is fixed. Count each coset using the order of its permutation group, computed in polynomial time from generators, and sum. Taking the source and target both equal to $H$ produces the factor $|\operatorname{Aut}(H)|$. The same diagonal-coset algorithm supplies an isomorphism witness from any nonempty coset. This uses the established result for the named group family. [Babai–Codenotti–Qiao, Theorem 1 and §§5.1–5.3](https://people.cs.uchicago.edu/~laci/papers/icalp12.pdf)

The proofs are written mathematics. The uniform circuit construction uses the finite-simple-group diameter theorem, and epimorphism testing uses Fitting-free isomorphism. The companion Python replay checks both kernel enumerators against independent normal-subgroup and derived-series enumeration on ten Cayley tables of orders 1 through 240. It also checks the bounded masks for simplicity, minimal normals, and the socle.
