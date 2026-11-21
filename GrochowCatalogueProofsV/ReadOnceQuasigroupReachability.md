# Read-once parenthesized products in finite commutative quasigroups

## GP-0527

Given the table of a finite quasigroup, a list of named occurrences, and a target, deciding whether an arbitrarily ordered fully parenthesized product uses each occurrence exactly once and equals the target is NP-complete. Hardness holds for commutative quasigroups. The corresponding witness search is NP-hard and lies in $\mathsf{FP}^{\mathsf{NP}}$. The reduction outputs the entire multiplication table in polynomial time.

For NP membership, guess a permutation of the occurrence indices and a binary tree whose leaves use that order. Evaluate each internal vertex by one table lookup. Polynomial-time decision-to-search follows by the usual prefix fixing of the witness bits under an NP oracle.

For hardness use the strongly NP-complete 3-PARTITION problem. Its input is $3m$ positive integers $a_i$ with total $mB$ and $B/4<a_i<B/2$, and the question asks for a partition into $m$ triples each of sum $B$. Strong NP-completeness permits $B$ to be bounded by a polynomial in the instance length. [Garey–Johnson, Chapter 4](https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf)

Use the additive group $A=\mathbb Z/(3m+1)\mathbb Z\times\mathbb Z/(mB+1)\mathbb Z$. For two elements $u,v\in A$, inspect their canonical representatives as pairs of integers. Define a symmetric function $c(u,v)\in\{0,1\}$ to be zero precisely in the following cases.

- Both first coordinates are one.
- The first coordinates are one and two in either order, and the sum of their second coordinates is $B$.
- Both first coordinates are positive multiples of three.

On $Q=A\times\mathbb Z/(3m+1)\mathbb Z$ put
$$
(u,z)*(v,w)=(u+v,z+w+c(u,v)).
$$
This is a commutative quasigroup. With one input and the output fixed, the other base coordinate is uniquely obtained by subtraction in $A$, then the other last coordinate is uniquely obtained by subtracting the now known correction. Its order is $(3m+1)^2(mB+1)$ and its table can therefore be generated in polynomial time in the promised 3-PARTITION instance size.

Supply leaves $((1,a_i),0)$, one per occurrence, and the target $((3m,mB),0)$. Every subtree's base coordinates are its true count and weight because the entire count and weight are below the respective moduli. The last coordinate at the root is the number of joins with $c=1$, also below its modulus because there are only $3m-1$ joins. Therefore the target can be reached precisely when all joins are legal.

A legal subtree of count two must combine two singletons. The only legal construction of a subtree of count three combines such a pair with a singleton of complementary weight. All other legal subtrees whose counts are positive multiples of three combine two subtrees of completed multiples of three. Induction from the root gives disjoint triples of sum $B$ covering the occurrence list. In the other direction any 3-partition supplies a tree evaluating each triple first and then combining the completed triples. Repeated item sizes are allowed because the leaves use named occurrences.

For contrast with ordinary membership, the requirement that each occurrence is consumed can carry an NP-complete partition choice even though multiplication and both division operations are efficient. [Ordinary quasigroup reachability context](https://arxiv.org/html/2402.00133#S7)
