# Group epimorphism for abelian Sylow towers with bounded action ranks

Grochow, Srivastava, and Thakkar ask in Open Question 3(4) whether epimorphism testing for groups with abelian Sylow towers is in polynomial time under the Cayley table representation. The theorem below extends the previous MathProofs result to arbitrarily many non-elementary layers under an explicit bound on their action ranks. The full question remains open. An exact correspondence with binary subcode containment accounts for a family with unbounded action ranks. [Original question](https://arxiv.org/html/2609.07429v1#S7) · [Prior MathProofs theorem](https://github.com/Dugongue/MathProofs/blob/main/PortfolioIsomorphismCrossovers/GroupAlgorithms.md)

## 1. Statement

Write an abelian Sylow tower as a sequence of split extensions

$$
G^{(i)}=A_i\rtimes G^{(i+1)},\qquad
G^{(1)}=G,\qquad G^{(t+1)}=1,
$$

where \(A_i\) is a normal abelian Sylow \(p_i\)-subgroup of \(G^{(i)}\), and the complement is identified with a subgroup. The primes \(p_i\) are distinct. For \(i>j\) the subgroup \(A_i\) normalizes \(A_j\). Set

$$
E_i=\ker\left(A_i\longrightarrow\prod_{j<i}\operatorname{Aut}(A_j)\right).
$$

If \(A_i\) is elementary abelian, put \(r_i=0\). Otherwise let \(r_i\) be the minimum number of generators of \(A_i/E_i\). A trivial quotient has rank zero.

**Theorem.** Given the Cayley table of \(G\) and any target Cayley table \(H\), an algorithm tests and constructs epimorphisms from \(G\) to \(H\) in deterministic time

$$
(|G|+|H|)^{O(1)}\prod_i |A_i|^{r_i}.
$$

The bound holds for the best splitting tower of \(G\). In particular, if all non-elementary layers have bounded joint action rank, then the total time is polynomial. More generally it is polynomial whenever \(\sum_i r_i\log |A_i|=O(\log |G|)\). The group's table supplies all structural data. There is no bound on the individual Sylow exponents or on the number of layers.

## 2. A fixed marked module quotient

Let \(A\) be a finite abelian \(p\)-group acted on by a finite \(p'\)-group \(K\), and let \(A_0\) be a \(K\)-invariant subgroup. Set \(C=A/A_0\) with quotient map \(\rho\). Fix another finite abelian \(p\)-group \(B\) acted on by \(K\) and a \(K\)-equivariant epimorphism \(\psi:B\to C\).

**Lemma.** One can determine whether there is a \(K\)-equivariant epimorphism \(f:A\to B\) satisfying \(\psi f=\rho\), and construct one if it exists, in time polynomial in the explicit tables and actions.

Use the coprime homocyclic decomposition into direct summands \(A=\bigoplus_j S_j\) whose reductions \(S_j/pS_j\) are simple \(\mathbb F_pK\)-modules. Here and below this refers to the full integral \(K\)-action, up to the exponent of each summand. The prior proof constructs the decomposition by averaging projections over \(K\), then correcting idempotents through the nilpotent kernel of reduction. Its quotient enumeration result also gives a list of at most \(|A|\) concrete \(K\)-module representatives for all quotients of \(A\). These consist of truncating the homocyclic simple lifts. [Decomposition and quotient enumeration, §5](https://github.com/Dugongue/MathProofs/blob/main/PortfolioIsomorphismCrossovers/GroupAlgorithms.md) · [Endomorphism-ring reduction, Proposition 3.7](https://arxiv.org/html/2605.26748v1#S3.SS2)

Choose \(a_j\in S_j\) with nonzero residue modulo \(p\). Its \(K\)-orbit generates \(S_j\) as an additive group. Indeed, that orbit spans the simple residue, and if its additive span \(L\) satisfies \(L+pS_j=S_j\), iteration gives \(L+p^sS_j=S_j\) for all \(s\), hence \(L=S_j\). A \(K\)-equivariant homomorphism \(f_j:S_j\to B\) is determined by \(f_j(a_j)\). For each candidate value in \(B\), evaluate the table of the map by simultaneous traversal of the additive Cayley graph of the orbit generators and their proposed images. Reject a candidate if two paths to the same element assign different values, or if table verification of either the homomorphism, equivariance, or \(\psi f_j=\rho|_{S_j}\) fails. This lists all allowed maps for each summand in polynomial time. An empty list makes the fixed lift impossible.

The residue \(f_j\bmod p\) is either zero or a map from a simple module \(S_j/pS_j\) to the corresponding isotypic summand of \(B/pB\). Treat each listed map as an element of a ground set and impose two matroid constraints. The first is a partition matroid permitting at most one element from each list. For the second, identify the homomorphisms into each isotypic target with column vectors over the corresponding simple module's endomorphism field, after identifying isomorphic simple domains. Take the direct sum over the simple types of the resulting linear matroids. The latter test can be implemented without writing down the endomorphism fields. Within each nontrivial selection of one type of simple of dimension \(d\), compute the \(\mathbb F_p\)-dimension of the sum of the residue images and check whether it is \(d\) times the number of selected elements. A zero residue is a loop. The equivalence follows by the isotypic decomposition and the independence of columns over the endomorphism field.

Run the polynomial-time maximum-cardinality matroid intersection algorithm. A fixed lift exists exactly when the resulting cardinality equals the sum of the simple multiplicities of \(B/pB\). In one direction a surjective map has residue images spanning every isotypic summand, and bases can be selected from its chosen columns. In the other direction fill every unselected source list with an arbitrary allowed map and take the resulting direct-sum map. The residue images span \(B/pB\). The same iteration used for \(S_j\) shows that this implies surjectivity onto \(B\). Every summand satisfies the marked equation, which gives \(\psi f=\rho\). [Matroid intersection algorithm](https://page.math.tu-berlin.de/~felsner/Lehre/SemMatS/Literatur/Schrijver-41%3AMatIntersection.pdf)

## 3. Enumerating representatives over the mark

Let \(G'=A\rtimes K\) be the current splitting layer and let \(D\unlhd G'\) be the current bound on the kernel. We seek one representative for each sufficient class of normal quotients \(G'/N\to G'/D\), where \(N\le D\), up to isomorphism respecting the displayed map.

For non-elementary \(A\), use \(A_0=A\cap D\) and \(C=A/A_0\). Enumerate the at most \(|A|\) fixed quotient types \(B\) of \(A\) from Section 2. For each \(B\), enumerate all additive homomorphisms \(B\to C\), keeping the equivariant epimorphisms. If \(C\) needs \(r\) generators and the cyclic factors of \(B\) have lengths \(s_1,\ldots,s_b\), the image of a cyclic generator for a factor of length \(s_j\) has at most \(p^{rs_j}\) possibilities, since it is killed by \(p^{s_j}\). Hence the total number of homomorphisms, and the enumeration cost up to a polynomial factor, are at most \(|B|^r\). For each retained \(\psi\), apply the marked lemma and retain one \(f\) if it exists.

Any eligible kernel \(U\le A\cap D\) invariant under \(K\) yields a quotient map \(A/U\to C\). Choose a \(K\)-module isomorphism \(A/U\cong B\) to one of the representatives. Transporting the mark through that isomorphism gives some enumerated \(\psi:B\to C\), and the composite \(A\to A/U\cong B\) is a feasible lift. The retained representative therefore has the same quotient map up to \(K\)-equivariant isomorphism over \(C\). For elementary abelian \(A\), use the original marked algorithm. In that case \(A\cap D\) has a \(K\)-stable complement inside \(A\), and the old algorithm has at most \(|A|\) representatives without a restriction on the rank of \(C\). [Elementary layers, §§2–3](https://github.com/Dugongue/MathProofs/blob/main/PortfolioIsomorphismCrossovers/GroupAlgorithms.md)

## 4. Recursion and bounds

Every \(N\unlhd G'\) has the form \(U\rtimes W\), with \(U\le A\) invariant under \(K\), \(W\unlhd K\), and \(W\) acting trivially on \(A/U\). To check this, put \(U=N\cap A\). The normal subgroups \(N/U\) and \(A/U\) of \(G'/U\) commute by their trivial intersection. Thus if \((a,k)\in N\), then \(k\) acts trivially on \(A/U\). Raising \((a+U,k)\) to the order of \(k\) puts its \(A/U\)-coordinate in this trivial intersection, so \(a\in U\) by coprimality. It follows that \(W=N\cap K\). Conversely, the stated conditions make \(U\rtimes W\) the kernel of the natural map to \((A/U)\rtimes (K/W)\).

At each retained representative \(f:A\to B\) recurse inside \(K\) with

$$
D'=(K\cap D)\cap\ker(K\to\operatorname{Aut}(B)).
$$

For a returned quotient \(K/W\to K/D'\), reconstruct \(B\rtimes (K/W)\to G'/D\). Its map on \(B\) comes from \(\psi\) and \(C=A/(A\cap D)\), and its map on \(K/W\) comes from the original map \(K\to G'/D\). The action on \(B\) and this latter map both factor through \(K/D'\). Therefore relative isomorphism over \(K/D'\) extends to relative isomorphism over \(G'/D\). Section 3 shows that replacing an actual \(A/U\) by a retained \(B\) leaves the kernel of the action of \(K\) unchanged and identifies the two maps to \(C\). Induction gives coverage of all eligible kernels up to relative isomorphism.

Start with \(D=G\). Along a recursion branch, \(D\) inside \(G^{(i)}\) is the intersection of the kernels of its actions on the chosen quotients of the earlier \(A_j\). Each chosen module is a quotient \(A_j\to B_j\) equivariant for \(G^{(j+1)}\). Therefore \(E_i\le A_i\cap D\), which bounds the rank of \(A_i/(A_i\cap D)\) by \(r_i\) whenever \(A_i\) is non-elementary. The local branch bound is \(|A_i|^{r_i+1}\), including elementary layers where \(r_i=0\). Thus the number of nodes is bounded by

$$
(1+\log_2|G|)\prod_i |A_i|^{r_i+1}
=(1+\log_2|G|)|G|\prod_i |A_i|^{r_i}.
$$

Local candidate testing and reconstruction have polynomial cost per enumerated branch, including empty branches. Recursion leaves produce actual quotient tables and maps from \(G\), each of which can be compared with \(H\). Every quotient of an abelian Sylow tower again has an abelian Sylow tower. This follows from the images of the tower series, whose nontrivial factors are quotients of the Sylow factors and have the appropriate prime-power orders. Recognize a target tower by successively finding normal abelian Sylow subgroups and passing to quotients. Babai and Qiao's polynomial-time isomorphism and transporter-coset test gives a witness for any positive comparison. Composing the quotient map with that isomorphism constructs the requested epimorphism. [Babai–Qiao](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2012.453) · [Coset formulation, Proposition 1.1](https://arxiv.org/html/2605.26748v1#S1)

To obtain the best bound from raw input, try all prime orders. There are at most \(|G|\) of these, since the product of \(t\) distinct primes dominates \(t!\). Normal Sylow subgroups, when present, are exactly the set of prime-power order elements for the selected prime. Splitting each extension is a polynomial-time table calculation by averaging the section's two-cocycle. Two complements to an abelian Hall kernel are conjugate by an element of the kernel. For coprime complements this follows by averaging their difference, a one-cocycle. Applying such a conjugation to a splitting at level \(i\) preserves each earlier \(A_j\) as a subgroup and transports all later actions, so feasibility of a prime order and the numerical \(r_i\)'s are independent of the complement choices. The algorithm computes the product bound in binary and uses the best valid order. [Cocycle averaging, §1](https://github.com/Dugongue/MathProofs/blob/main/PortfolioIsomorphismCrossovers/GroupAlgorithms.md)

## 5. Exact binary subcode correspondence

Let \(C\le\mathbb F_2^r\) be a binary code, identify \(\mathbb F_2^r\) with \(2(\mathbb Z/4)^r\) by doubling, and set

$$
A_C=(\mathbb Z/4)^r/(2C),\qquad
G(C)=\mathbb F_3^r\rtimes A_C.
$$

An element with residue \(a\in A_C/2A_C=\mathbb F_2^r\) inverts precisely the coordinates \(i\) with \(a_i=1\). These are abelian Sylow towers admitting explicit tables in \(2^{O(r)}\) bit time.

**Theorem.** For \(C,D\le\mathbb F_2^r\), epimorphism \(G(C)\to G(D)\) holds exactly when some coordinate permutation \(\pi\) carries \(C\) into \(D\). The exact number of epimorphisms is

$$
6^r\,2^{r(r-\dim D)}
\#\{\pi\in S_r : \pi C\subseteq D\}.
$$

An epimorphism maps the normal Sylow \(3\)-subgroup onto the target's normal Sylow \(3\)-subgroup, because the quotient of the source by that subgroup has order a power of two. Its restriction there is an isomorphism. The image of \(A_C\) is a Sylow \(2\)-complement of the target, so conjugate by a target element of \(\mathbb F_3^r\) to send this complement to \(A_D\). The resulting map on complements is onto. Its induced map on \(A_C/2A_C\to A_D/2A_D\) is an invertible binary linear map. Compatibility with the \(3\)-subgroup isomorphism means that it transports the multiset of weights of the diagonal action. Those weights are the \(r\) distinct coordinate characters, which constitute a basis of the dual. Therefore the binary map is a coordinate permutation \(\pi\).

Any lift \(\beta:A_C\to A_D\) of \(\pi\) carries the double of a coordinate generator to the double of the corresponding target generator. Its respect for the defining doubled relations is exactly \(\pi C\subseteq D\). Conversely, if this containment holds, the coordinate permutation on \((\mathbb Z/4)^r\) descends and gives a surjection between the complements. Combined with the same coordinate permutation on \(\mathbb F_3^r\), this gives the group epimorphism.

For a fixed allowable \(\pi\), each of the \(r\) images of the generating lifts in the complement can be chosen independently within its residue coset of size \(|2A_D|=2^{r-\dim D}\). The relators of \(A_C\) are commutativity, fourth powers, and the specified doubled relations, so all choices work. Surjectivity follows from surjectivity modulo \(2\) by iteration. Each weight space of the \(3\)-subgroup is a line, with two available nonzero scalars for its isomorphism, giving \(2^r\) choices. Finally conjugating the image complement by the \(3\)-subgroup yields \(3^r\) choices, all distinct because the common fixed subspace of the independent coordinate inversions is zero. Each resulting epimorphism has a unique normalization of its complement, giving the formula.

The code can also be recovered from a raw table promised to come from this family. Compute the normal Sylow \(3\)-subgroup and a complement \(A\). Recover the common weight lines by scanning the nonzero vectors of \(\mathbb F_3^r\) and retaining those on lines preserved by every generator of \(A\). List these lines in any order. For each coordinate sign pattern with one negative sign, choose an element of \(A\) with that pattern. The binary relations among the doubles of the chosen elements give \(C\), up to the chosen permutation of lines. The recovered code therefore suffices for a reverse reduction.

It follows that polynomial Cayley-table time on this two-prime subfamily is equivalent to \(2^{O(r)}\)-time binary permutation subcode containment, with both source and target of length \(r\). The known NP-completeness of succinct subcode containment by itself gives no Cayley-table lower bound, since the tables are exponential in \(r\). This identifies a precise common algorithmic target with the earlier direct-power central-radical construction for Open Question 3(5). [Binary subcode containment](https://eprint.iacr.org/2022/1749) · [MathProofs central-radical correspondence](https://github.com/Dugongue/MathProofs/blob/main/FourAlgebraicIsomorphismTransfers/Epimorphisms.md)

For example, taking \(G(0)\) as the fixed source yields quotients \(G(C)\) for every binary code \(C\). For even \(r\), the codes of dimension \(r/2\) supply at least \(2^{r^2/4}/r!\) different group isomorphism classes by the theorem (or by counting graphs of linear maps between two \(r/2\)-spaces). Since \(|G(0)|=12^r\), a method explicitly listing all unmarked quotient isomorphism types cannot run in polynomial time. The marked-quotient representation in the positive theorem circumvents this growth exactly where its rank bound applies.

An independent finite check compared the counting formula with direct enumeration of generator images for all 25 ordered pairs of binary codes of length two. It checked commutation, fourth-power and doubled-code relations, the prescribed conjugation actions, and generation of each target. The proof above establishes the formula for all lengths.
