# Polynomial group isomorphism with arbitrary central radicals and perfect product quotients

**Status:** AI-assisted informal proof. The new combination is explicit scalar-cohomology enumeration with a bit-position hypergraph. The previous algorithms and group-theoretic ingredients are credited below. Publication priority has not been established.

**Theorem.** Let $G,H$ be finite groups given by Cayley tables. Suppose their solvable radicals equal their centers and, for each group, the quotient by the center is either a direct product of nonabelian simple groups or a direct product of perfect groups of bounded order. There is a deterministic polynomial-time algorithm for isomorphism, an isomorphism witness, generators of the full automorphism group, and exact counting of isomorphisms. The bound in the second branch may depend on the fixed order bound. The centers may be arbitrary finite abelian groups. The proof allows both kinds of factors in the same product, with one fixed size bound on the nonsimple factors.

This extends both branches of Grochow–Qiao's [Theorem 7.1](https://arxiv.org/pdf/1309.1776) by dropping the elementary-abelian hypothesis. It leaves Open Problem 8.3's further step from a product quotient to the permutation kernel untreated. The recent [Levet algorithm](https://arxiv.org/abs/2604.13953) gives stronger parallel bounds under the elementary-abelian hypothesis.

## 1. Reduce the coefficient orbit to a family of scalar subgroups

Compute the centers and quotient multiplication tables. Reject unequal abelian types and identify the centers as one abelian group $A$. Decompose the quotients into directly indecomposable factors, using the polynomial-time direct decomposition algorithm used in Grochow–Qiao Section 7. A perfect factor remains perfect after direct decomposition. The resulting factors are centerless, perfect and directly indecomposable. Such factors are unique as subgroups of the quotient, by the direct product structure fact in Grochow–Qiao Section 5.1. Match factor types using the supplied tables: for a nonabelian simple factor, two generators suffice, so all isomorphisms can be found by testing generator images. A nonsimple factor has bounded order. This identifies the two quotients with the same product $Q=\prod_i T_i$. A mismatched type multiset is grounds to reject. Fix the same labeled representative for factors of each type.

Choose sections and compute the two central extension classes $c,c'\in H^2(Q,A)$. There is an isomorphism inducing $\beta\in\operatorname{Aut}(Q)$ exactly when an automorphism of $A$ carries $\beta c$ to $c'$, where $\beta$ acts by inverse pullback. Because the action of $Q$ on $A$ is trivial, quotient pullback commutes with all coefficient endomorphisms.

Write $R=\operatorname{End}(A)$. In any left module over a finite ring, $Rx=Ry$ is equivalent to $y=ux$ for a unit $u$ of $R$. For the nontrivial direction write $y=ax$ and $x=bx$, put $c_0=1-ba$, and note $c_0 x=0$. In each matrix block of $R/\operatorname{Jac}(R)$ the images $A_0,C_0$ have disjoint kernels. On $\ker C_0$ the operator $A_0$ is injective. On a complement choose an isomorphism $j$ onto a complement to $A_0(\ker C_0)$ and extend $T(C_0v)=j(v)-A_0v$ linearly. Then $A_0+TC_0$ is invertible. Lift the block choices to $t\in R$. The unit $u=a+tc_0$ satisfies $ux=y$. The reverse direction is immediate. This is the finite-ring stable-range-one argument used in the companion central-extension work. The Grochow–Qiao scaled-row orbit criterion in Section 6.1.1 is a related coordinate description.

For each distinct cyclic type $D=C_{p^e}$ occurring in $A$, define
$$
S_D(c)=\{f_*c:f\in\operatorname{Hom}(A,D)\}\le H^2(Q,D).
$$
These are images of additive homomorphisms. Decompose $A$ into individual cyclic summands. Every coefficient endomorphism is an independent choice of one map from $A$ to each target summand. Additivity of cohomology in the coefficients shows that $Rc$ is the product of the corresponding $S_D(c)$, with repeated copies for repeated target types. Consequently
$$
\beta\text{ lifts}\quad\Longleftrightarrow\quad \beta S_D(c)=S_D(c')\text{ for every }D.
$$
The same $\beta$ is used for all types. Treating different types independently at the final transporter step would lose this condition.

## 2. Enumerate the scalar codes in polynomial table time

For a cyclic coefficient $D$ the restriction isomorphism
$$
H^2(Q,D)\simeq\prod_i H^2(T_i,D)
$$
is natural for factor automorphisms and permutations. To see injectivity, lift the factors to the central extension. Their mutual commutators define pairings biadditive in the abelianizations, which vanish by perfectness. Products of sections on the factors then give a section whose cocycle is the sum of the individual cocycles. Surjectivity follows by summing pullbacks of arbitrary factor cocycles. This is the restriction argument of Grochow–Qiao Lemma 7.4.

Let $B_{i,D}=H^2(T_i,D)$. For simple $T_i$, Lemma 7.9 of the same paper bounds the minimal number of generators of $B_{i,D}$ by an absolute constant (we may use 18) for every cyclic $D$. For a factor of bounded order, the cocycle subgroup of $D^{|T_i|^2}$, and hence its cohomology quotient, needs at most $|T_i|^2$ generators. Here $D$ is a cyclic prime-power group, so the latter bound follows from the structure of subgroups of finite abelian $p$-groups. Positive-dimensional finite group cohomology is annihilated by the group order, by restriction and transfer to the identity subgroup. Hence for an absolute constant $b$ in the simple case, or a constant depending on the factor-order bound, we have
$$
|B_{i,D}|\le |T_i|^b,\qquad \prod_i |B_{i,D}|\le |Q|^b.
$$
In particular this bound does not contain a factor $|D|$ for each coordinate. Compute cyclic coordinates for $B_{i,D}$ by solving the normalized cocycle congruences and quotienting by coboundaries using Smith normal form. Smith normal form also computes the images under group and coefficient maps. Generate $S_D(c)$ by evaluating on additive generators of $\operatorname{Hom}(A,D)$ and restricting to the factors. These generator lists and matrices have polynomial bit size. Enumerate each subgroup by additive closure in its ambient product. The number of elements per subgroup is at most $|Q|^b$, and the number of cyclic types is at most $\log_2 |A|$. All enumeration is polynomial in the original table size. The ambient group $H^2(Q,A)$ and the simultaneous product of all the scalar subgroups are never expanded.

## 3. Encode one scalar code using logarithmically many vertices

Factor-preserving permutations act on positions in the product $\prod_i B_{i,D}$. Identical factor types use identical coordinate systems, and label each element of their common alphabet by an integer from zero to its order minus one. For a fixed $D$ make a hypergraph with a marker vertex $v_i$ and $\lceil\log_2|B_{i,D}|\rceil$ bit vertices at each position $i$. Color marker vertices by factor type and bit vertices by their bit number and factor type. Give the marker and its bit vertices a distinguished block edge. For each word in $S_D(c)$ add a word edge consisting of the vertices where its letter bits are one. Distinguish block and word edges by edge color. Zero gives an empty word edge, which can also be omitted since every code contains zero.

A permutation preserving the vertex and block-edge colors is exactly a permutation of equal-type factors and its unique extension to bit vertices. If a block has no bit vertices, its marker still retains the factor. Such a permutation matches the word edges exactly when it maps one scalar subgroup to the other. The encoding has at most
$$
\sum_i(1+\lceil\log_2 |B_{i,D}|\rceil)=O(\log|Q|)
$$
vertices, with a constant independent of the coefficient exponent and prime.

Use [Luks's singly exponential hypergraph isomorphism algorithm](https://doi.org/10.1145/301250.301427), including colored hypergraphs. It takes $2^{O(v)}$ times polynomial in the explicit input length on $v$ vertices. A decision implementation suffices to recover the complete coset. Individualize vertex images along a stabilizer chain, in at most $O(v^2)$ decision calls to obtain a witness and generators. Unique vertex colors used for individualization are retained by the colored algorithm. Thus every scalar code returns its exact transporter coset as permutations of the same marker set, in polynomial time. Intersect the resulting permutation cosets using the singly exponential coset-intersection algorithm of Luks (1999), as cited in Grochow–Qiao Sections 5.2 and 7.3. Its degree is the number of factors, at most $\log_2 |Q|$. Iterated intersection returns the transporter requiring all $D$ simultaneously. Separate hypergraphs for different $D$ retain the logarithmic vertex bound.

## 4. Process all quotient maps and lift the resulting cosets

Every quotient automorphism is uniquely a product of independent factor automorphisms and a type-preserving permutation. In the simple case $|\operatorname{Aut}(T_i)|\le |T_i|^2$ by two-generation. In the bounded case it is at most a fixed power of $|T_i|$. All diagonal tuples can therefore be enumerated in polynomial table time. For each tuple twist one extension by that tuple and compute the permutation coset using Sections 2–3. This yields a disjoint union of cosets of liftable quotient maps, indexed by diagonal part. Empty centers and trivial quotients give the same algorithm with empty constraint families and the evident trivial cases.

For one returned quotient map construct an actual lift by the polynomial [fixed-quotient abelian-extension module algorithm](AbelianExtensionLinearization.md). It applies to an arbitrary abelian kernel and uses the quotient table, so no bounded-generation assumption is introduced. For the source group against itself, take a representative from every nonempty diagonal part and generators of the permutation-only stabilizer, which is the identity-diagonal part. These generate the full image of the source automorphism group on $Q$: within each diagonal part any two liftable maps differ by a liftable pure permutation, after taking the difference in the correct order for the chosen product convention. Lift each of these generators and adjoin the full fixed-quotient kernel. That kernel is computed in polynomial time by the marked variant of the companion algorithm and its stabilizer-chain construction. The resulting permutations on $G$ generate $\operatorname{Aut}(G)$. Standard permutation group order computation gives the number of isomorphisms whenever a witness exists. Otherwise the number is zero.

## 5. Relation to the published question

Grochow and Qiao already use independent factor automorphisms, factorwise cocycle restriction, and coset intersection. Their Section 7.4 discusses extending Theorem 7.1 to arbitrary abelian centers, and Observation 7.8 gives a sufficient algorithm for group codes over cyclic prime-power alphabets. Here the alphabet at position $i$ is the much smaller group $H^2(T_i,D)$, whose binary length is bounded in terms of the quotient factor. Encoding individual letter bits as vertices makes all words explicit while preserving the exact permutation action. This sidesteps the need for an algorithm with singly exponential dependence on the length for *general* cyclic-alphabet group codes. The Levet parallel result cited above still assumes elementary-abelian centers in its polynomial-size constant-depth product-quotient theorem. These comparisons establish the scope relative to those papers. They do not establish first publication priority.
