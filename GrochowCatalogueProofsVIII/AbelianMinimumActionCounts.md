# Counting all minimum faithful actions of finite abelian groups

## GP-0390

For any finite abelian group, the number of isomorphism types of faithful actions of minimum permutation degree is computable in polynomial bit time from its prime-power invariant factors, without enumerating the actions. The result includes the extra four-point orbits available at the prime two. Group isomorphisms here are fixed: actions are first counted up to equivariant bijection for the given group.

### Orbit costs and normal form

Let $A$ be the character group of the input, written additively. A transitive orbit with stabilizer $H$ corresponds to its annihilator $B\le A$, of order equal to the orbit size. A family of orbits is faithful precisely when these subgroups generate $A$. A finite abelian subgroup decomposes into cyclic groups of prime-power orders $m_1,\ldots,m_h\ge2$. Replacing its orbit by the orbits from those cyclic subgroups preserves the subgroup they generate and costs $\sum m_i$ in place of $\prod m_i$. With at least two factors this is strictly cheaper, except when $h=2$ and $m_1=m_2=2$. Fixed points can be deleted for a nontrivial input. Consequently every optimal action uses cyclic prime-power character subgroups and, possibly, distinct elementary abelian subgroups of order four. All these subgroups are supported on a single prime.

For a fixed prime $p$, choose one generator of each cyclic subgroup and an ordered basis for each elementary subgroup of order four. Faithfulness is equivalent to spanning $A_p/pA_p$. Any dependence among the chosen residue vectors allows one vector to be removed without changing the generated subgroup of $A_p$. This uses the finite form of Nakayama's lemma, or iteration of multiplication by $p$. If the vector came from an order-four elementary subgroup, replace that subgroup by the line of its remaining basis vector. Either change lowers the cost. Thus the vectors of an optimum give a basis. Conversely the cost of an elementary subgroup of order four is exactly the sum of the costs of its two involution lines. It suffices to optimize a basis by element orders, and then allow pairs of order-two basis vectors to be grouped in such subspaces.

Write $A_p\cong\bigoplus_j(C_{p^j})^{a_j}$, and put $b_j=\sum_{i\le j}a_i$ and $b_0=0$. The residues of elements of order dividing $p^j$ are exactly the subspace $U_j=(A_p[p^j]+pA_p)/pA_p$ of dimension $b_j$. For every basis, the number of chosen elements of order at most $p^j$ is at most $b_j$. A single basis reaches all these upper bounds by using the cyclic factors. Writing the weighted order sum by its successive threshold counts shows that equality at every threshold is necessary and sufficient for optimality, because the weights $p^j$ strictly increase. Thus an optimal basis has exactly $a_j$ vectors of order $p^j$ and their residues at lengths at most $j$ are a basis of $U_j$. This also proves the usual additive formula for the degree. [Faithful degrees and orbit decompositions](https://archives.maths.anu.edu.au/people/Kovacs/K084.pdf)

### The counting formula

Define
$$
 L_j=p^{\sum_i a_i\min(i,j)-b_j},
 \qquad
 M_j=|\mathrm{GL}_{a_j}(\mathbb F_p)|\,p^{a_j b_{j-1}}\,L_j^{a_j}.
$$
Here $L_j$ is the number of lifts of a residue in $U_j$ to $A_p[p^j]$. At length $j$, the ordered new residues must form a basis of $U_j/U_{j-1}$, each with $p^{b_{j-1}}$ lifts into $U_j$. Each further lift to $A_p[p^j]$ has exact order $p^j$, since the residue lies outside $U_{j-1}$. This proves the count $M_j$ for the ordered generator choices, independently of the earlier basis choices in the flag.

For $(p,j)\ne(2,1)$ the factor in the answer is
$$
 \frac{M_j}{a_j!\,\varphi(p^j)^{a_j}}.
$$
Permuting the generators and replacing each by another generator of the same cyclic subgroup is exactly the overcount. At $(p,j)=(2,1)$ the factor instead is
$$
 M_1\sum_{t=0}^{\lfloor a_1/2\rfloor}
       \frac{1}{(a_1-2t)!\,t!\,6^t}.
$$
Indeed, for $t$ elementary subgroups of order four, use the first $a_1-2t$ vectors as single lines and group the remaining ordered vectors into consecutive pairs. There are six ordered bases for each resulting two-dimensional subgroup, and its image still has independent dimension two in $U_1$. The stated divisor also accounts for ordering the single lines and ordering the pairs. Multiplying these factors over all primes and lengths counts the actions, since an abelian transitive action is determined up to equivariant bijection by its stabilizer, and a general action by the multiset of its transitive types. All integers have polynomial bit length in the listing of expanded prime-power invariant factors and $\log|A|$. The trivial group has one minimum action under either convention for the empty domain.

### GP-0391 as a consequence

The minimum actions form one orbit under twisting by group automorphisms for each possible number $t$ of elementary character subgroups of order four, giving exactly $\lfloor a_{2,1}/2\rfloor+1$ such orbits, with $a_{2,1}=0$ if there is no two-part. In fact any optimal ordered list of chosen generators of given lengths defines an isomorphism from the displayed product of its cyclic factors to $A$, because it is onto and the orders agree. Send one such list to another with groups of two matched. This induces a group automorphism by character duality. Conversely twisting preserves the number of order-four noncyclic annihilators, so different $t$ cannot merge.
