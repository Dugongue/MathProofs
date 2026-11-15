# Exponential sparse Polynomial Calculus lower bounds for tensor nonisomorphism in characteristic zero

**Theorem.** Over any field of characteristic different from 2, for every sufficiently large $n$ there are two nonisomorphic $n\times n\times n$ tensors with entries in $\{0,1\}$ whose ordinary Polynomial Calculus (PC) refutations require degree $\Omega(n)$ and sparse size $2^{\Omega(n)}$. The equations are the cubic action and quadratic inverse equations of Galesi, Grochow, Pitassi and She. Sparse size counts nonzero monomial occurrences. A separate positive-characteristic proof covers characteristic 2.

## A Boolean source with exponential sparse proof size

Use an inconsistent 3-XOR instance on $k$ bits and $m=ck$ clauses for a sufficiently large fixed constant $c$. Assume each clause uses three distinct variables and no underlying triple repeats. The Ben-Sasson–Impagliazzo degree bound in Galesi et al., Theorem 6.1, supplies instances whose signed PC encoding needs degree $\Omega(k)$ over the working field. At constant clause density, a repeated underlying triple has probability $O(k^{-1})$ by the union bound, and satisfiability has probability at most $2^{k-m}$ for independent uniform right-hand sides.

Let $\ell_{i,0},\ell_{i,1}$ be complementary Boolean literal variables. The Polynomial Calculus with Resolution (PCR) encoding uses their Boolean axioms, the complement axiom $\ell_{i,0}+\ell_{i,1}-1$, and the literal product $\prod_{i\in e}\ell_{i,a_i}$ for each assignment $a$ violating a clause $e$. The product $\ell_{i,0}\ell_{i,1}$ follows by multiplying the complement axiom by $\ell_{i,0}$ and subtracting its Boolean axiom.

The PCR degree is $\Omega(k)$. Substitute $\ell_{i,a}\mapsto(1+(-1)^a y_i)/2$ into the signed equations in variables $y_i$. The complement and Boolean axioms can be derived in degree at most 2. For a forbidden assignment $a$ on clause $e$, let $\phi$ be the image of its literal product. The difference $y_i(1+(-1)^{a_i}y_i)/2-(-1)^{a_i}(1+(-1)^{a_i}y_i)/2$ is a scalar multiple of $y_i^2-1$. Consequently $(\prod_{i\in e}y_i)\phi$ is congruent to $(-1)^{\sum_i a_i}\phi$ by an ordinary degree-6 derivation. Multiplying the signed clause by $\phi$ gives the opposite sign, so subtraction and scaling derive $\phi$ in degree 6. A multiplication by an affine literal can be simulated by one variable multiplication and linear combination. Thus a PCR proof of degree $D$ yields a signed proof of degree at most $\max(D,6)$. The PCR size–degree tradeoff gives sparse size $2^{\Omega(k)}$, using $2k$ literal variables and axiom degree at most 3.

## Parity graphs and monomial witnesses

For right-hand sides $d$, construct a graph $G_d$. Each variable $i$ contributes two state vertices $v_i^0,v_i^1$, joined to each other, with five private leaves attached to each state. For each clause $e$, create four vertices $w_e^a$ indexed by labels $a\in\{0,1\}^e$ of parity $d_e$, and join each to $v_i^{a_i}$ for every $i\in e$. Add two separate disjoint edges. Both $G_0$ and $G_b$, with $b$ the instance's right-hand sides, have $N=12k+4m+4$ vertices.

They are isomorphic exactly when the 3-XOR instance is satisfiable. A satisfying assignment flips each state pair, translates the corresponding three bits of each clause label, transports the leaves by their parents, and fixes the two separate components. Conversely, every isomorphism preserves the state vertices (degree at least 6) and the clause vertices (degree 3). The edges between states recover the variable pairs. An isomorphism permutes them and flips each pair by some bit, indexed at the target. The three labels adjacent to any source clause vertex have parity zero. Their images have parity equal to the sum of the three target flip bits. This must be the parity of the target clause, yielding a satisfying assignment.

Use a matrix $P$ with target vertices as rows and source vertices as columns. Entries between different groups are zero. On each pair of state vertices, entries are $\ell_{i,a+c}$ for source and target bits $a,c$, where addition is modulo 2. On leaves, the same pair rule applies separately to each variable and private-leaf index. Inside a clause group $e$, set $P_{c,a}=\prod_{i\in e}\ell_{i,a_i+c_i}$. Use the identity on the fixed components. Entries are zero, one or single monomials of degree at most 3.

The following all have polynomial sparse-size and constant-degree PC derivations from the PCR axioms.

1. **Row and column sums.** For a state or leaf pair, the sum is a complement equation. For a fixed source or target clause label, summing over all eight possible flip triples gives $\prod_{i\in e}(\ell_{i,0}+\ell_{i,1})$, which equals 1 by telescoping the complement equations. The products excluded from the row or column are precisely the forbidden assignments, hence vanish by input axioms.
2. **Orthogonality and idempotence.** In one row, distinct nonzero entries prescribe incompatible flips somewhere, and likewise in one column. Their pairwise products are multiples of $\ell_{i,0}\ell_{i,1}$. Each entry is idempotent by the Boolean axioms. Together with the sums this proves $PP^{\mathsf T}=P^{\mathsf T}P=I$.
3. **Adjacency transport.** For adjacency matrices $A_0,A_b$, if $A_0(v,v')\ne A_b(u,u')$ then $P_{uv}P_{u'v'}$ is zero or divisible by a literal collision. A state-pair edge requires the opposite bit in the same pair. A leaf edge requires the same bit as its parent. A clause-to-state edge requires incidence and the same bit. Each change in adjacency within the allowed groups therefore requires two incompatible flips of a shared variable. All other adjacencies are fixed under the group rules. Now expand
   $$
   (P A_0 P^{\mathsf T})_{u,u'}-A_b(u,u')
   =\sum_{v,v'}(A_0(v,v')-A_b(u,u'))P_{uv}P_{u'v'}
   +A_b(u,u')\left((\textstyle\sum_v P_{uv})(\textstyle\sum_{v'}P_{u'v'})-1\right).
   $$
   The terms in the sum vanish by the collisions, and the last expression follows from the two row sums by telescoping. Thus $P A_0P^{\mathsf T}=A_b$.

## Tensor equations and sparse-size transfer

For a graph $G$ of this form, take the slices $E_{11},\ldots,E_{NN},A_G$ of size $N\times N$. Pad the first two modes with zeros to make a cube of side $N+1$. The span of the rank-one slices in the resulting slice space is the diagonal space $D$. Indeed, for a diagonal matrix $D_0$ and $\lambda\ne 0$, the matrix $D_0+\lambda A_G$ has a $2\times2$ submatrix $\lambda I_2$, using one endpoint of each separate edge for rows and the opposite endpoints for columns. Inside $D$ the only rank-one lines are the individual $F E_{ii}$.

Consequently a tensor isomorphism induces a left-right equivalence of the slice spaces that preserves $D$ and permutes its rank-one lines. If $X E_{ii}Y^{\mathsf T}$ is a multiple of $E_{jj}$, then $Xe_i$ and $Ye_i$ are multiples of the same $e_j$. Thus on the first $N$ coordinates both matrices act monomially with the same permutation. They send $A_G$ to a matrix in $F A_H+D$ with nonzero coefficient of $A_H$ and zero diagonal. This sends the adjacency nonzero pattern to that of $A_H$, giving a graph isomorphism. Conversely a graph permutation acts on all three modes, preserving the last position. This also proves nonisomorphism after scalar extension.

For the formal projection, substitute $\operatorname{diag}(P,1)$ in each mode and its transpose in each inverse. The inverse and adjacency-slice equations follow from the preceding identities. Action equations for the diagonal slices reduce to
$$
\sum_v P_{uv}P_{u'v}P_{tv}-\boldsymbol{1}_{u=u'=t}.
$$
If the indices differ, column orthogonality annihilates each summand. When all are equal, idempotence and the row sum give the equation. The padding equations are identically satisfied. In a fixed finite field, each projected entry is idempotent so the added field equations also follow.

A substitution by degree-at-most-3 monomials cannot increase the number of terms in a proof line. Each multiplication inference can be simulated with at most three such inferences, and the simulations of all projected axioms together have polynomial size. Therefore size $S$ for a TI refutation would give a PCR refutation of size at most $3S+\operatorname{poly}(N)$, and degree $D$ would give degree at most $\max(3D,O(1))$. Since $N=\Theta(k)$, the source bounds give both claims. For a prescribed large $n$, choose $k=\Theta(n)$ with $N+1\le n$ and pad the tensors with zeros and the substitutions with identities. Zero padding preserves the essential spaces of a tensor in each mode and therefore preserves nonisomorphism.

## Scope and sources

This informal argument gives the sparse lower-bound direction in Open Question 7.2 in characteristic zero, in addition to the separate positive-characteristic proof. The bound is exponential in the tensor side dimension and still leaves open a subexponential upper bound measured in the $6n^2$ ring variables.

- Nicola Galesi, Joshua A. Grochow, Toniann Pitassi and Adrian She, [On the Algebraic Proof Complexity of Tensor Isomorphism](https://arxiv.org/abs/2305.19320), Theorem 6.1 and Open Question 7.2.
- Eli Ben-Sasson and Russell Impagliazzo, [Random CNFs Are Hard for the Polynomial Calculus](https://doi.org/10.1007/s00037-010-0293-1), Theorem 3.3 and Lemma 4.3 of the final journal version.
- Michael Alekhnovich, Eli Ben-Sasson, Alexander A. Razborov and Avi Wigderson, [Pseudorandom Generators in Propositional Proof Complexity](https://doi.org/10.1137/S0097539701389944), the PCR size–degree theorem.
- Christoph Berkholz and Martin Grohe, [Linear Diophantine Equations, Group CSPs, and Graph Isomorphism](https://arxiv.org/abs/1607.04287), the group-CSP approach to isomorphism underlying the parity graphs.
