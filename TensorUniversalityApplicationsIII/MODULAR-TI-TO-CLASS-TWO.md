# From free tensor isomorphism modulo an integer to class-two groups

**Theorem.** Let $M\ge2$ be given in binary. Ordinary 3-tensor isomorphism over $R=\mathbb Z/M\mathbb Z$, with free modes of ranks $n_1,n_2,n_3$, reduces in deterministic polynomial time to isomorphism of finite class-two groups given by central presentations. For positive mode ranks the group order is at most $M^{O(n_1+n_2+n_3)}$, with an absolute constant. The reduction needs no factorization of $M$. If $M=p^e$ the groups are $p$-groups. Their quotient by the center has exponent $M$, and the center is homocyclic of exponent $M$ for odd $M$ and $2M$ for even $M$. A group isomorphism recovers an ordinary tensor isomorphism, and every tensor isomorphism lifts. The conversion also works when every input coefficient is a nonunit.

Together with the [class-two group to free tensor reduction](https://github.com/Dugongue/MathProofs/blob/main/TensorUniversalityApplicationsII/CLASS-TWO-POWER-TENSORS.md) this proves uniform polynomial-time equivalence between the two succinct problems, with the modulus allowed as part of the tensor input. The linear bound on the logarithm of the group order is specific to the tensor-to-group direction. It transfers class-two Cayley-table algorithms even at arbitrary even moduli. The construction extends the alternating marker method of [Grochow–Qiao, Part IV §2](https://arxiv.org/html/2306.16317#S2). Compare the finite-ring tensor actions of [Part V, Theorem 1.6](https://arxiv.org/html/2611.00735v1#S1.SS3).

## 1. A rank that detects nonunit markers

First work over $R_p=\mathbb Z/p^e\mathbb Z$. For a matrix $A$ over $R_p$ let $\rho(A)$ be the smallest number of generators of its image. This is preserved by invertible changes of row and column coordinates, and is additive on block diagonals. For any finite abelian $p$-group, the minimum number of generators is the number of nonzero cyclic summands, which is also the dimension of its subgroup killed by $p$. A submodule generated inside $R_p^D$ therefore needs at most $D$ generators. In particular $\rho(\alpha I_w)=w$ for every nonzero $\alpha\in R_p$, since its image is a direct sum of $w$ nonzero isomorphic cyclic modules. The same holds when the identity is replaced by an invertible matrix. This is also the inner rank. A factorization through an $r$-dimensional free module places the image inside an $r$-generated module, and conversely any $r$ generators of the image give a factorization. The argument uses the equality between the generating rank and the dimension of the subgroup killed by $p$ for the containment step. [Part V, §§2.3–2.4](https://arxiv.org/html/2611.00735v1#S2.SS3)

## 2. Four alternating markers recover both tensor modes

Write the three mode spaces as $X,Y,Z$. Regard the tensor as the rectangular matrix $B_z$ obtained by contracting with $z\in Z^*$. In $X\oplus Y$ put the alternating slice
$$
A_T(z)=\begin{pmatrix}0&B_z\\-B_z^{\mathsf T}&0\end{pmatrix}.
$$
The diagonal is zero also at even moduli. The coefficient module used below is the actual free module $Z^*$, so the construction makes no assumption on independence of these slices.

Put $V=X\oplus Y$. Add two private copies of $X^*$ and two of $Y^*$. There are four markers $F_1,F_2,F_3,F_4$. The first two pair $X$ with their own copies, and the next two pair $Y$ with their own copies. A pairing is written as a skew block with entries $I,-I$ off its diagonal. Give each marker a disjoint private symplectic block of dimension
$$
w_i=2(5+i)(D+1),\qquad D=3(n_1+n_2),\quad 1\le i\le4,
$$
on which it is the standard alternating matrix with determinant one. Other records vanish on this block. The total space so far is $E$ of rank $h=D+\sum_i w_i=O(n_1+n_2)$. The extended coefficient module is $Z^*\oplus R^4$.

For the slice with coefficients $(z,\alpha_1,\ldots,\alpha_4)$ the rank is
$$
\sum_{i\colon\alpha_i\ne0} w_i+r,\qquad 0\le r\le D.
$$
Indeed the four private symplectic blocks are direct summands and the remaining carrier has rank $D$. The threshold $\rho\le D$ detects exactly $Z^*$. The disjoint bands $[w_i,w_i+D]$ detect exactly nonzero coefficients on marker $i$ alone modulo $Z^*$. Successive weights differ by $2(D+1)$ and $2w_1>w_4+D$. Thus under any invertible congruence on the carrier and invertible map on the coefficient module, the base coefficient submodule and each marker line in its quotient are recovered. The image of the $i$-th standard marker coefficient has a unit on that line, because the induced quotient map has an inverse preserving the same lines. Consequently its slice has the form $\alpha F_i+A_{T'}(z)$ with $\alpha$ a unit.

For a marker of $X$ with unit coefficient, the image intersects $V$ in exactly $X$. In fact a vector in the image with no coordinate in the private copy of $X^*$ must have zero input covector on $X$, by the unit pairing. The data slice then contributes only an $X$ component, and the private copy supplies every $X$ component. For a unit marker of $Y$ the argument gives $Y$. The two image submodules for markers of $X$ have disjoint private supports outside $V$, so their intersection is exactly $X$. The other two images similarly recover $Y$. This works for any possible data coefficients in the two images and does not require a radical-free input. These intersections identify the two output modes under any transporter, and the restriction to $Z^*$ gives the original third-mode map by inverse transpose. Thus an isometry of the alternating records yields an ordinary tensor isomorphism. Conversely an ordinary tensor isomorphism acts on $V$ by the recovered block map, acts by inverse transposes on the four paired copies and fixes their heavy blocks. Its coefficient map uses the inverse dual of the given third-mode map and fixes each marker coefficient. These maps transport all the records.

The duplicate-image argument applies the two private markers per block from the [balanced partition reduction, §5](https://github.com/Dugongue/MathProofs/blob/main/TensorUniversalityApplications/BALANCED-TENSOR-DIMENSION.md). The additional step over the local rings is to count generators of each private image so that nonzero nonunit coefficients are visible.

## 3. Make the full alternating bimap have zero radical

Add a fifth marker $F_0$ on $\widehat E=E\oplus E^*\oplus H_0$. It pairs $E$ with its new dual copy and has a private standard symplectic block on $H_0$ of even dimension $w_0=2(h+1)$. Old slices are extended by zero. Every old coefficient has rank at most $h$. Any nonzero coefficient of $F_0$ has rank at least $w_0>h$ from its private block alone. The first rank cut therefore recovers all old coefficients, and the four original rank bands apply unchanged on them. Their image intersections recover exactly the two original modes in the larger carrier too. In the forward direction extend the old map on $E$ by inverse transpose on its new dual and by identity on $H_0$. This preserves the fifth marker.

Write the resulting alternating bimap as $\beta_T\colon\widehat E^*\times\widehat E^*\to Z\oplus R^5$ by evaluating the slices on the two covectors. A pseudoisometry means invertible maps on the argument module and the output module, with one common map on the arguments. This is the congruence comparison above with the applicable inverse transposes. The slice $F_0$ has invertible matrix on all of $\widehat E$, so $\beta_T$ has zero radical. Both $\operatorname{rank}\widehat E$ and the sum of the ranks of the input modules of this bimap are linear in $n_1+n_2+n_3$.

The construction uses only the input coefficients and constants zero, one and minus one. We can form it directly over $\mathbb Z/M\mathbb Z$. To prove correctness, decompose that ring by the Chinese remainder theorem into its prime-power factors. The same arrays give the construction over each factor with the same ranks. Invertible mode changes and bimap pseudoisometries exist over the product exactly when they exist in every factor. The arguments over local rings therefore give the same equivalence over $R$, without a factorization in the algorithm. Witness recovery can also be carried out over $R$ directly. The coefficient and carrier maps of a pseudoisometry already preserve the indicated submodules in every factor and hence globally, so read the restrictions in the displayed coordinates.

## 4. Realize the bimap by a group with the right central powers

Write $A=\widehat E^*$, $B=Z\oplus R^5$, and put $d=1$ for odd $M$ and $d=2$ for even $M$. Use $C=(\mathbb Z/dM\mathbb Z)^{\operatorname{rank}B}$, with inclusion $\iota:B\to C$ given by multiplication by $d$. Choose the ordered basis of $A$. Define a bilinear map $c:A\times A\to C$ whose entries above the diagonal are those of $\iota\beta_T$ and whose other entries are zero. Its skew difference is $\iota\beta_T$. On $A\times C$ use
$$
(a,u)(b,v)=(a+b,u+v+c(a,b)).
$$
Bilinearity gives the cocycle identity, so this is an associative group law with identity $(0,0)$ and inverse $(-a,-u+c(a,a))$. Its commutator is the skew difference, using $[x,y]=x^{-1}y^{-1}xy$. Its center is exactly $C$ because $\beta_T$ has zero radical and $\iota$ is injective. Thus any group isomorphism induces a pseudoisometry on the characteristic quotient and on the characteristic subgroup $dC\cong B$ of the center. Conversely any invertible change of $B$ lifts to an invertible change of $C$. If $d=2$, take any matrix representative modulo $2M$. Its determinant is coprime to $M$, and hence to $2M$ because $M$ is even.

The chosen basis lifts have $M$-th power zero in additive central notation. For an arbitrary lift the formula is
$$
(a,u)^M=(0,Mu+\tbinom M2 c(a,a)).
$$
The second term lies in $MC$ in either parity. For odd $M$ the binomial coefficient is a multiple of $M$. For even $M$ the value $c(a,a)$ is twice an integral residue, and $2\binom M2=M(M-1)$. Therefore any quotient basis image can be represented by a lift with $M$-th power zero, by changing its central coordinate. For a given pseudoisometry choose those adjusted lifts and the lifted center map. They preserve the commutators and power relations. The center relations, centrality and these basis commutator and power relations present the group, since collecting gives at most $|A||C|$ normal forms and the displayed multiplication realizes that many. The resulting homomorphism is an isomorphism because it is an isomorphism on the center and its quotient. These are the same central power corrections used in the reverse [class-two encoding](https://github.com/Dugongue/MathProofs/blob/main/TensorUniversalityApplicationsII/CLASS-TWO-POWER-TENSORS.md), here guaranteed for all pseudoisometries by the choice of central modulus.

The output presentation lists only the displayed cyclic orders, zero basis powers and the computed central commutator coefficients. Thus it has polynomial bit size and can be written in deterministic polynomial time. Its order is $M^{\operatorname{rank}A}(dM)^{\operatorname{rank}B}$, as claimed. Unequal input formats and formats with a zero mode are decided by their headers before constructing common-format outputs.

The special case $M=2$ uses the same central enlargement as an earlier reduction from binary field tensors. Here the marker and power arguments give the uniform construction for arbitrary binary moduli $M$. [Earlier field reduction, §7](https://github.com/Dugongue/MathProofs/blob/main/FourTensorAndGroupIsomorphismResults/group.md)

## 5. Algorithmic consequence

Let $L=(n_1+n_2+n_3)\log_2 M$. A Cayley table of either constructed group takes $2^{O(L)}$ time to write. By [Sun, Corollary 1.2](https://arxiv.org/html/2611.05920v1), the tensor problem therefore has a deterministic algorithm taking
$$
2^{O(L^{51/26}(1+\log L))}.
$$
The bound is uniform in $M$, including $2^e$ with variable $e$. Inserting the earlier [tuned class-two bound](https://github.com/Dugongue/MathProofs/blob/main/GrochowProofTransfersIII/CLASS-TWO-GROUP-ISOMORPHISM.md) gives $2^{O(L^{39/20}(1+\log L)^{1/10})}$ under the assumptions of that written algorithm. The reduction concerns all explicit free tensors, so the parameter here is the sum of the three mode lengths times the bit length of the modulus, with no nondegeneracy assumption. Specialized fixed-field or odd-modulus algorithms can have smaller exponents.

The constructions and comparison above have written proofs. The Lean companion checks the scalar coefficient and unit-intersection identities, and the finite replay checks rank bands and cyclic powers over both fields and nonfields. Publication priority remains open.
