# Sharp growth of the ordinary tensor genus with abelian splitting field

Let $F$ be a number field. A tensor of side $n$ is geometrically diagonal if, over an algebraic closure, it is equivalent to the multiplication tensor of the split algebra $F^n$. Equivalence here uses three independent invertible linear maps. Its ordinary local genus consists of global tensor equivalence classes whose tensors are equivalent to it over every completion of $F$.

**Theorem.** Let $M_F(n)$ be the largest size of an ordinary local genus of side $n$ represented by the multiplication tensor of a degree-$n$ étale $F$-algebra with abelian splitting field. Then
$$
\log M_F(n)=\tfrac14 n\log n+O(n),
$$
with absolute constants in the error. For every $n\ge4$ there is a genus attaining the lower bound up to the stated error. All varying field factors in that construction are biquadratic over $F$, all representatives split over a common multiquadratic extension of $F$ of degree less than $4n$, and every decomposition group of that extension is cyclic. The genus bound and construction are unconditional. Under Dirichlet GRH, the rational examples can have absolute discriminants $\exp(O(n\log^2 n))$.

## Tensor and character reductions

Write a tensor as a bilinear map $T\colon V_1\times V_2\to V_3$. In diagonal coordinates over an algebraic closure its left and right slices have nonzero determinant polynomials. Since $F$ is infinite, choose $x_0\in V_1$ and $y_0\in V_2$ over $F$ such that $P(x)=T(x,y_0)$ and $Q(y)=T(x_0,y)$ are invertible. On $V_3$ set $u*v=T(P^{-1}u,Q^{-1}v)$. In diagonal coordinates this is coordinatewise multiplication divided by the nonzero coordinatewise product $x_0y_0$. Thus it descends as a unital finite étale algebra over $F$, and $T$ is equivalent to its multiplication tensor. A tensor equivalent to a geometrically diagonal tensor over even one completion is geometrically diagonal, by solvability of the transporter equations over an algebraically closed extension and the Nullstellensatz. Thus all representatives of the local genus are covered by this algebra model.

If $A$ and $B$ are unital commutative algebras and $R(xy)=P(x)Q(y)$ is a tensor isomorphism, put $a=P(1)$, $b=Q(1)$. Multiplication by $a$ and by $b$ is bijective, since $R(x)=aQ(x)=P(x)b$, so $a,b$ are units. The map $x\mapsto (ab)^{-1}R(x)$ is an algebra isomorphism. The converse takes the same algebra isomorphism in all three slots.

For an étale algebra $A$, its set of embeddings into a separable closure is a finite Galois set of size $\dim_F A$, with one orbit per field-factor occurrence. Let $\chi_A$ be its permutation character. After passing to a common Galois splitting extension of two algebras, local isomorphism at unramified places implies equality of their characters on each Frobenius conjugacy class. Chebotarev gives equality on the entire Galois group. The kernel of each embedding action is the locus where its character has value $n$. Its fixed field is the minimal Galois splitting field. Thus any algebra locally equivalent to $A$ has the very same splitting field as $A$, in a common separable closure. In particular all representatives in the genus of an abelian-split algebra are abelian-split. [Finite étale algebras and permutation representations](https://people.math.harvard.edu/~mmwood/Publications/ArithStats.pdf)

If every decomposition group in a common splitting field is cyclic, equality of the global permutation characters conversely implies local isomorphism at every place. On a cyclic group $D=\langle g\rangle$, the fixed counts at all powers $g^j$ determine the multiplicities of each cycle length by divisor inversion. Hence equal restricted characters give isomorphic $D$-sets. These sets are the restrictions that classify the completed étale algebras.

## Upper bound for the full genus

Fix the common abelian splitting field with Galois group $G$, and the common character $\chi$. In the character group $\widehat G$ let $S$ be the set of characters occurring in $\chi$. Then $|S|\le n$. An orbit $G/H$ of size $d$ affords the sum of the characters of the annihilator $H^\perp$, each once. This is the character decomposition of the regular representation of $G/H$. Thus the annihilator is a subgroup of $\widehat G$ contained in $S$, and it specifies the orbit uniquely. There is no cancellation since all multiplicities are nonnegative.

A subgroup of order $d\ge2$ has a generating tuple of length at most $r_d=\lfloor\log_2 d\rfloor$, by adjoining one generator at a time and doubling the current subgroup order. Pad with the trivial character to length $r_d$. Thus there are at most $n^{r_d}$ possible orbit types of size $d$. For a component profile with $c_d$ factors of size $d$, the possibilities at that size are unordered multisets. If $c_d>0$, their number is at most
$$
\binom{n^{r_d}+c_d-1}{c_d}
 \le \left(\frac{2e\,n^{r_d}}{c_d}\right)^{c_d}.
$$
The size-one orbit has only one type. Summing the logarithms for $d\ge2$ gives the leading term $\sum_d c_d(r_d-1)\log n$ and error at most $\sum_d c_d\log(n/c_d)+O(n)$.

For every $d\ge2$, $r_d-1\le 2^{r_d}/4\le d/4$. Since $\sum_d d c_d=n$, the leading term is at most $(n/4)\log n$. To bound the residual uniformly, for each positive $c_d$ use
$$
c_d\log(n/c_d)
 =2c_d\log d+c_d\log\bigl(n/(d^2c_d)\bigr)
 \le \frac{2\log d}{d}\,d c_d+\frac{n}{e d^2}.
$$
The last inequality maximizes $x\log(a/x)$ at $x=a/e$. Both terms are summable with total $O(n)$, using $\sum_d dc_d=n$ and $\sum_{d\ge2}d^{-2}<\infty$. Finally there are at most $2^{n-1}$ profiles because each integer partition is one particular composition of $n$. This proves the claimed upper bound, including the case of arbitrarily large common splitting field.

## Lower bound from complete mappings

Put $m=\lfloor n/4\rfloor$, and take $U=\mathbb F_4^s$ with $4^s$ the least power of four at least $m$. Choose disjoint affine $\mathbb F_4$-subspaces $C_i=u_i+U_i\subseteq U$ whose sizes $M_i$ sum to $m$ and are its base-four summands, each power occurring at most three times. For example, build a radix-four tree by fixing coordinates in order. The first $m$ leaves are a disjoint union of full rooted subtrees corresponding to the base-four digits. Each such subtree is an affine subspace of the desired size.

Use the binary vector space $V=U\oplus\mathbb F_2^2$ as a character group and name the two basis vectors in its second factor $a,b$. Fix $\lambda\in\mathbb F_4\setminus\{0,1\}$. For each $i$, let $f_i$ be a complete mapping of the additive group of $U_i$, meaning that $f_i$ and $z\mapsto z+f_i(z)$ are permutations. For every $z\in U_i$ take the two-dimensional binary subspace with nonzero points
$$
a+u_i+z,\qquad b+\lambda u_i+f_i(z),\qquad
a+b+(1+\lambda)u_i+z+f_i(z).
$$
The third point is the sum of the first two, which are independent by their distinct nonzero tag coordinates. Within each tag layer, these subspaces cover each point of $C_i$, $\lambda C_i$, or $(1+\lambda)C_i$ once. This follows from the two permutation conditions and from the fact that $U_i$ is linear over $\mathbb F_4$. The layer supports are disjoint across $i$. Therefore the multiset of nonzero characters in the subspaces is independent of all the $f_i$. The subspaces determine the $f_i$ because the first point determines $i,z$, and its partner in the second tag layer determines $f_i(z)$.

Let $G$ be dual to $V$. Replace every subspace $W$ by the orbit $G/W^\perp$ of size four, and add $n-4m$ fixed points. The resulting $G$-sets all have the same character, including the trivial character multiplicity, and no two choices give isomorphic $G$-sets. The Hall–Paige asymptotic of Eberhard, Manners and Mrazović gives $\exp(M\log M-O(M))$ complete mappings for an additive $\mathbb F_4$-space of size $M$. The Hall–Paige condition holds when $M>1$ since the binary dimension is at least two. The uniform lower inequality for small $M$, including $M=1$, follows by enlarging the absolute constant, since multiplication by $\lambda$ gives a complete mapping. Summing over $i$ gives
$$
\log(\text{number of choices})\ge\sum_i M_i\log M_i-O(m)=m\log m-O(m).
$$
For the equality up to $O(m)$, write $4^\ell\le m<4^{\ell+1}$. Then
$\sum_i M_i\log(m/M_i)\le 3\cdot4^\ell\log(4)\sum_{j\ge0}4^{-j}(j+1)=O(m)$.
Since $m=\lfloor n/4\rfloor$, the result is $(n/4)\log n-O(n)$. [Eberhard, Manners and Mrazović, Theorem 1.2](https://arxiv.org/abs/2003.01798)

## Realizing the local genus

Choose distinct rational primes $p_1,\ldots,p_{\dim_{\mathbb F_2} V}$ outside the ramification set of $F$, all $1\bmod 8$, with every pair quadratic residues modulo one another. Recursively choose a prime $1\bmod 8\prod_{j<i}p_j$ by Dirichlet's theorem and then apply quadratic reciprocity. The squareclasses of these primes are independent. The multiquadratic field $L=\mathbb Q(\sqrt{p_1},\ldots,\sqrt{p_{\dim V}})$ has Galois group isomorphic to $G$. Its decomposition group at $p_i$ has order two because the other radicands are squares over $\mathbb Q_{p_i}$. At 2 and at infinity the field splits. All other decomposition groups are cyclic by unramifiedness. Also $F\cap L=\mathbb Q$, since any nontrivial subfield of the multiquadratic $L$ contains a quadratic subfield, and every such quadratic subfield ramifies at a chosen prime. Thus $K=FL$ has Galois group $G$ over $F$, and its local decomposition groups inject into those of $L/\mathbb Q$. Its degree is $4|U|<16m\le4n$.

The étale algebras corresponding to the constructed orbits are products of the fixed fields $K^{W^\perp}$ and the stated copies of $F$. Each varying factor has Galois group $(C_2)^2$ over $F$. Equal characters now give actual local algebra isomorphisms at every place, including ramified ones. No two global algebras or multiplication tensors are equivalent. Over $\mathbb Q$, taking products of their maximal orders also gives globally distinct integral multiplication tensors that are equivalent over each $\mathbb Z_p$. Indeed a local field-algebra isomorphism preserves the integral closure of $\mathbb Z_p$.

## Discriminant bound under Dirichlet GRH

For the rational construction only, let $Q_i=8\prod_{j<i}p_j$ and consider the compositum of $\mathbb Q(\zeta_8)$ with the earlier quadratic fields. Its Galois group has size $h_i\le 2^{i+1}$ and all its characters have primitive conductors dividing $Q_i$. Complete splitting is exactly the average of these characters at good primes. Under Dirichlet GRH, the smoothed prime sum for each primitive character of conductor dividing $Q_i$, with a fixed nonnegative smooth weight $w(p/x)$ of positive integral $I$ supported in $(1/2,1)$, is $Ix$ for the principal character and zero for the other main terms, with error $O_w(\sqrt x\log(2Q_i)+\log(2Q_i))$. The explicit formula bounds zero terms by $\sqrt x$ times the conductor logarithm using Mellin decay and the standard zero count in unit intervals. Removing higher prime powers costs $O_w(\sqrt x)$ and removing the primes dividing $Q_i$ costs $O_w(\log(2Q_i))$. Averaging yields main term $Ix/h_i$ with the same error. Taking $x=C h_i^2\log^2(2Q_i)$ for an absolute sufficiently large $C$ proves that a good splitting prime $p_i\le x$ exists. Such a prime meets the quadratic residue conditions, is $1\bmod8$, and is distinct from the earlier primes.

Consequently
$$
\log p_i\le O(i)+2\log\bigl(\log16+\textstyle\sum_{j<i}\log p_j\bigr).
$$
Induction gives $\log p_i=O(i)$, since the sum is $O(i^2)$ under the inductive bound and the additional logarithm is $O(\log(i+1))$. There are $O(\log n)$ primes, so the logarithm of their conductor product is $O(\log^2 n)$. Each biquadratic factor has three nontrivial quadratic characters of conductor dividing this common conductor. By the conductor-discriminant formula the logarithmic discriminant of each factor is $O(\log^2 n)$. There are $m$ such factors, proving the bound. This reasoning uses Dirichlet GRH only for abelian extensions of $\mathbb Q$. [Bach and Sorenson, explicit GRH prime estimates](https://doi.org/10.1090/S0025-5718-96-00763-6)

## Scope and comparison

This quantifies the problem of forms highlighted in Grochow and Qiao's field-change question, by counting all global classes with common completions on the abelian-split geometrically diagonal locus. It gives no assertion on reductions between unrestricted tensor isomorphism problems over different fields. The closest project precedent characterized the first failure at side six. The growth law above determines an asymptotic for the entire abelian-split locus, and the matching lower bound uses complete mappings rather than repetitions of a fixed small counterexample. The proof is informal. Literature priority for the growth law has not been established. [Grochow–Qiao, Open Question 10.6, arXiv version 1](https://arxiv.org/html/1907.00309v1#S10.SS2) · [Previous side-six theorem](https://github.com/Dugongue/MathProofs/blob/main/DickeAndIsomorphismMethods/GEOMETRY.md)
