# Epimorphism testing onto fixed dihedral groups

**GP-0349.** Given an arbitrary finite group presentation, deciding whether its group surjects onto the dihedral group of order eight is NP-complete. More generally, for every fixed finite nonabelian dihedral group the epimorphism problem from finite presentations is NP-complete. For the abelian dihedral groups it is polynomial-time decidable. The order-eight result answers Open Question 4.1 of Elder, Shen and Weiß. [Problem statement](https://arxiv.org/html/2610.39487v1#S4)

## 1. Boolean quadratic feasibility

It is NP-complete to decide whether a system of equations of degree at most two over $\mathbb F_2$ has a solution. For hardness, encode a Boolean circuit for a 3-CNF formula by one variable for each input and each gate output. The gate equations are $z=xy$ for AND and $z=1+x$ for NOT. These gates suffice, and the circuit output is constrained to equal $1$. A satisfying assignment of the circuit inputs extends uniquely to gate values, and each quadratic-system solution has the required gate values. This construction has polynomial size.

Introduce a formal extra variable $x_0$. In each input equation replace $1$ by $x_0^2$, replace $x_i$ by $x_0x_i$, and leave $x_ix_j$ as it stands. The resulting homogeneous quadratic equations recover the original system when $x_0=1$. Write each equation as a list of pairs $(i,j)$, one for each monomial with coefficient $1$. Coefficients are understood modulo $2$.

## 2. The presentation

Let $D_8=\langle r,s\mid r^4=s^2=1,\ srs=r^{-1}\rangle$; its central involution is $z=r^2$. Its central quotient is $\mathbb F_2^2$, and commutation defines the nondegenerate alternating form on that quotient with values in $\langle z\rangle$ identified with $\mathbb F_2$. In a basis of reflection cosets it is the determinant. This follows from class two and from $[s,sr]=r^2$, using the convention $[u,v]=uvu^{-1}v^{-1}$.

Give the source presentation $2(n+1)$ generators $a_0,\ldots,a_n,b_0,\ldots,b_n$. Require every generator to square to the identity, and require all pairs of $a$ generators to commute and all pairs of $b$ generators to commute. Write the word $c_{ij}=[a_i,b_j]$. Add the relations
$$
c_{ij}c_{ji}=1 \quad(0\le i<j\le n),\qquad
c_{ii}c_{0i}=1 \quad(1\le i\le n).
$$
For each input list of monomial pairs add one relator, the product of its $c_{ij}$ words, in any fixed order. The interpretation as a bit product holds in the target, where every commutator is central of order dividing two. The source presentation need not describe a finite group. The reduction has quadratic overhead in the number of variables in addition to the total equation length.

## 3. Soundness and completeness

Given an epimorphism to $D_8$, let $U$ and $V$ be the spans of the images in the central quotient of the $a$ generators and $b$ generators respectively. Each is totally isotropic, because the corresponding generators commute. Nondegeneracy in dimension two means each has dimension at most one. The total images generate the central quotient by surjectivity, so both $U,V$ are one-dimensional and they are distinct. Choose nonzero vectors $u\in U$, $v\in V$. Their alternating pairing is $1$. Write the images of $a_i$ and $b_j$ as $x_i u$ and $y_j v$. Then each $c_{ij}$ maps to $z^{x_i y_j}$.

The matrix $X=(x_i y_j)$ is nonzero, has rank one, and is symmetric by the first additional family of relators. Consequently $x=y$. To see this without a rank factorization convention, choose $i,j$ with $x_i y_j=1$. Symmetry gives $x_j y_i=1$, so $x_i=y_i=1$. Now $X_{ki}=X_{ik}$ implies $x_k=y_k$ for every $k$. The second family of relators gives $x_i^2=x_0x_i$ for $i\ge1$. If $x_0=0$ then all $x_i$ with $i\ge1$ vanish, contradicting the nonzero matrix. Thus $x_0=1$. The equation relators now say precisely that the original Boolean quadratic system holds.

Conversely, given a solution of the quadratic system, set $x_0=1$ and send $a_i$ to $s^{x_i}$ and $b_i$ to $(sr)^{x_i}$. Each half commutes and every image is an involution or the identity. Cross-commutators are exactly $z^{x_i x_j}$, so all relators hold. The images of $a_0,b_0$ generate $D_8$ because the product of $s$ and $sr$ is $r$. This proves equivalence. Membership in NP follows by guessing one target element for each source generator, evaluating its relators, and checking generation in the fixed target.

## 4. All fixed finite dihedral targets

Write $D_{2^k}$ for the dihedral group of order $2^k$, with $k\ge3$ and rotation generator $r$ of order $2^{k-1}$. Use the same construction, except that in each of the symmetry, normalization, and equation relations replace an occurrence of $c_{ij}$ by $c_{ij}^{\,2^{k-3}}$. Leave involution and within-half commutation relations untouched. The extra word-length factor is constant for a fixed target.

Under any target assignment a cross-commutator has the form $r^{2\ell}$, since the quotient by $\langle r^2\rangle$ is abelian. Its power $2^{k-3}$ equals the central involution $r^{2^{k-2}}$ raised to the bit $\ell\bmod2$. Reducing rotations mod $4$ gives a quotient map $D_{2^k}\to D_8$. The bit $\ell\bmod2$ is precisely the commutator bit in that quotient. Therefore a surjection to $D_{2^k}$ produces the same Boolean solution by applying the order-eight argument to the quotient images and the transmitted bits. Conversely the same two generating reflections $s,sr$ in $D_{2^k}$ realize a valid lift of any Boolean solution. Their commutator is $r^2$ or $r^{-2}$ according to convention, and either has the required central involution as its $2^{k-3}$-th power. The images again generate.

Elder, Shen and Weiß prove NP-completeness for the remaining nonabelian dihedral groups, whose orders have an odd factor. Abelian targets are handled by computing the finitely generated abelianization by Smith normal form and testing whether it has the fixed target as a quotient. This gives the stated classification. [Elder–Shen–Weiß, Section 4](https://arxiv.org/html/2610.39487v1#S4)

The rank-one test uses the alternating central commutator data already central to the [class-two group–tensor correspondence](https://github.com/Dugongue/MathProofs/blob/b0947ecc8675432a7292628b99e945b7d50b216e/FourIsomorphismResults/GroupTensorEquivalence.md). Its role here is to encode feasibility and ensure that surjectivity removes the spurious homogeneous zero assignment.
