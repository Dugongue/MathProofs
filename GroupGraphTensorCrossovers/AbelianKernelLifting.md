# Polynomial lifting through arbitrary abelian kernels

Let $G,H$ be finite groups given by their Cayley tables. Let $A\unlhd G$ and $A'\unlhd H$ be supplied abelian normal subgroups, and let $\alpha:G/A\to H/A'$ be a supplied quotient isomorphism.

**Theorem.** There is a deterministic polynomial-time algorithm that decides whether $\alpha$ lifts to an isomorphism $G\to H$ carrying $A$ to $A'$. If it does, the algorithm returns such an isomorphism, generators for the group of automorphisms of $G$ inducing the identity on $G/A$, and the exact number of lifts. The runtime is polynomial in the explicit Cayley-table size for arbitrary finite abelian kernels and arbitrary quotient groups.

This removes the generator bound in the question following Corollary 1.5 of Skresanov's paper, including the coset output in its Theorem 1.1. It also answers the first request in Grochow and Qiao's Open Problem 8.1, extending their Theorem 6.11 from elementary abelian to arbitrary abelian solvable radicals. The ultimate polynomial-time question for groups with arbitrary abelian solvable radical and no restriction on the quotient remains open here. The proof below uses their cohomological formulation, the finite module isomorphism algorithm of Ciocănea-Teodorescu, and Skresanov's finite-ring algorithms. [Skresanov, arXiv v2, Introduction](https://arxiv.org/html/2602.15497v2#S1) · [Grochow–Qiao, Theorem 6.11 and Open Problem 8.1](https://arxiv.org/pdf/1309.1776#page=49) · [Ciocănea-Teodorescu, Theorem 1.1](https://arxiv.org/abs/1512.08365)

## Identifying the two extension modules

Reject unequal group orders, then identify the two quotient groups with $Q=G/A$ via $\alpha$. A section of a quotient map makes the corresponding multiplication take the form
$$
 (a,x)(b,y)=(a+\rho(x)b+f(x,y),xy),
$$
where $\rho$ is the conjugation action of $Q$ on the abelian kernel and $f$ is the normalized extension cocycle. The action is independent of the section because the kernel is abelian. All entries of the action and cocycle are obtained from the Cayley tables.

Write the abelian kernels in cyclic generator coordinates, with algorithms converting their explicit tables to these coordinates. Set $e=\operatorname{lcm}(\exp A,\exp A')$. The two actions make the kernels modules over the same ring $(\mathbb Z/e\mathbb Z)[Q]$. This ring can be encoded by its additive generators and known structure constants, with polynomial input length. Apply finite module isomorphism to find a compatible module isomorphism $\mu:A\to A'$, or reject if none exists. When both kernels are trivial the supplied $\alpha$ is already the unique lift. For the rest, use $\mu$ to express the target module and its cocycle in the source module $A$. Denote the two cocycles in these coordinates by $f,f'$, and let $c=[f]$ and $c'=[f']$ in $H^2(Q,A)$. [Skresanov, §2 and Proposition 2.1](https://arxiv.org/html/2602.15497v2#S2)

Let $R=\operatorname{End}_Q(A)$ with multiplication by composition. It acts on $H^2(Q,A)$ by applying an endomorphism to cocycle entries. A lift exists exactly when some $u\in R^\times$ sends $c$ to $c'$. Indeed, such a unit admits a $1$-cochain $v$ satisfying
$$
 u f-f'=\delta v,\qquad
 (\delta v)(x,y)=v(x)+\rho(x)v(y)-v(xy).
$$
The resulting lift sends $(a,x)$ to $(u(a)+v(x),x)$ in the common coordinates. Conversely any lift over $Q$ has this form by its restriction to $A$ and its images of the chosen section. The coordinate identifications for $H$ then apply $\mu$ on the kernel and $\alpha$ on the quotient.

## Constructing a unit from two homomorphisms

Compute the ring $R$ by imposing the linear equations $r\rho(x)=\rho(x)r$ on the additive group of endomorphisms of $A$. Solve the two systems
$$
 a f-f'=\delta v_a,\qquad b f'-f=\delta v_b,\qquad a,b\in R.
$$
These are systems of linear congruences in cyclic coordinates. If either has no solution, reject. If both have a solution, then $ac=c'$ and $bc'=c$. Set $d=1-ba$, so that $dc=0$ and $ba+d=1$.

The following construction makes the finite-ring stable-range-one step explicit. Compute the Jacobson radical $J$ of $R$ and an explicit decomposition of $R/J$ into matrix rings over finite fields. In a given block write $B,D$ for the images of $a,d$. The identity $ba+d=1$ implies $\ker B\cap\ker D=0$, by acting on a column vector in the joint kernel. Choose a complement $U$ to $\ker D$ in the column vector space. The restriction of $B$ to $\ker D$ is injective, so choose a complement $U'$ to $B(\ker D)$ of dimension $\dim U$. Fix an isomorphism $j:U\to U'$. Since $D$ is one-to-one on $U$, there is a well-defined linear map $T$ on $D(U)$ with
$$
  TDx=j(x)-Bx\quad(x\in U).
$$
Extend it linearly to the whole block. The matrix $B+TD$ is invertible. It acts as $B$ on $\ker D$ and as $j$ on $U$, with complementary images.

Construct such a matrix $T$ in each block and lift the resulting quotient-ring element to $t\in R$. Then
$$
 u=a+td
$$
has invertible image modulo $J$ and hence is a unit in $R$. Since $dc=0$, this unit satisfies $uc=ac=c'$. Solve the coboundary equation for $v$ and output the lift.

All ring operations are polynomial-time in the table model. The endomorphisms are specified by images of cyclic generators of $A$. Their additive group has order at most $|A|^{\log_2 |A|}$, and the same bound holds for $R$. Such additive groups, their subgroups, and their quotients are handled in cyclic coordinates and via integer linear systems. Ring structure constants are computed by composing endomorphism generators and expressing the results in these coordinates. Every prime dividing $|R|$ is at most $|A|$. The radical and the explicit matrix decomposition used above are the operations in Skresanov's proof of Theorem 1.6 and Lemma 4.2. They run in time polynomial in $\log |R|$ and the largest prime divisor of $|R|$, so their use here takes polynomial time in the input table size. The cochain equations have at most polynomially many cyclic coordinates because they range over $Q$ and $Q^2$. They are solved by integer linear systems with a slack variable for each congruence. [Skresanov, Proposition 2.2, Lemma 4.2, and proof of Theorem 1.6](https://arxiv.org/html/2602.15497v2)

## Generators for all lifts and their exact count

For the source extension define the subring
$$
 R_c=\{r\in R:r c\in\mathbb Zc\}.
$$
It contains $1$ and is closed under multiplication because the endomorphisms commute with integer scalar multiplication. Its additive generators are computed by projecting the solution group of
$$
 r f-k f=\delta v
$$
to the $r$ coordinates. Here $k$ ranges modulo the additive order $m$ of $c$, which divides $\exp A$. Compute $m$ by testing positive integers up to $\exp A$ for the condition that $m f$ is a coboundary. The case $c=0$ has $m=1$.

A unit of $R$ that carries $c$ into its additive cyclic group maps that group bijectively to itself, so its inverse also belongs to $R_c$. Thus $R_c^\times$ is exactly the subgroup of $R^\times$ preserving $\mathbb Zc$. Compute its generators by Skresanov's Theorem 1.6. The homomorphism
$$
 R_c^\times\ \longrightarrow\ (\mathbb Z/m\mathbb Z)^\times,\qquad
 r\longmapsto k\ \text{where } r c=k c
$$
has kernel the stabilizer of $c$. For $m=1$ take the target to be trivial. For every generator the scalar is found by testing $k$ through the same coboundary equations. The image has at most $m\le |A|$ elements, so enumerating its orbit of the identity and using Schreier generators computes generators of the kernel in polynomial time. This yields the coefficient units that can lift to automorphisms of the extension over the quotient identity.

Lift every resulting coefficient generator by its coboundary equation. Adjoin translation automorphisms from additive generators of the solution group $Z^1(Q,A)$ of the equation $\delta v=0$. These generate all automorphisms of $G$ over the quotient identity. Indeed the latter group maps onto the coefficient stabilizer, and the translation group is exactly the kernel of that map. The resulting permutations on the original group elements represent the group faithfully. Compute its order by permutation stabilizer chains. Composing a particular lift with this automorphism group gives exactly the coset of all lifts and the requested count. [Skresanov, Theorem 1.6 and Corollary 4.3](https://arxiv.org/html/2602.15497v2#S4)

## Consequence for groups with abelian solvable radical

There is a deterministic polynomial-time decision, search, counting, and automorphism-generator algorithm for Cayley-table groups of order $s$ with abelian solvable radical whose quotient by that radical has $O(\log s/\log\log s)$ minimal normal subgroups, with the constant in the promise fixed. This is the application stated with the open question in Skresanov's paper.

The solvable radical can be found by taking the subgroup generated by the table elements with solvable normal closure. It is characteristic, and the quotient has no nontrivial solvable normal subgroup. In particular the quotient has no abelian normal subgroup. Use the enumeration algorithm of Babai, Codenotti, Grochow, and Qiao to list all isomorphisms between the quotient groups in polynomial time. Their bound holds for the displayed number of minimal normal subgroups expressed using $s$, the order of the full input groups, since their running time is bounded by a polynomial in the quotient order times a factorial in the number of minimal normal subgroups. Apply the theorem to each candidate and sum the numbers of lifts over the disjoint quotient maps. The witnesses and automorphism kernel generators similarly assemble the full automorphism group by processing a group against itself. The unrestricted enumeration bound in the same work gives $s^{c\log_2\log_2 s+O(1)}$ time for decision, search, counting, and the full coset with arbitrary abelian solvable radical, with $c=1/\log_2 60$. More generally the per-map procedure gives the extension of the enumeration-based Theorem 6.11 with a polynomial factor multiplying the time to list quotient isomorphisms. [Babai–Codenotti–Grochow–Qiao, §4](https://people.cs.uchicago.edu/~laci/papers/soda11.pdf) · [Grochow–Qiao, Theorems 5.5–5.6 and 6.11](https://arxiv.org/pdf/1309.1776)

This is an informal proof in the explicit Cayley-table model.
