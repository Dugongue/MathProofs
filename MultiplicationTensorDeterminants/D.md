# Tensor Isomorphism reduces to determinant-one correction

For every fixed odd finite field $k=\mathbb F_q$, ordinary Tensor Isomorphism reduces in polynomial time to testing determinant-one equivalence of unital associative multiplication tensors. The reduction supplies an explicit ordinary transporter, even an algebra isomorphism, for every output pair. For the unrestricted determinant-one problem, a second construction gives a field-independent dimension bound and works uniformly over finite fields.

Let $A$ be a finite-dimensional nonzero unital associative $k$-algebra and $s\ge2$. Set $B=M_s(A)$ and use the triangular algebra
$$
 C_s(A)=\begin{pmatrix} k & B \\ 0 & B \end{pmatrix},
 \qquad
 (a,w,b)(a',w',b')=(aa',aw'+wb',bb').
$$
The off-diagonal copy of $B$ is its regular right module, with scalars acting on the left. This gives center $k$ and dimension $1+2s^2\dim_k A$. Every automorphism has determinant in $(k^\times)^s$. Also, $C_s(A)\cong C_s(A')$ if and only if $A\cong A'$.

## Matrix amplification and cancellation

Write $M_s(A)=\operatorname{End}_A(A^s)$ using the free right module. The images of the standard matrix units under an automorphism give a new full set of matrix units. Their diagonal idempotents split $A^s$ into $s$ summands and the off-diagonal units give inverse isomorphisms between each pair of summands. If one summand is $P$, this gives $P^s\cong A^s$. Krull–Schmidt for finite-length right $A$-modules gives $P\cong A$, by cancelling the factor $s$ in the multiplicity of every indecomposable. An isomorphism from $A$ to the first summand, transported by the new matrix units, gives a basis change carrying the standard units to the new ones. After undoing that inner conjugation, the automorphism fixes the standard matrix units. It then acts entrywise by its restriction to the first corner, which is an automorphism of $A$. The same reasoning for an isomorphism $M_s(A)\to M_s(A')$, using the target free $A'$-module, identifies the transported first corner with $A'$. Thus $M_s(A)\cong M_s(A')$ implies $A\cong A'$.

On $B$, left multiplication by any unit acts by the same linear map on each of the $s$ column spaces. Right multiplication does the same on the row spaces. Both determinants are $s$-th powers. An inner automorphism is the product of one left and one right multiplication. An entrywise automorphism repeats the action on $A$ in $s^2$ entries, so its determinant is an $s^2$-th power. All determinants of automorphisms of $B$ are therefore $s$-th powers.

## The odd-dimensional triangular algebra

The radical of $C_s(A)$ consists of $(0,w,b)$ with $b\in J(B)$. This ideal is nilpotent and its quotient is $k\times B/J(B)$. Every simple block of $B/J(B)\cong M_s(A/J(A))$ has matrix size at least $s$, so the first $k$-factor is the unique simple quotient block of dimension one. The idempotent $e=(1,0,0)$ maps to its identity. An automorphism sends $e$ to an idempotent $f$ congruent to $e$ modulo the radical. The element $u=fe+(1-f)(1-e)$ is congruent to 1 modulo the radical and satisfies $ue=fu$, so $f=ueu^{-1}$. Conjugation by $u$ has determinant 1, since left and right multiplication by elements of $1+J$ are unipotent. The same argument aligns the marked idempotents under any isomorphism between two such algebras and recovers the bottom corner $B$.

An automorphism fixing $e$ also fixes $1-e$. Hence it preserves the three summands and acts on the bottom corner by some $\sigma\in\operatorname{Aut}_k(B)$. Its off-diagonal action $F$ satisfies $F(xb)=F(x)\sigma(b)$, so $F(x)=F(1)\sigma(x)$. Bijectivity makes $F(1)$ a unit. The total determinant is $(\det\sigma)^2\det L_{F(1)}$, an $s$-th power. For the center, commuting with $e$ first makes a central element diagonal. Commuting with the off-diagonal element $w=1$ forces the bottom entry to be the top scalar times $1_B$. Thus the center is $k$. The dimension formula follows from the three summands, and the isomorphism criterion follows from recovery of the bottom corner and matrix cancellation.

## Reduction with an ordinary transporter

For odd $q$, take $s=2^{v_2(q-1)}$. In $k^\times$, the scalar $-1$ is outside the subgroup of $s$-th powers. Given $A,A'$, take $E=C_s(A)\times C_s(A')$. The centers of its two factors are $k$, so any automorphism either preserves the two factors or exchanges them. A factor-preserving automorphism has determinant in $(k^\times)^s$. An exchange exists precisely when $A\cong A'$. Use the factor isomorphism one way and its inverse the other way. This exchanges two odd-dimensional summands in pairs and has determinant $-1$. Thus $E$ has an automorphism of determinant $-1$ exactly when $A\cong A'$.

Choose a diagonal linear map $P$ of determinant $-1$ on $E$. Output its multiplication $\mu$ and the transported multiplication $\mu'(x,y)=P\mu(P^{-1}x,P^{-1}y)$, together with $P$. The isomorphisms between these presented algebras are $P\sigma$ for $\sigma\in\operatorname{Aut}_k(E)$. One has determinant 1 exactly when $A\cong A'$. The determinant ratio for unital associative multiplication turns this into the same criterion for three independent determinant-one tensor maps. The tensor side length is $2+2s^2(\dim A+\dim A')$, giving polynomial time for fixed $q$. Composing with Grochow and Qiao's reduction to unital associative algebra isomorphism gives the Tensor Isomorphism claim. [Grochow and Qiao, Corollary 8.5(1)](https://arxiv.org/html/1907.00309#S8)

One can instead choose $s=q-1$ for an exact orbit-count formulation. Every automorphism of a single triangular factor then has determinant 1. Left multiplication by $(a,0,1_B)$ has determinant $a^{1+\dim_k B}=a$, and right multiplication by it has determinant $a$. These units realize the two full determinant images on the factor and on the product $E$. The ordinary multiplication orbit of $E$ therefore splits into $q-1$ determinant-one orbits when $A\not\cong A'$ and $(q-1)/2$ when $A\cong A'$. In particular exact orbit splitting on these multiplication tensors is Tensor Isomorphism hard. [The determinant ratio and orbit-count argument](B.md)

## Uniform reduction by using the dual module

For the unrestricted problem, there is a construction of side length $1+8\dim_k A$ that works over any field. Let $B=M_2(A)$ and replace the off-diagonal copy of $B$ in the triangular algebra by the dual $B^*=\operatorname{Hom}_k(B,k)$. Give it the right $B$-action $(f\cdot b)(x)=f(bx)$. Call the resulting algebra $C^*(A)$. Its radical has the whole off-diagonal module and $J(B)$ in the bottom corner. The argument that recognizes the unique one-dimensional quotient block and aligns its idempotent still applies. Consequently an algebra isomorphism $C^*(A)\cong C^*(A')$ gives $M_2(A)\cong M_2(A')$ and hence $A\cong A'$.

Conversely, an isomorphism $A\to A'$ induces an entrywise isomorphism $\beta:B\to B'$. The map
$$
(a,f,b)\longmapsto (a,f\circ\beta^{-1},\beta(b))
$$
is an algebra isomorphism because the contragredient map intertwines the right module actions. In the corresponding bases, using the dual basis in the off-diagonal slot, its determinant is $1\cdot(\det\beta)^{-1}\cdot\det\beta=1$. It gives a determinant-one transporter on all three tensor legs. Conversely, such a tensor transporter gives an algebra isomorphism by the determinant-ratio normal form. The construction of the structure constants uses matrix units and duality and has cost polynomial in the input size, independently of $q$. Composing with the reduction to unital associative algebras proves $\mathrm{TI}\le_m^p\mathrm{TI}_{\mathrm{SL}}$ uniformly over finite fields, including when the prime is part of the input. This proves the hardness direction asked in the two papers below. [Grochow, Qiao and Tang, Open Question 9](https://drops.dagstuhl.de/storage/00lipics/lipics-vol287-itcs2024/LIPIcs.ITCS.2024.31/LIPIcs.ITCS.2024.31.pdf) · [Connecting Homogeneous Multilinear Equations to Hyperdeterminants, Question 9](https://drops.dagstuhl.de/storage/00lipics/lipics-vol325-itcs2025/LIPIcs.ITCS.2025.62/LIPIcs.ITCS.2025.62.pdf)

The reductions have written proofs. The Lean companion checks the repeated-block determinant and odd-component exchange as separate components. Bibliographic priority for these reductions remains open.

## A three-layer path algebra version

Over every fixed odd finite field $\mathbb F_q$, Graph Isomorphism reduces to determining whether two multiplication tensors of finite-dimensional unital associative algebras admit a determinant-one transporter on all three legs. The reduction supplies an ordinary algebra isomorphism, hence an ordinary tensor transporter, with its output. The algebras are two coordinate presentations of a path algebra whose quiver has three layers and no path of length greater than two. Over $\mathbb F_3$, for two nonempty input graphs with $n_G,n_H$ vertices and $m_G,m_H$ edges, the tensor side length is $22(n_G+n_H)+8(m_G+m_H)+2$.

A second result computes the number of determinant-one orbits in the ordinary orbit of any finite acyclic path algebra. It gives a sharp dimension bound for prime divisors of that number.

## Determinants for an acyclic path algebra

Use the convention that a path product follows the left factor by the right factor. Let $A=KQ$ for a nonempty finite acyclic quiver $Q$, with parallel arrows allowed. Write $L_v$ and $R_v$ for the numbers of paths starting and ending at $v$, including its trivial path. For every ordered vertex pair $u,v$ with at least one arrow from $u$ to $v$, put $e_{uv}=R_uL_v$. Let $g$ be the gcd of the $e_{uv}$, with empty gcd 0.

The ideal $J$ of positive-length paths is nilpotent and the quotient $A/J$ is a product of copies of $K$. It follows that $J$ is the Jacobson radical. The powers $J^i$ are spanned by paths of length at least $i$. A unit of $A$ has nonzero vertex coordinates $a_v$ modulo $J$. On the associated graded space, left multiplication scales each path starting at $v$ by $a_v$, and right multiplication scales each path ending at $v$ by $a_v$. A determinant equals the product of its induced determinants on the quotients of a stable filtration. The two determinants are therefore $\prod_v a_v^{L_v}$ and $\prod_v a_v^{R_v}$. A sink has $L_v=1$ and a source has $R_v=1$, so each determinant image is all of $K^\times$.

An algebra automorphism preserves $J$ and acts on $A/J$ by a vertex permutation. Its action on $J/J^2$ sends the arrow space from $u$ to $v$ to the corresponding space between the permuted vertices. Thus the vertex permutation preserves arrow multiplicities. Label parallel arrows once, and lift any such vertex permutation by keeping the labels. Its determinant is the sign of the resulting permutation of all paths. After composing with the inverse lift, the action on $J/J^2$ is an arbitrary family of invertible linear maps on the arrow spaces. The entire action on the associated graded algebra is determined by these vertex and arrow actions, because every path is a product of arrows.

Consider a vertex-fixed change in one arrow space. Invertible maps there are generated by individual arrow rescalings and elementary transvections. A given arrow occurs at most once in a path, and paths containing it correspond bijectively to a prefix ending at $u$ and a suffix starting at $v$. Hence rescaling that arrow by $\lambda$ contributes $\lambda^{R_uL_v}$ to the determinant on all paths. A transvection replaces that arrow by itself plus a multiple of a distinct parallel arrow. Order the paths containing the replaced arrow after all other paths. The resulting action is triangular with diagonal 1, since substituting the parallel arrow removes the replaced arrow from the path. Any such linear change extends to a graded automorphism by the path product. This proves that the automorphism determinant image is generated by $(K^\times)^g$ and the signs of the path permutations coming from vertex relabelings.

Combining this with the determinant-ratio theorem gives the number of special-linear orbits in the ordinary multiplication orbit over $\mathbb F_q$. It is $\gcd(q-1,g)$ unless an odd path permutation occurs and $q$ is odd. In that case it is $\gcd((q-1)/2,g)$. Indeed the two unit determinant images are full, so only the automorphism determinant index remains. In the cyclic group of order $q-1$, adjoining the element $-1$ adds the exponent $(q-1)/2$ to the gcd.

## Encoding Graph Isomorphism in the sign of a path permutation

Given a nonempty simple graph $G$, make a source $s$ and two vertices $X_i,Y_i$ for each vertex $i$. All $X_i$ and $s$ are sources. All $Y_i$ are sinks. Introduce middle vertices as follows. Each middle vertex has one incoming arrow from the specified source and one outgoing arrow to the specified sink.

| Source and sink | Number of middle vertices |
|---|---:|
| $s,Y_i$ for each $i$ | 3 |
| $X_i,Y_i$ for each $i$ | 2 |
| $X_i,Y_j$ when $i$ and $j$ are adjacent | 1 |

Each edge is used in both orders in the last row. Denote the result by $Q(G)$. The quiver is connected as an undirected graph. The source $s$ is recoverable from the length-two path multiplicities, since it has a multiplicity-three connection and the other sources do not. The multiplicity-two connections between the remaining sources and the sinks recover the pairing $X_i,Y_i$. The multiplicity-one connections then recover adjacency. Consequently $Q(G)\cong Q(H)$ holds exactly when $G\cong H$. One can adjoin an isolated vertex to both input graphs to ensure nonemptiness, which preserves their isomorphism relation.

First take $q=3$. The path basis comprises $s$, the two endpoint banks, and four paths for each middle vertex. These four are the trivial path at the middle vertex, the incoming and outgoing arrows in order, and their composite. Any quiver automorphism acts by the same permutation on the two endpoint banks. It permutes the middle vertices and preserves the four positions within each block. Its sign on the path basis is therefore $+1$. Each arrow is in exactly two paths, so all $e_{uv}$ are 2. Over $\mathbb F_3$ the scalar generator determinants are all 1, and the preceding filtration proof shows that every algebra automorphism of $\mathbb F_3 Q(G)$ has determinant 1.

There are $5n+2m$ middle vertices. The odd path basis size is $2n+1+4(5n+2m)=22n+8m+1$. Now take the disjoint union $Q=Q(G)\sqcup Q(H)$. The determinant image of $\operatorname{Aut}(\mathbb F_3 Q)$ contains $-1$ exactly when an automorphism exchanges the connected components. Without an exchange, both component signs are even. With an exchange, choose an isomorphism of the quivers and its inverse in the opposite direction. The resulting permutation swaps two equal odd-size path bases in pairs and has sign $-1$. Hence the ordinary orbit splits into one determinant-one orbit if $G\cong H$ and two otherwise.

Finally let $P$ be the diagonal change of basis that negates one chosen basis coordinate and fixes the others. If $\mu$ is multiplication of $A=\mathbb F_3Q$, set
$$
\mu'(x,y)=P\mu(P^{-1}x,P^{-1}y).
$$
Both inputs are multiplication tensors of unital associative algebras. The map $P$ is an explicit ordinary algebra isomorphism between them. All algebra isomorphisms are $P\sigma$ with $\sigma\in\operatorname{Aut}(A)$, so one has determinant 1 precisely when an automorphism has determinant $-1$. The determinant-ratio theorem makes this equivalent to a three-leg determinant-one tensor transporter. Enumerating the basis paths, filling their concatenation table and negating the selected coordinate are polynomial-time operations. This proves the reduction.

## Every fixed odd finite field

Write $d=2^{v_2(q-1)}$. Replace each incoming and outgoing arrow at a middle vertex by $d-1$ parallel arrows. The support of the incidence pattern is unchanged. A length-two path count between a source and a sink is now the old count times $(d-1)^2$, so it recovers the same graph. Each middle contributes $1+2(d-1)+(d-1)^2=d^2$ paths. Each arrow belongs to exactly $d$ paths, since it can be followed or preceded by one of $d-1$ arrows. Every lifted vertex relabeling keeps the parallel labels, so the same permutation acts on both endpoint banks and the induced middle permutation acts on $d^2$ copies. This gives an even path permutation within each component and an odd number of paths per component.

Over $\mathbb F_q$, the determinant image on each component is therefore $(\mathbb F_q^\times)^d$. It excludes $-1$ because $(q-1)/2$ is indivisible by $d$. An exchange of isomorphic components still contributes $-1$. Thus the same explicit determinant $-1$ isomorphism can be corrected precisely when $G\cong H$. The ordinary orbit splits into $d$ special-linear orbits for nonisomorphic graphs and $d/2$ for isomorphic graphs. The path-basis size of a component is $2n+1+d^2(5n+2m)$. Since the field is fixed, the reduction remains polynomial-time.

## The sharp prime dimension bound

Assume $Q$ has at least one arrow. Suppose a prime $p$ divides the number of determinant-one orbits in the ordinary multiplication orbit. The formula above gives $p\mid e_{uv}$ for every arrow space. Choose a positive-length source-to-sink path. The start has $R=1$, and the vertex immediately before the sink has $p\mid R$ because the sink has $L=1$. At the first vertex $x$ along the route with $p\mid R_x$, its predecessor has $p\nmid R$. Divisibility along the entering edge gives $p\mid L_x$. Thus at least $p^2$ paths pass through $x$. The source and sink trivial paths are distinct and avoid $x$, so $\dim A\ge p^2+2$.

For a prime $p\mid q-1$, take three vertices in a chain with $p-1$ parallel arrows on both steps. Its dimension is $p^2+2$. The two arrow-space exponents are $p$, and its vertex relabeling group is trivial, so the orbit count is $p$. Equality in the lower bound forces exactly the two extra trivial paths, hence exactly three vertices and no direct source-to-sink arrow. Both middle path counts must be $p$, forcing the two indicated multiplicities. The same construction with $d-1$ arrows on each step realizes every divisor $d>1$ of $q-1$. A one-arrow quiver realizes $d=1$.

## Scope and prior work

The determinant profiles, complexity reduction and sharp bound above have written proofs. The Lean companion checks the coupled path sign, the sign of an odd-size component exchange and the divisibility transition used in the dimension bound. The finite control checks the incidence recovery, path exponents and signs directly, including parallel-arrow examples. The main result builds on the use of path algebras in tensor isomorphism and the classical description of actions on path generators. Priority for this promised-input reduction and exact determinant count is unestablished. [Lean components](D.lean) · [Finite control](DCheck.py) · [Grochow and Qiao](https://arxiv.org/abs/1907.00309) · [Le Meur](https://arxiv.org/abs/math/0503302)
