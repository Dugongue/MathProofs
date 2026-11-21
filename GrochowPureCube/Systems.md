# Exact equivalence of ordered cubic systems in characteristic three

Let $K=\mathbb F_q$, where $q=3^e$. The inputs are ordered lists $F=(f_1,\ldots,f_m)$ and $G=(g_1,\ldots,g_m)$ of formal homogeneous cubics in $n$ variables. A transporter is $A\in\mathrm{GL}(n,K)$ such that $G(Ax)=F(x)$ componentwise. The list coordinates are fixed throughout.

**Theorem.** For each input, polarize the list to a symmetric trilinear map $T:V^3\to K^m$. Let $C$ be the quotient by its common contraction radical and $U=\operatorname{span}T(C,C,C)$. Define
$$
 c=\dim C,\quad s=\dim U,\quad
 b=\dim\operatorname{im}\bigl[\operatorname{Sym}^2 C\longrightarrow
       \operatorname{Hom}(C,U)\bigr],\qquad
 xy\longmapsto T(x,y,-).
$$
Use $L=\max\{c_F+b_F+s_F,\ c_G+b_G+s_G\}$, and use $c$ for the larger quotient dimension. Decision, one transporter, and the exact transporter count reduce to $q^{O(c)}\operatorname{poly}(n,m,\log q)$ ordinary tensor-isomorphism decision calls with side lengths $O(L)$ and the same bound on additional work. Consequently the tasks take $q^{\widetilde O(L^{3/2})}\operatorname{poly}(n,m,\log q)$ deterministic time. If Graph Isomorphism is in $\mathsf P$, this improves to $q^{O(L)}\operatorname{poly}(n,m,\log q)$. The proof also constructs a quotient transporter coset by generators and a representative. When both polarizations vanish, all three tasks take polynomial time in $n,m,\log q$.

The width satisfies $b\le\min\{\binom{c+1}{2},cs\}$ and $s\le m$. The distinction between $m$ and $L$ is useful for long lists. The simultaneous pure-cube fiber has size $q^{cm}$ before taking the radical quotient. The algorithm processes one residual coordinate at a time and each orbit search visits at most $q^c$ cubics.

## 1. Radical shears and the exact count

Write $P_f(x,y,z)=[t_1t_2t_3]f(t_1x+t_2y+t_3z)$. In a basis, testing on a triple of basis vectors retrieves a coefficient times $1,2,$ or $6$, according to whether its multiplicities are $(1,1,1),(2,1),$ or $(3)$. Thus $P_f=0$ precisely for pure-cube sums. For the common radical $R$, choose a complement representing $C$. The same coefficient test makes every nonpure monomial involving a radical variable vanish. Cubing in $K$ is bijective with inverse $a\mapsto a^{q/3}$. In particular, $F$ has a decomposition
$$
 F(x+r)=F_C(x)+\ell_F(r)^{[3]}\qquad(x\in C,\ r\in R),
$$
where $\ell_F:R\to K^m$ is linear and $[3]$ denotes coordinatewise cubing. Apply the same decomposition to $G$. A transporter must respect the radicals. Reject unequal quotient dimensions and unequal images $\operatorname{im}\ell_F,\operatorname{im}\ell_G$. Write $D$ for the common image, $t=\dim D$, and $r=n-c$. The Frobenius image $D^{[3]}$ is also a $K$-subspace. Fix one quotient map $\rho:K^m\to K^m/D^{[3]}$, used on both sides.

Suppose $S:C_F\to C_G$ is a polarized transporter. A full transporter over $S$ has the form
$$
 A(x+r)=Sx+Wx+Hr,\qquad W:C_F\to R_G,\quad H:R_F\xrightarrow{\sim}R_G.
$$
Because the polarization discrepancy is zero, $F_C-G_C\circ S$ has the unique form $b_0^{[3]}$ for a linear $b_0:C_F\to K^m$. The equations for $A$ are precisely $\ell_GH=\ell_F$ and $\ell_GW=b_0$. The second is solvable if and only if $\rho F_C=\rho G_C\circ S$, in which case there are $q^{(r-t)c}$ choices. For the first, choose linear splittings of both maps onto $D$. The induced map on $D$ is the identity, the kernel block is any invertible matrix on $r-t$ dimensions, and the block from $D$ to the target kernel is arbitrary. These choices give a witness by linear algebra. If $N$ denotes the number of admissible $S$, the full count is
$$
 Nq^{(r-t)(c+t)}|\mathrm{GL}(r-t,q)|.
$$
This includes $c=0$, where the quotient contributes one map and no polarized search is needed.

## 2. A small oracle for polarized systems

Let $T_F=P_{F_C}$ and $T_G=P_{G_C}$. A polarized transporter requires equal subspaces $U\subseteq K^m$ and equal $b$. For either system write $B=\operatorname{im}[xy\mapsto T(x,y,-)]$. There are two bilinear maps
$$
 \mu:C\times C\to B,\qquad \epsilon:B\times C\to U,\qquad
 T(x,y,z)=\epsilon(\mu(x,y),z).
$$
A polarized transporter $S$ gives a uniquely determined transporter on $B$, namely $h\mapsto h\circ S^{-1}$ on the generating contractions. Conversely compatible transports on both bilinear maps give preservation of $T$, with the indicated output transport on $U$.

The decision oracle may also prescribe images of independent projective lines on $C$. Separate changes of basis place the lines in each list on the first coordinate axes. Use the following linked partitions for the bilinear maps and the line constraints.

| Tensor direction | Main blocks |
|---|---|
| First | $B,U,C$ |
| Second | $C^*,B^*$ |
| Third | $C^*$ |

Place $\mu$ in $B\otimes C^*\otimes C^*$ and $\epsilon$ in $U\otimes B^*\otimes C^*$. Link the $C$ transformation to inverse transposes on its dual blocks and the $B$ transformation to the inverse transpose on its dual block. Use disjoint auxiliary blocks on the second and third directions for each pin gadget. On the first-leg $C$ block, pin the requested axes. On the first-leg $U$ block, pin every axis of an identical basis $e_1,\ldots,e_s$ on both inputs. One additional rank-one block $(\sum_i e_i)\otimes a\otimes b'$ in two separate one-dimensional auxiliary blocks pins the all-ones line. This forces the output transformation to be $\lambda I_U$. The two bilinear equations then imply $T_G(Sx,Sy,Sz)=\lambda T_F(x,y,z)$. Replacing $S$ by $\lambda^{-1/3}S$ gives exact equality and preserves all prescribed lines. Conversely any exact polarized transporter extends to the construction with identity on $U$.

Here is the linear-size axis-pinning gadget. For $k\ge18$ pins take a rigid simple graph with $k$ edges and minimum degree two. The degree-three Frucht graph has 18 edges. Subdividing one edge into a path of $k-17$ edges preserves rigidity, since the degree-three vertices recover the original rigid graph and the path endpoints are fixed. Use the tensor
$$
 \sum_{a,v\colon v\in a} e_a\otimes e_v\otimes e_{(a,v)}
$$
on edges, vertices, and incidences. An eligible pair of transformations on the first two factors preserves the matrix space supported on incidences. Each invertible matrix has a support permutation by determinant expansion. The two support permutations send each incidence to an incidence because the image of its elementary matrix has a nonzero entry at the permuted position. They thus induce a graph automorphism and are both identities. All diagonal entries are consequently nonzero. A nonzero off-diagonal entry on either factor would force containment of one incidence neighborhood in another. Distinct edges have distinct two-element endpoint sets. Distinct vertices share at most one incident edge and each has at least two. The transformations on the first two factors are therefore diagonal. Conversely any diagonal on the first factor extends by inverse incidence scalars on the third. Embed the first factor on the span of the pinned axes. This span is the first contraction image and must be preserved. For $k<18$ use one rank-one block for each pin with two individually partitioned one-dimensional auxiliaries. The number of blocks is bounded by an absolute constant in either case, and each direction has length $O(L)$. [Frucht's cubic graphs](https://doi.org/10.4153/CJM-1949-033-6), [Grochow–Qiao IV, diagonal gadgets](https://arxiv.org/html/2306.16317#S4.SS5)

Theorems 5.3 and 5.1 of Grochow–Qiao IV successively remove the links and partitions at linear side lengths for a bounded number of blocks. Their Theorem 2.1 passes to alternating matrix spaces with linear order. The alternating matrix-space algorithm of Ivanyos, Mendoza, Qiao, Sun, and Zhang supplies the stated unconditional bound. One may deterministically enumerate the two individualizing matrices from Section III-E and verify the kernel rank test. Their small side has order the square root of the padded matrix dimension, so this preserves the exponent. For the conditional bound, encode the explicit carriers of the three tensor factors and the field as a finite relational structure. Label their sorts, name field scalars by unary colors, and encode vector addition, scalar multiplication, and the relation giving the value of the tensor applied to three covectors. All relations have bounded arity and the labeled incidence encoding has $q^{O(L)}$ size. The vector sorts are preserved, and preservation of addition and all fixed scalar operations is equivalent to $K$-linearity. [Grochow–Qiao IV, Theorems 2.1, 5.1 and 5.3](https://arxiv.org/html/2306.16317), [Ivanyos et al., FOCS 2024, Theorem I.4](https://chuanqizhang.com/assets/pdf/pdf/focs24.pdf)

### Witnesses and the polarized stabilizer

Given a positive oracle answer, begin with the prescribed independent lines and extend them to an ordered basis of source lines. For each new line, try each of fewer than $q^c$ projective image lines and retain a choice for which the oracle remains positive. With the complete list fixed, enumerate the $(q-1)^c$ scalar choices and check the exact trilinear equations. This produces a witness in $q^{O(c)}$ calls and nonoracle work apart from input-polynomial factors.

For the target polarization, use the stabilizer chain of the first $i$ coordinate lines, $0\le i\le c$. For each prefix, use the oracle to enumerate the orbit of the next line under its pointwise line stabilizer. Obtain a transporter for every reachable orbit point by the preceding witness procedure. These transporters, together with the stabilizer of the next line, generate the prefix stabilizer. The last stabilizer consists of the verified diagonal choices. The union of the transversal witnesses and the last stabilizer generates the full group, and the product of orbit sizes and the final stabilizer order gives its exact order. The total number of calls is still $q^{O(c)}\operatorname{poly}(n,m,\log q)$. [Grochow–Qiao IV, projective stabilizer chain](https://arxiv.org/html/2306.16317#S7.SS4)

## 3. Sequential recovery of the pure-cube data

Use $S\cdot F_C=F_C\circ S^{-1}$. Start with a polarized transporter $S_0$ and $H_0=\operatorname{Aut}(T_G)$. The remaining candidates form $H_0S_0$. Iterate through the coordinates of $\rho G_C$ in a fixed common basis of the quotient output space.

At each stage the candidate set is $HS$, where $H$ stabilizes the previously matched target cubics. For the next coordinate, let $u$ be the corresponding scalar cubic of $\rho(S\cdot F_C)$ and $v$ the target. Every element of $H$ preserves its polarization, so $H\cdot u$ is contained in a fiber of $P$ on one $c$-variable cubic. It has at most $q^c$ states, each determined in that fiber by its pure-cube coefficients. Enumerate the orbit by breadth-first search with group generators, retaining a witness for each reached state. If $v$ is absent, reject. Otherwise choose $h_0$ taking $u$ to $v$; the accepted candidates are precisely $H_v h_0 S$, where $H_v=\operatorname{Stab}_H(v)$. Replace $H,S$ accordingly. Orbit–stabilizer updates the order by dividing by the orbit length. Re-root the orbit at $v$ by composing the recorded witnesses with $h_0^{-1}$. The Schreier products $w_{h\cdot z}^{-1}h w_z$, for generators $h$ and visited states $z$, generate $H_v$. Indeed multiplying them along a word carrying $v$ back to itself telescopes.

To keep the generator set size bounded uniformly in the number of stages, regard matrices as permutations of all $q^c$ vectors. This is faithful. Test each candidate for membership in the group generated by the candidates already retained. Deterministic permutation-group membership is polynomial in the permutation degree and list length. Every accepted generator at least doubles the subgroup order, so the compressed list has at most $\log_2|\mathrm{GL}(c,q)|\le c^2\log_2 q$ elements. Each stage, including membership compression, thus costs $q^{O(c)}\operatorname{poly}(n,m,\log q)$. There are at most $m$ stages. At termination the subgroup order is $N$ from Section 1, and the retained representative gives a lift. [Furst–Hopcroft–Luks, polynomial-time permutation-group algorithms](https://ecommons.cornell.edu/entities/publication/f360d936-ad6c-47ab-8ceb-105c662e23d0)

### A large simultaneous orbit at small width

Let $f_0=h\sum_{i=1}^k x_i y_i$ and use the ordered system consisting of $f_0$ and $f_0+x_i^3,f_0+y_i^3$ for all $i$. Its common polarization is concise. Contracting with $(x_i,y_i)$, $(h,y_i)$, or $(h,x_i)$ tests the corresponding coordinate of the first argument. All its output polarizations coincide, so $s=1$. Since the two flattenings of a scalar symmetric trilinear form have the same rank by transposition, $b=c=2k+1$, and $L=2c+1$. The polarized group contains $\mathrm{GL}(k,q)$ acting by $x\mapsto Mx,\ y\mapsto M^{-\mathsf T}y,\ h\mapsto h$. This subgroup preserves $f_0$ and acts freely on the ordered tuple. Fixing the tuple forces every $x_i^3,y_i^3$ to be fixed, hence every $x_i,y_i$ by injectivity of cubing. The simultaneous orbit therefore has at least $|\mathrm{GL}(k,q)|=q^{\Omega(c^2)}$ states. The sequential searches use at most $q^c$ states per coordinate on this family.

## Relation to the literature

Ordered cubic systems in this model are a case of isomorphism of polynomials with one input secret. Patarin introduced polynomial isomorphism in cryptography. Ivanyos and Qiao solve the degree-two one-secret problem in odd characteristic by simultaneous quadratic-form isometry. Grochow, Qiao, and Tang give a characteristic-three predecessor for scalar cubics in their odd-order average-case theorem. The STOC 2025 proceedings state an overarching cubic-form corollary, and the finite-field cubic corollary and full-version Corollary 1.11 state characteristic greater than three. Those formulations warrant care in assessing priority for a scalar worst-case running-time headline. The exact contribution proved here is the ordered multi-output algorithm with the $c+b+s$ oracle width, output-image quotient, sequential single-coordinate orbit restriction, and radical lifting count. The primary sources checked did not establish priority for this combination. [Patarin, EUROCRYPT 1996](https://doi.org/10.1007/3-540-68339-9_4), [Ivanyos–Qiao](https://arxiv.org/abs/1708.03495), [Grochow–Qiao–Tang, Section 3.1](https://arxiv.org/abs/2012.01085), [STOC 2025 proceedings version](https://opus.lib.uts.edu.au/bitstream/10453/189643/2/3717823.3718282.pdf), [Grochow–Qiao IV, full version](https://arxiv.org/html/2306.16317)

The proof uses the cited tensor-isomorphism and permutation-group theorems. Running `python Systems.py` independently checks sequential coset restriction against all 6,561 binary ordered target pairs for one source over the field of three elements. This includes 24 negative instances with both coordinates individually reachable and compatible joint polarization. The script also enumerates four stabilizers in the three-variable general linear group and obtains orders 36, 2, 2, and 18. These include a non-coordinate radical image and a case of unequal radical images.

