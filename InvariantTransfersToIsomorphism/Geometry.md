# Graph isomorphism in smooth cubic hypersurfaces and their tensor polarizations

**Theorem.** Graph Isomorphism reduces by a deterministic polynomial-time many-one reduction to isomorphism of geometrically smooth cubic hypersurfaces given by rational equations. The output has $17(n+1)$ homogeneous coordinates for a graph on $n$ vertices. The equivalence holds even for abstract isomorphism over the algebraic closure. For the same cubics, their symmetric trilinear polarizations give a reduction to ordinary three-tensor isomorphism over $\mathbb Q,\mathbb R,\mathbb C$, independent-mode orthogonal isomorphism over $\mathbb R$, and independent-mode unitary isomorphism over $\mathbb C$. All these tensors have scalar pair adjoints. The product of the three transporter determinants is exactly the permutation sign of the underlying graph isomorphism on the padded vertex set.

A second construction gives GI-hardness of geometrically smooth cubic hypersurface isomorphism over every field of characteristic two, including $\mathbb F_2$. This construction uses $10n+42$ homogeneous coordinates for a graph with $n$ vertices.

## 1. A characteristic-zero construction

Adjoin one universal vertex to the graph. Denote the resulting connected graph by $G$ and its vertex count by $N$. Two padded graphs are isomorphic exactly when the originals are. To recover the original, delete any one universal vertex. All universal vertices can be permuted arbitrarily by automorphisms of the padded graph. Distinct input vertex counts can be handled immediately by a fixed negative instance.

Fix a graph $L$ consisting of a triangle with pendent paths of lengths $2,4,7$ on its three distinct vertices. It has sixteen vertices and sixteen edges. It is rigid because its unique triangle must be preserved, the three distinct lengths force each triangle vertex to be fixed, and distance along each path then fixes the path. It is connected and contains an odd cycle. It has an induced matching of size four. Use the edges joining distances $1,2$ on the short path, distances $2,3$ on the middle path, and distances $1,2$ and $4,5$ on the long path. None of their endpoints lies in the triangle, and no other edges join the selected endpoints. Also two vertices have disjoint closed neighborhoods, for example the end vertices of the short and long paths.

For each graph vertex use a coordinate $x_i$ and a copy $(y_{ir})_{r\in V(L)}$ of the auxiliary coordinates. Let $W$ be the subspace of the coordinate space with all $x_i=0$. Define
$$
\begin{aligned}
 f_G(x,y)={}&\sum_i x_i^3+\sum_{i,r} y_{ir}^3\\
 &+\varepsilon\left(\sum_i x_i\sum_{\{r,s\}\in E(L)} y_{ir}y_{is}
             +\sum_{\{i,j\}\in E(G)}(x_i^2x_j+x_ix_j^2)\right),
 \qquad \varepsilon=\frac1{100(N+1)}.
\end{aligned}
$$
The coefficients have polynomial bit length, and the output is computable in polynomial time in dense or sparse format.

### Smoothness

If every partial derivative vanished at a nonzero point over $\mathbb C$, choose a coordinate whose absolute value $M>0$ is maximal. The corresponding derivative contains its term $3u^2$. The absolute value of the sum of the other terms in an $x$-derivative is bounded by $\varepsilon(16+3(N-1))M^2<3M^2$. The bound for a $y$-derivative is at most $3\varepsilon M^2$, as $L$ has maximum degree three. Thus the derivative for the chosen coordinate cannot vanish. This proves smoothness over $\mathbb C$ and geometric smoothness over $\mathbb Q$.

### Recovering the graph from any projective equivalence

Let $H_f(v)$ denote the Hessian evaluated at $v$, viewed as a symmetric bilinear form. Under a linear change of coordinates the Hessian transforms by congruence with the original matrix, and an overall nonzero scalar does not change its rank.

If $x_i(v)\ne0$, restrict the rows and columns of the Hessian to opposite endpoints of the chosen induced matching in the $i$-th $L$ copy. These sets are disjoint. The resulting submatrix is the $4\times4$ scalar matrix $\varepsilon x_i(v)I_4$. Thus $H_f(v)$ has rank at least four. At each auxiliary coordinate vector $e_{ir}$, write $s_{ir}$ for the sum of the auxiliary coordinate covectors indexed by the neighbors of $r$. The Hessian is
$$
  6y_{ir}\otimes y_{ir}
  +\varepsilon(x_i\otimes s_{ir}+s_{ir}\otimes x_i).
$$
It has rank three, since the three covectors are independent and $\varepsilon\ne0$. Consequently $W$ is exactly the span of the vectors where the full Hessian has rank at most three. All of this argument works in any extension of $\mathbb Q$.

Suppose $f_{G'}(A v)=\lambda f_G(v)$ for $A$ invertible and $\lambda\ne0$. Then $A$ takes $W$ onto its counterpart. On $W$ the cubic is the Fermat form $\sum y_{ir}^3$. Its Hessian has rank one exactly on the nonzero coordinate axes. It follows that the restricted map $Q=A|_W$ is monomial. Write $A(x,y)=(P x, Qy+Sx)$. In the coefficient of $y_{ir}^2$ times a linear form in $x$, only the Fermat cube of the corresponding output auxiliary coordinate contributes. Its contribution is the corresponding component of $Sx$ multiplied by $3$ times the square of a nonzero monomial coefficient. The auxiliary terms with two distinct $y$-variables cannot contribute to this coefficient because $Q$ is monomial. The source has no such coefficient. Hence $S=0$.

The coefficients of $y_{ir}y_{js}$ as linear forms in $x$ now show that the auxiliary variable permutation carries the disjoint union of the $N$ copies of $L$ to itself. They are its connected components. Each copy has a unique isomorphism to another copy in the prescribed $L$-labels, by rigidity. For each paired copy the same coefficient equation matches the line of the associated vertex covector $x_i$ to that of the paired vertex. Thus $P$ is monomial with the same vertex permutation $\pi$. The support of the terms $x_i^2x_j$ shows that $\pi$ is a graph isomorphism.

Every such $A$ is a scalar times the specific coordinate permutation $P_\pi$ on the vertex variables and matched copies of the auxiliary graph. To verify the scalar claim, first the coefficients of $x_i^3$ give $a_i^3=\lambda$ for every vertex scale $a_i$. The coefficient of $x_i^2x_j$ on each edge then gives $a_i^2a_j=\lambda$. Thus all $a_i$ equal a common $a$ by connectivity, and $\lambda=a^3$. The auxiliary scales divided by $a$ have cube one. Along any edge in one copy of $L$, their product is one, by comparing the coefficient of the corresponding $x_i y_{ir}y_{is}$. Its odd cycle makes all these ratios have square one as well, hence they are all one. Conversely every graph isomorphism gives the stated coordinate permutation of the cubics. This proves the projective comparison and the exact projective transporter description.

## 2. Independent tensor actions and determinant signs

Let $\Phi_G$ be the symmetric trilinear polarization, normalized by $\Phi_G(v,v,v)=f_G(v)$. In characteristic zero it is obtained by linear coefficient arithmetic. The pair-adjoint assertion here concerns the space of common transfer operators
$$
 \{ M\colon\Phi_G(Mu,v,w)=\Phi_G(u,Mv,w)\ \text{for all }u,v,w\}.
$$
In this definition the same $M$ appears on both sides. The argument below also identifies the space with arbitrary separate operators $M,M'$ in the two slots.

First suppose $M$ is a common transfer operator. It satisfies
$M^T H_f(w)=H_f(w)M$ for every $w$. Thus its dual $M^*$ preserves the image of each $H_f(e_{ir})$, namely $\langle x_i,y_{ir},s_{ir}\rangle$. Intersecting two such spans from disjoint closed neighborhoods of $L$ gives $\langle x_i\rangle$, so $M^*x_i=a_i x_i$. Write
$$
 M^*y_{ir}=b_r x_i+c_r y_{ir}+d_r s_{ir},\qquad
 M^*s_{ir}=e_r x_i+f_r y_{ir}+g_r s_{ir}.
$$
Comparing the two ways of applying $M^*$ to one factor of the displayed $H_f(e_{ir})$ gives $d_r=0$, $g_r=a_i$, and $6b_r=\varepsilon f_r$. These identities hold for every $r$. But $M^*s_{ir}=\sum_{s\sim r}M^*y_{is}$, and each summand has auxiliary part $c_s y_{is}$. There is no $y_{ir}$ term because $L$ is loopless. Hence $f_r=b_r=0$. Comparing the neighbor coefficients gives $c_s=a_i$ for every neighbor of $r$. Every vertex has a neighbor, so $M^*$ is scalar on the entire $i$-th block. For each graph edge the monomial $x_i^2x_j$ has nonzero polarization, forcing $a_i=a_j$ by applying the transfer identity in the $i,j$ slots. Connectivity gives a global scalar.

Now suppose $M,M'$ satisfy $\Phi_G(Mu,v,w)=\Phi_G(u,M'v,w)$. The same kernel and image argument gives preservation of every $\langle x_i,y_{ir},s_{ir}\rangle$ by both dual maps, using the transpose identity for the other map. Thus both send $x_i$ to a scalar multiple of itself. Write on the $i$-th block
$$
 M^*x_i=a x_i,\quad M'^*x_i=a'x_i,\quad
 M^*y_{ir}=b_r x_i+c_r y_{ir}+d_r s_{ir},\quad
 M'^*y_{ir}=b'_r x_i+c'_r y_{ir}+d'_r s_{ir}.
$$
Comparison in $(M^*\otimes I)H_f(e_{ir})=(I\otimes M'^*)H_f(e_{ir})$ forces $d_r=d'_r=0$, $c_r=c'_r$, and the $s_{ir}$ coefficients in $M^*s_{ir}$, $M'^*s_{ir}$ to be $a'$, $a$, respectively. The neighbor sums therefore give $c_s=a'$ and $c'_s=a$. Hence $a=a'$. In these neighbor sums the $y_{ir}$ coefficient is zero, which, by the same identity and its transpose, gives $b_r=b'_r=0$. Thus the two maps agree and are global scalars by the edge test. The same statement holds for every pair of slots by symmetry.

If independent invertible mode maps satisfy $\Phi_{G'}(Au,Bv,Cw)=\Phi_G(u,v,w)$, interchange $u,v$ and use symmetry on both sides. Writing $R=BA^{-1}$ gives
$$
 \Phi_{G'}(a,b,c)=\Phi_{G'}(Ra,R^{-1}b,c).
$$
Replace $b$ by $Rb$ to see that $R$ is a common transfer operator. Thus $B$ is a scalar multiple of $A$, and the same argument gives that $C$ is a scalar multiple of $A$. On the diagonal $A$ consequently carries $f_G$ to $f_{G'}$ up to a scalar. The previous calculation shows that all independent transporters are triples $a_1 P_\pi,a_2 P_\pi,a_3 P_\pi$, where $\pi$ is a graph isomorphism and $a_1a_2a_3=1$. Conversely every such triple works. Transpose or inverse transpose conventions for arrays give the same isomorphism and determinant-sign conclusions.

In particular, every YES instance has a transporter acting by the coordinate permutation in all modes. Such a permutation is orthogonal over $\mathbb R$ and unitary over $\mathbb C$. Nonisomorphic graphs have no ordinary transporter even over $\mathbb C$. The exact reduction therefore holds for all the stated actions. The sign of $P_\pi$ is $\operatorname{sgn}(\pi)$, since a permutation of blocks of sixteen contributes even sign and all internal labels are fixed. Multiplying the three determinants yields $\operatorname{sgn}(\pi)$. In particular the special-linear tensor question on these outputs is precisely the even-graph-transporter question on the padded graphs. An even graph isomorphism supplies three permutation matrices of determinant one, while determinant one in all modes requires even sign.

**Special-linear hardness.** For a GI instance on $n$ vertices, adjoin two universal vertices to each graph in place of the single universal vertex. Deleting any two universal vertices recovers the original graph up to isomorphism. If the padded graphs are isomorphic, an isomorphism extends from the original graphs, and composing it with a transposition of the two new vertices changes its sign whenever needed. Thus some padded isomorphism is even. Applying the determinant characterization above gives a deterministic many-one reduction from GI to special-linear tensor isomorphism on the same smooth, scalar-pair-adjoint family with $17(n+2)$ coordinates per mode.

## 3. Characteristic two with a linear number of coordinates

Add two disjoint single-edge components to the input graph. Delete any two components of this type to recover the input up to isomorphism. Call the padded graph $G$, with $N=n+4$ vertices. Its adjacency matrix has rank at least four over every field because of the two new components.

Use coordinates $u=(x_i,y_{i1},y_{i2},y_{i3},y_{i4},z)$, with one $x_i$ and four auxiliary variables per vertex and one global coordinate $z$. Set
$$
 t_G(u)= z\sum_{\{i,j\}\in E(G)}x_i x_j
          +\sum_i x_i(y_{i1}y_{i2}+y_{i3}y_{i4}),\qquad
 F_G(u,v)=t_G(u)+\sum_a(u_a^2 v_a+v_a^2 u_a).
$$
Here $v_a$ is a mirror of each coordinate of $u$. In characteristic two, the $v$-derivatives of $F_G$ are $u_a^2$. If these vanish, $u=0$, and then its $u$-derivatives are $v_a^2$. Thus the cubic is geometrically smooth. There are $2(5N+1)=10n+42$ coordinates.

The third polarization of a cubic is defined by taking the coefficient of $str$ in the evaluation at $sa+tb+rc$. In characteristic two this trilinear form is alternating, and terms containing a squared variable have zero third polarization. Write $\tau$ for the third polarization of $t_G$ on the $u$-space $U$, and $W\subset U$ for the span of $y$-coordinate vectors. We recover $W$ as the span of vectors having contraction rank at most two for $\tau$. For a vector with $x_i\ne0$, the contraction restricted to the $i$-th four-dimensional auxiliary block in both remaining arguments is $x_i$ times the invertible alternating matrix of the two private matching edges. Its rank is four. For a vector with $z\ne0$, the submatrix on the vertex arguments is $z A_G$, of rank at least four, independent of the other coordinates of the contracted vector. Finally every single auxiliary coordinate vector has contraction rank two, pairing its vertex coordinate and its partner. This proves the characterization of $W$.

The global coordinate line $Z$ is intrinsically
$$
 Z=\{u\in U\colon\tau(u,W,U)=0\}.
$$
Indeed the restriction to $W\times W$ forces all $x_i=0$ as above. Then the restriction to the $i$-th auxiliary block and the $i$-th vertex direction forces the $i$-th auxiliary component to vanish by the same invertible four-dimensional matching matrix. The $z$-direction itself gives zero on $W\times U$. In particular the radical of $\tau$ is contained in $Z$, and it is zero since contraction of the $z$-direction on vertex vectors is the nonzero adjacency matrix. It follows that the radical of the third polarization of $F_G$ is exactly the mirror $v$-space. Thus a projective equivalence of the smooth cubics induces a linear equivalence up to scalar of their forms $\tau$ on the respective quotients by the mirror spaces.

In $U/(W+Z)$, the contraction on $W\times W$ is well defined and has rank $4$ times the number of nonzero $x_i$-coordinates of its argument. Therefore its rank-four directions recover exactly the individual vertex axes, and a transporter on this quotient is monomial. Contracting any nonzero vector of $Z$ in $\tau$ also gives a two-form on this quotient. It is a nonzero scalar multiple of the alternating adjacency matrix. The quotient transporter thus preserves its support by the associated vertex permutation, which is a graph isomorphism. Conversely every graph isomorphism acts by the indicated permutation of vertex and auxiliary coordinates, fixes $z$, and acts by the corresponding mirror permutation. These maps preserve the displayed cubic exactly. The argument works over every extension of any field of characteristic two.

Pairs of different input orders can be handled by a fixed negative instance. For a fixed negative pair of the same format, one may use the four-vertex graphs consisting respectively of two disjoint edges and of two incident edges with an isolated vertex. The proofs apply after padding, and the output formats agree.

## 4. Abstract hypersurface isomorphism and scope

On both constructions the hypersurface dimensions are at least three after the direct small cases. For a smooth hypersurface of that dimension over an algebraically closed field, the Grothendieck–Lefschetz theorem identifies its Picard group with $\mathbb Z$ generated by the hyperplane bundle. An abstract isomorphism must preserve that ample generator. The sections of this bundle are exactly the restrictions of the ambient linear forms, by the defining hypersurface sequence. Thus the isomorphism extends to a projective linear map. Smoothness gives reduced cubic hypersurfaces, so a projective linear equivalence of the hypersurfaces is equality of their defining cubics up to scalar. This proves the claimed reduction even if the target comparison is by abstract isomorphism over the algebraic closure. [Grothendieck, SGA 2, Exposé XII, Corollary 3.7](https://jcreinhold.github.io/sga/ii/12-projective-algebraic-schemes.html)

### Every finite group is the full symmetry group of a smooth cubic

The characteristic-zero construction applies directly to every connected graph, since connectedness is the only use of the universal vertex in the tensor argument. To embed any graph $G$ on $n\geq 2$ vertices into a connected graph while preserving its full automorphism group, add a vertex $u$ adjacent to every old vertex and attach one new path on $n+1$ vertices by one endpoint to $u$. The degree of $u$ is $n+1$, greater than those of all other vertices. Removing $u$ leaves the added path as the unique component with $n+1$ vertices. The endpoint through which it meets $u$ is distinguished, so its vertices are all fixed by any automorphism. Thus restriction is an isomorphism $\operatorname{Aut}(J(G))\cong\operatorname{Aut}(G)$.

Every projective automorphism of the corresponding smooth cubic is the projective class of the unique coordinate permutation obtained from a graph automorphism. The ambient projective extension of an abstract automorphism is unique because it is determined by the complete linear system of the hyperplane bundle. Hence the resulting hypersurface over $\mathbb Q$ has geometric automorphism group isomorphic to $\operatorname{Aut}(G)$, and every automorphism is defined over $\mathbb Q$. Frucht's theorem therefore implies that every finite group occurs as the full geometric automorphism group of a smooth cubic hypersurface defined over $\mathbb Q$, with all automorphisms defined over $\mathbb Q$. [Frucht, Graphs of Degree Three with a Given Abstract Group](https://doi.org/10.4153/CJM-1949-033-6)

The fixed-cubic Ley construction encodes a graph by triples containing the two endpoints and one edge point. Here cubic monomials encode this incidence and contraction ranks recover the auxiliary subspaces directly from the geometric form. Earlier work reduced GI to unrestricted cubic form equivalence and to unrestricted orthogonal or unitary TI. The promises established here are geometric smoothness, scalar pair adjoints in characteristic zero, and the explicit graph transporter including its determinant sign. Primary-source searches found the unrestricted predecessors and related graphical matrix-space reductions. Publication priority for the smooth restrictions remains unverified. The proofs are informal. [Agrawal–Saxena on cubic forms](https://repository.ias.ac.in/122780/) · [Chen–Grochow–Qiao–Tang–Zhang on classical tensor actions](https://arxiv.org/abs/2306.03135)
