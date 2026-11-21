# Determinant lines from signed graph layers of ternary cube-zero algebras

Let $F=\mathbb F_3$. The results below give a deterministic polynomial-time, single-instance reduction to ordinary three-tensor isomorphism on a recognizable class of based commutative algebras with scalar residue and radical cube zero. Their quadratic multiplication maps have scalar pair adjoint, and both the label space and its quadratic relation space can have quadratic dimension in the number of radical generators. The reduction attaches a one-dimensional role on which **every** transporter acts by its raw determinant.

The remaining unrestricted large scalar-centroid case of Open Question 1.9 is outside this class. The construction supplies an actual determinant line for use with an orientation-preserving cubic transporter. [Chen–Grochow–Qiao–Tang–Zhang, *Actions by classical groups*, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5) · [Exact cubic transporters](ExactCubicOrientationSeed.md)

## 1. Input class

Let $A$ be a commutative unital algebra with residue $F$ and radical $J$, with $J^3=0$. Put $U=J/J^2$, $W=J^2$, and let $\beta:U\times U\to W$ be multiplication. Its image spans $W$. We identify $W^*$ with its image $L$ in the symmetric bilinear forms on $U$ under $\beta^*$. The goal is to read the determinant of a map $A\to A'$ in the given raw bases. Any algebra transporter induces a transporter of $\beta$, and conversely any transporter of $\beta$ lifts by choosing complements for the two radical filtrations. The determinant of a lift is the product of the determinants on $U$ and $W$, up to the known ratios of frame determinants. There is also a direct free correction if $\dim U$ is odd. The map that negates a complement of $J^2$ in $J$ and fixes $J^2$ and the unit is an automorphism of determinant $-1$.

Here is the class for the nontrivial even case. There is a decomposition $U^*=X\oplus Y$ with even dimensions $a,b\ge4$, and bases $(\ell_i)$ of the two parts, for which
\[
 L=L_0\oplus FQ,qquad
 L_0=\operatorname{span}\{\ell_i\otimes\ell_i: i\in X\cup Y\}
   \oplus
   \operatorname{span}\{\ell_i\otimes\ell_j+\ell_j\otimes\ell_i:i\in X,\ j\in Y\}.
 \tag{1}
\]
The notation $i\in X$ means that the basis vector has index in the $X$ part. The symmetric form $Q$ has zero diagonal and no cross-part entries. In each part take its undirected support graph, with edge weights $\omega_{ij}\in F^\times$ given by the off-diagonal entries of $Q$. Require each graph to be connected, to have no universal vertex, and to have an edge avoiding each specified vertex. These conditions imply the existence of an induced path of length two in each part.

We also require the following computable graph condition. Color each internal edge by the dimension of its part and the unordered pair of the ordinary degrees of its two endpoints. Require a union $P$ of these color classes such that every vertex has odd degree in $P$. This is a system of linear equations over $\mathbb F_2$ in one variable per color. Take the lexicographically first solution in the lexicographically ordered colors. The solution is intrinsic under graph isomorphisms, including an exchange of equal-sized parts. In particular the condition holds whenever both graphs have all degrees odd, since all the edges then give a solution.

The next section recovers this presentation and tests the graph conditions by linear algebra and graph operations. The input does not include its hidden frames.

## 2. Intrinsic recovery of the two frames

For a space of symmetric matrices $L$, impose the linear lifts of all $2\times2$ minors of a general element of $L$ on the symmetric tensors in $L\otimes L$. Specifically a monomial $x_i x_j$ on the coordinates of $L$ is evaluated on a symmetric tensor by taking its $(i,j)$ coordinate, including the diagonal. Let $D$ be the computed kernel. The construction is intrinsic because the family of minors transforms by exterior squares of the two change-of-basis maps. The square of each rank-one element of $L$ belongs to $D$.

In the coordinates of (1), write $M=\operatorname{diag}(x)+Y_{\rm cross}+tQ$, where $Y_{\rm cross}$ is an arbitrary symmetric cross matrix. The minors force every coefficient involving $t$ to vanish on $D$.

- An induced path $i-j-k$ inside one part gives a minor on rows $i,j$ and columns $j,k$ equal to a nonzero multiple of $t^2$.
- For a diagonal coordinate $x_i$, choose an internal edge $j-k$ not incident to $i$ in its part. The minor on rows $i,j$ and columns $i,k$ is a nonzero multiple of $t x_i$ plus a multiple of $t^2$.
- For a cross coordinate $y_{ab}$ with $a$ in the first part and $b$ in the second, choose an internal nonneighbor $j$ of $a$ and a neighbor $i$ of $j$ in the first part. The minor on rows $a,i$ and columns $b,j$ is a nonzero multiple of $t y_{ab}$, because the $a,j$ entry vanishes.

Thus $D$ is supported on $L_0\otimes L_0$. Conversely, $L_0$ is spanned by rank-one elements. The diagonal elements have rank one, and subtracting the appropriate two diagonal elements from $(\ell_i+\ell_j)\otimes(\ell_i+\ell_j)$ gives any cross basis element. The squares of these rank-one elements lie in $D$, so their lines lie in the linear span of all one-factor contractions of $D$. Consequently that computed span is exactly $L_0$.

Take the annihilator $K_0$ of $L_0$ in the symmetric forms on $U^*$. The contraction pairing on these symmetric tensors is nondegenerate since $2\ne0$ in $F$. In the hidden basis, $K_0$ consists of the full off-diagonal symmetric matrix spaces on the two parts, with no cross entries. Its pair adjoint consists exactly of the pairs of matching scalar operators on each part. To prove this, let $(P_1,P_2)$ be an adjoint, so $P_1^{\mathsf T}M=MP_2$ for every $M\in K_0$. For each elementary internal form $M=E_{ij}+E_{ji}$ the two adjoint operators preserve its kernel, by the equation and its transpose. Intersecting the kernels of all internal forms whose two indices avoid a fixed index $k$ gives precisely the coordinate line $k$, since each part has at least three vertices. Thus both operators are diagonal. The equations on the off-diagonal units give $(P_1)_{ii}=(P_2)_{jj}$ for all distinct $i,j$ in the same part. This makes both operators the same scalar in that part, and the two part scalars are arbitrary. Therefore the two primitive idempotents of this two-dimensional split adjoint algebra recover $X,Y$ intrinsically from their first operators.

Within each recovered part the space $L_0\cap\operatorname{Sym}^2 X$ or $L_0\cap\operatorname{Sym}^2 Y$ is a full diagonal space. Its pair adjoint, computed on the dual of the part, consists of matching diagonal operators. To see this use the preservation of the coordinate hyperplanes given by the kernels of the individual diagonal forms. The simultaneous eigenspaces of these operators give the coordinate lines in the dual part, hence also their dual lines in the original part. They can be computed by repeatedly splitting a candidate space into the intersections with the $0,1,-1$ eigenspaces of each operator in a computed basis. For the required split diagonal algebra these intersections give direct sums at every step, with one-dimensional final spaces.

These computations give an explicit recognition algorithm. Compute $J$ as the kernel of cubing, which is linear over $F$ under the stated algebra hypotheses, and compute $W,\beta,L,D,L_0$ by linear algebra. Check that the annihilator adjoint has the stated two idempotents and that the diagonal recovery gives one-dimensional slots. Then check (1) in the resulting frames and that the quotient $L/L_0$ has dimension one. Select any lift of a quotient basis vector and erase its diagonal and cross entries to obtain $Q$. The remaining conditions on the two internal graphs and the union $P$ are then explicit tests. A successful test gives a literal presentation of the stated form, and the preceding proof shows that all such presentations are accepted in arbitrary raw bases. Every role has polynomial dimension. The minor equations use a polynomial number of degree-two coefficient arrays and all the subsequent eigenspace and consistency computations are linear algebra.

The original multiplication bimap has scalar pair adjoint. Indeed the diagonal forms in $L$ force both adjoint operators to preserve all coordinate hyperplanes and hence to be diagonal, with their diagonal entries agreeing in pairs. Every cross elementary form then equates the scalars at its two endpoints. The cross graph is complete bipartite and connected. Consequently the associated bimap centroid is scalar as well.

## 3. The determinant identity

Choose any based presentation recovered as above, ordering the parts by dimension when they differ and choosing any order in a tie. On each part select an arbitrary nonzero vector on each recovered coordinate line. Use the resulting dual basis in $U$. Use the basis of $L$ given by the diagonal forms, the cross forms in tensor-product order, and the chosen $Q$, and take its dual basis in $W$. Lift the basis of $U$ to $J$ and prepend the unit to obtain an adapted basis of $A$. Let $S_A$ be its column matrix in the original displayed basis of $A$.

Let $\phi:A\to A'$ be an isomorphism. Its inverse-dual map on $U^*$ sends $\ell_i$ to $s_i\ell'_{\pi(i)}$ with $s_i\in\{1,-1\}$. It acts on the quotient line $L/L_0$ with scalar $\sigma$ in the respective chosen quotient bases. Its action on the two primitive adjoint idempotents has permutation sign $\tau$. If the parts have distinct dimensions, $\tau=1$ by the ordering convention. If both have dimension $a$, a part exchange contributes $\tau^{a(a-1)/2}$ on the cross space. Indeed it flips the two tensor factors, whose coordinate permutation exchanges the two ordered pairs for each distinct pair among $a$ indices. Without exchange, the determinant on the cross space is the product of the determinants on the two parts raised to the dimensions of the opposite parts, and is one because both dimensions are even. With exchange, these same powers are one, leaving just the flip sign.

The diagonal label rows are permuted in exactly the same way as the raw coordinate lines, since $s_i^2=1$. Thus their permutation sign cancels with the permutation sign on $U^*$. Passing from duals to primal spaces inverts determinants, which does not change signs over $F$. The resulting product of determinants on $U,W$ in the adapted frames is
\[
 \left(\prod_i s_i\right)\sigma\tau^{\delta},
 \qquad
 \delta=
 \begin{cases}
  a(a-1)/2\bmod2,&a=b,\\
  0,&a\ne b.
 \end{cases}
 \tag{2}
\]
The unit is fixed and the discarded shears are block triangular with determinant one.

On an internal edge $ij$, applying the transported form $Q$ and comparing coefficients modulo $L_0$ gives
\[
 \omega_{ij} s_i s_j=\sigma\,\omega'_{\pi(i)\pi(j)}.
\]
The map $\pi$ preserves the support graphs and their degree colors, and hence maps the canonically chosen $P$ onto $P'$. Write $\omega(P)=\prod_{ij\in P}\omega_{ij}$. Multiplying the edge equations over $P$ gives
\[
 \prod_i s_i=\sigma^{|P|}\frac{\omega(P')}{\omega(P)},
\]
because every degree in $P$ is odd. Put $\kappa_A=\det(S_A)\omega(P)$ and $\varepsilon=|P|+1\bmod2$. In the original displayed bases we have the exact identity
\[
 \det\phi=\frac{\kappa_{A'}}{\kappa_A}\sigma^\varepsilon\tau^\delta.
 \tag{3}
\]
The determinant factors from the bases are essential and are computed once for each input. If the two parity parameters or part dimension multisets differ, the original algebras are not isomorphic.

## 4. A compact determinant record

Keep the multiplication table of $A$ and the canonical radical subspaces and quotients as linked roles, using inclusions and quotient maps. Every algebra isomorphism extends to these roles and their duals. Here is a constant-size extension forcing a single determinant line.

- If $\varepsilon=1$, take the quotient line $L/L_0$ with the quotient map from $W^*\simeq L$. If $\varepsilon=0$, use an anchored one-dimensional space with a fixed nonzero marked vector instead. These lines carry the factor $\sigma^\varepsilon$ in their natural bases.
- If $\delta=1$, keep the two-dimensional space of first operators of the adjoint of $K_0$ with its faithful action on $U^*$. Preserving the action forces conjugation by the actual transporter. The top exterior line of this two-dimensional space, attached by the single surjective wedge map, has multiplier $\tau$ in the two ordered primitive idempotent bases. If $\delta=0$, use an anchored line.
- Link the two resulting lines to their one-dimensional tensor product by a nonzero bilinear map. In that tensor-product line display the basis vector $\kappa_A^{-1}$ times the natural product basis vector.

Every algebra isomorphism lifts to these records, using the induced maps on all quotients, operators, and lines. Conversely the records link all line actions to that same isomorphism. The induced map in the displayed product bases is exactly (3). In particular, to compare for a prescribed sign $d$, mark the source displayed basis vector and $d$ times the target displayed basis vector. The tensor-system compiler applies because the records are linear or bilinear, or are marked vectors, and their number is independent of the dimensions. This produces one ordinary TI instance over $F$. It also supplies the determinant record needed by the exact cubic orientation construction on these algebras. [Chen–Grochow–Qiao–Tang–Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4) · [Exact cubic transporters](ExactCubicOrientationSeed.md)

## 5. Large scalar examples with a genuine sign constraint

For each part use a prism graph $C_m\square K_2$, with $m\ge4$, on its $2m$ coordinate lines. It is connected and $3$-regular, has no universal vertex, and each vertex avoids some edge. Take all weights $+1$ for simplicity. Use distinct and arbitrarily large part sizes, with one prism parameter $m$ even and one odd. In each part there is one degree color, and selecting it is necessary for odd degrees. Hence $P$ is the full internal edge set and $|P|$ is odd. Now $\varepsilon=\delta=0$ and every automorphism has determinant $1$ in the original basis. Reversing one vector of the displayed target basis of $W$ gives ordinarily isomorphic inputs whose only possible raw transporter sign is $-1$. Thus the sign constraint is genuine.

The bimap is realized by the commutative cube-zero algebra $F1\oplus U\oplus W$ with the stipulated products between two elements of $U$ and all other radical products zero. It has even total dimension $2+2(a+b)+ab$. Its label dimension is $a+b+ab+1$, and its quadratic relation dimension is $\binom a2+\binom b2-1$. Both are quadratic when the part sizes are comparable. The computed determinant role still has dimension one, and the bimap adjoint and centroid are still scalar.

The proofs are informal.
