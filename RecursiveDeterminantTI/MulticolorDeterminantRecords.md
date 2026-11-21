# Determinant records from multicolored internal graphs with two scalar centroids

Over $F=\mathbb F_3$, there is a polynomial-time recognizable class of based commutative cube-zero algebras for which both the graded multiplication bimap and its dual relation bimap have scalar centroid. A single ordinary three-tensor isomorphism instance decides any prescribed determinant on this class. The construction reads the raw determinant of every transporter in a one-dimensional role. The number of independent graph colors can grow without bound, and both the label and relation dimensions can be quadratic in the number of generators. The determinant uses only fixed-size exterior data and a triangular matrix algebra of polynomial dimension.

## 1. A multicolored class

Let $A$ be a based commutative unital algebra with scalar residue $F$ and radical $J$, where $J^3=0$. Put $U=J/J^2$, $W=J^2$, and denote its multiplication bimap by $\beta:U\times U\to W$. Write $L\subseteq\operatorname{Sym}^2 U^*$ for the space of symmetric forms obtained from $W^*$ by composition with $\beta$. The dual relation bimap has slices
\[
 K=L^\perp\subseteq\operatorname{Sym}^2 U
\]
on $U^*$. This annihilator is defined by the natural perfect pairing, since the characteristic is odd. By centroid we mean the algebra of linked input and output actions which can move between either input and the output. The balanced pair adjoint only imposes equality of the two input actions.

The presentation considered here consists of a decomposition $U^*=X\oplus Y$ of even dimensions $a,b\ge4$, a frame $(\ell_i)$ in each part, and
\[
 \begin{split}
 L&=L_0\oplus\bigoplus_{c=1}^r FQ_c,\\
 L_0&=\operatorname{span}\{\ell_i^2\}_{i\in X\cup Y}
       \oplus \operatorname{span}\{\ell_i\otimes\ell_j+\ell_j\otimes\ell_i:i\in X,j\in Y\}.
 \end{split} \tag{1}
\]
Here $\ell_i^2=\ell_i\otimes\ell_i$. Each symmetric $Q_c$ has nonzero coefficients only on internal, off-diagonal edges. The supports for different $c$ are disjoint. Call these supports the colors of an undirected graph with edges internal to the parts. Each color occurs in both parts. An edge $ij$ of color $c$ has weight $\omega_{ij}=(Q_c)_{ij}\in F^\times$ in the chosen frames.

Impose the following coordinate conditions.

- For any colors $c,d$, including $c=d$, there are oriented edges $ij$ of color $c$ and $kl$ of color $d$ in one part with $i\ne k$ and $j\ne l$. At least one of the pairs $(i,l),(k,j)$ has distinct endpoints and is a nonedge in the union graph.
- For every vertex $a$ and color $c$, there is a color-$c$ edge in the same part which avoids $a$. There is also a color-$c$ edge $ij$ in its part with $j\ne a$ and $aj$ a nonedge.
- At a vertex in a part of dimension $d$, at most $d-3$ colors occur on its incident edges.

The determinant-line theorem further imposes two algorithmic conditions.

- Each color has a distinct signature, defined as the unordered list of the two pairs (part dimension, number of edges of this color in the part).
- There is an edge set $P$ with every vertex of odd degree, which is a union of edge cells defined by color signature, part dimension, and unordered endpoint degrees in the full union graph.

The last condition is linear algebra over $\mathbb F_2$. Use one variable per edge cell and one parity equation per vertex. Choose the lexicographically first solution in the order of the displayed cell descriptors. This is computed by testing consistency with each tentative first coordinate in sequence. It is invariant under all graph isomorphisms preserving the parts or exchanging equally sized parts.

We will recover (1) from the based algebra. Thus the presentation is a testable property rather than additional input data. The one-color signed graph class with a connected noncomplete internal graph in each part and the earlier edge-witness hypotheses is included. An induced internal path gives its first condition, and the incident-color bound holds because each part has size at least four.

## 2. Intrinsic recognition

For a space of bilinear forms $L$, form the kernel $D\subseteq(L\otimes L)^{\mathrm{swap}}$ of the linear lifts of all $2\times2$ minors of a general element of $L$. A coordinate monomial $x_i x_j$ is evaluated by taking the $(i,j)$ coordinate of a symmetric tensor. This is intrinsic, because the minors of a matrix transform by exterior squares of the two change-of-basis maps. If a form $v$ has rank one, then $v\otimes v\in D$.

In coordinates (1), write a general matrix as $\operatorname{diag}(x)+Y_{\rm cross}+\sum_c t_c Q_c$. The first witness condition gives a minor in rows $i,k$ and columns $j,l$ which is a nonzero multiple of $t_c t_d$. A same-part edge $jk$ of color $c$ avoiding a specified $a$ gives a minor in rows $a,j$ and columns $a,k$ whose first product is a nonzero multiple of $x_a t_c$. The other product either vanishes or is a multiple of a pair of color variables, which already vanishes on $D$. Finally for a cross coordinate $y_{ab}$ with $a\in X,b\in Y$, use the color-$c$ edge $ij$ in $X$ with $aj$ a nonedge. The minor in rows $a,i$ and columns $b,j$ is a nonzero multiple of $y_{ab}t_c$. The second product vanishes by the nonedge condition. Thus every coordinate involving a $t_c$ vanishes on $D$, so $D$ is supported inside $L_0\otimes L_0$.

The rank-one forms in $L_0$ span it. The diagonal squares are rank one, and the cross basis forms follow by subtracting diagonals from $(\ell_i+\ell_j)^2$. Hence the linear span of the one-factor contractions of $D$ is exactly $L_0$. All these spaces and contractions are computed by linear algebra on polynomial-size arrays.

Take $K_0=L_0^\perp\subseteq\operatorname{Sym}^2 U$ as forms on $U^*$. In the hidden frame this is the sum of the two full off-diagonal symmetric spaces, one per part. Its balanced pair adjoint has two scalar factors. To verify this, if $P^{\mathsf T}M=MQ$ for all $M\in K_0$, then $P,Q$ preserve the kernel of each elementary internal form $E_{ij}+E_{ji}$, by the equation and its transpose. Intersecting these kernels over internal pairs avoiding a vertex $k$ gives its coordinate line, because each part has at least three vertices. Hence both operators are diagonal. The equations on internal forms force the two operators to coincide and be scalar on each part. The two primitive idempotents recover the parts. These can be found by linear equations for the adjoint and by testing its nine elements once it has dimension two.

Restrict $L_0$ to the pure symmetric space of each recovered part. This gives its full diagonal space, whose pair adjoint consists of matching diagonal operators, as follows from the kernels of its diagonal rank-one basis. Recover the coordinate lines by refining simultaneous eigenspaces of the first operators at the three scalars of $F$ and taking the corresponding dual lines. For the required diagonal space this yields one-dimensional slots. Verify the resulting presentation of $L_0$ in these slots.

The quotient $Q=L/L_0$ embeds in the coordinate space of internal off-diagonal coefficients. Each internal edge coordinate is thus a row functional on $Q$. Group its nonzero rows into projective lines in $Q^*$. In (1) these distinct row lines are exactly the dual color basis lines. Conversely, if the distinct row lines are independent and span $Q^*$, choose a nonzero representative of each row line and take the dual basis of $Q$. The resulting forms, with diagonal and cross coefficients removed, have disjoint supports. This recovers the colors and their weights. The algorithm checks all three witness conditions and the graph conditions in the recovered frames. Every step on a valid presentation is invariant under isomorphisms up to the stated change of frame. For other inputs, successful final checks certify an actual presentation of (1).

## 3. Both centroids are scalar

The pair adjoint of the original bimap is scalar. Its diagonal slices force both operators to preserve all coordinate hyperplanes, and their entries agree at each vertex. The complete cross support then equates the two endpoint entries for every cross pair, so the entries are all equal.

For the relation bimap, $K$ is given in $K_0$ by the $r$ equations $\langle M,Q_c\rangle=0$. Fix a coordinate $i$ in a part of dimension $d$. The forms with star shape
\[
 M=e_i\otimes v+v\otimes e_i
\]
belong to $K$ when $v$ is supported in the same part off coordinate $i$ and is orthogonal to each color row at $i$. By the third witness condition this gives at least a two-dimensional space of $v$. Each nonzero such form has kernel the annihilator of $\operatorname{span}(e_i,v)$ in the input space of the relation bimap. Any paired adjoint preserves the kernel of every one of these forms, as before. Its dual therefore preserves both planes obtained from two independent $v$, and hence their intersection $Fe_i$. Varying $i$ makes the two adjoint operators diagonal.

Every internal cross coefficient within a part occurs nontrivially in some element of $K$. An uncolored edge coordinate is unconstrained. For a colored coordinate one may cancel its contribution using any edge of the same color in the other part. Thus the diagonal adjoint equations force the two operators to be the same scalar on each part, so the relation pair adjoint is precisely $F\times F$. The same stars show full relation support. A vector with nonzero coordinate $i$ cannot be in the common radical, since evaluating the star at this vector has its nonzero off-$i$ component proportional to $v$.

A relation centroid must in addition act on the slice space $K$. Scaling the two parts by scalars $\alpha,\gamma$ preserves its equations only if $\alpha=\gamma$. Indeed choose an element of $K$ with two nonzero entries, one from each part in a common color, whose contributions to that color equation are $1$ and $-1$. The transformed equation is $\alpha-\gamma=0$. An equal scalar gives a centroid element, with the same output scalar by spanning. Hence the original and relation centroids are both scalar. In particular this proves the two-scalar claim for the whole earlier one-color class, with no extra graph-degree assumption.

## 4. Transporting the raw determinant

Assume first that the signatures are distinct and the required $P$ exists. Order the two parts by dimension when they differ, using any order in a tie. Take the cross basis in tensor-product order. For each recovered coordinate line choose a nonzero vector $\ell_i$. Choose a nonzero quotient generator $q_c$ for each color and order the colors by signature. Use its lift supported on internal edges as $Q_c$. The diagonal, cross, and color bases of $L$ give a dual basis of $W$. Together with the dual frame of $U$, lifted into $J$, and the unit, this gives an adapted basis of $A$. Let $S_A$ have its columns in the raw basis.

An algebra isomorphism $\phi:A\to A'$ induces the inverse-dual map on $U^*$ with
\[
 \ell_i\longmapsto s_i\ell'_{\pi(i)},\qquad s_i\in\{1,-1\}.
\]
It maps the parts according to a permutation of sign $\tau$, and sends $q_c$ to $\sigma_c q_c'$ on each signature line. The permutation sign on the diagonal basis of $L_0$ equals the one on $U^*$, since $s_i^2=1$. They cancel in the combined sign. The determinant on the cross space has only a possible part exchange sign. Without exchange the factors have exponents $a$ and $b$, both even. With exchange of equal parts of dimension $a$, the tensor flip has sign $(-1)^{a(a-1)/2}$. Thus write $\delta=a(a-1)/2\bmod2$ if $a=b$ and $\delta=0$ otherwise. The combined adapted sign is $(\prod_i s_i)(\prod_c\sigma_c)\tau^\delta$. Taking inverse duals has no effect on signs over $F$.

Comparing the image of $Q_c$ on an internal edge $ij$ gives
\[
 \omega_{ij}s_is_j=\sigma_c\omega'_{\pi(i)\pi(j)}.
\tag{2}
\]
The map preserves the selected edge cells and maps $P$ onto $P'$. Multiplying (2) over $P$ uses every vertex sign to an odd power. With $\omega(P)=\prod_{ij\in P}\omega_{ij}$ and $\kappa_A=\det(S_A)\omega(P)$, this proves
\[
 \det_{\rm raw}\phi=
 \frac{\kappa_{A'}}{\kappa_A}\,\tau^\delta
 \prod_{c: \ |P\cap E_c|\ {\rm even}}\sigma_c .
 \tag{3}
\]
The filtration shears have determinant one. The known frame ratios in (3) include the original based algebra, so the equality holds for every transporter.

## 5. A fixed number of records for any number of colors

Keep the multiplication of $A$ and its radical subspaces and quotients as linked roles. This links $U^*,W^*$ to the actual algebra maps. Keep the quotient $Q=L/L_0$ by its map from $W^*$. The even-count colors on the right of (3) are intrinsically ordered by signature. Say there are $t$ of them. Put $V_P$ equal to their direct sum inside $Q$, with basis $q_1,\ldots,q_t$ in that order.

Use the algebra of upper triangular $(t+1)\times(t+1)$ matrices with ordered indices $0,\ldots,t$, and keep its diagonal subalgebra by one inclusion. Attach $V_P$ to the first superdiagonal by sending $q_i$ to $E_{i-1,i}$. Any isomorphism of these records permutes the primitive diagonal idempotents. The relation $E_{ii}AE_{jj}\ne0$ holds exactly for $i\le j$, so their total order forces each idempotent to its corresponding idempotent. The arrow multipliers are therefore $\sigma_1,\ldots,\sigma_t$, and multiplication forces the line $FE_{0t}$ to have their product. Conversely any arrow multipliers extend by scaling each $E_{ij}$ by the product along its path. This includes $t=0$, where the single diagonal unit fixes the product line.

When $\delta=1$, the two-dimensional space of first adjoint operators of $K_0$ is attached by its faithful action on $U^*$. This forces conjugation by the actual transporter. Attach its two-dimensional top exterior line by the binary wedge map. Its multiplier is $\tau$ in the ordered primitive-idempotent frames. When $\delta=0$, use an anchored line. Multiply the two scalar lines by a one-dimensional tensor-product record, and display its basis vector as $\kappa_A^{-1}$ times the natural one. Its multiplier is precisely (3). Every algebra transporter lifts, and all lifts have this multiplier.

There are a fixed number of linear and bilinear records and marked vectors, independently of $t$. The triangular algebra has dimension $O((t+1)^2)$ and its multiplication table is polynomial-size. Therefore marking the displayed determinant vector on the source and its desired multiple on the target gives a single ordinary three-tensor comparison over $F$. This is an actual determinant line and can equally be linked to the exact cubic transporter construction. [Tensor-system compiler](https://arxiv.org/html/2306.03135v2#S4) · [Exact cubic transporters](ExactCubicOrientationSeed.md)

## 6. Matching examples and direct decision with repeated signatures

Both internal union graphs may be matchings covering all their vertices, with at least two edges of each color in each part. The witness conditions then hold. For two colors take disjoint edges in a common part, using different edges also when the colors coincide. For a specified vertex and color, a color edge outside its matching edge avoids that vertex and both endpoints are nonneighbors. Every vertex is incident to a single color. The intrinsic set $P$ is all edges, since covering every vertex with odd degree requires its unique incident edge.

For a family with an arbitrary odd number $r$ of colors, use $2c$ matching edges in the first part and $2c+1$ in the second for color $c=1,\ldots,r$. The dimensions are $a=2r(r+1)$ and $b=2r(r+2)$. The signatures are distinct, and each color has odd total count. Thus every automorphism has sign one by (3), and reversing one raw output-basis vector gives ordinarily isomorphic algebras with only determinant $-1$ transporters. The label dimension is $a+b+ab+r$ and the relation dimension is $\binom a2+\binom b2-r$, both quadratic in $a+b$. Total algebra dimension is even. Replacing the second part count $2c+1$ by $2c+2$ makes every color count even and gives instances with an unbounded number of line multipliers in the triangular product construction.

On matching inputs the determinant decision has a direct polynomial-time solution even if some signatures repeat. For each of the at most two dimension-preserving alignments of the parts, compare multisets of ordered color counts in the aligned parts. Ordinary isomorphism for that alignment is equivalent to equality of these multisets. Indeed choose a matching of colors of equal profiles, biject their edges separately in both parts, and choose endpoint signs independently on each edge. This satisfies (2) for arbitrary specified color scalars. There are no further constraints because the diagonals and full cross space automatically transport.

For such an alignment, the determinant formula acquires the additional sign of the permutation of the quotient colors, computed in any chosen color order on each input. It uses $P$ equal to all edges. If any color has even total count, its freely chosen scalar changes the determinant. If some ordered count profile repeats, exchanging two assignments with that profile changes the color permutation sign while all the other factors can be held fixed. Otherwise the matching of profiles is unique and all scalar exponents vanish, so the one possible sign is given by the frame ratio, the two edge products, the part flip, and the permutation of colors. This computes exactly the attainable signs by testing the at most two alignments.

The proofs are informal. An unrestricted compiler for two scalar centroids would settle the ternary one-sign question by the earlier normal form. The present construction addresses the stated graph and matching classes. [Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)
