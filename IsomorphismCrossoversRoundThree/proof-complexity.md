# Low-degree Polynomial Calculus equivalence for Grigoriev graph tensors

**Theorem.** Over every field, the standard polynomial equations for Graph Isomorphism on a pair of finite simple graphs with equal numbers of vertices and edges, the algebra-isomorphism equations on their Grigoriev graph algebras, and the ordinary three-mode tensor-isomorphism equations on the bare multiplication tensors of those algebras reduce to one another in ordinary Polynomial Calculus (PC) with absolute constant substitution and derivation degrees. The reductions are explicit and use polynomial-size derivations for every substituted input equation. In particular, the graph algebra route preserves PC refutation degree in both directions up to constant factors and an additive constant. No inversion inference beyond ordinary PC is used.

This treats a concrete algebra route relevant to Galesi–Grochow–Pitassi–She Open Question 7.5. The algebra is Grigoriev's radical-square-zero graph encoding, and the tensor is the unaugmented multiplication tensor. This manuscript does not assert equivalence for the particular Futorny–Grochow–Sergeichuk compiler or for the other routes listed in that question. [Open Question 7.5](https://arxiv.org/html/2305.19320#S7.SS5) · [Grigoriev construction as recalled by Grochow–Qiao](https://arxiv.org/abs/1907.00309).

## 1. Encodings and degree accounting

For graphs $G,H$ with vertex labels $1,\ldots,n$, the graph equations use entries $p_{ui}$ of a source-to-target permutation matrix. Include the row and column sum equations, Boolean equations, collision equations for distinct entries in a row or column, and $p_{ui}p_{vj}=0$ whenever the adjacency statuses of $i,j$ and $u,v$ differ. These are the local graph equations of Galesi–Grochow–Pitassi–She. If one also uses $P A_G=A_H P$, it is derived by expanding
$$
\sum_{v,j}(A_G(j,i)-A_H(u,v))p_{uj}p_{vi}
$$
using the sums and local collisions. Unequal vertex or edge counts can be rejected as a combinatorial preliminary; the PC comparisons below concern pairs with equal counts.

For a graph $G$ let $D(G)$ consist of both ordered orientations of each undirected edge. The algebra $A_G$ has basis $e_i$ for vertices and $r_{ij}$ for $(i,j)\in D(G)$. Its products are
$$
 e_i e_j=\delta_{ij}e_i,\qquad
 e_k r_{ij}=\delta_{ki}r_{ij},\qquad
 r_{ij}e_k=\delta_{jk}r_{ij},\qquad
 r_{ij}r_{ab}=0.
$$
It is associative, since the radical span is a square-zero bimodule over the coordinatewise vertex algebra, and its unit is $\sum_i e_i$. Multiplicativity of a linear map $M:A_G\to A_H$ gives one quadratic coordinate identity for each pair of basis elements, and we include two-sided inverse equations for $M,M'$. Unit preservation may be included or derived. Indeed $E=M1$ satisfies $(L_E-I)M=0$ by multiplicativity, and multiplying by $M'$ gives $L_E=I$, so $E=1$. Conversely $M'$ is multiplicative by applying $M$ to $M'(a)M'(b)$ and reducing the two $MM'$ products, then applying $M'$. Deriving unit preservation uses degree at most three, and deriving inverse multiplicativity uses degree at most five: substitute two linear inverse images into the multiplication equation, which reaches degree four, and apply the inverse map once, which reaches degree five.

All matrix products, evaluations of linear maps, and coefficient identities below denote their coordinate expansions. A displayed product of a derived equation by a polynomial with constant-degree factors can be expanded and implemented by repeated variable multiplication, then linear combination. A replacement of one factor by a proved equal expression uses the difference times the remaining factors. Thus a fixed formula containing at most a bounded number of variable factors yields an ordinary PC derivation of bounded degree. Sums over matrix indices have polynomially many terms because the number of factors is bounded. Each displayed derivation below uses only such operations, with no multiplication of an unbounded number of matrices.

## 2. Graph equations yield algebra equations

Send the matrix of $M$ to $\operatorname{diag}(P,W)$, where
$$
W_{(u,v),(i,j)}=p_{ui}p_{vj}
\qquad\bigl((u,v)\in D(H),\ (i,j)\in D(G)\bigr).
$$
Send $M'$ to $\operatorname{diag}(P^{\mathsf T},W^{\mathsf T})$. The substitutions have degree at most two.

The vertex blocks are two-sided inverses by the row and column sums, Boolean equations, and collisions of $P$. For the directed-edge blocks, off-diagonal entries of $W^{\mathsf T}W$ vanish by row collisions in $P$ because distinct source ordered edges differ in at least one endpoint. The diagonal entries reduce by Boolean equations to $\sum_{(u,v)\in D(H)}p_{ui}p_{vj}$. Extend the sum to all ordered vertex pairs. Every extra term vanishes by adjacency mismatch, and the full sum is one by the two column sums. The same argument using row sums, with source and target swapped, gives $WW^{\mathsf T}=I$.

Vertex multiplication is preserved by row collisions and Boolean equations. For $e_k r_{ij}$, a target coefficient of the equation is
$$
 (p_{uk}-\delta_{ki})p_{ui}p_{vj}
$$
at the edge $(u,v)$; it vanishes by the collision in row $u$ or by Boolean idempotence. Right multiplication uses the same identity at target endpoint $v$. Radical multiplication is identically zero on both sides. Unit preservation follows from the row sums. All derivations have degree at most four.

## 3. Algebra equations yield graph equations

Write $P$ for the vertex-to-vertex block of $M$, $Q$ for that of $M'$, and $W,W'$ for their radical-to-radical blocks. First derive that the radical-to-vertex blocks vanish. In the source, $r_{ij}=[e_i,r_{ij}]$ for $i\ne j$. The vertex projection of a commutator in the target algebra is identically zero, since its vertex quotient is coordinatewise commutative. Subtracting the two applicable multiplication equations therefore gives a linear equality asserting that the vertex projection of $Mr_{ij}$ vanishes. The inverse map $M'$ gives the same equations in the other direction, using its derived multiplicativity. This argument uses an actual linear cancellation, rather than inferring that a nilpotent coordinate is zero from its square.

The two-sided inverse identities now restrict to $PQ=QP=I$ and $WW'=W'W=I$ by deleting terms containing the proved zero blocks. Vertex multiplication and units give, for both $P$ and $Q$, the row sums, idempotent entries, and collisions in each row. To recover columns of $P$, multiply $(PQ-I)_{ij}$ by $p_{ik}$. The resulting row-orthogonality identity is
$$
p_{ik}q_{kj}=\delta_{ij}p_{ik},
$$
because the $\ell\ne k$ summands $p_{i\ell}p_{ik}q_{\ell j}$ have row collisions and $p_{ik}^2=p_{ik}$. Apply the same reasoning to $QP-I$ using the known rows of $Q$. Multiplication of $(QP-I)_{kj}$ by $q_{ki}$ gives
$$
q_{ki}p_{ij}=\delta_{kj}q_{ki}.
$$
Use the two identities together as follows. For fixed $i,k$ take $j=i$ in the first identity, obtaining $p_{ik}q_{ki}=p_{ik}$. Take $j=k$ and the same $k,i$ in the second, obtaining $q_{ki}p_{ik}=q_{ki}$. Subtract to get $q_{ki}=p_{ik}$. This is a degree-three derivation. The rows of $Q$ are therefore the columns of $P$, providing column sums and collisions.

For adjacency, suppose $(i,j)\in D(G)$ but the target ordered pair $(u,v)$ is not in $D(H)$. Put $w_f=W_{f,(i,j)}$ for each $f=(a,b)\in D(H)$. Left and right multiplication of $r_{ij}$ by $e_i,e_j$ give
$$
(p_{ai}-1)w_f=0,\qquad (p_{bj}-1)w_f=0.
$$
No radical-to-radical correction from the images of the vertices survives because the radical squares to zero, and their images on the radical have no vertex component. For each target edge $f$, either $a\ne u$ or $b\ne v$. In the first case multiply the left equation by $p_{ui}$, subtract the column collision multiplied by $w_f$, and derive $p_{ui}w_f=0$. In the second case do the same with the right equation and $p_{vj}$. Thus in either case $p_{ui}p_{vj}w_f=0$ is available. Multiply the $(i,j),(i,j)$ diagonal entry of $W'W-I$ by $p_{ui}p_{vj}$ and subtract the sum of $W'_{(i,j),f}$ times these derived zero products. This yields $p_{ui}p_{vj}=0$. Using $M'$ and $Q=P^{\mathsf T}$ proves the opposite adjacency mismatch in the same degree. This includes diagonal nonedges. The substitutions for the graph variables are just the entries of $P$. The degree is at most five overall: inverse multiplicativity can use five, while radical preservation after it, the inverse-block equations, the transpose equations, and the adjacency test use at most four.

## 4. Unital associative algebra isomorphism versus ordinary multiplication-tensor isomorphism

This step works for any two finite-dimensional unital associative algebras $A,B$ of equal dimension over any field. Represent their multiplication tensors in the two input-dual modes and one output mode. Independent invertible transformations on the modes, with inverse witnesses, encode an isotopy. It is convenient to use the equivalent equations
$$
 Z(ab)=X(a)Y(b)
 \tag{1}
$$
on basis pairs, where $X,Y,Z:A\to B$ are independent and $X',Y',Z'$ are their inverses. Indeed the ordinary cubic tensor action in inverse-transposed input coordinates reads
$$
 Z\bigl(X'(c)Y'(d)\bigr)=cd.
$$
Substitution of $c=X(a),d=Y(b)$ turns these equations into (1), after reducing $X'X$ and $Y'Y$. The reverse multiplies in the other direction and uses $XX'$ and $YY'$. Each substitution amounts to multiplying a bilinear coordinate equation by two matrices and then reducing two inverse identities. The maximum degree is at most five from the cubic convention to (1), and at most four in the other direction. Exchanging the variables for a map, its inverse or its transpose is linear.

An algebra isomorphism gives an isotopy by $X=Y=Z=M$ and $X'=Y'=Z'=M'$, a degree-one substitution. To extract an algebra isomorphism in the other direction, let
$$
 u=X(1_A),\quad v=Y(1_A),\quad
 u'=Y Z'(1_B),\quad v'=X Z'(1_B).
$$
Equation (1) gives $Z=L_uY=R_vX$, where $L_u,R_v$ are left and right multiplication in $B$. Multiply these equations by the inverse witnesses, and reduce $YY'=XX'=I_B$, to see $L_u=ZY'$ and $R_v=ZX'$. In particular their inverse identities with $YZ'$ and $XZ'$, respectively, follow by reducing the two-sided inverse products for $X,Y,Z$. Evaluating $L_uYZ'=I_B$ and $R_vXZ'=I_B$ at $1_B$ gives $uu'=1$ and $v'v=1$.

Both inverse equations also hold in the other order in ordinary PC. For example, associativity gives
$$
 L_u(u'u-1)=(uu'-1)u,
$$
so multiply the derived right-hand-side zero by $YZ'$, and reduce $(YZ')L_u=I_B$. This gives $u'u=1$. Right multiplication by $v$, followed by $XZ'$, similarly gives $vv'=1$. These derivations have bounded degree even though a one-sided matrix inverse principle for arbitrary matrices would be harder in PC, because both linear inverse identities used here were derived from existing witnesses.

Now define polynomial substitutions
$$
 M(a)=u'Z(a)v',
 \qquad M'(b)=Z'(u b v).
$$
The degrees are at most five and three, respectively. Composing these maps and using the inverse equations for the units and for $Z$ gives $MM'=I_B$ and $M'M=I_A$. Equation (1) at the units gives $M(1_A)=1_B$. Also $X(a)=Z(a)v'$ and $Y(b)=u'Z(b)$, since $Z=R_vX=L_uY$. Therefore
$$
 M(ab)=u'X(a)Y(b)v'=u'Z(a)v' u'Z(b)v'=M(a)M(b),
$$
using (1) and associativity. Here are explicit bounds for this extraction. Deriving the linear-multiplication inverse identities reaches degree at most four, from products such as $YZ'ZY'$. Evaluating them gives the first unit-inverse identities in degree at most three. Reversing those unit identities reaches degree at most six, from multiplying an equation of degree at most four by $YZ'$ or $XZ'$. The candidate map and its inverse have degrees at most five and three, so composing and successively replacing the inverse pairs uses degree at most eight. The two formulae for $X(a)$ and $Y(b)$ use degree at most four. In the multiplicativity calculation the last expression has degree ten, and replacing one factor at a time keeps every intermediate in degree at most ten. Unit preservation uses degree at most six, from multiplying the degree-two unit instance of (1) by both inverse units. Expanding gives polynomially many terms in each substituted equation derivation.

## 5. Consequences and scope

The two pairs of reductions compose. For degree, a variable multiplication after a polynomial substitution of degree at most $d$ is simulated by expanding that multiplier and doing $d$ ordinary variable multiplications per monomial. The composite deriving bare tensor axioms from graph axioms has substitution degree at most two and derivation degree at most eight. The reverse composite has substitution degree at most five and derivation degree at most twenty-five. Thus an original degree bound grows by at most a constant factor and the explicit constant cost of deriving the substituted original axioms. All steps are uniform in graph size and field characteristic. The forward substitution from graph variables into bare tensor witnesses replaces each tensor witness entry by a variable, a quadratic monomial, or zero. Therefore any tensor refutation transfers back to a graph refutation with polynomial overhead in sparse proof size, even at unbounded degree. The reverse substitution is generally dense, and the argument for it bounds degree and per-axiom simulation size.

The result gives a bidirectional PC comparison between a standard GI presentation and a bare multiplication-tensor GI presentation. It is an informal proof. The algebra reduction is classical, as is the set-theoretic passage from isotopy to isomorphism for unital associative algebras. The contribution is the constant-degree ordinary-PC simulation in both directions, including the two-sided inversion and adjacency conditions. Targeted comparison did not establish publication priority for this exact presentation.
