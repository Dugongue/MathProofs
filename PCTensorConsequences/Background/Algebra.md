# Quadratic recovery from the output matrix of an algebra isotopy

Let $A,B$ be finite-dimensional associative unital algebras over a field $K$. Their multiplications, units and bases are fixed. Write an isomorphism of their ordinary, unpartitioned multiplication tensors as an isotopy
$$
Z(ab)=X(a)Y(b).
$$
The input gives two-sided inverse variables $X',Y',Z'$ for all three matrices. There are substitutions of **degree two**, using only $Z,Z'$, that produce an algebra isomorphism and its inverse. Every substituted algebra axiom has an ordinary Polynomial Calculus (PC) derivation of degree at most five, uniformly in the field and the dimensions. This improves the degree-five reverse substitution in the earlier project proof. The underlying correspondence between unital associative isotopy and isomorphism is classical. [Earlier graph-tensor PC comparison](https://github.com/Dugongue/MathProofs/blob/main/IsomorphismCrossoversRoundThree/proof-complexity.md)

### Recovering the left regular representation

For fixed $a\in A$, let $L_a$ denote left multiplication on $A$. Define
$$
D_a=ZL_aZ',\qquad E_a=XL_aX',\qquad
\alpha(a)=D_a(1_B),\qquad
\beta(b)=(Z'L_bZ)(1_A).
$$
The symbols $L_b$ in the last expression denote left multiplication on $B$. The reverse isotopy $Z'(xy)=X'(x)Y'(y)$ follows by substituting $X'(x),Y'(y)$ and applying $Z'$. Starting instead from the usual cubic tensor-action convention $Z(X'(x)Y'(y))=xy$, apply $Z'$ directly for the reverse isotopy, or substitute $x=X(a),y=Y(b)$ for the forward one. The largest degree for these conversions is five. All equations here are coefficient equations on fixed basis arguments. Substituting variable linear combinations into a bilinear equation means multiplying its coefficients by the two new coefficients and summing.

For $x,y\in B$, use the reverse isotopy and associativity in $A$ to write
$$
D_a(xy)=Z\big((aX'(x))Y'(y)\big)=(X(aX'(x)))y=E_a(x)y .
$$
The second equality is the forward isotopy and $YY'=I$. Taking $y=1_B$ gives $D_a=E_a$. Taking $x=1_B$ now gives $D_a=L_{\alpha(a)}$. Exchanging source and target proves $Z'L_bZ=L_{\beta(b)}$. These calculations after the initial conversions have degree at most four. For example, the two substitutions into the forward isotopy each contribute one linear coefficient.

The inverse identities for $Z,Z'$ give $D_aD_c=D_{ac}$, so evaluating the left-multiplication identity at $1_B$ gives $\alpha(a)\alpha(c)=\alpha(ac)$ in degree at most four. Also $D_{1_A}=I$, hence $\alpha(1_A)=1_B$. The inverse multiplicative and unit axioms follow by symmetry. From $Z'L_{\alpha(a)}Z=L_a$ one obtains $\beta(\alpha(a))=a$ by evaluation at $1_A$. The other composition follows identically. Conjugating a proven matrix identity here adds at most two variable factors. Every derivation consists of fixed-length matrix products, sums of coordinate equations and ordinary PC multiplications by variables. Its expanded size per axiom is polynomial in the displayed structure constants. No field equations on the witness entries are needed.

Conversely an algebra isomorphism and its given inverse provide $X=Y=Z$ and the corresponding inverse substitutions. This direction has substitution degree one.

### Reading the graph

For a loopless directed simple graph the Grigoriev algebra has idempotents $e_i$ and an arrow $r_{ij}$ for each arc. Its radical $R$ is spanned by the arrows, $R^2=0$, the quotient is the coordinate algebra on vertices, and $e_k r_{ij}=\delta_{ki}r_{ij}$, $r_{ij}e_k=\delta_{jk}r_{ij}$. Replace each undirected edge by both orientations for simple undirected graphs. [Original algebra result](https://www.mathnet.ru/eng/znsl3395) · [Grochow and Qiao](https://doi.org/10.1137/21M1441110)

Use as graph variable $p_{ui}$ the coefficient at $e_u$ of $\alpha(e_i)$, a quadratic polynomial in the original output witness and inverse. The commutator identity $r_{ij}=[e_i,r_{ij}]$ implies that $\alpha$ and $\beta$ preserve the arrow spans, since a commutator in a coordinate algebra vanishes. On the vertex quotients the induced inverse matrices $P,Q$ are unital and multiplicative. In a row, entries therefore sum to one, are idempotent and are pairwise orthogonal. Multiply $(PQ)_{uv}=\delta_{uv}$ by $p_{ui}$ and simplify to obtain $p_{ui}q_{iv}=\delta_{uv}p_{ui}$. The reverse calculation yields $q_{iu}p_{uj}=\delta_{ij}q_{iu}$. Their common specialization gives $q_{iu}=p_{ui}$ and supplies all the column axioms.

Let $W$ be the restricted arrow matrix with inverse $W'$. For a source arc $(i,j)$, put $w_{ab}=W_{(a,b),(i,j)}$. Multiplication by the endpoint idempotents gives $w_{ab}=p_{ai}w_{ab}=p_{bj}w_{ab}$. When $(u,v)$ is a target nonarc, every target arc $(a,b)$ differs from it in at least one endpoint. The column collisions then give $p_{ui}p_{vj}w_{ab}=0$. Multiply the $(i,j)$ diagonal entry of $W'W=I$ by $p_{ui}p_{vj}$ and sum to obtain $p_{ui}p_{vj}=0$. Using $\beta$ yields the opposite mismatch. This recovers all GI axioms, including for isolates. The earlier algebra-to-graph proof uses degree at most five in entries of the algebra isomorphism and inverse. The present quadratic substitution gives **degree at most ten** in the raw tensor equations. Forward graph-to-tensor substitution has degree at most two, using $P$ on vertices and $p_{ui}p_{vj}$ on directed edges. The comparison applies to pairs with equal numbers of vertices and arcs. [Detailed graph-axiom derivations](https://github.com/Dugongue/MathProofs/blob/main/IsomorphismCrossoversRoundThree/proof-complexity.md)

The degree two of this graph decoder is optimal for recovering the induced vertex permutation from every witness over $\mathbb F_3$ on any graph possessing a nontrivial automorphism. To see this, rescale $(X,Y,Z)$ to $(sX,tY,stZ)$ and rescale the inverse witnesses accordingly, independently for $s,t\in\{1,-1\}$. The decoded $ZL_aZ'$ and all its vertex entries remain fixed. Averaging any affine-linear polynomial in the six matrices over these four choices leaves only its constant term, since each matrix carries a nontrivial sign character and four is invertible. A coordinate recovered linearly and invariant under these gauges must therefore be constant on all witnesses. The identity witness and a graph automorphism give differing values for some vertex coordinate. This sharpness concerns recovery of the actual induced permutation.

### Recovery in larger algebras

The reverse substitution also extracts **arc existence in the ordinary quiver** of a split basic algebra, with a degree bound independent of its radical nilpotence index. Suppose the radical $R$ is the two-sided ideal generated by commutators, the split quotient is $K^n$, and fixed bases of $R$, $R^2$ and of the corners of the quotient bimodule $R/R^2$ are given. Use distinct vertices for distinct primitive idempotents of the split quotient and an arc $i\to j$ precisely when $e_i(R/R^2)e_j\ne0$. Parallel arrows are collapsed.

Every fixed radical basis element is a constant linear combination of $a[b,c]d$ since the algebra is unital. Its image under a multiplicative map has zero vertex projection, by the commutativity of the target quotient. Thus $R$ transports. Express each fixed basis element of $R^2$ as a sum of products of two radical elements to derive transport of $R^2$ as well. Both inverse maps are available, so the resulting matrices on $R/R^2$ are mutual inverses. The bimodule actions factor through $A/R$. Every chosen basis vector in a nonzero corner has the same two endpoint equations as $r_{ij}$. The diagonal inverse entry above, applied to any one basis vector in the source corner, detects the absence of the target corner. This proves the asserted decoder in absolute constant degree and polynomial size per axiom, using only products of bounded length. Fixed coordinate decompositions into the indicated spans can be found by linear algebra.

For example every path algebra of a finite loopless quiver truncated by all paths of length $d\ge2$ satisfies these hypotheses. Each arrow is a commutator with its initial idempotent, so all positive-length paths lie in the commutator ideal and the quotient is the vertex algebra. The extraction is uniform even when $d$ varies. The graph-to-algebra forward substitution above is for $d=2$.

### Finite witness check

Over $\mathbb F_3$, take two vertices with one arrow in each direction, with coordinates $(i,j,x,y)$ on the vertex and arrow spaces. Multiplication sends two tuples $(i,j,x,y),(k,l,s,t)$ to $(ik,jl,is+xl,jt+yk)$. The 36 units have $i,j\in\{1,-1\}$ and arbitrary $x,y$. For each pair of units $u,v$ and each of the identity and vertex-swap automorphisms $f$, take $X(a)=u f(a)$, $Y(a)=f(a)v$, $Z(a)=u f(a)v$. Direct arithmetic checked the tensor and decoded multiplication equations for every basis pair in these 2,592 witnesses, totaling 41,472 basis-pair checks. In every case $\beta\alpha$ fixed the basis, $\alpha(a)=u f(a)u^{-1}$ and the vertex quotient recovered $f$. The statements above are written proofs. The ordinary tensor used here is the bare multiplication tensor. Reversing separate FGS rank markers requires a separate argument. [Galesi, Grochow, Pitassi and She, Question 7.5](https://arxiv.org/html/2305.19320#S7.SS5)
