# Tensor isomorphism in global dimension two

**Theorem.** Over any field $k$, ordinary three-tensor isomorphism has a deterministic polynomial-time many-one reduction to testing $k$-linear derived equivalence of finite-dimensional algebras of global dimension exactly two given by dense multiplication tables. The outputs are split basic, have three simple modules and center $k$, and have the same Cartan matrix whenever the intermediate algebras have the same dimension. On the image family, derived equivalence and algebra isomorphism coincide, so the promised comparison problem is TI-complete. This is an informal proof.

A three-vertex algebra $A(B)$ of global dimension two encodes any finite-dimensional commutative unital $k$-algebra $B$ of dimension at least two in the Lie bracket on its first Hochschild cohomology. The construction also works in characteristics two and three.

## 1. The three-vertex algebra

Put $d=\dim_k B\ge 2$. Let $m$ be the first member of $\{d+3,d+4\}$ that is nonzero in $k$, and put $W=B^m$. The integer $m$ exists in every characteristic and satisfies $m\ge 5$. Form $A=A(B)$ with diagonal corners $ke_s,ke_x,ke_y$ and strict off-diagonal corners
$$
e_xAe_s=W_X,\qquad e_yAe_x=B,\qquad e_yAe_s=W_Y.
$$
Here $W_X,W_Y$ are copies of $W$. The only nonzero product of two strict corners is
$$
B\times W_X\longrightarrow W_Y,\qquad (b,w)\longmapsto bw.
$$
The diagonal acts by scalars at the indicated ends, and $e_s+e_x+e_y$ is the unit. The multiplication is associative by the corner rule and because a triple of strict corners has zero product under either parenthesization. An isomorphism $B\cong B'$ acts on the $B$-corner and entry by entry on both $W$-corners, yielding $A(B)\cong A(B')$. Equivalently, this is the one-point extension of the $d$-arrow Kronecker algebra by the representation on $W_X,W_Y$ whose arrows act by left multiplication by a basis of $B$.

The sum $J$ of strict corners is nilpotent, with $J^2=W_Y$ because $B$ has a unit, and $J^3=0$. Since $A/J=k^3$, this is the Jacobson radical and the algebra is split basic with three simples. A central element must commute with the three idempotents and therefore be diagonal. Commuting with $W_X$ and $B$ forces equality of its three diagonal scalars. Thus the center is $k$. With entries $\dim_k e_iAe_j$ in vertex order $s,x,y$, the Cartan matrix is
$$
\begin{pmatrix}
1&0&0\\
md&1&0\\
md&d&1
\end{pmatrix}.
$$
The transpose gives the other convention. The matrix depends only on $d$ and the characteristic.

For global dimension, write $P_i=Ae_i$ and $S_i=P_i/JP_i$. Then $P_y=S_y$ and $JP_x\cong P_y^{\,d}$. Multiplication gives a surjective $A$-map
$$
P_x\otimes_k W_X\longrightarrow JP_s,\qquad a\otimes w\longmapsto aw.
$$
On the $x$-component this is the identity of $W_X$, and on the $y$-component it is the surjection $B\otimes_k W_X\to W_Y$. The kernel is $P_y^{(d-1)\dim_k W}$. Thus $S_s$ has a projective resolution of length two and every simple has projective dimension at most two. Also $JP_s$ is nonprojective. Otherwise the displayed surjection would split with its nonzero kernel a direct summand of $P_x\otimes_k W_X$ lying inside its radical. The top of a nonzero direct summand is nonzero and the tops add under a direct sum, which precludes such a summand. Thus $S_s$ has projective dimension exactly two. Over a finite-dimensional algebra, global dimension is the maximum of the projective dimensions of the simple modules, so the global dimension is exactly two.

## 2. The first Hochschild Lie algebra

Let $\mathfrak h(B)=HH^1(A(B))$, with the Lie bracket given by the commutator of derivations modulo inner derivations. Every derivation is represented modulo inner derivations by one vanishing on the $e_i$. For a derivation $\Delta$, take $t=\sum_i\Delta(e_i)e_i$. Differentiating the idempotent and orthogonality identities gives $[t,e_i]=\Delta(e_i)$, so subtracting $[t,-]$ gives the required representative. A derivation vanishing on the idempotents preserves every corner and vanishes on their scalar spans. An inner derivation vanishes on all the $e_i$ exactly when its inducing element is diagonal, since that is their common centralizer.

Identify the two copies of $W$ with $B^m$. Write $P,Q,R$ for the corner endomorphisms on $W_X,W_Y,B$, and write $L_b$ for multiplication by $b$ on $W$. The only product condition to check is
$$
QL_b-L_bP=L_{R(b)}\qquad(b\in B).
$$
Let $a=R(1)$. Evaluating at $1$ gives $Q=P+L_a$, and consequently
$$
[P,L_b]=L_{\delta(b)},\qquad \delta(b)=R(b)-ab.
$$
The map $b\mapsto L_b$ is faithful and multiplicative. Applying the commutator identity to $L_bL_c$ shows that $\delta$ is a $k$-derivation of $B$. Its entrywise action $\delta_W$ on $W$ has the indicated commutators with all $L_b$. Thus $D=P-\delta_W$ is $B$-linear and lies in $M_m(B)=\operatorname{End}_B(B^m)$. Conversely each choice of $D\in M_m(B)$, $a\in B$, and $\delta\in\operatorname{Der}_k(B)$ gives a derivation by these formulas. Inner diagonal derivations account for independently adding elements of $kI_m$ to $D$ and $k1$ to $a$. The three diagonal scalars $t_s,t_x,t_y$ give $D=(t_x-t_s)I_m$, $a=(t_y-t_x)1$, and $\delta=0$.

It follows that
$$
\mathfrak h(B)\cong
\left((\mathfrak{gl}_m(B)/kI_m)\oplus (B/k1)\right)\rtimes\operatorname{Der}_k(B).
$$
The $B/k1$ summand is abelian and commutes with the matrix summand. The derivation part acts on both by applying the derivation to entries. These operations follow by taking the commutator of the operators $P=\delta_W+D$ and $R=\delta+L_a$. In particular $S(B)=\mathfrak{sl}_m(B)$ embeds as a Lie ideal. The embedding is injective since $m$ is invertible in $k$, and trace annihilates matrix commutators and commutes with entrywise derivations. Its codimension in $\mathfrak h(B)$ is $2d-2+\dim_k\operatorname{Der}_k(B)\le d^2+2d-2$.

## 3. Recovering $B$ intrinsically

The integer $d$ is determined by the dimension of $\mathfrak h(B)$ with the base field fixed. For each $d$, its possible dimensions lie in
$$
[(m(d)^2+1)d-2,\ (m(d)^2+1)d-2+d^2].
$$
These intervals are disjoint in increasing order. Indeed $m(d+1)\ge m(d)$, so the next lower endpoint exceeds the current lower endpoint by at least $m(d)^2+1>d^2$.

With $d$, hence $m$, determined, $S(B)$ is the intersection of the Lie ideals of $\mathfrak h(B)$ of codimension less than $m^2-1$. The constant-matrix subalgebra $\mathfrak{sl}_m(k)\subseteq S(B)$ has dimension $m^2-1$, so every such ideal intersects it nontrivially. The intersection is an ideal of $\mathfrak{sl}_m(k)$ and hence contains all of it by simplicity. Taking brackets with $S(B)$ gives all of $S(B)$, by perfectness of $\mathfrak{sl}_m(k)$ and $S(B)=\mathfrak{sl}_m(k)\otimes_k B$. Also $S(B)$ itself has codimension $<m^2-1$, by the bound above and $m\ge d+3$.

For completeness, $\mathfrak{sl}_m(k)$ is absolutely simple for the indicated $m$. Over an algebraic closure choose a trace-zero diagonal matrix with distinct nonzero adjoint weights on the off-diagonal units, except that in characteristic two opposite units have the same weight. Each excluded equality defines a proper hyperplane on the trace-zero diagonals. A difference of two weight vectors is supported on at most four coordinates, so it can vanish on all trace-zero diagonals only if it is zero, since $m\ge 5$. Any nonzero ideal contains a nonzero weight component, by polynomial projection along this adjoint action. A nonzero diagonal component yields an off-diagonal unit by taking a bracket, since the only trace-zero scalar is zero. In characteristic two a nonzero component $aE_{ij}+bE_{ji}$ gives a nonzero multiple of $E_{i\ell}$ by bracketing with $E_{j\ell}$ if $a\ne0$, where $\ell\notin\{i,j\}$. If $b\ne 0$ the same argument interchanges $i,j$. Starting from $E_{ij}$, bracketing with $E_{j\ell}$, then $E_{ji}$, then $E_{\ell i}$ gives $E_{i\ell},E_{j\ell},E_{ji}$, up to signs. Further brackets yield the other off-diagonal units and the diagonal differences. This proves simplicity after extending scalars. The matrix-unit brackets also prove perfectness.

For a Lie algebra $S$, its centroid is the algebra of $k$-linear endomorphisms $c:S\to S$ satisfying
$$
c([u,v])=[c(u),v]=[u,c(v)].
$$
The centroid of $S(B)$ is $B$ as a unital associative algebra. Absolute simplicity gives $\operatorname{End}_{\mathfrak{sl}_m(k)}(\mathfrak{sl}_m(k))=k$, by Schur's lemma over an algebraic closure and scalar descent. Every centroid map commutes with the adjoint action of the constant matrices, so expansion along a basis of $B$ makes it $1\otimes f$ for some $k$-linear $f:B\to B$. Applying the centroid identity to $u\otimes b$ and $v\otimes b'$ with $[u,v]\ne0$ gives $f(bb')=f(b)b'$. Thus $f(b')=f(1)b'$, and conversely every such multiplication is a centroid element. Composition recovers multiplication in $B$.

It follows that an isomorphism $\mathfrak h(B)\cong\mathfrak h(B')$ yields $B\cong B'$. This implication uses the ideal intersection mathematically. Computing the intersection is unnecessary for the reduction.

## 4. Derived equivalence and computational bounds

An exact $k$-linear equivalence of bounded derived categories of finite-dimensional modules over $A(B)$ and $A(B')$ gives an isomorphism of their Hochschild cohomology respecting the Gerstenhaber bracket. Finite global dimension identifies the bounded categories with the perfect categories, and Rickard's derived Morita theorem supplies a two-sided tilting equivalence from the resulting tilting complex. Keller's derived invariance then applies. Its degree-one restriction is the Lie isomorphism examined above. Conversely $B\cong B'$ gives an algebra isomorphism of the output tables and hence a derived equivalence. [Rickard, *Morita theory for derived categories*](https://doi.org/10.1112/jlms/s2-39.3.436) · [Keller, *Derived invariance of higher structures on the Hochschild complex*](https://webusers.imj-prg.fr/~bernhard.keller/publ/dih.pdf).

The dimension of $A(B)$ is $3+d+2md=O(d^2)$. Build its dense table by placing entries from the table of $B$ into the $m$ copies of its module action and writing structural zeros and ones. This is polynomial time for explicit field coordinates, including the usual binary presentations of finite fields and $\mathbb Q$. Selecting $m$ tests only whether bounded integers vanish in $k$.

Grochow and Qiao's TI-completeness theorem gives a deterministic polynomial-time many-one reduction from tensor isomorphism over $k$ to isomorphism of commutative unital associative $k$-algebras. We can restrict the comparison to dimension at least two. Different dimensions give a negative answer, and the sole unital one-dimensional $k$-algebra is $k$. These preliminary cases can be mapped to fixed positive or negative pairs in our family, using $k\times k$ and $k[t]/(t^2)$ for the negative pair. Compose the published reduction with $B\mapsto A(B)$. The earlier MathProofs tensor-to-commutative-algebra encoding also gives a composition, with a fixed Cartan matrix for each tensor format. [Grochow–Qiao, Theorem B and Corollary 6.5](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full).

For the reverse reduction on the promised family, take the multiplication tensor of each input algebra. Unital associative algebra isomorphism is equivalent to isotopy of multiplication. Indeed, if invertible linear maps $f,g,h:C\to C'$ satisfy $h(xy)=f(x)g(y)$, set $a=f(1)$ and $b=g(1)$. The identities $h(x)=f(x)b=a g(x)$ make right multiplication by $b$ and left multiplication by $a$ bijective, so $a,b$ are units. Substitution gives $h(xy)=h(x)(ab)^{-1}h(y)$, and hence $x\mapsto (ab)^{-1}h(x)$ is a unital algebra isomorphism. The converse uses the same isomorphism in all three slots. This gives a polynomial-time reverse reduction to ordinary TI.

## 5. Sharpness for objectwise polynomial-size encodings

Over a fixed finite field $\mathbb F_q$, global dimension two is the smallest possible bound for an objectwise polynomial-size encoding into split basic algebras with a fixed bound on the number of simples. Split basic hereditary finite-dimensional algebras are path algebras of acyclic quivers. For at most $r$ vertices and dimension at most $M$, there are at most $(r+1)(M+1)^{r^2}$ labelled directed multiplicity tables. The number of derived-equivalence classes in that collection is at most the same number. But $n\times n\times n$ tensors have at least $q^{n^3-3n^2}$ isomorphism classes, since the group acting on $q^{n^3}$ tensors has order at most $q^{3n^2}$. If $M$ is polynomial in $n$, a comparison-preserving encoding would inject the latter class set into the former, an impossibility for large $n$. This concerns objectwise encodings, which give one algebra per tensor. [Iyama, *Algebras of finite global dimension and special Cohen–Macaulay modules*, Example 1.1](https://nagoya.repo.nii.ac.jp/record/10442/files/Iyamalecture.pdf).

## 6. A TI-complete family of perfect Lie algebras

Fix $m_0=5$ when $5$ is nonzero in $k$ and $m_0=6$ otherwise. Over each $k$, Lie algebra isomorphism is TI-complete even when both input algebras are centerless and perfect and each has a solvable radical of nilpotency class exactly two, split off by a complement isomorphic to the fixed split simple Lie algebra $\mathfrak{sl}_{m_0}(k)$.

The commutative 3-nilpotent encoding of Grochow and Qiao yields local unital encodings $B=k\oplus I$ by adjoining a unit, with $I^3=0$ and $I^2\ne0$. In detail, their construction starts from symmetric matrix-space isometry, takes a linearly independent basis of the slice space, and makes the codomain of the bilinear product an annihilated summand. A nonzero slice space gives $I^2\ne0$. Cases involving a zero slice space can be decided during the reduction and sent to fixed positive or negative pairs using $k[t]/(t^3)$ and $k[t,u]/(t^3,u^2,tu)$. The ideal $I$ is the Jacobson radical of $B$, so adjoining the unit preserves and reflects isomorphism of the encodings. [Grochow–Qiao, Theorem B and Corollary 6.5](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full).

Put $L=\mathfrak{sl}_{m_0}(k)$ and output the bracket table of $L\otimes_k B$, with bracket $[x\otimes b,y\otimes c]=[x,y]\otimes bc$. Section 3 identifies $B$ with its centroid. Conversely a coefficient-algebra isomorphism $B\cong B'$ gives an isomorphism of the Lie algebras. These Lie algebras are perfect since $L=[L,L]$ and $B$ has a unit. They are centerless since an element of the center commutes with $L\otimes 1$, and $L$ is centerless. The ideal $L\otimes I$ has commutator ideal $L\otimes I^2\ne0$ and its third lower-central term vanishes. It is the entire solvable radical, since every solvable ideal maps to zero in the nonsolvable simple quotient $L$. The copy $L\otimes1$ splits the quotient. The output Lie dimension is $(m_0^2-1)\dim B$. The reverse comparison reduction is the published reduction from algebra isomorphism to ordinary TI. [Grochow–Qiao, Theorem B](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full).

## Relationship to prior work

One-point extensions, invariance of the Gerstenhaber bracket and split simple matrix Lie algebras are standard. The combination here chooses a replicated regular representation whose Hochschild Lie algebra contains an intrinsic ideal with centroid $B$, even though the three-vertex algebra itself has scalar center. The earlier MathProofs dimension-three construction used the center of an Auslander–Dlab–Ringel algebra. A focused literature search found the standard one-point-extension Hochschild sequence and did not locate this comparison reduction. Publication priority remains unestablished.
