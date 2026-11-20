# When every rank-metric code isometry extends

## Statement and relation to the literature

For positive integers $m,n$ and any prime power $q$, every $\mathbb F_q$-linear rank isometry between subspaces of $\operatorname{Mat}_{m,n}(\mathbb F_q)$ extends to a linear rank isometry of the ambient space if and only if $\min(m,n)=1$ or $(q,m,n)=(2,2,2)$. In every other parameter choice there is a nondegenerate code with a nonextendable linear self-isometry. Here nondegeneracy means that both the common left kernel and the common right kernel of the code are zero.

Santonastaso and Zullo ask in §6 whether the extension theorem holds for nondegenerate rank or sum-rank metric codes. Earlier examples already give a negative answer. Gorla and Salizzoni’s Example 2.4 uses square MRD codes containing full-rank words. Those codes are nondegenerate by Corollary 3.6 of the question’s source. The contribution here is an exact classification for a single matrix block, with nondegenerate witnesses in every negative format. Publication priority for that classification has not been established. [Santonastaso and Zullo, *Invariants for sum-rank metric codes*](https://link.springer.com/article/10.1007/s10231-025-01640-6) · [Gorla and Salizzoni, *MacWilliams’ Extension Theorem for rank-metric codes*, §2](https://arxiv.org/html/2304.13341#S2)

## The two positive cases

If $\min(m,n)=1$, every nonzero matrix has rank one. Extend any given linear isomorphism of subspaces by completing a basis in each space. The resulting ambient map preserves rank.

For $2\times2$ matrices over $\mathbb F_2$, let $Q(X)=\det X$. In coordinate order $X=(a,b,c,d)$, this is $ad+bc$. Its polar bilinear form is alternating and nondegenerate. A linear injection preserves rank on its domain precisely when it preserves $Q$, since the determinant determines the rank of a nonzero $2\times2$ binary matrix.

Extend the given map from a subspace $U$ to a polar-form isometry $g$ of the ambient space by alternating Witt extension. Write $B$ for the polar form. Since $g$ preserves $B$, the function $Q(gx)+Q(x)$ is linear over $\mathbb F_2$. There is a unique $v$ with $Q(gx)+Q(x)=B(v,x)$, and $B(v,U)=0$. The sum $\sum_x(-1)^{Q(x)}$ is nonzero. In fact $Q=ad+bc$ separates into two binary hyperbolic pairs, each giving sum $2$. Since $g$ is a permutation and $x\mapsto x+v$ is a translation,
$$
\sum_x(-1)^{Q(x)}
  =\sum_x(-1)^{Q(x)+B(v,x)}
  =(-1)^{Q(v)}\sum_x(-1)^{Q(x)}.
$$
Hence $Q(v)=0$. The map $t_v(x)=x+B(v,x)v$ is an invertible linear involution fixing $U$. It satisfies $Q(t_vx)=Q(x)+B(v,x)$ and $B(v,t_vx)=B(v,x)$. Therefore $gt_v$ preserves $Q$ and extends the original map. Alternating Witt extension is the same extension step used for the finite-field tensor-isomorphism arguments in MathProofs.

## A nondegenerate witness in every other format

Transpose at the outset if necessary so $2\le m\le n$. Let $K=\mathbb F_{q^n}$, write $\operatorname{Tr}$ for its trace to $\mathbb F_q$, and choose an $m$-dimensional subspace $W\le K$ with basis $w_1=1,w_2=\theta,w_3,\ldots,w_m$, where $\theta$ generates $K$ over $\mathbb F_q$. Define a matrix code by
$$
X(a)\colon K\longrightarrow\mathbb F_q^m,\qquad
x\longmapsto\bigl(\operatorname{Tr}(a w_i x)\bigr)_{i=1}^m,\qquad a\in K.
$$
For every $a\ne0$, the $m$ row functionals are linearly independent by the nondegenerate trace pairing and independence of the $w_i$. Thus $X(a)$ has rank $m$, and $a\mapsto X(a)$ is injective. These matrices have no common left kernel. The first coordinate has no common right kernel as $a$ varies, again by the trace pairing. Every linear bijection $D:K\to K$ thus induces a rank-metric self-isometry $X(a)\mapsto X(D(a))$ of a nondegenerate code.

The Hua–Wan classification gives the ambient linear isometries as $M\mapsto PMQ$, with the additional possibility $M\mapsto PM^\top Q$ when $m=n$. In the square case choose the domain basis of $K$ to be $w_1,\ldots,w_n$. Each $X(a)$ is symmetric in these coordinates, so transpose adds no induced code maps. [Gorla and Salizzoni, Theorem 1.3](https://arxiv.org/html/2304.13341#S1)

Suppose $PX(a)Q=X(D(a))$ for all $a$. Let $\sigma_Q$ be the adjoint of $Q$ under the trace pairing. Put $u_i=\sum_j P_{ij}w_j$. Comparison of the row functionals gives
$$
\sigma_Q(a u_i)=D(a)w_i.
$$
The equation at $i=1$ is $\sigma_Q(a u_1)=D(a)$. Writing $L_b$ for multiplication by $b$ on $K$, the equations imply
$$
D L_{u_i/u_1}D^{-1}=L_{w_i}.
$$
The ratios $u_i/u_1$ span $W/u_1$ over $\mathbb F_q$. The field they generate contains $1/u_1$ and $\theta/u_1$, hence contains $\theta$ and is all of $K$. The $w_i$ also generate $K$. Conjugation by $D$ therefore normalizes the algebra $\{L_b:b\in K\}$ and induces an $\mathbb F_q$-automorphism $\sigma$ of $K$. Applying $D L_b = L_{\sigma(b)}D$ to $1$ gives $D(b)=c\sigma(b)$, where $c=D(1)\ne0$.

More precisely, the extendable maps are exactly $D(b)=c\sigma(b)$ with $c\in K^\times$ and $\sigma(W)$ a nonzero scalar multiple of $W$. The row equations imply $W=u_1\sigma^{-1}(W)$. Conversely, given that equality, set $u_i=u_1\sigma^{-1}(w_i)$, use the basis change from $(w_i)$ to $(u_i)$ for $P$, and choose $Q$ with trace adjoint $D L_{u_1}^{-1}$. These data satisfy every row equation.

The full group of internal linear maps has order
$$
|\operatorname{GL}_n(q)|=(q^n-1)\prod_{i=1}^{n-1}(q^n-q^i).
$$
At most $n(q^n-1)$ extend. The product is greater than $n$ when $n\ge 3$, since its last factor alone is $q^{n-1}(q-1)>n$. When $n=2$, it is $q(q-1)>2$ for $q>2$. This proves the claimed failure in every remaining format.

## Two individually extendable blocks can fail together

Two binary $2\times2$ blocks already give a nondegenerate counterexample for sum-rank distance. Parameterize each code by $(a,b)\in\mathbb F_2^2$, in the nonzero order $(1,0),(0,1),(1,1)$. In one code, the first block is the regular $\mathbb F_4$ multiplication representation of $a+b\theta$, and the second block is $\operatorname{diag}(a,b)$. Their respective rank triples are $(2,2,2)$ and $(1,1,2)$. In the other code, take the respective blocks $a E_{12}+bI$ and $aI+bE_{12}$. Their rank triples are $(1,2,2)$ and $(2,1,2)$. Both codes have total rank triple $(3,3,4)$. Each projection contains an invertible matrix, which gives nondegeneracy. The map that keeps $(a,b)$ fixed is a linear isometry between the codes. Any full ambient extension would act by rank isometries in the individual blocks and a block permutation. This would preserve the multiset of the two rank triples, which differs. [Santonastaso and Zullo, Theorem 3.2 and Corollary 3.9](https://link.springer.com/article/10.1007/s10231-025-01640-6)

The arguments are informal.
