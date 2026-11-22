# Minimal finite quotients separating nilmanifold loops

**Theorem.** Fix an odd prime $p$ and $s\ge1$. From an affine matrix pencil
$$
A(t)=A_0+\sum_{i=1}^m t_i A_i,\qquad t\in\mathbb F_p^m
$$
one can construct in polynomial bit time a torsion-free integral class-two nilpotent group $\Gamma$ by an explicit lattice and commutator tensor. It has elements $g,h$ that are not conjugate in $\Gamma$ and are conjugate in its real Mal'cev completion. Put $r_*=\min_t\operatorname{rank}A(t)$. For a specified integer $D$ linear in the pencil dimensions, the smallest order of any finite quotient in which $g,h$ remain nonconjugate is exactly
$$
p^{\,s+2(D+1+r_*)}.
$$
The optimizing quotient can be chosen of exponent dividing $p^s$. No prime or exponent restriction is imposed when taking the minimum. In the associated compact nilmanifold the two elements give different free-loop components with representatives of Lipschitz constant at most $2p^s$ for the specified metric. Equivalently, the formula computes the smallest finite group $Q$ that can distinguish those components by a map from the nilmanifold to $K(Q,1)$.

The bounded-order decision problem is NP-complete on these explicit inputs. On a subfamily from a 3-CNF formula, the number of normal kernels of the indicated order that distinguish the two components is a known power of $p$ times the number of satisfying assignments. Thus exact counting of separating kernels on this subfamily is $\#\mathrm P$-complete under a single numerical postprocessing reduction.

The arithmetic quantity is a choice of scalar projections of a Grochow–Qiao commutator tensor. The geometric viewpoint is the distinction between free-loop components in the lattice and real conjugacy orbits underlying the class-two persistence calculation. [Grochow–Qiao, tensor and class-two group isomorphism](https://arxiv.org/abs/1907.00309) · [Block–Manin–Weinberger, Question 1.4](https://arxiv.org/html/2505.16907v2#S1.SS3)

## Integral group and its two loop classes

Let $W=\mathbb Z z\oplus\bigoplus_{i=1}^m\mathbb Z w_i$. The alternating commutator tensor $\beta:\bigwedge^2 V\to W$ is specified by its scalar alternating form for a linear functional $\lambda$ on $W$. Write $\lambda_0=\lambda(z)$ and $\lambda_i=\lambda(w_i)$. Use a rectangular integer lift of each $A_i$, including $A_0$, and write
$$
C_\lambda=\lambda_0 A_0+\sum_i\lambda_i A_i,\qquad
P_\lambda=\lambda_0 I_D+\sum_i\lambda_i J_D^i ,
$$
where $J_D$ is the single nilpotent upper shift and $D>2m+1+\min(\#\text{rows of }A,\#\text{columns of }A)$. For any rectangular matrix $M$, write
$$
\mathcal A(M)=\begin{pmatrix}0&M\\-M^{\mathsf T}&0\end{pmatrix}.
$$
Define $\lambda\beta$ by the block diagonal matrix
$$
p^{s-1}\!\left(\mathcal A(C_\lambda)\oplus\mathcal A(P_\lambda)\oplus
\mathcal A([\lambda_0])\right).
$$
This is a linear prescription in $\lambda$ and so defines the integral tensor itself. Let $d=\operatorname{rank}V$. Denote the ordered basis of the final two-dimensional block by $x,y$, so $\beta(x,y)=p^{s-1}z$.

Choose an integral bilinear form $B:V\times V\to W$ with $B-B^{\mathsf T}=\beta$, for instance the strictly upper triangular part in the displayed ordered basis. Put a group law on $V\oplus W$ by
$$
(v,w)(v',w')=(v+v',w+w'+B(v,v')).
$$
Its commutator, with convention $[u,v]=u^{-1}v^{-1}uv$, is $\beta$. Denote by the same symbols the group elements representing basis vectors and put $g=x^{p^s}$, $h=gz^{p^{s-1}}$. An integral conjugation changes $g$ by a commutator in $p^sW$, and $p^{s-1}z\notin p^sW$. In the real group with the same multiplication formula, conjugation by $y^{1/p^s}$ takes $g$ to $h$, since the commutator is $p^s\cdot p^{-s}\beta(x,y)$.

The real group is simply connected and $\Gamma$ is a cocompact lattice. Reducing the $V$ coordinates by integer translates and then the central $W$ coordinates gives a compact fundamental region. Thus the left quotient $\Gamma\backslash G$ of the real group $G$ is a compact aspherical nilmanifold, and free homotopy of loops is exactly conjugacy in $\Gamma$. Use the left-invariant metric making the specified tangent basis orthonormal at the identity. The one-parameter path from the identity to $x^{p^s}$ has length $p^s$, and a central path adds $p^{s-1}$ to reach $h$. Constant-speed reparametrization gives the claimed Lipschitz bound on a circle of circumference one. Maps to $K(Q,1)$ realize the homomorphisms from $\Gamma$ to $Q$. Taking images reduces to the surjective case for minimizing the size of $Q$, since nonconjugacy in $Q$ implies nonconjugacy in the image. The group presentation or lattice tensor is the compact input format. In particular no triangulation of the nilmanifold or Cayley table of the separator is part of the reduction.

## An upper bound by a scalar quotient

Let $R=\mathbb Z/p^s$. For a functional $\lambda:W\to R$ with $\lambda_0=1$, let $\Lambda_\lambda\le V$ be the inverse image of the radical of $\lambda\beta\bmod p^s$. On $(V/\Lambda_\lambda)\oplus R$ the cocycle $\tfrac12\lambda\beta$ defines a finite class-two group of exponent dividing $p^s$, where $2$ is invertible in $R$. There is a surjective homomorphism from $\Gamma$ onto it. One explicit form is
$$
(v,w)\longmapsto (v+\Lambda_\lambda,\lambda(w)-\tfrac12\lambda B(v,v)).
$$
Indeed the symmetric correction changes the original cocycle to $\tfrac12\lambda(B-B^{\mathsf T})$. This quotient maps $g$ to the identity and $h$ to the nonzero central value $p^{s-1}$. Its order is
$$
p^s\,|\operatorname{im}(\lambda\beta\bmod p^s)|
=p^{\,s+2(D+1+\operatorname{rank} A(\bar\lambda_1,\ldots,\bar\lambda_m))}.
$$
Here the image is that of the linear map from $V/p^s V$ to its $R$-dual. Each block has the common factor $p^{s-1}$, so its image size is read from the rank of the remaining matrix over $\mathbb F_p$. The shift block with $\lambda_0=1$ is invertible over $\mathbb F_p$, and the final scalar block contributes one before passing to the alternating matrix. Minimize over the reductions of the $\lambda_i$ to obtain the upper bound.

## A lower bound against arbitrary finite quotients

A finite quotient of $\Gamma$ is nilpotent and is the direct product of its Sylow subgroups. In each Sylow subgroup at a prime different from $p$, the images of $g,h$ are conjugate. To see this, choose the power of the image of $y$ with exponent inverse to $p^s$ modulo the order of the image of $[x,y]$. Conjugation by this power multiplies the image of $g$ by precisely the image of $z^{p^{s-1}}$. A separating finite quotient must therefore separate in its $p$-Sylow factor. It suffices to prove the lower bound for that factor $Q$.

Let $W'$ be the image of $W$ in $Q$, a finite abelian central subgroup. The image of $z^{p^{s-1}}$ is nonzero, or else the two elements would agree in $Q$. Choose a surjective cyclic coordinate of $W'$, with order $p^\ell$, on which that image is nonzero. This is possible by the primary cyclic decomposition of a finite abelian group. Composing the quotient maps gives a functional $\lambda:W\to\mathbb Z/p^\ell$. Set $t=v_p(\lambda_0)$, so $0\le t\le\ell-s$.

The order of the center of $Q$ is at least $p^\ell$. Also $Q/Z(Q)$ is a quotient of $V$, and the kernel of $V\to Q/Z(Q)$ lies in the radical of $\lambda\beta\bmod p^\ell$, since its image commutes with everything. Consequently
$$
|Q|\ \ge\ p^\ell\,|\operatorname{im}(\lambda\beta\bmod p^\ell)|.
$$
For a matrix over $\mathbb Z/p^\ell$ divisible by $p^a$, if the matrix after division has rank at least $k$ modulo $p$, its image has order at least $p^{(\ell-a)k}$. Indeed an invertible $k\times k$ minor of the divided matrix yields $k$ independent coordinates over $\mathbb Z/p^{\ell-a}$. This applies to rectangular matrices, and an alternating block $\mathcal A(M)$ has twice the mod-$p$ rank of $M$.

If every $\lambda_i$ is divisible by $p^t$, divide all central coefficients by $p^t$ and reduce modulo $p$. The normalized $\lambda_0$ is nonzero. Thus $P_\lambda$ has rank $D$ after removing the common factor, and $C_\lambda$ has rank at least $r_*$ since it is a nonzero scalar times an evaluated original affine pencil. The scalar block has rank one. Removing the common factor $p^{s-1+t}$ in the commutator matrix leaves $\ell-(s-1)-t\ge1$ effective digits. The image cardinality is therefore at least $p^{2(D+1+r_*)}$, and $\ell\ge s$ supplies the desired order bound.

Otherwise let $v<t$ be the minimum of the valuations of the $\lambda_i$. In the shift block after division by $p^v$ and reduction modulo $p$, the first nonzero term is a unit times $J_D^j$ for some $1\le j\le m$. The remaining factor after extracting $J_D^j$ is invertible, so this block has rank $D-j\ge D-m$. There are at least two effective digits, since $\ell-(s-1)-v\ge2$. The alternating shift block alone now has image of order at least $p^{4(D-m)}$. The choice of $D$ gives
$$
4(D-m)>2(D+1+\min(\#\mathrm{rows},\#\mathrm{columns}))\ge2(D+1+r_*).
$$
These quotients are strictly larger than the stated optimum. This proves the lower bound without an exponent assumption. The shift block is what excludes potentially cheaper cyclic characters that detect $z$ only at a higher $p$-adic digit.

## Decision and exact counting

For a 3-CNF formula, take one variable $t_i$ per Boolean variable and one additional variable per clause. Impose $t_i(1-t_i)=0$. For a clause with literal values $a,b,c$, require
$$
u=(1-a)(1-b),\qquad u(1-c)=0.
$$
Negative literals use $1-t_i$. The auxiliary variable is determined uniquely. All equations have the form $a'b'=c'$ with affine linear entries. For each equation use the affine block $\begin{psmallmatrix}1&a'\\ b'&c'\end{psmallmatrix}$, and take the block diagonal sum for $A(t)$. Each block has rank at least one and has rank one exactly when its equation holds. If there are $T$ equations, rank $T$ is attained exactly at satisfying assignments, with one point of the pencil parameter space per such assignment. Taking the size limit $p^{s+2(D+1+T)}$ proves hardness. The bit length of this limit and the tensor construction are polynomial. Membership in NP follows from the exact formula and a certificate consisting of the parameters modulo $p$. Affine MinRank itself has classical independent hardness results. [Buss–Frandsen–Shallit](https://doi.org/10.1006/jcss.1998.1608)

One can count kernels of precisely that index in the 3-CNF family. If the formula is unsatisfiable, the lower bound excludes every such kernel. Otherwise, equality throughout the lower bound forces $Q$ to be a $p$-group, and forces $\ell=s$ and $t=0$. It also forces $Z(Q)=W'$ cyclic of order $p^s$ and the kernel of $V\to Q/Z(Q)$ to be exactly $\Lambda_\lambda$. In fact equality first requires elimination of the mixed-valuation case, then requires $\ell=s$ to avoid the strict center-size penalty. The condition $\ell-t\ge s$ then gives $t=0$. Since $W'$ has a cyclic quotient of order $p^s$ and is a subgroup of this center of order $p^s$, both claims follow. The image of $z$ gives a unique normalization $\lambda_0=1$.

Given such a normalized $\lambda:W\to\mathbb Z/p^s$, any relevant kernel meets $W$ in $\ker\lambda$. Pass to $\Gamma/\ker\lambda$. The subgroup over the free lattice $\Lambda_\lambda$ is abelian because $\Lambda_\lambda$ consists of radical elements. In fact it is central in $\Gamma/\ker\lambda$. Its central extension by $\mathbb Z/p^s$ splits since $\Lambda_\lambda$ is free abelian. A kernel over $\Lambda_\lambda$ that meets this cyclic subgroup trivially is exactly a graph complement. There are $p^{sd}$ such complements, by choosing a homomorphism from $\Lambda_\lambda$ to $\mathbb Z/p^s$ relative to one splitting. Their preimages are all normal, have the required index, and separate $g,h$, since $p^s x$ lies in $\Lambda_\lambda$ and $z^{p^{s-1}}$ survives. Distinct normalizations $\lambda_0=1$ give distinct kernels on $W$. Each parameter in $\mathbb F_p^m$ lifts to $p^{(s-1)m}$ normalized choices, and rank sees only that reduction. Therefore the total number of separating kernels at the stated threshold is exactly
$$
p^{sd+(s-1)m}\cdot\#\{\text{satisfying assignments of the input formula}\}.
$$
This proves the single-call numerical reduction. The stated count belongs to $\#\mathrm P$: nondeterministically choose the normalized character and, using Smith normal form for a fixed choice of radical basis, the $d$ coordinates of a graph complement. Reject unless the mod-$p$ rank is $T$. This counts each kernel exactly once.

## Scope and precedents

Effective conjugacy separation bounds ask how large a finite quotient must be in the worst case for a fixed group and bounded word length. This theorem instead computes an exact instance minimum parametrized by a varying bracket tensor and gives its compact-input complexity. The real conjugacy orbits agree in the constructed family. Class-two real displacement remains affine, as in the proof of the linear loop-persistence bound. Finite integral separation can already be NP-complete at that same geometric cutoff. [Pengitore, effective separability](https://arxiv.org/abs/1502.05445) · [Recent uniform conjugacy separation bounds](https://arxiv.org/abs/2610.03074) · [Bridson–Riley, class-two Diophantine conjugacy](https://doi.org/10.1112/blms.70327)

## The same minimum at the prime two

The least-order formula and the decision and counting reductions also hold when the fixed prime is two. The lower bound and counting classification require only the alternating commutator tensor and valuations. For the upper bound take the same normalized character modulo $2^s$. Its radical contains $2^s x$, and it detects $z^{2^{s-1}}$. The split-center construction in the general separator theorem attains its matrix-image bound. This extension claims the same order bound. [General separator theorem](GeneralFiniteSeparator.md)
