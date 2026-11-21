# Fully symmetric tensor isomorphism in one final-digit class

**Theorem.** Let $R$ be a finite commutative local ring with nonzero maximal ideal $\mathfrak m$, residue field $k$, and a supplied nonzero element $s$ with $s\mathfrak m=0$. There is a deterministic reduction from ordinary three-tensor isomorphism over $k$ to ordinary three-tensor isomorphism over $R$. For fixed positive input format $(a,b,c)$, the reduction writes fully symmetric tensors on $N=O(a+b+c)$ variables with the following simultaneous properties.

- The outputs agree entrywise modulo $sR$.
- Contracting at the same fixed basis vector in any of the three modes gives the same fixed permutation matrix. In particular every mode has an invertible slice.
- The tensors are Frobenius forms of finite free commutative unital associative algebras with a perfect multiplication pairing. The reduction of each algebra to $k$ is local Gorenstein with maximal-ideal cube zero.
- Every independent-mode output transporter yields a field input transporter in polynomial time. Every field input transporter extends to an output transporter using the same determinant-one matrix in all modes. Consequently independent $\mathrm{GL}^3$, independent $\mathrm{SL}^3$, diagonal $\mathrm{GL}$, and diagonal $\mathrm{SL}$ give the same decision on this family.

For $R=\mathbb Z/p^e\mathbb Z$, $e\ge 2$, use $s=p^{e-1}$. The construction and witness recovery are uniform and polynomial bit-time in the explicit input, including $\log p$ and $e$ for these rings. More generally they use polynomially many ring and field operations, conversions to and from the supplied residue coordinates, and inversions of units, given an explicit identification $k\simeq sR$. For any fixed $R$, each of the four promised problems is polynomial-time equivalent to ordinary tensor isomorphism over the prime field of $k$. No division by $2$ or $3$ occurs.

## 1. Converting the three roles into one symmetric field form

Write a tensor $t$ as a trilinear form on three independent argument spaces $X_1,X_2,X_3$ of dimensions $a,b,c$, where $X_3$ is dual to the output space in the bimap convention. Put $n=a+b+c$, $M=n+7$, and $h_i=2^i M$ for $i=1,2,3$. Give an $h_i$-dimensional space $H_i$ the split symmetric pairing with matrix made of blocks $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$. Set
$$
O_i=X_i\oplus X_i^*\oplus H_i,\qquad
K=O_1\oplus O_2\oplus O_3,\qquad
L=K\oplus k z_1\oplus k z_2\oplus k z_3.
$$
On $O_i$, let $\beta_i$ be the orthogonal sum of the evaluation pairing on $X_i\oplus X_i^*$ and the split form on $H_i$. Define a symmetric trilinear form $C_t$ on $L$ by its summand restrictions. Its restriction to $X_1\times X_2\times X_3$ is $t$, copied to the other five argument orders. Its restriction to $kz_i\times O_i\times O_i$ is given by $C_t(z_i,o,o')=\beta_i(o,o')$, also copied to the other argument orders. Every other summand restriction is zero. These are assignments on disjoint summand triples, so the definition works in characteristic two and three as written.

An input equivalence extends to an exact diagonal isometry of the $C_t$ by acting contragrediently on the $X_i^*$ and identically on the $H_i$ and $z_i$. For reflection, even a projective equivalence of $C_t$ suffices. The following three intrinsic tests give its action on the three input roles.

1. **Recover $K$.** For $u\in K$, the slice $C_t(u,-,-)|_{K\times K}$ factors through the $n$-dimensional space $\bigoplus_iX_i$. Passing to the full slice adds three rows and three columns. Its rank is therefore at most $n+6$. If $u=o+\sum_i\alpha_i z_i$ has a nonzero marker coefficient $\alpha_i$, the restriction to $H_i\times H_i$ has rank $h_i>n+6$. Thus precisely $K$ has full slice rank at most $n+6$.

2. **Recover the three marker lines in $L/K$.** For the same $u$, the slice restricted to $K\times K$ is block diagonal between the spaces $H_i$ and the remaining space of dimension $2n$. On $H_i$ it is $\alpha_i$ times the split pairing. Its rank lies between $\sum_{\alpha_i\ne 0}h_i$ and $\sum_{\alpha_i\ne0}h_i+2n$. These intervals are disjoint for distinct subsets because their left endpoints are distinct multiples of $2M$. The interval is therefore determined by the class in $L/K$ and can be read from any representative. In particular the intervals of the three singleton subsets distinguish the three individual marker lines.

3. **Recover the ordered support quotients of the input.** Let $D$ be the radical of $C_t|_{K^3}$. Write $D_i^0\subset X_i$ for the input mode radical, meaning the kernel of contraction in that mode. Then
$$
D=\bigoplus_i(D_i^0\oplus X_i^*\oplus H_i).
$$
Indeed only the $X_i$ contribute to $C_t|_{K^3}$ and evaluating on the two other $X_j$ isolates the individual mode contraction. For a nonzero representative $u_i$ of marker line $i$, pair $K$ with $D$ via $C_t(u_i,-,-)$. The map is unchanged by adding an element of $K$ to $u_i$, and scaling $u_i$ scales the pairings by the same factor. Project its left kernel to $K/D$. The kernel inside $O_i$ lies in $X_i^*$ because it annihilates $X_i^*\oplus H_i$. All the other $O_j$ belong to the kernel. The projected subspace is exactly the sum of the two support quotients $X_j/D_j^0$ for $j\ne i$. The intersection of the two projected subspaces with labels other than $i$ is therefore $X_i/D_i^0$.

The diagonal equivalence carries these recovered subspaces to their corresponding targets and intertwines the restriction of $C_t$ on their product, up to the common projective scalar. Absorb this scalar in one mode. Each isomorphism of supported spaces extends to the original argument spaces by choosing complements and arbitrary isomorphisms of the matching contraction radicals. The input form vanishes whenever any argument is in its radical, so the extensions give an input transporter. These steps, including the zero-tensor case, use linear algebra on the supplied witness and displayed coordinates. The rank characterization is a proof of invariance and does not call for searching a rank locus. The full $C_t$ has zero contraction radical. The first test confines any radical vector to $K$, and pairing with $z_i$ and $O_i$ detects its $O_i$-component by nondegeneracy of $\beta_i$.

## 2. A commutative Frobenius lift with fixed slices

The map $\jmath:k\to sR$, $\bar r\mapsto sr$, is a well-defined $R$-module isomorphism. Its kernel before quotienting is exactly $\mathfrak m$, since $\operatorname{Ann}_R(s)$ is a proper ideal containing $\mathfrak m$. Also $s\in\mathfrak m$ because a unit cannot annihilate the nonzero ideal $\mathfrak m$.

Let $L_R$ be free on the displayed field basis of $L$, and let $z$ be a new socle generator. Set
$$
A_t=R1\oplus I_t,\qquad I_t=L_R\oplus L_R^*\oplus Q\oplus Rz.
$$
Here $Q$ is zero or has basis $w$. Choose its rank $\epsilon\in\{0,1\}$ so that $N=2\dim_k L+2+\epsilon=32n+204+\epsilon$ is prime to $\operatorname{char}k$. The unit acts as usual. For elements of $I_t$ use the following products, their transposes and zero for all unspecified products:
$$
xy=\jmath\bigl(C_t(\bar x,\bar y,-)\bigr)\in sL_R^*,\qquad
x\ell=\ell(x)z,\qquad
w^2=z\quad(\epsilon=1),
$$
where $x,y\in L_R$, $\ell\in L_R^*$, and $\jmath$ acts coefficientwise in the displayed dual basis. For three factors in $I_t$ any bracketing vanishes unless all three lie in $L_R$. In that case both bracketings yield $\jmath(C_t(\bar x,\bar y,\bar z_0))\,z$ for third argument $z_0\in L_R$, using symmetry of $C_t$. This proves associativity, and $I_t^4=0$.

Use the linear functional $\lambda:A_t\to R$ taking the coefficient of $z$. Write the output tensor as
$$
F_t(x,y,v)=\lambda(xyv).
$$
It is fully symmetric by commutativity and associativity. The matrix $G$ of the pairing $(x,y)\mapsto\lambda(xy)$ swaps $1$ with $z$, swaps each basis vector of $L_R$ with its dual, and fixes $w$ when present. These are all the nonzero pairings. Thus $G$ is a fixed permutation matrix over $R$, independent of $t$, and is the slice of $F_t$ at $1$ in every mode. Modulo $sR$ the only products that could depend on $t$ vanish, so all $F_t$ of that format agree. The residue algebra $A_t/\mathfrak m A_t$ is local because its augmentation ideal is nilpotent with quotient $k$. That residue ideal has square $kz$, cube zero, and annihilator $kz$ by the perfect pairing on the complement of $1,z$. This proves the Gorenstein assertion over $k$.

## 3. Reflecting arbitrary independent-mode transporters

Suppose an ordinary output transporter is $F_{t'}(f(x),g(y),j(v))=F_t(x,y,v)$. The perfect pairings for the source and target send an element $a$ to the functional $v\mapsto\lambda(av)$. By using these identifications on both sides, there is a unique invertible $h:A_t\to A_{t'}$ with $h(xy)=f(x)g(y)$. Explicitly $h$ is the source pairing identification, followed by $(j^*)^{-1}$, followed by the inverse target pairing identification.

Put $u=f(1)$ and $v=g(1)$. Evaluating at one input equal to $1$ shows that multiplication by $u$ and multiplication by $v$ are bijections. Both elements are units because their images contain $1$. Then $\varphi(x)=(uv)^{-1}h(x)$ is a unital algebra isomorphism, since $h(xy)=(uv)^{-1}h(x)h(y)$. All of this applies over the given coefficient ring. [Albert, *Non-associative algebras I*](https://doi.org/10.2307/1968960).

If $x\in I_t$, left multiplication by $x$ sends $1$ into $I_t$, $L_R$ into $L_R^*\oplus Rz$, and $L_R^*\oplus Q$ into $Rz$, and kills $z$. Its trace is zero by the displayed ordered decomposition. For $r1+x$ the trace is therefore $Nr$. Since $N$ is a unit, $I_t$ is intrinsically the kernel of the trace of left multiplication. The optional square $w^2=z$ permits $N$ to be odd in residue characteristic two while retaining a perfect pairing. Also the annihilator of $I_t$ inside $I_t$ is $Rz$, because the $z$-coefficient pairing on $L_R\oplus L_R^*\oplus Q$ is perfect.

Consequently every algebra transporter carries $I_t$ and $Rz$ to their counterparts, acting on the latter by a unit $\eta\in R^\times$ in the displayed generators. Products of three elements of $I_t$ lie in $sRz$ and define, under $sRz\simeq k$, a trilinear form on $I_t/\mathfrak m I_t$. It is $C_t$ extended by zero on the other summands. By conciseness of $C_t$, quotienting the contraction radical recovers $L$ and $C_t$ up to a choice of generator of $Rz$. The induced residue map is a projective equivalence of $C_t$ with multiplier $\bar\eta$. The three field tests recover the original tensor transporter.

Conversely start with an input field transporter. Section 1 extends it to an exact field isometry $P:L\to L'$ of $C_t,C_{t'}$. Lift its entries to an invertible $R$-linear map $\widetilde P:L_R\to L_R'$, which is invertible since its determinant is nonzero modulo $\mathfrak m$. Act by $\widetilde P$ on $L_R$, by $\widetilde P^{-\mathsf T}$ on its dual and identically on $1,Q,z$. The first multiplication rule only sees residue maps. Duality gives the second rule, and the other products are fixed. The resulting algebra isomorphism preserves $\lambda$ and has determinant $1$. Using it in all three slots proves the forward assertion even for diagonal special-linear equivalence.

## 4. Complexity and priority

The form $C_t$ uses $\dim L=16n+101$ coordinates. Writing the dense array of $F_t$ costs polynomial time. Witness recovery uses linear systems, reductions and the displayed product: it need not classify local algebras, decide unmarked rank loci, or find roots of a scalar. In the prime-power case the identification $k\simeq sR$, its inverse on $sR$, all unit inverses and the needed linear algebra have polynomial bit cost. The construction maps format mismatches, if admitted in the input problem, to a fixed pair constructed from a zero and nonzero format-$(1,1,1)$ tensor. For fixed $R$, the ordinary output problem has the known unrestricted upper reduction to the prime field of $k$. For the other three promised problems, use ordinary output isomorphism as the upper reduction on this written family, since the four decisions coincide there. [Fixed finite ring equivalence](https://github.com/Dugongue/MathProofs/blob/main/PrimePowerTensorIsomorphism/PROOF.md).

The starting final-digit theorem already obtained hardness within a common square-zero multiplication class with unit minors in all flattenings. A unit minor of a flattening does not require an invertible slice in that mode. The theorem above adds fixed invertible slices in all modes, full symmetry and simultaneous ordinary and determinant-one equivalence. Grochow–Qiao already gave linear-length algebra and tensor reductions, including the symmetric matrix-space to trilinear step in Part IV, §6. Grochow, Qiao and Tang previously established the complexity equivalence involving symmetric trilinear forms. The field-side short local Gorenstein consequence and the construction from a symmetric form and its dual also have precedent. The contribution here is their final-digit refinement with a common array, a prescribed invertible slice in every mode, and explicit witness recovery for the four actions over the coefficient ring. [Starting final-digit theorem](https://github.com/Dugongue/MathProofs/blob/main/FixedRingFour/CongruenceClass.md) · [Grochow–Qiao IV](https://arxiv.org/html/2306.16317) · [Grochow–Qiao–Tang](https://arxiv.org/abs/2012.01085) · [Field-side compressed algebras](https://github.com/Dugongue/MathProofs/blob/main/GrochowCubicFour/CompressedAlgebras.md) · [Grochow–Qiao–Stange–Sun V](https://arxiv.org/html/2611.00735v1).

For a related geometric formulation over fields, Jagiełła and Jelisiejew identify the evaluation tensor of a Gorenstein algebra with its multiplication tensor in Proposition 4.1 and Corollary 4.2. This is the field counterpart of the perfect-pairing step. The closest inspected statements do not establish the final-digit package above, and publication priority remains unverified. [Jagiełła–Jelisiejew, *Unrestrictions and concise secant varieties*](https://arxiv.org/html/2604.24879v1).

The proof is informal. The accompanying finite control tests the rank bands with several representative lifts and checks basis-level associativity, the trace kernel, symmetry, all three identical invertible slices, and equality of the common reduction on contrasting tensors over $\mathbb Z/4\mathbb Z$, $\mathbb Z/8\mathbb Z$, $\mathbb Z/9\mathbb Z$, and $\mathbb Z/25\mathbb Z$.
