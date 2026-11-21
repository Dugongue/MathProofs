# Exact tensor-lift slices over finite local rings

Let $R$ be a finite commutative local ring, with maximal ideal $\mathfrak m$, residue field $k=\mathbb F_q$ and residue characteristic $p$. Write $\mathcal T_R=R^{n_1}\otimes R^{n_2}\otimes R^{n_3}$ and $G_R=\prod_i\operatorname{GL}_{n_i}(R)$, where all dimensions are positive. The central scalar subgroup
$$
 Z_R=\{(aI,bI,(ab)^{-1}I):a,b\in R^\times\}
$$
acts trivially. Fix $\bar T\in\mathcal T_k$ and let $\Gamma=\operatorname{Stab}_{G_k}(\bar T)$. Assume its infinitesimal stabilizer consists exactly of the ineffective scalars. Explicitly, for the linear infinitesimal action
$$
 d_{\bar T}(X_1,X_2,X_3)
  =(X_1\otimes I\otimes I+I\otimes X_2\otimes I+I\otimes I\otimes X_3)\bar T
$$
assume
$$
 \ker d_{\bar T}=\{(a I,b I,-(a+b)I):a,b\in k\}.
$$
This is a single rank test over the residue field. Let $W=\operatorname{coker}d_{\bar T}$, with the induced $\Gamma$-action.

**Theorem.** The tensors over $R$ reducing to $\bar T$, modulo changes of basis reducing to the identity, have a unique normal representative $T_0+v$ with $v\in\mathfrak m N$, once any lift $T_0$ and the explicit pivot complement $N$ below have been chosen. The kernel of reduction on every resulting tensor stabilizer is $(1+\mathfrak m)^2$, acting by ineffective scalars.

If $p\nmid|\Gamma|$, the remaining action on the slice can be made linear. The full $R$-isomorphism classes of lifts form a set in bijection with
$$
 \Gamma\backslash W^s,\qquad s=\log_q|\mathfrak m|,
$$
where $W^s$ has the diagonal $\Gamma$-action. This bijection can preserve the conjugacy class of the stabilizer in $\Gamma$. The number of lift classes is
$$
 \frac{1}{|\Gamma|}\sum_{\gamma\in\Gamma}|\mathfrak m|^{\dim_k W^\gamma}.
$$
For any class with residue stabilizer $\Gamma_v$, its full automorphism group is isomorphic to $(1+\mathfrak m)^2\times\Gamma_v$. Thus the class count and residue stabilizer distribution depend on the local ring only through $k$ and $|\mathfrak m|$, at the specified residue tensor. The ring need not be principal or contain $k$.

## Normalizing the congruence action

Write $\mathfrak g_R=\bigoplus_i\operatorname{Mat}_{n_i}(R)$. Let $X\subset\mathfrak g_R$ consist of tuples whose first two $(1,1)$-entries are zero. It is complementary to the two scalar directions over every ring, since subtracting from the first and second factors their $(1,1)$-entry times the identity then fixes the third scalar adjustment. There is no trace division. If $T_0$ is any lift of $\bar T$, the reduction of $d_{T_0}|_X$ is injective. Choose a full-column minor over $k$; it is a unit over $R$. The coordinate vectors at the remaining output positions form a free complement $N$ with
$$
 \mathcal T_R=d_{T_0}(X)\oplus N,\qquad N\otimes_R k\cong W.
$$
More generally any free complement to this image can be used in the argument.

Let $G_1=\ker(G_R\to G_k)$. Every element of $G_1$ can be written uniquely as a scalar in $Z_R\cap G_1$ times an invertible tuple $I+x$ with $x\in\mathfrak m X$. Read the two scalar units from the first two $(1,1)$-entries and divide by the corresponding central scalar tuple. The normalized tuple is close to the identity, so its factors are invertible.

Consider the map
$$
 (\mathfrak m X)\times(\mathfrak m N)\longrightarrow T_0+\mathfrak m\mathcal T_R,
 \qquad (x,v)\longmapsto (I+x)\cdot(T_0+v).
$$
It is bijective. At the first step $x,v$ are zero modulo $\mathfrak m$. At step $j\geq1$, a correction $(\delta x,\delta v)$ in $\mathfrak m^j$ changes the image modulo $\mathfrak m^{j+1}$ by exactly $d_{T_0}(\delta x)+\delta v$. Every other term has at least one factor in $\mathfrak m$ in addition to the correction. The displayed direct-sum isomorphism gives a unique correction on $\mathfrak m^j/\mathfrak m^{j+1}$, even if that layer has dimension greater than one over $k$. Nilpotence gives existence and uniqueness after finitely many steps. The same proof with a nilpotent ideal in an $R$-algebra works because the direct-sum linear map is already invertible over $R$.

Since the scalar factor acts trivially, two points of the normal slice can be related by $G_1$ only if they are equal and the normalized multiplier is the identity. It follows that the congruence orbit representatives and the reduction kernel of the stabilizer are exactly as claimed. Conjugating from a normal representative to an arbitrary tensor does not change the central kernel. For any prescribed element of $\Gamma$, an arbitrary lift to $G_R$ maps the set of congruence orbits to itself. Its action on that set is independent of the lift because any two lifts differ by $G_1$. Thus the quotient by this residual action always classifies the full $R$-isomorphism classes. This assertion does not require the tame hypothesis.

## Lifting the tame residual group and linearizing the slice

Assume now that $|\Gamma|$ is a unit in $R$. Lift the inclusion of $\Gamma$ into $G_k$ successively along the quotient rings $R/\mathfrak m^j$. At one step choose arbitrary matrix lifts $u_g$ of the preceding group homomorphism. They are invertible because their reductions are invertible. The failure of multiplicativity has the form
$$
 u_g u_h=(I+c(g,h))u_{gh}
$$
with $c(g,h)$ a tuple of matrices in the square-zero ideal $\mathfrak m^j/\mathfrak m^{j+1}$. Conjugation on this ideal depends only on the residue matrices and gives a $\Gamma$-module. Associativity gives
$$
 c(g,h)+c(gh,t)=g\cdot c(h,t)+c(g,ht).
$$
Averaging this equality over $t$ yields $c(g,h)=g\cdot b(h)+b(g)-b(gh)$, with $b(g)=|\Gamma|^{-1}\sum_t c(g,t)$. Replacing $u_g$ by $(I-b(g))u_g$ kills the defect, so the lift is a homomorphism. Iteration constructs a section $\sigma:\Gamma\to G_R$ of reduction over $\Gamma$.

Average an arbitrary lift of $\bar T$ under $\sigma(\Gamma)$ to obtain a fixed lift $T_0$. The image of $d_{T_0}$ is invariant under this group since $T_0$ is fixed. It is the same as $d_{T_0}(X)$, because scalar directions act infinitesimally by zero. Average any $R$-linear projection onto this image. The result is still a projection since it still takes values in the image and restricts to the identity there. Its kernel $N$ is now a $\sigma(\Gamma)$-invariant complement, free because $R$ is local. On $T_0+\mathfrak m N$ the residual action is the actual linear action of $\sigma(\Gamma)$ on $\mathfrak m N$. This uses the fixed lift and does not require invariant choices of the matrix normalization.

If $\gamma$ fixes $v$, the element $\sigma(\gamma)$ fixes $T_0+v$. Conversely, the reduction of every stabilizer element fixes $v$ since the normal slice is unique. Thus the residual stabilizer group has the displayed splitting by $\sigma$. Its kernel is $Z_R\cap G_1\cong(1+\mathfrak m)^2$, and that kernel is central, proving the direct product assertion.

## Independence of the higher multiplication in the ring

The successive quotients of $\mathfrak m N$ have the residue actions
$$
 \mathfrak m^j N/\mathfrak m^{j+1}N
   \cong(\mathfrak m^j/\mathfrak m^{j+1})\otimes_k W .
$$
They are copies of $W$ with multiplicities $\dim_k\mathfrak m^j/\mathfrak m^{j+1}$. They need not split additively over $R$. For the orbit classification they split as $\Gamma$-sets. For each successive surjection, choose one representative in every orbit of its target and choose any lift of that representative. Average that lift over the stabilizer of the representative. The averaging is well defined in the additive quotient because all subgroup orders are units, and the result still maps to the representative. It is fixed by its stabilizer, so extending the section equivariantly gives a well-defined section on the whole target. Subtraction of that section identifies the map with a product with its additive kernel as $\Gamma$-sets.

Iterating produces the asserted, generally noncanonical, equivariant bijection $\mathfrak m N\cong W^s$ with $q^s=|\mathfrak m|$. It preserves point stabilizers. Burnside's lemma gives the formula since $(W^s)^\gamma=(W^\gamma)^s$. In particular the same numbers and residual stabilizers occur over $\mathbb Z/p^3\mathbb Z$, $\mathbb F_p[t]/(t^3)$, and $\mathbb F_p[u,v]/(u,v)^2$, for any residue tensor obeying the hypotheses.

On a fixed finite ring, the pivot, linear corrections, and averaging are polynomial-time procedures in the tensor length and the size of an explicit list of $\Gamma$. When residue tensors are presented in different bases, first align them using a supplied residue transporter and any lift of it to $R$. Once aligned, the tame isomorphism test normalizes and checks the $\Gamma$-orbit in the linear slice. The result assumes the residue data rather than solving unrestricted residue tensor isomorphism.

## A family of arbitrary size over each fixed residue field

For every finite field $k$, take four distinct positive integers $m_1,m_2,m_3,m_4$ prime to $p$, and set $n=\sum_i m_i$. Construct a $3\times n\times n$ tensor by the matrix pencil
$$
 M(x,y,z)=xI+yD+zE ,
$$
where $D$ is diagonal, and $E$ is upper bidiagonal with superdiagonal entries all one. Choose their diagonal pairs $(d,e)$, in consecutive blocks of dimensions $m_i$, to be $(0,0),(0,1),(1,0),(1,1)$. The corresponding covectors are a projective frame, since every choice of three has determinant $1$ or $-1$. The determinant polynomial is the product of the four linear factors $x+dy+ez$ with multiplicities $m_i$.

In the slice convention a transporter satisfies $B M(w)=M(Cw)A$. This is the standard tensor action after dualizing the appropriate factors, which sends scalar directions to scalar directions. If the tensor is fixed, the induced action on the determinant polynomial preserves the linear factors and their multiplicities. Unique multiplicities force $C$ to fix every covector line, hence to be scalar. Evaluating at the identity slice then gives $B$ as the corresponding scalar multiple of $A$, and $A$ commutes with both $D,E$. The vector at the last coordinate is cyclic for $E$: its images under powers $0,\ldots,n-1$ have successive leading coefficients one. Thus a matrix commuting with $E$ is a polynomial in $E$ of degree less than $n$, by its effect on the cyclic vector. A polynomial of highest degree $j\geq1$ has constant nonzero $j$-th superdiagonal. Some entry of this diagonal crosses the two consecutive $D$-blocks, so the matrix cannot commute with $D$. Therefore the common centralizer and the residual tensor stabilizer have only the scalar directions, and $\Gamma=Z_k$.

For the infinitesimal stabilizer, let the third change be $I+\varepsilon C_1$ over the dual numbers. The determinant equality to first order says
$$
 \sum_i m_i(\ell_i\circ C_1)\ell_i^{m_i-1}\prod_{j\ne i}\ell_j^{m_j}
     =a\prod_i\ell_i^{m_i}
$$
for some $a\in k$, where the $\ell_i$ are the four covectors. Divide by $\ell_i^{m_i-1}$ and reduce modulo $\ell_i$. The other factors are nonzero in the quotient domain, and $m_i\neq0$ in $k$, giving $\ell_i\circ C_1\in k\ell_i$. Hence $C_1$ is scalar. The first-order tensor equation now reduces, after the identity slice, to the same common centralizer calculation, and the infinitesimal stabilizer is exactly the ineffective scalar Lie algebra. All hypotheses therefore hold for these examples, with normal dimension $n^2-7$. Their number of lift classes is exactly $|\mathfrak m|^{n^2-7}$, and every lift has the scalar automorphism group $Z_R$. The dimensions grow over the same fixed $k$ by increasing an admissible multiplicity.


For a fixed finite commutative ring with several local factors, the result applies componentwise. The Artinian decomposition $R=\prod_iR_i$ splits the free tensor spaces and the change-of-basis groups into their products. Fixing a residue tensor in each local factor therefore gives a product of the classifications above, and the local counts multiply. In the explicit pencil family the multiplicities can be chosen distinct and prime to all residue characteristics at once, so this yields families of unbounded size over any fixed finite commutative ring.

## Relation to prior work

Grochow, Qiao, Stange and Sun study tensor isomorphism over commutative rings and distinguish free-module tensor inputs from general module inputs. The theorem here is a local calculation at a residue orbit for free-module tensor inputs. It isolates a class where all nilpotence lengths admit an exact affine slice and where residue automorphism actions suffice for classification. [Grochow, Qiao, Stange and Sun, Tensor Isomorphism over Commutative Rings](https://arxiv.org/abs/2611.00735)

Prasad, Singla and Spallone develop extension-based similarity normal forms over local principal rings of length two. Alper, Hall and Rydh give relative étale local quotient structure around linearly reductive stabilizers, including mixed characteristic. This proof directly constructs a normal form on finite-ring points through first-order linear systems and a finite-group averaging argument. It covers the stated infinitesimal-stabilizer condition without a tame hypothesis for congruence normalization, and it gives the stronger residue-group linear action in the tame case. The proof is in prose, with no Lean verification or independent priority claim. [Prasad, Singla and Spallone, Similarity of matrices over local rings of length two](https://arxiv.org/abs/1212.6157) · [Alper, Hall and Rydh, The étale local structure of algebraic stacks](https://arxiv.org/abs/1912.06162)

Singla also gives a canonical section of finite-ring reduction on the centralizer of a matrix in block Jordan form at length two and uses it to transfer exact class counts between rings. The present group lift uses the prime-to-$p$ condition on the rational tensor stabilizer and supports arbitrary local length and nonprincipal rings. The public MathProofs notes on ring universality give exact reductions over arbitrary commutative base rings. Those reductions concern global isomorphism problems. The slice and class counts here are for a prescribed residue orbit. [Singla, A canonical section method for conjugacy classes of $\operatorname{GL}_n(\mathcal O_2)$](https://arxiv.org/abs/2608.10468) · [MathProofs, Rank two completion and tensor universality over rings](https://github.com/Dugongue/MathProofs/blob/main/RankTwoAndRingUniversality/README.md) · [MathProofs, Tensor and cubic-form isomorphism questions](https://github.com/Dugongue/MathProofs/blob/main/TensorFormQuestions/README.md)

Geometry.py runs 24 exact normalization checks in each of three local rings of order 125, using a $3\times4\times4$ tensor with residue derivative rank 39. It also enumerates the 325 orbits of a tame sign-action control on pairs of maximal-ideal elements in each ring. The numerical controls supplement the prose proof.
