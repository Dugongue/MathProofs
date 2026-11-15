# Determinants on large residual spaces from paired bilinear forms

Informal mathematics. This strengthens the anchored determinant compiler over each fixed finite field, including characteristic two. The source and target bilinear forms are paired as ordered tuples. Dimensions of the residual spaces can grow without a logarithmic bound. The new cost depends on the sizes of simple modules whose determinant contribution survives multiplication by the desired character. This is a sufficient theorem for marked branches.

## Theorem

Let $F=\mathbb F_q$ be fixed and $m=q-1$. Consider any anchored tensor-transport branch with a source residual space $R$ and target residual space $R'$. The spaces can be subquotients of a tensor mode. Their map $f:R\to R'$ is induced by the actual tensor transporter through typed inclusions and quotients. Suppose that every transporter in the branch preserves an explicit ordered pair of tuples $(B_i)$ on $R$ and $(B'_i)$ on $R'$, in the sense
$$
f^{\mathsf T}B'_if=B_i.
$$
Assume each $B_i$ and $B'_i$ is symmetric or each is alternating, with the choice allowed to vary with $i$. Keep all the original branch equations. The claim below gives a terminal for imposing a prescribed factor $(\det f)^\ell$ within any joint determinant character test.

Compute the source adjoint algebra
$$
\mathcal A=\{(P,Q):P^{\mathsf T}B_i=B_iQ\text{ for every }i\},
\qquad
(P,Q)(P',Q')=(PP',Q'Q),
\qquad
(P,Q)^*=(Q,P).
$$
Write its semisimple quotient as $\prod_j\operatorname{Mat}_{d_j}(E_j)$. Let $e_j$ be the total multiplicity of the natural simple module for factor $j$ in the radical filtration of $R$, using the first projection of $\mathcal A$. The involution permutes the factors in orbits of size at most two. Define $b$ as the largest $d_j$ among the following factors, and as zero if there are none.

- One factor $j$ from an exchanged pair $\{j,k\}$ if $\ell(e_j-e_k)$ is nonzero modulo $m$. The two matrix dimensions are equal.
- A self-paired factor of orthogonal type in odd characteristic if $\ell e_j[E_j:F]$ is odd.

Then $(\det f)^\ell$ can be represented on an attached scalar line, including a known calibration, with branch construction size polynomial in the explicit input and $2^b$. The attached line is part of a fixed-signature tensor system with the original branch. Every original transporter preserving the given data extends to the system, and each system isomorphism induces such a transporter. In particular $b=O(\log L)$ at input size $L$ suffices even with large residual dimension. The same conclusion applies along several steps of an exact-sequence decomposition if each step satisfies the bound and the total number of steps is polynomial.

## 1. A reference left-right equivalence is enough

First compute invertible $P_0,Q_0:R\to R'$ satisfying
$$
P_0^{\mathsf T} B'_i Q_0=B_i
$$
by the deterministic module isomorphism algorithm for the two-vertex representation given by the ordered arrows $B_i$. The left map of the two-vertex representation is $P_0^{-\mathsf T}$ and its right map is $Q_0$. Existence of a congruence implies existence of this pair, so failure of the module calculation rejects the branch. Write $s=P_0^{-1}Q_0$. Taking transposes of the calibration relation gives $Q_0^{\mathsf T}B'_iP_0=B_i$, including in characteristic two. Thus $s^{\mathsf T} B_i=B_is$, and $(s,s)$ is a unit of $\mathcal A$.

For any actual congruence $f$ of the paired forms, put
$$
x=(P_0^{-1}f,\ f^{-1}Q_0).
$$
Indeed $(P_0^{-1}f)^{\mathsf T}B_i=f^{\mathsf T}B'_iQ_0=B_if^{-1}Q_0$, so $x$ is in $\mathcal A$. Its invertible two components imply it is a unit. In the specified product
$$
xx^*=(s,s).
$$
This constant relation is the only equation about the two components required below. An isometry of the bilinear tuple need not be found in advance.

## 2. Recover the determinant on the first projection

Let $J$ be the radical of $\mathcal A$. It is invariant under the involution. Filter $R$ by $J^a R$ and write $x_j$ for the matrix of $x$ in simple quotient factor $j$. The first projection of $x$ has determinant
$$
\det_F(P_0^{-1}f)=\prod_j N_{E_j/F}(\det_{E_j} x_j)^{e_j}.
$$
This is the product of determinants on the graded layers, which are semisimple modules for $\mathcal A/J$. The determinant of an $E_j$-linear map after restriction of scalars is the field norm of its $E_j$-determinant. The quotient algebra, layer bases, matrix units and simple multiplicities can all be computed by fixed-field module algorithms. In particular, on each layer the dimension of the image of a first diagonal matrix unit divided by $[E_j:F]$ is its simple multiplicity.

The determinant relations imposed by $xx^*=(s,s)$ reduce the number of large modules needed. Write $t_j=\det_{E_j} x_j$ and $c_j$ for the determinant of the image of $(s,s)$ in factor $j$.

- For exchanged factors $j,k$ the anti-isomorphism carries the center of one to the other by an $F$-field isomorphism, so absolute field norms satisfy $N_j(t_j)N_k(t_k)=N_j(c_j)$. The product of their two character factors is therefore $N_j(c_j)^{\ell e_k}N_j(t_j)^{\ell(e_j-e_k)}$.
- On a self-paired factor with nontrivial involution on its center $E$, let $E_0$ be the fixed field of that involution. Then $t\bar t=c$, and $N_{E/F}(t)=N_{E_0/F}(c)$ is known. One may compute this without constructing $E_0$ as a separate field by using exponent $(|E_0|-1)/(q-1)$ on $c$.
- On a self-paired factor with center fixed in characteristic two, $t^2=c$. Squaring is invertible in the finite field $E$. Thus this factor changes only the known calibration.
- In odd characteristic, a self-paired factor with center fixed admits a Gram matrix $G$ for the involution, so $z^*=G^{-1}z^{\mathsf T}G$. Find $G$ by solving the linear equations $z^{\mathsf T}G=Gz^*$ for the matrix units. Skolem-Noether gives an invertible solution, and every nonzero solution is a scalar multiple of it since the full matrix algebra has scalar centralizer. The involution property implies $G^{\mathsf T}=G$ or $G^{\mathsf T}=-G$. In the alternating case,
  $$
  c_{\rm mat}G^{-1}=x_jG^{-1}x_j^{\mathsf T},
  $$
  where $c_{\rm mat}$ is the image of $(s,s)$ in this matrix factor. Consequently $t=\operatorname{Pf}(c_{\rm mat}G^{-1})/\operatorname{Pf}(G^{-1})$ is known. If the calculated numerator matrix is not alternating, the branch has no actual congruence. In the symmetric case $t^2=c$. Let $u=(|E|-1)/(q-1)$ be the norm exponent. If $\ell e_j[E:F]$ is even, $\ell e_j u$ is even as well, and the desired factor is known as $c^{\ell e_j u/2}$. If it is odd, this is an active factor eligible for a direct terminal.

Reject if a claimed base-field calibration produces an undefined scalar or an element outside $F^\times$. Every actual transporter gives the displayed defined base-field values. These identities hold for every actual transporter regardless of which quotient units extend to tensor transporters. No lifting of arbitrary semisimple unitary elements is used.

## 3. Share the determinant factors with the tensor equations

For each active factor, select a simple copy $S_j$ in a radical layer where it occurs. If an exchanged orbit was represented by a factor absent from all layers, switch its representative to the other one, whose nonzero multiplicity then supplies a copy. A matrix-unit construction gives such a submodule. On the target side take all the corresponding layer spaces and simple copies by applying $P_0$ to their source coordinates. They are legitimate markers because actual congruences act as $P_0$ followed by the first projection of a unit of $\mathcal A$, so they carry all named spaces to these corresponding spaces. That projection preserves the radical filtration and acts on each selected copy by its simple factor. Include the inclusions and quotient maps so that all induced actions are forced. In particular the source and target $E_j$ module structures on each copy are calibrated by $P_0$, and the transported copy map is $E_j$-linear in their chosen coordinates.

The top of the $E_j$ exterior algebra of $S_j$ gives the multiplier $t_j$. The existing finite-field norm diagram uses Frobenius maps between copies of that top line, multiplies the conjugates, and includes the resulting base-field line. It has polynomial size in $[E_j:F]$. Combine the powers of these base-field multipliers with the constants from Section 2 and $(\det P_0)^\ell$. This is exactly $(\det f)^\ell$ in the selected input coordinates. Combine with the other physical-mode determinant tests or frame factors in the same typed system. A terminal pin imposes any prescribed joint product. All remaining placements are direct sums, quotient maps or ordered arrows, and the fixed-signature compiler is applied once to the system with the original tensor still present.

In particular, these markers do not require an independent choice of residual isometry to extend to the other tensor modes. Each tensor transporter induces the maps used to evaluate the terminal scalar. Conversely an isomorphism of the enlarged structures preserves the original tensors and auxiliary branch conditions, so the algebraic calculation applies to its actual induced residual map.

## 4. Realization by marked tensors with growing radical dimension

The improvement applies to explicit anchored pencils where every alternating form produced by a marked slice is singular and successive radicals retain growing dimension. Fix $r\ge1$ and let $R=\bigoplus_{j=1}^r F^3$. For each pair $a<b$ of the three coordinates of each $j$, make a separate matrix block of size three, indexed by $i=(j;a,b)$. On this block let the normalized slice for $v\in R$ be
$$
N(v)_i=v_{j,a}E_{12}+v_{j,b}E_{23}.
$$
Add pointwise matched anchor labels for each block projector $P_i$ and for each $C_i=E_{31}$ in that block. Use the sum of the projector labels as the invertible identity anchor. The first label mode is the span of those independent anchor labels and $R$. The corresponding slice space is concise. In the calibrated normalized-pencil convention, the pinned labels ensure determinant one on their span, so the determinant on the first label mode is the determinant on the quotient identified with $R$.

The word algebra of the anchors has basis consisting of $P_i,C_i$. Thus all anchor trace functionals vanish on $R$. For each $i=(j;a,b)$,
$$
\operatorname{tr}(C_i[N(v),N(w)])=v_{j,a}w_{j,b}-v_{j,b}w_{j,a}.
$$
Commutators with a projector vanish. Commutators with any anchor $C_i$ pair to zero in these forms, by the matrix-unit products, so they descend through the pointwise fixed anchor span. Consequently the alternating tuples on $R$ are exactly the three elementary alternating forms on each three-dimensional summand, tagged independently. Every linear combination has at least a one-dimensional radical in each summand. Iteratively restricting any further combination to the previous radical still leaves dimension at least one in each of those summands. Thus the successive-radical method always leaves at least $r$ residual dimensions.

The adjoint algebra of the full descended tuple on $R$ is $F^r$ with identity involution. The three forms supported on one given summand have common radical zero inside that summand, so their adjoint identities force all off-diagonal blocks between summands to vanish. Inside a summand, the kernel of the form on any coordinate pair is the remaining coordinate line. The adjoint equations force both components to preserve each of those lines. If the two components are diagonal with entries $p_a,q_a$, the equations for coordinate pairs say $p_a=q_b$ for every $a\ne b$, so all six entries agree. This proves the asserted algebra. It has only one-dimensional factors. Over odd fields the possible isometry contributions on each summand include its scalar reflection with determinant $-1$, and the determinant identities read those scalars directly. Over even fields there is no surviving factor at all. On the two matrix modes the anchor projectors force the centralizer to split over the three-dimensional blocks, so all its determinant-relevant simple matrix dimensions are at most three. Hence the full anchored character compilation is polynomial for this unbounded example.

These examples distinguish the determinant readout from the rank of a single form and from any successive-radical calculation using its pencil. More generally, a large simple matrix factor contributes no exponential cost whenever it is self-paired of symplectic or unitary type, or whenever its multiplicity exponent cancels by the displayed equations.

## Sources and scope

The algorithm uses the constructive two-vertex module isomorphism and norm diagram in the prior anchored-slice and semilinear proofs, the adjoint-algebra construction and fixed-field decomposition used by [Ivanyos and Qiao](https://arxiv.org/abs/1708.03495), and the [same-field tensor-system compiler, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4). The additional steps are the left-right calibration of the determinant without finding a congruence, the explicit exponent cancellation on the whole tuple, and the family where it reduces an unbounded residual to one-dimensional terminals. The result covers marked branches satisfying the displayed width criterion. Generating suitable marks for arbitrary raw tensors remains separate.
