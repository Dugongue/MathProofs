# Quiver diagrams as ordinary multiplication tensors

**Theorem.** Let $Q$ be any finite named directed graph, including loops and parallel arrows, and let $X,Y$ be based representations over a field $k$ with the same dimension vector. There is an explicit construction $X\mapsto T(X)$ of an ordinary three-tensor, the multiplication tensor of a unital associative algebra, with the following properties.

1. Over every commutative $k$-algebra, there are natural maps from diagram isomorphisms to tensor isomorphisms and back. The composite on diagram isomorphisms is the identity. Both maps preserve identities and composition.
2. If $D$ is the side length, then
   $$
   D=O\left(1+|Q_0|+|Q_1|+\sum_v\dim X_v+
             \sum_{a:u\to v}(\dim X_u+\dim X_v)\right),
   \quad D\le \operatorname{rank}T(X)\le 5D .
   $$
3. With the literal two-sided inverse equations for isomorphisms and without coordinate field equations, Polynomial Calculus refutation degrees of the diagram and ordinary tensor systems satisfy
   $$
   d_{\rm diagram}\le d_{\rm tensor}
   \le C\max(1,d_{\rm diagram})
   $$
   for an absolute constant $C$. The first inequality comes from substituting only constants and individual variables, so its sparse proof-size overhead is polynomial. The other direction has polynomial overhead at fixed degree.

The construction applies to linear diagrams with any specified relations already satisfied by both inputs. The equal dimension vector is a necessary check for diagram isomorphism and is fixed throughout the construction. A zero-dimensional vertex and all its incident arrows can be dropped, since those arrows are zero and the zero space has a unique isomorphism. We allow the resulting graph to be empty.

## 1. The algebra and its witnesses

Construct a bipartite diagram with sources $s_v,s_a$ and targets $t_v,t_a$, one of each per vertex or arrow. The copies indexed by a vertex $v$ have space $X_v$. For $a:u\to v$, $s_a$ has space $X_u$ and $t_a$ has space $X_v$. Use the distinct links
$$
s_v\longrightarrow t_v \;(\mathrm{id}),\qquad
s_a\longrightarrow t_u \;(\mathrm{id}),\qquad
s_v\longrightarrow t_a \;(\mathrm{id}),\qquad
s_a\longrightarrow t_a \;(X_a).
$$
The first family is indexed by vertices and the last three by $a:u\to v$. The links have distinct ordered endpoint pairs even when $u=v$ or several arrows share endpoints. Every target receives an identity link.

Add two anchor vertices $d,h$, then topologically order all vertices, with anchors first, sources next and targets last. Define an algebra
$$
A(X)=k^m\oplus M\oplus W
$$
where $m$ is the number of these vertices. The coordinate idempotents $e_i$ act on a corner $e_j A e_i$ on its indicated endpoints. The $k^m$-bimodule $M$ has the following components.

- At $e_s M e_d$, put the data space $X_s$ of each source $s$. At $e_s M e_h$, put a copy of $k$.
- For each bipartite link $\lambda:s\to t$, put a copy of $k$ at $e_t M e_s$, with basis $u_\lambda$.
- For every consecutive pair $i,i+1$ in the total order whose corner is still empty in $M$, place one extra line at $e_{i+1} M e_i$.

The bimodule $W$ has the data space $X_t$ at $e_t W e_d$ and a copy of $k$ at $e_t W e_h$ for each target $t$. The only prescribed products between elements of $M\oplus W$ are
$$
u_\lambda x=X_\lambda x \text{ in the data space of }t,
\qquad
u_\lambda r_s=r_t,
$$
where $r_s,r_t$ are the source and target basis vectors in the respective $h$-corners. All other products in $M\oplus W$ are zero. The products respect endpoints, so are balanced with the idempotent actions. Every product of three elements of $M\oplus W$ is zero, proving associativity together with the diagonal actions. The sum of the idempotents is a unit.

Write $N=M\oplus W$. All commutators lie in $N$ since the quotient $k^m$ is commutative. Every basis vector $x$ of $N$ satisfies $x=[e_j,x]$ for its left endpoint $j$, since all corners are off diagonal. Thus $N$ is exactly the commutator span. Every basis vector of $W$ is a product via a chosen identity link, and hence $N^2=W$. These two identities hold over every commutative scalar extension. In particular $M=N/N^2$ and $W=N^2$ have intrinsic bimodule actions of $A/N$, and there is an intrinsic product $M\otimes M\to W$.

The vector-space dimension of the algebra has the asserted linear bound. The contributions involving diagonal idempotents use at most $2D$ pure tensors. Each link contributes at most $1+\operatorname{rank}X_\lambda$ further pure tensors by expressing the data map as a sum of rank-one matrices. The sum of the ranks of identity links and original-arrow copies is at most twice the sum of copied data dimensions, by the displayed list of links. The number of links is at most $D$, since each has its own line. Hence the rank is at most $5D$, and the product by the unit makes the output flattening surjective, proving the lower bound.

For a tensor witness $P,Q,T$ with $T(xy)=P(x)Q(y)$, put $a=P(1),b=Q(1)$. The identities $T=L_aQ=R_bP$ make $a,b$ units. Its normalized algebra isomorphism is
$$
\phi(x)=a^{-1}T(x)b^{-1}.
$$
It is unital, multiplicative and unique with $P=L_a\phi,\ Q=R_b\phi,\ T=L_aR_b\phi$. This construction commutes with arbitrary scalar extension. Normalization is compatible with composition: the two unit factors in a composite are obtained by applying the second normalized map to the first units and multiplying on the corresponding side.

An algebra isomorphism preserves $N$ and $W$, so acts on the quotient idempotents and both bimodules. Over a field it permutes the quotient idempotents. Since $e_jMe_i=0$ for $j\le i$, but $e_{i+1}Me_i\ne0$ for every $i$, this permutation is strictly increasing and hence the identity. Over any commutative ring the same holds by the orthogonal-idempotent calculation in §2.

From $\phi$ read the maps $G_s,H_t$ on the data components and the units $\rho_s,\rho_t$ on the $h$-components of $M,W$. Write $\eta_\lambda$ for its invertible scalar on a link. Multiplication gives
$$
H_t X_\lambda=\eta_\lambda Y_\lambda G_s,
\qquad \rho_t=\eta_\lambda\rho_s .
$$
Thus $F_s=\rho_s^{-1}G_s$ and $F_t=\rho_t^{-1}H_t$ are compatible with every link. The identity links identify the copies of the same original map, so the $F_{s_v}$ form a diagram isomorphism. Extraction is compatible with composition because the data maps and the ruler scalars each compose by multiplication on the intrinsic corner modules.

Conversely a diagram isomorphism acts by its maps on all corresponding data copies and by identity on the diagonal, link, extra and ruler lines. It preserves each displayed product, giving an algebra isomorphism and then a tensor witness by using it on all three factors in the bilinear convention. This is a functor and its composite with extraction is the identity.

## 2. Transport of Polynomial Calculus proofs

Use input matrices $F_v,\widehat F_v$ for each diagram vertex, the forward equations $F_vX_a=Y_aF_u$, and both inverse products. The ordinary tensor equations are the triple tensor action and both inverse products in each mode. For a multiplication tensor in $A^*\otimes A^*\otimes A$, its tensor-action matrices are $P^{-T},Q^{-T},T$ in terms of the bilinear witness convention above. Inverse-variable pairs allow these names to be obtained by transposition and exchange. Multiplying the tensor-action equations by the two input transformation matrices and using both inverse identities gives $T(xy)=P(x)Q(y)$ on basis entries in constant degree. This uses just the standard coordinate identities for transporting a bilinear map.

**From tensor proofs to diagram proofs.** Substitute the lifted diagram witness of §1, with $F_v$ on each data copy, $\widehat F_v$ for its inverse, and constants on the other blocks. Each tensor variable becomes a constant or an individual diagram variable. In actual tensor-action coordinates, the transported diagonal-action summands give inverse-product equations of degree two, and the transported radical-product data for $a:u\to v$ are $F_vX_a\widehat F_u$. The difference from $Y_a$ is the sum of $(F_vX_a-Y_aF_u)\widehat F_u$ and $Y_a(F_u\widehat F_u-I)$, of degree at most two. Identity links use only an inverse product, and ruler products use fixed constants. All other components vanish by the indicated block substitution. Thus each tensor axiom specializes to a degree-at-most-two diagram consequence with polynomial sparse derivation size. A tensor refutation has degree at least two, since the untranslated inputs contain no degree-zero or degree-one polynomials except zero. Each proof line then replays without increasing degree. Variable identification and constant specialization do not increase its number of monomials.

**Normalize in bounded degree.** In the tensor system, write $a=P(1)$, $b=Q(1)$, and define $a^-=Q T^{-1}(1)$, $b^-=P T^{-1}(1)$ as coordinate polynomials using the named inverse matrix. The relations $L_aQ=T$ and $R_bP=T$, with the inverse equations, imply $L_a^{-1}=QT^{-1}$ and $R_b^{-1}=PT^{-1}$ in constant-degree PC. For example the first inverse equations follow by multiplying $L_aQ-T$ by $T^{-1}$ on the right, and by using $L_a=TQ^{-1}$ for the opposite product. Apply these linear operators to the unit to obtain both unit products for $a^-,b^-$. Put
$$
\phi=L_{a^-}R_{b^-}T,\qquad \psi=T^{-1}L_aR_b .
$$
They are mutually inverse and derive $\phi(1)=1$, $\phi(xy)=\phi(x)\phi(y)$ from the bilinear tensor equations. Multiplicativity and unitality of $\psi$ follow by applying the two inverse products to those identities of $\phi$. All these substitutions use bounded products of coordinate polynomials. From this point on all formulas can first be considered in abstract matrix variables $\phi,\psi$, then substituted by these bounded-degree polynomials.

**Extract quotient and corner maps in bounded degree.** For each basis vector $x=[e_j,x]$ in $N$, derive $\phi(x)=[\phi(e_j),\phi(x)]$. Its diagonal entries vanish, so $N$ is preserved by $\phi$, and similarly by $\psi$. For each $W$-basis vector use the prescribed identity link expressing it as a product of two $N$-basis vectors. In that product, terms involving forbidden diagonal entries of the images vanish by the already derived linear equations. Thus $W$ is preserved. Project the inverse equations to obtain mutually inverse quotient matrices $\alpha,\beta$ on $A/N$, and inverse pairs on $M=N/W$ and $W$. Up to this point every calculation needs degree at most two in $\phi,\psi$.

Put $\alpha_{ki}$ for the $k$-th quotient coordinate of $\phi(e_i)$, and define $\beta$ similarly using $\psi$. Their rows are partitions of 1 by orthogonal idempotents, by the multiplication and unit constraints. Multiply $(\alpha\beta)_{kk}=1$ by $\alpha_{ki}$. Row orthogonality gives $\alpha_{ki}\beta_{ik}=\alpha_{ki}$. The same calculation with $\beta\alpha$ gives $\alpha_{ki}\beta_{ik}=\beta_{ik}$. Thus $\alpha=\beta^{\mathsf T}$ in degree at most three. The columns of $\alpha$ are consequently partitions of 1 by orthogonal idempotents as well.

Fix consecutive input vertices $i,i+1$, and choose a basis vector $x$ in the nonzero component $e_{i+1}Me_i$. The left and right bimodule equations for $\phi_M(x)$ are obtained from the products by $e_{i+1}$ and $e_i$. In a target corner $e_lMe_k$ they give each output coordinate $\mu$ the two relations $\mu=\alpha_{l,i+1}\mu=\alpha_{k,i}\mu$. For any pair $b\ge a$, multiply by $\alpha_{b,i}\alpha_{a,i+1}$. Every coordinate in a different target corner vanishes by column orthogonality, and the corner $e_aMe_b$ is zero by construction. Apply the inverse coordinate map of $M$ and read the entry of the original basis vector $x$. This gives
$$
\alpha_{b,i}\alpha_{a,i+1}=0\qquad(b\ge a)
$$
in degree at most four. More explicitly, the inverse map is linear in $\psi$, and the vanishing coordinates on which it is applied are already cubic, so the final step has degree at most four.

For $i<j-1$, insert $\sum_h\alpha_{h,j-1}=1$ in $\alpha_{b,i}\alpha_{a,j}$ with $b\ge a$. Each term in the sum vanishes by the shorter-distance incompatible pair if $h\le b$, and by the consecutive incompatible pair if $h>b\ge a$. This extends the equations to all $i<j$ in degree three beyond the prepared lines. To force $\alpha=I$, process rows $k$ in increasing order. For $i>k$, expand $\alpha_{ki}$ against the column sum at $k$. Terms with output index $h<k$ vanish by earlier rows and all $h\ge k$ vanish by the just-derived incompatible pair. The already fixed columns below index $k$ give $\alpha_{ki}=0$ for $i<k$. The row sum forces $\alpha_{kk}=1$, and column orthogonality forces the remaining entries of that column to vanish. The resulting identities also give $\beta=I$. This procedure uses polynomially many operations on entries and works over any commutative ring. In particular it proves the claimed quotient statement without requiring a ring to have only trivial idempotents.

The projected bimodule equations now give that $\phi_M,\phi_W,\psi_M,\psi_W$ preserve the indicated corners, with mutual inverse maps on each. Apply the product equation in the given link and data and ruler corners. It gives the two identities $H_tX_\lambda=\eta_\lambda Y_\lambda G_s$ and $\rho_t=\eta_\lambda\rho_s$ of §1. Take the inverses of the corner scalars from $\psi$. Multiplying the ruler identity by the two named scalar inverses gives $\rho_t^{-1}\eta_\lambda=\rho_s^{-1}$. Consequently the prescribed substitutions $F_s=\rho_s^{-1}G_s$, $\widehat F_s=\rho_s G_s^{-1}$, and the target versions derive the two-sided inverse and all link equations in constant degree. Substituting the identity-link equalities into the original links derives the source diagram axioms, now in $F_{s_v},\widehat F_{s_v}$.

**From diagram proofs to tensor proofs.** The resulting diagram variables are polynomials in the tensor variables of bounded degree, say $c$. The preceding derivations of their axiom images have bounded degree and polynomial size. To replay a diagram proof, substitute those polynomials and expand a multiplication by one substituted variable into additions of individual monomial multiples. This has degree at most $c$ times the original proof degree, or the prepared axiom bound if larger. Expansion has polynomial cost at fixed degree, since each variable image has bounded degree and polynomially many terms in the tensor dimension.

## 3. An explicit degree separation on associative multiplication tensors

**Corollary.** For every prime $p$ and every $k_0\ge 1$, there is an explicit pair in characteristic $p$ of unital associative multiplication tensors of side length and rank $\Theta(p^{k_0})$ requiring PC degree $\Theta(p^{k_0})$. Every negative pair in the construction, over every field, has a constant-degree, polynomial-sparse-size refutation in $\mathrm{PC}+\mathrm{Inv}$, with the matrix inversion substitution rule of Galesi–Grochow–Pitassi–She. No coordinate field equations occur in either assertion.

Take the one-vertex one-loop diagram with $q=p^{k_0}$, source loop $\operatorname{diag}(I_q,0_{2q})$ and target loop $\operatorname{diag}(I_{2q},0_q)$. The two diagram representations are nonisomorphic by the loop ranks. From the linear intertwiner equations the off-diagonal blocks of $F$ between the 0 and 1 eigenspaces vanish. Therefore the inverse products give the two-sided rectangular inverse equations on the 1-eigenblocks of $F,\widehat F$, in degree at most two. For the other direction specialize $F=\operatorname{diag}(U,V)$ and $\widehat F=\operatorname{diag}(V,U)$ for $U,V$ of shapes $2q\times q$, $q\times2q$. Each diagram axiom then specializes to zero or a rectangular inverse axiom. The known exact PC degree of $UV=I_{2q},\,VU=I_q$ in characteristic $p$ is $\min(q+2,2p^{v_p(q)})=q+2$. Thus the diagram degree is $q+2$, and the two degree transfers yield the claimed asymptotics. [Exact rectangular inverse degree](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/ExactMatrixProofDegrees/ConjugacyDegree.md).

For the general $\mathrm{PC}+\mathrm{Inv}$ upper bound, let $E=\operatorname{End}_Q(X\oplus Y)$. The reverse arrow equations for $\widehat F$ follow in degree three by multiplying the forward equations by the inverse maps on each side. Project $F,\widehat F$ by fixed linear maps to the spaces of forward and reverse intertwiners. Each projection error is in the linear span of the arrow equations since it vanishes on their linear kernel. By multiplying those differences by linear entries, the projected intertwiners inherit both inverse products in degree at most three.

Over the base field, write the decompositions of $X,Y$ into indecomposables, and let $a_i,b_i$ denote the multiplicities of their distinct common types, with multiplicity zero if absent. In the corresponding semisimple factor of $E/\operatorname{rad}E$, the two summand projectors have ranks $a_i,b_i$ over a division algebra $\Delta_i$. This follows by reducing the blocks within each indecomposable type modulo the radical of its local endomorphism algebra. A composition through a different type has radical image because an invertible composite would split off an isomorphic indecomposable. Project the two inverse products to a factor with unequal multiplicities, which exists by Krull–Schmidt. The projection is linear on coordinates and gives two inverse products over $\Delta_i$ between rectangular matrices with unequal sizes. Applying the left regular representation of $\Delta_i$ gives the same products for rectangular matrices over the base field with sizes $a_i\dim_k\Delta_i$ and $b_i\dim_k\Delta_i$. Either there is a literal nonzero constant, or the larger identity product can be padded by zero columns and rows to a square identity product. Inversion then gives the reverse square identity product, whose padded diagonal equation is a nonzero constant. All replacements here are linear in the projected diagram variables, and moving the same proof to the tensor variables uses the polynomial substitutions of §2. The substituted matrix inversion rule is among the allowed rules in $\mathrm{PC}+\mathrm{Inv}$. The entire proof has constant degree and polynomial sparse size, since each matrix operation is a polynomial number of bounded-degree coordinate steps. [Galesi–Grochow–Pitassi–She, §1.2](https://arxiv.org/html/2305.19320#S1.SS2).

## Scope and antecedents

Futorny–Grochow–Sergeichuk proved decision reductions from systems of tensors to ordinary tensor isomorphism. Grochow–Qiao also used algebras with nilpotent radical in their reductions. The earlier portfolio treats presented-module diagram decision, all-linear-restriction functors in the directions specified there, and exact source-side quiver proof degree. The construction here transfers witnesses and proof degree in both directions for *ordinary* tensor isomorphism and preserves a linear bound on output rank. It gives an isomorphism-groupoid retract, so makes no assertion about lifting noninvertible diagram maps to all-covariant tensor maps. The known linear lower bounds in tensor rank include other tensor families. The separation above concerns multiplication tables of the unital associative algebras in §1, and the constant upper bound is for $\mathrm{PC}+\mathrm{Inv}$ on this entire image. These are prose proofs. [Wildness for tensors](https://arxiv.org/abs/1810.09219), [Tensor Isomorphism-Completeness](https://doi.org/10.1137/21M1441110), [Prior sparse TI degree bounds](https://github.com/Dugongue/MathProofs/tree/5c79909f4154482965afbd5348f4a3e4284c2d53/TensorSparsePCBounds).
