# Matrix tuple isometry in characteristic two with a square-zero adjoint radical

**Status.** AI-assisted informal proof.

**Theorem.** Let $F$ be a fixed finite field of characteristic two. Given a finite-dimensional unital associative $F$-algebra $A$, an $F$-linear involution $ * $, and a self-adjoint unit $c$, decide whether $c=u^*u$ for some $u\in A^\times$. If the Jacobson radical $J$ satisfies $J^2=0$, this takes Las Vegas polynomial time in structure-constant encoding. Arbitrary finite residue field extensions, simple-factor multiplicities, and radical bimodules are allowed.

The corresponding isometry problem for ordered matrix tuples whose adjoint algebra has square-zero radical also has this bound.

## The square-zero norm equation

Compute $J$ and a matrix-factor presentation of $S=A/J$ by standard Las Vegas finite-algebra algorithms. A unital algebra section exists by separability. Compute it by correcting any unital linear lift by a linear map into $J$. Basis-product equations are linear in the correction because $J^2=0$. Write $A=S\oplus J$ using this section. [Rónyai](https://doi.org/10.1016/S0747-7171(08)80017-X) · [Eberly–Giesbrecht](https://www.sciencedirect.com/science/article/pii/S0747717199903085).

Let $\dagger$ act by the quotient involution on $S$ and the given involution on $J$. It is an anti-involution, since for $s,t\in S,\ v\in J$, $(svt)^*=t^\dagger v^\dagger s^\dagger$; terms with two radical factors vanish. The map $\delta(s)=(s^\dagger)^*-s$ is a derivation $S\to J$. Separability makes it inner: applying $x\otimes y\mapsto x\delta(y)$ to the separability-element identity $\sum sa_i\otimes b_i=\sum a_i\otimes b_is$, with $\sum a_ib_i=1$, proves the claim. Thus one can find $\eta\in J$ by linear equations with
$$
 s^*=(1+\eta)s^\dagger(1+\eta)^{-1}.
$$
Applying $ * $ twice shows that $k=\eta+\eta^\dagger$ centralizes $S$.


First solve the norm equation in $S$. On exchanged factors with involution $(X,Y)^\dagger=(Y^t,X^t)$, use $(1,C^t)$ for target $(C,C^t)$. On a self-dual factor write $s^\dagger=B^{-1}\sigma(s)^tB$, where $B$ is invertible and $\sigma(B)^t=B$. Compute $B$ by linear equations, with Hilbert 90 for scalar normalization when the center involution $\sigma$ is nontrivial. In the first-kind case the symmetry scalar squares to one, hence is one. The residue norm equation asks if $B$ and $B\bar c$ are isometric. Standard symplectic elimination and Hermitian diagonalization construct isometries in polynomial time. For a Hermitian diagonal entry a square root in the fixed field is a norm preimage. For symmetric nonalternating forms use the bilinear conversion in the decision section.

If the residue equation succeeds, lift one solution to $a$. Replace $c$ by $(a^*)^{-1}ca^{-1}=1+h$, where $h=h^\dagger\in J$. This preserves solvability. Every candidate is $g(1+v)$, with $g\in U(S,\dagger)$ and $v\in J$. Its norm is $1+\eta+g^\dagger\eta g+v+v^\dagger$. Thus the exact condition is
$$
 h+\eta+g^\dagger\eta g\in \rho(J),\qquad \rho(v)=v+v^\dagger. \tag{1}
$$
The left side is $\dagger$-fixed because $k$ centralizes $S$.

## The surviving bimodules

Let $e_i$ be the central primitive idempotents of $S$ and $i\mapsto i^*$ the involution on indices. The Peirce blocks $e_iJe_j$ are permuted by $\dagger$ as $(i,j)\mapsto(j^*,i^*)$. For a pair of distinct blocks interchanged by $\dagger$, each fixed element of their sum belongs to $\rho(J)$. Thus only blocks $j=i^*$ can matter.

In each surviving block the two center fields are isomorphic. Identify them as $E$, using the involution for an exchanged pair. Let $\sigma$ be the center involution on a self-dual block and the identity on the identified centers of an exchanged pair. Split the block into the subspaces $J_\theta=\{x:xa=\theta(a)x\ \forall a\in E\}$ over the $F$-automorphisms $\theta$ of $E$. This is the decomposition of $E\otimes_F E$ as a product of fields. It is computable by linear equations using one field generator. The involution sends $\theta$ to $\theta^{-1}$ and is $\theta^{-1}\sigma$-semilinear on left scalars. Inverse pairs of distinct summands again contribute nothing to (1). On a fixed summand with $\theta\sigma\ne1$, choose a scalar $b\in E$ with $b+\theta\sigma(b)=1$. Every fixed $z$ then equals $\rho(bz)$. The only remaining twist is $\theta=\sigma$, and there $\dagger$ is $E$-linear.


On a self-dual factor $M_n(E)$, the remaining $J_\sigma$ is a sum of copies of $M_n(E)$ with left multiplication and right multiplication twisted by $\sigma$. For example, the $E_{11}$-corner determines the multiplicity space, and matrix units identify the other corners. On each copy make the change of coordinates $Y=BX$. In these coordinates the actions $X\mapsto sXt^\sigma$ become $Y\mapsto (BsB^{-1})Y\sigma(t)$. Because $\sigma(B)^t=B$, the involution exchanges these matrix actions by transpose. Equivalently, composing $\dagger$ with matrix transpose produces a bimodule endomorphism acting only on the multiplicity space. It is $E$-linear and squares to one. Decompose its Jordan blocks into fixed lines and pairs $u,\dagger u$. Pairs contribute nothing to (1) because their fixed space equals their trace image. Each fixed line has ordinary matrix transpose as involution in $Y$-coordinates, and $\rho$ has image the alternating matrices.

In a fixed line write $Y_0=B\eta_i$ and $Y_1=B(\eta_i+h_i)$ for the two projections. If the center involution is trivial, (2) gives $Y_0+Y_0^t=k_i B$ and $Y_1+Y_1^t=k_i B$ for a scalar $k_i$. If $\sigma\ne1$, centrality forces $k_i=0$ since the left and right center actions differ. The condition on $g$ is exactly
$$
 Q_0(\sigma(g)x)=Q_1(x)\quad\hbox{for all }x,\qquad Q_j(x)=x^tY_jx. \tag{2}
$$
Indeed, the commutator part of (1) transforms $Y_0$ by $\sigma(g)^tY_0\sigma(g)$. The difference from $Y_1$ has zero polar and is symmetric. It lies in the alternating matrices exactly when its quadratic polynomial is zero.

For an exchanged pair of simple factors, normalize its involution to swap transposes. In the remaining blocks $J_{i,i^*}$ and $J_{i^*,i}$, the center twist is trivial and $k$ has zero component because it centralizes the two distinct central idempotents. Matrix units again give copies of the transpose action and a multiplicity involution. Each fixed line contributes a symmetric matrix in both source and target. If $g$ denotes the first matrix of an exchanged pair, the unitary pair is $(g,g^{-t})$. The transformations on the two blocks are $X\mapsto g^{-1}Xg^{-t}$ and $X\mapsto g^tXg$, respectively. Their diagonals give, after taking square roots, simultaneous vector and covector markings on a single $g$. All other Peirce or twist summands have already disappeared from (1), so no constraint couples distinct involution orbits of $S$.


## Deciding all markings in polynomial time

On one self-dual factor, if all the polars in (2) vanish, taking square roots turns the conditions into matching a list of linear functionals under $g$; undo $\sigma$ on their coefficients if necessary. With the fixed nondegenerate form $B$, these become matching a list of vectors, by duality. Test their linear relations and the induced partial isometry on their spans. For a symplectic or Hermitian form, Witt extension gives sufficiency.

For a nonalternating symmetric bilinear form $b$, put $\ell(x)=\sqrt{b(x,x)}$ and define $w$ by $b(w,x)=\ell(x)$. If $\ell(w)=0$, the alternating form $a=b+\ell\otimes\ell$ is nondegenerate, and the isometry problem for $b$ equals the problem for $a$ with $w$ marked. Indeed $a(w,-)=\ell$, so $b$ is recovered from $a$ and $w$. If $\ell(w)=1$, split off the canonical line $Ew$, on which the form has value 1, and use the nondegenerate alternating complement $w^\perp$. Check the scalar components of all marks and match their projections in $w^\perp$. The two cases have even and odd dimension respectively, by the ranks of the associated alternating forms. This argument also constructs an unmarked residue isometry by completing symplectic bases, with one prescribed vector in the even case.

If some polar is nonzero, the center involution is trivial and this polar is a nonzero scalar multiple of the nondegenerate alternating $B$. Retain this one quadratic form on each side. Subtract the suitable scalar multiples from every other quadratic to leave zero-polar forms. The conditions become one nonsingular quadratic isometry with a list of linear markings. Compare the ambient quadratic types via their Arf invariant. Convert the markings into vectors using the polar form. Test the linear relations and quadratic form on their spans. Isometric ambient forms and a partial isometry on the marked spans give a global isometry by Witt extension. The test on spans needs only basis values and pairwise polar values. These uses of Witt extension allow degenerate marked subspaces and have nondegenerate ambient polar forms. [Magma's description of the symplectic, unitary and characteristic-two quadratic extension routines](https://docs.magma-maths.org/v2.30-1/MatricesLinearAlgebra/PolarSpaces/isom-sim.html).

For an exchanged pair, write the marks as $g v_i=v'_i$ and $f'_j g=f_j$. The vector marks must define an isomorphism of spans $U\to U'$, compatible with the stacked maps $f,f'$ to $E^t$. The images of $f,f'$ must agree. These conditions suffice: extend bases in $U\cap\ker f$ and $U'\cap\ker f'$ to bases of the two kernels, and extend the bases of $f(U)=f'(U')$ in the common image using chosen lifts. This builds the required invertible $g$.

All steps use polynomially many operations on algebras and spaces of polynomial dimension. The center field degrees are at most $\dim_F A$. Computing trace kernels, matrix coordinates, normalizing factors and all marking tests takes polynomial time. Combining the independent simple-factor tests decides (1), which in turn decides the original norm equation. Its only randomized subroutines can be taken Las Vegas.


## Ordered matrix tuples and scope

Close the two tuples under transpose. This keeps the isometry problem unchanged. Use finite-field module isomorphism for the Kronecker representation to find an invertible left–right pair $X,Y$ with $X^t A_iY=B_i$, or reject if none exists. Let
$$
 {\cal A}=\{(L,R):L^tA_i=A_iR\text{ for every }i\},
 \qquad (L,R)(L',R')=(LL',R'R),\quad (L,R)^*=(R,L).
$$
The transpose conditions make this a unital algebra with involution. They give $Y^tA_iX=X^tA_iY$, so $c=(YX^{-1},YX^{-1})$ is a self-adjoint unit of ${\cal A}$. If $P$ is an isometry then $(PX^{-1},YP^{-1})$ has norm $c$. Conversely a norm solution $(L,R)$ gives $RL=YX^{-1}$ and the isometry $P=LX$. Constructive left–right equivalence and the norm formulation are standard. [Ivanyos–Qiao](https://arxiv.org/abs/1708.03495) · [Qiao–Sun](https://arxiv.org/abs/2409.12457).

The square-zero hypothesis can be checked on the adjoint algebra directly. A nontrivial twisting example already occurs for $A=M_2(F[\varepsilon]/(\varepsilon^2))$. Let $\sharp$ be the entrywise extension of the adjoint for $B=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$, and set $x^*=(1+\varepsilon E_{12})x^\sharp(1+\varepsilon E_{12})^{-1}$. This squares to the identity. The residual symplectic matrix $\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$ fails to lift to a unitary: the corresponding quadratic marking is $x_2^2$, which it changes. The algorithm applies to this twisted case as well as to cases with an involution-stable algebra section.

The result is a case of the characteristic-two matrix-tuple isometry question, which the general odd-characteristic algorithm leaves open. The unrestricted finite-field and mixed-characteristic ring versions remain outside this theorem. The new step here is the reduction of the entire first-order unitary defect, including Frobenius-twisted radical bimodules, to classical isometries with markings. Publication priority has not been established. [Grochow–Qiao–Stange–Sun, Part V](https://arxiv.org/html/2611.00735v1) · [Sun, Appendix A](https://arxiv.org/html/2611.05920v1#A1).
