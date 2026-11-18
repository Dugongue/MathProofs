# Tensor-isomorphism completeness with a fixed simple Levi factor

The complexity class in Grochow's Open Question VII.1 was already determined by later work. Grochow–Qiao Part I, Corollary 6.2(1), gives tensor-isomorphism hardness for square-zero abelian matrix Lie algebras, which lie in the requested class by taking zero semisimple factor. Matrix Lie algebra conjugacy is a special case of matrix-space conjugacy, which reduces to three-tensor isomorphism. The strengthening below keeps a fixed nonzero simple Levi factor and a nonzero abelian radical with nontrivial Levi action. The encoded Lie algebras are perfect and centerless. The reduction gives the full ambient transporter up to an explicit factor and radical shear. [Grochow, CCC 2012, Question VII.1](https://sites.math.washington.edu/~billey/classes/lie/bulletins/grochow.2012.pdf#page=10) · [Grochow–Qiao, Part I, §6, Corollary 6.2 and Observation B.1](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full)

## The class

Let $F$ be the coefficient field. Set $d=2$ in characteristic other than two and $d=3$ in characteristic two. Put $W=F^d$ and $\mathfrak s=\mathfrak{sl}(W)$. The following promise class is TI-complete over $F$ under polynomial-time many-one reductions in the same input model as ordinary tensor isomorphism. The input is a spanning list of explicit matrices. The class consists of perfect matrix Lie algebras with a nonzero abelian radical $R$, satisfying $RR=0$ under ambient matrix multiplication, and with simple Levi factor isomorphic to $\mathfrak s$. More specifically, hardness holds with the displayed form of the Levi representation, with its basis supplied. The radical is a direct sum of copies of the standard module. In particular, $[L,R]=R$ and $Z(L)=0$.

Over $\mathbb Q$ and explicitly represented finite fields the reductions take polynomial bit time. Over arbitrary exact coefficient fields they are polynomial-time field-arithmetic reductions. The complex case uses the exact arithmetic model of the original question. The conjugating matrix always belongs to the original coefficient field.

## Encoding a rectangular matrix space

Start with $\mathcal M\leq\operatorname{Hom}_F(V,U)$ for nonzero vector spaces $U,V$. Two such spaces are equivalent when some $A\in\operatorname{GL}(U)$ and $B\in\operatorname{GL}(V)$ give $A\mathcal M B^{-1}=\mathcal M'$. A three-tensor is represented by its space of slices on the first two modes. Linear elimination recovers a basis for that space. If the two original tensors have the same mode dimensions, they are isomorphic exactly when these slice spaces are equivalent. For the converse even when slices are dependent, view each tensor as a linear map from the dual third mode to its slice space. A left-right equivalence identifies the images, and the image isomorphism lifts to an isomorphism of the domains by choosing complements to the equal-dimensional kernels. Dualize that domain isomorphism to obtain the third factor map.

On $E=(W\otimes U)\oplus V$, define

$$
 L(\mathcal M)=
 \left\{
 \begin{pmatrix}
    s\otimes I_U & r\\
    0 & 0
 \end{pmatrix}
 :\ s\in\mathfrak s,\quad r\in W\otimes\mathcal M
 \right\}.
$$

Here $W\otimes\mathcal M$ lies in $\operatorname{Hom}(V,W\otimes U)$. The top-left copy of $\mathfrak s$ is a subalgebra. The upper-right block space is an abelian ideal of square-zero matrices. The bracket with the Levi factor acts on the $W$ slot. Forming the matrices uses a basis of $\mathfrak s$, a basis of $W$ and a basis of $\mathcal M$. The ambient matrix size is $d\dim U+\dim V$, a constant-factor increase compared with the rectangular block embedding.

The standard $\mathfrak s$-module has no invariant vectors, is irreducible, and its endomorphisms commuting with $\mathfrak s$ are exactly the scalars. All off-diagonal matrix units belong to $\mathfrak s$. They generate the full associative matrix algebra since their products include the diagonal matrix units. This also gives $\mathfrak sW=W$.

In characteristic other than two, the basis $H,E_{12},E_{21}$ of $\mathfrak{sl}_2$ consists of the three eigenvectors of $\operatorname{ad}H$ with distinct eigenvalues $0,2,-2$. Applying spectral projections to a nonzero ideal shows it contains a basis vector. The bracket relations give the other two. In characteristic two, take $\mathfrak{sl}_3$. The adjoint actions of the trace-zero diagonals split it into the diagonal subspace and the three spaces spanned by $E_{ij},E_{ji}$ for the unordered pairs $\{i,j\}$. These are distinct simultaneous eigenspaces because the character on each pair is the remaining diagonal entry. Their projections are polynomials in the two commuting adjoint operators of the diagonals $(1,1,0)$ and $(1,0,1)$. A nonzero ideal contains a nonzero diagonal or a nonzero element $aE_{ij}+bE_{ji}$. A nonzero diagonal is nonscalar, so its bracket with some matrix unit yields that unit up to nonzero scale. In the second case bracket with $E_{jk}$ if $a\ne0$ and with $E_{ik}$ otherwise, for the third index $k$, again yielding a matrix unit. Bracket a matrix unit $E_{ij}$ in the ideal with $E_{ji}$ to obtain $E_{ii}-E_{jj}$. Its brackets with the four matrix units incident to the third index give those units. Their brackets then give all off-diagonal units and diagonal differences. Thus $\mathfrak s$ is simple and noncommutative in each required characteristic.

The quotient of $L(\mathcal M)$ by its upper-right ideal is this simple noncommutative algebra. Every solvable ideal maps to zero in the quotient. The upper-right ideal is therefore the radical. Since $\mathfrak s$ is perfect and $\mathfrak sW=W$, the full algebra is perfect. A central element must project to zero and must lie in the invariant part of $W\otimes\mathcal M$, which is zero. As an abstract Lie algebra $L(\mathcal M)$ is the semidirect product of $\mathfrak s$ with $\dim\mathcal M$ copies of its standard module. Matrices coming from two spaces of equal dimension are thus always abstractly Lie-isomorphic, even when they fail the ambient conjugacy test.

## Reflection and all transporters

The span $L(\mathcal M)E$ of the images of the input matrices is exactly $W\otimes U$. Containment follows from the block form. Equality follows already from $\mathfrak sW=W$. Thus a conjugating matrix $P$ has block form

$$
 P=\begin{pmatrix}D&Z\\0&B\end{pmatrix}
$$

with $D,B$ invertible. On the intrinsic subspace $W\otimes U$, the restrictions of Lie algebra elements form the copy of $\mathfrak s$ tensor $I_U$. Consequently some Lie automorphism $\varphi$ of $\mathfrak s$ satisfies

$$
 D(s\otimes I_U)=(\varphi(s)\otimes I_U)D
 \qquad(s\in\mathfrak s).
$$

View $D$ as a matrix of blocks $D_{ij}:W\to W$ indexed by a basis of $U$. Each block intertwines the standard representation with its twist by $\varphi$. At least one block is nonzero. Let $C$ be such a block. It is invertible because both representations are irreducible. Then $C^{-1}D_{ij}$ commutes with $\mathfrak s$ and is therefore a scalar for every block, including the zero ones. These scalars form an invertible matrix $A$ on $U$, and $D=C\otimes A$. Conversely every invertible $C$ on $W$ normalizes $\mathfrak{sl}(W)$.

The radical is intrinsic as well. Its upper-right blocks are transported by $P$ to

$$
 (C\otimes A)(W\otimes\mathcal M)B^{-1}
       =W\otimes(A\mathcal M B^{-1}).
$$

This is $W\otimes\mathcal M'$ precisely when $A\mathcal M B^{-1}=\mathcal M'$, by contracting with a nonzero linear functional on $W$. Conversely, such $A,B$ give a conjugator with diagonal blocks $I_W\otimes A$ and $B$. This uses only the restrictions of the Lie algebra action to the intrinsic image space. No choice of Levi conjugation is needed.

The upper-right block obtained by conjugating a pure Levi element is $-((CsC^{-1})\otimes I_U)ZB^{-1}$. Hence all such elements land in $L(\mathcal M')$ exactly when the class of $ZB^{-1}$ in $W\otimes(\operatorname{Hom}(V,U)/\mathcal M')$ is annihilated by every $s\in\mathfrak s$. This module has zero invariant part. The full transporter is therefore precisely

$$
 \left\{
 \begin{pmatrix}I&R'\\0&I\end{pmatrix}
 \begin{pmatrix}C\otimes A&0\\0&B\end{pmatrix}
 :\
 R'\in W\otimes\mathcal M',\
 C\in\operatorname{GL}(W),\
 A\in\operatorname{GL}(U),\
 B\in\operatorname{GL}(V),\
 A\mathcal M B^{-1}=\mathcal M'
 \right\}.
$$

Its possible determinants are exactly $\det(C)^{\dim U}\det(A)^d\det(B)$ over these choices.

## Completeness

If the tensor dimensions or slice ranks differ, the answer is no. If both tensors vanish with equal dimensions, the answer is yes. Such cases can be mapped to fixed promised pairs with nonzero radicals. A fixed yes-pair uses the same image twice. A fixed no-pair uses the images of the one-dimensional spaces spanned by the $2\times2$ matrices $\operatorname{diag}(1,0)$ and $I_2$, which are distinguished by rank. All other inputs reduce to algebras with nonzero radicals using linear elimination and matrix assembly.

For the reverse reduction, every promised input is already an instance of matrix-space conjugacy. Its standard reduction to 3TI gives membership in TI. The same upper bound applies to the whole class in Grochow's original question. The published abelian case establishes the matching hardness for that whole class. The fixed simple quotient, perfectness, centerlessness, and nonzero radical action give the stronger promised result. [Grochow–Qiao, Part I, Theorem B and Corollary B, using Futorny–Grochow–Sergeichuk for the reverse reduction](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full)
