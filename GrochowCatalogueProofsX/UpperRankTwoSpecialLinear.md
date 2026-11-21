# Special-linear tensor isomorphism for all upper-rank-two slice spaces

## GP-0269

Let $T,T'$ be three-tensors over an explicitly presented finite field. Suppose that every matrix in one of $T$'s three slice spaces has rank at most two. Then special-linear equivalence can be decided deterministically in time polynomial in the dense input size and $\log q$, uniformly over all finite fields. Hence this entire class admits a same-field many-one reduction to ordinary three-tensor isomorphism by outputting the constant yes or no instance after the decision. The key case is a mixed row-column compression with both matrix sides unbounded. Its stabilizer determinant image has at most five independent scalar parameters, with all parameters realizable.

## Essential spaces and determinant requirements

The essential space on a tensor leg is the image of its flattening onto that leg. A tensor transporter restricts to a transporter on all three essential spaces, and any such restricted transporter extends by independent isomorphisms on chosen complements. On legs with unused dimensions, the complement isomorphisms can absorb any prescribed nonzero determinant. On a full essential leg, the determinant-one condition remains in force. Thus it suffices to solve exact equivalence on concise tensors with a selected subset of determinant constraints.

Choose the upper-rank-two slice mode and replace the tensor by its slice space $S\subseteq\operatorname{Hom}(U,W)$ with a basis coming from the third leg. An ordinary transporter consists of invertible matrices $P,Q$ with $P S Q=S'$, where $Q$ represents the transpose of the second tensor leg's map in fixed coordinates. The slice-label map is forced because the third-leg flattening is injective on its dual. For a stabilizer, if $R\colon S\to S$ is the induced linear map, the tensor determinant triple is
$$
(\det P,\det Q,(\det R)^{-1}).
$$
An ordinary transporter exists precisely when the slice spaces are left-right equivalent. Once one is available, its possible determinant triples form a coset of this stabilizer image. The same detection can be done on a target of arbitrary upper rank, since the upper-rank promise is invariant and polynomially recognizable. [Ordinary equivalence and upper-rank recognition](RankTwoMatrixSpaceEquivalence.md)

## Mixed compressions

Assume both essential matrix dimensions are at least three, and the unique mixed compression flag is a domain hyperplane $U_0$ and codomain line $W_0$. Use bases with $U=k\oplus E$, $W=k\oplus F$, $U_0=E$ and $W_0=k\oplus0$. Write the matrix space in the form
$$
A=\begin{pmatrix}a&b\\c&0\end{pmatrix},
\qquad b\in E^*,\quad c\in F.
$$
Put $e=\dim E$ and $f=\dim F$. Its arm image $M\subseteq E^*\oplus F$ is a fiber product over a common quotient $H$ of dimension $h$. Let $K_E,K_F$ be the kernels of the arm quotient maps, of dimensions $e-h,f-h$. Let $\epsilon=1$ if the pivot line belongs to $S$ and $\epsilon=0$ otherwise. In the latter case the pivot is a linear function of the arms and can be cleared by fixed unipotent shears, as in the ordinary equivalence proof. Work in this normalized presentation. The determinants of a stabilizer image do not depend on these coordinating basis changes.

Flag-preserving stabilizers have left and right matrices
$$
P=\begin{pmatrix}\alpha&u\\0&P_0\end{pmatrix},
\qquad Q=\begin{pmatrix}\beta&0\\v&Q_0\end{pmatrix}.
$$
The arm maps are $b\mapsto\alpha bQ_0$ and $c\mapsto\beta P_0c$. Preserving the fiber product means that these maps preserve $K_E,K_F$ and induce the same automorphism on $H$. Write $\xi,\eta,\zeta$ for the determinants on $K_E,K_F,H$, respectively. Each can be arbitrary in $k^\times$ when its space has positive dimension, and is one when the space is zero. Choose compatible block-diagonal automorphisms on the arms to realize all allowed $\xi,\eta,\zeta$. For any desired $\alpha,\beta\in k^\times$, recover invertible $P_0,Q_0$ by dividing out the corresponding scalar. Taking the shears zero preserves the normalized space in both values of $\epsilon$, so every choice is realized.

The determinants of the full arm maps are $\xi\zeta$ and $\eta\zeta$. On $M$ the determinant is $\xi\eta\zeta$ by its quotient sequence with kernel $K_E\oplus K_F$. The pivot line, when present, adds a factor $\alpha\beta$. Hence the exact determinant triple is
$$
\big(
  \alpha\beta^{-f}\eta\zeta,
  \beta\alpha^{-e}\xi\zeta,
  (\alpha\beta)^{-\epsilon}(\xi\eta\zeta)^{-1}
\big).
$$
Nonzero shears can change only a pivot-coordinate off-diagonal block and produce no further determinant values. The ordinary transporter of any pair passing the uncolored classification is found explicitly by mapping both spaces to the same standard fiber product coordinates. A desired determinant correction is now a constant-size monomial system over $k^\times$.

## Primitive and pencil cases

For the wide primitive case over $q>2$, the reduced slice space is equivalent to the full $3\times3$ alternating space $S_0$. A pair $P,Q$ preserves $S_0$ precisely when $P=cQ^{\mathsf T}$ for some $c\in k^\times$. To show this, put $X=Q^{-\mathsf T}P$. Congruence preserves alternation, so $XA$ is alternating for all $A\in S_0$. For a basis alternating matrix supported on indices $i,j$, its only possibly nonzero columns after left multiplication are columns $i,j$. Alternation forces its other rows to vanish, showing $X_{\ell i}=X_{\ell j}=0$ for $\ell\notin\{i,j\}$. Varying the pair makes $X$ diagonal, and the $i,j$ entries require its diagonal entries equal. This argument also works in characteristic two for the alternating space. Conversely $P=cQ^{\mathsf T}$ induces ordinary congruence followed by scaling. Its determinant on the three-dimensional alternating space is $c^3(\det Q)^2$, from the exterior-square action. Thus the exact triples are $(c^3d,d,c^{-3}d^{-2})$ for $c,d\in k^\times$.

A transporter to $S_0$ can be recovered by solving the linear system $XS\subseteq S_0$. Ordinary equivalence implies $S=M S_0$ for some $M$ acting on the left alone, since any right multiplier of $S_0$ can be moved to the left by the congruence identity. The same argument with $XM$ shows that every nonzero solution $X$ is invertible. Thus one gets a base transporter by linear algebra, followed by the displayed determinant correction. Over $\mathbb F_2$ every invertible determinant is one, so the ordinary rank-two algorithm already handles all primitive alternatives.

If an essential leg has dimension one, the tensor is a nondegenerate pairing on the other two legs, which have the same dimension $m$. In the presentation as a one-dimensional matrix space with invertible generator $A$, $PAQ=rA$ gives the exact triples $(r^m d^{-1},d,r^{-1})$ for arbitrary $r,d\in k^\times$; rank reduction gives an ordinary transporter directly. The zero tensor is decided separately. In all other thin cases one leg has dimension two, so permute it into the pencil position. The earlier factorization-free pencil algorithm covers arbitrary singular and regular pencils, including the case of no rational roots. Its root algebra tests variable changes, and its character equations permit a selected subset of determinant constraints. For at least three geometric roots, retain precisely the desired rows of its equations (2). For one or two roots do the same in (4). In the nonsplit two-root case the residual norm has arbitrary nonzero value if the slice determinant row is absent, so it becomes a new scalar variable in the remaining two rows. For the completely singular case the correction powers in (3) depend only on the slice determinant, so use one free nonzero variable for it unless that determinant is prescribed. These modifications retain the polynomial bit bound. [Prior pencil determinant formulas and root algebra](https://github.com/Dugongue/MathProofs/blob/3454ca222e13e2f12bf232b920771763bf8a7d1a/TISLPencilsAndOrbits/Pencils.md)

Finally a monomial system with integer exponent matrix is decided by integer Smith normal form, applying its unimodular row operations to the right sides by monomial changes. Each diagonal equation $z^a=u$ then requires $u^{(q-1)/\gcd(a,q-1)}=1$, and a zero row requires $u=1$. This uses field powering and polynomial bit arithmetic, without discrete logarithms. The rank-two classification makes the cases exhaustive. The scope is upper rank two in a slice space, with no restriction on that slice space's dimension.
