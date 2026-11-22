# Exact transporter schemes and local forms of compiled tensors

The linear-side labelled-network construction in the higher-order universality theorem preserves the full scheme of changes of basis after adjoining explicit smooth factors. It also preserves the set of all fppf forms over every local ring, including forms which cannot be compared by separable Galois descent. The construction works in all characteristics and uses the same multiplication tensor. [Universality construction](https://github.com/Dugongue/MathProofs/tree/b3bde958f05b17ea912394edb1edd18852b9c85d/HigherOrderUniversality)

## The theorem

Let $R$ be a commutative unital ring, and let $X,Y$ be two labelled systems of tensors in finite free modules and their duals, of the same fixed format. The order of the tensors is arbitrary. Write $I(X,Y)$ for their transporter scheme, with one change of basis per declared module. Apply the binary product markers and the linear-side compiler to obtain associative unital algebras $A_X,A_Y$, and let $T_X,T_Y$ be their ordinary multiplication three-tensors.

Use the following integers from the order-three auxiliary format. Let $r_X,r_Y$ count the designated summands of the first and second spaces of the compiler's marked bilinear map, respectively. Put $k=3+r_X+r_Y$, the number of original diagonal vertices. There are $v=2k+1$ diagonal vertices including the sentinel source and path. Let $j$ be the total rank of the strict corners of the algebra, and $M$ the sentinel rank. These integers depend on the format alone. There is a natural isomorphism of $R$-schemes
$$
\begin{split}
I(T_X,T_Y)\ \simeq\ I(X,Y)&\times \mathbb A_R^{3j}
 \times\mathbb G_{m,R}^{\,2v+2+r_X+r_Y+k}\\
 &\times\mathrm{GL}_{M,R}\times\mathrm{GL}_{2,R}^{\,k-1}.
\end{split}
$$
The projection and its identity-factor section respect composition of transporters. On automorphism group schemes this is a split quotient with the displayed smooth kernel as a scheme. The product coordinates need not give a direct product of groups.

In particular every graph of transporter equations over a base ring, including its infinitesimal functions and nilpotent fibers, survives as the source scheme times explicit smooth factors. If $R$ is local, the induced map
$$
H^1_{\mathrm{fppf}}(R,\operatorname{Aut}(X))
 \ \longrightarrow\
H^1_{\mathrm{fppf}}(R,\operatorname{Aut}(T_X))
$$
is a bijection. Here an fppf form is an object isomorphic to the specified object after a faithfully flat, finitely presented cover of $\operatorname{Spec}R$. Thus the classification by fppf forms of the network is the classification by fppf forms of its single multiplication tensor.

The statement takes the actual linear equations in tensor records. A marked relation submodule is also allowed when it is a free direct summand given by a basis. Use its unpadded basis-frame matrix. The frame coefficients are uniquely determined over every test ring, because the inclusion is split injective. For a general generator list one can apply this theorem to the network that records the padded generator maps themselves.

## Algebra transporters and the exact kernel

For every commutative $R$-algebra $S$, write $A=A_X\otimes S$ and $B=A_Y\otimes S$. Let $J_B$ be the ideal made up of all strict corners. It is the commutator ideal, and $J_B^3=0$. Its definition and free coordinate basis are fixed by the format. Each composition of strict corners lands in one of the projection targets or in the core output $Z$. In the compiler the two scalar-copy blocks reach every basis vector of every summand of $Z$, and every projection onto a summand is surjective. Consequently $J_B^2$ is exactly the direct sum of the output corners of these compositions. Both $J_B^2$ and $J_B/J_B^2$ are free in displayed coordinates, with formation compatible with arbitrary scalar extension.

An algebra isomorphism $F:A\to B$ preserves $J$. Modulo every residue field it fixes the ordered quotient idempotents by the sentinel and rank-one/rank-two path argument. The image of each quotient idempotent in every coordinate of $B/J_B=S^v$ is an idempotent, so the label also holds over $S$. Indeed an idempotent in every maximal ideal is zero, since its complement is a unit. Apply this to each coordinate or its complement. If $f_i=F(e_i)$ and $e'_i$ are the standard target idempotents, the element $u=\sum_i f_i e'_i$ is in $1+J_B$. It satisfies $f_i u=u e'_i$. Thus $\operatorname{Ad}(u^{-1})F$ fixes the ordered idempotents strictly. The choice of $u$ is unique: the centralizer of all $e'_i$ meets $1+J_B$ in the identity, as $e'_iJ_Be'_i=0$. This gives an isomorphism of transporter functors between all algebra isomorphisms and the strictly idempotent-preserving ones times $1+J_B$.

A strictly idempotent-preserving isomorphism consists of maps on separate Peirce corners. In each projection mark $X\times S\to X_i$, or $S\times Y\to Y_j$, the unit scalar on the one-dimensional argument can be chosen arbitrarily. The map on the output corner is uniquely forced by this scalar and the restriction of the core $X$ or $Y$ map. The projection kernels force the designated summands to be preserved. The scalar-copy equations force the transformations on the three copies of any reference or occurrence to be $a g_i,b g_i,ab g_i$, with two independent units $a,b$. Private scalar-copy lines lock the occurrence map to its reference, evaluation locks its dual to inverse transpose, and the pinned scalar on the network itself is fixed. The data blocks are therefore exactly the original transporter equations, after cancelling $ab$. Conversely, a source transporter extends uniquely once the copy and projection scales and marker maps have been chosen. The sentinel, path and tag corners have no nonzero product constraints and their maps are independent general linear maps of ranks $M,2,1$, respectively. No other corner gives a free parameter. The binary product markers in the arbitrary-order step have unique product maps whenever the named source maps are specified.

It follows that the strict algebra transporter is the source transporter times the group
$$
K_0=\mathbb G_m^{\,2+r_X+r_Y+k}\times\mathrm{GL}_M
\times\mathrm{GL}_2^{\,k-1}.
$$
On stabilizers it is a direct product: all these scales commute with source maps, and the section is the identity on every sentinel, path and tag corner. For general compositions, the normalized isomorphisms compose: in the formula $F=\operatorname{Ad}(u)\phi$, a composite with $F'=\operatorname{Ad}(u')\phi'$ has conjugator $u'\phi'(u)$ in the new target's $1+J$ and normalized part $\phi'\phi$. Uniqueness identifies these as the recovered factors. The group $1+J_B$ is affine space of dimension $j$ as a scheme using $z\mapsto1+z$.

## Ordinary three-tensor transporters

The exact isotopy calculation for unital associative algebras has the following natural form. A three-mode transporter of multiplication laws is an isotopy
$$
P(x)Q(y)=W(xy).
$$
Set $a=P(1), b=Q(1)$, so right multiplication by $b$ and left multiplication by $a$ in $B$ are invertible. A one-sided inverse is two-sided here by injectivity of the opposite multiplication identity. Thus $a,b$ are units. The map $\phi(x)=a^{-1}W(x)b^{-1}$ is an algebra isomorphism and
$$
P=a\phi,\qquad Q=\phi b,\qquad W=a\phi b.
$$
Conversely these formulas give all isotopies. Under composition, $\phi$ composes strictly and the two unit coordinates obey multiplication in $B^\times$ and $(B^\times)^{\rm op}$, with the intervening algebra map applied to the preceding units. This yields the split quotient to algebra isomorphisms. [Earlier exact isotopy theorem](https://github.com/Dugongue/MathProofs/blob/b3bde958f05b17ea912394edb1edd18852b9c85d/AssociativeIsotopyDegeneration/PROOF.md)

In our algebra every unit is the product of its unique diagonal residue lift and an element of $1+J_B$. Hence $B^\times\simeq\mathbb G_m^v\times\mathbb A^j$ as schemes. This gives the theorem on substituting the algebra transporter formula. All recovery and assembly operations are polynomial operations or inversions of specified invertible matrices, and are natural over all test rings, so they give the asserted scheme isomorphism. In particular over a finite commutative base ring $S$ the exact number of compiled transporters is the number of original transporters times
$$
 |S|^{3j}|S^\times|^{\,2v+2+r_X+r_Y+k}
      |\mathrm{GL}_M(S)|\,|\mathrm{GL}_2(S)|^{\,k-1}.
$$
The same formulas apply to dual-number and higher finite jet rings. Over a field, at a rational transporter and its corresponding compiler lift, completed local rings agree after adjoining formal power-series variables in the dimension of the smooth factor.

## Twisting and forms over arbitrary affine bases

Fix $X$, and write $H=\operatorname{Aut}(X)$ and $E=\operatorname{Aut}(T_X)$. The double unit factor is normal. Modulo $J$ both units give diagonal units, and all normalized algebra automorphisms and inner changes fix the diagonal labels. Put
$$
Q=\mathbb G_m^{2v}\times K_0,\qquad
N=((1+J)\times(1+J)^{\rm op})\rtimes(1+J).
$$
The affine group scheme $E$ is $N\rtimes(H\times Q)$. The normal subgroup $N$ retains the two principal-unit factors and the idempotent conjugator. A section of $H\times Q$ chooses diagonal lifts of the two unit residues, the strictly idempotent-preserving scale and marker transformations of $K_0$, and the section of $H$. The Peirce maps commute with the diagonals since they fix all $e_i$. The $K_0$ and $H$ sections commute by the explicit corner formulas. These facts verify that this section is a homomorphism with the prescribed direct product domain.

Each of the two principal-unit factors is preserved by $H\times Q$, and the action on the third $1+J$ quotient of $N$ also preserves the principal-unit filtration. In the first two factors the action is by the normalized algebra maps and left or right diagonal conjugation. In the third quotient it is by the normalized algebra maps. Each $1+J$ has the invariant sequence $1+J^2\subset 1+J$, with successive quotients the additive groups of $J^2$ and $J/J^2$. This follows from $J^3=0$. On both groups all the indicated actions are induced by linear maps.

Twist these normal sequences by any $(H\times Q)$-torsor $\xi$. The vector-group quotients descend to additive groups of finite locally free modules. Such groups have trivial first fppf cohomology over an affine scheme, by faithfully flat descent for quasi-coherent modules. Successively applying the exactness of torsor sequences gives $H^1(R,N^\xi)=1$. More concretely, after the torsor for a quotient has become trivial, its chosen trivialization gives a reduction to the subgroup, so triviality of the subgroup torsors forces triviality of the original torsor. The section lifts every $(H\times Q)$-torsor to $E$. Comparing different lifts by twisting with the section lift uses torsors for $N^\xi$; this vanishing makes each lift class unique. Consequently
$$
H^1_{\rm fppf}(R,E)\ \simeq\
H^1_{\rm fppf}(R,H)
\times\operatorname{Pic}(R)^{2v+2+r_X+r_Y+k}
\times\mathcal V_M(R)\times\mathcal V_2(R)^{k-1},
$$
where $\mathcal V_m(R)$ is the set of isomorphism classes of locally free $R$-modules of rank $m$. This is a formula for forms allowing locally free modules in both categories. If $R$ is local, every such module is free, the extra factors are singletons, and compilation identifies the network forms with the compiled tensor forms on the original free formats. [Faithfully flat descent for modules](https://stacks.math.columbia.edu/tag/023R) · [Torsors and torsor classes](https://stacks.math.columbia.edu/tag/03AG)

## Realizing arbitrary affine group schemes as split stabilizer quotients

Let $G$ be an affine group scheme of finite type over a field $k$. Then $G$ occurs as a split quotient of the ordinary stabilizer of one concise three-tensor over $k$, with a smooth kernel of the explicit form above. This includes nonsmooth and nonreduced $G$. Their fppf torsor classes over any field extension and, more generally, over any local $k$-algebra, are exactly the fppf forms of the constructed tensor.

To prove this, embed $G$ as a closed subgroup scheme of $\mathrm{GL}_n$. In its defining ideal choose polynomial generators $f_1,\ldots,f_s$ in matrix coordinates, clearing determinant denominators, and let $D\ge1$ bound their total degrees. Put $W=k[x_{ij}]_{\le D}\subset k[\mathrm{GL}_n]$, with right-translation action $g:f(M)\mapsto f(Mg)$. This action preserves degree and therefore $W$. Let $U=W\cap I(G)$. For any $k$-algebra $S$, $U_S=W_S\cap I(G)_S$, by flatness over the field $k$. Right translation by a point of $G(S)$ preserves $U_S$, because it preserves the subgroup and its ideal. Conversely, if $g\in\mathrm{GL}_n(S)$ preserves $U_S$, then evaluating $g f_i$ at the identity gives $f_i(g)=0$ for every $i$, so $g\in G(S)$. This is a direct subspace-stabilizer realization on all test rings. [Affine linearity over a field and Chevalley's theorem](https://arxiv.org/html/2012.05708v3#S2)

For a small tensor network realizing this action, introduce a pinned rank-$n$ row-index sort $F$, with the first basis vector and the shift endomorphism of its ordered basis as marks. Their common stabilizer on $F$ is the identity. The canonical product $F\otimes k^n\to W_1$, where $W_1$ is the degree-one variable sort, forces the $n$ row copies of the same original basis change. Give $W$ the multiplication table of $k[x_{ij}]$ truncated above degree $D$, with its usual monomial basis. Add the linear inclusion $W_1\to W$. A multiplication-preserving invertible change on $W$ fixes its identity and is determined by its degree-one generators, hence realizes the stipulated translation. The final mark is the inclusion of $U$ using its fixed basis, with a unique induced change on the domain. Over every test $S$, this network stabilizer is $G$. Its constant number of records have total slot rank $O(\binom{n^2+D}{D})$, and the linear compiler gives the same output side bound. This bound concerns the specified subspace realization; a defining list alone is not assumed to give its basis in polynomial time. The multiplication tensor is concise in both input modes by evaluation at the unit, and it spans its output mode by the same evaluation.

Existing exact isotopy results handle the last change from associative law to multiplication tensor. The reduced orbit-closure compiler handles directional degeneration and smooth geometry on reduced orbit closures. The theorem here concerns the entire transporter scheme, including nonreduced structure, and descends all forms by controlling every twisted kernel over local rings. The full argument is a written proof.
