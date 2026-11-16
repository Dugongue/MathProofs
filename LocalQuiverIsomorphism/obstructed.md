# Tensor isomorphism in genuinely obstructed local quiver deformations

## Theorem

Fix $e\ge 3$. Let $R_e$ be $k[t]/(t^e)$ for any field $k$, or $\mathbb Z/p^e\mathbb Z$ with $t=p$ and $k=\mathbb F_p$. There is an explicit family of four-vertex square-zero residue algebras with the following properties.

1. On a natural open subset of their finite free unmarked lifts, every lift over $R_e$ has a normal form $(M,E)$. Here $M$ is a three-tensor over $R_{e-1}$ and $E$ is a three-tensor of the same format over $k$. Two normal forms are isomorphic exactly when one triple of invertible mode maps transports $M$ and its reduction transports $E$.
2. The lift extends to $R_{e+1}$ exactly when $E=0$. In that case it extends compatibly to every higher order.
3. For an explicit choice of predecessor over $R_{e-1}$ for each format, the entire last-step unmarked comparison has an effective linear slice over $k$. It is an orbit problem for a connected split reductive group on a pair consisting of a tangent-quotient class and an ordinary tensor. Ordinary three-tensor isomorphism over $k$ is polynomial-time equivalent to isomorphism of the lifts of this predecessor that fail to extend to $R_{e+1}$. The reductions have linear output dimensions in both directions, with an explicit transporter decoder.

The word unmarked means that the comparison need not fix a chosen identification with the common reduction. The theorem identifies the obstruction and gives the comparison problem on the entire fiber above the chosen predecessor.

## 1. Peirce normalization of all lifts

Use four vertices $0,1,2,3$, with diagonal subalgebra $k^4$ and strict forward spaces
$$
C_{01}=X,\quad C_{12}=Y,\quad C_{23}=L,\quad
C_{02}=Z,\quad C_{13}=Y',\quad C_{03}=Z'.
$$
The rank of $L$ is one. The positive ranks of $X,Y,Z$ are $a,b,c$, respectively. The ranks of $Y'$ and $Z'$ are $b,c$. All backward spaces vanish. The residue product of any two strict spaces is zero. In a finite free associative unital $R_e$-algebra lifting this residue algebra, lift the four orthogonal idempotents and apply the Peirce decomposition. Each corner is a finite free direct summand with the indicated rank. Each diagonal is just its scalar line, and each backward corner is zero, by reduction and Nakayama's lemma.

The four possible products of two strict corners all have coefficients divisible by $t$. Write their divided forms over $S=R_{e-1}$ as
$$
M:X\times Y\longrightarrow Z,\quad
A:Y\times L\longrightarrow Y',\quad
B:Z\times L\longrightarrow Z',\quad
N:X\times Y'\longrightarrow Z'.
$$
Multiplication by $t$ identifies $S$ with $tR_e$ as an $R_e$-module, so the divided forms are unique once bases are chosen. Choose a generator $\ell$ of $L$. The open condition is that $A(-,\ell)$ and $B(-,\ell)$ are invertible modulo $t$, equivalent to invertibility over $S$. It is invariant under changes of bases. Change the two primed-space bases so these two divided maps are identities. The new bases can be lifted from $S$ to $R_e$, since any lift of an invertible matrix modulo a nilpotent ideal is invertible. The two products involving $L$ are now scalar multiplication times $t$.

The only potentially nonzero associator of strict corner elements is on $X,Y,L$. After normalization it gives
$$
t^2\big(M(x,y)-N(x,y)\big)=0.
$$
Thus $N\equiv M\pmod{t^{e-2}}$ in $S$, or equivalently
$$
N=M+t^{e-2} E
$$
for a unique $k$-coefficient array $E$. This equation ensures all associativity identities. For three strict corners the only increasing chain of four vertices is $0<1<2<3$. Identities involving diagonal elements follow by the prescribed scalar actions. Conversely every pair $M,E$ defines a lift by these formulas.

The relative Hochschild calculation explains why this family is obstructed. Relative to the separable diagonal $k^4$, normalized cochains use composable chains of strict corner inputs. The differential vanishes on degrees one and two, since it only uses strict products, and every output on a composable chain is again in a strict corner. The four displayed products give all of $\mathrm{HH}^2$, and the chain $X,Y,L$ gives $\mathrm{HH}^3=\operatorname{Hom}_k(X\otimes Y\otimes L,Z')$. In these coordinates the primary associativity obstruction is $B(M(x,y),\ell)-N(x,A(y,\ell))$. The same expression, evaluated after division by $t^2$, governs every order for this residue algebra. This uses the ordinary associator, so it works in characteristic two as well. [Gerstenhaber–Schack, relative Hochschild cohomology](https://www2.math.upenn.edu/~mgersten/papers/Barrfest.pdf) · [Cibils et al., Hochschild cohomology of zero-composition categories](https://arxiv.org/abs/1708.00203)

## 2. Exact unmarked transport and obstruction

The commutator ideal in a lift is precisely the sum $J$ of its strict corners. The diagonal quotient is commutative, and a strict corner element $x\in e_i A e_j$ equals $[e_i,x]$. Any isomorphism therefore induces an isomorphism on the diagonal quotient $R_e^4$. This permutes its primitive idempotents. Reducing modulo $t$, the six directed corner supports give a strict total order, so this permutation fixes the four vertices. If $f_i$ are the images of the idempotents in the target, then
$$
u=\sum_i f_i e_i\in1+J,\qquad f_i u=u e_i .
$$
The ideal $J$ is nilpotent, so conjugating by $u^{-1}$ aligns the idempotents. The conjugation unit in $1+J$ is unique because any element in $1+J$ commuting with all four $e_i$ is $1$.

For an idempotent-preserving transporter, the six strict corner maps, reduced modulo $t^{e-1}$, are $g_X,g_Y,\lambda,g_Z,g_{Y'},g_{Z'}$. The $L$ map is the scalar $\lambda\in S^\times$. Preservation of the two scalar products forces
$$
g_{Y'}=\lambda g_Y,\qquad g_{Z'}=\lambda g_Z.
$$
Consequently the equations for $M,N$ have the same triple of mode maps. Their difference gives the residual equation for $E$. In the bilinear convention, writing a tilde for reduction to $k$, the equations are
$$
g_ZM=M'(g_X,g_Y),
\qquad
\widetilde g_Z E=E'(\widetilde g_X,\widetilde g_Y).
$$
Conversely, any such triple over $S$ gives an isomorphism after choosing $\lambda=1$, setting the primed maps by the displayed equations, and lifting all corners to $R_e$. This proves both directions and supplies efficient witness conversion. There is also an exact count when $k$ is finite of order $q$. If $h$ triples over $S$ satisfy the two equations, the number of algebra isomorphisms is
$$
h\, |S^\times|\,q^{a^2+2b^2+2c^2+1}\, |R_e|^{a+2b+2c+1}.
$$
The factors count the scalar on $L$, the independent entry lifts in the six invertible corner maps, and the unique conjugating unit in $1+J$, respectively.

For an extension over $R_{e+1}$, choose bases lifting those of the given jet, after first choosing its reduction isomorphism. The divided products over $R_e$ then must satisfy their associator modulo $t^{e-1}$. The reduction of that equation is already determined by the given four divided maps over $S$. On those maps it is the equality $M=N$ over $S$, or $E=0$. No higher coefficient in the extension can change this equation. Conversely if $E=0$, lift $M$ and use the identical lift at the other corner, with the same scalar actions at every level. This gives a compatible extension to all orders. In particular $E\ne0$ is a genuine obstruction at order $t^e$.

## 3. Computing the normal form from an unmarked table

First reduce the input table to $k$ and form the span of commutators $J_0$. The quotient $k^4$ acts on $J_0$ on both sides because $J_0^2=0$. The right and left annihilator lines are the first and last vertex idempotent lines, respectively. A nonzero vector $v$ on such a line has $v^2=\alpha v$ with $\alpha\ne0$, so $v/\alpha$ is the idempotent. Remove these two vertices from the quotient and restrict the corner bimodule to the two remaining vertices. Their first and last lines follow by the same calculation. This finds all four idempotents using only linear algebra and field arithmetic.

Lift an orthogonal system through the preimage of $J_0$ in the raw algebra. That ideal is nilpotent since its square is contained in $t$ times the raw algebra. The correction
$$
v\longmapsto v+(1-2v)(v^2-v)
$$
squares the defect ideal of an approximate idempotent. It works in the subalgebra generated by $v$, where the factors commute. Repeat to obtain an idempotent and use its complementary corner to lift the next one. For each lifted strict corner, project the original basis vectors to the corner and select a subset giving a basis modulo $t$. Its lifts form a free basis by Nakayama's lemma. Dividing coefficients by $t$ and changing the primed-space bases yields the displayed normal form.

These computations take deterministic polynomial time in explicit coordinates. Over finite fields in binary representation and over $\mathbb Z/p^e\mathbb Z$ they take polynomial bit time in the table and coefficient-ring encoding. For fixed $e$, the same holds for truncated polynomial rings over $\mathbb Q$ with explicit coefficient lists. For rational coefficient growth, one can use the finite geometric series for each inverse of a unit modulo $t$ after the initial Gaussian eliminations over $\mathbb Q$. Products and divisions over the truncated ring have polynomial coefficient bit length in the input size when $e$ is fixed. This last assertion is sufficient for all hardness results over $\mathbb Q$ here.

## 4. The entire fiber over a fixed predecessor

We record the explicit three-arm tensor used in the earlier MathProofs deformation argument. Take free spaces $U,V,W$ of respective ranks $u,v,w\ge 2$, their duals, and three scalar lines generated by $\ell_i$. On
$$
P=U\oplus k\ell_1\oplus W^*,\quad
Q=U^*\oplus V\oplus k\ell_2,\quad
K=k\ell_3\oplus V^*\oplus W
$$
put the base tensor
$$
T_0=\sum_i u_i\otimes u_i^*\otimes\ell_3+
    \sum_j \ell_1\otimes v_j\otimes v_j^*+
    \sum_l w_l^*\otimes\ell_2\otimes w_l.
$$
Use the same identity coefficients over every truncated coefficient ring. Label the summands $1,2,3$ in the displayed order. The three terms occupy cells $(1,1,1),(2,2,2),(3,3,3)$. Its stabilizer over any commutative local coefficient ring is
$$
H=\mathrm{GL}(U)\times\mathrm{GL}(V)\times\mathrm{GL}(W)\times\mathbb G_m^3.
$$
Indeed the intrinsic single-mode centroid is the three scalar projection operators, one per term. An off-diagonal centroid block would produce a cell with two equal labels and one different label in a single mode, where the action in another mode is zero. Contracting the paired identity shows that block vanishes. In each diagonal cell the common centroid action is scalar, given by the action on its scalar line. An isomorphism permutes the primitive projection idempotents. The rank-one summand is in a different mode in each arm, so all three projections are fixed. On the paired spaces the maps are dual inverses up to the reciprocal of the scalar-line map. Thus there are exactly the three independent general linear factors and the three independent units. In particular $H(k)$ acts on the payload cell $U\otimes V\otimes W$ by the three independent ordinary mode maps. This description also shows that stabilizer elements lift along all the truncated coefficient rings considered here. [Earlier fixed-residue construction](https://github.com/Dugongue/MathProofs)

Choose the residue corner format with $X=P^*,Y=Q^*,Z=K$. The fixed predecessor over $R_{e-1}$ has both divided data products equal to $T_0$ and both scalar actions equal to the identity. A lift of it over $R_e$, after choosing an identification with its predecessor and recovering the normalized bases, has
$$
M=T_0+t^{e-2}F,\qquad N=M+t^{e-2}E,\qquad F,E\in\mathcal V=P\otimes Q\otimes K.
$$
Every such pair occurs. Let $D\subseteq\mathcal V$ be the image of the derivative of the ordinary three-mode group action at $T_0$. It is computed by applying single-mode endomorphism basis elements to $T_0$ and taking their span. It is $H(k)$-stable because $H$ fixes $T_0$.

Any normal-form transporter reduces modulo $t^{e-2}$ to a stabilizer element of $T_0$ over $R_{e-2}$. Lift it to an exact stabilizer element over $S=R_{e-1}$. The remaining factor is $1+t^{e-2}A$ in the three modes, with $A$ a tuple of $k$-endomorphisms. In $S$, $(t^{e-2})^2=0$, so the change of $F$ is exactly the derivative direction $dA$, and the change of $E$ by this remaining factor is zero. Conversely an arbitrary such tuple $A$ gives that change of $F$ and does not change $E$. Therefore unmarked isomorphism of lifts is exactly
$$
H(k)\text{-orbit equivalence on }(\mathcal V/D)\oplus\mathcal V,
\qquad
\text{with coordinates }([F],E).
$$
If two chosen representatives have the same orbit, a witness in $H(k)$ lifts by the explicit block formulas. Solve the remaining linear system for $A$, then use Section 2 to lift the strict corner maps and return an algebra isomorphism.

The fixed predecessor admits lifts at every order. Nevertheless, in the whole fiber just described, precisely the orbits with $E\ne0$ are obstructed at the next step. The derivative directions and obstruction directions are different coordinates of the exact slice, rather than separate assumptions about a proposed isomorphism.

### Aligning the predecessor from the raw table

The promise supplies the predecessor format, and the algorithm requires no identification with it. After Section 3, reduce $M$ to $\overline M$ over $k$. Its centroid is $k^3$ because $\overline M$ is isomorphic to $T_0$. Compute this centroid by its linear equations on triples of endomorphisms. One can recover its three primitive idempotents deterministically over the coefficient field as follows. View each mode as a module over the computed centroid algebra $C$. Pick a nonzero vector in the current module quotient, compute its annihilator ideal $I$ in $C$, and obtain the identity of $I$ by solving $p z=z$ on a basis of $I$, with $p\in I$. The cyclic span has support idempotent $1-p$. Remove the cyclic span and repeat in the module quotient. The rank at any simple factor of $C=k^3$ is the number of supports in which it occurs. Multiplying each existing orthogonal support part by $1-p$ and $p$ refines the partition at each iteration. At most three nonzero parts and at most the mode rank many iterations occur. This computes the rank-one support idempotent in that mode. The three modes have different rank-one arms, so this recovers all three projections without field factorization. Choose bases using their images. Each arm is a nondegenerate two-mode pairing tensored with a scalar line, so ordinary linear algebra constructs a transporter from $\overline M$ to $T_0$.

Lift this witness successively from $R_j$ to $R_{j+1}$ for $1\le j<e-2$. After an arbitrary lift of the current matrices, the defect of the equation is in degree $t^j$. The correction $1+t^jA$ changes this defect by $t^j dA$, with $d$ the derivative computed over $k$, so a Gaussian elimination step suffices. Existence of the next correction follows from the promise that $M\bmod t^{e-2}$ is isomorphic to $T_0$. Compare the current partial witness with the reduction of any full witness. Their ratio stabilizes $T_0$ and lifts because of the block description of $H$. Consequently every correct partial witness admits a full extension. Finally take any invertible lift of the resulting predecessor witness to $R_{e-1}$, and act with it on $M,N$. The coefficients of $t^{e-2}$ give $F$ and $E$. The algorithm is independent of the alignment choices up to the exact orbit relation already proved.

When $k$ has $q$ elements, the formula is also compatible with exact counting. Each field witness $h\in H(k)$ for $([F],E)$ has $q^{(e-3)\dim H}$ lifts to $H(R_{e-2})$. For each such lift the remaining transporter has $q^{\dim H}$ choices in its top-order linear system. This is because the solution affine space is a translate of the kernel of the derivative, which is the Lie algebra of $H$ and has dimension $u^2+v^2+w^2+3$. Thus each slice witness contributes exactly $q^{(e-2)\dim H}$ triples over $S$ in Section 2. On the embedded payload family, each input-tensor transporter contributes $(q-1)^3$ slice witnesses, from the three line units. The hardness reduction therefore transfers exact transporter counting with a known multiplicative factor as well.



## 5. Complexity of the obstructed comparison

For hardness, take $F=0$ and put any nonzero input tensor in the payload cell of $E$. This is a complete orbit embedding by the description of $H(k)$ on that cell. The extra unit factors act trivially there. Recovering the three input mode maps from an algebra witness uses Section 2, reduction to $k$, and the three intrinsic blocks of $T_0$. The sum of the six strict corner ranks, plus four diagonal coordinates, is linear in the three input side lengths. Input tensors of rank-zero support can be tested directly and sent if needed to fixed yes or no pairs of nonzero payloads of one common format. Padding field tensor sides to rank at least two preserves TI: restrictions to the contraction supports are forced, and these restricted witnesses extend in each original side.

For the upper reduction on the entire promised fiber with $E\ne0$, there is a linear-dimension exact encoding of the tangent quotient. Decompose the ambient tensor module into its 27 cells by the three arm labels. Each cell is $H(k)$-stable. The derivative fills each equal-label cell, since a change on a paired factor of the identity arm spans that cell. A two-equal cell comes from a unique derivative block. If the changed source leg was a paired leg, its identity pairing shows again that the derivative fills the cell. If the changed source leg was the scalar line $L_j$ of arm $j$, the derivative in that cell is exactly $U_i\otimes k I_j$. Here $U_i$ is the new summand in the changed mode, and $I_j$ is the identity pair tensor in the other modes. A cell with three distinct labels has no derivative directions. Thus the tangent-quotient data retain the six all-distinct cells exactly and the six scalar-leg cells modulo $U_i\otimes k I_j$.

Encode these data by a fixed typed tensor system over $k$. Its named spaces initially are the nine mode summands of $T_0$. The three original arm tensors impose their common $H(k)$-action. Record every cell of $E$ and the six all-distinct cells of $F$ as ordinary typed tensors on these spaces. For a scalar-leg cell introduce a separate $\widehat U_i=U_i\oplus k\widehat \ell$, together with the fixed inclusion $U_i\to\widehat U_i$ and fixed quotient $\widehat U_i\to L_j$ sending $\widehat\ell$ to the chosen generator of $L_j$. Record the tensor
$$
F_{\rm cell}+\widehat\ell\otimes I_j
$$
with its changed leg in $\widehat U_i$, placing the other legs in their original order. Equivariance of the inclusion and quotient forces a lift of the $U_i$ map to send $\widehat\ell$ to $\lambda_j\widehat\ell+z$ with arbitrary $z\in U_i$, where $\lambda_j$ is the map on the original scalar line. The other two legs send $I_j$ to $\lambda_j^{-1} I_j$, by the arm equation. Consequently preservation of this augmented tensor is exactly the equation modulo $U_i\otimes k I_j$. Conversely choose $z$ to realize any required such difference. The choices for the six different cells are independent.

The number of named spaces, inclusion and quotient maps, and three-tensors is fixed. Their total mode dimensions are linear in the source rank sum, even when an exceptional cell requires a fresh copy. The fixed-type field tensor compiler of the earlier MathProofs result sends them to one ordinary three-tensor instance over $k$, with only linear side-length growth. Its construction applies to the inclusion and quotient maps by treating a linear map as a mixed tensor of order two. This proves the upper direction on the full obstructed fiber. Together with the lower direction, both reductions have linear dimension growth in the respective rank parameters. [Futorny–Grochow–Sergeichuk, wildness for tensors](https://arxiv.org/abs/1810.09219) · [MathProofs linear-length fixed-type tensor compiler](https://github.com/Dugongue/MathProofs)



For the earlier open locus without a fixed predecessor, an upper reduction to ordinary TI over $S$ follows by encoding the pair $(M,N)$ as two labelled tensors on the same three spaces. The two tensors share their mode maps by construction, and their equations are exactly the transport equations above. The earlier ring compiler has linear side growth in the sum of the ranks for any fixed type.

## Status and provenance

AI-assisted informal proof. Idempotent lifting, relative Hochschild cohomology, and tensor-system encoding are established machinery. The new combination identifies both a complete unmarked orbit slice and the obstruction on the same four-vertex family, with a mixed-characteristic version and a TI-completeness result inside a single predecessor fiber. The three-arm identity tensor and triangular corner normalizations reuse earlier MathProofs work. Publication priority for the exact combined statement is unverified. [Grochow–Qiao–Stange–Sun, TI over commutative rings](https://arxiv.org/html/2611.00735v1) · [Huang–Lu–Ye–Zhang, Centers of multilinear forms](https://arxiv.org/abs/2110.07915) · [Gerstenhaber, On the deformation of rings and algebras III](https://annals.math.princeton.edu/1968/88-1/p01)
