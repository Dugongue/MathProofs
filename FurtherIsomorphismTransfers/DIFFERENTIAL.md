# Tensor isomorphism in bounded-degree symplectic dynamics

## Theorems

Over every field $k$, ordered 3-tensor isomorphism is polynomial-time many-one equivalent to each of the following conjugacy problems on the explicit family defined below.

1. Conjugacy of quadratic polynomial automorphisms by arbitrary polynomial automorphisms.
2. Conjugacy of the same maps by polynomial symplectic automorphisms.
3. Conjugacy of the same maps by linear symplectic automorphisms.

The output maps themselves preserve the standard symplectic form, have unipotent linear part with Jordan block lengths only $2,3,4$, and have degree at most two for every positive and negative iterate. The phase space has dimension at most $8(\dim X+\dim Y+\dim Z)$ for a tensor represented as $T:X\times Y\to Z$. In characteristic $p>0$, the maps have order dividing the least power of $p$ that is at least eight. In characteristic zero, they are time-one maps of polynomial additive group actions that are Hamiltonian and remain quadratic for all time parameters. The corresponding polynomial Hamiltonian vector fields also give a TI-complete ordinary conjugacy problem.

All polynomial equalities in this statement are identities of polynomials, including over finite fields. The complexity claim is for standard explicit field arithmetic as in the tensor-isomorphism input model. The argument is informal.

## Construction

Regard each tensor as a bilinear map $T:X\times Y\to Z$. First pass to the concise tensor by quotienting each input by the kernel of contraction against the other input, and restricting the output to the linear span of all values. These are intrinsic spaces and are computed by elimination. A transporter induces a transporter of the cores. Conversely, for equal original formats, a core transporter can be extended by arbitrarily chosen invertible maps on the two kernels and on an output complement. In this paragraph $X,Y,Z$ now denote the core spaces. The nonzero inputs below are concise. Test equality of core formats before the reduction and handle zero tensors directly. Fixed yes and no pairs in the output family are available. For fixed no, use two $2\times2\times2$ matrix pencils $\langle I_2,\operatorname{diag}(1,0)\rangle$ and $\langle I_2,\left(\begin{smallmatrix}0&1\\0&0\end{smallmatrix}\right)\rangle$, whose projective determinant quadrics have two versus one distinct roots over an algebraic closure. Both tensors are concise.

Put $V=X^{\oplus 2}\oplus Y^{\oplus 3}\oplus Z^{\oplus 4}$. Number the layers in a chain from bottom $0$ to top $r-1$ for a chain of length $r$. Let $J$ be the shift lowering every chain one layer and killing its bottom layer, and put $D=I+J$. Define $Q_T:V\to V$ to have only one possibly nonzero component, $T(x_0,y_0)$ in the top $Z$-layer. Let $S_T=\operatorname{id}+Q_T$ and $f_T=D\circ S_T$. The maps $S_T$ and $S_T^{-1}$ fix the $X$ and $Y$ variables. They differ from the identity by $Q_T$ and $-Q_T$, respectively.

For a polynomial automorphism $f$, its cotangent lift is

$$
 f^\flat(v,p)=\bigl(f(v),(df_v)^{-{\rm T}}p\bigr),\qquad p\in V^* .
$$

The chain rule gives functoriality. The lift preserves the tautological one-form $p^{\rm T}dv$ by substitution, hence preserves the canonical symplectic two-form. This argument works in every characteristic. Here $dQ_T$ is zero except for maps from $X,Y$ to $Z$, so its square is zero and the lift of $S_T$ has the form $\operatorname{id}+R_T$, with

$$
 R_T(v,p)=\bigl(Q_T(v),-(dQ_T)_v^{\rm T}p\bigr).
$$

The output is $F_T=f_T^\flat=L\circ(\operatorname{id}+R_T)$, where $L=\operatorname{diag}(D,D^{-{\rm T}})$. This is an explicit polynomial automorphism of degree at most two on $V\oplus V^*$. Both this map and its inverse have quadratic coefficients obtained directly from $T$. The promised family uses this coordinate presentation. Its tensor coefficients can be read from the primal output at the top $Z$-layer, so the reverse reduction on this family is immediate once the equivalence is proved.

A tensor transporter $(A,B,C)$ with $CT(x,y)=T'(Ax,By)$ acts on $V$ by repeating $A,B,C$ across the layers of their respective chains. The resulting map commutes with $D$ and conjugates $S_T$ to $S_{T'}$. Its cotangent lift is a linear symplectic conjugator from $F_T$ to $F_{T'}$.

## Fixed-point translations and the derivative

It remains to show that an arbitrary polynomial conjugator gives a tensor transporter. Order the dual chain layers in reverse of their primal order. Set $N=L-I$. On both primal and dual chains $N$ strictly lowers the layers. Its component from each layer to the next lower one is the identity in primal chains and minus the identity in dual chains. The dual shift may also lower several layers at once. In particular $N^4=0$, and each whole chain is a direct sum of Jordan blocks of its displayed length.

The quadratic part $R_T$ uses only bottom coordinates in the chain groups $X,Y,Z^*$, and has outputs only in top layers of the disjoint groups $Z,X^*,Y^*$. The only nonlinear terms are the three pairings of those input chain groups, with output in the third length group. More explicitly the primal term has input $X_0,Y_0$ and output top $Z$. The dual term with $X_0$ and bottom $Z^*$ outputs into top $Y^*$. The term with $Y_0$ and bottom $Z^*$ outputs into top $X^*$. In particular every derivative coupling from an input chain of length $r$ to an output chain of length $s$ has $r+s>4$. This disjointness also implies
$$
(dR_b)N^j L(dR_b)=0\quad\text{for every }j\ge0
$$
at every point $b$, since the intermediate image remains in output chain groups.

Suppose $\Phi F_T=F_{T'}\Phi$. Put $b=\Phi(0)$. The fixed-point equation gives $Nb+LR_{T'}(b)=0$. Since $N$ always has zero top coordinates and $L$ preserves all top coordinates, while $R_{T'}(b)$ lies in pure top layers, we get $Nb=R_{T'}(b)=0$. Write $\delta=d(R_{T'})_b$. Differentiating the conjugacy shows that $L+L\delta$ is similar over $k$ to $L$.

We claim $\delta=0$. If a nonzero component couples an input chain of length $r$ to an output chain of length $s$, choose a pure top input $u$ so that this component of $\delta N^{r-1}u$ is nonzero. Such an input exists because the adjacent lowering maps are invertible. Expand $(N+L\delta)^4u$. Terms with two or more factors $L\delta$ vanish by disjointness. The term $N^4u$ vanishes. The remaining term with $r-1$ factors $N$ on the right of $L\delta$ has a nonzero component at output layer $s-1-(4-r)$, which exists since $r+s>4$. Every term with fewer right factors has more left factors and reaches only lower layers of this output chain. More right factors give zero. Hence $(N+L\delta)^4u\ne0$, contradicting similarity. This proves the claim, without division or eigenvalue assumptions on the field.

For any homogeneous quadratic map $R$, expansion at $b$ gives $R(v+b)=R(v)+R(b)+dR_b(v)$ in every characteristic. Thus $R_{T'}(v+b)=R_{T'}(v)$, and translation by $b$ commutes with $F_{T'}$. We may compose $\Phi$ with the reverse translation and assume $\Phi(0)=0$.

## The quadratic coefficient recovers the tensor

Let $\ell=d\Phi_0$, which is invertible. Write $P$ for the homogeneous quadratic term of $\Phi$. Compare the linear and quadratic terms of conjugacy:
$$
 \ell L=L\ell,\qquad
 \ell L R_T(v)+P(Lv)=L P(v)+L R_{T'}(\ell v).
$$
On $K=\ker N$, the correction $LP(v)-P(Lv)$ is $NP(v)$. It disappears in the quotient $E/NE$ of the full phase space $E=V\oplus V^*$. Since $L$ acts trivially on $E/NE$ and $\ell$ commutes with $N$, this gives equality of the quadratic maps $\bar\ell\,\overline{R_T(v)}$ and $\overline{R_{T'}(\ell v)}$ on $K$, modulo $NE$. Polarize this equality by evaluating at the sum of a pure primal $X_0$ vector $x$ and a pure primal $Y_0$ vector $y$, then subtracting the two separate evaluations.

The intrinsic descending filtration $K\cap N^{i-1}E$ on $K$ consists of the bottoms of chains of length at least $i$. It is preserved by $\ell$. In particular the image of $y$ has no length-two bottom component, while the $X_0$ component of $\ell x$ and the $Y_0$ component of $\ell y$ are linear maps $A x$ and $B y$. On $E/NE$, the images of $\ker N^i$ give the increasing filtration by tops of chains of length at most $i$. The induced map on its last quotient, the doubled length-four top space, is invertible. Call it $C_4$.

Project the polarized equality to this last quotient. On the source the sole term is $T(x,y)$ in the primal $Z$-top. On the target only the first pair of chain groups can contribute to length four. The other two nonlinear terms go to length two or three. Thus
$$
 C_4(T(x,y),0)=(T'(Ax,By),0).
$$
By concision, the tensor values span primal $Z$. This equality therefore makes $C_4$ preserve that summand and restricts it to an invertible $C:Z\to Z'$. If $Ax=0$, the equality and $C$'s injectivity show that $T(x,y)=0$ for every $y$, so $x=0$ by concision. Likewise $By=0$ implies $y=0$. Since corresponding dimensions agree, $A,B$ are invertible. The equality is precisely the tensor transporter equation. There was no symplecticity or degree bound assumed for $\Phi$. The same coefficient argument treats formal power series conjugacies at the origin, since only the first two coefficients were used after fixing the origin.

## Degree, bounded order and Hamiltonian flows

The base maps are of block form
$$
 (x,y,z)\longmapsto (U_Xx,U_Yy,U_Zz+\beta(x,y))
$$
with invertible $U_X,U_Y,U_Z$ and bilinear $\beta$ on the full chain groups. This class is closed under composition and inverse. Its cotangent lift is still quadratic: the derivative has a block diagonal invertible part and one off-diagonal row from $X,Y$ to $Z$. Its inverse transpose is linear in the base coordinates by the square-zero block formula, so multiplication by $p$ has degree at most two. Functoriality now proves the iterate bound.

One can also linearize the base action after adjoining the feature $x\otimes y$, using the invariant graph of that bilinear map. For $f_T$ the feature evolves by $D_X\otimes D_Y$, where $D_X-I$ has square zero and $D_Y-I$ has cube zero. The tensor product differs from the identity by a nilpotent of index at most four, by expanding the commuting shifts. The $Z$-block has index at most four and receives a linear term from the feature block. Thus the whole augmented matrix is $I+M$ with $M^8=0$. In characteristic $p$, its $p^a$-th power is $I+M^{p^a}$, which is the identity once $p^a\ge8$. The same bound holds for the cotangent lifts. In characteristic two the order is exactly eight for every nonzero tensor in the construction. To see this, choose an augmented feature supported on X-bottom times the second Y layer whose tensor value is nonzero, arising from a pure base point with those nonzero coordinates. One application of the feature shift minus the identity brings that feature to X-bottom times Y-bottom, and the second application kills it. In the fourth power of M the term crossing into the Z block then lowers the nonzero top output twice. It has a nonzero component at the second Z layer from the bottom, while the zero-shift feature never contributes. Thus the fourth iterate is not the identity.

In characteristic zero, form the polynomial family $\sum_{j=0}^7\binom tjM^j$ of augmented matrices. On all integer parameters it is the ordinary integer-power family. By polynomial identities it preserves the feature graph and acts by the additive group for all parameters. Descending to the original variables gives a polynomial flow on $V$ that remains in the same block form. The cotangent lift is a symplectic polynomial additive flow of degree at most two at all parameters. If its infinitesimal base vector field is $U(v)$, differentiation of the cotangent formula gives the Hamiltonian $p(U(v))$, of degree at most three. A polynomial conjugacy of time-one maps conjugates all integer-time maps and hence conjugates the full flow by polynomial identity in the time parameter. Conversely, conjugacy of the polynomial vector fields conjugates these flows: formal solutions at a given initial condition are unique in characteristic zero by recursive comparison of coefficients, and both flows are polynomial. Thus ordinary polynomial conjugacy of these Hamiltonian vector fields is also equivalent to the original tensor isomorphism.

## Provenance and limits

The construction combines linear conjugacy of quadratic vector fields, cotangent symplectic lifting, and intrinsic tensor support and quotient recovery. The previous survey's quadratic-dynamics entry explained the Markus correspondence and its relation to TI. The principal additional mechanism here is to preserve a bilinear tensor contraction against an arbitrary nonlinear conjugator by using three different Jordan lengths, and to carry that mechanism through a cotangent lift. The field-uniform proof covers characteristic two without a polarization denominator. It addresses ordinary 3TI and does not assert a reduction for unrestricted SL-TI.

Relevant precedents include Markus's analysis of quadratic vector fields through algebras, Moser and Koch–Lomelí on quadratic and affine-integrable symplectic dynamics, basic cotangent lift geometry, and Grochow–Qiao on tensor-isomorphism completeness. The bounded-order statement is in positive characteristic, and the Hamiltonian additive-flow statement uses characteristic zero. A targeted literature search did not establish priority for the stated algebraic conjugacy theorem.

[Markus](https://rainbow.ldeo.columbia.edu/~alexeyk/QDS/Markus1960.pdf) · [Moser on quadratic volume-preserving maps](https://amath.colorado.edu/pub/dynamics/papers/Moser.pdf) · [Koch–Lomelí](https://web.ma.utexas.edu/mp_arc/c/13/13-13.pdf) · [Cotangent geometry, Cannas da Silva](https://people.math.ethz.ch/~acannas/Papers/handbook.pdf) · [Grochow–Qiao](https://arxiv.org/abs/1907.00309)

Federated DAG probes reached 103 registered source catalogs. The most useful cross-field match was the OpenAI Nearby Lagrangian development's cotangentLift_liouville and cotangentLift_symplectic declarations. The Jordan-block and tensor-support searches supplied the adjacent structural interfaces. The retrieved Lean declarations were source evidence. The proof above verifies the algebraic identities directly and establishes no new kernel-checked Lean theorem. [Nearby Lagrangian cotangent lifts](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Geometry/NearbyLagrangian/CotangentLifts.lean)

Exact controls tested the scalar tensor in characteristics two and three. They checked the symplectic derivative and whether a nonzero derivative coupling increases the nilpotency index at every fixed point of the test instance. They also checked the augmented linear order bound on an entire basis. [Control program](check_dynamics.py)
