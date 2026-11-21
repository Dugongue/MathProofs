# A same-field reduction for special-linear isomorphism of local Gorenstein multiplication tensors

Let $k$ be a field. Consider a pair of $N\times N\times N$ tensors, interpreted as bilinear maps from two based spaces to a third. Suppose the source is ordinarily isomorphic to the multiplication tensor of a finite-dimensional commutative unital split local algebra $A$ with one-dimensional socle. The target can be arbitrary. Here split local means that the residue field is $k$. The tensor problem imposes determinant one on each of the three independent legs.

**Theorem.** There is a deterministic same-field many-one reduction to ordinary three-tensor isomorphism in the following cases.

1. In characteristic two, for every such source algebra.
2. In arbitrary characteristic, if a square-zero power $I$ of the maximal ideal satisfies $\dim(\operatorname{Ann}(I)/I)\le d$, with construction size and time $\operatorname{poly}(N,2^d)$. In particular, $d=O(\log N)$ gives a polynomial reduction. The case $d=0$ includes the multiplication tensors of standard graded Artin Gorenstein algebras of odd socle degree.

The field-operation bound holds over every field of any fixed characteristic, including imperfect fields. The reduction has polynomial bit cost over the rationals and standard represented finite fields. No witness extension or root extraction is used by the output compiler.

## Normalize the independent input legs

Use $U_1,U_2,W$ for the three based spaces and write the law as $\beta:U_1\times U_2\to W$. Scan the fixed bases for an invertible slice $D=\beta(-,v_0)$ and an invertible slice $E=\beta(u_0,-)$. An ordinary translate of promised multiplication has both. Indeed the vectors whose multiplication maps are invertible are precisely the units. In a split local algebra the nonunits are a hyperplane, so any basis meets the units. Set
$$
m(x,y)=\beta(D^{-1}x,E^{-1}y),\qquad e=\beta(u_0,v_0).
$$
On a promised tensor, the two slices in original algebra coordinates are multiplication by units, so $m$ is isomorphic to the original algebra. Its unit is $e$. Reject if a scan fails, or if the normalized law fails the unital, associative, or commutative equations. This cannot reject an ordinarily isomorphic target.

Recover the residue homomorphism $\epsilon$ of each normalized law. When $N$ is invertible, it equals $\operatorname{tr}(L_x)/N$, since multiplication by $\epsilon(x)1$ plus a nilpotent gives the multiplication matrix. Over a represented finite field of characteristic $p$, take a power $p^a\ge N$. On the promised law, $x^{p^a}=\epsilon(x)^{p^a}e$ by nilpotence and Frobenius. Compute these powers on basis vectors and apply the inverse finite-field Frobenius to their scalar coefficients. The iteration needs only polynomially many operations in $N$ and $\log |k|$. In all cases verify that $\epsilon$ is a unital homomorphism and its kernel $\mathfrak m$ is nilpotent by testing $\mathfrak m^N=0$. Compute the socle as $\operatorname{Ann}(\mathfrak m)$ and require dimension one. These tests prove the promised properties of a surviving target. If relying on supplied augmentations, the same tests validate them. No claim of arbitrary-field root extraction is needed for this step.

Write the normalized algebras as $A,B$. Define two computable scalars
$$
d_1=\det(D_B)/\det(D_A),\qquad d_2=\det(E_B)/\det(E_A).
$$
A raw witness in argument convention is $\beta_B(Px,Qy)=H\beta_A(x,y)$, and the corresponding literal tensor legs have determinants $\det(P)^{-1},\det(Q)^{-1},\det H$. Passing to the normalized laws makes the input maps $P'=D_BP D_A^{-1}$ and $Q'=E_BQ E_A^{-1}$. Consequently the required determinants of $(P',Q',H)$ are $(d_1,d_2,1)$.

Every isotope of the normalized unital commutative laws has
$$
(P',Q',H)=(L_u\phi,L_v\phi,L_{uv}\phi)
$$
for a unital algebra isomorphism $\phi:A\to B$ and units $u,v$ in $B$. To see this, evaluate the isotope equation at the two units. The multiplication maps by $P'(1)$ and $Q'(1)$ are invertible, and division by these units gives the common isomorphism. Conversely such a triple always works. Since $\det L_u=\epsilon(u)^N$, the equations on the three independent determinants are exactly
$$
\det\phi=d_1d_2,\qquad (\epsilon(u))^N=d_2^{-1},\qquad (\epsilon(v))^N=d_1^{-1}.
\tag{1}
$$
When the last two equations have solutions, the units can be chosen to be their scalar solutions times the unit element. Thus all three conditions are sufficient.

## Recover the orientation from Frobenius duality

In each algebra choose a nonzero socle vector $s$ and a linear functional $\lambda$ with $\lambda(s)=1$. The pairing $h(x,y)=\lambda(xy)$ is perfect. Indeed every nonzero ideal meets the socle: multiply a nonzero element by successive powers of the maximal ideal and take the last nonzero product. A nonzero principal ideal therefore contains a nonzero socle vector, on which $\lambda$ is nonzero. Let $G_A,G_B$ be the pairing matrices in the fixed normalized output bases.

For an algebra witness $\phi$, put $\phi(s_A)=\alpha s_B$. Nondegeneracy gives a unique $w\in A$ with $\lambda_B\phi(x)=\lambda_A(wx)$. Evaluating on $s_A$ gives $\epsilon(w)=\alpha$, so $w$ is a unit. Pairing transport now gives
$$
\det(\phi)^2\det G_B=\det G_A\,\alpha^N.
\tag{2}
$$
In characteristic two the squaring map on a field is injective. Consequently the first equation of (1) is equivalent to the scalar equation
$$
\alpha^N=(d_1d_2)^2\,\det G_B/\det G_A .
\tag{3}
$$
This removes the full determinant test, including when $N$ is even.

For the second part choose the same maximal-ideal power on both inputs. The algorithm can pick the first square-zero power of maximal dimension from the source and verify that the target power is square zero and has matching dimension. An isomorphism carries it to the same power. Put $J=\operatorname{Ann} I$, $r=\dim I$, and $M=J/I$. Orthogonality of $I$ for $h$ is exactly $J$: if $x$ pairs to zero with $I$, then for each $i\in I$, $xi$ pairs to zero with every element because $I$ is an ideal. Perfectness gives $xi=0$. Thus $I\times A/J\to k$ is perfect. Choose a basis of $I$, lifts of an arbitrary basis of $M$, and lifts of the dual basis in $A/J$. Let $\omega_A$ be the determinant of this concatenation in the original output coordinates. Define $\omega_B$ the same way. Then
$$
\det\phi=(\omega_B/\omega_A)\,\alpha^r\,\det(\phi_M),
\tag{4}
$$
where $\phi_M$ is in the chosen middle bases. In fact the matrices on $I$ and $A/J$ have determinant product $\alpha^r$, since the transformed pairing is twisted by multiplication by $w$. Multiplication by $w$ on $A/J$ has determinant $\alpha^r$: its difference from $\alpha I$ is nilpotent. Finally multiply by the determinant on the middle and convert the two basis determinants. This proves (4) without a graded presentation or a choice of a square root. In a standard graded Artin Gorenstein algebra of odd socle degree $2b+1$, the ideal of degrees at least $b+1$ is $\mathfrak m^{b+1}$, is square zero, and has half the dimension by perfect complementary pairings. Hence that case has $M=0$.

## Compile the scalar and small exterior conditions into TI

Use simultaneous isomorphism of a list of based spaces with linear and bilinear maps. Each bilinear map is a tensor with an output factor and two dual input factors. Each linear map is such a block with one extra fixed-scalar factor. Put every datum in its own three explicitly partitioned blocks. Link copies of each space by equality and link a dual copy by inverse transpose. To fix the extra scalar, add a scalar block with coefficient one and three line actions linked as $(a,a,a^{-1})$, so its equation is $a=1$ over every field. This is a linked-partitioned tensor instance. Grochow–Qiao IV, Theorem 5.3, removes the links with polynomial overhead. Use the duplicate-tag partition removal proved in [Gadgets.md](Gadgets.md) for the resulting partitions. The distinct private ranks and exact divisor of maximal minors give polynomial overhead even when the number of parts grows. The blocks have explicitly prescribed dimensions and the comparison uses the same base field throughout. [Grochow–Qiao IV, linked partitions and partition removal](https://arxiv.org/html/2306.16317#S5)

Include the multiplication as a bilinear datum on one space $A$ or $B$. Use a linear datum from a multiplier line to the algebra with image generator $s_A$ or $s_B$. This forces the multiplier-line action to equal $\alpha$. For the middle-space variant include linear data for the inclusion $J\hookrightarrow A$ and the quotient $J\to M$. These force the action on $M$ to be the induced $\phi_M$. Add $\bigwedge^i M$ for $1\le i\le \dim M$ and the maps $M\times\bigwedge^i M\to\bigwedge^{i+1}M$. The products span their output, so their actions are forced to be the exterior powers of $\phi_M$, including the determinant on the one-dimensional top exterior power. When $M=0$ use the trivial fixed-scalar line. Exterior structure constants are signed zeros and ones, and all these spaces total at most $2^d$ dimensions.

A scalar line with action $x$ can be raised to the $s$th power using a chain of scalar multiplications with coefficient one, each forcing the output action to be the product of the input actions. A final linear map from its output line to the fixed line, with source coefficient $c$ and target coefficient one, forces that action to be $c$. This uses $O(s)$ data, or $O(\log s)$ with repeated squaring. Use two free scalar lines for the two unit-root equations in (1). For orientation impose (3) in characteristic two. In the middle-space variant impose
$$
\alpha^r\det(\phi_M)=d_1d_2\,\omega_A/\omega_B .
$$
These equations are necessary by (1)–(4). All induced actions extend a valid witness to the data, and conversely the linked tensor equations enforce them and thereby give an exact raw determinant-one witness.

All scans, coordinate constructions and coefficient calculations are polynomial exact linear algebra in the explicit input. The output has size polynomial in $N$ and $2^d$, with $d$ absent from the characteristic-two construction. Over the rationals the normalization uses a constant number of inverse matrices before the residue and socle calculations. Powers of the radical can be computed as spans of products of length at most $N$ in the original fixed generators, retaining independent original product vectors. Their heights grow polynomially in the input length. All remaining determinant and basis computations and the rational output data have polynomial bit size. The finite-field version uses polynomial bit-time field operations and inverse Frobenius in the usual polynomial-basis representation.

## Remove inverse Frobenius over imperfect fields

The direct residue extraction above is sufficient over finite fields. For an arbitrary field of positive characteristic $p$ in which $N$ vanishes, choose $P=p^a\ge N$. In the fixed basis compute the scalar $s_i$ from the equality $e_i^P=s_i e$ in the original law and reject if an equality fails. Form a second law by raising all structure coefficients and unit coordinates to the $P$th power. Its augmentation on this fixed basis is the row of $s_i$: on a split original law $s_i=\epsilon(e_i)^P$, and all the residue equations are preserved by Frobenius. Validate this augmentation and the socle for the twisted law as above. All radical powers, annihilators and their dimensions on a split law agree after twisting and extending scalars, since twist commutes with multiplication and with ranks of coefficient matrices.

Include the original law in the linked-partition instance, with transporter $\phi$. To link its basis to the twisted basis, repeat the following construction $a$ times. For a space $V$, form its symmetric powers up to degree $p$ using bilinear maps $V\times\operatorname{Sym}^i V\to\operatorname{Sym}^{i+1}V$. Every output is spanned by products, so simultaneous isomorphisms act by the induced symmetric powers. Include the linear inclusion of a new based copy of dimension $\dim V$ into $\operatorname{Sym}^p V$, mapping its basis to the pure powers $e_i^p$. The new action is forced to be the entrywise $p$th power of the original matrix, since $(\sum_i a_i e_i)^p=\sum_i a_i^p e_i^p$. Conversely the forced actions extend every $\phi$. After the $a$ links the transporter of the twisted law is exactly $\phi^{[P]}$. One can include the twisted law as a bilinear datum, with that action.

Use the socles, flags and determinant formulas of the twisted laws to impose $\det(\phi^{[P]})=(d_1d_2)^P$. Injectivity of Frobenius on $k$ gives the original determinant constraint. The two unit-root equations in (1) are still imposed over $k$ on their original coefficients. No root of a residue coefficient is computed. A positive output contains an original algebra witness, so its target is split and the derivation of (1) applies. Thus a target with nonsplit original law cannot introduce a false positive even if its twist is split. The extra symmetric-power dimensions are polynomial in $N$ for each fixed $p$, and for $p=2$ the only additional power is $\operatorname{Sym}^2 V$. Over represented finite fields the direct method avoids any dimension factor exponential in $p$.

This extends the use of Frobenius dual blocks from the recent short multiplication algebras. The theorem treats literal special-linear witnesses on the multiplication tensors themselves, including arbitrary independent changes of their input and output bases. The characteristic-two argument needs no small middle space. The unrestricted reduction for three arbitrary tensor legs remains open. [Jelisiejew, Classifying local Artinian Gorenstein algebras](https://doi.org/10.1007/s13348-016-0183-1)

[Frobenius.py](Frobenius.py) tests the two determinant formulas and the three-coordinate determinant criterion on 16 truncated local algebras, including 974 automorphism substitutions and 120 determinant targets. Lean independently verified the [three determinant equations](IsotopeDeterminants.lean) with `propext` and `Quot.sound`. The algebra and reduction theorems are written proofs.
