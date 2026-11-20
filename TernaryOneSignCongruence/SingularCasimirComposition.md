# A singular-anchor composition for the one-sign problem

Fix $F=\mathbb F_3$. For based alternating spaces $D_A\subseteq\bigwedge^2 V_A^*$ and $D_B\subseteq\bigwedge^2 V_B^*$, a congruence $Y:V_A\to V_B$ induces $f(M)=Y^{-\mathsf T}MY^{-1}$, with tested sign $\det(Y)\det(f)$. All determinants use the given input bases. In odd equal ambient dimensions any ordinary congruence can realize either sign by composition with $-I$, which fixes all forms, so assume the ambient dimensions are equal and even.

**Theorem.** Supply a paired nonzero projective anchor $F\Omega_A,F\Omega_B$ of the same rank and restrict to congruences matching these lines. The anchors may be singular. Set $K_X=\ker\Omega_X$, $\bar V_X=V_X/K_X$, and let $\bar D_X^0$ consist of the descended forms of $D_X$ whose radical contains $K_X$, for $X=A,B$. The form $\bar\Omega_X$ is nondegenerate. Assume the normalized code $\bar\Omega_X^{-1}\bar D_X^0$ has nondegenerate trace pairing. Choose an ordered polynomial-size family of covariant matrices on each code, such as its Casimir iterates. If the source common centralizer has semisimple simple ranks at most $O(\sqrt{\log L})$ over their center fields and $\dim K_A=O(\sqrt{\log L})$, where $L$ is dense input length, then the prescribed sign question on the branch reduces in deterministic polynomial time to one ordinary 3-TI instance. The conclusion also holds when the actual exterior grades pass the odd-multiplicity width test in the [commutative Casimir centralizer proof, Section 5](CyclicCasimir.md). Both the width conditions and all hypotheses can be checked for the branch. A polynomial list of compatible anchor branches can then be packed into a single comparison. In particular, the fixed-corank polynomial factor marks from [FactorWordAnchorBank](FactorWordAnchorBank.md) are eligible wherever they produce the requisite matched anchor and quotient code. Their own bound on a final label radical is unnecessary for this composition.

## Align only the nondegenerate quotient

The kernels are explicit subspaces and can be calculated by linear equations. The condition $K_X\subseteq\mathrm{rad}(M)$ on $M\in D_X$ is a linear condition. Every branch congruence takes $K_A$ to $K_B$, and it preserves the corresponding forms disappearing along those kernels. Hence its quotient map $\bar Y$ transports the two normalized codes by conjugation. More precisely, if the anchor multiplier is $\epsilon\in F^\times$ so that $f(\Omega_A)=\epsilon\Omega_B$, then
$$
\bar\Omega_B^{-1}\,\overline{f(M)}
  =\epsilon\,\bar Y(\bar\Omega_A^{-1}\bar M)\bar Y^{-1}.
$$
Multiplying a whole code by $\epsilon$ leaves its span unchanged. The Casimir basis-independence and conjugation laws used in [CyclicCasimir](CyclicCasimir.md) therefore force $\bar Y$ to intertwine the ordered covariants in either scalar branch.

Find an invertible simultaneous intertwiner $\bar Y_0$ for just these quotient covariants by constructive module isomorphism. If none exists, the branch is impossible. Extend $\bar Y_0$ to an invertible $Y_0:V_A\to V_B$ mapping $K_A$ to $K_B$ by selecting arbitrary adapted complements and an isomorphism of the kernel spaces. Pull back the target along $Y_0$ so the residual physical map is $c=Y_0^{-1}Y$. The possible residual maps now lie in the unit group of
$$
\mathcal T=\{c\in\operatorname{End}_F(V_A):cK_A\subseteq K_A,\ \bar c\in\mathcal A\},
$$
where $\mathcal A$ is the common full centralizer of the source quotient covariants. Relative to the complement coordinates $\mathcal T$ is a block triangular algebra. Its block on $K_A$ is $M_{\dim K_A}(F)$, its quotient block is $\mathcal A$, and all maps from the quotient into the kernel are allowed as shears. Its semisimple quotient is $M_{\dim K_A}(F)\times(\mathcal A/\operatorname{rad}\mathcal A)$, omitting the first factor if the kernel is zero. Indeed the shear ideal together with the quotient radical is nilpotent, and the displayed quotient is semisimple. Keep the original tensor equations and the actual projective-anchor mark in the final construction. Thus enlarging the ambient group to $\mathcal T^\times$ only provides a filtration for the determinant calculation. It does not discard shared conjugacy or anchor equations. [Brooksbank–Luks, constructive module isomorphism](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

## Read the whole sign on the natural annihilator

Let $E_X\subseteq\bigwedge^2 V_X$ be the annihilator of $D_X$ under the natural exterior pairing. Give $Q_X=\bigwedge^2 V_X^*/D_X$ an explicit quotient basis, and give $E_X$ its paired dual basis. Lifting the quotient basis after the supplied basis of $D_X$ gives one frame of $\bigwedge^2 V_X^*$. Write $\eta_X$ for the determinant of that frame in the exterior basis of the given ambient coordinates. If $g_Q$ is the quotient map induced there by the congruence, the exact-sequence formula is
$$
(\det Y)^{-(n-1)}
 = \det\bigwedge^2(Y^{-\mathsf T})
 =\frac{\eta_B}{\eta_A}\,\det f\,\det g_Q.
$$
Here $n=\dim_F V_X$. In the stated dual bases the induced map on $E_A\to E_B$ is $g_Q^{-\mathsf T}$. Since $n$ is even, $\det(Y)^{2-n}=1$ over $F$, and consequently
$$
\det(Y)\det(f)
 = \frac{\eta_A}{\eta_B}\,\det\bigl(\bigwedge^2Y|_{E_A}:E_A\longrightarrow E_B\bigr).
$$
This is a calibration in the supplied bases, and uses no ambient Pfaffian for the singular anchor.

Pull the target annihilator back by $\bigwedge^2Y_0^{-1}$, carrying along its chosen dual basis, so the residual action is the exterior square of the actual $c\in\mathcal T^\times$. Apply the explicit algebra composition flag and exterior-grade construction of [CyclicCasimir, Section 5](CyclicCasimir.md) to the natural $\mathcal T$-module $V_A$ rather than the contragredient module. No change is needed in that construction: it uses only the simple finite-field modules and their induced exterior action. Intersect the fixed exterior flag with the source and pulled-back target annihilators. On each grade use the linked scalar or small matrix norm test on the actual restriction. This reads the determinant on $E$ in the aligned coordinates, with the usual additional ratio of the adapted grade frames to the two given dual bases. Attach the original congruence and anchor marks and enforce the computed total multiplier. Include both scalar branches $\epsilon=1,-1$, unless the anchor vectors already have a prescribed match.

Every genuine witness satisfying the branch and its sign intertwines the quotient atoms. Its residual map preserves the exterior flag and extends to every linked norm mark, with the prescribed calibrated output. Conversely, a matching of the enlarged tensor system supplies an actual congruence in the original branch, and the attached line reads the annihilator determinant of that same congruence. The displayed calibration gives the requested sign. The largest field rank of a grade is at most the square of the largest simple rank of $\mathcal T$, so the exterior norm cost is polynomial under the stated logarithmic bound. The alternative odd-multiplicity criterion from [CyclicCasimir](CyclicCasimir.md) gives polynomial size by using a top exterior line only for the grade-subspace stabilizer factors whose determinants contribute. All other data are computed by polynomial linear and algebra operations. The number of marks is polynomial, the tensor-component arities at most three, and polynomially many branches combine using the fixed-signature and positive OR packing described in [FactorWordAnchorBank](FactorWordAnchorBank.md).

This is a written proof for the stated branch criterion. It allows a singular pencil with zero common radical because only the kernel of a selected, compatibly marked form is used. Classifying all raw inputs by polynomially many such branches remains open.
