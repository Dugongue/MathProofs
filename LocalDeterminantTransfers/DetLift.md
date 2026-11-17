# The determinant-constrained local lifting equation

Let $R$ be a finite commutative local ring as in the [ordinary lifting proof](https://github.com/Dugongue/MathProofs/blob/main/NovemberGroupIsoTransfers/LocalLifting.md), with computable residue coordinates and ideal layers. Given two free three-tensors and a prescribed unit determinant in each mode, the complete transporter coset under that prescription can be computed in $q^{O(n_1+n_2+n_3)}\operatorname{poly}(L)$ bit time, conditional on Qiao–Zhang's transporter theorems. Here a nonempty coset is represented by a prescribed-determinant transporter and generators of the determinant-one stabilizer. This note checks how to impose the determinant throughout the induction.

For positive ranks, multiplying the target by the inverse of a tuple of diagonal matrices of the prescribed determinants reduces the comparison to determinant one. Rank-zero modes are handled directly. At the residue level supply $\prod_i\operatorname{SL}_{n_i}(k)$ to [Qiao–Zhang, Theorem 8.1](https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1723.pdf). Its generators are elementary transvections with coefficients in a prime-field basis of $k$. For dimension one the group is trivial. The output provides the exact starting coset.

At level $a$ let $H_a$ be the determinant-one stabilizer, $K_a$ its residue kernel, and $J_a$ its residue image. Put $I=\mathfrak m^a/\mathfrak m^{a+1}$, $B=\bigotimes_i k^{n_i}$, and let $D$ be the ordinary tangent tensor map. A lift of any mode map can be corrected to determinant one without changing its reduction, using a diagonal matrix supported in one coordinate with determinant the inverse of the discrepancy. Consequently the determinant-one reduction kernels are exactly the tuples $1+X$ with $\operatorname{tr}X_i=0$ for all $i$. The displacement quotient is
$$
W_\mathrm{SL}=(I\otimes_k B)/D\bigl(\textstyle\bigoplus_i\ker\operatorname{tr}\bigr).
$$
With determinant-one lifts, the proof for ordinary cosets works in this quotient, including the residue cocycle, quotient by translations of $K_a$, and graph algorithm for its next kernel. The tangent subspace is invariant because each mode trace is unchanged by conjugation. Thus the effective group input to Theorem 8.10 is the same degree-three quotient of the original residue representations. The initial residue restriction is essential.

Equivalently one can use unrestricted matrix lifts and work with the following joint quotient:
$$
\frac{(I\otimes_k B)\oplus I^3}
{\{(D(X),(\operatorname{tr}X_i)_i):X_i\in\operatorname{Mat}_{n_i}(I)\}} .
$$
The class of a lift $h$ uses both $\widetilde hT-T$ and $(\det(\widetilde h_i)-1)_i$. The determinant entries add because $I^2=0$; the group acts trivially on $I^3$, so the same cocycle identity holds. The trace map onto $I^3$ is surjective. Clearing the three trace components identifies the joint quotient canonically with $W_\mathrm{SL}$. Its trivial summands have degree zero in Definition 25. This formulation is useful for an exact target discrepancy using an arbitrary lifted witness.

The two correction requirements must be solved together. Over the dual numbers, with all three mode ranks one, take source $1$, target $1+\epsilon$, and zero required principal determinant discrepancy. The tensor tangent $D(x)=x_1+x_2+x_3$ is surjective, and the individual trace maps are surjective. Their joint image is the graph of the sum, so no permitted lift exists. This checks why quotienting the tensor and determinant coordinates independently gives a wrong answer.

## An unconditional ordinary-TI test for the trace-zero tangent quotient

Take any field $k$ of effective arithmetic and a split square-zero algebra $R=k\oplus I$. Input two base tensors $T_0,T'_0$ and two perturbations $U,U'$ with entries in the tensor layer $I\otimes_k B$. The following affine comparison reduces to a single ordinary 3TI query over $k$, without a supplied residue stabilizer:
$$
  gT_0=T'_0,\qquad
  U'-gU\in D_{T'_0}\bigl(\textstyle\bigoplus_i\ker\operatorname{tr}\bigr),
  \qquad g\in\prod_i\operatorname{GL}_{n_i}(k).
$$
Here $D_{T'_0}$ is the tensor tangent map at the target, with matrix entries in $I$. Form the two lifts $T_0+U,T'_0+U'$. Any transporter over $R$ is uniquely a product of a constant residue map $g$ and a left correction $1+X$ with entries in $I$. Its principal determinants are one precisely when all the traces vanish. The tensor equation on the layer is the displayed affine condition. Apply the [derivation compiler](Compiler.md) with $D(c+x)=x$. This gives a decision reduction even when the base tensors are zero or nonconcise. This comparison accounts for the entire one-layer tensor and trace condition. Requiring $\det_k(g_i)=1$ on the residue is an additional constraint over fields with nontrivial unit group.
