# Exact exponential separating degrees for fixed general-linear tensor actions

Let \(k\) be any algebraically closed field. The following representations have explicit pairs of disjoint closed \(\mathrm{GL}(V)\)-orbits with the stated exact least degree of a separating polynomial invariant.

| Representation | Dimension of \(V\) | Exact degree |
|---|---:|---:|
| \(\operatorname{Hom}(V^{\otimes 2},V)\oplus \operatorname{Hom}(V,V^{\otimes 2})\) | \(m\) | \(2(2^m-1)\) |
| \(V^{\otimes r}\otimes(V^*)^{\otimes r}\) | \(m+1\) | \((2r-1)(r^m-1)/(r-1)\) |

Here \(m,r\geq 2\). Both cubic records are symmetric in their repeated slots. The single order-\(2r\) tensors are invariant under independent permutations of each set of \(r\) slots. The same separation degree holds on those permutation-fixed subrepresentations. In characteristic zero these are ordinary symmetric powers, including a single symmetric balanced quartic and a single symmetric balanced sextic. The formulas use permutation-fixed subspaces directly in arbitrary characteristic. In characteristic zero the examples have nonnegative integer coordinates. In positive characteristic their entries can be chosen in any finite subfield with more than \(m\) elements.

Any invariant family deciding orbit closure intersection for either representation requires exponential degree in the side dimension. For \(r=2,3\) these are the balanced signatures singled out in Lysikov–Walter's Question I.12. That question asks for a complexity classification, and even the separator exhibited for the cubic pair has a polynomial-size arithmetic circuit. [Lysikov–Walter, Questions I.11–I.13](https://arxiv.org/html/2411.04639v2#S1.SS4)

## 1. Reducing to diagonal actions

A polynomial equivariant endomorphism \(A\) that at \(x\) has simple spectrum reduces closedness of \(\mathrm{GL}(V)x\) to closedness of its diagonal torus orbit. Choose a basis in which \(A(x)=\operatorname{diag}(\lambda_j)\) for distinct \(\lambda_j\). Each point in the closure has \(A\) with the same characteristic polynomial. Its roots are distinct, so a change of basis makes its endomorphism equal to \(A(x)\). For any endomorphism \(D\) in this conjugacy class let
\[
P_j(D)=\prod_{l\ne j}\frac{D-\lambda_l I}{\lambda_j-\lambda_l}.
\]
The matrix \(B(D)\) with columns \(P_j(D)e_j\) is invertible on an open neighborhood of \(A(x)\). There \(B(D)^{-1}D B(D)=A(x)\). The regular map \(z\mapsto B(A(z))^{-1}z\), with the inverse matrix acting via the representation, sends each orbit point in its domain into the diagonal torus orbit of \(x\). It fixes points with \(A(z)=A(x)\). By continuity on this open set the normalized limit belongs to the closure of the diagonal torus orbit. If that orbit is closed, the limit belongs to the full orbit.

Restriction to a torus-stable coordinate family also bounds separating degrees. The coordinate monomials are eigenvectors under the torus, and independence of distinct characters forces every monomial of a restricted invariant to have total weight zero. This holds in every characteristic over the infinite field \(k\). The restriction maps below are linear and hence do not increase degree.

## 2. Cyclic weights

Let \(\epsilon_1,\ldots,\epsilon_m\) be basis characters of a torus, written additively. Put \(\epsilon_{m+1}=\epsilon_1\), \(w_i=r\epsilon_i-\epsilon_{i+1}\), \(Q=r^m-1\), and \(S=1+r+\cdots+r^{m-1}=Q/(r-1)\). An integer equation \(t\epsilon_1=\sum_i c_i w_i\) gives \(c_{j-1}=r c_j\) for \(2\leq j\leq m\) and \(t=r c_1-c_m=Q c_m\). Thus \(c_i=r^{m-i}(t/Q)\). For payload weight \(r\epsilon_1\), an equation \(rt\epsilon_1=\sum_i c_i w_i\) still gives \(Q\mid t\) because \(Q\) and \(r\) are coprime. At \(t=Q\) its solution is \(c_i=r^{m-i+1}\).

For the corresponding torus orbit, write the acting coordinates as \(u_i\in k^\times\) and set \(z_i=u_i^r/u_{i+1}\) using cyclic indices. The equations can be solved successively from \(u_1\), and the closing equation is
\[
u_1^Q=\prod_i z_i^{r^{m-i}}=:C(z).
\]
When both forward and reverse markers have nonzero starting values, the torus orbit satisfies reciprocal relations that cut out a closed locus and make all \(z_i,z_i^{-1}\) regular there. Alongside these markers a payload initially zero stays zero. A payload initially \(1\) of weight \(\epsilon_1\) takes exactly the values \(y\) with \(y^Q=C(z)\), since one can start the recursion at \(u_1=y\). For weight \(r\epsilon_1\) the equation becomes \(y^Q=C(z)^r\). To see sufficiency choose integers \(\alpha,\beta\) with \(\alpha Q+\beta r=1\) and take \(u_1=C(z)^\alpha y^\beta\). It satisfies \(u_1^Q=C(z)\) and \(u_1^r=y\). For payload zero the marker closing equation has a root by algebraic closedness. These are closed equations in the reciprocal locus and in each case describe the full torus orbit. This argument works when the characteristic divides \(Q\), since it uses existence of a scalar root over \(k\) and every regular normalization uses only the distinct eigenvalues of the endomorphism.

## 3. Two mixed cubic tensors

Use a basis \(e_1,\ldots,e_m\) with cyclic subscripts. Choose pairwise distinct nonzero \(b_1,\ldots,b_m\). Define two symmetric maps by
\[
\mu(e_i,e_i)=b_i e_{i+1},\qquad
\delta_x(e_{i+1})=e_i\otimes e_i,
\]
with unused coordinates zero. Add the term \(x(e_1\otimes e_2+e_2\otimes e_1)\) to \(\delta_x(e_2)\). The two points use \(x=0,1\). The equivariant endomorphism \(\mu\delta_x\) takes \(e_{i+1}\) to \(b_i e_{i+1}\), since the extra term has distinct inputs for \(\mu\). The torus weights of the guard coefficients in \(\delta_x,\mu\) are \(w_i,-w_i\) with \(r=2\), and the payload has weight \(\epsilon_1\). Sections 1 and 2 prove both full orbits are closed. Every transporter between the two points must centralize their common simple-spectrum endomorphism, and diagonal transport preserves the condition \(x=0\). The closed orbits are disjoint.

Allow all marker coefficients and \(x\) to vary independently, keeping the two payload placements tied. This is a torus-stable linear coordinate family. A restricted invariant monomial distinguishing the points has positive \(x\)-exponent \(t\). If its forward and reverse exponents are \(f_i,b'_i\), then \(c_i=b'_i-f_i\) satisfies the equation in Section 2. Thus \(t\geq Q=2^m-1\) and the monomial has degree at least \(t+\sum_i |c_i|=2t\geq 2Q\).

For equality, partially contract one output of \(\delta\) with its input to obtain a vector \(v_1\), which on the examples is \(x e_1\). Form \(v_{i+1}=\mu(v_i,v_i)\) for \(i<m\), and let \(L_v(w)=\mu(v,w)\). Then
\[
F(\mu,\delta)=\operatorname{tr}(L_{v_m}\cdots L_{v_1})
\]
is an invariant polynomial. On the examples \(v_i=d_i x^{2^{i-1}}e_i\), with \(d_1=1\) and \(d_{i+1}=b_i d_i^2\). The endomorphism inside the trace sends \(e_1\) to \((\prod_i b_id_i)x^{Q}e_1\) and kills every other basis vector, so \(F\) separates the points in every characteristic. The degree is \(2Q\), since \(v_i\) has degree \(2^i-1\) and \(L_{v_i}\) has degree \(2^i\).

## 4. One balanced tensor of order \(2r\)

Use a basis \(e_0,\ldots,e_m\) with dual basis \(e_j^*\). Write \([a;b]\) for the sum of the \(r\) distinct placements of \(a\) among \(r-1\) copies of \(b\). The successor of \(m\) is \(1\). Choose distinct \(\lambda_0,\ldots,\lambda_m\) and set
\[
\begin{split}
T_x={}&\sum_{j=0}^m \lambda_j e_j^{\otimes r}\otimes(e_j^*)^{\otimes r}\\
 &+\sum_{i=1}^m \left(e_i^{\otimes r}\otimes[e^*_{i+1};e^*_0]
       +[e_{i+1};e_0]\otimes(e_i^*)^{\otimes r}\right)
 +x e_1^{\otimes r}\otimes(e^*_0)^{\otimes r}.
\end{split}
\]
The partial trace over \(r-1\) pairs gives \(\operatorname{diag}(\lambda_j)\). Only the first sum survives, since the primal and dual indices of each other term are disjoint. Relative to coordinate \(0\), the characters \(\epsilon_i\) are \(u_i/u_0\) in multiplicative notation. The forward and reverse marker weights are \(w_i,-w_i\) and the payload weight is \(r\epsilon_1\). The same normalization and torus equations show that \(x=0,1\) give disjoint closed orbits.

Allow the tag, forward marker, reverse marker and payload coefficients to vary independently. By Section 2 a weight-zero monomial with positive payload exponent \(t\) has \(t\geq Q\). The net reverse exponents are \(c_i=r^{m-i}(rt/Q)\), so its degree is at least
\[
t+\sum_i c_i=\frac{2r-1}{r-1}t\geq Q+rS.
\]
At equality there are \(Q\) payload factors, \(b_i=r^{m-i+1}\) copies of reverse marker \(i\), and zero tags and forward markers.

Construct one contraction of \(D=Q+rS\) copies of the ambient tensor. The primal slots of each copy are outputs and the dual slots are inputs. Partition the labeled copies into \(Q\) copies \(X\) and layers \(R_i\) of \(b_i\) copies. Select one \(R_1^*\) in layer \(R_1\), which has \(Q+1\) members.

1. Send all \(r\) outputs of each \(X\) copy to all \(r\) inputs of a distinct nonreserved \(R_1\) copy.
2. For each \(i=2,\ldots,m\), partition the first outputs of the copies in \(R_{i-1}\) into groups of \(r\). Send each group to all inputs of a distinct \(R_i\) copy. Send the first outputs of the \(r\) copies of \(R_m\) to the inputs of \(R_1^*\).
3. Send all remaining outputs from the \(R_i\) copies bijectively to the inputs of \(X\). There are exactly \((r-1)rS=rQ\) slots on each side.

These pairings define a complete contraction through evaluation and hence a polynomial invariant. Any nonzero summand on \(T_1\) that uses the payload obeys the counts forced at degree \(D\), because each edge matches the same primal and dual index. Each participating copy is a payload factor or a reverse marker, and all its inputs have equal indices. A copy in \(X\) sends its \(r\) outputs to a single target, so its outputs are all equal. This forces the payload type, since a reverse marker has two distinct output indices. These \(Q\) copies use the entire payload quota. Step 3 forces the last \(r-1\) output indices of every \(R_i\) member to be zero, leaving the first output as the unique nonzero index. The nonreserved members of \(R_1\) receive index \(1\) and have theoretical reverse type \(1\). Every group in step 2 for \(R_2\) contains a nonreserved \(R_1\) member, which forces input index \(2\). Induction forces each subsequent layer, and the \(R_m\) outputs force reverse type \(1\) for \(R_1^*\). Exactly one assignment uses the payload, and its coefficient is \(1\). Every assignment without it contributes equally to \(T_0,T_1\). The contraction values differ by \(1\) in every characteristic.

## Sources and verification

The cyclic recurrence develops the calculation in [the previous Frobenius separator construction](https://github.com/Dugongue/MathProofs/blob/main/TensorUniversalityApplicationsIII/DICKSON-SEPARATORS.md). The spectral readout uses the same type of projector as [the earlier balanced quartic compression](https://github.com/Dugongue/MathProofs/blob/main/PortfolioIsomorphismCrossovers/BalancedQuarticCompression.md). Acuaviva et al. already give exponential separation degrees for a single complex PEPS tensor under a product of general linear groups, and an exact threshold in their construction. Their lower bound applies to separating their two input tensors under the diagonal acting subgroup as well. The conclusions here include an explicit pair of closed orbits in the independently symmetric balanced subspace, the sharp formula in arbitrary characteristic, and a fixed pair of opposite-variance cubics. [PEPS degree bound, Proposition 4.15 and Remark 4.16](https://arxiv.org/html/2209.14358#S4.SS3)

Derksen and Makam established exponential degree lower bounds for invariant generation and null-cone definition in several special-linear actions. [Characteristic-zero degree bounds](https://arxiv.org/abs/1902.10773) · [All-characteristic polystability and degree bounds](https://arxiv.org/abs/2107.06838)

The proof is written mathematics. The companion exact replay checks the cubic contraction in finite fields, the weight recurrences, and the balanced contraction uniqueness for small formats. Publication priority for these particular bounds remains unverified.
