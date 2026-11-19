# A finite-field orientation lock including the Frobenius sign

Work over F₃ with an explicit three-tensor pair. One designated mode U on each side is supplied with an explicit action of a field E of degree d over F₃, and has rank r ≥ 1 over E. Assume these structures are covariant. Every ordinary transporter induces a field isomorphism on the displayed actions and is semilinear on U for that isomorphism. This applies in particular when the actions are computed intrinsically from the raw arrays and satisfy the same covariance. The other two physical determinant tests, when present, remain unrestricted.

For every fixed C, if r≤C log₂(2+L) in explicit input length L, there is a polynomial ordinary tensor-system mark enforcing determinant +1 on U. On these inputs one can eliminate one sign while retaining either or both other signs on the same transporter.

## Separate the norm and Frobenius terms

Choose aligned field coordinates via one fixed F₃-field isomorphism between the two named fields. The actual transported field map relative to this alignment is φ=Frob^j. Choose E-bases of the two copies of U. The determinant of the F₃-linear map on U is

    δ · Norm_{E/F₃}(k) · (-1)^((d−1)rj).

Here δ∈{1,−1} is the computable ratio of the aligned coordinate frame determinants in the original F₃ frames, and k is the E-determinant of the linear part in these coordinates. The first identity is the determinant of restriction of scalars for a linear E-map, followed by a semilinear Frobenius action on the r coordinates. One sees the latter sign by cyclically permuting a normal field basis. Fixed alignment and coordinate changes are all included in δ.

Include the fields, their action on U, and the E-exterior ladder as mixed tensor data. Degree i is an E-module of dimension binom(r,i) with its field action and its successive wedge product. The marks force the action on the top E-line D to be a↦kφ(a) in its displayed basis. For k∈E*, Norm(k)=+1 exactly when k is a square, by cyclicity of E*. Choose a target coefficient θ with Norm(θ)=δ.

If d is odd or r is even, add an E-line with bilinear map to D given by multiplication on the source and by θ times multiplication on the target. Its semilinear map a↦sφ(a) extends the transporter precisely when θs²=k. This exactly enforces the original determinant sign.

## Correct the even-degree, odd-rank case

When d is even and r is odd, let ω be a square root of −1 in the unique F₉ subfield. In aligned field frames choose the same ω on each side. Add a copy of the split F₃-algebra F₃² and a linear mark sending its two ordered primitive idempotents to ω and −ω in E. Its algebra isomorphism permutes these two idempotents, and their mark makes the permutation z↦z′ satisfy z′=z+j mod 2. Add two E-lines R₀,R₁ linked to these idempotents by the corresponding block action. Put a bilinear map (R₀⊕R₁)×(R₀⊕R₁)→D with zero mixed blocks and line coefficients

    source: c^z,        target: θ c^z,

where c is any nonsquare in E*. Semilinearity and the marked label permutation require the comparison of the z and z′ squares to satisfy

    θ c^z′ s_z² = k φ(c^z).

Both equations are solvable exactly when Norm(k)=δ(-1)^j. Indeed taking norms uses Norm(c)=−1 and Norm(φ(c))=Norm(c), and a norm of +1 is sufficient for a square root in each equation. The multipliers s_z are independent. This is exactly the remaining Frobenius correction in the determinant formula. The forcing marks link all choices to the same field map induced by the actual original transporter.

## Effective choices and polynomial size

Deterministic field alignment can use the tensor product E⊗_{F₃}E′. For equal-degree finite fields it is a product of d copies of E′. Its Frobenius-fixed subalgebra, computed as the linear kernel of x↦x³−x, is a split algebra F₃^d. Joint eigenspaces of multiplication by a basis of the fixed algebra yield its primitive idempotents. On any component the two field embeddings identify E with E′, with all maps given by linear algebra. If d is even, the field F₉ is the linear kernel of x↦x⁹−x, where an ω can be found by direct enumeration. To find a nonsquare, start with −1 and repeatedly replace it by a square root until it ceases to be a square. A square test and root can be computed by taking the same Frobenius-fixed subalgebra in E[X]/(X²−a), which is either one field or two copies of E. The order of the chosen 2-primary element doubles at each successful step, so there are O(d) steps. Computing E-bases and storing all these field operations takes polynomial time in the original explicit input. A difference in the required covariant degree or ranks can be sent to a fixed negative pair. Field actions and marks are included on both sides with matched signatures.

The exterior ladder has total F₃-dimension d·2^r. All tensors used as marks have order at most three and their dense tables have polynomial size in L. The standard ordinary compiler handles the case with no remaining sign, and the retained-sign compiler handles one or two remaining signs. [Ordinary system compiler](https://arxiv.org/html/2306.03135v2#S4) · [Retained-sign compiler](https://github.com/Dugongue/MathProofs/blob/main/TensorSignChain/RetainedSigns.md) · [Earlier rank-one field pencil case](https://github.com/Dugongue/MathProofs/blob/main/ObjectwiseTensorOrientation/FieldPencils.md)

This proof is informal. It requires a supplied or deterministically recovered covariant field action of low E-rank. The construction does not recover such fields on arbitrary tensors.
