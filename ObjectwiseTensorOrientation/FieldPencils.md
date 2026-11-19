# One ordinary orientation mark for a field of alternating forms

Work over F = F_3. Let T be a raw tensor with tested mode U_T. Suppose a polynomial-time procedure computes a nonzero subspace Q_T of alternating forms on U_T and that the pullback by every ordinary transporter carries Q_S onto Q_T. Choose any invertible form B_T in Q_T. Define the subspace of operators

    E_T = { A in End_F(U_T) : B_T(Ax,y) is a form in Q_T }.

**Theorem.** On the raw class where E_T is a field under operator composition, there is a deterministic polynomial-time object map enforcing positive tested determinant by ordinary bounded-order tensor marks. The algebra E_T is computed from the input. Its dimension can grow linearly with the dimension of U_T. The construction does not enumerate its elements. When one or two additional signs must remain live on the same transporter, the objectwise signed compiler gives one comparison with one or two live sign conditions respectively. [Objectwise signed compiler](RetainedKernel.md)

## Recognition and covariance

Choose the first nonzero vector in a computed basis of Q_T, using any deterministic elimination order. If it is singular, reject this sufficient-condition test. Otherwise it gives B_T and the displayed operator space by linear algebra. Test closure under composition and commutativity on a basis of E_T. It contains the identity. Test bijectivity of the cube map A↦A³, which is F-linear on a commutative algebra. Then test that the cube-fixed space has F-dimension one. These are exact field tests. Injectivity of cubing excludes nonzero nilpotents in a finite commutative algebra. A finite reduced commutative algebra is a product of finite fields, and each factor contributes exactly one fixed dimension under cubing. Hence the tests pass precisely when the operator space is a field.

If some invertible B with the required field property exists, then every nonzero member of Q_T is invertible. In fact Q_T consists of B(A−,−) for A in that field, and every nonzero A is a unit. Replacing B by any other nonzero member simply multiplies the operators by one fixed nonzero element of the same field, so E_T is unchanged. This proves that the deterministic first-basis-vector choice detects the entire class. It also proves that E_T is covariant under an ordinary transporter: conjugation transports the operator construction based on any B to the same field in the target. The tests use polynomially many matrix operations and linear equations. They do not require field factoring or a supplied transporter.

The relation between E_T and Q_T gives Q_T a rank-one E_T-module structure, in which λ in E_T acts by replacing the first argument x of a form by λx. Every such λ is self-adjoint with respect to B_T. Indeed the form B_T(λx,y) is alternating, so antisymmetry gives B_T(λx,y)=B_T(x,λy). This also ensures that the displayed rule defines an action on all of Q_T. The cotransport on forms is compatible with the conjugation map on the field.

## The exact Pfaffian formula

Write E for one of the recovered fields and B for the chosen generator. The action of E makes U into a finite-dimensional E-vector space. The nondegenerate trace pairing defines an E-valued form η by

    Tr_(E/F)(λ η(x,y)) = B(λx,y) for every λ in E.

The trace identity gives E-linearity in the first variable, and self-adjointness of every element of E gives it in the second. Since B(λx,x)=0 for all λ, η is alternating. It is nondegenerate because B is nondegenerate. In particular dim_E U=2m for an integer m. Choose an E-symplectic basis for this proof. Multiplying the first vector of each hyperbolic pair by λ defines an F-linear operator whose determinant is Norm_(E/F)(λ)^m, and whose pullback of B is the form denoted by λB. The integral polynomial Pfaffian congruence identity now gives the exact formula in the original F-coordinate frame,

    Pf(λ B) = Pf(B) Norm_(E/F)(λ)^m.

The proof uses the symplectic basis only to establish the identity. The construction evaluates the ordinary F-Pfaffian of B_T directly by alternating elimination. Write p_T=Pf(B_T) in F×.

For an ordinary tested map g:U_T→U_S write h:Q_T→Q_S for the inverse of its pullback. Let σ:E_T→E_S be conjugation by g. The form equation says that h sends xB_T to σ(x) μ B_S for a unique μ∈E_S×. Applying the Pfaffian identity to g and h(B_T) shows

    det_F(g) positive  iff  p_S Norm_(E_S/F)(μ)^m = p_T.

Thus the only remaining orientation condition is on the norm of a single scalar on a rank-one field module. The scalar is unknown, and the next step imposes its norm by explicit marks.

## Compile the norm without enumerating the field

Include the original tensor, the field multiplication and unit on E_T, its evaluation action on U_T, the evaluation of Q_T on the two tested copies of U_T, and the field action on Q_T. Use the appropriate dual or identity links so the evaluated form sees exactly the physical tested map. The scalar output is fixed. Any transporter of this diagram must induce σ and h as above. Conversely every original transporter extends uniquely to these field and form actions. In the following module sorts use B_T as a coordinate choice only. Do not fix it as a marked vector on Q_T.

For each j from 0 through d−1, where d=dim_F E_T, introduce a one-dimensional E_T-module Q_j. Require its map to be semilinear along the same σ by marking its actual field action. Mark the F-linear map Q_T→Q_j defined in the chosen coefficient frames by x↦x^(3^j). Its entries are obtained by powering the basis using field multiplication. Since σ commutes with cubing, the induced multiplier on Q_j is μ^(3^j). Link these d module sorts by successive bilinear scalar multiplications into new one-dimensional E_T-modules. In their displayed coefficient frames each link is the usual multiplication of the two scalar coordinates. Thus their final product line has semilinear multiplier

    ∏_(j=0)^(d−1) μ^(3^j) = Norm_(E_S/F)(μ),

which lies in F×. A link forces exactly the required product multiplier and imposes no restriction on an ordinary transporter, because every such map extends using the indicated multipliers.

For m odd, mark the final line vector of coefficient p_T^(-1). Preservation says that the final multiplier sends p_T^(-1) to p_S^(-1), exactly the positive determinant condition. For m even the norm power is one, so instead place the explicit scalar p_T in the fixed scalar sort. Then preservation is p_T=p_S, also exactly the condition. In either case every positive tested transporter extends to the diagram and every diagram transporter is positive in the tested mode. The number of sorts and maps is O(d) beyond the original data. Each new line has F-dimension d, every component has at most three variable slots, and the tables are polynomial to construct. In particular the method does not list forms indexed by the 3^d field elements.

Apply the ordinary tensor-system compiler for a single ordinary comparison. If one or two other physical determinants are still needed, instead use the objectwise signed compiler to retain those roles. These signs are tested on the same original transporter that met the norm condition. This yields a kernel reduction on the stated class. Unequal formats or a change in the outcome of an invariant recognition test cannot create a positive orbit and can be treated by fixed format marks. [Standard bounded-order compiler](https://arxiv.org/html/2306.03135v2#S4) · [Objectwise retention](RetainedKernel.md)

## Raw realization of the class

Let E/F be any finite extension, let U=E^(2m) for m≥2, and choose a nondegenerate alternating E-bilinear form η. Use the F-pencil

    Q = { (x,y) ↦ Tr_(E/F)(λ η(x,y)) : λ∈E }.

This has F-dimension d and every nonzero form is invertible. For example, if x≠0 then η(x,−) is a surjective E-linear map to E, so a value with nonzero trace after multiplication by λ exists. The field recovered by the operator construction is exactly the copy of E acting on U. Indeed for B equal to the trace form at λ=1 the correspondence is the scalar action, and the conclusion holds for any chosen nonzero B by the independence already proved.

Realize Q by the raw symmetrized quotient tensor. Start with the common annihilator K of Q in Λ²_F U, embed that exterior square in U⊗_F U by x∧y↦x⊗y−y⊗x, and define T as the bilinear quotient map to (U⊗_F U)/K. Fresh independent rebasing of each physical space is allowed. Recover the annihilator K_raw by flattening and solve the linear equations on m_0:V→U requiring that (I⊗m_0)K_raw vanish in Sym²_F U. In the hidden common basis the identity is one solution. For any nonzero x, the d linear equations of Q leave a common orthogonal subspace of dimension at least dim_F U−d, so one can choose y independent of x there. The corresponding x∧y condition gives x m_0(y)=y m_0(x) in the symmetric algebra. Independent degree-one elements x,y are coprime, forcing m_0(x) to lie on Fx. Therefore m_0 is scalar in hidden coordinates. The system recovers exactly the line of the hidden identification. With any nonzero solution, take the annihilator of its image of K_raw in Λ²_F U to recover Q. That annihilator is independent of scaling the identification and is covariant under every ordinary transporter by the linear construction. For a raw recognition test verify equal input dimensions, spanning of the output, a one-dimensional solution space with invertible generator, the needed codimension bound dim Q≤dim U−2, and then the explicit field tests. All are polynomial. [Earlier raw quotient extraction](https://github.com/Dugongue/MathProofs/blob/main/OneSignTensorComparison/SymbolicPencils.md)

For m fixed, the pencil dimension d is linear in the tested dimension and exceeds the logarithmic width in the earlier form enumeration arguments. With even m the entire stabilizer is positive in the tested mode by the norm formula. A single-mode negative reflection yields an ordinary-positive comparison that fails the one-sign test. With odd m, an E-similitude of multiplier λ of negative field norm acts simultaneously on the two copies of U. It preserves Q as a family and hence preserves K, so it extends to the quotient tensor. Its tested determinant is negative, giving a flexible instance. The same field mark works for both families.

The proofs are informal. They cover an intrinsic-pencil class with unbounded operator field and give no universal extraction of such a field for arbitrary tensors.
