# One ordinary TI comparison from a symbolic alternating pencil

**Theorem.** Work over the field F of three elements. Suppose that each raw tensor determines a computable covariant subspace B(T) of alternating forms on the tested mode V. Covariance means that the pullback by every ordinary transporter g sends B(S) onto B(T). Suppose the dimension d of this space is bounded by an absolute constant and its determinant polynomial is nonzero. Thus some form over an extension field is nonsingular. A deterministic polynomial-size object map reduces one-sign TI on this class to ordinary TI. The map uses exact base-field transporters and works whether the stabilizer sign is flexible or rigid. The hypothesis allows every individual form over F to be singular.

## Compile the oriented form family

Let n be the tested mode dimension and take the same explicitly represented field E of order Q>n for each raw format, with Q≤3(n+1). A defining polynomial of the required degree can even be found by finite enumeration in polynomial time because its degree is O(log n). Extend B(T) to E and mark all forms in B(T)⊗E, partitioned by their **exact** Pfaffian in E, including zero. A nonzero minor polynomial has degree at most n on the coefficient variables. Since Q>n, there is a nonsingular form by the usual polynomial evaluation bound. Therefore exact Pfaffian color preservation under pullback is equivalent to positive determinant.

Here is an explicit tensor-system realization of the latter construction. Use the split coordinate algebra E^X with one primitive coordinate idempotent per enumerated form, where X is now the set of all forms. Include multiplication and the algebra unit. Its automorphisms permute the idempotents. Mark the vector whose coordinate at a form is its Pfaffian. Include the trilinear evaluation which on a coordinate idempotent e_J and two vectors gives J(u,v), with the scalar output fixed by a unit mark. Tie the two copies of the tested vector space to its physical mode by identity maps. Then preserving evaluation makes the permutation of idempotents exactly the permutation of forms by pullback. Mark physical Frobenius on the three modes, so their extended maps are always defined over F. The auxiliary permutation of the coordinate algebra does not introduce any additional restriction on a genuine positive base-field transporter. On restriction of scalars also mark multiplication by a fixed generator of E, to enforce E-linearity. This is a polynomial-size bounded-order mixed tensor system. Uniform packing into a fixed number of components and the ordinary tensor-system compiler turn it into one ordinary TI object. A distinct format tag for each original input shape can be used so unequal shapes do not accidentally match. Thus a single per-object map works with no correlated choices between the inputs. [Uniform packing](https://github.com/Dugongue/MathProofs/blob/main/SLAdjointMultiplicities/PRIOR-UNIFORM-PACKING.md) · [Ordinary TI compiler](https://arxiv.org/html/2306.03135v2#S4)

## Recover the form pencil from raw symmetrized exterior quotients

The following raw family verifies the hypothesis by linear equations. Let U have dimension n, and identify a second copy V with U in the hidden standard presentation. Let K be the common annihilator in Λ²U of a d-dimensional alternating pencil B, where d≤n−2. The quotient map is the bilinear tensor

    U × U → (U ⊗ U)/K.

Use the alternating embedding x∧y ↦ x⊗y−y⊗x. An actual raw rebase determines the kernel K_raw of its flattening U⊗V→W. Solve linear equations on m:V→U requiring that the composition (1⊗m)K_raw projects to zero in Sym²U. In hidden coordinates m=I solves the equations. Conversely for every nonzero x, the common equations b(x,y)=0 for b∈B allow some y independent of x because n−d≥2. Then the imposed condition gives

    x m(y) = y m(x)

as a polynomial of degree two in the symmetric algebra. The independent degree-one elements x,y are relatively prime. It follows that x divides m(x), so m(x) lies on the line through x. A linear map preserving all lines acts as a scalar, by applying it to basis vectors and each sum of two basis vectors. This proves that the solution space is exactly the scalar line of the hidden identification. Its nonzero elements are invertible. Using any one of them identifies K_raw with a subspace of Λ²U, and taking its annihilator recovers B exactly. Changing the chosen identification by a scalar leaves that annihilator unchanged.

This is also a recognition procedure for the unrestricted B-quotient format within the indicated dimensions. If the solution space is one-dimensional with invertible generator, take the image K. Check that its codimension in Λ²U is at most n−2 and the original tensor values span W. The induced quotient then gives the required presentation. Conversely all displayed models pass the tests. For constant d the existence of a nonsingular extension form is checked by the enumeration above. Covariance is exact because the identification equations are transported by g_U m g_V⁻¹. Pullback on the first mode consequently takes the two recovered pencils to each other.

## An example with no nonsingular base-field form

Take n=8r and split U into four blocks of dimension 2r, each with a standard nondegenerate alternating matrix J. Use the pencil with block values

    xJ, yJ, (x+y)J, (x−y)J.

Every pair (x,y) over F makes a factor zero. Thus every base-field pencil form has corank at least 2r. The Pfaffian polynomial is a nonzero constant times [xy(x+y)(x−y)]^r, so the extension construction applies to every r.

The tested sign is rigid for r even and flexible for r odd. In fact an autotopism of the quotient induces a linear map on the recovered pencil. Its action permutes the four rational projective zero lines, so it takes the squarefree degree-four product to itself up to a nonzero scalar in F. For even r the Pfaffian polynomial is therefore invariant, and the Pfaffian congruence identity forces determinant +1. For odd r the coefficient substitution (x,y)↦(−x,y) is realized by a congruence swapping the last two blocks and using sign-minus similitudes on three blocks. The block swap contributes determinant +1 because the block sizes are even. Each similitude can be taken as diag(−I_r,I_r), of determinant (−1)^r. Their product has determinant −1. This map preserves the pencil and therefore induces a quotient tensor autotopism with equal tested and second input maps. For even r, reflecting the first mode gives an ordinary-equivalent pair with a negative-only tested coset.

The result shows that symbolic rank in a small covariant pencil suffices, even when an entire finite-field family of candidate forms has a large radical. It does not establish that arbitrary tensors admit such a pencil. The arguments and the reused tensor packing are informal in this packet. Publication priority for the reduction is unverified.
