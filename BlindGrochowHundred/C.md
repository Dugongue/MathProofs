# Recovering algebra from multiplication tensors and trilinear contractions

The 25 audited statements in [C.lean](C.lean) give transport, reconstruction and decomposition criteria. The scalar semiring is commutative. The regular-operator results allow noncommutative algebras. The Frobenius results use commutative algebras and a scalar-valued linear functional whose multiplication pairing separates points wherever separation is stated.

## Regular operators

Evaluation at the unit recovers one-sided intertwiners from right multipliers. Imposing both regular actions restricts the multiplier to the centralizer of the transported algebra. The double-commutant criterion recovers the left-regular operators from their full commutant. It works in the presence of zero divisors. The generator theorem propagates intertwining from an algebra generating set via addition, products and scalars. A simultaneous transporter of regular-operator tuples recovers an algebra equivalence on their coefficient spaces.

Keeping the output of a multiplication tensor fixed gives a transporter criterion in terms of a single unit and its inverse. With one potentially noninvertible input transport and the other input transport surjective, the zero fibres of the output recover the remaining input kernel. For a central idempotent, the projection criterion identifies its image and the elements killed under multiplication on both sides.

## Frobenius forms

For a commutative algebra and a functional $\phi$, set $T(x,y,z)=\phi(xyz)$. The centroid test compares movement of a linear operator across two arguments. Under separation all such operators are multiplication operators. An invertible slice recovers a uniquely prescribed rescaling of the algebra product. Over a field in finite dimension the separating slices are exactly the units. The kernel of a weighted trilinear form is the annihilator of the weight. Testing contractions against a spanning set suffices for exact tensor equality.

With a transported reference pairing, checking multiplication of the two input factors proves the corresponding three-way tensor equality. A common change of basis preserving both the reference pairing and the tensor is already an algebra equivalence. Once an algebra equivalence preserves the functional, the additional weighted tensor equality is exactly transport of the weight. The product pairing is separating exactly when both component pairings are separating.

Orthogonal cross-block contractions determine whether the products of the corresponding support elements vanish. A splitting of a separating form by an orthogonal idempotent linear projection forces the projection to be multiplication by an algebra idempotent. The weighted version uses the complementary map $x\mapsto x-Px$ for the second projection. Invertible weights preserve detection of individual nilpotent powers. Normalized slices commute, and conversely commuting left contractions of a symmetric tensor with a separating reference pairing give associativity of the recovered product. The latter criterion only uses point separation and works without division by 2 or 3.

The field-level setting of tensor and algebra reductions is classical. Albert supplies the framework for multiplication isotopy. Harrison and Pareigis and Huang–Lu–Ye–Zhang provide prior results on centroids and orthogonal decompositions. Koiran studies commutation of normalized matrix slices in tensor rank. The package gives formal reconstruction and transport lemmas with their stated hypotheses. Bibliographic priority is unestablished. [Albert](https://doi.org/10.2307/1968960) · [Harrison–Pareigis](https://epub.ub.uni-muenchen.de/7099/1/7099.pdf) · [Huang–Lu–Ye–Zhang](https://arxiv.org/abs/2110.07915) · [Koiran](https://arxiv.org/abs/2006.02374) · [Grochow–Qiao](https://arxiv.org/abs/1907.00309)

## Discovery provenance

The frozen third queue supplied disjoint numeric candidates. Its one-based positions 2, 88, 151 and 176 contained handles 272034 for associativity normalization, 27777 for transport of isomorphism, 585721 for dual transfer, and 502483 and 402258 for composition and equality testing. After reveal these prompted the two directions developed here, reconstruction from multiplication on the unit and reconstruction from a pairing that separates coefficients. The handles record discovery prompts. The proofs are the independently elaborated Lean statements in this package.
