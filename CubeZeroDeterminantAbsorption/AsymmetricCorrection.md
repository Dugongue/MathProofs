# An upper bound for one-sign TI with an independent odd automorphism test

Work over F₃. Write A for one-sign tensor isomorphism, F for a source odd-automorphism test, and C for the asymmetric correction comparison defined in the determinant chain. The input to C is one ordinary raw tensor pair. Let D be its relative three-bit sign profile, and H its source's stabilizer sign subgroup. It accepts if D is nonempty and both of the following hold:

1. A relative transporter has first sign zero, or a source automorphism changes the third sign.
2. A relative transporter has second sign zero, or a source automorphism changes the first sign.

The two relative witnesses may be independent. Every arrow described below is a deterministic polynomial-time many-one reduction.

**Proposition.** A∧F reduces to C. In particular, a full reverse reduction C to A would settle the requested absorption.

Take an A comparison (T,T′) and an independent source U for F. Use the one-axis construction below and a direct sum to give a combined pair with relative sign profile

    D = {(1,d,h) : d is attainable on the tested A mode,
                       h is attainable on the tested stabilizer mode of U}.

To construct it, project the relative pair to the second coordinate only and the self-pair (U,U) to the third coordinate only. Take the direct sum of the resulting pairs and reflect a target coordinate in the first mode. This makes the first sign always one, while preserving relative emptiness. The source stabilizer profile has zero first bit, independently of which relative transporter exists. Its third bit can be one precisely when the F predicate holds.

For the resulting raw comparison, the first clause of C cannot use a first-positive transporter and thus requires F. The second clause cannot use first-mode stabilizer correction and thus requires A. If the original relative pair is ordinarily inequivalent, D is empty and C rejects. The reduction really uses one raw C input and preserves both conditions on arbitrary inputs. The one-axis construction gives the required exact sign profiles without using the general three-sign projection.

The known reduction A≤A∧F uses a fixed positive F instance. This proposition therefore places A∧F between A and C, below the unrestricted two-conjunction of independent one-sign comparisons. It neither assumes nor establishes that these degrees are distinct.



## The one-axis construction used above

For a raw pair, move the designated mode first. Unequal formats or unequal support dimensions give a fixed negative output. If that first mode is deficient or has odd dimension, and a transporter exists, both signs are attainable by a complement reflection or a compensated scalar minus one. Use the ordinary TI comparison in a [determinant-neutral multiplication cube](NeutralConjunction.md), and take its direct sum with a fixed action tensor with both signs in the desired mode, as described below. For zero-dimensional designated modes there is only the positive sign, so the cube alone suffices for a relative comparison and the odd-self test fails. These steps handle zero tensors as well. For inputs passing these branches the first mode is injective as a flattening and has positive even dimension.

The [cube-zero construction](OddAutomorphisms.md) is exact for relative pairs as well as self-pairs. Pad the two untested modes to odd dimensions larger than the tested dimension, then use their calibrated castling annihilator. Relative transporters give and are recovered from annihilator transporters by double annihilation. The original first sign equals the transformed product sign. The new concise tensor has all three dimensions odd. The associated local scalar-residue algebra B with radical cube zero therefore has even dimension b. Its algebra transporters have exactly the determinant signs of the original first mode, by the filtration in the cube-zero construction. The argument uses independent chart choices with determinant-one ambient completion at each endpoint.

Now use the tensor of the left action of B on B⊕B, of format (b,2b,2b). For its transporter (s,g,h), with s the label map, g the module input and h the module output, the equality at label 1 is h=L_u g for u=s(1). Thus u is a unit, and the other labels give
$$
 L_{\phi(a)}=g L_a g^{-1},\qquad \phi(a)=u^{-1}s(a).
$$
Faithfulness and the unit show that phi is an algebra isomorphism. Conversely every algebra isomorphism extends with g=h=phi⊕phi and u=1. The label sign equals det(phi), since unit multiplication has positive determinant for even b. After removing phi⊕phi, the map g is linear over the target algebra. Its map on the free rank-two module modulo the radical is a 2-by-2 matrix over the scalar residue. On all radical grades it acts by that matrix on the free-module index, so its determinant is the determinant of that matrix to the power b, which is positive. Hence g and h are positive. Dualizing in the tensor convention preserves all signs over F₃.

This action tensor is concise, and its centroid is the center of B. In fact the identity slice identifies the input and output components of a centroid element, and equates that linear map to left multiplication by the label component's value at 1. The other slices force that value to commute with every element of B, and the label map is multiplication by the same value. Since B is local, its center has scalar residue and nilpotent kernel. The action tensor is therefore indecomposable. To get a fixed sign-flexible auxiliary for the free branch above, take B=F₃⊕V⊕W with V two-dimensional and W one-dimensional, and radical product the identity symmetric form on V. A single-coordinate reflection of V gives the negative algebra sign, and the identity gives the positive one. The same action tensor proof applies to this four-dimensional B.

Permute the active label role to mode two on the relative pair and to mode three on the self-pair. Their indecomposable active factors have formats (2b,b,2b) and (2b',2b',b'), which cannot coincide for positive b and b'. Neither format is cubic, so the active factors do not mix with any neutral cube. If both inputs use neutral cubes, choose their cubic dimensions distinct by increasing the neutral branch parameter of the padding construction. The centroid idempotents separate all these factors. Independent transporters hence give exactly the product profile used in the proposition. All sizes and frame computations are polynomial in the raw input lengths.
