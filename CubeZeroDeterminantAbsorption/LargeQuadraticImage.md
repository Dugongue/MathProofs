# Determinant tests for two families of cube-zero multiplication tensors over F₃

Informal proof. This note concerns 3-tensors of unital local associative algebras with scalar residue and radical cube zero over F₃. It gives one ordinary tensor-isomorphism query to test a prescribed determinant sign in either of two polynomially recognizable families. Write TI for ordinary 3-tensor isomorphism, A for TI with determinant +1 in one prescribed mode, and F for the test whether the stabilizer of one tensor has an element of determinant −1 in its prescribed mode.

## Algebra and raw frames

For raw multiplication-tensor recognition, require three equal positive dimensions d and an injective slicing map. Treat the slices as linear maps M(u) from the second input to the output. Compute by linear equations the algebra E of pairs (P,Q) such that QM(u)=M(u)P for every u. Require dim E=d and test whether both remaining mode spaces are isomorphic to the left regular E-module, with the E-actions as fixed operator tuples. These are constructive module-isomorphism tests in deterministic polynomial time. With successful identifications, every slice is right multiplication by its value at 1. The injective slicing map identifies the first mode with all such right multiplications. This gives three multiplication frames for R=E^op. Conversely, a unital multiplication tensor passes the tests: in multiplication frames the identity slice forces P=Q and commuting with every left multiplication forces right multiplication. [Brooksbank and Luks, Testing Isomorphism of Modules](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

The residue and radical can be recognized in this family without general radical decomposition. In every algebra in the promise each x=t·1+j satisfies x³=t·1, since the scalar commutes with j, the characteristic is 3 and j³=0. Compute the cubes of the basis vectors of R and reject if one fails to be scalar. Use the corresponding scalar coefficients as the values of a candidate linear residue map. Check that it is a unital homomorphism by testing all basis products, and that its kernel has cube zero by linear algebra on products. If all tests pass, its kernel is a nilpotent ideal with field quotient, hence is the radical. On the promised input the basis cubes recover the true map. This proves promise recognition directly from the recovered multiplication.

Let R be such an algebra, J its radical, V=J/J², W=J², and m : V × V → W its induced product, with outputs spanning W. Choose independent bases for V and W and lift the V basis to J. The resulting ordered basis (1,V,W) identifies R with F₃⊕V⊕W, where the only nonzero products within J arise from m. A pair of maps g : V → V′ and h : W → W′ extends to an algebra isomorphism exactly when h m(v,w)=m′(g v,g w). The determinant of any lift to the ordered algebra bases is det(g) det(h).

Every isotopy of unital associative algebras in multiplication coordinates has the form
```
a(x) = u φ(x)
b(x) = φ(x) v
c(x) = u φ(x) v
```
for an algebra isomorphism φ and units u,v. Indeed c(xy)=a(x)b(y) gives c(x)=a(x)v=u b(x) for u=a(1) and v=b(1). The resulting left and right multiplication maps are bijections, so u,v are units. Substitution then proves multiplicativity of φ(x)=u⁻¹c(x)v⁻¹. Both left and right multiplication by a unit with residue t∈F₃* have determinant t^(dim R) by the filtration R⊃J⊃W⊃0. If dim R is odd, units alone permit either sign in each individual mode. If dim R is even, both units act with positive determinant. In that case the sign in any tested physical mode is det(g) det(h) times the product of the determinants of the two recovered physical basis changes for that mode. Compute those factors directly and include them in the requested algebra sign. In using the convention with the dual action on an input mode, the inverse determinant equals the determinant over F₃.

## Theorem 1 — one large quadratic image

Fix C. Let L be the input bit length, n=dim V, and write W₊, W₋ for the images of the symmetric and skew parts of m. These are intrinsic, and W=W₊+W₋. Write Γ₊(V)=Sym² V and Γ₋(V)=Λ² V, and let K₊ and K₋ be the kernels of the surjections Γ₊(V)→W₊ and Γ₋(V)→W₋ induced by those parts. Suppose n is even and there is a sign ε with dim Kε≤C log₂(L+2) and dim Pε≤C log₂(L+2), where Pε=W/Wε. The prescribed-mode sign test and odd-self test each reduce to one ordinary TI instance in polynomial time. Both symmetric and alternating choices of ε are allowed. The dimensions are computed by elimination. The same fixed choice of ε can be made at the two ends of any isomorphism.

Use ordered bases of V, W, Wε, Pε, Kε. The two exact sequences are
```
0 → Kε → Γε(V) → Wε → 0
0 → Wε → W → Pε → 0 .
```
In each sequence choose an adapted basis of the middle space by adjoining arbitrary lifts of the right-hand basis to the embedded left-hand basis. Let c(R) be the product of the determinants of the two adapted bases against the standard middle-space bases. These constants are signs.

In standard monomial and exterior bases, det Sym²(g)=det(g)^(n+1) and det Λ²(g)=det(g)^(n−1). Over an algebraic closure, triangularize an endomorphism and multiply its induced diagonal entries, which are the diagonal pair products with or without the repeated index. This gives the formulas over F₃ for every matrix and hence for a map between independently chosen endpoint bases. After applying both exact sequences and multiplying by det(g), the exponent on det(g) is n+2 or n, respectively. It is even. Thus
```
det(g) det(h)
 = c(R) c(R′) det(g|Kε) det(h on Pε).
```
Here and below an induced restriction between different spaces uses the separately ordered endpoint bases. Division of signs is multiplication in F₃*.

To represent this identity, encode m as the basic tensor and add Γε(V) with its spanning bilinear product V×V→Γε(V). The equation for this product forces the uniquely induced map on Γε(V). Represent the inclusion of Kε there and the quotient map W→Pε. Add the exterior algebras on the two small spaces, with multiplication and degree-one inclusion. An algebra isomorphism extending the degree-one map is uniquely forced, since the algebra is unital and generated by degree one. Restrict its induced map to the one-dimensional top-degree line by inclusion of that line. Link the two lines via a nonzero bilinear map on one-dimensional spaces, in their displayed standard volume frames, and pin one vector in the product line, scaled at the target by the specified product of signs. This forces exactly the calibrated condition above. The zero-dimensional convention uses the degree-zero top line identified by the unit. Any eligible (g,h) extends through these auxiliaries by the indicated induced maps, giving completeness as well as soundness.

Every structure has tensor order at most 3, and the number of structures and spaces is bounded independently of L. Exterior algebra dimensions are at most 2^(C log₂(L+2)). Therefore the system is constructed in polynomial time and one ordinary TI instance suffices by the bounded-order tensor-system compiler. [Chen et al., Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

Both yes and no cases occur with unbounded n and W. For n≡2 mod 4, take W=Sym² V and m the symmetric product. R has even dimension, the calibrated self sign is always +1, and F is false. For n≡0 mod 4 with n≥4, quotient Sym² V by the line spanned by e₁e₂. R again has even dimension, and the map negating e₁ alone acts by −1 on that kernel line. Hence F is true. In both examples the image W has quadratic dimension. The opposite channel can also have quadratic dimension in these examples. Choose a skew part from a surjective linear map Λ² V→W onto a subspace of dimension Θ(n²) within the symmetric image, without changing the symmetric part or W. For a concrete yes example, choose that skew part to factor through Λ² of the fixed hyperplane spanned by e₂,…,eₙ and to map into its symmetric square. The reflection on e₁ preserves the skew part and still supplies the negative sign.

## Theorem 2 — a small output and a near-nondegenerate skew specialization

The same reductions exist if dim W≤C log₂(L+2) and some nonzero ℓ∈W* makes the alternating form
```
aℓ(v,w) = ℓ(m(v,w) − m(w,v))
```
have kernel of dimension at most C log₂(L+2). No parity restriction on n is needed. Enumerate all qualifying covectors. Their set I is intrinsic and has polynomial cardinality. An isomorphism (g,h) maps ℓ to h^(−T)ℓ, preserves the form between endpoints, and induces an isometry on the symplectic quotients.

For each ℓ compute Kℓ=ker aℓ and choose an ordered basis for it, followed by lifted symplectic basis vectors for V/Kℓ. Let cℓ be the determinant of that adapted frame against the fixed V basis. An isometry of two symplectic forms in symplectic bases has determinant +1 by the Pfaffian identity Pf(PᵀAP)=det(P) Pf(A). The identity follows over characteristic zero by taking the top exterior power of the associated 2-form and dividing by the factorial. Both sides have integer polynomial coefficients, so it holds over F₃. Thus, for the corresponding ℓ′ at the other endpoint,
```
det(g) = cℓ c′ℓ′ det(g|Kℓ).
```

The many kernel spaces can be represented with a fixed number of tensor roles. Introduce E=F₃^I with componentwise multiplication. Introduce W* via its pairing with W against a fixed scalar line, and a map E→W* taking the primitive idempotent eℓ to its actual covector ℓ. This forces the correct permutation of I even when the covectors are linearly dependent. Use E-module structures on K=⊕ℓ Kℓ and on the product algebra B=∏ℓ Λ Kℓ. Include the aggregate map K→V from the kernel inclusions and the degree-one map K→B. On each summand this forces the kernel map and its uniquely induced exterior-algebra action. Form the direct sum Ω of the top exterior lines, with E-action and inclusions into B.

Add a common line D_V and map its reference vector to the element of Ω whose ℓ component is cℓ times that component's ordered volume vector. Equivariance along every idempotent then forces the map on D_V to be det(g) in the fixed endpoint frames. Any actual (g,h) extends by precisely that scalar. Taking the top exterior line of W forces det(h). The same product-line pinning as in Theorem 1 tests det(g) det(h). The sum of the exterior algebra dimensions is bounded by 3^(dim W)·2^(maxℓ dim Kℓ), polynomial in L. All structure tensors have order at most 3 and their number is fixed, so again one ordinary TI instance suffices. [Chen et al., Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

For example, take m with scalar output, a nondegenerate alternating form on an even-dimensional subspace U, and a symmetric product form on a complementary two-dimensional space K. Then every nonzero covector has skew kernel K, the skew specialization is singular, the algebra has even dimension, and a reflection fixing U witnesses odd sign whenever the symmetric form is diagonal and nondegenerate.

The same tangent determinant construction uses W₋* in place of W* when W₋ is small. In particular the symmetric-channel part of Theorem 1 extends to odd n when such a covector of W₋* exists. The exact sequences still give the calibration, and the odd residual exponent on det(g) is supplied by D_V. In this additional branch one takes a product with that third one-dimensional role.

## Consequences for absorption

For any A instance paired with an F input in either family, use the odd-self ordinary TI query for F and absorb that ordinary query into the A input by the previously proved determinant-neutral conjunction. If the A input pair belongs to either family and F is unrestricted, use the ordinary query for the A pair, regard F as its one-sign reflected self-pair, and absorb the former ordinary query into the latter in the same way. Each construction outputs one A instance. The result covers raw tensors in either indicated family. The determinant constraint for general cube-zero multiplication tensors remains open here, as does unrestricted absorption.

The multiplication-frame test and determinant-neutral conjunction are prior parts of the MathProofs odd-automorphism and one-sign TI project. The earlier cube-zero construction reduces unrestricted F to the full scalar-residue cube-zero case. The present results use additional structural hypotheses on that case. The arguments above use their exact interfaces, together with ordinary elimination and the cited tensor-system compiler.
