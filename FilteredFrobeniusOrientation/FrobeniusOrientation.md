# Determinant cancellation in filtered Frobenius algebras

**Status:** informal proofs, with finite exact controls. No Lean verification or publication-priority claim. These are sufficient reductions on explicitly recognizable families. They do not collapse the unrestricted ordinary, one-sign, two-sign or special-linear tensor-isomorphism degrees.

All computational statements are over the fixed field F = F₃. Tensor inputs are explicit dense arrays, and reductions are deterministic polynomial-time many-one reductions to a single ordinary three-tensor comparison. The algebraic determinant identities hold over any field. No grading, transporter, stabilizer generators or orientation is supplied.

## 1. Main sufficient reduction

Let R be a finite-dimensional commutative local F-algebra with residue field F and one-dimensional socle. Write J for its radical, N = dim R, s for its socle degree, and hᵢ = dim(Jⁱ/Jⁱ⁺¹). Thus Jˢ is the socle and Jˢ⁺¹ = 0. The tensor is the multiplication map, possibly presented after three independent changes of basis.

Requiring determinant one in the first tensor mode reduces to ordinary TI on each of these families:

1. N is odd.
2. s is odd and the Hilbert function is symmetric: hᵢ = hₛ₋ᵢ for every i.
3. R is compressed of even socle degree s = 2t, and
   α = binomial(e + t − 1, t − 1) is even, where e = h₁.

In condition 3, compressed means

    hᵢ = min{binomial(e + i − 1, i), binomial(e + s − i − 1, s − i)}.

All dimensions, s and e may grow with the input. The algorithm first recognizes the algebra and the displayed conditions. For a pair, unequal intrinsic data immediately rejects. No assumption that the algebra is isomorphic to its associated graded algebra is made.

In particular, for Hilbert function

    (1, e, e(e + 1)/2, e, 1),

the reduction works for every e not divisible by 4. For e congruent to 1 or 2 modulo 4, N is odd. For e congruent to 3 modulo 4, α = e + 1 is even. The e divisible by 4 case is not resolved by this cancellation argument.

The main identities behind the reduction are as follows, in the explicitly constructed compatible filtered bases:

- If s is odd and the Hilbert function is symmetric, every algebra isomorphism φ has determinant λ^(N/2).
- If R is compressed and s = 2t, every algebra isomorphism φ has determinant (λ det g)^α, where g is its induced map on J/J² and λ is its scale on the chosen socle vectors.

The relative determinant of the independently chosen coordinate frames must also be included when testing a raw tensor. Sections 5–7 give that calibration and the actual single-query reduction.

## 2. Perfect pairings without a grading assumption

Choose a nonzero socle vector ω and a linear functional ℓ on R with ℓ(ω) = 1. The bilinear form β(x,y) = ℓ(xy) is nondegenerate. Indeed, every nonzero ideal meets the socle: starting with a nonzero element of an ideal, choose a longest nonzero product with elements of J. That product is killed by J. Since the socle is one-dimensional, it is a nonzero scalar multiple of ω. Hence for every nonzero x there exists y with ℓ(xy) nonzero.

For every ideal I, its annihilator equals its orthogonal complement for β. This standard identity is also Lemma 2.7 of [Hermitian K-theory via oriented Gorenstein algebras](https://hoyois.app.uni-regensburg.de/papers/gorenstein.pdf). One direction is immediate. If ℓ(xI) = 0 and xi were nonzero for some i in I, the preceding argument applied to xi would supply y with ℓ(xiy) nonzero. But iy belongs to I, a contradiction. Consequently

    dim Ann(Jⁱ) = N − dim Jⁱ.

Suppose the Hilbert function is symmetric. Products show that Jˢ⁺¹⁻ⁱ is contained in Ann(Jⁱ). Symmetry gives equal dimensions, so

    Ann(Jⁱ) = Jˢ⁺¹⁻ⁱ.

It follows that multiplication induces a perfect pairing

    Jⁱ/Jⁱ⁺¹ × Jˢ⁻ⁱ/Jˢ⁻ⁱ⁺¹ → Jˢ = Fω.

For example, if x in Jⁱ pairs to zero with every element of Jˢ⁻ⁱ, then x lies in Ann(Jˢ⁻ⁱ) = Jⁱ⁺¹. Equal dimensions finish the claim. This argument uses the actual radical filtration and is valid in characteristic three.

## 3. Odd socle degree

Write s = 2t + 1. For grades 0 through t choose bases, taking the class of 1 for grade 0. For each complementary grade choose the basis dual under the perfect product pairing into ω. Lift the bases into the actual radical powers and concatenate in increasing grade order. This produces a basis of R by elementary linear algebra. Make the same choices independently for R′, with socle generator ω′.

An isomorphism φ preserves every radical power and sends ω to λω′. If its matrix on grade i is Gᵢ, the paired matrix on grade s − i is λGᵢ^(-T). Their determinants multiply to λ^hᵢ. The matrix on the full algebra is block triangular in the filtered bases, so all off-diagonal terms have no effect on its determinant. Therefore

    det φ = ∏(i = 0,…,t) λ^hᵢ = λ^(N/2).

This proves the first identity. It does not use a graded splitting or a procedure recovering a complete isomorphism.

Over F₃ there are two cases. If N/2 is even, the determinant is always 1 in these bases. If N/2 is odd, the determinant equals the socle scale λ. A constraint on the image of one explicitly computed vector suffices in the latter case. Section 7 compiles that constraint into ordinary TI.

## 4. Even compressed socle degree

Let s = 2t. Compression implies that, for 0 ≤ i ≤ t, the multiplication map

    Symⁱ(J/J²) → Jⁱ/Jⁱ⁺¹

is an isomorphism: it is surjective because Jⁱ consists of products, and the dimensions agree. Choose a tangent basis and use the corresponding monomial bases in these grades. For the upper grades use bases dual to the lower grades, as in Section 3.

Let g be the tangent map induced by φ. Its middle-grade action is Symᵗ(g). All other grades pair, giving

    det φ = λ^A det(Symᵗ g),
    A = Σ(i = 0,…,t−1) binomial(e + i − 1, i).

Here h₀ = 1, including the paired unit and socle. The hockey-stick identity gives

    A = binomial(e + t − 1, t − 1) = α.

For every invertible e-dimensional g,

    det(Symᵗ g) = (det g)^α.

One proof extends scalars to an algebraic closure and triangularizes g. On a degree-t monomial, the diagonal action is the corresponding product of its eigenvalues. The total exponent of each individual eigenvalue across all monomials is α: count its occurrences by summing, for r from 1 to t, the monomials in which that exponent is at least r. The identity therefore holds in every characteristic, with no division by a factorial. Descent follows because both determinants are unchanged by scalar extension.

Thus

    det φ = (λ det g)^α.

If α is even, this is 1 over F₃. The case t = 2 gives the quartic identity

    det φ = (λ det g)^(e + 1).

This proof also covers filtered, non-graded algebras with the specified Hilbert function. In particular, it does not use the assertion that compressed algebras of socle degree four are canonically graded. That assertion has characteristic restrictions, with counterexamples in characteristic three. [Jelisiejew, Classifying local Artinian Gorenstein algebras](https://arxiv.org/abs/1511.08007)

## 5. Multiplication isotopies and units

Suppose p, q, r are invertible linear maps between two unital associative algebras satisfying

    p(x) q(y) = r(xy).

Put u = p(1) and v = q(1). Then r(x) = p(x)v = u q(x). Bijectivity implies that u and v are units. The map

    φ = Lᵤ⁻¹ p = Rᵥ⁻¹ q

is a unital algebra isomorphism, and

    p = Lᵤ φ,    q = Rᵥ φ,    r = Lᵤ Rᵥ φ.

Multiplicativity follows by substitution and cancellation of u and v. Conversely, every such φ and every choice of units give an isotopy. Thus ordinary multiplication-tensor isomorphism is equivalent to algebra isomorphism, including all three independent tensor maps.

In a scalar-residue local algebra, multiplication by a unit u acts on every radical grade by its scalar residue ε(u). Hence

    det Lᵤ = ε(u)^N.

When N is even over F₃, this is 1. The first determinant of an isotopy is then exactly det φ. When N is odd, multiplication by −1 permits either first sign, so the signed question is simply ordinary TI. In the contravariant tensor convention the affected determinants are inverted; over F₃ inversion fixes both nonzero determinants.

## 6. Recognition and basis calibration from raw tensors

Here is the reused recognition procedure, included to specify the input contract. If the three dimensions differ, the tensor cannot be a unital multiplication tensor. On a square format n, view it as μ: U × V → W and write M(u): V → W. Require the slice map u ↦ M(u) to be injective. Solve the linear equations

    E = {(P,Q) : Q M(u) = M(u) P for all u}.

This is a unital associative algebra under coordinatewise composition. Compute its multiplication table and its natural actions on V and W. Require dim E = n and that both natural modules are isomorphic to the left regular E-module. Constructive module isomorphism supplies frames α: E → V and β: E → W in polynomial time over the fixed field. [Brooksbank and Luks, Testing isomorphism of modules](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

In those frames, β⁻¹M(u)α commutes with the left regular action, so it is right multiplication by its value a(u) on 1. The map a: U → E is an isomorphism by injectivity and equal dimensions. Thus

    β⁻¹ μ(u, α(v)) = v a(u).

This recovers multiplication of Eᵒᵖ with explicit frames on all three original modes. Conversely, for any unital multiplication tensor, the identity slice identifies the two fixed-label adjoints as right multiplication, and both natural modules are regular. The test is therefore exact.

Check commutativity of the recovered algebra. In a finite commutative algebra over F₃ choose 3ᵏ ≥ n. The map x ↦ x^(3ᵏ) is F₃-linear and its kernel is the nilradical. Local scalar residue is exactly the condition that this kernel has codimension one. Compute its powers by span-and-multiply, and compute the socle by solving xJ = 0. All operations are polynomial in the table size. This recognizes the families in Section 1, including symmetry and compression. Binomial coefficients are only needed up to the input dimension: if a required dimension exceeds it, the test rejects immediately.

Let a_T and a_T′ be the first-mode frames from the compatible filtered algebra bases to the original raw coordinates. Both are explicitly known. Put

    η = det(a_T′) / det(a_T) ∈ {1,−1}.

For every raw transporter p, Section 5 and change of basis give, in even dimension,

    det p = η det φ.

Thus the required determinant in the filtered algebra frames is η⁻¹ = η. Ignoring this factor would give an incorrect raw-input reduction.

## 7. The actual single ordinary-TI output

After the recognition and frame computations:

- In odd dimension, output the original ordinary tensor pair.
- In the odd-socle case with N/2 even, or the even compressed case with α even, reject if η = −1; otherwise output the original ordinary pair.
- In the odd-socle case with N/2 odd, construct the algebra-isomorphism system requiring φ(ω) = ηω′.

For the last branch include, on each side, the vector spaces F and R, scalar multiplication F × F → F with its unit, algebra multiplication R × R → R with its unit, and the map F → R taking 1 to ω on the source and to ηω′ on the target. Scalar action is pinned to identity. An isomorphism of this system is exactly a unital algebra isomorphism satisfying the required socle scale. The number of spaces and maps is constant, every map has order at most three, and their coordinate tables are polynomial-size. The ordinary tensor-system compiler therefore produces one ordinary three-tensor comparison. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

Use fixed equal tensors for an immediate yes and a zero/nonzero scalar tensor pair for an immediate no. This specifies both verdict directions and a polynomial-size construction. No oracle answers, uncomputed scalars or hypothetical determinant gadgets are used.

For a total conditioned language, activate the first-determinant requirement precisely on these recognized algebra families and use ordinary TI otherwise. The construction proves that this conditioned language has ordinary TI degree: the upper reduction is above, and the lower reduction pads an arbitrary ordinary input to a nonsquare format, which disables the algebra condition while preserving ordinary equivalence. This is a newly stated restriction, not an identification of the earlier unrestricted L5 degree.

## 8. Verification, scope and attribution

The supplied control program checks 450 full determinant identities over F₃ for tangent dimensions 1 through 9. It additionally constructs nondegenerate quartic multiplication tables at tangent dimensions 3 and 4, checks all 10,744 basis associativity triples, and verifies ten complete multiplication-table isomorphisms. These are finite controls; the universal arguments are Sections 2–7.

The methods used are standard Frobenius pairings, radical filtrations, symmetric-power determinants, constructive module isomorphism and tensor-system compilation. The synthesis was found during the determinant-tier search; novelty has not been established. Related compressed-algebra literature includes [Elias and Rossi](https://arxiv.org/abs/1207.6919) and [Jelisiejew](https://arxiv.org/abs/1511.08007). Their canonical-grading results are not premises of the proofs here.

This document contains newly written exposition and an original control script. No external source code or Lean proof text is copied. It reuses the existing MathProofs normalization strategy mathematically and credits the published algorithmic dependencies above.

The unresolved general cases include arbitrary Frobenius Hilbert functions and the odd α, even-dimensional compressed case. In particular, this result does not give A ∧ A ≤ A, B ≤ A, S ≤ B or A ≤ O for unrestricted tensors. Nor is it presented as closing a published open question.
