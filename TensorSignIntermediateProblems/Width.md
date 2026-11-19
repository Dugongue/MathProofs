# Determinant width between the sign tiers of tensor isomorphism

Use the field F₃ and write Pₖ for ordinary three-tensor isomorphism with determinant +1 on its first k modes, for 0 ≤ k ≤ 3. In particular P₀ is TI and P₃ is SL-TI. All reductions below are deterministic polynomial many-one reductions unless a different cost model is specified.

## The comparison problem

A typed tensor system has labelled coordinate spaces and an ordered list of tensors of order at most three, with each slot labelled by a space or its dual. In particular a vector, a linear map and a bilinear map are allowed. A transporter is a simultaneous family of invertible linear maps preserving the displayed data. The number of spaces is arbitrary. Use explicit dense encodings with the space dimensions also given in unary, so the bit length L of an input pair bounds the dimensions and the number of roles. These encodings are polynomially interconvertible with ordinary effective explicit encodings for every construction used here.

For p = 0, 1, 2, require determinant +1 on p designated unrestricted roles and on one further designated role V. Define W(p,a) to be this comparison with the input requirement

    dim V ≤ ceil(log₂(2+L))^a.

Only positive integer a is used. Pairs with incompatible signatures, malformed data or excessive dim V are no instances. The problem receives no group generators or transporters. Width refers to the dimension of a named role of the raw input, before any reduction.

For each p = 0, 1, 2, there are reductions

    Pₚ ≤ W(p,2) ≤ W(p,3) ≤ W(p,4) ≤ Pₚ₊₁.

To place Pₚ below the width comparisons, use the tensor as one system relation and add a separate one-dimensional role with a fixed nonzero vector. The role map must be the identity. The p input determinants belong to the existing roles. For a ≤ b, check the a bound and otherwise use the same pair for W(p,b); output a fixed no instance if the check fails. Finally use the retained-sign compiler on the p+1 designated roles. This compiler preserves their joint sign profile, including empty transport profiles, in the corresponding physical tensor modes. [Retained-sign compiler](https://github.com/Dugongue/MathProofs/blob/main/TensorSignChain/RetainedSigns.md)

## An exact ordinary lock for a short role

Let w = dim V. For i from 2 through w, add the exterior-power spaces ΛⁱV and the wedge bilinear maps V × Λⁱ⁻¹V → ΛⁱV, where Λ¹V is V. Mark the ordered coordinate top wedge by a fixed nonzero vector on ΛʷV, in both objects. In dimension one mark the coordinate vector on V. In dimension zero no lock is needed.

Every original transporter g on V extends to this diagram before the final mark by using Λⁱg at degree i. Conversely the wedge products span each ΛⁱV, so preservation of the wedge maps forces these same actions successively. The top vector is preserved exactly when det g = +1. The lock leaves every other original witness and designated sign unchanged. All marks have order at most three and their dense tables take at most poly(L)·2^O(w) time and space to write.

Consequently W(p,1) ≡ Pₚ via this diagram and the compiler with p retained signs. The same conclusion holds with any width O(log L). At the other end, a width bound at least L^ε for some fixed ε>0 eventually gives exactly Pₚ₊₁. Encode Pₚ₊₁ as a typed system and add an untested auxiliary space with an identically zero bilinear form on it. A polynomial-size dense zero table makes the resulting input length L at least the 1/ε power of the original designated dimension (and large enough for the eventual bound to apply). The extra system imposes no new restriction on the original transporters.

## Strictness for compilers that preserve every valid witness

Here is a size distinction that applies even to pair-dependent preprocessing. In this section an exact compiler to typed systems must enable the original mode maps to be read on designated invariant subquotients of the output. Every valid source transporter must lift, and every accepted output transporter must project to a valid source transporter. The output tensor order is bounded by a fixed constant. The model permits additional output automorphisms that are invisible on the original spaces.

We use the earlier exact-lift theorem with k = p+1 independent signs and j = p retained signs. Its explicit tensor Tₙ has three modes of dimension 3n+2 and n ranges over sufficiently large even integers. In its stabilizer are k independent GLₙ factors, each contributing one of the k physical signs. Retaining all corresponding SLₙ witnesses with at most j output tests requires total output coordinate dimension exp(Ω(n)) at fixed tensor order. Equivalently, systems of total dimension exp(o(n)) cannot do this. The theorem permits recovery on invariant subquotients and arbitrary lift kernels. [Exact-lift theorem](https://github.com/Dugongue/MathProofs/blob/main/TensorSignChain/ExactLifts.md)

Take exponents a>b≥1. Use Tₙ as the principal mark of a width-a input self-pair. Choose one of the k designated roles as V. Add an auxiliary role of dimension

    Kₙ = 2^ceil((3n+2)^(1/a))

with a dense Kₙ×Kₙ zero bilinear form. This gives an input bit length with log₂ L = Θ(n^(1/a)), and its width is admissible because L≥Kₙ. All principal tensor transporters extend by the identity on the auxiliary role. Suppose a polynomial-size exact compiler outputs a width-b pair of length at most L^C. Lock its width-b role by the exterior diagram. The new system has only p live signs and has length bounded by

    L^O(1) · 2^O((log L)^b) = exp(o(n)).

Its order is still bounded. Exterior locking is exact, so the composition preserves all valid input witnesses and excludes invalid ones on the original three modes. In particular it retains the independent SLₙ factors on the self-pair. This contradicts the cited theorem. When a>1 the same argument rules out a polynomial-size exact compiler directly to Pₚ by omitting the exterior-lock postprocessing.

The reverse direction Pₚ₊₁ → W(p,a) in the exact model is also ruled out, for any fixed a. Start from the unpadded Tₙ, of polynomial length in n. The alleged output has width O((log n)^a). Locking it gives a system with only p live signs and length exp(O((log n)^a + log n)) = exp(o(n)). The same contradiction applies.

Thus every reverse arrow in each displayed chain is ruled out for the stated witness-preserving model. For example, width log⁴ L cannot be compressed to log³ L in this model despite preserving the same number of explicitly designated signs. The proof does not forbid reductions that change the witness search, certify just one good witness, inspect raw coefficients in another way, or use output tensors of unbounded order. It does not show any of the four endpoint problems have different unrestricted many-one degrees.

These proofs are informal. The published motivation for comparing the two endpoints is [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5).
