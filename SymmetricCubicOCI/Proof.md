# A single fully symmetric cubic is TOCI-complete under the complex orthogonal group

Informal proof. November 14, 2026.

For every fixed integer `d >= 3`, the orbit closure intersection problem for `Sym^d(W)` under the standard complex orthogonal group `O(W)` is TOCI-complete. Hardness holds under efficient algebraic reductions in the sense of Lysikov–Walter. For `d <= 2`, the problem has a deterministic polynomial-time algorithm over the usual exact encodings of rational or fixed number field coefficients. All orbit closures are taken over the complex numbers.

This supplies a fully symmetric, single-slot example for [Lysikov–Walter, Question I.14](https://arxiv.org/html/2411.04639v2#S1.SS4). The project's earlier example, `Sym²(W) ⊗ Sym²(W*)` under `GL(W)`, has separate symmetries within its primal and dual slots. Here the input is a single homogeneous cubic, or higher-degree form, symmetric across every factor. The group in this result is `O(W)`.

## The closed marker principle

Let a complex algebraic group `G` act on an affine variety `Z`, and let `m : Z -> M` be an equivariant regular map. Suppose a marker `m0` has closed orbit, and write `H` for its stabilizer. For any `z,z'` in the fiber over `m0`, their `G`-orbit closures intersect if and only if their `H`-orbit closures intersect in that fiber.

For the forward direction, take a common point of the two closures and translate it by one element of `G` so its marker is `m0`. The marker lies in the orbit by closedness. For either input, there exists a sequence `g_j z` converging to the common point, since Euclidean and Zariski closures of complex algebraic orbits agree. The orbit map of a complex algebraic group onto an orbit has local analytic sections, by the submersion theorem for the smooth homogeneous orbit. Choose a section through the identity. If `s_j` is the section at the marker of `g_j z`, then `s_j` tends to the identity and `s_j^(-1) g_j` belongs to `H`. The transformed sequence still tends to the common point. Apply this to each input. The reverse direction is immediate from `H <= G`. This argument also applies within a closed invariant fiber after fixing an earlier marker. An injective equivariant linear data mapping then reflects closure intersection, since its image is closed and it has a linear inverse on that image. [Lysikov–Walter, Definition II.4 and Corollary III.8](https://arxiv.org/html/2411.04639v2).

## Encoding two cubic tensors and recovering their actions

By [Lysikov–Walter, Theorem V.21](https://arxiv.org/html/2411.04639v2#S5.SS2), the orthogonal action on a pair of labelled tensors in `E^⊗3` supplies a TOCI-complete source. All forms below are the standard dot products over C. Let `U` be the orthogonal direct sum of six copies `E_1,...,E_6` of `E`. In the symmetric algebra of `U`, the multidegree with one occurrence from each of `E_1,E_2,E_3` is canonically `E_1 ⊗ E_2 ⊗ E_3`. Store the first source tensor there by symmetric multiplication of the three different colors. Store the second in the analogous component for `E_4,E_5,E_6`. This data map to `Sym³(U)` is injective, since the two multidegrees are distinct, and equivariant under the diagonal `O(E)` action.

Use two tags in `Sym²(U)`, identified with self-adjoint endomorphisms using the dot product.

1. The first tag `A` is diagonal by color, with eigenvalue `i` on `E_i`. Its orthogonal orbit is closed. It is described by self-adjointness, the square-free polynomial equation `product_{i=1}^6 (A-iI)=0`, and equations imposing the ranks of all six polynomial spectral projections via their traces. These projections have distinct eigenspaces that are mutually orthogonal and nondegenerate. Choosing orthonormal bases in these eigenspaces proves transitivity. Its stabilizer is `K = product_i O(E_i)`.
2. The second tag `B` has only the off-diagonal blocks connecting `E_1` to each `E_i` for `i>1`, with an identity identification in each direction. Its orbit under `K` is closed. Indeed the block `E_1 -> E_i` changes to `g_i g_1^(-1)` in the chosen identifications. These five blocks range independently over orthogonal matrices, each cut out by `M^T M=I`. The opposite blocks are transposes and all other blocks are zero. The stabilizer of `B` within `K` is precisely diagonal `O(E)`.

Apply the marker principle first to `A`, then to `B`. This gives an affine reduction to the action of `O(U)` on `Sym³(U) ⊕ Sym²(U) ⊕ Sym²(U)`.

## Packing the two quadratic slots into one

Let `Y=U ⊕ C l_1 ⊕ C l_2`, an orthogonal sum with two unit vectors. Given general data `(x,A,B)` in the representation just constructed, encode it as a cubic and one new quadratic:

```
c = x + l_1 A + l_2 B + l_1^3 + l_2^3,
D = a self-adjoint operator taking distinct eigenvalues 1,2,3 on U,C l_1,C l_2.
```

These are symmetric-algebra products in the displayed factors. The quadratic `D` has closed orbit, by the square-free spectral argument from the previous section, and its stabilizer is `O(U) × {±1}²`. In this fiber the two pure line cubic coefficients are equivariant coordinate projections. The orbit of their value `(1,1)` under the line signs is the closed set `{±1}²`. Its stabilizer forces both signs to be `+1`. The remaining data lie in three distinct multidegrees `Sym³(U)`, `l_1 Sym²(U)`, and `l_2 Sym²(U)`, carrying exactly the original `O(U)` action. Two applications of the marker principle finish a reduction to `Sym³(Y) ⊕ Sym²(Y)` with group `O(Y)`.

## Packing everything into one symmetric cubic

Let `W=Y ⊕ C e` with `e` of norm one. Write `N=dim W`, `q` for the standard quadratic tensor in `Sym²(W)`, and `Delta` for the orthogonal Laplacian on the symmetric algebra in an orthonormal basis. For a degree-one polynomial `v`,

```
Delta(q v)=2(N+2)v.
```

Thus `Sym³(W)=q W ⊕ ker Delta` equivariantly, with projection `pi` onto `ker Delta` given by subtracting `q Delta(c)/(2(N+2))` from `c`. Use the cubic encoding of `(x,A) ∈ Sym³(Y) ⊕ Sym²(Y)`

```
q e + pi(x + e A).
```

The marker `q e` is recovered by equivariant projection to `q W`, and it has closed orbit because `O(W) e` is the unit quadric. Its stabilizer is `O(Y)`. The projection `pi` is injective on `Sym³(Y) ⊕ e Sym²(Y)`: writing `q=q_Y+e²` and `v=v_Y+c e`, a vector `qv` with only `e`-degrees zero and one must have `c=0` from its `e³` coefficient and `v_Y=0` from its `e²` coefficient. The data map is `O(Y)`-equivariant, so the marker principle proves correctness through all orbit degenerations.

Composing the reductions yields an affine map into a single `Sym³(W)` from the published complete two-cubic source. All constructions are over Q and have polynomial evaluation cost, including the divisions by `2(N+2)`. The dimension of `W` is `6 dim E + 3`. Membership in TOCI follows by the injective orthogonal-equivariant inclusion `Sym³(W) -> W^⊗3` in characteristic zero and the explicit orthogonal-to-general-linear reduction of [Lysikov–Walter, Theorem V.18](https://arxiv.org/html/2411.04639v2#S5.SS2).

## Higher and lower degrees

For the even-degree starting case, let `Y` now denote the cubic source space and write `W=Y ⊕ C e`, `q=q_Y+e²`. For `z ∈ Sym²(W)`,

```
Delta(q z)=2(N+4)z+q Delta(z).
```

The map `z -> Delta(qz)` on `Sym²(W)` is invertible: its eigenvalue is `2(N+4)` on harmonic quadratics and `4(N+2)` on the line spanned by `q`. Hence `q Sym²(W)` is an equivariant direct complement to the harmonic quartics. Let `pi_4` be projection onto the latter. Encode the cubic `x ∈ Sym³(Y)` as

```
q e² + pi_4(e x).
```

The recovered marker `q e²` has closed orbit, because `e²` corresponds to a rank-one self-adjoint projection, with closed orbit as above. Its stabilizer is `O(Y) × {±1}`. The projection `pi_4` is injective on `e Sym³(Y)`: if `qz` has only `e`-degree one, write `z=z_0+e z_1+e² z_2`. The coefficients of `e⁴`, `e³`, and `e²` successively force `z_2=z_1=z_0=0`. The line sign acts on the cubic payload by a sign, which can be absorbed into the central element `-I_Y` of `O(Y)` since the payload is cubic. Every action of `O(Y)` on the source payload also appears with the line sign `+1`. The marker principle proves that this map is an efficient algebraic reduction from symmetric cubics to symmetric quartics. Membership for quartics follows by the same inclusion as for cubics.

For either parity, multiplication by `q` is an injective equivariant linear map from `Sym^d(W)` to `Sym^(d+2)(W)`, so this proves completeness at each fixed degree at least three.

At degree zero compare scalars. At degree one compare the quadratic norm, which generates the one-vector polynomial invariants. At degree two identify the tensor with a self-adjoint operator. Orthogonal contraction invariants of one such operator are products of traces of its powers, because contraction diagrams with quadratic vertices are cycles. The characteristic polynomial determines these traces and is determined by them via Newton identities in characteristic zero. Thus compute and compare characteristic polynomials. This uses polynomial bit time under the stated exact encodings. [Lysikov–Walter, Theorem II.7, Theorem IV.23, and Corollary IV.29 on the orthogonal invariant tensors](https://arxiv.org/html/2411.04639v2).

## Attribution and status

The source problem and the complexity model are due to Lysikov and Walter. The closed marker argument is a standard property of homogeneous fibrations and was used in earlier MathProofs orbit-closure constructions. The present reduction combines it with symmetric multidegrees and the Laplacian splitting to obtain a single fully symmetric cubic. Exact rational controls on monomial bases verified both Laplacian formulas, harmonicity of the constructed projections, and full rank of the projected data in each whole-space dimension from 2 through 6. The proof is informal and makes no publication-priority claim.
