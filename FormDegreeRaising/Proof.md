# Raising the degree of forms over an arbitrary field

Informal proof. Form equivalence here means equality of **formal homogeneous polynomials** after an invertible linear substitution over the source field. A scalar multiple is a different input and can be inequivalent. This convention matters even over finite fields.

## Exact answer for the proposed map

Grochow and Qiao ask in Appendix A, just after Proposition A.1, whether the map `f(x) -> z^(d-m) f(x)` reduces degree-`m` form equivalence to degree-`d` form equivalence whenever `m < d`. The map works exactly over the fields and degrees specified below. A different polynomial-time reduction works over every field for fixed degrees. [Grochow–Qiao, Part I, Appendix A](https://epubs.siam.org/doi/10.1137/21M1441110)

**Theorem.** Let `K` be a field, let `m >= 1` and `k >= 1`, and let `f` and `g` be degree-`m` forms in the same number of variables. Then `z^k f` and `z^k g` are linearly equivalent if and only if there are `c in K*` and `A in GL_n(K)` such that

```text
g(x) = c^k f(Ax).
```

Consequently, raw padding is a kernel reduction on all degree-`m` forms if and only if `(K*)^k` is contained in `(K*)^m`. Over `F_q` this is equivalent to `gcd(m,q-1)` dividing `k`. Over an algebraically closed field it always holds.

**Proof.** The displayed identity directly yields an equivalence by substituting `(Ax,c z)` into the padded form. Now assume the padded forms are equivalent and nonzero. Write the substitution as

```text
z^k g(x) = l(x,z)^k f(b_1(x,z),...,b_n(x,z)),
```

where the linear forms `b_1,...,b_n,l` are a basis. Let `v` be the direction with `b_i(v)=0` for every `i` and `l(v)=1`.

If `l` is not a multiple of `z`, unique factorization gives `l^k | g(x)` in `K[x,z]`. The degree in `z` of a product is the sum of the degrees, so `l` and its quotient `g_0=g/l^k` belong to `K[x]`. After canceling `l^k`, the remaining polynomial `z^k g_0` is formally invariant under translation by `t v`, since the `b_i` are invariant. In the polynomial ring in the added parameter `t`, the degree of the translated product is the sum of the degrees of its nonzero factors. Both factors therefore have degree zero in `t`. It follows that `z(v)=0` and that `g_0` is invariant along `v`. The quotient `g_0` is also invariant along the added coordinate direction `e_z`, since it belongs to `K[x]`.

The vectors `v,e_z` complement `ker(l) intersect ker(z)` because their `(l,z)` coordinates are `(1,0),(0,1)`. Swapping these two vectors and fixing that common kernel interchanges the linear forms `l,z` and leaves `g_0` unchanged. Hence it preserves `z^k g = z^k l^k g_0`. Precomposing the displayed substitution with this swap makes the substituted last coordinate equal to `z`. This argument uses polynomial identities in a formal parameter and is valid in every characteristic.

In either case the adjusted substitution sends the last coordinate to `c z`, with `c != 0`. Invertibility now implies its block on the `x` coordinates modulo `z` is some `A in GL_n(K)`. Cancel `z^k` and set `z=0` to get the desired identity. If either input is zero then the equivalence forces both to be zero, and the same conclusion holds.

If `(K*)^k` is contained in `(K*)^m`, choose `a` with `a^m=c^k` and absorb the scalar by using `aA` in place of `A`. Conversely, if this containment fails, take `c` with `c^k` outside the `m`-th powers and use the one-variable forms `x^m` and `c^k x^m`. They are inequivalent, while their padded forms are equivalent. For example, over `Q`, `x^3` and `2x^3` are inequivalent, while `z x^3` and `2 z x^3` are equivalent under `z -> 2z`. This identifies the missing normalization in the proposed proof of Proposition A.1. Preservation of the added variable's **line** allows arbitrary nonzero rescaling of that variable. The finite-field criterion follows from cyclicity of `F_q*`. ∎

As a finite check, exhaustive substitutions over `F_2` and `F_3` for all binary quadratics and padding exponents `k=1,2` found no disagreements with the displayed biconditional across 1,586 ordered input pairs. This check uses equality of formal coefficients.

## A reduction that works over every field

**Theorem.** For any fixed integers `1 <= m < d` and any field `K`, degree-`m` formal form equivalence reduces by a deterministic polynomial-time kernel reduction to degree-`d` formal form equivalence over `K`. Here polynomial time is in explicit coefficient encodings with the usual effective field arithmetic, or in field operations in the algebraic model.

1. **Encode the form in a fixed low-arity linear signature.** Let `X` have basis the formal variables and let `S_r = Sym^r(X)` for `0 <= r <= m`. Take one ambient direct sum of these spaces, with unary subspace relations for the separate summands. Add the usual multiplication on `S_0 = K`, the multiplication maps `X x S_r -> S_(r+1)` for `1 <= r < m`, and the linear map `S_0 -> S_m` sending `1` to `f`. Define each function as zero outside its indicated input blocks by means of the canonical direct-sum projections. An isomorphism fixes the scalar line pointwise because its multiplication has a unique nonzero idempotent. If it acts by `G` on `X`, the monomial multiplication maps force its action on every `S_r` to be `Sym^r(G)`. Indeed the monomial products span each next symmetric power. The last function then forces exactly the original form-equivalence equation. Conversely, every original change of variables extends by its symmetric powers and the identity on `S_0`. This construction uses no polarization, division by factorials, or roots.
2. **Compile to ordinary 3TI.** The signature is fixed when `m` is fixed, and all functions are unary or bilinear. Apply the published fixed-signature theorem (Futorny–Grochow–Sergeichuk, as stated in Grochow–Qiao Theorem 7.3). For fixed `m` the ambient dimension `sum_(r=0)^m binom(n+r-1,r)` and the explicit function tables have polynomial size. [Grochow–Qiao, Part I, Section 7.1](https://epubs.siam.org/doi/10.1137/21M1441110) · [Futorny–Grochow–Sergeichuk](https://arxiv.org/abs/1810.09219)
3. **Use the specific scalable cubic output.** Reduce 3TI to commutative unital associative algebra isomorphism via Grochow–Qiao Theorem B(4a). In characteristic two one can use alternating matrix-space isometry first, since alternating matrices are symmetric in that characteristic, and then apply their construction attaching a unit to the commutative algebra. In other characteristics use the symmetric matrix-space version. Apply Agrawal–Saxena Theorem 4.1. Its output cubic `C(y,c,v)` in equation (13) is homogeneous of degree one in the entire `y` block. Thus for any `a in K*`, the substitution `y -> a y` carries `C` to `a C`. This uses the actual output format of the published construction. [Grochow–Qiao, Part I, Theorem B](https://epubs.siam.org/doi/10.1137/21M1441110) · [Agrawal–Saxena, Theorem 4.1 and equation (13)](https://doi.org/10.1007/11672142_8)
4. **Raise the scalable cubic to the target degree.** If `d=3` use `C` itself. If `d>3` output `z^(d-3) C`. By the first theorem, a padded equivalence gives equivalence up to a nonzero scalar of the original cubics. The preceding scaling substitution absorbs that scalar. Thus padding reflects strict equivalence on these cubic outputs over every field. The only remaining case `d=2,m=1` uses raw padding, since `(K*)^1=K*`.

All reductions here compare objects with fixed layouts for each source dimension and degree. For decision input pairs of mismatched source dimensions, the output can be a fixed NO instance. The use of fixed `m,d` ensures polynomial dense output size, including the final degree-`d` coefficient table. This proves all-field existence for each fixed pair even when the direct map proposed in Appendix A fails.

For `d>=3`, the same proof also gives TI-completeness of degree-`d` formal form equivalence over every field: use Steps 1–2 with degree `d` for membership, and Steps 3–4 for hardness from ordinary 3TI. The symmetric-power encoding gives an alternative to the earlier MathProofs coset encoding for membership. The Appendix A correction concerns the raw padding map and is separate from that earlier membership result. No Lean check or historical-priority claim is made.
