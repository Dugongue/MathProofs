# A bounded-degree detector for principal determinants in arbitrary nilpotent directions

Let $k$ be a fixed finite field. Let $R$ be a finite-dimensional commutative local $k$-algebra with residue field $k$ and coefficient inclusion $k\hookrightarrow R$ splitting the residue map. Supply structure constants, the coefficient and residue maps and vector-space coordinates. Write $J$ for its maximal ideal and assume $J^e=0$. The exponent $e$ is a fixed bound; the dimension of $R$, the embedding dimension of its radical, and all tensor dimensions may vary. The proof applies to a general field as a field-operation bound under the same explicit hypotheses.

**Theorem.** Given arbitrary pairs of free three-tensors over $R$, one ordinary three-tensor isomorphism instance over $k$ can require the principal determinant of every mode transporter to take any prescribed value in $1+J$. Here the principal determinant of $g$ is
$$
                 \delta(g)=\det_R(g)/\det_k(\bar g),
$$
using the coefficient inclusion on the denominator. The reduction is deterministic with size and construction time $L^{O(e)}$ for fixed $e$, where $L$ includes the dense input and the structure constants. In particular, over every such binary-residue algebra of characteristic two, **unrestricted special-linear tensor isomorphism reduces to ordinary binary three-tensor isomorphism**. Positive ranks suffice; a zero-dimensional mode makes both tensors zero, and the remaining determinant constraints are decided by elementary diagonal scalings.

### A polynomial of degree bounded by the nilpotence length

For one mode $W=R^n$ let $V=W/JW$. Identify $R\otimes_k V$ with the free coordinate module of the displayed instance by its coordinate lifts. In $\operatorname{Hom}_k(V,W)$ take the subspace $E$ of maps $h$ whose reduction is a scalar multiple $s$ of the identity of $V$. The scalar is unique for $n>0$. In the displayed bases write $h=sI+X$, where $X$ has entries in $J$. Extending the columns $R$-linearly interprets this as a square matrix over $R$.

If $g:W\to W'$ is $R$-linear and invertible, with reduction $\bar g:V\to V'$, the induced action on $E$ is $h\mapsto gh\bar g^{-1}$. The scalar $s$ stays fixed. The slice $s=1$ is the affine space of $k$-linear splittings of the residue map. The two free coordinate identifications used to define determinants on that slice are the displayed ones at the corresponding inputs.

Let $\sigma_j(X)$ be the sum of the principal $j$-minors, with $\sigma_0=1$ and $\sigma_j=0$ for $j>n$. Each minor of size at least $e$ vanishes since it is a sum of products of at least $e$ radical entries. Mark the homogeneous $R$-valued form
$$
      P(s,X)=\sum_{j=0}^{e-1}s^{\,e-1-j}\sigma_j(X).
$$
Its degree is $e-1$, independently of $n$. In the polynomial algebra with $s$ inverted it equals $s^{e-1}\det_R(I+X/s)$. Multiplicativity now gives, in source and target coordinates,
$$
                    P'(gh\bar g^{-1})=\delta(g)\,P(h).
$$
The identity holds for formal polynomials: the radical in the coefficient polynomial algebra still has $e$-th power zero, and localization at the indeterminate $s$ is injective even over $R$. This avoids extracting a polynomial identity from agreement on points of a small finite field. Conversely, $P(1,0)=1$, so the multiplier is uniquely detected.

### Forcing precisely the designated tensor maps

Work in a system of named vector spaces over $k$ with linear maps, bilinear maps and vectors. Fix $R$ pointwise by its displayed basis and include $R\times W_i\to W_i$ in each mode; this forces $R$-linear witnesses. Include $W_i\to V_i$, which forces the quotient map on the residue. Factor the tensor-product operation through the two balanced products $W_1\otimes_R W_2$ and $(W_1\otimes_R W_2)\otimes_R W_3$ and mark the given input tensor. Each product map spans its codomain and forces the induced action. All these spaces and maps have polynomial size in the input.

For each mode include the full evaluation $\operatorname{Hom}_k(V,W)\times V\to W$ and the subspace inclusion of $E$. By nondegeneracy of evaluation, the only action on $E$ above $g,\bar g$ is the one just calculated. Include the standard duality pairing on $E^*,E$, with fixed scalar codomain, and the multiplication maps
$$
 E^*\times\operatorname{Sym}^{j-1}(E^*)\longrightarrow\operatorname{Sym}^j(E^*)
$$
through degree $e-1$, where degree one is $E^*$. Products span, so every induced polynomial action is forced. Identify $P$ with the tuple of its $k$-coordinate polynomials in the fixed basis of $R$. All constructions use formal symmetric powers. Polarizing a polynomial into its symmetric multilinear form would lose information in small characteristic and is unnecessary.

To require $\delta(g)=d\in1+J$, mark the tuple $P$ at the source and $d^{-1}P'$ at the target. The induced contragredient action on forms sends a form to its pullback by the inverse transporter. Consequently the marks agree precisely when $P'(gh\bar g^{-1})=d P(h)$. For $e=1$ the principal group is trivial; the ordinary tensor system alone suffices. At fixed $e>1$, the largest polynomial space has dimension at most $(1+n^2\dim_k J +e)^{e-1}$. Enumerating principal minors only up to size $e-1$, expanding each determinant, and doing coefficient arithmetic using the structure constants all take polynomial time for fixed $e$. The construction does not require enumerating $k^n$ or all minors of unbounded size. For a dimension-dependent precision it gives a parameter-dependent bound; no uniform polynomial exponent for arbitrary $e$ is claimed.

A basis of $R$ can, for example, be pinned by a cyclic shift operator together with its first cyclic vector. The $R$-valued tuple of forms can be stored as one marked tensor with a fixed $R$-factor; it is forced by duality and a named tensor product. The total number of distinct spaces and maps can therefore be bounded in terms of fixed $e$, even for varying $R$. The fixed-signature polynomial compiler of Futorny, Grochow and Sergeichuk turns the system into one ordinary three-tensor pair over $k$, preserving existence of a witness. When $k=\mathbb F_2$, every invertible residue matrix has determinant one and hence $\det_R(g)=\delta(g)$. [Futorny–Grochow–Sergeichuk](https://arxiv.org/abs/1810.09219)

### Application of the integral graph stabilizer

Suppose the two residue tensors are in the general-linear orbit of six-layer graph encodings. They can be given in arbitrary hidden bases. The integral graph construction provides the following more precise residue data. Over fixed $k$, one can decode each graph, compute a transporter to its model, and compute a scalar $\mu$ independent of the chosen witness and graph labeling. Whenever the decoded graphs are isomorphic and these two scalars agree, **every** residue transporter is adjustable to determinant one in every mode by a central tuple of mode scalars with product one. This follows from the character kernel and the determinant-one lifts of all graph maps in the integral graph construction. Inequality of the two scalars precludes an SL transporter. Compare only after checking agreement of the residue format and scaffold parameters.

Require $\delta(g_i)=1$ in the compiled instance and compare the residue scalars separately, rejecting on mismatch. Any accepted ordinary witness over $R$ gives an isomorphism on residue tensors, so graph isomorphism already holds. When the scalars match, lift the central scalar correction to $R$ using its coefficient field. It multiplies the full tensor by one because its three entries have product one, and it has principal determinant one in every mode. Thus it corrects the residue determinants without disturbing the principal ones or any higher-order coefficients. This gives **one ordinary TI decision for SL equivalence of arbitrary nilpotent perturbations of those residue tensors**, over any fixed finite coefficient field at fixed nilpotence bound. In particular, the graph at residue does not predetermine or restrict the higher coefficients being compared. For arbitrary residue tensors over larger fields the reduction still enforces the principal determinants exactly; residue determinants remain a separate question. [Integral graph construction and hidden-coordinate correction](Signed.md)

The earlier project compiler uses the logarithmic derivative and already handles split square-zero binary algebras and some unbounded-length multigraded families. The bounded-degree theorem applies to *all* the stated split algebras at each fixed length, including $R=\mathbb F_2[t]/(t^3)$, where $1+t^2$ is undetectable by every ordinary derivation. Here the one-dimensional transporter $1+t^2$ has principal determinant $1+t^2$ and is detected by the coefficient form. The advances have different uniformity in $e$. This is an informal proof; external priority for this particular compilation is unverified. [Prior logarithmic-derivative proof](https://github.com/Dugongue/MathProofs/blob/main/LocalDeterminantTransfers/Compiler.md)
