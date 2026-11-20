# Comparing the two worlds through relative determinant norms

Let $F$ be a fixed finite field, and write $H(F)$ for the same-field deterministic many-one collapse. For an explicitly represented extension $K/F$, define the norm-one comparison to require a $K$-linear transporter with
$$
N_{K/F}(\det_K g_i)=1
$$
on each of three modes. This is a constraint in the base field on the determinant. Allow the representation of $K$ to vary in the uniform problem.

**Theorem.** If $H(F)$ holds, the norm-one comparisons over all explicitly represented finite extensions $K/F$ have one uniform deterministic polynomial-time many-one reduction to ordinary TI over $F$. For any one fixed extension of degree $r$ with $\gcd(r,|F^\times|)=1$, the existence of an ordinary many-one reduction for its norm-one problem is equivalent to $H(F)$. Here the ordinary target may be over $F$ or over $K$.

Ordinary TI over $K$ always reduces to the norm-one comparison over $K$ by adding unused lines, which can repair the full $K$ determinants. Restriction to the intrinsic supports gives reflection. Thus a failure of the reverse norm reduction gives a strict comparison of the degrees.

In particular if $H(\mathbb F_3)$ fails, norm-one TI stays outside ordinary TI over every fixed extension of **odd** degree, and determinant-one TI stays outside ordinary TI over every fixed extension of **any** degree, by [finite extension reflection](CubeZeroAndExtensions.md). The norm-only conclusion for even extension degree is a separate question.

## Uniform direction using the cube-zero compiler

Suppose a bimap is given over $K$ in the indicated format. Regard its three roles as $F$-spaces. Keep the bimap and add a linear endomorphism on each role, given by multiplication by a specified generator $\alpha$ for $K/F$. The maps intertwining those operators are exactly $K$-linear maps. Indeed they intertwine multiplication by all polynomials in $\alpha$, which range over $K$.

The [symmetric-bimap compiler](CubeZeroAndExtensions.md#2-put-the-system-inside-a-symmetric-bimap) accepts this fixed-signature system: it has one bilinear constraint on a pair of roles and a fixed list of linear constraints. Run that compiler over $F$ with the chosen three determinant weights. Its output is a scalar-residue commutative local $F$-algebra with cube-zero radical and trivial unit determinant images. The exact possible determinants of algebra isomorphisms are the weighted products of the determinants of the three underlying $F$-linear maps. A determinant of an underlying $F$-linear map equals the field norm of its determinant over $K$. For instance, after extending $F$ to its algebraic closure the representation of $K$ is the direct sum of its distinct embeddings. The determinant is the product of the conjugate determinants under those embeddings, which is the field norm.

Thus each weighted character test reduces to one special-linear $F$-TI comparison on the multiplication tensors. The number of auxiliary roles and all field data of that compiler depend only on $F$. Dimensions of the three original roles over $F$ multiply by $[K:F]$, and the multiplication operators by $\alpha$ have explicit polynomial-size matrices. Consequently the construction is uniform in the extension degree and polynomial in the written bit length. It does not use symmetric powers of growing degree for the variable extension.

The possible norm triples of the original pair form an empty set or a coset in the threefold product of $F^\times$. Checking its characters for the identity detects exactly the norm-one target. There are $|F^\times|^3$ characters, a constant. After applying $H(F)$ to each compiled comparison, join the ordinary outcomes with a fixed positive conjunction. This gives the asserted uniform ordinary reduction.

## Recovering the base-field hypothesis from one norm problem

Now fix $K/F$. For each determinant character of a bimap transporter over $F$, use [the Frobenius-entry compiler](CubeZeroAndExtensions.md#1-a-typed-system-for-prescribed-coefficients) over $K$. Its cube-zero $K$-algebras have the exact determinant set prescribed by that character, lying in $F^\times\subseteq K^\times$. Its multiplication tensor transporters have that same determinant in all three modes, by the triviality of the left and right unit determinant images. On $d\in F^\times$ the relative norm is $d^r$. If the degree is coprime to $|F^\times|$, norm one is equivalent to $d=1$. Therefore the assumed norm-one decision reduction over this single $K$ tests each character of the base tensor comparison. The ordinary representations over the two fixed fields are themselves many-one equivalent: restriction of scalars with marked multiplication operators gives ordinary TI over $K$ to ordinary TI over $F$, and the Frobenius-entry compiler with the zero character gives the opposite direction. A fixed determinant-character conjunction now proves $H(F)$.

The proof of the converse uses coprimality exactly at the step $d^r=1\Rightarrow d=1$. For even degree over the field of three elements that step destroys the distinction between the two base signs. This is a limitation of this particular transfer, separate from the unrestricted equality or inequality of the norm-one decision degrees for even degree.

The uniform norm result and the coprime-degree equivalence also give a direct cross-check on the earlier extension-norm section of the equality catalogue. They work by keeping scalar multiplication operators in a typed system and then using the cube-zero compiler, rather than by relying on the earlier projective four-line marker. The proof is informal.
