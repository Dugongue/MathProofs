# Reversible LCD normalization and monomial code canonization

## GP-0314

Over any explicitly represented finite field $F$ of order greater than three, a linear code can be converted to a monomially equivalent Euclidean LCD code in deterministic polynomial bit time, retaining a reversible monomial transporter. Computing an orbit-constant LCD representative with reversible transport is polynomial-time equivalent to ordinary constructive monomial code canonization. The literal condition $F(gC)=gF(C)$ for a choice of representative in the monomial orbit is impossible on every orbit containing a non-LCD code.

### Constructing the transporter

Write a full-row-rank generator, after a recorded coordinate permutation and row operations, as $[I_k\mid A]$. Row operations change only the displayed basis, not the code. Scale information-set coordinate $i$ by $d_i\ne0$. The Gram matrix of the new generator is
$$
AA^{\mathsf T}+\operatorname{diag}(d_1^2,\ldots,d_k^2).
$$
Choose two field elements $u_0,u_1\in F^\times$ with distinct squares. They exist since the square-map fibers in $F^\times$ have size at most two, and a constant number of distinct explicitly encoded field values suffice to find them. Having set $d_1,\ldots,d_{i-1}$, require the leading $(i-1)$-by-$(i-1)$ principal determinant to be nonzero. The leading $i$-by-$i$ determinant is affine in $d_i^2$ with that nonzero determinant as coefficient. At least one of the two candidate scales keeps it nonzero. Start with the empty determinant one and repeat. The final Gram is invertible. A linear code with a full-rank generator $M$ is Euclidean LCD exactly when $MM^{\mathsf T}$ is invertible, since the kernel of its Gram parametrizes the intersection with the dual. All determinants and inverses of nonzero scales take polynomial bit time. This supplies the desired normalization and its inverse. [Existence of monomial-equivalent LCD codes](https://arxiv.org/abs/1703.04346)

Choose the row reduction, information-set order, scale order, and final row-reduced output deterministically. If a canonical orbit representative and a transporter to it are available, apply the deterministic normalization to that representative and compose the recorded transporters. Equal orbits then get exactly the same normalized code. Conversely an orbit-constant LCD representative in the original orbit is already a valid canonical representative for ordinary monomial equivalence, and its transporter is the one required for constructive canonization. This proves the equivalence, with unchanged code length and field.

### Two transport requirements

Suppose a representative-choice rule $N$ sends every code to its monomial orbit and satisfies literal equivariance under the original monomial action. Fix $C$. Since $N(C)$ is in the orbit of $C$, its own monomial orbit is that same orbit. Equivariance therefore makes the range of $N$ on that orbit the entire orbit. If one member is non-LCD, the range cannot consist of LCD codes. Such examples exist in every characteristic $p$: the span of the all-ones word of length $p$ is not LCD.

If the desired requirement instead means that every input transporter induces an output transporter compatibly with composition, the deterministic normalization above has it without a canonization oracle. Write $D_C$ for the recorded transport from $C$ to its normalization. The map induced on a transporter $g:C\to C'$ is $D_{C'}gD_C^{-1}$. This preserves identity and composition and is reversible by the inverse recorded transports. The algorithm consequently supports comparing normalized inputs under the transported monomial action. Orbit-constant output remains exactly the separate canonization question.

This Gram calculation supplies an efficient way to produce LCD inputs for the earlier witness-preserving reductions, while retaining the original field and coordinate count. [Earlier monomial witness comparison](https://github.com/Dugongue/MathProofs/blob/f1a463ce1a77aa494b7d33b81a4cbaac5dcb708b/GrochowCatalogueProofsII/CodeEquivalenceAndOracle.md)
