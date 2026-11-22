# Counting determinant-one orbits of multiplication tensors

Let $A$ be a nonzero finite étale algebra over $\mathbb F_q$. Regard its multiplication as a bilinear map to $A$, with invertible changes of basis on both inputs and on the output. Its ordinary orbit splits into exactly
$$
\begin{cases}
(q-1)/2,& q\text{ odd and some field-factor degree is even or repeated},\\
q-1,&\text{otherwise}
\end{cases}
$$
orbits under determinant-one changes on all three legs.

For example, over $\mathbb F_7$ the degree profile $(1,3)$ gives six determinant-one orbits inside its ordinary orbit. The degree profiles $(4)$ and $(1,1,1,1)$ each give three. The first profile has distinct odd degrees, the second has an even degree, and the third repeats a degree.

More generally, let $A$ be any nonzero finite-dimensional unital associative algebra over $\mathbb F_q$. Write $D_L$ and $D_R$ for the determinant images of the left and right multiplication operators of units, and write $D_{\mathrm{aut}}$ for the determinant image of algebra automorphisms. The number of determinant-one orbits inside the ordinary orbit of its multiplication is
$$
\frac{(q-1)^3}{|D_L|\,|D_R|\,|D_{\mathrm{aut}}|}.
$$
This statement follows from the same stabilizer proof. In the triple $(\ell\delta,r\delta,\ell r\delta)$ one recovers $\delta$ by taking the ratio of the product of the first two entries to the third, then recovers $\ell$ and $r$ by division. Thus the number of distinct determinant triples is exactly $|D_L|\,|D_R|\,|D_{\mathrm{aut}}|$.

## Proof

On the product group of linear changes $(X,Y,Z)$, take the three determinants. This surjects onto $(\mathbb F_q^\times)^3$ since $A$ has positive dimension. The kernel is the product of the three special linear groups. The determinant-one orbits in an ordinary orbit are therefore indexed by the cosets of the determinant image of its stabilizer. Indeed the ordinary orbit is the space of right cosets of the stabilizer, and the determinant map identifies the orbits of the normal kernel on that space with cosets of the stabilizer's image.

The multiplication stabilizer consists of the triples satisfying $Z(xy)=X(x)Y(y)$. The associative unital normal form writes these as $X(x)=a\sigma(x)$, $Y(y)=\sigma(y)b$ and $Z(z)=a\sigma(z)b$, where $a,b$ are units and $\sigma$ is an algebra automorphism. Set $\ell=\det L_a$, $r=\det R_b$ and $\delta=\det\sigma$. Their determinant triple is $(\ell\delta,r\delta,\ell r\delta)$, so the ratio $\det X\det Y/\det Z$ is $\delta$. The Lean source gives this determinant accounting for arbitrary finite-dimensional associative unital algebras over a field. [Determinant fibers](C.lean)

Each multiplication determinant on $A$ is a product of multiplicative field norms. The degree-$d$ field norm is the power map $x\mapsto x^{(q^d-1)/(q-1)}$ from the cyclic group of order $q^d-1$. Its image has order $q-1$, so each of $\ell$ and $r$ independently ranges over all of $\mathbb F_q^\times$. Consequently the determinant image of the stabilizer is the full preimage of $\det\operatorname{Aut}_{\mathbb F_q}(A)$ under the ratio homomorphism. It remains to compute the index of that subgroup of $\mathbb F_q^\times$.

Over an algebraic closure, algebra automorphisms of the split product just permute its primitive idempotents, so their determinants are the signs of the induced permutations. Descent requires those permutations to commute with Frobenius. The degree-$d$ field factors are the length-$d$ Frobenius cycles. A rotation on a single even cycle is odd. Exchanging two odd cycles of the same length is also odd, as it transposes the paired positions. These operations cover every case where an even degree or a repeat occurs. If the degrees are distinct and odd, commuting permutations can only rotate each odd cycle and all such permutations are even. In characteristic two both signs represent the same scalar. Thus the determinant subgroup has the asserted index. [Finite étale schemes and Galois sets](https://stacks.math.columbia.edu/tag/04JI)

This written deduction combines the determinant fibers of the multiplication tensor with the Frobenius cycle model. The orbit-count statement itself is outside the 200 Lean targets.

## Truncated polynomial algebras

For $A=\mathbb F_q[t]/(t^m)$ with $m\ge1$, the same ordinary orbit contains exactly
$$
\gcd(m,q-1)^2\gcd\left(\binom m2,q-1\right)
$$
determinant-one orbits. In the basis $1,t,\ldots,t^{m-1}$, multiplication by a unit of constant term $a$ is triangular with constant diagonal $a$. Its determinant is $a^m$, and every nonzero $a$ is possible. The algebra is commutative, so the left and right images agree. When $m\ge2$, any algebra automorphism sends $t$ to $b t$ plus higher terms with $b\ne0$, because it must preserve the maximal ideal and induce an automorphism on its quotient by its square. Conversely, such a substitution is a homomorphism with invertible triangular matrix whose diagonal entries are $1,b,\ldots,b^{m-1}$. Thus its determinant is $b^{\binom m2}$ and every nonzero $b$ occurs. For $m=1$ the automorphism group is trivial, with determinant given by the same zero exponent. Index computations in the cyclic group of order $q-1$ give the displayed formula.

For instance $\mathbb F_7[t]/(t^4)$ gives 24 determinant-one orbits, and the dual numbers give four for any odd $q$. These counts are written applications of the kernel-checked determinant-fiber result.
