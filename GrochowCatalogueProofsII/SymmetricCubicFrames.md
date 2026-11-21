# GP-0154 · Symmetric cubics in a canonical trace-generated frame

**Theorem.** Let $V=\mathbb F_q^n$ with the standard bilinear dot product. Let $T$ be a uniform symmetric trilinear form, with one independent uniform coordinate for each unordered triple with repetition. There is a polynomial-time recognizable and orthogonally invariant set of sources of density $1-q^{-\Omega(n)}$, with absolute constants, on which diagonal orthogonal equivalence against every target is decidable in deterministic polynomial bit time. The algorithm gives the unique transporter on yes-instances. It applies in characteristic two to symmetric trilinear arrays under the bilinear dot-product group. It also applies to uniform homogeneous cubic forms through polarization when the characteristic is greater than three.

Write $\langle-,-\rangle$ for the dot product. Define the canonical bilinear product and trace vector by
$$
\langle x *_T y,z\rangle=T(x,y,z),\qquad
\langle \tau_T,z\rangle=\sum_i T(e_i,e_i,z).
$$
The second definition is independent of the orthonormal coordinates because the inverse form tensor is invariant. Both operations are covariant under the diagonal orthogonal action. Let $W_T$ be the vector space generated from $\tau_T$ by this bilinear product. Accept if $W_T=V$. This can be tested by starting with the trace vector and repeatedly appending an independent product of two current basis vectors, stopping as soon as their products are all in the span. At most $n$ append operations are needed and the span at termination is exactly $W_T$. When accepting, this procedure gives a covariant ordered basis by choosing the first eligible pair in the previously fixed order of the constructed vectors. A genuine transporter must carry this basis to the target's basis. Compute both bases, test the candidate map for orthogonality and test the tensor identity. These tests are sound for arbitrary targets, and an actual transporter cannot be missed. Covariance also proves uniqueness.

We prove the density in the actual symmetric coefficient space. Regard a symmetric trilinear form as a linear functional on $\operatorname{Sym}^3(V)$, with its monomial basis. This description and the independent sampling convention are valid in all characteristics. Fix a proper $r$-dimensional subspace $W\neq0$ and put $s=\dim(W\cap W^\perp)$. Closure under the product is precisely the vanishing of $T$ on $\operatorname{Sym}^2(W)W^\perp$. Choose a basis common to $W$ and $W^\perp$, beginning with $W\cap W^\perp$ and then separate bases of complements. Products of a quadratic basis monomial of $W$ and a linear basis vector of $W^\perp$ give distinct cubic monomials except that there are at most three choices of the distinguished linear factor. In particular,
$$
\dim(\operatorname{Sym}^2(W)W^\perp)
\ge \frac{1}{3}\binom{r+1}{2}(n-r).
$$
Using only the $n-r-s$ basis vectors of $W^\perp$ outside $W$ gives the additional bound $\binom{r+1}{2}(n-r-s)\ge\binom{r+1}{2}(n-2r)$.

The number of $r$-spaces is at most an absolute constant times $q^{r(n-r)}$ by the Gaussian binomial formula. For $r\ge6$ the first bound leaves an exponent saving $r(r-5)(n-r)/6$, at least $(n-1)/6$ whenever $r<n$. For $2\le r\le5$, the second bound leaves an exponent saving
$$
\bigl(\tbinom{r+1}{2}-r\bigr)n-\bigl(2\tbinom{r+1}{2}-r\bigr)r ,
$$
which is at least $n-O(1)$. Summing those probabilities over all $r$ gives $q^{-\Omega(n)}$.

On a line $W=Fu$, the product condition vanishes on $u^2W^\perp$, of dimension $n-1$. Containment $\tau_T\in W$ independently vanishes on $gW^\perp$, where $g=\sum_i e_i^2\in\operatorname{Sym}^2(V)$. If $u\nmid g$, then these two spaces meet only at zero: an equality $u^2\ell=g\ell'$ would force $u^2\mid\ell'$ by unique factorization, impossible for nonzero linear $\ell'$. Thus a specified such line has probability $q^{-2(n-1)}$ of satisfying both constraints. In odd characteristic and dimension at least three, $g$ has rank $n$, so it has no linear factor since a product of linear forms has rank at most two. In characteristic two $g=(\sum_i e_i)^2$, so there is exactly one exceptional line to control by the product constraints alone. This costs $q^{-(n-1)}$. Finally $\tau_T=0$ has probability $q^{-n}$, since multiplication by nonzero $g$ injects $V$ into $\operatorname{Sym}^3(V)$. If the greedy procedure fails and the trace is nonzero, its generated subspace is one of the proper nonzero spaces counted above. The sum of the probabilities proves the result uniformly in the field.

This proof uses an intrinsic ordered frame from the original covariant operations. It does not assume independent flattening or Gram statistics for a symmetric source. [Related orthogonal tensor problem](https://arxiv.org/html/2604.00591v2) · [Lean-checked P18 for unrestricted fields and tensors](https://github.com/Dugongue/MathProofs/tree/ef3248c44a28fcc2e97f90392942083b33dce716/Problem18)
