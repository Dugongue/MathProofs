# Sampling tensors with no finite-field singular tuple

Narayanan's *Strong Keys for Tensor Isomorphism Cryptography* asks for a polynomial-time sampler for nondegenerate interior-format tensors. The definition in equation (2.2) quantifies over nonzero vectors over the supplied finite field. The same paper subsequently uses the geometric hyperdeterminant, whose zero criterion instead quantifies over the algebraic closure. The theorem below answers the question with the quantifiers in (2.2), in every format. It also gives a density estimate for uniform samples in most interior formats. The geometric sampling question has a separate scope. [Narayanan, MFCS 2025, §§1 and 2](https://drops.dagstuhl.de/storage/00lipics/lipics-vol345-mfcs2025/html/LIPIcs.MFCS.2025.78/LIPIcs.MFCS.2025.78.html)

## A zero-error sampler

**Theorem.** For any explicitly represented finite field $F=\mathbb F_q$ and positive format $n_1\times\cdots\times n_r$, $r\ge2$, one can sample a tensor with no singular tuple over $F$ in expected bit time polynomial in the encoded format length, its dense output size, and $\log q$. Every sample satisfies the guarantee. In bounded characteristic, one can also construct such a tensor deterministically in polynomial bit time.

Let $m=\max_j n_j$, let $s$ attain the maximum, and construct the field $K=\mathbb F_{q^m}$ as a degree-$m$ extension of $F$. In mode $s$ take an $F$-linear isomorphism $E_s:F^m\to K$. In every other mode choose an $F$-linear injection $E_j:F^{n_j}\to K$. Choose any nonzero $F$-linear functional $\lambda:K\to F$. Output the dense coefficients of

$$
 A(x_1,\ldots,x_r)=\lambda\!\left(\prod_{j=1}^r E_j(x_j)\right).
$$

For any tuple of nonzero $F$-vectors, the product $u=\prod_{j\ne s}E_j(x_j)$ is nonzero in the field $K$. Multiplication by $u$ is bijective. Thus the contraction $v\mapsto\lambda(uE_s(v))$ in mode $s$ is a nonzero functional. A singular tuple would make every contraction vanish. This argument allows unequal dimensions and formats of arbitrary order.

For $m\ge2$, construct $K$ by sampling uniformly random monic degree-$m$ polynomials and testing irreducibility. The number of elements of exact degree $m$ in $\mathbb F_{q^m}$ is at least $q^m-\sum_{d=1}^{\lfloor m/2\rfloor}q^d\ge q^m/2$. Each monic irreducible accounts for exactly $m$ of these, so the acceptance probability is at least $1/(2m)$. Irreducibility is tested by $X^{q^m}\equiv X\pmod f$ and $\gcd(f,X^{q^{m/\ell}}-X)=1$ for each prime $\ell\mid m$. Trial division on $m$, repeated squaring, and polynomial gcd take polynomial bit time in $m,\log q$. For $m=1$ use $K=F$. Alternatively Shoup's deterministic construction finds the degree-$m$ polynomial in polynomial bit time in bounded characteristic. The multiplication for a single coefficient takes $r-1$ field multiplications, so forming the output has polynomial bit cost. [Shoup, *New Algorithms for Finding Irreducible Polynomials over Finite Fields*](https://www.shoup.net/papers/detirred.pdf)

Fixed embeddings into a power basis suffice for the existence guarantee. For a family of samples, keep $E_s$ fixed and choose the other maps independently and uniformly from injections with $E_j(e_1)=1$, where $e_1$ is the first basis vector. Sample each subsequent image uniformly from outside the span of the previously chosen images. Each rejection loop has acceptance probability at least $1-1/q$. Once $K$ and $\lambda$ are fixed the sampler is uniform on its support of size

$$
 \prod_{j\ne s}\prod_{i=1}^{n_j-1}(q^m-q^i).
$$

Indeed, fixing all the other modes outside $s,j$ at their first basis vectors gives the bilinear pairing $(v,x)\mapsto\lambda(E_s(v)E_j(x))$. It uniquely determines $E_j$, since for every nonzero $a\in K$, the functional $b\mapsto\lambda(ba)$ is nonzero. Standard independent invertible basis changes can further randomize the samples while preserving the guarantee. In a cubic format the injective maps are all invertible, so the field construction lies in a single tensor-isomorphism orbit. Its use as a construction does not establish cryptographic indistinguishability.

## How often a uniform tensor has a rational singular tuple

Write $n_j=k_j+1$ and $D=\sum_j k_j$. Assume $r\ge3$, $2k_j<D$ for each $j$, and $D-k_i-k_j\ge2$ for each pair of distinct modes. For a uniform tensor of this format, the probability of a rational singular tuple is

$$
 q^{-1}+O_r(q^{-2}).
$$

The estimate is uniform in the dimensions satisfying these hypotheses. They include every cubic three-way format of side at least three. Let $P=\prod_j\mathbb P^{k_j}(F)$. For $x\in P$, the conditions for $x$ to be singular are exactly that $A$ annihilate the affine tangent space to the Segre cone at a product vector representing $x$. In a basis beginning with the chosen line in each mode, this subspace is spanned by basis products whose indices vary from the chosen tuple in at most one coordinate. Hence its dimension is $D+1$, and the expected number of singular tuples is

$$
 |P|q^{-D-1}=q^{-1}\prod_j(1+q^{-1}+\cdots+q^{-k_j})=q^{-1}+O_r(q^{-2}).
$$

For a distinct pair of points, use compatible mode bases by placing the selected lines at the first two basis vectors in a differing mode. A basis product belongs to both tangent spaces precisely if its index differs from each selected index tuple in at most one mode. If the pair differs just in mode $i$, the intersection dimension is $k_i+1$. If the pair differs in precisely two modes the dimension is two. If it differs in at least three the intersection is zero.

For fixed first point, the number of second points differing in a specified set $J$ of modes is $O_r(q^{\sum_{j\in J}k_j})$. Thus pairs differing in one mode contribute $O_r(q^{2k_i-D-1})=O_r(q^{-2})$ to the sum of joint singularity probabilities. For two differing modes the contribution is $O_r(q^{k_i+k_j-D})=O_r(q^{-2})$. Pairs differing in at least three modes contribute a total of $O_r(q^{-2})$ because they impose $2(D+1)$ independent linear conditions. The first two Bonferroni bounds now give the claimed estimate. This density calculation does not supply a polynomial-time test for arbitrary dense samples.

## Geometric scope and prior work

For the cubic format of side $m\ge3$, the construction is geometrically degenerate. Over an algebraic closure, $K$ becomes a product of $m$ copies of the algebraic closure, because the finite field extension is separable. The tensor becomes a weighted diagonal sum $\sum_i c_i x_i y_i z_i$. Choose three distinct coordinate vectors for the three input modes. Their pairwise products vanish, so all three contractions vanish. This example separates the finite-field condition in (2.2) from the geometric condition for hyperdeterminant nonvanishing. The theorem does not solve the geometric interior sampler.

The cubic construction is the familiar field example from the theory of finite semifields and nonsingular tensors. The contribution here is its direct application to the precisely quantified sampling question for arbitrary formats, its bit-time guarantee, and the separate rational-singularity density estimate. Publication priority for the application and estimate is unestablished. [Lavrauw, *Finite semifields and nonsingular tensors*, §4](https://files.core.ac.uk/download/pdf/55898477.pdf) · [Narayanan, *Hyperdeterminants are hard in four dimensions*, geometric formulation](https://eccc.weizmann.ac.il/report/2025/131/download/)
