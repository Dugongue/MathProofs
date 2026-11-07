# High-Coverage Ordinary Four-Tensor Isomorphism over Growing Finite Fields

**Theorem.** Let $n\geq37$. For every explicitly presented finite field $\mathbb F_q$, there is a zero-error algorithm taking two ordinary ordered four-tensors of side $n$. It either decides isomorphism correctly or abstains. It decides whenever its first input passes an isomorphism-invariant recognition test. If that first input is uniform and its second input is arbitrary, the probability of passing is at least
$$
 1-\frac{16n^4}{q}.
$$
The expected bit runtime is polynomial in $n$ and $\log q$. In every fixed characteristic the algorithm can be made deterministic in polynomial bit time. In particular the density tends to one if $q/n^4$ tends to infinity. No nonzero lower bound for fixed $q$ and growing $n$ is asserted by this estimate.

The proof transports the spectral approach of [MathProofs Problem 1.8](../Problem18/README.md) from a fixed orthogonal or unitary form to the ordinary $\mathrm{GL}(n)^4$ action. The new ingredients are a rational substitute for conjugate transpose from [Full-Cut-Rank Tensor Isomorphism](../FullCutTensorIsomorphism/PROOF.md), a combinatorial witness for simultaneous separability in every mode, and the finite-field quotient method from [Tensor Frame Recovery and Cyclic Quotients](../TensorFrameRecovery/CYCLIC-QUOTIENT.md). The argument is informal.

## 1. Covariants and the recognition test

For a four-tensor $T$, let $M(T)$ be the $12\mid34$ flattening. Where it is invertible, relabel the inverse as the tensor $S(T)$ with four contravariant slots. For source basis changes $g_1,\ldots,g_4$, the tensor $S(T)$ transforms by their inverse transposes. Thus one can contract positive copies of $T$ with negative copies of $S(T)$ using the canonical evaluations, with no choice of inner products.

Use four copies of each, with copies on each side indexed by $H=\mathbb Z/4$, and shifts $(s_1,s_2,s_3,s_4)=(0,1,3,2)$. In mode $j$ contract positive copy $x$ to negative copy $x+s_j$. Delete the edge of color $i$ at positive copy $0$. The remaining two open slots give a conjugation-covariant endomorphism $A_i(T)$ in mode $i$. Its computation uses a fixed number of tensor entries and summed indices and therefore polynomially many field operations. The recognition test accepts when $M(T)$ is invertible and all four $A_i(T)$ have squarefree characteristic polynomial. This is an invariant condition and is checked by linear algebra and polynomial gcds.

## 2. A combinatorial certificate in every side dimension

Work with index labels in $\mathbb Z/n$, independently of the coefficient field. Choose a permutation $P$ of ordered pairs preserving their sum and commuting with simultaneous translation of both coordinates. Use formal weights $w_{ab}$ at the support positions $(a,b,c,d)$ with $(c,d)=P(a,b)$. This gives a weighted permutation matrix in the $12\mid34$ cut, with the inverse tensor having the same support and reciprocal weights.

On this formal tensor all four covariants are diagonal. Every support row satisfies $a+b=c+d$. When one edge of the contraction is omitted, the other three full color matchings equate the sums in those three coordinates. The support relation then equates the sums in the remaining coordinate. The other three edges of that color force equality on the omitted edge. Thus every contribution to a diagonal entry can be indexed by a full matching. Its Laurent monomial is the product of four positive row weights divided by the product of four negative row weights.

We construct $P$ to contain eight rows forming one full matching. Put $t=(1,3,-1,-3)$ indexed by $\mathbb Z/4$. At position $x$ take the positive two-parameter row $(A,B)=(-t_x-t_{x+1},t_{x+1})$ and the negative row $(A,B)=(-t_x-t_{x+1},t_x)$. The four values $(A,B,A+B,A+2B)$ on these rows agree on every prescribed edge with shifts $(0,1,3,2)$, by substitution. Apply a fixed integer scaling to each coordinate to make the actual four-coordinate row
$$
 (a,b,c,d)=(A,3B,-A-B,2A+4B).
$$
The edge equalities survive this scaling, and now $a+b=c+d$. Among the four positive rows the coordinate lists are
$$
 (-4,-2,4,2),\quad(9,-3,-9,3),\quad
 (1,3,-1,-3),\quad(4,-8,-4,8).
$$
Each consists of four distinct residues when $n\geq37$. Among the eight rows the values of $b-a$ are
$$
 (13,-1,-13,1,7,11,-7,-11),
$$
in positive-then-negative order, and the values of $d-c$ are
$$
 (3,-11,-3,11,-7,9,7,-9).
$$
Both lists are distinct modulo $n$. The second list therefore defines a partial permutation $h$ of the first differences, sending each $b-a$ to its matching $d-c$. If $n$ is even, it preserves parity by $a+b=c+d$. Extend $h$ to a permutation of all residues, separately within each parity class when $n$ is even. Choose $f(\delta)$ such that $2f(\delta)=\delta-h(\delta)$ for every $\delta$. This is possible by parity for even $n$ and invertibility of 2 for odd $n$. At the eight prescribed differences use $f(b-a)=c-a$, which solves that equation. Now take
$$
 P(a,b)=\bigl(a+f(b-a),\ b-f(b-a)\bigr).
$$
It preserves the sum and commutes with simultaneous translation. It is bijective because the output difference determines the input difference through $h$, after which the displayed translations can be undone. It includes all eight prescribed rows. This construction uses only the single invertible cut needed in the test.

The Laurent monomial for the prescribed matching has eight distinct variables, four with exponent $1$ and four with exponent $-1$. Any full matching giving the same monomial must use exactly the same two row sets, since there are only four slots on each side. In each color the four positive labels are distinct, so every edge between the two row sets is uniquely determined by that color's labels. Consequently all ways to assign the same row sets to the positions differ by a color-preserving automorphism of the diagram. Color 1 forces the positive and negative permutations to be equal. Color 2 then forces that permutation to commute with the cyclic shift by 1. The four translations are the only such permutations and all are allowed. Thus the monomial occurs exactly once in each diagonal entry whose external label belongs to the four positive labels, and in no other entry. Its coefficient is 1 in every coefficient characteristic.

For each mode the four positive labels lie in an integer interval of length at most 18. For $n\geq37$, the gap around the cyclic order outside that interval is greater than 18 and all internal gaps are at most 18. A translation preserving the set must preserve that unique largest gap and fix its endpoints, so its only period is zero. Because $P$ commutes with translation, every common translate of the matching still belongs to the support. For any two different labels $z,z'$ in the mode, some translate of the four positive labels contains $z$ and omits $z'$. Indeed, otherwise the four-element sets of translations that place $z$ and $z'$ in the set would be equal, making $z'-z$ a period. The translated monomial separates those diagonal entries. Hence all pairwise differences are nonzero Laurent polynomials, and all four spectra are simultaneously squarefree over the rational function field of the formal weights.

The [exact checker](check_switches.py) verifies the routing, the eight-row configuration, the four reassignments and the period argument at representative odd and even sizes. The proof of nonvanishing does not require evaluating the weights or enumerating the field.

## 3. Passing from a formal witness to a density bound

Each entry of $P_i(T)=\det(M(T))^4 A_i(T)$ is a polynomial of total degree at most $4n^2$. There are four positive copies and four adjugate factors of degree $n^2-1$. The discriminant of the characteristic polynomial of an $n$-by-$n$ matrix is homogeneous of degree $n(n-1)$ in its entries. One way to see this is to use the product of squared eigenvalue differences, with its symmetric polynomial expression. Therefore
$$
 \Delta(T)=\det M(T)\prod_{i=1}^4 \operatorname{disc}(\chi_{P_i(T)})
$$
is a polynomial of degree at most $n^2+16n^3(n-1)\leq16n^4$. On the weighted permutation witness it is nonzero as a Laurent expression, by Section 2 and the nonzero determinant. Hence it is a nonzero polynomial in the ordinary tensor coordinates. The recognition test accepts precisely when $\Delta$ does not vanish. The elementary polynomial zero bound on independently uniform coordinates of $\mathbb F_q$ gives the claimed rejection bound.

## 4. Solve the entire residual orbit, including zero entries and nonsplit spectra

If the first tensor passes, then an isomorphic second tensor must also pass and have the same four characteristic polynomials $f_i$. A mismatch certifies a negative answer. For equal polynomials, choose cyclic bases for the mode endomorphisms of the two tensors. They exist because each characteristic polynomial is squarefree. Explicitly, split into the irreducible primary components using polynomial factoring and add a nonzero projected vector from each component. This is cyclic since each primary component occurs with multiplicity one. In these bases the mode spaces are identified with the same algebras $K_i=\mathbb F_q[z]/(f_i)$. The remaining allowed maps are exactly multiplication by units of the $K_i$, since the centralizer of a cyclic operator consists of its polynomials.

Write the two tensors in $K=K_1\otimes K_2\otimes K_3\otimes K_4$. Each $K_i$ and $K$ is a finite product of fields. Split them by factoring, for $K$ factoring one successive polynomial over each previous factor field. The total dimension of $K$ is $n^4$. If the two tensors have different sets of nonzero field components, return no. On common nonzero components $E_s$, take ratios $r_s$. The remaining question is whether the vector $r$ is in the image of the product of the local field unit groups $L_j^\times$. For each $s$, the homomorphism from the $K_i$ selects one factor of $K_i$ and embeds that field into $E_s$. All selected embeddings are given by the computed bases. Empty support can be handled by equality with zero.

Here are the bit-complexity details of the quotient method for varying $q$. Denote the relevant field orders of the multiplicative groups by $m_s=q^{[E_s: \mathbb F_q]}-1$ and $m_j=q^{[L_j: \mathbb F_q]}-1$. Make compatible models $F(e)$ of all required extension degrees as follows. For each prime dividing a required degree, choose one displayed field whose degree has maximal valuation at that prime. Its nested subfields of prime-power degrees are computed by Frobenius fixed spaces. The tensor product of the needed prime-power models is a field, as the degrees are pairwise coprime. The divisor maps between these models are the tensor products of the nested subfield maps, so they compose exactly. Each required constructed field has degree at most $n^4$. Identify the displayed fields with these models by choosing an algebra generator and factoring its minimal polynomial over the model. A random element is a generator with probability at least a constant. Indeed the non-generators lie in the union of maximal proper subfields, whose relative sizes sum to at most $1/2$ by the bound $\omega(e)2^{-e/2}$ for $e\geq4$ and the direct cases $e=2,3$. Testing the generator condition uses the Frobenius fixed subfields. Every embedding of a degree-$e$ source field into a degree-$f$ target field then equals the coherent embedding composed with one of the $e$ powers of $q$-Frobenius on the source. Compare on a generator to compute that shift $k_{sj}$.

In a hypothetical common field of degree the least common multiple of all degrees, take powers of one primitive root to give compatible abstract generators of all the multiplicative groups. The common field and the generators are used only for correctness. No algorithmic operation takes place there. In the abstract exponent coordinates the local unit map has matrix entries $(m_s/m_j)q^{k_{sj}}$ when the field $L_j$ embeds into $E_s$, and 0 otherwise. The matrix is explicit without computing any logarithms. Form the lattice generated by its columns and the columns of $\operatorname{diag}(m_s)$. Compute a Smith row transform $U$ with image lattice $\operatorname{diag}(d_i)\mathbb Z^S$. Membership is equivalent to the abstract exponent vector of $r$ having $(U\log r)_i=0\bmod d_i$ for every $i$.

To evaluate this condition, compute a gcd-free basis for the integers $d_i$ and $m_s$ by repeated gcd splitting and merging. The resulting atoms are pairwise coprime, and the computation uses no integer factorization. For each atom power $D$ in $d_i$ choose a target field with $D\mid m_{s_0}$. Such a field exists because the exponent of the quotient divides the least common multiple of the original orders and atom exponents track all their prime divisors together. Evaluate in each model $F([E_s: \mathbb F_q])$ the element
$$
 r_s^{m_s U_{is}/D}.
$$
The exponent is integral since $d_i$ divides $m_s U_{is}$. The result has order dividing $D$ and $m_s$, so it lies in the gcd-degree subfield shared with $F([E_{s_0}: \mathbb F_q])$. Move it there through the coherent subfield maps using linear algebra. The product in the target model is 1 precisely when the quotient exponent is 0 modulo $D$. Checking every atom power checks the original Smith congruences. This proves exactness, including nonsplit spectra and zero payload components.

All field dimensions, the number of factors, the matrix sizes, and the order bit lengths are polynomial in $n$ and $\log q$. Finite-field factoring is Las Vegas in these parameters, and the remaining arithmetic uses Gaussian elimination, powering, gcd splitting, and polynomial-time integer normal forms with multipliers. For fixed characteristic $p$ there is a deterministic version. A squarefree polynomial can be split by computing the $p$-Frobenius fixed algebra of its étale quotient over $\mathbb F_p$, which is a product of copies of $\mathbb F_p$. Multiplication eigenspaces of basis elements with scalars from the fixed prime field split this product and give the factor idempotents. To deterministically find an algebra generator, choose prime-field coordinates one at a time while maintaining a positive count of elements outside the union of maximal proper subfields. Inclusion–exclusion has at most $2^{\omega(e)}\leq e$ terms and each intersection count is an affine linear solve. Thus the deterministic bit bound in fixed characteristic follows without enumerating the base field.

## 5. Extension to every even order

For every even order $d=2k\geq4$ and $n\geq37$, the same algorithm decides ordinary $d$-tensor isomorphism on a uniform first-input fraction at least
$$
 1-\frac{4d\,n^{d/2+2}}{q}.
$$
The expected runtime is polynomial in the dense input length, including when $d$ varies. The fixed-characteristic deterministic version also transfers.

Use the $k\mid k$ flattening and extend the sum-preserving permutation from Section 2 on the first two coordinates of each side by the identity on each of the remaining $k-2$ coordinates. In the four positive and four negative rows of the switch, put the value of the first coordinate in all those extra coordinate pairs. Use shift 0 on each extra color. The eight row assignments still satisfy all matchings, and the four positive labels in each extra color are distinct and aperiodic. The total sum of input labels equals that of output labels, so summing the other colors still restores the one missing equality in every mode. All coordinates can still be translated together. The same monomial separation proves squarefree spectra simultaneously for the $d$ mode covariants.

Writing $M$ for the $k\mid k$ flattening, the degree of each denominator-cleared covariant is at most $4n^k$. The determinant times the product of the $d$ discriminants has degree at most $n^k+4d n^k n(n-1)\leq4d n^{k+2}$. The polynomial zero bound applies as before. The direct contractions have at most $4d-1$ internal indices and two output indices, so even direct enumeration is polynomial in the $n^d$ input entries. The residual algebra has dimension $n^d$, and the steps of Section 4 work with $d$ local algebras. This proves the stated dense-input bound.

## 6. Relation to earlier results

- [Li, Li, Qiao, Tao, and Wang, arXiv v2](https://arxiv.org/html/2604.00591v2), Theorem 1.3 and Problem 1.7, concerns ordinary four-tensor isomorphism at fixed $q$ and growing dimension. The result here gives near-full coverage in a different, growing-field regime. It does not resolve their fixed-field question, and it does not give a comparable algorithm for ordinary three-tensor isomorphism.
- [Problem18](../Problem18/README.md) supplies the spectral-recognizer architecture for fixed form-preserving actions. [Full-Cut-Rank Tensor Isomorphism](../FullCutTensorIsomorphism/PROOF.md) supplies the odd four-copy inverse-contraction diagram, and [Tensor Frame Recovery and Cyclic Quotients](../TensorFrameRecovery/CYCLIC-QUOTIENT.md) supplies the quotient method. The new links are the sum-preserving routing, the Laurent monomial separation, and the resulting ordinary-group density theorem.
- Standard algorithmic inputs include [Cantor and Zassenhaus, finite-field factoring](https://doi.org/10.1090/S0025-5718-1981-0606517-5) and [Kannan and Bachem, integer normal forms](https://doi.org/10.1137/0208040). The density proof and the algorithm are informal, with external validation and publication priority unestablished.
