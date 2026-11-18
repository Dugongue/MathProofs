# Exact exponential separation degree for local tensor isomorphism

**Theorem.** For every $m\ge 2$, put $n=6m-8$ and $D_m=8(F_{m+2}-2)$, where $F_1=F_2=1$ are the Fibonacci numbers. There is an explicit pair of real $n\times n\times n$ tensors on the same support, differing by the sign of a single entry, for which the least total degree of a separating $\mathrm U(n)^3$-invariant polynomial in the real and imaginary coordinates is exactly $D_m$. Each mode slice contains at most three nonzero entries. The nonzero magnitudes can all be one, or can be positive integers at most $1+3n(n-1)/2$ chosen so that the two tensors have the same positive, simple-spectrum Gram in each mode.

There is also a real pair of side $2n$ for which the least separating degree for $\mathrm O(2n)^3$ is exactly $D_m$. Its one-mode Grams agree between the two tensors and can have every eigenvalue of multiplicity exactly two. Finally, an $n\times n\times n$ local-unitary comparison with simple one-mode Gram spectra always admits a separating polynomial of degree $2^{O(n)}$ if the two tensors are inequivalent. Thus the exponential scale is tight on the simple-spectrum unitary class.

For positive-magnitude versus sign-edited pairs, the least degree is given by a shortest odd incidence relation. Testing whether the least degree is at most a given bound is NP-complete on this class. Approximation within a sufficiently small constant factor greater than one is NP-hard, even on known inequivalent pairs with identical simple Grams and at most five nonzeros per slice.

## 1. A three-dimensional support encoding Fibonacci weights

Let $x_1,\ldots,x_m$ be the variables of the signed equations

$$
x_2-x_1=0,\qquad x_{i+2}-x_{i+1}-x_i=0\quad(1\le i\le m-2).
$$

Make four copies of each row, twice with original signs and twice with reversed signs. Use one first-mode vertex for each copied row and make one hyperedge for each occurrence of a variable in that row. For a given variable, there are equally many positive and negative occurrences, with at least two of each. Arrange its occurrences in an alternating-sign cycle. Partition the cycle edges into its two alternating perfect matchings. Use one second-mode vertex for each pair in the first matching and one third-mode vertex for each pair in the second matching. An occurrence hyperedge now has three endpoints, given by its row and the two matching pairs containing it.

Each pair of different hyperedges shares at most one endpoint. Within a row the variables are distinct, and the last two labels come from separate variable cycles. Within a variable cycle the two matchings have no common pair, because the cycle has length at least four. The first-mode vertex count before padding is $4(m-1)$. Each of the other two modes has $n=6m-8$ vertices, since the total occurrence count is $12m-16$.

Here is padding to exactly $n$ vertices in all three modes. Order the second- and third-mode vertices by the same variable blocks. The two corresponding blocks have the same length and each length is at most six, since a variable occurs in at most three unreplicated equations. Let $b$ be the maximum block length. We have $n\ge 2b$, including $m=2,3$ by direct count. Cyclically pair vertex $j$ of the second mode with vertex $j+b$ of the third. The two matched vertices belong to different variable blocks. For each new first-mode vertex, add one hyperedge using one different such pair. These hyperedges share at most one endpoint with any old hyperedge, and consume each second- and third-mode vertex at most once. All three parts now have $n$ vertices of degrees between one and three.

Write $A$ for the vertex-by-hyperedge incidence matrix. A vector in its integer kernel must be zero on each padding hyperedge because its new row has only one incidence. Each matching pair imposes that the two entries sum to zero. Thus the occurrences of variable $x_i$ equal its printed sign times some integer $x_i$. The remaining rows are precisely repetitions of the original signed recurrence. Consequently

$$
\ker_{\mathbb Z} A=\mathbb Z u,\qquad
u_e=(\text{printed sign of }e)F_i
$$

for an occurrence of $x_i$, with $u_e=0$ on padding hyperedges. An occurrence of $x_1$ has weight $1$ or $-1$. The absolute values sum to $4(2+2\sum_{j=3}^m F_j)=8(F_{m+2}-2)=D_m$. This proof produces the entire saturated integer kernel directly.

## 2. Exact separation over the complex numbers

For positive magnitudes $a_e$, define $T_+$ to have entry $a_e$ at each hyperedge $e$, and zero off the support. Define $T_-$ by changing the sign at one occurrence of $x_1$. Under a product of three diagonal unitary matrices, a supported entry $z_e$ is multiplied by the product of the three endpoint phases. A polynomial invariant restricted to this support is a sum of weight-zero monomials in $z_e,\overline{z_e}$. Indeed the two variable families are independent polynomial coordinates after complexifying the real coordinate ring, and projection onto weight zero is obtained by averaging circle characters in each vertex phase. Equivalently, any surviving monomial $z^\alpha\bar z^\beta$ satisfies $A(\alpha-\beta)=0$.

If $|\alpha|+|\beta|<D_m$, then $\|\alpha-\beta\|_1<D_m$, so the preceding kernel calculation forces $\alpha=\beta$. The value consequently depends only on magnitudes. Every full-group invariant of degree less than $D_m$ agrees on the pair.

For the reverse direction let $u=u^+-u^-$, and take $u_e^+$ copies of the entry $e$ on a positive list and $u_e^-$ copies on a negative list. For each mode separately match the two lists' positions having each particular vertex label. The matchings exist because $Au=0$, and the two lists have equally many positions by summing over the vertices of any one mode. Use these three bijections as wires in a tensor contraction between copies of $T$ and copies of $\bar T$. Specifically each wire identifies one index of a positive copy with one index of a negative copy in the same mode, and all remaining label assignments are summed. The resulting polynomial is $\mathrm U(n)^3$-invariant by cancellation of every unitary with its adjoint. Its degree is $D_m$.

One term in this sum is the intended monomial $z^{u^+}\bar z^{u^-}$. Every term is nonnegative at $T_+$. At $T_-$ every term has the same magnitude as it does at $T_+$, and the intended monomial reverses its sign because its exponent at the flipped entry is one. Thus the real part of the contraction strictly separates the pair, with no cancellation of the difference.

Every one-mode Gram is diagonal because two different supported entries never agree on both other indices. Its diagonal at a vertex $v$ is $\sum_{e\ni v}a_e^2$, so the two tensors have identical Grams. To make every spectrum simple, assign positive integer magnitudes in any edge order. For any pair of vertices in the same mode their incident edge lists are disjoint and nonempty. At the last edge of this pair's two lists, at most one positive integer magnitude would make their squared sums equal. Avoid all such conflicts when they close. At most $3n(n-1)/2$ positive integers are forbidden at a step, which gives a deterministic polynomial-time choice from the asserted range. Both tensors have all mode ranks full.

## 3. The real orthogonal counterpart

Replace each vertex line by a real plane with orthonormal vectors $p_v,q_v$ and put $w_v=p_v+\mathrm i q_v$. The following tensor is real for every choice of complex $z_e$:

$$
R(z)=\sum_{e=(i,j,k)}
 \bigl(z_e\,w_i\otimes w_j\otimes w_k+
 \bar z_e\,\bar w_i\otimes\bar w_j\otimes\bar w_k\bigr).
$$

Rotations of the coordinate planes act by the same endpoint phase rule, after choosing the sign convention for each angle. Restrict an orthogonal invariant to the real-linear family $R(z)$. The weight-zero calculation still applies, with the same upper bound on total degree under substitution. Hence all $\mathrm O(2n)^3$-invariants of degree below $D_m$ agree on $R(T_+),R(T_-)$.

Use the same three wire matchings, now as real Euclidean bilinear contractions between copies of $R$. In their complex multilinear expansion, contractions of $w_v$ with $w_v$ or of $\bar w_v$ with $\bar w_v$ vanish, and contraction of $w_v$ with $\bar w_v$ gives $2$. Different vertices give zero. Thus each surviving term is a positive power of $2$ times its entry-product, and choosing $w$ at the positive occurrences and $\bar w$ at the negative occurrences gives the intended term. The same sign argument gives strict separation at degree $D_m$. The Gram on a vertex plane is $8\sum_{e\ni v}|z_e|^2$ times the identity: the two contracted modes contribute $4$, and the sum of $w_v\bar w_v^{\mathsf T}$ and its conjugate is twice the identity. Linearity of the support rules out off-block contributions. Thus the simple unitary spectra become exactly double eigenvalues.

## 4. A matching exponential upper bound for simple unitary spectra

Trace powers of each one-mode Gram, through exponent $n$, determine its spectrum by Newton's identities. If two tensors agree on these and the spectra are simple, diagonalize each Gram in the same eigenvalue order on both tensors. A transporter must then act diagonally. To test magnitudes by full-group invariants, for each fixed eigenvalue $\lambda$ of the common spectrum use

$$
P_{\lambda}(G)=\prod_{\mu\ne\lambda}\frac{G-\mu I}{\lambda-\mu}
$$

as a polynomial spectral projector on its Gram variable. Contract $T$ against $\bar T$ with the three corresponding projectors to test the squared magnitude of a specified coordinate in the common eigenbasis. These polynomials have degree $O(n)$. Distinct support or magnitude already separates.

On common nonzero support, equality up to diagonal phases is determined by all phase characters indexed by the integer kernel of its incidence matrix $B$. This follows by Smith normal form on the map taking vertex phases to endpoint products. The image of each nonzero Smith diagonal entry is the full circle, and the zero diagonal entries give the integer characters that must agree. It suffices to test a generating set of this kernel.

Here is a short bound on a generating set. Fix an orthant and absorb its signs into the columns of $B$. In the nonnegative real kernel cone, every extreme ray has a minimal support with restricted kernel dimension one. Otherwise a nonparallel kernel vector on that support allows small perturbations of both signs, contradicting extremality. If $r=\operatorname{rank}B$, such a support has at most $r+1$ columns. Primitive integer ray generators are bounded entrywise by $3^{r/2}$, by taking minors of independent restricted rows and applying Hadamard's inequality to columns of Euclidean norm at most $\sqrt3$. By conic Carathéodory, every ray decomposition can use at most the number $s$ of columns of $B$. For an indecomposable nonnegative integer kernel vector, each coefficient in such a decomposition is less than one unless the vector itself is a primitive ray generator. Indeed otherwise one can subtract that integer generator and stay in the same cone. Every indecomposable vector therefore has $\ell_1$-norm at most $s(r+1)3^{r/2}$, and every integer kernel vector is a sum of such vectors in its orthant by descending $\ell_1$-norm. Here $s\le n^3$ and $r\le3n$.

The monomial tester for one such short vector is lifted to a full-group invariant by inserting the spectral projector at each wire in the matching contraction from Section 2. These matrices transform by conjugation, so the contraction is invariant everywhere. In the common eigenbasis it gives exactly the chosen monomial with the specified labels. Taking its real or imaginary part separates whenever its complex values differ. Inserting these degree-$O(n)$ matrices multiplies the degree by at most $O(n)$. Thus some invariant of degree $2^{O(n)}$ separates any inequivalent simple-spectrum pair.

The real simple-spectrum case differs quantitatively. In the common Gram eigenbases the residual group consists of signs. Use the incidence matrix over $\mathbb F_2$. Its nullspace is generated by fundamental column dependencies of support at most $3n+1$, obtained by choosing a basis of its column space. Each such dependency has even incidence at every vertex and therefore gives a product of entries that can be lifted to an orthogonal invariant by pairing slots and inserting the same projectors. A separating invariant of degree $O(n^2)$ therefore suffices when the real Grams are simple, whereas the double-spectrum examples above require exponential degree.

## 5. Exact quantum consequence

Normalize the two unitary tensors by their common norm. Draw a product of three independent Haar unitaries once, applying the same draw to all $k$ copies of the chosen pure state. The ensemble density operator on the $k$ copies is the local Haar average of $(TT^\dagger)^{\otimes k}$ in vectorized notation. Every matrix entry is an invariant polynomial of degree $2k$. The two averaged density operators are therefore identical for $k<D_m/2$, including for measurements that act jointly on all copies.

At $k=D_m/2$ the displayed separating contraction is the expectation of an operator that permutes copies independently on each party's registers, with the three permutations given by its three wire matchings. It commutes with the action of the same local unitary on all copies. Its Hermitian part has different expectation on the normalized pair by the sign argument, so the averaged density operators differ at exactly that copy number. This is a statement about exact equality of moment operators, with no uniform advantage bound asserted at the first differing copy number.

## 6. Computing the least degree is NP-complete

Let the first tensor have positive real magnitudes on a common support and the second tensor reverse the signs on a set $J$ of entries. The arguments of Section 2 give the exact formula

$$
\min\left\{\|u\|_1:u\in\mathbb Z^{E},\ Au=0,\quad
     \sum_{e\in J}u_e\equiv 1\pmod 2\right\}.
\tag{1}
$$

In a monomial the sign difference is $(-1)^{\sum_{e\in J}(\alpha_e+\beta_e)}$, with the same parity as $\sum_{e\in J}(\alpha_e-\beta_e)$. Any distinguishing monomial has degree at least (1), and a matching contraction witnesses every candidate vector with no sign cancellation. The same formula holds for the real counterparts $R(z)$. The empty minimum is $+\infty$. In fact Smith normal form shows in that case that the tensors are equivalent by diagonal phases, or by coordinate-plane rotations for $R(z)$. Computing a kernel basis suffices to check that parity is even on the whole kernel. Thus deciding equivalence for these sign pairs has a polynomial-time solution even though minimizing the separating degree is hard.

For NP membership, an integer kernel vector of norm at most the supplied bound $K$ has polynomial bit length in the support encoding and the binary length of $K$. Check its incidence equations, norm and parity directly.

For hardness start from perfect three-dimensional matching on three sets of size $k$. Let $z_S$ be an integer for each allowed triple $S$, let $y_i,y_i'$ be slack and its duplicate for each universe element $i$, and add the common integer $t$. Impose the signed equations

$$
\sum_{S\ni i}z_S+y_i-t=0,\qquad y'_i-y_i=0
      \quad (i=1,\ldots,3k).
$$

Use the same fourfold row duplication and alternating matching construction as in Section 1. It applies to any system with coefficients $\pm1$ on distinct variables per row, each occurring variable having at least four slots after duplication. Padding to cubical format also works here. Every unreplicated row has at least two variables, and no variable appears more than once per row, so each variable block has length at most half the number of vertices of a matching mode. Use the cyclic offset by the largest block as before. The first tensor is positive on the resulting support and the second reverses a single occurrence of $t$. Choose the magnitudes as in Section 2 for simple Grams.

The tensor incidence relations have exactly one signed copy, in each occurrence slot, of the original solution variables. The norm of a relation is

$$
12\sum_S|z_S|+12\sum_i |y_i|+12k|t|.
\tag{2}
$$

Each triple occurs in three unreplicated rows, $y_i$ occurs twice, $y'_i=y_i$ occurs once, and $t$ occurs $3k$ times. The parity condition is exactly that $t$ be odd. Summing the element equations gives $3\sum_S z_S+\sum_i y_i=3kt$, which shows that (2) is at least $24k|t|$. Equality at the threshold $24k$ forces $|t|=1$, all $y_i=0$, and all nonzero $z_S$ to have the sign of $t$. In fact $3\sum |z_S|+\sum |y_i|\ge 3k|t|$, whereas (2) counts each $|y_i|$ three times in that inequality. After changing the global sign to make $t=1$, the remaining system is exactly a perfect matching indicator. Conversely a perfect matching gives an odd relation of norm $24k$. The assignment $t=1,z_S=0,y_i=y'_i=1$ gives an odd relation of norm $48k$ on every instance. Therefore all output pairs are inequivalent and the degree problem is NP-complete. [Karp, *Reducibility Among Combinatorial Problems*](https://cgi.di.uoa.gr/~sgk/teaching/grad/handouts/karp.pdf)

The reduction preserves a constant gap. Use Petrank's Theorem 4.4 with occurrence bound three, which makes it NP-hard to distinguish a perfect matching from the case where every matching has size at most $(1-\delta)k$, for a constant $\delta>0$. Here the first-mode rows have size at most five and the other mode degrees remain at most three. For an odd relation with $|t|\ge3$, (2) is already at least $72k$. Otherwise take $t=1$ and write $P=\sum_S\max(z_S,0)$, $M=\sum_S\max(-z_S,0)$, $B_0=\sum_i|y_i|$, and $Y=\sum_i y_i$. The excess above $24k$, divided by 12, is $a=P+M+B_0-k=2M+B_0-Y/3$. Make a multiset of triples with the positive multiplicities. The total surplus of positive incidences above one per element is at most $3M+B_0$: at element $i$ its positive count minus one is its negative count minus $y_i$. Deleting one copy incident to an overloaded element decreases this surplus by at least one. At most $3M+B_0$ deletions give a matching of size at least

$$
P-3M-B_0=k-2M-B_0-Y/3\ \ge\ k-2a,
$$

since $2M+B_0-Y\ge0$. On a gap NO input this forces $a\ge\delta k/2$, hence least degree at least $24k(1+\delta/4)$. The YES degree is $24k$. In particular there can be no polynomial-time approximation scheme for the least separating degree on this class unless $\mathsf P=\mathsf{NP}$. [Petrank, *The Hardness of Approximation: Gap Location*, Theorem 4.4](https://csaws.cs.technion.ac.il/~erez/Papers/gap.pdf)

## Sources and scope

The project DAG led from exact character averaging in the Lean module $\texttt{FourierCubatureBridge20260906}$ and the Gram-coordinate step in $\texttt{RobustRealTISpectral20261006}$ to the use of a phase lattice on a sparse support. The character comparison above is the circle counterpart of finite character orthogonality. The recurrence realization uses the idea of balanced monomial walks in algebraic statistics, with two alternating matchings added to enforce the three-mode linear support. [Petrović–Stasi, *Toric algebra of hypergraphs*](https://arxiv.org/abs/1206.1904) · [Petrović–Thoma–Vladoiu, *Hypergraph encodings of arbitrary toric ideals*](https://arxiv.org/abs/1711.04354) · [Bürgisser et al., *Polynomial time algorithms in invariant theory for torus actions*](https://arxiv.org/abs/2102.07727)

Derksen–Makam obtain exponential bounds for algebraic special-linear actions on tuples of tensors and on tuples of cubic forms. Acuaviva et al. give an exponential lower bound for tensor-network gauge invariants. The pair above involves one tensor per input, independent compact local actions, an exact first separating degree, and explicit marginal spectra. The contraction-to-copy correspondence is standard in local-invariant methods. A targeted literature check did not identify this combination as a prior theorem. Publication priority remains unestablished. This is an informal proof. [Derksen–Makam](https://arxiv.org/abs/1902.10773) · [Acuaviva et al., Proposition 4.15](https://arxiv.org/abs/2209.14358) · [*Tensor invariants for multipartite entanglement classification*](https://arxiv.org/abs/2604.02269)

Exact finite controls verified the incidence ranks, signed weights, cube padding and slice sparsity for $m=2,\ldots,12$. For the all-unit-magnitude pair at $m=2$, one degree-eight matching contraction evaluates to $64$ and $48$, respectively.
