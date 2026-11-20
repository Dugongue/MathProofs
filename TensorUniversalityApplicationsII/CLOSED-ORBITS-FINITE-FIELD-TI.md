# Finite-field tensor isomorphism as a closed-orbit problem

**Theorem.** Fix a prime $p$. Ordinary 3-tensor isomorphism over a presented finite field of characteristic $p$ reduces in deterministic polynomial time to Zariski orbit closure intersection over $\overline{\mathbb F}_p$ for a fixed collection of mixed tensor records under a product of special linear groups. Every constructed orbit is closed, including the orbit for a zero input tensor. The number of spaces and records is bounded in terms of $p$. Each record has at most three ordinary or dual factors. The construction uses finite-field input coordinates and structural constants zero and one.

There is also a direct encoding over $K=\mathbb F_{p^a}$, using $3ap$ spaces and output side at most $O_p((n+1)^p)$ for maximum input side $n$. In this encoding the geometric isomorphisms between any two outputs restrict bijectively to the original isomorphisms over $K$. The fixed collection in the theorem follows by first using scalar restriction to $\mathbb F_p$. This is a positive-characteristic result for the orbit-equality versus orbit-closure comparison in Lysikov and Walter’s Question I.11 and their discussion of special linear actions. Their complexity class TOCI is defined over the complex numbers. [Questions I.11 and I.13](https://arxiv.org/html/2411.04639#S1.SS4)

## 1. Tensor records and the action

Work over $L=\overline{\mathbb F}_p$. For a source mode of dimension $n_0$ put $E_i=L^{n_0+1}$ for $i$ modulo $a$. Use $S_{i,r}=\operatorname{Sym}^r E_i$ for $1\le r\le p$ with $S_{i,1}=E_i$. These are named coordinate spaces with their monomial bases. The acting group uses an **independent** $\mathrm{SL}(S_{i,r})$ on every named space. Thus the records below are ordinary mixed tensors on these named spaces, even though some of the spaces were sized and based using homogeneous polynomials. Use one such system for each of the three source modes and take the product group $H$ of all its factors.

Include the following constant records on each system.

- For every $i$ and $2\le r\le p$, take homogeneous multiplication $\mu_{i,r}:E_i\times S_{i,r-1}\to S_{i,r}$.
- For each $i$, take the linear map $J_i:E_{i+1}\to S_{i,p}$ sending basis vector $e_{i+1,j}$ to $e_{i,j}^p$.
- On $E_0=V\oplus L$, where $V$ is the original mode, take the linear projector $P$ onto $V$ along the added coordinate.

The data-dependent record is the original tensor in the product of the three $V$ summands at index zero. A linear record contributes one primal and one dual factor. A bilinear record contributes one primal and two dual factors. In these conventions the group action on a map is the output change of basis applied after the map and inverse input changes of basis. Every constant record has coefficients zero and one. The map from the original tensor to the tuple is a coordinate projection with constants.

Call the tuple of multiplication and cyclic linking records the **structural tuple**, leaving the projectors and data tensor as extra coordinates. We first examine this tuple and then its orbit closure.

## 2. Exact recoverability over the finite field

For one system write $g_i$ for the $E_i$ change of basis. If all multiplication records are preserved, the map on $S_{i,r}$ is forced to be $\operatorname{Sym}^r(g_i)$. An induction on $r$ proves this by evaluating on products of the basis vectors and using that these span. For any $g_i\in\mathrm{SL}(E_i)$ the forced map lies in $\mathrm{SL}(S_{i,r})$. One can triangularize $g_i$ over $L$. In the induced monomial basis the diagonal entries are all degree-$r$ monomials in the original diagonal entries. Each original diagonal entry occurs with the same total exponent, so their product is a power of $\det g_i=1$.

On the pure powers the matrix of $\operatorname{Sym}^p(g_i)$ is $g_i^{[p]}$, the matrix obtained by taking entrywise $p$-th powers. Consequently preservation of $J_i$ is equivalent to $g_{i+1}=g_i^{[p]}$. Returning to the starting index gives $g_0^{[p^a]}=g_0$. The roots of $X^{p^a}-X$ in $L$ are precisely $K$. Conversely every $g_0\in\mathrm{SL}_{n_0+1}(K)$ extends uniquely to preserve all multiplication and linking maps. The stabilizer of the structural tuple in $H$ is therefore finite.

Preserving the projector $P$ further forces $g_0=\operatorname{diag}(u,\lambda)$ with $u\in\mathrm{GL}_{n_0}(K)$ and $\lambda=(\det u)^{-1}$. Conversely any such $u$ is allowed. On the data record the three $u$ act by exactly the ordinary 3-tensor action. Hence the geometric isomorphisms between the outputs are in bijection with the original finite-field isomorphisms, including automorphisms. The bijection respects composition. The cyclic link is the pure-power construction from [the same-characteristic field comparison](https://github.com/Dugongue/MathProofs/blob/main/TensorUniversalityApplications/SAME-CHARACTERISTIC-TENSOR-ISOMORPHISM.md).

## 3. The structural orbit is closed

Consider one system and omit $i$ momentarily. Given arbitrary candidate multiplication records $\nu_r$, form a matrix $B_r(\nu)$ whose columns are the fixed ordered degree-$r$ monomials evaluated using the records $\nu$. Specifically use the leftmost basis vector of the written monomial as the first input and recursively evaluate the remaining factors as the second input. Take $B_1=I$. This is a polynomial matrix in the candidate records.

At any point of the structural orbit, denote the transformations on $S_r$ by $h_r$ and the one on $E$ by $g=h_1$. Directly multiplying the transformed basis vectors with the transported operations gives
$$
B_r=h_r\operatorname{Sym}^r(g^{-1}).
$$
Thus $\det B_r=1$ at every orbit point. Multiplication also satisfies the identity
$$
\nu_r=B_r\mu_r(1,B_{r-1}^{-1}).
$$
It follows by applying the preceding formula and the naturality of homogeneous multiplication. On $\det B_{r-1}=1$, inverse means adjugate, so these are closed polynomial equations. They hold throughout the orbit closure.

Return to the cyclic indices. If $J'_i$ is a possibly limiting link, write its normalized version as $B_{i,p}^{-1}J'_i$. At orbit points this is the inclusion into the fixed pure-power subspace of $S_{i,p}$ composed with the square matrix
$$
C_i=g_i^{[p]}g_{i+1}^{-1}.
$$
In particular its off-subspace coordinates vanish and $\det C_i=1$. Both conditions are polynomial in the candidate records on the preceding closed set, again using adjugates. Therefore every point in the closure can first be normalized by changing the bases of $S_{i,r}$ by $B_{i,r}^{-1}$ for $r\ge2$, leaving every $E_i$ fixed. After normalization the multiplications are standard and the normalized links are arbitrary matrices $C_i\in\mathrm{SL}_{n_0+1}(L)$ in the pure-power coordinates.

Every such list of links occurs in the structural orbit. Indeed the required equations are $g_{i+1}=C_i^{-1}g_i^{[p]}$. Starting at $g_0$ and substituting around the cycle yields $g_a=Dg_0^{[p^a]}$ for some $D\in\mathrm{SL}_{n_0+1}(L)$ obtained by multiplying Frobenius powers of the $C_i^{-1}$. The equation $g_a=g_0$ is solvable by Lang’s theorem for the connected group $\mathrm{SL}_{n_0+1}$ and the $p^a$-Frobenius. The orientation $g_0^{[p^a]}g_0^{-1}=D^{-1}$ is a Lang map after inverting the variable and the value. Use the resulting $g_i$ on $E_i$ and the forced $\operatorname{Sym}^r(g_i)$ on $S_{i,r}$, which preserves the standard multiplications and gives the specified links. Restoring the $B_{i,r}$ gives the desired point of the original orbit. Apply this independently in the three modes. The structural orbit is closed. [Lang, *Algebraic Groups Over Finite Fields*](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf)

## 4. Closure equivalence and cost

Let $x$ be a full output and let $y$ lie in its orbit closure. The projection of $y$ onto its structural tuple lies in the closed structural orbit by continuity under this equivariant coordinate projection. Its stabilizer in $H$ is conjugate to the finite group from Section 2. Hence the stabilizer of $y$ itself is finite and its orbit has dimension $\dim H$. The same holds for $x$. Every boundary orbit of an algebraic group orbit has strictly smaller dimension. Therefore $y$ lies in the orbit of $x$ itself. This shows every full output orbit is closed, even if the data record vanishes. Section 2 now implies that two output orbit closures meet exactly when the two inputs are isomorphic over $K$. [Borel, *Linear Algebraic Groups*, §1.8](https://www.math.utah.edu/~ptrapa/math-library/borel/%20Borel-Linear-Algebraic-Groups-1991.pdf)

In the direct construction $\dim S_{i,r}=\binom{n_0+r}{r}$, so the sum of the side lengths is $O_p(a(n+1)^p)$. All records have at most three factors. The structural coordinates and data embedding can be written in time polynomial in the explicit input format and extension degree for fixed $p$. This algorithm constructs the queried records and never computes a Lang preimage. Unequal source formats can be rejected immediately by outputting a fixed negative instance. Formats with a zero-length mode are decided directly from their format headers.

To keep the record collection independent of $a$, first restrict to the prime field. A named endomorphism recording multiplication by a generator of $K/\mathbb F_p$ on each mode forces recovered linear maps to be $K$-linear. Compiling those two-space and three-space records gives ordinary 3-tensor isomorphism over $\mathbb F_p$ by the [fixed-type arity-three compiler](https://arxiv.org/abs/1810.09219). Then use the construction above with $a=1$. Thus the fixed record collection uses $3p$ spaces, and its entries can be presented in the prime field even though the oracle tests geometric orbit closures. As a consequence the same closed-orbit problem is hard for finite-field code equivalence at fixed characteristic, using its reduction to tensor isomorphism. [Grochow–Qiao, §7.1 in the preprint’s related reductions and Proposition 3.6](https://arxiv.org/html/1907.00309)

## Verification

The argument for geometric closedness is written above and uses Lang’s theorem and the dimension of algebraic group orbits. The separate Lean companion checks algebraic identities at the determinant normalization and Frobenius links. The exact finite replay tests the transported multiplication normalization in degrees two and three, the link normalization, and the recovered finite stabilizers. Publication priority remains open.
