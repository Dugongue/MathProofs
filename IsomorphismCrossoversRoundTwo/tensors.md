# Tensor isomorphism over fixed finite rings of prime-power characteristic

**Status.** Informal proof. The reduction is deterministic and works on explicit finite module presentations and tensor coordinates. Publication priority is unestablished.

**Theorem.** Let $R$ be a fixed nonzero finite commutative ring of characteristic $p^e$, for a prime $p$ and $e\ge1$. Tensor isomorphism over $R$ on explicitly presented finite modules, free tensor isomorphism over $R$, and ordinary tensor isomorphism over $\mathbb F_p$ are polynomial-time many-one equivalent. In the notation of Grochow, Qiao and Stange, the resulting equality in the explicit presentation model is

$$
\mathsf{3TI}_R=\mathsf{3FTI}_R=\mathsf{3TI}_{\mathbb F_p}.
$$

The upper reduction works on a finite system of modules, marked elements and maps that are additive separately in each slot, with a fixed bound on the arity. In the tensor case, only linear and bilinear maps are needed. Vector spaces over $\mathbb F_p$ in the intermediate system have dimension at most $\binom{m+p^{e-1}}{p^{e-1}}$ when the corresponding additive group has $m$ base-$p$ digit coordinates. This dependence is why the theorem fixes the ring. The proof below does not assume a uniform polynomial bound as the characteristic exponent grows.

## 1. Digit functions and Lucas's theorem

Let $M$ be any finite additive group killed by $p^e$. Give it cyclic coordinates $M=\bigoplus_i\mathbb Z/p^{e_i}\mathbb Z$. Write the representative of each coordinate in base $p$, and view its digit at position $j$ as a function $x_{i,j}:M\to\mathbb F_p$ of weight $p^j$.

Every $\mathbb F_p$-valued function on $M$ has a unique digit polynomial with degree at most $p-1$ in each digit. This is the tensor product of the one-variable interpolation bases on $\mathbb F_p$. For $0\le a\le D=p^{e-1}$, let $F_a(M)$ be the span of these monomials of weighted degree at most $a$. Multiplication of functions maps $F_a(M)\otimes F_b(M)$ to $F_{a+b}(M)$: each use of $x^p=x$ decreases weight. Every digit coordinate belongs to $F_D(M)$.

**Digit bound.** If $f:M\to N$ is additive, then pullback by $f$ sends $F_a(N)$ into $F_a(M)$. To prove this, work in a target cyclic coordinate of period $p^r$. Write a nonnegative integer representing that coordinate of $f(x)$ as $S=\sum_\nu c_\nu p^{j_\nu}x_\nu$, where $c_\nu$ are fixed nonnegative integers and $x_\nu$ are digit values in $[0,p-1]$. This expression follows by applying $f$ to the cyclic generators. Its digit at position $k<r$ is

$$
[z^{p^k}](1+z)^S\pmod p.
$$

Indeed, modulo $p$ one can use $(1+z)^{p^i}=1+z^{p^i}$ in the base-$p$ expansion of $S$. Lower digits contribute exponents at most $p^k-1$, and higher ones contribute no positive exponent at most $p^k$. This is the required digit case of Lucas's theorem.

Modulo $p$, the factor from digit $x_\nu$ is

$$
(1+z)^{c_\nu p^{j_\nu} x_\nu}
=\sum_{\ell=0}^{p-1}\binom{x_\nu}{\ell}
\big((1+z^{p^{j_\nu}})^{c_\nu}-1\big)^\ell .
$$

The polynomial $\binom{x_\nu}{\ell}$ has degree $\ell$ over $\mathbb F_p$ and is attached only to powers of $z$ of degree at least $\ell p^{j_\nu}$. Multiplying and extracting $z^{p^k}$ gives a digit polynomial of weight at most $p^k$. The nonnegative representative $S$ need not be smaller than $p^r$ because only its lower digits matter. Substitution into a monomial of weight at most $a$, followed by reduction via $x^p=x$, proves the digit bound.

For a map of several arguments that is additive in each separately, the pullback of $F_a(N)$ lies in $\bigotimes_i F_a(M_i)$. For each block of arguments, specialize the others to points and apply the digit bound. In the unique reduced multivariate expansion, a coefficient of an overweight monomial in this block then vanishes at every point of the other blocks, so it vanishes identically. The same separate weight bound applies to the group addition map $M\times M\to M$, since fixing one argument gives a translation. Translations obey the same proof with an extra constant factor $(1+z)^c$.

## 2. A finite system that recovers the actual module

To encode a presented $R$-module $M$, give the linear system a separate space for each $F_a(M)$ with its inclusions into $F_D(M)$. Add the constant function $1$ as a vector, all truncated multiplication maps, and the pullbacks on $F_D(M)$ of addition and of scalar multiplication by each $r\in R$. All are maps of arity at most two, including the addition pullback $F_D(M)\to F_D(M)\otimes F_D(M)$. A linear map is recorded as its mixed-variance tensor. Scalar point evaluations below are recorded as covectors, with scalar field action fixed by a marked one if a field line is included.

Suppose $h_a:F_a(N)\to F_a(M)$ are invertible linear maps preserving these data, including the inclusions. Put $h=h_D$. For each point $x\in M$ define $\phi(x)\in N$ by assigning its digit coordinates the evaluations $(h x_{i,j})(x)$, where $x_{i,j}$ on the right denotes the corresponding digit function of $N$. Any such tuple of digits defines exactly one point of $N$. For every $f\in F_D(N)$,

$$
(h f)(x)=f(\phi(x)).
$$

To see this for each basis monomial, factor it into digit variables and use preservation of the truncated product at each step. The total weight of every partial product is at most $D$. The constant is fixed and linearity handles sums. Apply the same construction to the inverse of $h$ to get $\psi:N\to M$. Since all digit functions belong to $F_D$, the composites $\phi\psi$ and $\psi\phi$ are identities. Commutativity with the two addition pullbacks forces $\phi(x+y)=\phi(x)+\phi(y)$: evaluate the intertwining equation on digit functions at $(x,y)$. The scalar pullbacks likewise give $\phi(rx)=r\phi(x)$. Thus $\phi$ is exactly an $R$-module isomorphism. Conversely every $R$-module isomorphism yields these intertwiners by the digit bound. In particular the system is fully faithful on isomorphisms, with contravariance from pullback.

For any supplied separately additive map $u:M_1\times\cdots\times M_k\to M_0$, append its pullback on $F_D$ as a tensor of valence $k+1$. Its intertwining equation, evaluated on digit functions of $M_0$, forces exactly the map-commutation equation on points. A marked $t\in M$ becomes the covector $f\mapsto f(t)$. The same digit separation reflects the exact mark. No table of every element of a module is used.

## 3. Explicit polynomial construction

An explicit finite presentation over the fixed ring $R$ gives a presentation of the underlying abelian group. Replace each free generator by generators of a fixed cyclic decomposition of the additive group of $R$, and each $R$-linear relation by its multiples by those generators. Smith normal form computes cyclic coordinates with polynomial bit complexity. Scalar maps and separately additive maps can then be evaluated in cyclic coordinates using their images of tuples of additive generators, with a polynomial number of such images for each fixed arity. In the application below these images are computed from the pure-tensor constructor and the presentation maps.

To compute pullback coefficient arrays, put

$$
I_a=\{\alpha\in\{0,\ldots,p-1\}^m\mid\sum_\nu p^{j_\nu}\alpha_\nu\le a\}.
$$

Use the product basis $\prod_\nu\binom{x_\nu}{\alpha_\nu}$ and evaluate at points whose digit tuples are in $I_a$. At the point $\beta$, the basis value vanishes unless $\alpha\le\beta$ coordinatewise, and it is one when $\alpha=\beta$. Ordering by total degree gives triangular interpolation. For several input blocks use the Cartesian product of their respective evaluation sets. Thus one evaluates polynomially many points and solves triangular linear systems to recover all promised coefficients. The dimension is at most $\binom{m+D}{D}$, polynomial for the fixed ring, and products of this count over the bounded arity remain polynomial. The explicit truncated product maps can be constructed by the same interpolation or by reducing digit exponents.

For a tensor $t\in M_1\otimes_R M_2\otimes_R M_3$, encode the five modules $M_1,M_2,M_3,M_{12},M_{123}$ and the two bilinear pure-tensor constructors. If $M_i$ have explicit free presentations, the tensor product presentation uses the pairwise generator products and the relations $r\otimes e_j$ and $e_i\otimes s$ from each factor's relations. Constructors, marks from tensor coordinates, and presentations are consequently polynomial-size. Mark the given element in $M_{123}$. On each tensor-product module a map commuting with the relevant constructor is the tensor product of the maps on the factors, because pure products generate. Therefore the resulting linear system has an isomorphism exactly when the original tensors do. All valences are at most three. Apply the published Futorny–Grochow–Sergeichuk compiler from finite systems of tensors to a single plain 3-tensor over the same field. This gives a deterministic many-one reduction to TI over $\mathbb F_p$.

For free tensor inputs there is a smaller intermediate system. Interpret the tensor as the bilinear map $M_1^\vee\times M_2^\vee\to M_3$, using the free duals. Independent invertible changes on the three factors correspond to independent invertible changes on the two arguments and the output, with inverse transpose on the first two. Hence a single bilinear pullback on the original three module ranks suffices. The sum of digit-space dimensions before compilation is $O((1+n_1+n_2+n_3)^D)$ for the fixed ring.

## 4. The converse through a residue field

Decompose $R$ into its finite local factors and select one factor $S$ with maximal ideal $\mathfrak m$ and residue field $k$. Its characteristic prime is $p$. The ideal $\mathfrak m$ is nilpotent. Choose a nonzero $s$ in its last nonzero power, using $s=1$ if $S$ is a field. Then $\mathfrak m s=0$, and no unit annihilates $s$. Thus $k\to sS$, $a\mapsto s\widetilde a$, is independent of the representative $\widetilde a$ and is an isomorphism of $S$-modules. Insert the encoded coefficients into this ideal in the selected factor and set all other components to zero. A free-tensor transporter over $R$ then reduces to the required $k$-transporter. Conversely every $k$-transporter lifts to invertible matrices over $S$, as a lifted determinant is a unit if its residue is nonzero. Use identity matrices on the remaining factors.

Finally TI over $\mathbb F_p$ reduces to TI over $k$. For completeness, in each factor $V=k^{n_i}$ encode the spaces $\operatorname{Sym}^j V$ for $1\le j\le p$ and their multiplication maps $\operatorname{Sym}^{j-1}V\otimes V\to\operatorname{Sym}^jV$. Surjectivity makes their actions unique given the action $g$ on $V$. Add the $k$-linear map $V\to\operatorname{Sym}^p V$ given by $e_i\mapsto e_i^p$ on the standard basis. Commuting with this map forces each entry of $g$ to satisfy $g_{ij}^p=g_{ij}$, by the characteristic-$p$ binomial identity. These are precisely $\mathbb F_p$ entries. Include the given tensor as another component and compile the whole system over $k$. The exponent $p$ is fixed, so the size is polynomial. This is the earlier symmetric-power field descent, stated here to give the full chain of reductions. All three classes are consequently equal.

For finite $R$ of arbitrary characteristic, prime-primary central idempotents split the modules and all tensors. Comparison reduces to a conjunction of one TI query per characteristic prime, each in its own prime field. There is no conversion between distinct prime fields in this consequence.

## Sources and scope

Grochow, Qiao and Stange define the two ring classes and study their reductions and algorithms. Their Theorem 5.1 reduces a class of Group Isomorphism instances to alternating matrix-space isometry over integers modulo prime powers, with the modulus not fixed in their general algorithm. The theorem here treats fixed rings and an arbitrary explicitly presented module tensor, including rings with higher characteristic powers than their residue fields. The weighted digit reduction can be composed with fixed-exponent versions of ring-valued encodings; its polynomial increase in the side length can be substantial. No new worst-case group-isomorphism time bound follows from that observation alone.

The DAG's Lucas theorem gives the digit coefficient identity, and the earlier symmetric-power field descent and mixed-system packing give the two ordinary-TI compilers. The combination uses only ordinary base-$p$ digits. The full function space on a module would be exponential in the number of cyclic generators. The truncated product, additions and marks retain enough information to recover the isomorphism at polynomial size.

An exact finite control checked the Lucas coefficient identity at every evaluation point for sample coordinate homomorphisms, addition and a bilinear map on $C_8\oplus C_4$ and $C_9\oplus C_3$. Multivariate Newton interpolation returned zero in all 7,793 overweight binary coefficients and all 3,522 overweight ternary coefficients. This tests the carry bounds on those instances.

- [Grochow–Qiao–Stange, Part V, Definitions 1.1–1.2 and Theorem 5.1](https://arxiv.org/html/2611.00735v1)
- [Futorny–Grochow–Sergeichuk, Wildness for tensors](https://arxiv.org/abs/1810.09219)
- [Mathlib, Lucas's theorem](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Nat/Choose/Lucas.lean)
- [Earlier same-characteristic field descent](https://github.com/Dugongue/MathProofs/tree/main/FixedCharacteristicTensorIsomorphism)
