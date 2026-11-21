# Field and invariant theory proofs for catalogue problems

## GP-0686 · Small separators need not have invariant replacements

**Theorem.** For a reductive action on a coefficient variety a degree-one separator can distinguish a point from an invariant closed set even when no invariant polynomial distinguishes them. This occurs for a fixed special-linear group on a natural coefficient representation.

Over an algebraically closed field of characteristic zero, take $V$ to be the binary homogeneous forms of degree $d\ge1$, with $\mathrm{SL}_2$ acting by change of variables. The linear coefficient of $X^d$ separates the point $X^d$ from the closed invariant set $\{0\}$. Act by the determinant-one subgroup $X\mapsto tX,\ Y\mapsto t^{-1}Y$. For every invariant polynomial $P$ and $t\ne0$, $P(t^d X^d)=P(X^d)$. These are polynomials in $t$, so evaluation at $t=0$ gives $P(0)=P(X^d)$. Thus the proposed unrestricted conversion fails. Both points lie in the same fiber of the categorical quotient. [Invariant-theoretic setting](https://arxiv.org/html/2410.14905#S4)

## GP-0711 · PIT with succinct rational-function constants

**Theorem.** For each fixed positive transcendence degree, bounded semantic degree PIT in the main variables over $K(t_1,\ldots,t_k)$, with circuit-encoded coefficient numerators and denominators, is polynomial-time many-one equivalent to unrestricted formal-degree circuit PIT over the effective constant field $K$. Denominators are promised nonzero.

For the forward reduction assign a numerator and denominator circuit over $K[t,X]$ to each gate. Addition uses $(a/b)+(c/d)=(ad+bc)/(bd)$ and multiplication uses $(ac)/(bd)$. DAG sharing gives constant gate overhead per gate after accounting for the input-constant circuits. The output is zero iff the numerator circuit is identically zero. This does not bound its degree in $t$.

For the reverse reduction take a division-free size-$s$ circuit over $K$ with $n$ variables and fan-in two. Its total degree, if nonzero, is at most $2^s$. Put $B=2^s+1$ and replace input $i$ by $t_1^{B^{i-1}}$. Each exponent has $O(ns)$ bits and hence a polynomial-size repeated-squaring circuit. Base-$B$ uniqueness makes the substitution injective on monomials of individual degree below $B$. The resulting polynomial is a single circuit-encoded rational-function constant with main-variable degree zero. This works over any effective constant field and leaves deterministic PIT itself open. [Grochow–Pitassi, proof fields and coefficient encodings](https://arxiv.org/html/2306.02184#S7.SS2)

## GP-0712 · Quasi-linear descent of finite-field IPS circuits

**Theorem.** Fix a prime $p$. Let $E=\mathbb F_p[T]/(m(T))$ for a supplied monic irreducible modulus of degree $k$. A division-free size-$s$ IPS certificate over $E$ for equations over $\mathbb F_p$ can be translated to a division-free certificate over $\mathbb F_p$ of size $\widetilde O(sk)$ in $\widetilde O(sk+L)$ bit time, for input length $L$. The certificate uses explicit power-basis field constants. The translation preserves any semantic degree bound in the original and placeholder variables.

Replace a gate by its length-$k$ vector of power-basis coordinates over the symbolic ring $R=\mathbb F_p[X,Y]$. Add coordinatewise. For multiplication use uniform Cantor–Kaltofen convolution over $R$, costing $\widetilde O(k)$ ring operations. Reduce the result modulo $m$ by reversal, truncated multiplication by the inverse of the reversed modulus, and subtraction of the product of quotient and modulus. The reversed modulus has constant coefficient $1$. Construct its truncated inverse once by Newton doubling $u\mapsto u(2-m^*u)$, valid also in characteristic two. The quotient and remainder require $\widetilde O(k)$ further coefficient operations. This uniform arithmetic gives a wiring description in quasi-linear bit time, including logarithmic gate addresses, without expanding coefficients in $X,Y$.

Induction on the circuit verifies its coordinate representation. At the root keep coordinate $0$. This projection is linear over the base field, takes $1$ to $1$, and commutes with substituting base-field axioms. It preserves both IPS identities. A certificate linear in the placeholders remains linear. [Cantor–Kaltofen](https://kaltofen.math.ncsu.edu/bibliography/91/CaKa91.pdf) · [Grochow–Pitassi](https://arxiv.org/html/2306.02184#S7.SS2)
