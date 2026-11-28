# Odd-arity extension of the rounding argument

The application uses the affine integer programming (AIP) criterion and the hypotheses stated below.

This is a direct extension of the audited ternary rounding theorem. It is an analytical corollary, not an additional computationally verified result. No claim that the odd-arity statement settles a published open problem is made. It adds no claim about even arities.

## Theorem

Fix an odd integer r>=3. Let Z_{r,1} be the r-ary relational structure on Z with relation

\[
x_1+\cdots+x_r=1.
\]

Let B be a finite nonempty structure with b elements and one r-ary relation, satisfying

\[
\#\{c:R^B(a,\ldots,a,c)\}\le1
\]

for every a, where a occurs r-1 times. There are no additional prescribed unary relations, constants, or endpoint values for the rounding map. Let T be the resulting partial diagonal transition.

For a positive integer d, write E_d for the r-ary sum-one structure on Z/dZ and let

\[
A_d=E_d\times\operatorname{NAE}_r.
\]

Then Z_{r,1} -> B if and only if B admits one of the following:

1. An injective homomorphism E_d -> B.
2. An injective homomorphism A_d -> B.

Here d is odd, every prime factor of d divides r (equivalently d divides r^N for some N), and the injective witness domain has at most b elements. The case d=1 is included. A uniform presentation by A_d is always possible with d<=b and hence at most 2b elements: in the first branch forget the sign coordinate before applying the injection.

Existence can be tested with at most

\[
b^2+(2^r-2)b^{r-1}
\]

relation-membership queries, after routine functional-graph work. This is O_r(b^{r-1}) for fixed r. Any successful candidate gives an explicit rounding map depending on n modulo d and, when needed, on n<=0 versus n>=1.

## Proof changes from the ternary case

Set

\[
F(n)=1-(r-1)n.
\]

It preserves the relation because r-(r-1)=1. Every homomorphism h satisfies hF=Th. Composing with F^b puts the image on cycles of T, where T is injective.

If h(x)=h(y)=a and u=(x+y)/2 is integral, use the source relation tuple consisting of (r-1)/2 copies of x, (r-1)/2 copies of y, and the last entry F(u). Its first r-1 images are all a. Diagonal uniqueness and injectivity of T give h(u)=a.

Thus the same midpoint-closure argument applies: every fibre is an arithmetic interval with odd step. For a colour on a T-cycle of length ell,

\[
F^{2\ell t}(x)
=\frac1r+(r-1)^{2\ell t}\left(x-\frac1r\right).
\]

The fixed point 1/r lies strictly between 0 and 1. The fibres are therefore unbounded toward positive infinity if they meet n>=1, and toward negative infinity if they meet n<=0. The exact-cover argument removes finite exceptional prefixes on each side.

Consequently h factors through A_m for some odd m. The map

\[
n\longmapsto(n\bmod m,\operatorname{signclass}(n))
\]

is surjective on relation tuples: every mixed sign assignment and every modular sum-one tuple can be lifted by choosing a positive representative sufficiently large and solving for one negative representative.

Factor m=m_r q, where every prime factor of m_r divides r and gcd(q,r)=1. Fix the q-coordinate to 1/r in Z/qZ. Chinese remaindering gives A_{m_r} -> A_m -> B.

## The diagonal transition on the source is a single cycle

On E_m for an odd m supported on primes dividing r, the transition is G(x)=1-(r-1)x. For every prime p dividing m, p is odd and p divides r. Its iterate gives

\[
G^t(x)-x
=\frac{\bigl((1-r)^t-1\bigr)(rx-1)}r.
\]

Since rx-1 is a p-adic unit, and

\[
v_p((1-r)^t-1)=v_p(r)+v_p(t),
\]

the least positive return time modulo m is exactly m. Thus G is one m-cycle.

The diagonal transition on A_m is

\[
S(x,s)=(G(x),1-s).
\]

Because m is odd, S is a single 2m-cycle.

A homomorphism into B intertwines S and T, so its image is one T-cycle of length k dividing 2m. Therefore k=d or k=2d for a divisor d of m.

If k=d is odd, the map factors through the residue projection A_m -> E_d and is injective on E_d. If k=2d, it factors through A_m -> A_d and is injective on A_d. Both projections are surjective on relation tuples, by lifting r-1 residues freely and determining the last. The induced maps are therefore homomorphisms.

Their images have k<=b elements.

Conversely, E_d receives n -> n mod d, and A_d receives the sign-and-residue map. Either injection therefore gives Z_{r,1} -> B.

## Algorithm

Construct T, using at most b^2 queries. Consider only cycles of length k=d or 2d, where d is odd and all prime factors of d divide r.

For a selected cycle, use the corresponding source E_d or A_d and map one fixed source vertex to one fixed cycle vertex, then follow the diagonal transitions.

Only one phase needs checking. The source transition is an automorphism, and every other phase is obtained by precomposing with one of its powers. Thus all phase choices succeed or fail together.

The larger source A_d has exactly (2^r-2)d^{r-1} ordered relation tuples. For E_d there are only d^{r-1}. Summing over disjoint target cycles,

\[
\sum_{\text{cycles}}(2^r-2)d^{r-1}
\le(2^r-2)\sum_{\text{cycles}}k^{r-1}
\le(2^r-2)b^{r-1}.
\]

This proves the query bound.

## Scope and edge cases

No symmetry of the target relation is used. The integer source and the finite source witnesses are symmetric.

The case d=1 in the first branch is a target loop. The case d=1 in the second branch is an injective copy of NAE_r.

When r is an odd prime, the only possible d are powers of r. For composite odd r, d can have different powers of the primes dividing r.

The proof deliberately uses oddness of r at the midpoint step and at the single-cycle step. It establishes no analogous result for even r.
