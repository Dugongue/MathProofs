# Prescribing isomorphism degrees for local-local Dieudonné modules

Fix a prime $p$. For a pair of objects over $\mathbb F_p$, its isomorphism-degree spectrum is the set of positive integers $d$ for which the pair becomes isomorphic over $\mathbb F_{p^d}$. This note constructs marked-coordinate module presentations whose ordinary, unmarked isomorphisms have prescribed spectra. The corresponding finite commutative group schemes are killed by $p$ and are local-local, meaning that they and their Cartier duals are connected.

**Theorem.** For positive $r,s$ and $A,B\in\operatorname{GL}_n(\mathbb F_p)$ there are explicit local-local Dieudonné modules $M(A),M(B)$ killed by $p$, each of dimension $(r+s)n$. Over $K=\mathbb F_{p^d}$ they are isomorphic if and only if
$$
 A^L\sim_{\mathbb F_p} B^L,\qquad L=\frac{d}{\gcd(d,r+s)} .
\tag{1}
$$
Consequently, given a nonempty finite list of arbitrary positive integers $b_1,\ldots,b_u$, including integers divisible by $p$, one can construct a pair of such modules with spectrum exactly
$$
\{d\ge1:\ b_i\mid d\text{ for some }i\}.
\tag{2}
$$
Writing $D=\operatorname{lcm}_i b_i$, one can take the module dimension at most $(D+1)D\,\tau(D)^2$, where $\tau(D)$ counts divisors. The construction is explicit in the numerical value of $D$. For (1), testing a specified degree $d$ requires only matrix powering over the prime field and ordinary similarity, with complexity polynomial in $n$, the lengths $r,s$ and $\log d$ in the prime-field arithmetic model. It requires no arithmetic in $\mathbb F_{p^d}$.

## 1. A cyclic semilinear obstruction encoded by two nilpotent chains

For a perfect extension $K$ of $\mathbb F_p$ let $\phi(x)=x^p$. Take two chains with a common top $T\simeq K^n$ and a common bottom $W\simeq K^n$. The $F$-chain has $r-1$ intermediate copies, the $V$-chain $s-1$. On each $F$-arrow use coordinatewise $\phi$, including the final arrow into $W$. On each $V$-arrow use $\phi^{-1}$ except at its last arrow, where use $A\phi^{-1}$. Define $F$ to kill the $V$-intermediates and the bottom, and $V$ to kill the $F$-intermediates and the bottom. This covers a chain of length one by an arrow directly from $T$ to $W$. The maps are nilpotent and $FV=VF=0$, so the module is killed by $p$ and satisfies the Dieudonné relations. Its dimension is $(r+s)n$.

The top quotient $M/(FM+VM)$ and the bottom $\ker F\cap\ker V$ are intrinsic. They identify with $T$ and $W$ in the displayed model. A module isomorphism from $M(A)$ to $M(B)$ induces some $P$ on the top and necessarily $\phi^r(P)$ on the bottom, since $F^r$ induces the map $\phi^r$ from top to bottom. The two maps $V^s$ on the top are $A\phi^{-s}$ and $B\phi^{-s}$. Compatibility gives
$$
 \phi^r(P)A=B\phi^{-s}(P)
 \quad\Longleftrightarrow\quad
 \phi^{r+s}(P)=B P A^{-1}.
\tag{3}
$$
The entries of $A,B$ are fixed by $\phi$. Conversely every invertible solution $P$ gives a module isomorphism by taking $P$ at the top, $\phi^i(P)$ at the $i$th $F$-intermediate, $\phi^{-j}(P)$ at the $j$th $V$-intermediate, and $\phi^r(P)$ at the bottom. The last $V$-equation is exactly (3). Thus the reduction to a semilinear matrix equation is exact even though arbitrary module isomorphisms may mix the displayed summands.

These are two-chain instances of circular-word constructions over an algebraic closure. The matrix coefficient retains rational form data, so the question here is how that data changes over every finite extension. [Kraft word classification and Dieudonné equivalence](https://www2.math.upenn.edu/~chai/HObook/current/ch2-Kraft_12aug2024.pdf) · [Mondal, Dieudonné theory via classifying stacks](https://arxiv.org/abs/2405.12967)

## 2. Norm descent to an ordinary similarity test

Let $a=r+s$, $g=\gcd(a,d)$, $L=d/g$, and let $\tau=\phi^g$. On $K$ this generates its degree-$L$ automorphism group over $\mathbb F_{p^g}$. Write $\phi^a=\tau^u$ with $u=a/g$ coprime to $L$. Iterating (3) $L$ times shows that ordinary similarity of $A^L$ and $B^L$ is necessary. If the powers are similar over $K$, their rational canonical forms over $\mathbb F_p$ agree. Indeed ranks of all powers of every base irreducible polynomial in a matrix are unchanged by field extension and determine its base elementary divisors. A conjugacy over $\mathbb F_p$ is therefore necessary as stated in (1).

Suppose conversely that such a conjugacy exists. First conjugate $B$ over $\mathbb F_p$ so that $A^L=B^L=C$. This changes the equation (3) only by an invertible base coordinate change. The group $G=\operatorname{Cent}_{\operatorname{GL}_n}(C)$ over $\mathbb F_{p^g}$ is connected: as a variety over an algebraic closure it is the nonempty open set of invertible elements in the linear matrix commutant of $C$. Also $A,B\in G$. Choose $k$ with $uk\equiv1\pmod L$, with $k=0$ allowed for $L=1$.

Over an algebraic closure apply Lang's theorem to $G$ and its $\mathbb F_{p^g}$-Frobenius $\tau$. Obtain $X,Y\in G$ with $\tau(X)=B^k X$ and $\tau(Y)=A^k Y$. This is the left-multiplication form of Lang surjectivity, obtained from the usual form by inversion. Then $P=XY^{-1}$ satisfies
$$
\tau(P)=B^k P A^{-k}.
$$
Iterate $L$ times to get $\phi^d(P)=C^kPC^{-k}=P$. Thus $P$ is defined over the specified field $K$. Iterating $u$ times and using $uk\equiv1\pmod L$ and $PC=CP$ now gives (3). This proves (1) over precisely the original finite extension. The centralizer argument is an explicit norm-descent proof for constant weights rather than an appeal to a splitting field of unknown degree. [Lang, Algebraic groups over finite fields](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf)

All original module presentations are over $\mathbb F_p$. Base change in classical Dieudonné theory identifies their extensions to $K$ with scalar extension and semilinear operators as above. The local-local condition remains true over every extension. Thus (1) applies verbatim to the isomorphism spectra of the associated group schemes. With a contravariant convention a module witness corresponds to a group-scheme witness in the opposite direction; spectra and numbers of isomorphisms are unaffected.

## 3. Modular permutation matrices realize every finite union of multiples

We construct a pair of permutation matrices $A,B$ over $\mathbb F_p$, with all cycle lengths dividing $D$, such that for every integer $j\ge1$ their $j$th powers are similar exactly when $b_i\mid j$ for some $i$. Permutation matrices allow $p$ to divide $D$ with no semisimplicity assumption.

First, similarity of permutation matrices over any field detects their cycle lengths. For a permutation matrix $P$ with $c_s$ cycles of size $s$, the dimension of $\ker(P^j-I)$ is its number of cycles after the $j$th power:
$$
 f_P(j)=\sum_s c_s\gcd(s,j)=\sum_{t\mid j}\varphi(t)\sum_{s\colon\,t\mid s}c_s .
\tag{4}
$$
The kernel consists of the constant coordinates on each cycle, also when the characteristic divides its length. Möbius inversion in $j$ recovers every sum of the $c_s$ over multiples of $t$ from the kernel dimensions. Inversion over the divisor lattice then recovers the individual $c_s$. It suffices to use $j\mid D$ when all cycle lengths divide $D$. Conversely matching cycle types give permutation conjugacy. We can therefore test similarity of $A^j,B^j$ by comparing the numbers of fixed points of their further powers, since those numbers are another invertible divisor transform of the cycle counts.

Call a divisor $d_0$ of $D$ good if some $b_i$ divides it. This is an upward-closed set of divisors. Let $\mathcal B$ be the set of maximal bad divisors. Set $h(d_0)=D$ for $d_0\in\mathcal B$ and $h(d_0)=0$ otherwise. Define the signed cycle multiplicities
$$
 x_s=\frac1s\sum_{c\mid s}\mu(s/c)h(c),\qquad s\mid D ,
\tag{5}
$$
where $\mu$ is the number-theoretic Möbius function. They are integers because $s$ divides $D$. Put the positive cycle counts in $A$ and the negative counts, with their signs reversed, in $B$. Their numbers of vertices are equal, since $\sum_s sx_s=h(D)=0$. Their common dimension is at most $D\tau(D)^2$, by summing absolute values in (5). A common trivial cycle can be used if all multiplicities are zero. In that case every divisor is good and one may instead take identical one-dimensional weights.

For a further exponent $v$, the fixed-point count difference of $A^v,B^v$ equals
$$
\sum_{s\mid \gcd(v,D)}s x_s=h(\gcd(v,D)).
$$
Write $g_0=\gcd(j,D)$. The exact set of gcds $\gcd(jt,D)$ for $t\ge1$ consists of the divisors of $D$ divisible by $g_0$. For example the divisor $c$ in this set is obtained with $t=c/g_0$, using $\gcd(j/g_0,D/g_0)=1$. It follows that all further fixed-point counts of $A^j,B^j$ agree if and only if no maximal bad divisor is a multiple of $g_0$. This is exactly the condition that $g_0$ is good. By (4), this is similarity of their $j$th powers. The count construction is the elementary cyclic fixed-point mark transform. The use of (4) keeps it valid in characteristic $p$ even for cycles whose lengths are divisible by $p$.

Finally take $r=1,s=D$, so $a=r+s=D+1$ is coprime to every desired divisor $b_i$. In (1) removing $\gcd(d,a)$ from $d$ preserves divisibility by every $b_i$. Thus (1) gives (2) with the advertised dimension bound. The always-isomorphic case can also use identical modules of chain lengths one and one.

## Finite controls

Exhaustive checks over all pairs of matrices in $\operatorname{GL}_2(\mathbb F_2)$, extension degrees $1,2,3$, and chain-length sums $2,3,4,5$ agreed with (1) in all 432 cases. A second check used every nonempty subset of the divisors of each $D\le 24$ as the supplied divisibility generators, including nonminimal lists. The resulting 622 inputs gave 23,196 exact cycle-signature checks, for all extension degrees $1\le d\le 2D$ on each input. These computations are finite controls for the written proof.

## Scope and relation to isomorphism over extensions

The construction gives arbitrary finitely generated divisibility spectra inside the local-local and killed-by-$p$ class, while deciding an individual spectrum test by ordinary matrix similarity over a prime field. It makes no claim that all finite Dieudonné modules have these spectra. Its comparison points are classical circular words and finite-field norm descent, and earlier work encoding extension spectra in tensor coordinates. The extra step here is the two-nilpotent-chain realization and the fixed-point mark construction that works in modular characteristic. Publication priority for this exact combination remains unconfirmed. [Grochow–Qiao–Stange–Sun, tensor isomorphism over commutative rings](https://arxiv.org/abs/2611.00735)
