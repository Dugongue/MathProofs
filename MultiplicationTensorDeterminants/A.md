# Exact determinant-one descent for finite étale multiplication tensors

Let $k=\mathbb F_q$, and let $A$ and $B$ be nonzero finite étale $k$-algebras of the same dimension, each with a fixed ordered $k$-basis. Write $\Delta_A$ and $\Delta_B$ for the actual determinants of their trace Gram matrices in those bases. The matrices are nonsingular. Let $K_m=\mathbb F_{q^m}$. All basis conventions extend to $K_m$.

**Theorem.** Suppose $A$ and $B$ are nonisomorphic over $k$. For every $m\ge1$, the following are equivalent.

1. Their multiplication tensors become equivalent over $K_m$ by three determinant-one maps.
2. Their algebras become isomorphic over $K_m$, and $\Delta_A=\Delta_B$ in $k$.

The discriminants are based values, including their squares from changes of basis. Equality of square classes alone suffices if the original bases may be chosen. In particular a pair of distinct finite étale algebras either has its entire ordinary extension spectrum as its determinant-one spectrum, or has empty determinant-one spectrum. The theorem includes characteristic two.

## Proof

For ordinary multiplication isotopy on three independent legs, the associative unital normal form writes a transporter as $(L_a\sigma,R_b\sigma,L_aR_b\sigma)$, with $a,b$ units and $\sigma$ an algebra isomorphism. To see this, let $X,Y,Z$ satisfy $Z(xy)=X(x)Y(y)$ and take $a=X(1)$ and $b=Y(1)$. Evaluating at 1 gives $Z(x)=X(x)b=aY(x)$. Thus multiplication by $a$ on the left and by $b$ on the right is surjective, so both are units in a finite-dimensional algebra. The map $a^{-1}Z(-)b^{-1}$ is bijective, unital and multiplicative. Its based determinant is $\det X\det Y/\det Z$. Consequently determinant-one tensor equivalence is exactly existence of an algebra isomorphism of based determinant 1. An algebra isomorphism of determinant 1 works on all three legs.

Every algebra isomorphism preserves the trace pairing. If $X$ is its matrix, then $X^{\mathsf T}G_BX=G_A$, and hence
$$
\Delta_A=(\det X)^2\Delta_B.
$$
The trace matrices commute with base change since the trace is that of a multiplication operator. A determinant-one isomorphism therefore forces equality of the original discriminants. When they agree, the only possible determinants of an isomorphism are $+1$ and $-1$. They coincide in characteristic two.

It remains to repair sign in odd characteristic. A finite étale algebra has a Frobenius permutation on its geometric points. Its cycle lengths are the field-factor degrees. Passing to $K_m$ powers Frobenius by $m$, so each length $d$ becomes $\gcd(d,m)$ cycles of length $d/\gcd(d,m)$. If either powered profile has no repeats, no original cycle split. If the powered profiles agree and lack repeats, both original profiles agree, contradicting nonisomorphism over $k$. Thus the common powered profile has a repeated degree.

Algebra automorphisms correspond to permutations of geometric points commuting with the appropriate Frobenius. Their based determinants are the signs of those permutations, by using the primitive idempotent basis after splitting. An even cycle gives an odd commuting rotation. Two repeats of any odd degree give an odd permutation commuting with Frobenius by interchanging the two cycles in phase. Two repeats of even degree already give an odd rotation. Thus a newly acquired isomorphism in odd characteristic always lands in an algebra with an odd automorphism. Compose with it if necessary to repair determinant $-1$. This realizes determinant 1 and proves the theorem. [Finite étale schemes and Galois sets](https://stacks.math.columbia.edu/tag/04JI)

## The extension spectrum inside a single ordinary orbit

Fix an ordinary multiplication orbit of $A$ over the base field. The three determinant homomorphisms on its product of general linear groups define the ratio $\det X\det Y/\det Z$. The multiplication stabilizer has determinant image $(\ell\delta,r\delta,\ell r\delta)$, where $\ell$ and $r$ range independently over all nonzero scalars by surjectivity of finite-field norms, and $\delta$ ranges over determinants of algebra automorphisms. Therefore the determinant-one orbits in this ordinary orbit are indexed by $k^\times/D_A$, where $D_A$ is the determinant subgroup of the automorphism group. Extension sends a ratio class to its class in $K_m^\times/D_{A\otimes K_m}$.

For distinct odd original degrees and odd $q$, one has $D_A=\{1\}$. Two unequal base classes merge if and only if their ratio is $-1$ and $m$ shares a prime divisor with an original degree. Indeed powering preserves odd lengths and creates a repeated degree exactly when a cycle splits. The first merging degree is the least prime dividing any original degree, or infinity if there is none. If $D_A$ already contains $-1$, its image contains both signs over every extension and the base classes remain distinct. Characteristic two also preserves every ratio class because every permutation determinant is 1.

For example the degree profile $(3,5)$ over any odd finite field has two distinct determinant-one classes with ratio quotient $-1$ that merge exactly over extension degrees divisible by 3 or 5. In contrast, the profile $(1,3)$ gives a first merging degree of 3 and no mergers over any power of two.

## Sharp first dimensions for prescribed extension tests

Fix a nonempty finite family of extension degrees $m_i>1$. Here one may choose the original bases. Let $H$ be a set of primes meeting the prime support of every $m_i$, and set
$$
D=\frac12\min_H\prod_{p\in H} (2p).
$$
The first dimension of two nonisomorphic finite étale algebras whose multiplication tensors become determinant-one equivalent over **every** tested extension is
$$
\begin{cases}
3 & q\text{ odd and all }6\mid m_i,\\
4 & q\text{ odd and all }2\mid m_i\text{ but some }3\nmid m_i,\\
D & \text{otherwise}.
\end{cases}
$$

To recall why $D$ is the ordinary minimum, write $z_d$ for the signed difference of cycle counts and $w_d=dz_d$. Define $F(v)=\sum_{d\mid v}w_d$ on a finite prime-exponent box containing the supported lengths and all the test degrees. Agreement after test $m_i$ means $F(v)=0$ at every multiple of $m_i$, since the fixed-point counts of powers recover all cycle counts. Take a coordinatewise maximal $v$ with $F(v)\ne0$. The set $H$ of coordinates strictly below the top of the box meets every test. Split the degrees along each $p\in H$ at its coordinate in $v$. Inclusion-exclusion shows that the signed sum on each of the $2^{|H|}$ resulting disjoint boxes equals $F(v)$ up to sign, since all strict increases of $v$ have mark zero. The all-high box has every degree divisible by $\prod_{p\in H}p$, so its nonzero signed sum has absolute size at least this product. The positive signed mass, at most the common dimension, is half the total absolute mass. This gives the lower bound $D$.

For the upper bound, take a minimizing $H$, write $Q=\prod_{p\in H}p$, and set $z_d=(-1)^{|H|-\omega(d)}Q/d$ for $d\mid Q$, zero otherwise. The positive and negative profiles have dimension $D$. For any prime $p\in H$ dividing a test degree, the terms at $d$ and $pd$ with $p\nmid d$ cancel after that test. The two profiles are distinct before extension.

For odd $q$, the square class of the trace discriminant is the sign of Frobenius. Indeed, if $E$ is the matrix evaluating a basis at all geometric points, then $\Delta=(\det E)^2$ and $(\det E)^q=\operatorname{sgn}(\mathrm{Frob})\det E$ by row permutation. Thus $\Delta^{(q-1)/2}=\operatorname{sgn}(\mathrm{Frob})$. Two equal-dimensional profiles have the same sign if and only if their numbers of cycles have the same parity. When the square classes agree, scaling the first basis vector of one algebra realizes equality of the based values. In characteristic two the square map on the finite field is bijective, so such scaling is possible for every pair.

The parity-cube witness has cycle-count difference $\sum_{d\mid Q}z_d=\prod_{p\in H}(1-p)$. This is even whenever $H$ contains an odd prime. Thus the ordinary minimum is attained with compatible orientations unless $H=\{2\}$ in odd characteristic. The singleton $\{2\}$ is feasible precisely when all tests are even, and then it is minimizing. Its dimension-2 pair consists of two fixed points versus a transposition. Their Frobenius signs differ. In dimension 3 the only possibly compatible distinct pair is one 3-cycle versus three fixed points, and it agrees precisely when all tests are multiples of 3. If that fails, two 2-cycles versus four fixed points attain dimension 4 for any even tests. These cases prove the sharp formula.

## Prior work and verification

The determinant-ratio normal form and ordinary sharp schedule bound were established in the preceding project work. The sign-discriminant relationship is classical. The new deductions here are the exact determinant-one extension spectrum, the merging rule inside one ordinary orbit, and the dimension-3 or dimension-4 exception for schedules of even degrees. Priority for the combined statements remains open. [Discriminant of finite étale algebras and alternating actions](https://arxiv.org/abs/0912.3405) · [Goldstein, Guralnick, Howe, and Zieve on twists over extension fields](https://arxiv.org/abs/0801.4614)

The full descent and dimension arguments are written above. The Lean source formalizes the profile rigidity, the squared determinant identity and the sign-repair implication. The finite control enumerates profiles and directly verifies the cutoff and sign formulas modeled by permutations. [Lean source](A.lean) · [Exhaustive finite control](A-Check.py)
