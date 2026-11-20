# Minimum tensor dimension for a principal extension spectrum

Fix a finite field $F=\mathbb F_q$ and an integer $k>1$. We consider pairs of based, dimension-$n$ finite étale $F$-algebras through their full, unmarked three-tensor multiplication tables. The required extension spectrum is all positive degrees $m$ for which $k\mid m$. Let $n_{\mathrm{GL}}$ be the least side dimension realizing that spectrum by ordinary tensor isomorphism. Let $n_{\mathrm{both}}$ also require determinant one on all three modes at every successful degree.

Let $R$ consist of the maximal prime powers dividing $k$. For a two-part partition $R=I\sqcup J$, write $s_I=\sum_{r\in I}r$ and $s_J=\sum_{r\in J}r$. Empty parts are allowed. Define

$$
B(k)=\min_{I\sqcup J=R}\max(s_I,s_J),\qquad
C(k)=\min_{I\sqcup J=R}\min\{\max(s_I+2,s_J),\max(s_I,s_J+2)\}.
$$
For $k\equiv2\pmod4$, also define
$$
U(k)=\min_{I\sqcup J=R,\ 2\in I}\max(s_I+2,s_J),\qquad
V(k)=\min_{I\sqcup J=R,\ \{2,3\}\subseteq I}\max(s_I+1,s_J+2).
$$

The minimum over an empty collection is infinity. In particular, $V(k)$ is finite exactly when 3 is a maximal prime power dividing $k$.

**Theorem.** Over every finite field, $n_{\mathrm{GL}}=B(k)$. The dimension for realizing both spectra is

$$
n_{\mathrm{both}}=\begin{cases}
B(k) & \text{if }q\text{ is even or }k\text{ is odd},\\
C(k) & \text{if }q\text{ is odd and }4\mid k,\\
\min\{U(k),V(k)\} & \text{if }q\text{ is odd and }k\equiv2\pmod4.
\end{cases}
$$

In all cases $B(k)\le n_{\mathrm{both}}\le B(k)+2$. The upper gap is attained at $k=2$ over odd fields. For $k=462$ over an odd field, $B(k)=12$, $U(k)=14$, and $V(k)=13$. Factor degrees $(6,7)$ on one side and $(2,11)$ on the other attain dimension 13 after the orientation adjustment below.

## Multiplication tensors and Frobenius

For finite-dimensional commutative unital algebras $A,B$ over a field, a transporter of their multiplication tensors has the form

$$
h(xy)=f(x)g(y),
$$

where $f,g,h:A\to B$ are invertible linear maps. The two input factors of the tensor are duals, which inverts their determinants and leaves the determinant-one condition identical. Write $u=f(1_A)$, $v=g(1_A)$. The identities $h(x)=f(x)v=u g(x)$ show that multiplication by $u$ and by $v$ is surjective, so both are units. The map $\phi=(uv)^{-1}h$ is a unital algebra isomorphism, since

$$
\phi(xy)=(uv)^{-1}f(x)g(y)=\phi(x)\phi(y).
$$

For an invertible element $z\in B$, put $N(z)=\det(M_z)$, where $M_z$ is multiplication by $z$. Then $(f,g,h)=(M_u\phi,M_v\phi,M_{uv}\phi)$, and

$$
\det\phi=\frac{\det f\det g}{\det h}.
$$

Conversely, any algebra isomorphism gives a transporter by taking all three maps equal to it. The argument is valid over every extension, with no restriction on the support or shape of the tensor maps.

An étale algebra over $F$ is a product of fields $\mathbb F_{q^d}$. After scalar extension to $\mathbb F_{q^m}$, a degree-$d$ factor becomes $\gcd(d,m)$ factors of degree $d/\gcd(d,m)$. One way to see this is to list the $d$ embeddings over an algebraic closure: $q$-Frobenius is a $d$-cycle, and taking its $m$-th power yields the factors over the extension. Isomorphism over the extension is therefore equality of the powered multisets of cycle lengths. Equivalently, for a permutation matrix of Frobenius the basis transforms by finite Fourier transform on each cycle in characteristic zero, and the multiplicity of each primitive $d$-th root is the total number of cycles of lengths divisible by $d$. Keeping the cycles themselves also works in modular characteristic.

## Sharp ordinary lower bound and construction

For any pair realizing the spectrum, let $L$ be the least common multiple of all factor degrees on both sides. Both algebras are split at degree $L$, so $k\mid L$. Each $r\in R$ therefore divides at least one factor degree. Assign it to one such factor. Within any factor, the assigned prime powers have distinct primes, so their product divides the factor degree. That product is at least their sum for a nonempty assignment. For two integers at least 2, $ab\ge a+b$, and iterating gives the inequality for any larger group. Factors with an empty assignment have no cost in the sum. Each side dimension is therefore at least the sum of the prime powers assigned to that side. Taking the best partition gives $n\ge B(k)$.

Conversely choose a minimizing partition and put one degree-$r$ field on its assigned side for each $r\in R$. Pad each side to dimension $B(k)$ by copies of $F$. After an arbitrary degree $m$, every remaining factor degree greater than 1 is a power of its designated prime. The remaining primes are disjoint between the two sides. Thus the profiles agree exactly when no remaining factor has degree greater than 1, which occurs precisely when all $r\in R$ divide $m$. This proves the asserted spectrum and the lower bound with the same unmarked tensor model.

## Determinant one and the sharp even-prime correction

Let $G_A$ be the matrix of the trace pairing $(x,y)\mapsto\operatorname{Tr}_{A/F}(xy)$ in the chosen basis of $A$. It is nondegenerate because the algebra splits over an algebraic closure. For odd $q$, the square class of $\det G_A$ is the sign of the Frobenius permutation on the geometric factors, in the sense that

$$
(\det G_A)^{(q-1)/2}=(-1)^{\#\{\text{even-degree field factors of }A\}}.
$$

Indeed, if $E$ has as rows the evaluations of the basis in the individual embeddings, then $G_A=E^{\mathsf T}E$. Entrywise raising $E$ to the $q$-th power permutes its rows by Frobenius. This gives $(\det E)^{q-1}=\operatorname{sgn}(\mathrm{Frob})$ and the displayed identity. In even characteristic every nonzero element of $F$ is a square. Whenever the two Gram determinants have the same square class, rescale one basis vector on one side by an element of $F^\times$ to make the actual determinants equal. At every successful degree in the constructions below, both algebras are split. Every algebra isomorphism then has determinant whose square is 1 by preservation of the trace pairing. In odd characteristic, composition with a transposition of two primitive idempotents changes the sign, so a determinant-one isomorphism is available. In characteristic two, a scalar whose square is 1 already equals 1.

If $q$ is even, the ordinary optimal construction thus realizes both spectra. If $k$ is odd, its factor degrees are all odd, so this also holds over odd $q$.

Now take $q$ odd and $k$ even. Any realizing pair must have at least one determinant-one transporter, and hence a determinant-one algebra isomorphism. Trace-pairing preservation implies the based Gram determinants over $F$ are equal, since they agree in the extension. The total number of even cycles across both algebras is therefore even. In the lower-bound assignment above one even cycle was used for the maximal power of 2 dividing $k$. There is at least one additional, distinct even cycle somewhere in the pair. This cycle has only odd prime powers assigned to it. Its length is at least 2 plus the sum of the assigned powers. For an empty assignment its length is at least 2. Otherwise, if the product of the odd powers is $P$, the length is a multiple of $2P$, and $2P\ge 2+P\ge 2+\sum r$. Thus one side pays at least 2 beyond its assigned sum, proving $n_{\mathrm{both}}\ge C(k)$.

For the upper bounds, start with any partition and add one degree-2 field factor on the chosen side before padding by $F$. The two total even-cycle counts then have the same parity. Adding the degree-2 field on the side with the original even factor works for every even $k$, because the other side has no residual factors of even degree. If $4\mid k$, adding on the opposite side also works. At an odd extension degree, the original power-of-2 factor remains of degree at least 4, and the added degree-2 factor cannot match it. At an even extension degree, the added factor splits, so the original power-of-2 factor must split to achieve equality. At every degree the odd-prime parts still have disjoint supports. Equality is therefore equivalent to $k\mid m$, and all factors split at those degrees. The trace-pairing basis adjustment gives determinant-one transporters at all of them. This proves the upper bound $C(k)$ when $4\mid k$, and the upper bound $U(k)$ when $k\equiv2\pmod4$.

## The case of exactly one factor of 2

Assume $q$ is odd and $k\equiv2\pmod4$. To attain the additional option $V(k)$, take a partition with $2,3\in I$. Replace the designated degree-2 and degree-3 factors on side $I$ by one degree-6 field. Add a degree-2 field on side $J$, then pad the sides to a common dimension. The costs are precisely $s_I+1$ and $s_J+2$ before padding. At an odd extension degree the degree-6 factor either stays a degree-6 factor or produces three degree-2 factors, so it cannot match the single degree-2 factor on side $J$. At an even degree the added factor splits, and the degree-6 factor splits exactly when 3 also divides the extension degree. If 3 does not divide that even degree, the resulting degree-3 factors have no counterpart on side $J$. All other primes are assigned to disjoint sides as before. Thus the two sides match exactly when $k\mid m$, at which point both split. The even-cycle counts are both one, so the orientation adjustment applies.

For the matching lower bound, take an arbitrary realizing pair of dimension $n$ and choose an assignment of maximal prime powers to field factors as in the ordinary lower bound. Name the sides $I,J$ so that 2 is assigned to side $I$. Put $a=n-s_I$ and $b=n-s_J$. These are nonnegative. If $a\ge2$, then this partition gives $U(k)\le n$. If $b\ge4$, move 2 to side $J$ in the partition and pay the extra 2 there, again giving $U(k)\le n$. It remains to treat $a\le1$ and $b\le3$.

Any even cycle other than the cycle assigned 2 costs at least 2 beyond the sum of its assigned powers, as in the parity lower bound. Thus there is exactly one even cycle on side $I$. Equal parity requires one on side $J$, and the slack bound allows at most one. If the even cycle on side $I$ is assigned only 2, it has length 2, since its length is even and at most 3. If it also has assigned odd powers of total $S$, its length is at least twice their product and hence at least $2S$. Its cost beyond the assigned sum is at least $S-2$. Since $a\le1$, this forces one assigned odd power, equal to 3, and length 6. In that case $a\ge1$ and $b\ge2$, so the current partition gives $V(k)\le n$.

Now suppose the even cycle on side $I$ has length 2. If the even cycle on side $J$ also had length 2, an odd extension degree divisible by all the odd factor degrees would split those factors and leave one degree-2 factor on each side. Since the dimensions agree, the ordinary profiles would agree, contradicting the required spectrum. The even cycle on side $J$ therefore has length at least 4. With no assigned prime powers this would cost at least 4, exceeding $b$. With assigned odd powers of sum $S$ its length is at least $2S$, using the same product bound. Its excess cost is at least $S$, so $b\le3$ forces precisely the assigned power 3 and length 6. Reassign 2 to side $J$ in the partition. The cost $s_J+3$ fits because $b\ge3$, and the cost on side $I$ is $(s_I-2)+2=s_I$. The new partition again gives $V(k)\le n$, completing the lower bound.
## Source and scope

The source analogy is Masullo's use of transform coordinates in §1.2, especially the Fourier and Poisson steps on PDF pages 16–19, the Mellin diagonalization on PDF page 18 and the Deninger discussion in §1.2.11. Here the exact finite decomposition is into Frobenius cycles, with one maximal prime-power requirement assigned to a concrete factor. The dimension argument and the trace orientation correction are finite algebra and use no analytic claim from the manuscript. [Alessandro Masullo, *The Music of the Primes*, public draft](https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=16)

The project already developed the general étale extension-spectrum calculus, the dimension bound for a disjunction of prime divisibility tests, and a general doubling construction for orienting étale tables. The result here optimizes the dimension for a conjunction of prime-power tests and gives the exact special-linear orientation cost in every case. The minimum is specific to finite étale multiplication tensors. Verification is by the mathematical proof above. [Earlier extension-spectrum results](https://github.com/Dugongue/MathProofs/blob/main/VertexCoverAndExtensionSpectra/Spectra.md) · [Grochow and coauthors, Open Question 1.9](https://arxiv.org/html/2306.03135v2)
