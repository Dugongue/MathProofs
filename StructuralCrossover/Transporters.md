# How long can a determinant-one quiver isomorphism take to descend?

Let $Q$ be any finite labeled quiver, including quivers with loops, over a fixed finite field $k=\mathbb F_q$. Two representations $V,W$ are given by vertex dimensions and arrow matrices in specified bases. Fix a subset $C$ of vertices. A permitted isomorphism intertwines each labeled arrow and has determinant one at each vertex in $C$. Its **extension spectrum** is the set of positive integers $t$ for which such an isomorphism exists over $\mathbb F_{q^t}$. Put $S=\sum_v\dim V(v)$, assuming the two dimension vectors agree. Complexity uses explicit vertex spaces and arrow matrices, with the input size including the total vertex dimension.

**Classification and sharp bounds.**

1. The spectrum is empty or consists of the multiples of one positive integer $M$. Every prime divisor of $M$ divides $q-1$. From the raw arrow matrices one can decide emptiness or compute $M$ in binary in deterministic polynomial time for fixed $q$.
2. Every positive integer $M$ supported on the primes dividing $q-1$ occurs, even with all vertex determinants constrained on an acyclic chain having at most two parallel arrows per link and bounded vertex dimensions depending only on $q$. For nonzero representations the smallest possible total dimension realizing $M$ is $\Theta_q(1+\log M)$.
3. For fixed $r\ge1$ and $q>2$, the maximum finite $M$ attainable with $S\le s$ and $r$ constrained vertices is $\Theta_{q,r}(s^r)$ as $s\to\infty$. One fixed quiver with $r$ vertices suffices for the lower bound. Thus even one, two and three independently constrained vertex determinants give respectively linear, quadratic and cubic worst-case field degrees in this model. With arbitrarily many constrained vertices, exponential degree is both possible and optimal in order of growth.

These assertions concern actual isomorphisms of labeled quiver representations, including nonsemisimple representations. They do not require an ordinary tensor-isomorphism oracle.

## A determinant image valid after every scalar extension

Ordinary isomorphism over a finite extension implies ordinary isomorphism over $k$. Indeed restriction of scalars gives $V^{\oplus t}\cong W^{\oplus t}$, and Krull–Schmidt cancels the multiplicities. Find an ordinary isomorphism $P$ over $k$ by constructive module isomorphism, or return the empty spectrum. To encode the quiver, act on the direct sum of the vertex spaces by the vertex projections and the arrow maps extended by zero. An intertwiner for these labeled operators preserves the sorts and is precisely a quiver intertwiner.

Let $A=\operatorname{End}_Q(V)$ and let $J$ be its Jacobson radical. Write
$$
A/J=\prod_j M_{b_j}(K_j),\qquad K_j=\mathbb F_{q^{e_j}}.
$$
The units of $A$ are the quiver automorphisms. Regard each $V(v)$ as an $A$-module and use its filtration by $J^iV(v)$. The graded pieces are semisimple. Let $D_{vj}$ be the sum across all pieces of the multiplicities of the standard simple $K_j^{b_j}$. Consequently
$$
\dim_k V(v)=\sum_j D_{vj}b_je_j .
$$
Retain the rows of $D$ indexed by $C$. For every finite extension $E/k$, the determinant vectors of automorphisms over $E$ are exactly
$$
\left\{ \left(\prod_j x_j^{D_{vj}}\right)_{v\in C}:x_j\in E^\times\right\}. \tag{1}
$$
To see this, intertwiner equations commute with extension of scalars because they are linear. The extended ideal $J_E$ is nilpotent and the quotient is still semisimple since $E\otimes_k K_j$ is a product of finite separable fields. Hence $J_E$ is the radical. Quotient units lift, and elements in $1+J_E$ act trivially on each filtration quotient. In a factor above $j$, the determinant on a copy of the extended standard simple is the product of the field norms to $E$ of the ordinary determinants of its component matrices. Each field norm is surjective. The same product occurs at every vertex, to power $D_{vj}$, since scalar extension takes each base simple to one copy of the standard simple in each component. The variables $x_j$ can therefore be chosen independently, proving (1).

## Reading the spectrum from the base field

Let $a=(\det P_v^{-1})_{v\in C}$. Correcting $P$ by an automorphism is equivalent to solving the monomial system (1) with right hand side $a$. Apply integer unimodular row and column operations to put $D$ in Smith form. They act as invertible monomial coordinate changes over *every* multiplicative group. Write $a'_i\in k^\times$ for the transformed right hand sides and $d_1\mid\cdots\mid d_h$ for the positive invariant factors. A zero row with $a'_i\ne1$ makes the spectrum empty. The remaining independent equations are $z_i^{d_i}=a'_i$.

Put $o_i=\operatorname{ord}(a'_i)$. The multiplicative group of the degree-$t$ field is cyclic of order $q^t-1$. Thus the $i$th equation is solvable precisely when, for each prime $\ell\mid o_i$,
$$
v_\ell(q^t-1)\ \ge\ v_\ell(d_i)+v_\ell(o_i).
$$
Only primes dividing $q-1$ need attention. For odd $\ell\mid q-1$, $v_\ell(q^t-1)=v_\ell(q-1)+v_\ell(t)$. The same formula holds at $\ell=2$ if $q=1\bmod 4$. For $q=3\bmod4$, the value is $1$ on odd $t$ and $v_2(q-1)+v_2(q+1)+v_2(t)-1$ on even $t$. These are the elementary lifting-the-exponent formulas, obtainable by expanding successive prime powers and factoring the prime-to-$\ell$ power as a geometric sum. Each requirement is therefore divisibility of $t$ by a power of $\ell$, and its exponent never exceeds $v_\ell(d_i)$. Take their least common multiple to obtain $M$. In particular $M\mid d_h$ for $h>0$. For $h=0$, a compatible system has $M=1$.

For completeness the matrix $D$ can be computed without constructing indecomposables over any extension. Obtain $A$ by linear equations and compute $J$ by the finite-dimensional algebra radical algorithm. Compute the center of $A/J$ by linear equations. Its Frobenius-fixed subalgebra, computed by another linear system, is $k^u$ for $u$ simple components. Splitting by the eigenspaces of multiplication by each element of a basis of this subalgebra partitions the components individually, since its functions distinguish any two coordinates. The eigenvalues lie in the fixed field $k$ and may be enumerated. This supplies the primitive central idempotents. From the dimensions of a central summand and its center obtain $e_j$ and $b_j$ via $\dim A_j=e_jb_j^2$. On each radical layer act by the corresponding central idempotent, using any lift, and divide the dimension of its image by $e_j b_j$. This gives the desired multiplicity. The number of layers and all these vector-space dimensions are polynomially bounded. Integer Smith form with transforming matrices has polynomial bit complexity. Element orders in fixed $k^\times$ have constant cost, and the valuations needed here only divide by fixed primes. Huge output fields need never be constructed. [Constructive module isomorphism](https://ix.cs.uoregon.edu/~luks/ModIso.pdf) · [Finite algebra algorithms](https://www.sciencedirect.com/science/article/pii/S074771710880017X) · [Kannan and Bachem on Smith and Hermite forms](https://doi.org/10.1137/0208040)

## Upper bounds on how late the first witness can occur

If $D$ has rank $h>0$, its last Smith factor is at most the absolute determinant of any nonzero $h$-row, $h$-column minor. By Hadamard this is bounded by the product of the column sums of that minor. These positive integers have sum at most $S$ by the dimension formula. As each integer $x\ge1$ satisfies $x\le3^{x/3}$, this gives $M\le3^{S/3}$. Also $h\le r$ if $r$ vertices are constrained, giving $M\le S^r$ for $S\ge1$.

## Serializing root extractions with actual arrow matrices

Fix integers $k_0\ge1$ and $a\ge2$. Use vertices $1,\ldots,k_0$ with one loop each and one forward arrow between consecutive vertices. For each $i$ define $U_i$ with the space $k[t]/(t^a)$ at $i$, on which the loop multiplies by $t$. If $i<k_0$, also give it a copy of $k$ at $i+1$, loop zero there, and use the quotient mod $t$ as its arrow $i\to i+1$. All remaining spaces and maps are zero. Its endomorphism ring is $k[t]/(t^a)$: the map at $i$ is multiplication and the map at $i+1$, when present, is forced to be its constant term. Thus the $U_i$ are pairwise nonisomorphic absolutely indecomposable modules of distinct supports. In $V=\bigoplus_i U_i$ there is exactly one copy of each. By Krull–Schmidt, the semisimple endomorphism quotient has one copy of $k$ per summand. Equivalently its diagonal scalar is the residue of each diagonal component, the other components belonging to the radical. The exponent columns in (1) are therefore $a\,e_i+e_{i+1}$ for $i<k_0$ and $a\,e_{k_0}$ for the last one. This reasoning permits all off-diagonal morphisms between summands.

Choose $c\in k^\times$. Change the basis at vertex 1 by a diagonal matrix of determinant $c^{-1}$ to obtain $W$ via conjugating the arrows by this base change. Impose determinants one at every vertex. The correction equations are
$$
x_1^a=c,\qquad x_{i-1}x_i^a=1\quad(2\le i\le k_0).
$$
They have a solution exactly when $c$ or, equivalently, $c^{-1}$ has an $a^{k_0}$th root. One chooses $x_{k_0}$ and recursively recovers all earlier variables. The construction has total dimension $ak_0+k_0-1$.

For $\ell\mid q-1$ take $c$ of exact order $\ell^{v_\ell(q-1)}$. If $a=\ell$, the first degree admitting such a root is $\ell^{k_0}$, except when $\ell=2$ and $q=3\bmod4$. In the exceptional case, to obtain degree $2^b$, $b\ge1$, use $k_0=b+v_2(q+1)-1$. The valuation formulas give exactly $v_2(t)\ge b$. Thus a chain of length $O_q(b)$ realizes the exact period $\ell^b$. For arbitrary supported $M$, put its prime-power chains consecutively and connect their endpoints by zero arrows. Vertex labels prohibit permutations and a zero arrow imposes no compatibility requirement, so the intersection of their spectra has period $M$. Use a one-dimensional identical pair when $M=1$.

To remove the loops, replace each vertex by two successive equal-dimensional vertices with parallel forward arrows $I$ and its loop matrix. Send the old inter-vertex arrow from the second vertex of its source to the first vertex of its target. In both representations the identity arrow forces the same transformation on the duplicated vertex, and the second arrow recovers exactly the original loop equation. The construction preserves every extension, including the determinant requirements. It doubles total dimension and has at most two parallel arrows per link. The vertex dimensions are at most $1+\max_{\ell\mid q-1}\ell$ for the nontrivial periods. Over $\mathbb F_5$, $a=2$ already yields period $2^{k_0}$ with each vertex dimension at most 3. Together with $M\le3^{S/3}$ this proves optimal asymptotic description in total dimension.

Finally fix $r=k_0$ and $q>2$. Choose any prime $\ell\mid q-1$ and let $a=\ell^u$ tend to infinity. The unchanged quiver now encodes a root of degree $\ell^{ur}$. The least field degree is $\ell^{ur}$, or within a fixed factor of it in the exceptional 2-adic case, once $u$ is large. The dimension is $ra+r-1$, so $M=\Omega_{q,r}(S^r)$. For a cap $s$, choose the largest such $a$ fitting the cap: the geometric ratio between successive choices is constant. This proves the third assertion.

## Scope and prior work

The determinant image over the base field, Krull–Schmidt and finite-field norms are existing ingredients. Ordinary quiver descent is classical. Earlier project work on finite étale multiplication tensors gives extension spectra with disjunctions and an NP-complete minimum-degree threshold. Here labeled quivers yield a principal divisibility spectrum and a polynomial-time minimum even though its value may be exponential. The matching inverse constructions and the fixed-number-of-determinants bounds specify the proposed contribution. These results concern the quiver transport setting; general three-mode tensor transport has an additional moving mode. Publication priority for the compound theorem remains unverified. [Noether–Deuring in the quiver setting](https://arxiv.org/abs/1805.06999) · [Quiver semi-invariants and their degree bounds](https://doi.org/10.1016/j.jpaa.2017.12.007)
