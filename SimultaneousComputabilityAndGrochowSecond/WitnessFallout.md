# Deterministic descent from tensor witnesses with different center maps

Let $L/K$ be an explicitly presented finite Galois field extension, and let $A,B$ be degree-$n$ central simple algebras over the same identified center $L$. Given explicit witnesses that their multiplication tensors are isomorphic over finite extensions $E_j/K$ linearly disjoint from $L$, the algorithm below recovers a witness over $K$ under the [sharp universal degree-list condition](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/SimultaneousComputabilityAndGrochow/Descent.md). It also succeeds for certain lists that fail that degree condition, by using the actual maps on the center. The number of field operations is deterministic and polynomial in the explicit inputs. The algorithm requires no Brauer invariants, splitting-field search, prior agreement of center maps, or enumeration of the full Galois group.

This advances the search side of Grochow–Qiao's field-comparison question for central simple multiplication tensors. The proof also covers the determinant-one action in volume-normalized bases. It requires the extension witnesses as part of the input, and it makes no bit-height claim over number fields. [Grochow–Qiao, Tensor Isomorphism-Completeness, §6.2 and Open Question 10.6](https://arxiv.org/pdf/1907.00309).

## 1. A sufficient criterion that uses the witnesses

Write a multiplication-tensor witness as $(P,Q,R)$ with $R(xy)=P(x)Q(y)$. Put $a=P(1)$ and $b=Q(1)$. The equations at the units say $R(x)=aQ(x)=P(x)b$, so both multiplications by $a,b$ are bijective and $a,b$ are units. Substitution shows that $\phi_j(x)=a^{-1}R(x)b^{-1}$ is a unital algebra isomorphism. Conversely a unital algebra isomorphism gives $P=Q=R=\phi_j$. These identities commute with scalar extension.

Write $d_j=[E_j:K]$ and let $g_j\in G=\operatorname{Gal}(L/K)$ be induced by $\phi_j$ on the center. The extended center is $LE_j$, and $\operatorname{Gal}(LE_j/E_j)=G$ by restriction. A matrix for $g_j$ over $K$ is obtained by applying $\phi_j$ to the designated $K$-basis of $L$. In the signed case the $g_j$ lie in the allowed subgroup $G_n$ described in §5.

For each prime $\ell\mid n$, let $J_\ell=\{j: \ell\nmid d_j\}$. For nonempty $J_\ell$ choose a reference $r_\ell\in J_\ell$ and define
$$
D_\ell=g_{r_\ell}\left\langle g_{r_\ell}^{-1}g_j:j\in J_\ell\right\rangle .
$$
This is the smallest left coset of a subgroup containing the supplied $g_j$ for $j\in J_\ell$, independently of the reference. If $J_\ell$ is empty set $D_\ell=\varnothing$.

**Theorem.** If $n>1$ and $\bigcap_{\ell\mid n}D_\ell\ne\varnothing$, there is a deterministic algorithm that constructs a base tensor witness inducing any selected $g$ in this intersection. It computes the intersection and uses polynomially many field operations in the explicit inputs. The $n=1$ case is immediate because both algebras are the identified field $L$.

The condition holds under the sharp degree-only guarantee. The Helly dimension $\kappa(G)$ bounds the size of a minimally inconsistent family of left cosets. If no set of at most $\kappa(G)$ prime divisors of $n$ meets every $d_j$, then every at most $\kappa(G)$ of our cosets has a common supplied $g_j$, from a degree avoiding their primes. Helly gives nonempty intersection. The value of $\kappa(G)$ is not needed to run the algorithm. [Domokos–Szabó, Helly dimension of algebraic groups](https://arxiv.org/abs/0911.0404).

## 2. Composing center maps with bimodules

For a fixed $g$, use explicit $K$-linear $B$-$A$ bimodules $M$ satisfying $m\lambda=g(\lambda)m$ for $\lambda\in L$, with their left $L$-space structure. Write $A^{[g]}$ for $A$ with structural map $L\to Z(A)$ given by $\lambda\mapsto g^{-1}(\lambda)$. These bimodules are left modules over the central simple $L$-algebra
$$
C_g=B\otimes_L(A^{[g]})^{\mathrm{op}}.
$$
For the constructed modules $e(M)=\dim_L(M)/n^2$ is an integer. Probe $j$ supplies a module of type $(B,A;g_j)$ by taking $B_{LE_j}$ with the left multiplication action of $B$ and the right action of $A$ through $\phi_j$, then restricting to $L$. Its normalized dimension is $d_j$. The inverse isomorphism gives the analogous $(A,B;g_j^{-1})$-bimodule of dimension $d_j n^2$.

If $M$ has type $(B,A;g)$ and $N$ has type $(A,D;h)$, for a third degree-$n$ algebra $D$, then
$$
(m\otimes n)\lambda
 =m\otimes h(\lambda)n
 =mh(\lambda)\otimes n
 =g(h(\lambda))(m\otimes n).
$$
Thus $M\otimes_A N$ has type $(B,D;gh)$. All left $A$-modules are sums of copies of one simple module. Comparing dimensions therefore gives ${}_AN\simeq A^{e(N)}$, hence $\dim_L(M\otimes_A N)=n^2e(M)e(N)$. To compute the product, take the ordinary $K$-tensor product and use bases of the modules and $A$ to impose the balancing relations $ma\otimes n=m\otimes an$. The action matrices descend to the quotient. [Drozd–Kirichenko, Finite Dimensional Algebras, §8](https://www.imath.kiev.ua/~drozd/drozd-kirichenko_en.pdf).

## 3. Deterministic dimension reduction

Any two modules of the same type and normalized dimensions $a,b>0$ yield an explicit module of normalized dimension $\gcd(a,b)$. They are modules over one central simple algebra $C_g$, so each is a sum of copies of the same simple module. At a Euclidean step with $a\ge b$, the module of normalized dimension $a$ admits an injection from $\lfloor a/b\rfloor$ copies of the smaller one. The cokernel realizes the remainder $a\bmod b$. A zero remainder retains the smaller module.

The injections can be computed deterministically over any field. For $C_g$-modules $X,Y$ with $\dim_L X\le\dim_L Y$, start with the zero map $f:X\to Y$. If its kernel is nonzero, its cokernel is also nonzero. By semisimplicity, there are a module-linear retraction $p:X\to\ker f$ and a module-linear section $s\colon\operatorname{coker}f\to Y$. Find both by imposing the corresponding intertwining and retraction or section equations, all linear. Find any nonzero module map $u\colon\ker f\to\operatorname{coker}f$ by computing the relevant Hom space. Such $u$ exists because the two nonzero modules have the same simple type. Replace $f$ by
$$
f+s u p.
$$
On $\ker p$ the replacement is $f$, whose image is $\operatorname{im}f$. On $\ker f$ its image is $s u(\ker f)$, in a complementary summand. Thus its rank increases by $\operatorname{rank}u$. After at most $\dim_L X$ iterations this gives an injection and, in equal dimension, an isomorphism. All action matrices and Hom spaces are over $L$. The maps can be checked on bases of the two acting algebras.

For every $g$, the regular left module of $C_g$ is an explicit module of its type with normalized dimension $n^2$, even when $g$ cannot lift to an algebra isomorphism. Taking a gcd with this known module reduces the normalized dimension from $e$ to $\gcd(e,n^2)$. This caps the size after every word multiplication without introducing any prime divisor that was absent from $e$.

## 4. Recovery and uniform complexity

Compute the $D_\ell$ by breadth-first search in the group of center-map matrices generated by the supplied ratios and their inverses. Each group generated this way has at most $[L:K]$ elements. For a selected $g$ in the intersection, the search records a word for $g$ from each reference and its ratios. The ratio $g_{r_\ell}^{-1}g_j$ is realized by composing the inverse reference module with the module for probe $j$. For its inverse, compose the inverse module for probe $j$ with the reference module. Starting with the reference and multiplying these generator modules on the right realizes $g$.

For each $\ell$, every probe used in that word has degree coprime to $\ell$. Cap its probe modules and all products by the regular modules as in §3. This constructs an explicit module $M_\ell$ of type $(B,A;g)$ and normalized dimension $e_\ell\mid n^2$, with $\ell\nmid e_\ell$. The computation uses no compositum of probe fields, which need not be disjoint from one another.

Apply Euclidean dimension reduction across the $M_\ell$, all of the same type. Their normalized dimensions have gcd $1$, because only primes dividing $n$ can occur and each such prime is avoided by some $M_\ell$. This yields a module $M$ with $\dim_L M=n^2$. Its left $B$-module structure is isomorphic to $B$ by unique simple type and dimension, and the deterministic rank procedure gives such an isomorphism. Put $m$ equal to the image of $1$. Define $\phi:A\to B$ by
$$
ma=\phi(a)m .
$$
The commuting actions and associativity imply $\phi(a_1a_2)=\phi(a_1)\phi(a_2)$. The map is unital, injective by simplicity, and bijective by dimension. The type of $M$ implies that the center map is $g$. Taking $P=Q=R=\phi$ gives the desired base tensor witness.

The initial modules have normalized dimensions $d_j$. After capping, a balanced product has normalized dimension at most $n^4$, and its ordinary $K$-tensor product before taking the quotient also has polynomial dimension in $n$ and $[L:K]$. Each Euclidean injection uses a domain bounded by the corresponding dividend, and each rank augmentation uses linear equations and rank computations. A word needs at most $[L:K]$ ratios and a reference. There is only one word per prime divisor of $n$, which can be found by trial division in polynomial time in the input dimensions. Thus the field-operation bound is uniform even when $L/K$ varies. It does not make a claim about coefficient growth over number fields.

## 5. Determinant-one witnesses and the effect of actual center maps

In the volume-normalized bases of the companion descent theorem, an algebra isomorphism inducing $g$ has determinant $\operatorname{sgn}_{\mathrm{reg}}(g)^{n^2}$. The normalization identity $\det\phi=\det P\det Q/\det R$ implies that a supplied determinant-one witness has a center map in $G_n=\{g: \operatorname{sgn}_{\mathrm{reg}}(g)^{n^2}=1\}$. The computed cosets stay in $G_n$, and the recovered algebra isomorphism of allowed sign gives a determinant-one tensor witness. The degree-only guarantee uses $\kappa(G_n)$.

For a test where the observed centers contribute information, take $G=C_2^2$ with basis $e_1,e_2$, $n=30$, and the actual primary center constraints $C_2=\{x_1=0\}$, $C_3=\{x_2=0\}$, $C_5=G$. They are realized over a biquadratic number-field center by the companion theorem's Brauer construction. Its cyclic probes of degrees $2,3,5$ and the compositum of the first two allow these choices:

| Probe degree | Supplied center map |
| ---: | --- |
| 2 | $e_1$ |
| 3 | $e_2$ |
| 6 | $e_1+e_2$ |
| 5 | $0$ |

The degree-only guarantee fails, since the three primes $2,3,5$ meet all four degrees and $\kappa(C_2^2)=3$. No supplied center map repeats and no single degree is coprime to $n$. The computed $D_2$ is the line through $0,e_2$, $D_3$ is the line through $0,e_1$, and $D_5$ is the affine span of the three nonzero points, hence all of $G$. The algorithm constructs a base witness with center map $0$.

## Literature and verification status

The companion central simple descent theorem supplies the degree criterion and recovery from witnesses already agreeing on a center map on a degree-gcd-one subfamily. The result here constructs witnesses even when all supplied center maps differ, using coset generation, balanced products of actual bimodules and deterministic gcd reduction with regular modules. The public *GrochowFunctorLifting* packet treats the separately posed all-homomorphism question. [GrochowFunctorLifting, Functors](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/GrochowFunctorLifting/Functors.md).

Constructive splitting of matrix algebras over number fields has separate algorithmic literature, including bounded-degree results with factoring oracles. This algorithm uses the supplied extension witnesses and exact field arithmetic. The proof is informal, and independent publication-priority review and Lean verification remain open. [Ivanyos–Rónyai–Schicho, Splitting full matrix algebras over algebraic number fields](https://arxiv.org/abs/1106.6191).
