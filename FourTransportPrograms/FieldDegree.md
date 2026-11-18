# Minimum field degree for tensor transporters

Informal proofs. The inputs below are three-tensors given by multiplication tables, and the output problem is to find the least field extension degree admitting a transporter. Over every fixed finite field, the threshold version is NP-complete already for finite étale multiplication tables, with or without determinant-one constraints. Given a particular extension degree in binary, both restricted decision problems are polynomial-time solvable.

## 1. Exact orbit formula

Let $A,B$ be finite étale algebras of dimension $n\ge 1$ over a field $F$, in specified bases. For an extension $E/F$, write $A_E=A\otimes_F E$ and likewise for $B$. In the bilinear-map convention a transporter is a triple of $E$-linear bijections
$$
f,g,h:A_E\longrightarrow B_E,\qquad h(xy)=f(x)g(y).
$$
Identifying a multiplication map with an element of $A_E^\vee\otimes A_E^\vee\otimes A_E$ gives the usual three-factor tensor action, with inverses and transposes in the first two factors. This change of convention preserves the field of definition and the determinant-one condition.

Put $u=f(1)$ and $v=g(1)$. Evaluating at $x=1$ and at $y=1$ gives $h(x)=u g(x)=v f(x)$ for all $x$. Multiplication by either $u$ or $v$ is a bijective linear map, so both are units. Then
$$
\phi(x)=(uv)^{-1}h(x)
$$
is a unital $E$-algebra isomorphism. In fact all transporters are exactly
$$
(f,g,h)=(m_u\phi,\ m_v\phi,\ m_{uv}\phi),\qquad
u,v\in B_E^\times,\quad \phi\in\operatorname{Iso}_{E\text{-alg}}(A_E,B_E),
$$
where $m_u$ denotes multiplication by $u$. This follows by substitution, using commutativity of $B_E$. In particular the minimum degree of an extension with a transporter equals the minimum degree for an algebra isomorphism. If all three determinants must be $1$, the same statement holds with $\det\phi=1$. Indeed $\det h=\det f\,\det g/\det\phi$. Conversely one can take $u=v=1$. The normalization is a direct instance of the classical unit argument for associative algebra isotopy. [Albert, 1942](https://doi.org/10.2307/1968960).

Choose a finite Galois extension $L/F$ splitting both algebras. Let $X_A,X_B$ be the $n$-element sets of primitive idempotents over $L$ and put $G=\operatorname{Gal}(L/F)$. The geometric isomorphisms are indexed by bijections $b:X_A\to X_B$, with $G$ acting by
$$
\gamma\cdot b=\gamma_B\circ b\circ\gamma_A^{-1}.
$$
Let $G_b$ be the stabilizer of $b$. Coefficientwise Galois action on the matrix of the corresponding isomorphism is exactly this action on $b$. Its entries therefore generate $L^{G_b}$ over $F$. Every isomorphism over any extension field, after embedding $L$ into an algebraically closed overfield of that extension, is one of these bijections. Hence an extension $E/F$ admits a transporter precisely when it contains an $F$-isomorphic copy of one of the fields $L^{G_b}$, and
$$
\min_{E/F \text{ finite},\;T_A\cong_E T_B}[E:F]
=
\min_{b:X_A\simeq X_B}[G:G_b].
$$
For determinant-one transporters restrict the minimum to the bijections with determinant-one matrix and take the empty minimum to be infinity. These bijections form a $G$-stable subset because the bases are defined over $F$. This is the explicit transporter version of the equivalence between finite étale algebras and finite continuous Galois sets. [Stacks Project, Tag 04JI](https://stacks.math.columbia.edu/tag/04JI).

The ordinary bound $n!$ is sharp. Take two independent tuples $(r_i)_{i=1}^n$ and $(s_i)_{i=1}^n$ of algebraically independent reals over a subfield $K\subseteq\mathbb R$. Take $F$ generated over $K$ by their two sets of elementary symmetric functions, and let $A$ and $B$ be the algebras of the two monic polynomials with these root sets. The compositum $L=K(r_1,\ldots,r_n,s_1,\ldots,s_n)$ has degree $(n!)^2$ over $F$. Indeed there are $(n!)^2$ independent root-permutation automorphisms, while successively adjoining roots gives the same upper bound. Its Galois group is $S_n\times S_n$, transitive on the $n!$ bijections. Every witness field therefore has degree at least $n!$, and one of degree $n!$ exists. For $n\ge 3$ a bijection stabilizer is a nonnormal diagonal copy of $S_n$, which illustrates why the minimal witness field can be non-Galois and strictly smaller than the common splitting field.

There is also a direct real computation benchmark. Given a monic degree-$n$ real polynomial $p$, when comparing $\mathbb R[X]/(p)$ with $\mathbb R^n$, decision amounts to testing positive definiteness of the trace form $\operatorname{Tr}(m_{xy})$. If $p$ has repeated roots, a nonzero nilpotent lies in the radical of this form. If $p$ has a complex factor, the trace quadratic form on that factor is $2((\operatorname{Re}z)^2-(\operatorname{Im}z)^2)$. If all roots are distinct and real, the form is a sum of squares in the product coordinates and is positive definite. Entries can be computed from traces of companion-matrix powers, then leading principal determinants decide in polynomially many field operations. If $K$ is the field generated by the finite machine constants, choose the real roots algebraically independent over $K$. The input generates only the coefficient field over $K$, and every exact transporter generates its degree-$n!$ splitting field after normalization. An arithmetic-only real BSS machine with Boolean oracles keeps all registers in the input-generated field, so it cannot always output such a transporter. More generally, allowing adjunctions of roots of degree at most $d$ leaves this obstruction for prime $n>d$, because the resulting tower has no degree divisible by $n$. This statement concerns exact scalar output. A symbolic polynomial-and-root description can have far smaller length than the extension degree. [Hermite matrix implementation](https://arxiv.org/abs/2110.10313), [BSS oracle model](https://arxiv.org/abs/1105.1380).

## 2. Finite-field spectra and pointwise decision

Fix $q$ and let $F=\mathbb F_q$. Write
$$
A=\prod_{d\ge 1}\mathbb F_{q^d}^{\,c_A(d)},\qquad
B=\prod_{d\ge 1}\mathbb F_{q^d}^{\,c_B(d)}.
$$
Frobenius acts with $c_A(d)$ cycles of length $d$ on $X_A$, and similarly for $B$. Over $\mathbb F_{q^m}$ each $d$-cycle turns into $\gcd(d,m)$ cycles of length $d/\gcd(d,m)$. Thus a binary-specified degree $m$ works if and only if the two transformed profiles agree. Equivalently, define
$$
\Delta(t)=\sum_{d\mid t}d(c_A(d)-c_B(d)).
$$
A degree $m$ works exactly when $\Delta(mk)=0$ for every positive integer $k$. Indeed $\Delta(t)$ is the difference of fixed-point counts of the two Frobenius permutations raised to $t$, and a permutation's cycle counts are determined by its fixed-point counts at all powers, by divisor inversion.

Let $N$ be the least common multiple of all original cycle lengths on either side. The answer depends only on $\gcd(m,N)$. For any divisor $g\mid N$, $g$ works precisely when it divides no divisor $t\mid N$ with $\Delta(t)\ne0$. To see this, if $g\mid t$ one can take the power $t$ itself. Conversely for every $k$, $\Delta(gk)=\Delta(\gcd(gk,N))$, and the latter gcd is a multiple of $g$. The complete spectrum is the union of the sets of positive multiples of its divisibility-minimal good divisors of $N$. In particular the smallest good degree divides $N$.

The profiles can be computed directly from the raw multiplication tables. The map $M_A:x\mapsto x^q$ is $\mathbb F_q$-linear. Its scalar extension as a linear map permutes the split primitive idempotents up to reversing the Frobenius convention, which preserves cycle lengths. Explicitly, in the embedding coordinates, for $x\in A$ the coordinate at an embedding $\alpha$ becomes $\alpha(x)^q=(\operatorname{Frob}_q\circ\alpha)(x)$, an identity that extends by linearity for this linear map. The fixed space of a permutation matrix has dimension the number of cycles over any characteristic, so for $k\le n$,
$$
u_A(k)=\dim\ker(M_A^k-I)
=\sum_d c_A(d)\gcd(d,k)
=\sum_{e\mid k}\varphi(e)\sum_{e\mid d} c_A(d).
$$
Computing $u_A(1),\ldots,u_A(n)$ by linear algebra, invert the divisor sums, divide by $\varphi(e)$ as integers, and invert the multiples sums downwards from $n$. This deterministically recovers all $c_A(d)$. The same applies to $B$. It yields polynomial bit-time for fixed $q$ and binary $m$. One can also validate the finite étale promise in polynomial time. Check the algebra axioms and solve the linear equations for a unit, then check invertibility of Frobenius. For a finite-dimensional commutative unital algebra over a finite field, Frobenius is invertible precisely when the algebra is reduced, or equivalently is a product of finite fields. A nonzero nilpotent would be killed by a sufficiently high power of Frobenius, while the converse follows from the decomposition of reduced Artinian rings.

An exact algorithm enumerates the divisors of $N$, tests each transformed profile and takes the least successful degree. Computing the factorization of $N$ needs only trial factoring integers at most $n$, since the profiles are available. With $k=\omega(N)$ distinct primes, the number of candidates is $\prod_{p\mid N}(1+v_p(N))$. Each exponent is at most $\log_2 n$, so the candidate count is at most $(1+\log_2 n)^k=2^{O(k\log(k+1))}n^{O(1)}$. The last inequality follows by maximizing $x^k\exp(-x)$ for $x\ge0$. Thus the problem is fixed-parameter tractable in $k$, with only $2^k$ candidates when $N$ is squarefree.

Every upward-closed family $\mathcal U$ in the divisor lattice of $N$ that contains $N$ occurs as an ordinary isomorphism spectrum, with extension degrees interpreted via $\gcd(m,N)$. To construct examples, prescribe $\Delta(t)=N$ at each maximal divisor outside $\mathcal U$ and $\Delta(t)=0$ elsewhere. For $d\mid N$ set
$$
a_d=\frac{1}{d}\sum_{e\mid d}\mu(d/e)\Delta(e).
$$
These are integers since $d\mid N$. Take the positive and negative parts of $a_d$ as the two multiplicities for field degree $d$. Divisor inversion gives the prescribed fixed-count differences, and $\Delta(N)=0$ gives equal dimensions. A common field factor of degree one can be added when both dimensions are zero. An optional common field factor of degree $N$ ensures that the joint permutation order is exactly $N$. For a fixed prescribed $\Delta$, if the order need only divide $N$ and dimension zero is allowed, the least common dimension is exactly $\tfrac12\sum_{d\mid N}d|a_d|$. Indeed any other choice of profiles with the same difference adds the same nonnegative multiplicity to both sides at each degree. This gives a dimension bound for a direct spectral encoding.

## 3. Complete determinant-one spectrum

Let $D_A,D_B\in\mathbb F_q^\times$ be the trace-form determinants in the supplied bases. Any algebra isomorphism $\phi$ satisfies
$$
(\det\phi)^2=D_A/D_B.
$$
This follows by pulling back the trace form. If $D_A\ne D_B$, no extension admits determinant-one transport. If the determinants are equal and the characteristic is two, every ordinary isomorphism has determinant one.

Suppose the characteristic is odd and $D_A=D_B$. For an ordinary successful degree $m$, any two isomorphisms differ by an automorphism of $B_{\mathbb F_{q^m}}$. After splitting, that automorphism permutes the idempotents and its determinant is its permutation sign. The automorphism group over $\mathbb F_{q^m}$ is the centralizer of the $m$-th power of Frobenius on these idempotents. This centralizer contains an odd permutation if and only if the cycle profile contains an even cycle length or has a repeated odd length. An even cycle is itself odd. Exchanging two odd cycles of equal length is odd. When all lengths are odd and distinct, every centralizing permutation rotates individual cycles and is even.

If the successful powered profile has distinct odd lengths, no original cycle could have split. Splitting one cycle creates repeated lengths. Hence $\gcd(m,N)=1$. In that case ordinary isomorphisms over $\mathbb F_{q^m}$ are already over $\mathbb F_q$, because the original Frobenius is the same inverse power of its $m$-th power on both sides. This gives the complete list of signed outcomes.

- If $A$ and $B$ are nonisomorphic at degree one, every ordinary successful degree is signed-successful.
- If they are already isomorphic and have a determinant-one base isomorphism, every degree is signed-successful.
- If they are already isomorphic and have no determinant-one base isomorphism, the original common lengths are distinct and odd. A degree is signed-successful exactly when $\gcd(m,N)>1$. In fact a common prime factor causes a cycle to split and provides an odd automorphism, whereas a degree coprime to $N$ creates no new isomorphisms. The spectrum is empty when $N=1$.

Here the bullets assume odd characteristic and equal trace-form determinants. The earlier cases give the other outcomes. In particular no computation in the potentially huge specified extension is needed. For the base orientation check, compute the fixed algebra $D=\ker(M_A-I)\cong\mathbb F_q^r$. Its coordinate idempotents can be built by recursive splitting. On an idempotent summand $eD$ of dimension greater than one choose $a\in eD$ not a scalar multiple of $e$. For each $\lambda\in\mathbb F_q$ build the Lagrange projector
$$
\prod_{\mu\in\mathbb F_q,\;\mu\ne\lambda}\frac{a-\mu e}{\lambda-\mu}.
$$
The nonzero projectors give a strict decomposition into idempotents summing to $e$. At most $n-1$ strict splits suffice. The same procedure on $B$ produces explicit field-factor multiplication tables. If profiles agree, pair factors of equal dimension and compute finite-field isomorphisms via Lenstra's deterministic algorithm. For a nonprime fixed $q$, any prime-field isomorphism can be corrected on the common embedded $\mathbb F_q$ by a prime-field Frobenius power. Either an odd automorphism is already known from the cycle-profile test, or this computed isomorphism has the unique possible determinant. [Lenstra, 1991](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf).

## 4. NP-completeness of selecting a bounded degree

Fix $\mathbb F_q$. The input consists of two explicit finite étale multiplication tables of the same dimension and a positive integer bound $K$ in binary. Ask whether some $1\le m\le K$ admits a transporter. This language is in NP. The certificate is the binary representation of $m$, whose length is bounded by the length of $K$, and Section 2 verifies it in polynomial time. Section 3 gives the analogous claim for determinant-one transport.

Reduce from Vertex Cover on a simple graph with vertices $1,\ldots,v$ and budget $k$, where $v\ge 2$, $0\le k\le v$, and the graph has at least one edge. Choose distinct odd primes $p_i$ in an interval $[P,Q]$ with $Q/P\le 1+1/v$ and $P>e$. To find them deterministically, start at $X=v^3$, sieve $[X,2X)$ and divide the interval into $v$ consecutive blocks of length $X/v$. Double $X$ and repeat if every block has fewer than $v$ primes. The prime number theorem gives more than $v^2$ primes in $[v^3,2v^3)$ for all sufficiently large $v$, so the first sieve succeeds for all such $v$. For the finitely many smaller $v$ the same theorem guarantees termination after finitely many doublings. Thus the running time and the numerical sizes are polynomial in $v$. Set $P$ and $Q$ to the endpoints of a successful block.

For each edge $\{i,j\}$ set $M=p_i p_j$. On the $A$ side adjoin the direct product of $M$ copies of $\mathbb F_q$ and one copy of $\mathbb F_{q^M}$. On the $B$ side adjoin the product of $p_j$ copies of $\mathbb F_{q^{p_i}}$ and $p_i$ copies of $\mathbb F_{q^{p_j}}$. Each addition has dimension $2M$ on both sides. The difference of its Frobenius fixed-point counts at power $t$ is
$$
M\big(1-\mathbf 1_{p_i\mid t}\big)\big(1-\mathbf 1_{p_j\mid t}\big).
$$
Indeed the four terms come from the cycle lengths $1,p_i,p_j,p_i p_j$. Taking products of the algebras adds these differences, and every summand is nonnegative. If the primes dividing $m$ do not cover an edge, then $\Delta(m)>0$. If they cover every edge, then all summands vanish at every multiple of $m$. Therefore
$$
T_A\cong_{\mathbb F_{q^m}}T_B
\quad\Longleftrightarrow\quad
\{i:p_i\mid m\}\text{ is a vertex cover}.
$$
The minimum good degree is the minimum product of the primes in a vertex cover. A cover of size at most $k$ gives a degree at most $Q^k$. If every cover has size at least $k+1$, every good degree is at least $P^{k+1}>Q^k$, because $(Q/P)^k\le(1+1/v)^v<e<P$. Thus the reduction outputs $K=Q^k$.

Each field factor has polynomial degree and its multiplication table can be generated from a monic irreducible polynomial in deterministic polynomial time for fixed characteristic by Shoup's algorithm. Multiplication in the direct product is blockwise. The resulting total dimension and the size of the fully expanded dense tensor are polynomial in $v$. The reduction is therefore deterministic on actual multiplication tensors. [Karp on Vertex Cover](https://dblp.org/rec/conf/coco/Karp72.html), [Shoup on deterministic irreducible polynomial construction](https://www.shoup.net/papers/detirred.pdf).

The same reduction gives NP-hardness with determinant-one transport over every fixed $q$. All factor degrees in the reduction are odd. In a splitting field let $V$ be the matrix of basis evaluations at the geometric points of an algebra. Its trace form has matrix $V^{\mathsf T}V$. Frobenius permutes the rows by an even permutation because every cycle length is odd. Thus $\det V\in\mathbb F_q^\times$ and its trace determinant is a square in the base field. For $q=2$ or $3$ the only nonzero square is $1$, so the two trace determinants are already equal. Over any other fixed $q$ they can be made equal by rescaling one basis vector on one side, finding a square root by enumeration in the fixed field. The graph has at least one edge, so the two base algebras are nonisomorphic. Section 3 now gives the exact same spectrum for ordinary and determinant-one transport.

Two further consequences follow directly from the reduction.

- Approximating the minimum degree within any fixed multiplicative factor $C\ge 1$ is NP-hard. The ratio between the two sides of the budget gap is at least $P/e$, which tends to infinity. An approximation within a factor $C$ in both directions can distinguish the cases once $P/e>C^2$.
- The number of divisibility-minimal successful degrees can be exponential in the number of relevant primes. A graph consisting of $w$ disjoint edges has $2^w$ minimal covers, each producing a distinct divisibility-minimal product. Thus the pointwise test can be succinct even when its explicit list of minimal good degrees is large.

The same gadget realizes bounded-rank hitting sets. For a hyperedge $S$ put $M=\prod_{i\in S}p_i$. For each $J\subseteq S$, put $M/\prod_{j\in J}p_j$ copies of the field of degree $\prod_{j\in J}p_j$ on the $A$ side when $|J|$ is even, and on the $B$ side when $|J|$ is odd. The difference is $M\prod_{i\in S}(1-\mathbf 1_{p_i\mid t})$. Each side has dimension $2^{|S|-1}M$, so the construction is polynomial in the hypergraph size whenever its edge size is bounded by a fixed constant.

## 5. Sharp worst-case finite-field extension degree

For any fixed $q$, write $D_q(n)$ for the maximum over pairs of dimension-$n$ finite étale algebras of their minimum successful ordinary extension degree. Then
$$
\log D_q(n)=(1+o(1))\sqrt{2n\log n}.
$$
For the upper bound take the Frobenius permutation on the union of the two $n$-element sets. Its order $N$ is a successful degree because both actions become trivial. The maximal permutation order on $2n$ points is Landau's $g(2n)$, with $\log g(2n)\sim\sqrt{2n\log(2n)}$. [Deléglise, Nicolas and Zimmermann](https://arxiv.org/abs/0803.2160).

For the lower bound partition all odd primes at most $x$ into two groups whose sums differ by at most $x$. This is obtained by adding each next prime to the group with smaller sum. Use one field factor of degree $p$ on its assigned side, and pad each side with copies of $\mathbb F_q$ to reach dimension $n$. Under Frobenius to power $m$, a prime-length cycle becomes fixed points if $p\mid m$ and remains a cycle of length $p$ otherwise. The two lists of prime lengths are disjoint, so a degree works exactly when all chosen primes divide $m$. The logarithm of the minimum is $(1+o(1))x$ by the prime number theorem. The larger of the two dimension sums is
$$
\tfrac12\sum_{p\le x}p+O(x)\sim \frac{x^2}{4\log x}.
$$
For each sufficiently large $n$ take $x=(1-\epsilon)\sqrt{2n\log n}$ for fixed $\epsilon>0$. Both dimension sums are at most $n$ for all sufficiently large $n$. Letting $\epsilon$ decrease to zero proves the lower bound. The same estimate holds for the maximum over pairs with a finite minimum determinant-one extension degree, over every fixed finite field. The lower-bound examples have an all-odd profile and can be given equal discriminants, so the signed and ordinary spectra agree when the two profiles differ. For the upper bound, any nonempty signed spectrum depends only on $\gcd(m,N)$ by the classification, so $N$ is again successful.

If the output format uses dense coordinates in an explicit degree-$m$ extension field, even representing one field element in that format uses $m\log_2 q$ bits up to rounding. The extremal family therefore rules out uniformly polynomial-size explicit dense witnesses for unrestricted extension degree on these tables. The decision algorithm and the NP certificate above use only a binary degree and avoid that expansion. This output-size conclusion is specific to the dense coordinate format.

## Relation to existing work

Albert's normalization, finite étale descent, Frobenius profiles and Landau's asymptotic are established ingredients. Grochow and Qiao's search-to-decision work concerns different fixed-field search problems and uses different output requirements. The extension-degree optimization here is a different problem even though it uses their tensor-isomorphism language. The closest permutation paper found considers whether some element of a generated group has a specified cycle type. For one cyclic generator that problem is in logspace. The problem here compares equal powers of two given permutations and constrains the numerical size of the common exponent. There is no contradiction since an unconstrained common exponent always exists. I did not find the exact bounded-degree result in these sources, and a broader priority check remains appropriate. [Grochow–Qiao, Part IV](https://arxiv.org/html/2306.16317v2), [Finding Cycle Types in Permutation Groups](https://arxiv.org/abs/2503.02864).

A next question is whether minimum extension degree for succinctly specified tensor families has similarly short, efficiently checkable certificates. For this finite étale class the binary degree alone suffices, and the Frobenius profile gives an explicit verifier. Another question is which spectra can be represented with polynomial-dimensional tables when the monotone CNF has unbounded edge size. The results concern finite étale multiplication tensors and optimization of the extension field.
