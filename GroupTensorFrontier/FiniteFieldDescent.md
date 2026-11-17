# Exponential extension degrees for ordinary tensor isomorphism over finite fields

Fix a finite field F of size $q$. For a pair of explicit ordinary three-tensors $T,T'$ over F of the same format, call $d\ge1$ admissible if they are isomorphic over $\mathbb F_{q^d}$. Write $d_{\min}$ for the least admissible degree and set it to infinity if the pair is not geometrically isomorphic. Proof status is informal.

**Theorem.** Fix any odd prime $\ell$ different from the characteristic of F. For each $k\ge1$ there is an explicitly constructible tensor pair with maximum side $n=O(k)$ and admissible degrees exactly the multiples of $\ell^k$. In particular every fixed finite field has geometric tensor pairs with first isomorphism over an extension of degree $2^{\Omega(n)}$.

For the same fixed F, threshold testing with a binary degree bound is NP-hard even on geometrically isomorphic inputs. Approximating their finite minimum degree within a two-sided factor $2^{L^\varepsilon}$, for some fixed $\varepsilon>0$ and dense input bit length $L$, is NP-hard. On the canonical generated family the threshold problem is NP-complete and testing a specified binary degree is deterministic polynomial time.

## 1. An exact divisibility test

Let $e$ be the order of $q$ modulo $\ell$, and let $E=\mathbb F_{q^e}$. Its multiplicative group is cyclic. Take $a\in E^\times$ of order $\ell^v$, where $v=v_\ell(q^e-1)$. For $K=\mathbb F_{q^d}$,
$$
 E\otimes_F K \cong \prod_{j=1}^{\gcd(e,d)} \mathbb F_{q^{\operatorname{lcm}(e,d)}} .
$$
Indeed the $e$ roots of a primitive generator's minimal polynomial are permuted cyclically by $q$-Frobenius. The $q^d$-Frobenius orbits all have length $e/\gcd(e,d)$, which gives these factor fields. In every factor $a\otimes1$ has order $\ell^v$.

For $\ell$ odd, the binomial formula gives $v_\ell(b^\ell-1)=v_\ell(b-1)+1$ when $b\equiv1\bmod\ell$, and $v_\ell(b^u-1)=v_\ell(b-1)$ when $\ell\nmid u$. Thus in the factor field the valuation of the group order is $v+v_\ell(\operatorname{lcm}(e,d)/e)=v+v_\ell(d)$, using $e\mid\ell-1$. In a cyclic group with this order an element of order $\ell^v$ is an $\ell^k$-th power exactly when $v_\ell(d)\ge k$. Consequently
$$
 \exists x\in (E\otimes_F K)^\times : x^{\ell^k}=a\otimes1
 \quad\Longleftrightarrow\quad \ell^k\mid d .
$$

## 2. Build the tensors with a short addition chain

Write $m=\ell^k$ and use a binary addition chain of length $R=O(\log m)$ for $m$. Encode a tensor system with the following shared roles and maps.

- A scalar F line with its multiplication.
- The field E as an F-algebra with its multiplication and a shift taking a fixed ordered basis $1,b_1,\ldots,b_{e-1}$ forward by one position and the last vector to zero. Algebra preservation fixes the unit, and the shift then fixes each basis vector even after scalar extension.
- The split F-algebra $D=F^{R+1}$ with its multiplication and the shift on its coordinate idempotents. Commutation with this shift fixes the last idempotent and all its predecessors.
- The role $V=E^{R+1}$, with the diagonal E-action and individual coordinate projections supplied by the D-action. The maps already fixed force the map on each copy of $E\otimes_F K$ to be multiplication by a unit $x_i$.
- A single bilinear map $B:V\times V\to V$. The output at coordinate $j\ge1$ multiplies the two input coordinates whose exponents sum to the $j$-th chain exponent. The zeroth output is zero. Preserving $B$ requires $x_j=x_s x_t$ for each addition-chain step, where $s,t$ are the indices whose exponents sum to the exponent at $j$.
- A marked vector supported in coordinate $R$ with value $1$ at the source and $a$ at the target.

Every map has order at most three, and the number of roles and maps is fixed. Simultaneous system isomorphism is precisely an $\ell^k$-th root of $a\otimes1$: the chain determines all $x_j$ from $x_0$, and the marked vector imposes the terminal equation. Conversely a root gives invertible maps on all roles.

Apply the constant-signature triangular compiler in Section 3 of the companion slice-module proof. Its fixed diagonal tags, private marker arrows, and order-three maps are unchanged by scalar extension. Its total side is linear in the sum of role dimensions. Thus the same pair of ordinary three-tensors works over every extension, with maximum side $O(e\log m)$. For a fixed $\ell$ this is $O(k)$. This improves the size of the first extension obstruction over the earlier MathProofs permutation-cycle construction. It uses the existing rational power-equation encoding with a marked finite coefficient algebra and a different root criterion. [Linear-side system compiler](SliceModuleKernel.md#3-one-compressed-tensor) · [Grochow and Qiao on the forms problem](https://arxiv.org/html/1907.00309#S10.SS2)

## 3. Vary the auxiliary primes in deterministic polynomial time

For the hardness reduction the primes $\ell$ are at most polynomial in the number of vertices, and e is at most $\ell-1$. Shoup's deterministic irreducible-polynomial algorithm constructs E and an extension $E'$ of degree $\ell$ over E in polynomial time, because the base characteristic is fixed. Compute a primitive $\ell$-th root of unity $\zeta\in E$ by splitting $X^\ell-1$ over E and taking any root other than 1. This splitting can use fixed-characteristic trace partitioning. Take a basis $b_i$ of E over its prime field $\mathbb F_p$. Successively split the current squarefree factors by taking gcds with $\operatorname{Tr}_{E/\mathbb F_p}(b_i X)-j$ for each $j\in\mathbb F_p$. Compute the trace polynomials modulo each factor by repeated $p$-th powering. The trace pairing is nondegenerate, so after all basis elements every part has a single root. All dimensions and polynomial degrees here are polynomial.

The $q^e$-Frobenius of $E'$ is E-linear of order $\ell$. In a normal basis it cyclically permutes the $\ell$ coordinates, so its $\zeta$-eigenspace is nonzero. Compute a nonzero eigenvector $y$ by linear algebra. Then $a_0=y^\ell\in E$. If $a_0$ were an $\ell$-th power in E, all $\ell$ roots of $X^\ell-a_0$ would be in E, contrary to the Frobenius eigenvalue of $y$. It follows that $a=a_0^{(q^e-1)/\ell^v}$ has order exactly $\ell^v$. This gives the construction without a multiplicative-generator search or a factorization of $q^e-1$. [Shoup, deterministic construction of irreducible polynomials](https://www.shoup.net/papers/detirred.pdf)

## 4. Combine degrees and separate the optimization problem

Take a graph on $h$ labelled vertices. Select distinct odd primes $\ell_i$ different from p, all bounded polynomially in $h$, by sieving. Write $P=\max_i\ell_i$ and $C=h^2+h\lceil\log_2 P\rceil+1$. For each vertex set $m_i$ to the smallest power of $\ell_i$ at least $2^C$, so $2^C\le m_i<P2^C$. Build the tensor pair for each divisibility test $m_i\mid d$.

Use the field-uniform AND and OR gates from the rational extension proof over the chosen finite ground field. Briefly, wrap a concise pencil $M(w):V\to U$ using two additional labels $c=(x,y)$. Add the evaluation block $U\otimes F^{2*}\to U$ at $c$, and on isolated additional matrix coordinates add the three equally sized blocks $xI_b,yI_b,(x+y)I_b$, with $b>\dim U$. Every nonzero $c$ makes at least two of the three blocks nonzero over any extension. Therefore the rank threshold $\dim U$ recovers $W$ and its slices recover the original pencil. The evaluation block forces a scalar centroid, making direct-sum matching exact. Wrapped tuples with unequal padded formats encode ordered conjunction. The unordered pair of wrapped tuples $\{(T_0,S_0),(T_1,S_1)\}$ compared with $\{(T_0,S_1),(T_1,S_0)\}$ encodes disjunction, since the straight and crossed matchings correspond to the two input tests. A balanced conjunction of edge disjunctions has logarithmic depth and polynomial total size. The original construction and centroid proof are field-uniform. [Gate proof](RationalExtensionDegree.md#2-field-uniform-conjunction-and-disjunction)

At degree $d$, the resulting pair is isomorphic exactly when $\{i:m_i\mid d\}$ covers the graph. There is a successful extension, for example of degree $\prod_i m_i$. The minimum degree is the minimum product of $m_i$ over vertex covers, by pairwise coprimality. Hence if the requested cover size is $j$, positive cases have minimum at most $D=(P2^C)^j$, and negative cases have minimum greater than $D2^{h^2}$. This proves NP-hardness and the stated two-sided approximation gap. Specifically the written length is at most $h^B$ for a fixed B after increasing B to absorb constants, so choose $B\varepsilon<1$ and compare any approximate answer to $D2^h$ for sufficiently large h.

For a canonical raw input family, append a fixed-format graph header to each output as an identical direct summand whose compacted tensor has format $1\times1\times1$. Use $1\times1\times(1+h^2)$ with entries 1 then the adjacency array. The main tensor is itself wrapped to a format larger than $1\times1\times1$ after compaction. On arbitrary input first check length and the header for a simple labelled graph, regenerate the construction, and compare both raw arrays. This recognition is polynomial and is on these canonical arrays. There the degree-d test is just arithmetic on the binary input d and a cover test, so guessing d in binary establishes NP membership for the threshold decision on that family.

## 5. General context and a certificate for the degree spectrum

For any nonempty geometric transporter variety $X$, the admissible degrees are exactly the multiples of the Frobenius orbit lengths on the geometric connected components of $X$. Indeed, over the algebraic closure $X$ is a translate of the reduced stabilizer, which is a smooth algebraic group over a perfect field. Its components are translates of the connected identity component. A rational transporter at degree $d$ lies in a component fixed by $q^d$-Frobenius. Conversely each component fixed by that Frobenius is a homogeneous space for the connected identity component defined over $\mathbb F_{q^d}$, and Lang's theorem yields a rational point. This applies to all ordinary three-tensors. [Lang, Algebraic Groups over Finite Fields](https://doi.org/10.2307/2372673)

For format $(a,b,c)$, the number of such components is at most $3^{a^2+b^2+c^2}$. In the affine space of three matrix maps, the transporter equations all have degree at most three. Start with one irreducible component of weight $3^{a^2+b^2+c^2}$ and count the weight of each intermediate irreducible component $Y$ as $3^{\dim Y}\deg Y$. Imposing one new equation either contains a component or cuts it in dimension one less with sum of degrees at most $3\deg Y$, by the hypersurface form of Bézout. Components of dimension zero either survive or disappear. Thus total weight never increases, and intersecting with the open subset of invertible maps does not increase the number of irreducible components. These coincide with connected components for the transporter, because each is a coset of the connected identity component. In particular the minimum extension degree of any geometrically isomorphic side-$n$ pair is at most $3^{3n^2}$. The new lower bound grows exponentially in $n$; closing the gap between the two exponents would require a sharper theorem on Frobenius component orbits or another family of examples.
