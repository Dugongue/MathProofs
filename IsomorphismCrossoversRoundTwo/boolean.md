# Abelian Cayley-table canonization in uniform FOLL

**Theorem.** For finite abelian groups of unrestricted order and exponent, given by binary-encoded Cayley tables under arbitrary labelings, isomorphism and the computation of a canonical representative table have deterministic logspace-uniform Boolean circuits of polynomial size and depth $O(\log\log n)$, where $n$ is the group order. The gates are unbounded fan-in AND and OR, with negated input literals. For every fixed exponent bound $E$, the same decisions and canonical outputs on inputs of exponent dividing $E$ admit logspace-uniform constant-depth polynomial-size circuits. If only one input in the decision problem is promised abelian, a nonabelian second table is rejected at constant extra depth.

The representative output is the table of a standard product of cyclic prime-power groups. The theorem does not compute a label-by-label isomorphism to that standard table.

## 1. Complete invariants with a multiplicative gap

For each prime $p\mid n$, write $e_p=v_p(n)$, and for $1\le j\le e_p$ set
$$
K_{p,j}(G)=\{x\in G:x^{p^j}=1\}.
$$
In an abelian group this is a subgroup, all of whose elements have $p$-power order. Write $c_{p,j}(G)=\log_p |K_{p,j}(G)|$, and set $c_{p,0}(G)=0$. If the elementary divisors of the $p$-primary subgroup are $p^{a_1},\ldots,p^{a_\ell}$, then $c_{p,j}=\sum_i\min(j,a_i)$. Thus $c_{p,j}-c_{p,j-1}$ gives the number of cyclic factors of order at least $p^j$, and consecutive differences give the multiplicity of each cyclic order. The collection of kernel sizes is a complete isomorphism invariant. Unlike the counts of elements of an individual exact order, these sizes are always powers of $p$, so consecutive possibilities differ by a factor of at least two.

The circuit in the next section, on a bit vector of length $n$ and a hardwired $a$ with $1\le a\le n$, returns 0 at Hamming weight at most $a$ and 1 at weight at least $2a$. Use it on $x\mapsto[x\in K_{p,j}(G)]$, for $a=p^t$ and $0\le t<e_p$. Its output is then exactly $[c_{p,j}>t]$ on all promised inputs. Comparing these Boolean vectors for two groups is a constant-depth bitwise equality test.

## 2. Uniform multiplicative-gap threshold circuits

Choose a prime $q$ with $100n<q<200n$, by Bertrand's postulate. For a chosen scale $a$, put $b=\lfloor q/(4a)\rfloor$. For each $u,v\in\mathbb F_q$, take the OR of the input bits at all labels $x\in\{0,\ldots,n-1\}$ for which
$$
ux+v\bmod q<b.
$$
This yields $q^2$ output bits. In the following analysis choose $u,v$ uniformly, solely to compute the fraction of those output bits equal to 1. The circuit itself enumerates every pair.

For any two distinct labels, their images under the randomized affine map are independent uniform elements of $\mathbb F_q$. The two equations for $u,v$ have a unique solution since the difference of their labels is nonzero modulo $q$. This includes the cases $u=0$ in the enumeration. Thus for any fixed support set $S$ of active input bits, the hit count $Y$ has paired independent indicator summands, each with mean $b/q$. Writing $\mu=|S|b/q$, we get
$$
\Pr(Y>0)\le\mu,\qquad
\mathbb E[Y^2]\le \mu+\mu^2,\qquad
\Pr(Y>0)\ge \frac{\mu}{1+\mu}\quad(\mu>0).
$$
The lower bound is Cauchy–Schwarz applied to $Y\mathbf 1_{Y>0}$. If $|S|\le a$, then $\mu\le1/4$. If $|S|\ge2a$, then $\mu\ge 2a(1/(4a)-1/q)>0.48$, and the hit fraction exceeds $0.48/1.48>0.32$. This argument works for every subset of labels without assumptions about their order or distribution.

Separate fractions at most $1/4$ from fractions at least $8/25$ by uniform constant-depth approximate majority. To apply the usual $1/3$ versus $2/3$ version directly, use the following constant amplification. Given the hit bits, enumerate all ordered length-1,000 tuples of their indices, with replacement. For each tuple test if its sample fraction exceeds $0.285$. Each local test is a fixed constant-size circuit, independent of $n$. The fraction of successful tuples in the two cases is respectively below $1/3$ and above $2/3$, by Hoeffding's bound $e^{-2\cdot 1000\cdot(0.035)^2}<1/3$. Use the deterministic uniform approximate-majority circuit on the whole tuple list. Polynomial size is preserved, since the sample length is an absolute constant. This establishes the multiplicative-gap comparison with no exact threshold gates.

For uniformity, all small integer values used to generate the circuit can be produced in logarithmic work space. Trial division finds $q$ using counters of $O(\log n)$ bits. The wiring condition $ux+v\bmod q<b$ involves only $O(\log n)$-bit integers. Each tuple index, and the counters enumerating the tuples, use $O(\log n)$ bits with a fixed constant multiplier. The final circuit can use Ajtai's DLOGTIME-uniform constant-depth approximate majority, which is in particular logspace uniform. [Viola, On Probabilistic Time versus Alternating Time, Table 1 and note 3](https://www.cs.columbia.edu/~viola/papers/BPvsE.pdf).

## 3. Power predicates and the Boolean depth bound

The classical table-power predicate $x^k=y$, for $1\le k\le n$, is computable in uniform FOLL by Barrington, Kadau, Lange and McKenzie. Its table encoding can be taken as the ternary relation for products $T(a,b)=c$. Binary table entries give this relation by comparing one addressed cell to the fixed candidate value via an AND of literal bits. Conversely, the relation gives each table bit by taking an OR of all products whose value has that bit equal to 1. These changes are logspace-uniform constant-depth transformations. The identity element has a constant-depth test: all its row and column products must equal the other operand. One may therefore OR over the candidate identity labels after checking the power predicate. No supplied identity label is needed. [Barrington–Kadau–Lange–McKenzie](https://doi.org/10.1006/jcss.2001.1764) · [Chattopadhyay–Torán–Wagner, Lemma 7](https://drops.dagstuhl.de/storage/00lipics/lipics-vol008-fsttcs2010/LIPIcs.FSTTCS.2010.317/LIPIcs.FSTTCS.2010.317.pdf).

Compute $p\mid n$, $e_p$, and the exponents $p^j,p^t$ at circuit construction time by trial division and integer multiplication in $O(\log n)$ space. All power tests run in parallel, with the constant-depth threshold circuits above composed afterward. There are polynomially many queries and all copies have polynomial size. This gives depth $O(1+\log\log n)$. A table is abelian if it is symmetric, which is another constant-depth test. If desired, a total language can reject invalid group tables too: range and identity conditions, the existence of inverses, and associativity all have constant-depth circuits by enumerating the bounded number of intermediate table labels in each check.

Under the promise that the exponent divides fixed $E$, only primes dividing $E$ and exponents $j\le v_p(E)$ are needed, since $K_{p,j}$ has stabilized at the full Sylow subgroup by that point. Each needed $p^j$ is numerically bounded. One constant-depth implementation disjoins over all possible intermediate labels in the product of $p^j$ copies of $x$, with a conjunction of the associated table-cell comparisons. The exponent is fixed, so the enumeration is polynomial and logspace uniform. Thus the same invariant and comparison have constant depth in this case.

## 4. Outputting a canonical table

For every order $n$, enumerate the lists of cyclic prime-power factors with product $n$, sorted by their numerical orders. The list can be represented by a self-delimiting binary encoding of each factor order $d\ge2$, of length at most $2\lceil\log_2(d+1)\rceil+1$ bits per factor. The total encoding length is $O(\log n)$ since $\sum_d \log_2 d=\log_2 n$, with factors counted with multiplicity. Thus one can enumerate all candidate encodings in polynomially many cases. A logspace construction checks validity, nondecreasing order, that each factor is a prime power, and that the product is $n$. An empty list is allowed at $n=1$. Each valid list gives one isomorphism type and a fixed kernel profile. Restrict to factor orders dividing $E$ in the fixed-exponent variant.

Using the computed invariant from Sections 1–3, test equality to each hardwired profile in parallel. Exactly one list matches. For each output table bit, take the OR of the match bits of those lists whose predetermined representative table has a 1 in that position. The table for a list is obtained by identifying labels with their mixed-radix digits, adding two digit tuples modulo the corresponding cyclic orders, and returning the resulting mixed-radix label. Given the list encoding and the two labels, the circuit construction machine scans the list, maintains the radix prefix and encoded output, and uses integer arithmetic on $O(\log n)$-bit integers. It computes each hardwired bit in logarithmic work space. The selection step adds constant depth, so the same bounds apply to the canonical output.

## 5. Relation to the earlier circuit bounds

Chattopadhyay, Torán and Wagner's Theorem 8 gives $\mathsf{TC}^0(\mathsf{FOLL})$ and uses threshold circuits to sort unrestricted order multisets. Grochow and Levet use restricted majority computations for exact order-class cardinalities. Collins, Grochow, Levet and Weiß, Theorem 4.1, use a different power-testing routine and still compare exact order counts through one majority gate after choosing a prime power. Here cumulative order classes are subgroups, and their cardinality gaps make the threshold stage unnecessary. The result is an informal theorem using classical powering and approximate-majority algorithms. A targeted search located the earlier threshold bounds and did not locate this exact uniform FOLL decision-and-canonical-output claim. Publication priority remains unestablished. [Earlier $\mathsf{TC}^0(\mathsf{FOLL})$ theorem](https://drops.dagstuhl.de/storage/00lipics/lipics-vol008-fsttcs2010/LIPIcs.FSTTCS.2010.317/LIPIcs.FSTTCS.2010.317.pdf) · [Collins–Grochow–Levet–Weiß, Section 4](https://arxiv.org/html/2402.00133v5#S4).

The result gives neither a fixed-depth bound for unrestricted exponents nor a depth-three lower bound or upper bound for general Group Isomorphism. Grochow–Kardeş–Levet Question 7.2 concerns that general problem. [Open Question 7.2](https://arxiv.org/html/2608.26257v2#S7).
