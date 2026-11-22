# Exact tensor isomorphism profiles over finite-field extensions

Fix $k=\mathbb F_q$ and regard $\mathbb F_{q^e}$ as the probe of index $e$, for each positive integer $e$. The comparison runs through all finite extensions of one field on the same input tensors. Grochow and Qiao ask for complexity-class comparisons over different fields in journal Open Question 7.6. The result below determines the entire scalar-extension profile of ordinary tensor isomorphism over finite fields. It also quantifies minimum tensor side in a class of exact examples. The same-characteristic complexity reduction in the [existing portfolio proof](https://github.com/Dugongue/MathProofs/blob/5e2ab397cd7bcaaec1a54642f5e62c0558a8e77d/FixedCharacteristicTensorIsomorphism/Proof.md) is a different statement: it constructs new inputs for a different base field. [Grochow–Qiao, journal §7.2](https://par.nsf.gov/servlets/purl/10494304) · [arXiv Open Question 10.6](https://arxiv.org/html/1907.00309#S10.SS2).

## 1. Frobenius orbits determine every profile

**Theorem 1.** For any two same-format tensors $T,U$ over $k$, let $X$ be the ordinary invertible transporter scheme. If $X(\bar k)$ is empty, every test rejects. Otherwise let $m_1,\ldots,m_j$ be the orbit sizes of the $q$-power Frobenius on the geometric connected components of $X$. Then
$$
 T\cong_{\mathbb F_{q^e}} U
 \quad\Longleftrightarrow\quad
 m_i\mid e\ \text{for some }i .
$$
In particular if $k$ is algebraically closed in an arbitrary extension $E/k$, an ordinary tensor isomorphism over $E$ implies one over $k$. The formula holds for arbitrary tensor order and all characteristics.

*Proof.* Over $\bar k$, a chosen transporter identifies $X$ with the stabilizer of $T$ in the product of general linear groups. At the level of reduced schemes this identifies the geometric components with the translates of the reduced identity component. This connected group is smooth: over a perfect field the reduction of an algebraic group scheme of finite type is a smooth closed subgroup. Reduction and the reduced identity component are defined over $k$ here because $k$ is perfect. The set of components is finite and is a finite étale $k$-set. In particular an $E$-point determines an $E$-point of that component set. One can see the component map by first taking the reduced scheme and descending its finitely many disjoint open-and-closed geometric components under Galois descent. Field-valued maps always factor through reduction.

A point over $\mathbb F_{q^e}$ lies on a component fixed by the $e$-th Frobenius power. Conversely let $C$ be such a component and choose $x\in C(\bar k)$. There is $g$ in the reduced identity component of the stabilizer such that $\operatorname{Fr}^e(x)=xg$. Lang's theorem gives $h$ in that connected group with $h\operatorname{Fr}^e(h)^{-1}=g$, by applying the usual Lang map to $h^{-1}$. Hence $xh$ is fixed by $\operatorname{Fr}^e$ and is a transporter over the indicated finite field. This proves the formula. If $k$ is algebraically closed in $E$, an $E$-point on the finite étale component set lies on a component with residue field $k$, and the same argument gives a $k$-point. [Lang, *Algebraic groups over finite fields*](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf) · [Conrad, treatment of smoothness over perfect fields and Lang's theorem](https://math.stanford.edu/~conrad/249BW16Page/handouts/AMSalggroups2.pdf). $\square$

For ordinary tensor isomorphism of all formats over a fixed finite field, reflection along an arbitrary extension $E/k$ holds exactly when $E$ contains no proper finite extension of $k$. The forward obstruction is concrete: if $\mathbb F_{q^a}\subseteq E$ with $a>1$, compare the multiplication tensors of $\mathbb F_{q^a}$ and $k^a$. They become isomorphic over $E$ and are distinct over $k$ by connectedness of the spectra and the unital multiplication-tensor normalization proved in [the arithmetic profile note](ArithmeticTI.md).

## 2. Every finite union of divisibility cones occurs

**Theorem 2.** A set of positive integers is the isomorphism profile of a pair of ordinary three-tensors over $k$ exactly when it is a finite union of sets of multiples of positive integers. Every nonempty such profile occurs on the multiplication tensors of two equal-dimensional finite étale $k$-algebras.

*Proof.* Necessity is Theorem 1. For sufficiency let $M$ be the least common multiple of a finite nonempty list of desired acceptance moduli. On divisors $d$ of $M$, put $f(d)=0$ if $d$ is accepted, and $f(d)=M$ otherwise. For each $a\mid M$, define the signed integer
$$
 c_a=\frac{1}{a}\sum_{d\mid a}\mu(a/d)f(d).
$$
Each is integral since $a\mid M$. Take a permutation with $c_a$ cycles of length $a$ for positive $c_a$, and another with $-c_a$ cycles of length $a$ for negative $c_a$. They have the same total size since the sum of $a c_a$ is $f(M)=0$. If the two sets have size zero, add one fixed point on both sides. Realize the two cycle lists by products of finite fields of the corresponding extension degrees.

For any positive integer $e$, the difference of the numbers of fixed points of the $e$-th permutation powers is $\sum_{a\mid\gcd(e,M)}a c_a=f(\gcd(e,M))$. If $e$ is rejected this is nonzero. If it is accepted, all its multiples are accepted. Hence all powers of the two restricted permutations have identical fixed point counts, and the cycle lists agree by Möbius inversion. The corresponding finite étale algebras over $\mathbb F_{q^e}$ are then isomorphic. By unital normalization, ordinary multiplication-tensor isomorphism gives precisely that algebra isomorphism. The empty profile is realized by a zero tensor and a nonzero tensor of the same format. $\square$

## 3. The sharp minimum side for one divisibility cone

**Theorem 3.** Let $m\ge2$ and write $m=\prod_i p_i^{a_i}$ with distinct primes $p_i$. Among equal-dimensional finite étale multiplication tensor pairs whose isomorphism profile is exactly $m\mid e$, the minimum side is
$$
 \min_{J\subseteq\{1,\ldots,r\}}
 \max\left\{
       \sum_{i\in J}p_i^{a_i},
       \sum_{i\notin J}p_i^{a_i}
     \right\}.
$$
In particular the minimum is $m$ for a prime power $m$, and it is $\max(p^a,q^b)$ for $m=p^a q^b$ with $p\ne q$.

*Proof.* For a partition into two sides, put the cycle of length $p_i^{a_i}$ on the indicated side and pad the shorter side with fixed points. Under the $e$-th Frobenius power, that cycle splits into fixed points exactly when $p_i^{a_i}\mid e$. Otherwise it supplies nontrivial cycles of $p_i$-power length on that side. The other side has none of that prime type. The two cycle lists therefore agree exactly on the multiples of $m$, proving the upper bound.

For the lower bound let $\lambda$ be the least common multiple of every cycle length on both sides. Over the probe of degree $\lambda$ both permutations are trivial, so $m\mid\lambda$. For each $i$ assign the prime power $p_i^{a_i}$ to one particular cycle whose length is a multiple of that power. Whenever several distinct prime powers are assigned to one cycle their product divides the cycle length, and their sum is at most their product. A cycle with one assignment also has length at least that assigned power. Summing independently on the two sides yields a partition with both totals at most the common side. $\square$

The finite-field profile theorem distinguishes two proof systems in the questions on Polynomial Calculus. The ordinary transporter equations have no solution in the algebraic closure precisely when the whole profile is empty. Over the specified finite field they can have a negative decision even when some extension accepts. Adjoining field equations gives a complete refutation problem for this latter kind of negative. The [matrix congruence result](PC.md) estimates proof degree and size in that setting.

These are written proofs. Lang's theorem and the cycle reconstruction step are classical. The contribution here is the exact profile classification for all ordinary tensors and the sharp minimum side for the indicated finite étale realizations.
