# Stretched-exponential CNF and DNF lower bounds for Group Isomorphism

**Theorem.** For infinitely many group orders $n$, deciding isomorphism from binary-encoded Cayley tables requires at least $2^{\Omega(\sqrt n)}$ clauses in a Boolean CNF and at least $2^{\Omega(\sqrt n)}$ terms in a Boolean DNF. The promise consists of valid tables for two Abelian groups of exponent dividing nine. For each polarity the second table can be fixed. The CNF bound answers Grochow, Kardeş and Levet's Question 7.1 affirmatively and exceeds its $n^{\Omega(\log^2 n)}$ target. The DNF bound strengthens the previously established affirmative answer to their Question 7.3. [Original questions](https://arxiv.org/html/2608.26257v2#S7)

For two Abelian groups of exponent dividing four, the same proof gives both bounds with exponent $\Omega(n^{1/3})$ at every order $n=8^r$ for $r\ge2$. A further variant uses the same fixed reference for both polarities.

## 1. A criterion from partial multiplication tables

Let $K,J$ be nonisomorphic Abelian groups of the same order $n$. Encode elements by the binary strings for labels $0,\ldots,n-1$, using $\lceil\log_2 n\rceil$ bits per label. The identity has label $0$. Suppose that any collection of cells of any labeled table of $K$ can be matched by a labeled table of $J$ with the same identity label, provided the operands, results and identity of those cells together use at most $t$ distinct elements. Suppose also that at most $4n/5$ labels have any specified value in any bit position. Set
$$
h=|K[2]|,\qquad q=\left\lfloor 10^{-5}\min(t,n/h)\right\rfloor.
$$
For the applications below $t\le\sqrt n$ and $q$ tends to infinity. We prove that every conjunction of prescribed Cayley-table bit values that fails on every labeling of $J$ has probability at most $2^{-\Omega(q)}$ under a uniform random labeling of $K$ fixing the identity.

This suffices for the CNF bound by fixing a table of $J$ as the second input. A clause can be false on a labeling of $K$ only if its falsifying conjunction fails on every labeling of $J$. The falsifying conjunctions cover all labelings of $K$. For the DNF bound fix a table of $K$ as the second input. A term can be true on a labeling of $K$ only if it fails on every labeling of $J$. The terms cover all labelings of $K$. In either case a union bound forces at least $2^{\Omega(q)}$ clauses or terms, respectively. Both arguments use valid tables and permit nonuniform circuits.

## 2. Large conjunctions are rare under random labelings

Consider a conjunction from the criterion. Substitute the fixed values in the identity row and column. If these violate the conjunction, its probability is zero. Otherwise delete those requirements. Merge the cell positions $(x,y)$ and $(y,x)$ since both groups are Abelian. Call the resulting family of used cells $\mathcal E$. Whenever the conjunction holds on $K$, the operands and results of $\mathcal E$, together with the identity, must use more than $t$ distinct elements. Otherwise the partial-table hypothesis supplies a labeling of $J$ satisfying the conjunction.

Write $v$ for the number of distinct operand labels in $\mathcal E$. The preimages of any prescribed list of distinct nonzero labels are uniform distinct elements of $K\setminus\{0\}$.

**Few operand labels.** If $v\le t/2$, condition on all operand preimages. This determines the result elements of every used cell. If the operands, results and identity use at most $t$ distinct elements, the conjunction cannot hold. Otherwise more than $t-v-1\ge t/2-1$ distinct nonzero result elements lie outside the operand set. Select $q$ of them and choose one specified bit from a used cell producing each of them. This selection uses only the exposed preimages, and all $q$ result labels are still unexposed.

**Many operand labels.** Suppose $v>t/2$. If at least $v/2$ labels occur in diagonal cells, select $q$ such cells. Otherwise at least $v/2$ labels occur in off-diagonal cells. In the graph of off-diagonal used cells, take an inclusion-minimal edge cover of all nonisolated vertices. Every edge has an endpoint of degree one, since an edge with both endpoints of degree at least two could be deleted. Thus every component of the edge cover is a star. Choose one center in each component, including one endpoint when there are two vertices. The graph of the cover has at least $v/4$ distinct leaves. Select $q$ leaves and their incident cells. The selected forest has at most $q$ centers, none of which is a selected leaf.

For diagonal cells, expose the preimages $a_i$ of the selected labels one by one. Maintain a list of active results, all distinct and avoiding zero and every operand preimage revealed so far. Step $i$ is bad if $a_i$ hits an active result, or if $2a_i$ hits zero, a revealed operand preimage, or an active result. The case $2a_i=a_i$ is impossible since $a_i\ne0$. Every other forbidden target for $2a_i$ is fixed before the reveal, and each has at most $h$ preimages under doubling. There are at most $2q+1$ such targets and at most $q$ active results that the operand itself could hit. At a good step add the new result to the list. At a bad step skip that addition and remove any old result equal to the new operand preimage. This removes at most one old result.

For a star forest, first expose the preimages of all selected centers, then expose the leaf preimages $b_i$ one at a time. Let $a_i$ denote the known preimage of the center of its cell. Use the same list with candidate result $a_i+b_i$. A step is bad if $b_i$ hits an active result or if $a_i+b_i$ hits zero, an exposed operand preimage, or an active result. The equality $a_i+b_i=b_i$ is impossible, and all the other forbidden values are fixed before the reveal. There are at most $3q+1$ prohibited results and at most $q$ prohibited operand values. Translation by $a_i$ is a bijection. Each good step adds one result, and each bad step skips the addition and removes at most one old result.

In both patterns fewer than $2q+1$ labels are unavailable while sampling an operand preimage. Conditional on any previous history, each bad-step probability is at most $16 qh/n\le 16\cdot 10^{-5}<2^{-12}$ for all sufficiently large $n$. With any uniform conditional bound $\delta$, the probability of at least $\lceil q/4\rceil$ bad steps is at most
$$
\binom q{\lceil q/4\rceil}\delta^{\lceil q/4\rceil}.
$$
For any prescribed indices this follows by repeated conditioning, then by a union bound over index sets. The displayed estimate is at most $2^{-q}$. With fewer bad steps at least $q/2$ active results remain, distinct from all selected operand preimages and from zero. For each result choose one specified bit from its cell.

In both operand-count cases the selected result elements, their source cells and the specified bits were chosen using only the revealed operand preimages. Their labels are a uniform sample without replacement from the unused labels. Throughout the exposure of the selected result labels, at least $n-v-q-1$ labels remain in the few-operand case and at least $n-3q-1$ labels remain in the many-operand case. Both counts exceed $9n/10$ for large $n$, since $t\le\sqrt n$. No specified bit value occurs on more than $4n/5$ labels in the entire label set. Conditional on any previously exposed result labels, the next prescribed bit therefore has probability at most $8/9$. Except on an event of probability at most $2^{-q}$, or a preimage profile on which the conjunction is impossible, there are at least $q/2$ such result bits. The conjunction's probability is at most
$$
2^{-q}+(8/9)^{q/2}=2^{-\Omega(q)}.
$$

## 3. Two Abelian types give the square-root exponent

Take $n=3^k$ for $k\ge2$ and let
$$
K=C_3^k,\qquad J=C_9\times C_3^{k-2}.
$$
The groups are nonisomorphic because they have different exponents. For any partial table from $K$ using an element set $S$ of size at most $t=\sqrt n/2$, choose $z\in K\setminus(S-S)$. The difference set has size at most $|S|^2\le n/4$ and contains zero, so $z$ exists and is nonzero. Since $S-S$ is closed under negation, neither nonzero element of $\langle z\rangle$ lies in it. Thus quotienting by $\langle z\rangle$ is injective on $S$. The quotient is $C_3^{k-1}$, which embeds as a subgroup of index three in $J$. Transport the old labels of $S$ to the images, and extend the partial labeling arbitrarily to the rest of $J$. A homomorphism preserves every queried product and keeps the identity's label. This proves the partial-table hypothesis.

To get balanced binary labels, restrict to those $k$ satisfying $n\ge(5/4)2^{\lfloor\log_2n\rfloor}$. Infinitely many $k$ qualify. If the ratio $n/2^{\lfloor\log_2 n\rfloor}$ is in $[1,5/4)$ at $k$, multiplication by three puts the next ratio in $[3/2,15/8)$. At the top bit, the two bit classes have sizes $2^{\lfloor\log_2 n\rfloor}$ and $n-2^{\lfloor\log_2 n\rfloor}$, both at most $4n/5$. In any lower bit of weight $w$, the class sizes differ by at most $w\le n/2$, by the alternating blocks of length $w$. Neither class exceeds $3n/4$. Finally $h=|K[2]|=1$ since $K$ has odd order. The criterion gives $q=\Theta(\sqrt n)$ and proves both claimed bounds.

## 4. Exponent-four versions

Take $n=8^r$ and the lower and higher square-rank types
$$
K=C_4^{r-1}\times C_2^{r+2},\qquad J=C_4^r\times C_2^r.
$$
Here $|K[2]|=2n^{2/3}$ and $|2K|=n^{1/3}/2$. For $|S|\le t=n^{1/3}/2$ one can choose $z\in K[2]\setminus(2K\cup(S-S))$, because $|S-S|\le t^2$ is smaller than $|K[2]\setminus 2K|$. The quotient by $\langle z\rangle$ is injective on $S$, has order $n/2$, and has the same square subgroup size as $K$. By the Abelian group classification it is $C_4^{r-1}\times C_2^{r+1}$, which embeds in $J$ with index two. This gives partial-table completion. Binary bit classes are exactly balanced since $n$ is a power of two. Now $q=\Theta(n^{1/3})$ in the criterion.

The same fixed reference can be used in both polarities at orders $n=4^r$, using $K=C_4^{r-1}\times C_2^2$, $J=C_4^r$ and $t=n^{1/4}/2$. These groups have $|K[2]|=2\sqrt n$, $|2K|=\sqrt n/2$, and $|J[2]|=|2J|=\sqrt n$. The preceding low-to-high completion works since $|S-S|\le\sqrt n/4$. For high-to-low completion choose any nonzero $z\in J[2]$ outside $S-S$. Quotienting by $\langle z\rangle$ preserves the chosen products and divides the square subgroup size by two. Both quotients have type $C_4^{r-1}\times C_2$, which embeds with index two in the respective target. Use $J$ as the fixed reference, sample $K$ for the CNF and $J$ for the DNF, and apply the probability bound in each direction. This gives $2^{\Omega(n^{1/4})}$ with that single fixed reference.

Grochow, Kardeş and Levet's published CNF lower bound $n^{\Omega(\log n)}$ uses canonically labeled groups and affine matrix restrictions. This proof uses arbitrary labelings to obtain both partial multiplication completion and small mass for conjunctions that rule out an entire group type. Recent algebraic query lower bounds for Abelian Group Isomorphism also use random labels. The argument here controls conjunctions on binary table bits directly. [Grochow–Kardeş–Levet](https://arxiv.org/html/2608.26257v2#S4.SS2) · [Bshouty](https://arxiv.org/abs/2610.08280)

This is an informal proof. The established bound is stretched exponential in the group order.
