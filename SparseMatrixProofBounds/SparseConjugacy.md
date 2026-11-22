# The sparse size exponent for matrix conjugacy with fixed multiplicity gaps

Consider the ordinary Polynomial Calculus (PC) equations $XA=BX$, $XY=I$, $YX=I$ for matrices of side $n$. The variables are the entries of $X,Y$. Size counts nonzero monomial occurrences across lines, with the ordinary two-premise linear-combination rule. This is the encoding in Question 7.3 of Galesi, Grochow, Pitassi and She. [Question and equations](https://arxiv.org/html/2305.19320#S7.SS3)

**Theorem.** Suppose $A_n,B_n$ are displayed diagonal matrices over a field of fixed characteristic. Group their entries by common eigenvalue. For each mismatched eigenvalue $i$, the signed difference $g_i$ of its two multiplicities is a fixed nonzero integer, and its smaller multiplicity is at least $c n$ for a fixed $c>0$. Equal-multiplicity eigenvalues are unrestricted. Assume the nonempty list of mismatched gaps is fixed as $n$ grows. Write $G=\gcd_i |g_i|$. The minimum sparse PC size $S_n$ satisfies
$$
 \Omega(n^{2q})\le S_n\le O(n^{2q}\log(2n)),\qquad
 q=\begin{cases}1&\operatorname{char}F=0,\\p^{v_p(G)}&\operatorname{char}F=p.\end{cases}
$$
In particular $\log S_n/\log n\longrightarrow 2q$. The constants can depend on the fixed gaps and $c$. The lower bound permits proofs of arbitrary degree. The matrices may have their diagonal entries in any order.

For example take complementary diagonal idempotents with ranks $r$ and $r+4$ on matrices of side $2r+4$. The sharp power of $r$ is eight in characteristic two and two in every other characteristic. For integer diagonal families with fixed distinct integer labels, the same rule applies at **every** prime: merge labels that coincide modulo the prime, sum their gaps, and discard zero sums. If every merged gap vanishes, the reductions are conjugate. Otherwise apply the theorem to the merged multiplicities. Positive density on both sides for each original discrepant label suffices. All assertions refer to the displayed coordinates.

## A lower bound on matching degree after immediate normalization

Work on a complete bipartite board of $u$ rows and $v$ columns. In the quotient by $x_e^2=x_e$ and the products of distinct incident edges, a polynomial has a unique normal form $\sum_T a_T x_T$ indexed by partial matchings $T$. Indeed the multiplication table is union of compatible matchings and zero on a conflict, and evaluation on all partial matching indicators gives a triangular independence argument. A design of order $j$ assigns field values $\psi(T)$ for $|T|\le j$. For every $|T|<j$ the value is the sum over the extensions obtained by adding an edge at one prescribed row, and also at one prescribed column. A conflicting extension has value zero, and adding a present edge leaves $T$ unchanged.

We use Riis's normalized designs and extension of lower-order designs from the square terminal coordinates to rectangular boards in the range $2j\le\min(u,v)$ and $j<p^{v_p(v-u)}$ for unequal sides in positive characteristic. We use only the interior range of that construction. Order zero always allows the design with $\psi(\varnothing)=1$. [Riis, Sections 14.1–14.4](https://arxiv.org/html/2611.07280v1#S14)

Suppose a calculation takes linear combinations and multiplies by single edge variables with **immediate normal form**. If no line ever exceeds matching degree $j$, each line derived from the row and column totality equations pairs to zero with every design of order $j$, provided order-$j$ extensions on the board with one row and column removed are available. The totalities have this property by the recurrences if $j\ge1$. For $j=0$ a nonzero totality cannot occur as a usable normalized line.

To verify multiplication, fix an edge $e$ and a design $\psi$ on the original board. For $j\ge1$, set $\eta(U)=\psi(U\cup\{e\})$ for $|U|\le j-1$ on the board disjoint from $e$. Its recurrences follow by using those for $\psi$, since extensions conflicting with $e$ vanish. Extend $\eta$ to order $j$ there. Lift the extended design back by forcing $e$: set the value zero on conflicts with $e$ and use the extended value on the matching with $e$ removed if present in every other case. The row and column recurrences hold, including at a forced endpoint. Call this design $\phi$. If $f$ and the normal form of $x_e f$ both have degree at most $j$, then $\langle x_e f,\psi\rangle=\langle f,\phi\rangle$. For top-degree $T$ disjoint from both endpoints, $a_T$ must be zero: its contribution at $T\cup\{e\}$ would survive in degree $j+1$, and the unique possible parent of that size in $f$ is $T$. On every other matching the identity follows directly from the definition. At $j=0$ a multiplication between constant lines by a retained variable is possible only from the zero constant. Normalization therefore costs no extra degree here.

For disjoint boards with cutoffs $j_i$, take products of designs as linear functionals on the span of matching tuples with $|T_i|\le j_i$ for all $i$. For a multiplication in one board the same argument acts in that board, keeping all other designs fixed. The top-degree uniqueness also holds coefficientwise for each tuple of the other boards. Thus a refutation must contain a surviving monomial with $|T_i|\ge j_i+1$ on some board: product designs normalized at the empty matching separate the conclusion $1$.

## How likely is one monomial to witness that degree?

In an $r$-by-$s$ board with $s=r+g$, $g>0$, choose independently uniform sets of $u$ rows and $v=u+g$ columns. Call them live. Match their complements by a uniform random bijection, setting its entries to one. Set all other nonlive entries to zero. A live edge remains a matching variable. Row and column totalities restrict to zero or to live totalities.

For a fixed $k$-edge matching and exactly $j$ live edges, the probability that all its other edges are pinned to one is
$$
 \binom{k}{j}\frac{(u)_j(v)_j(r-u)_{k-j}}{(r)_k(s)_k}.
$$
Here $(a)_b$ is the falling factorial, zero when $b>a$. To obtain the expression, choose the live subset of the matching. The live and pinned endpoints have the prescribed statuses on each side, and the probability of the specified pinned bijection on $k-j$ coordinates contributes the inverse of $(r-u)_{k-j}$ whenever those statuses are possible.

In positive characteristic let $b=p^{v_p(g)}$, and otherwise let $b=1$. Take $u=2b$ and $v=2b+g$. Every sufficiently large $r$ is eligible. The restrictions leave a normalized design of order $b-1$, and the required extension after deleting an edge also lies in the range above. For fixed $g$, the probability that a given monomial survives with at least $b$ live edges is $O_g(r^{-2b})$, uniformly in its unrestricted support size. A collision among distinct original support edges always kills the monomial. Powers reduce to a single occurrence. For $k<2b$ use a union bound over the at most $\binom{2b}{b}$ choices of $b$ edges. Both endpoints of every chosen edge must be live, with probability $(u)_b(v)_b/((r)_b(s)_b)$. For $k\ge2b$, track just $2b$ prescribed edges. For them all to survive, each row is either live or its edge must be pinned to its prescribed column. Upon specifying the $j$ live rows, the probability of that live inclusion is at most $(u/r)^j$. Conditional on row choices, the necessary $2b-j$ pinned edges occur with probability at most $1/(r-u)_{2b-j}$, even after discarding the column-status penalty. Summing over the assignments gives $O_g(r^{-2b})$.

Now specialize $X$ within each mismatched eigenvalue block to its own rectangular matrix of matching entries, and specialize $Y$ to the transposes of these matrices with the eigenvalue labels reversed. Give equal-multiplicity blocks mutually inverse permutation matrices, and put all entries across different labels equal to zero. The intertwiner equations vanish. In each mismatched block, inverse-product off-diagonals vanish by collisions and diagonals reduce to row or column totalities. Sample the live restriction independently in each board. Every target variable becomes zero, one or a single edge. Thus the normalized restricted proof is precisely a calculation of the preceding kind.

For each restriction some original occurrence in the proof survives with at least $b_i$ live edges on board $i$ for some $i$. By the bound just proved, the probability for one fixed monomial is at most $\sum_i O_{g_i}(n^{-2b_i})=O(n^{-2q})$. A union bound over all original monomial occurrences proves the lower bound. This directly analyzes the proof in its original coordinates, so there is no loss from translating the size of refutations of disjoint systems.

## Sparse upper bound

Choose a discrepant eigenvalue giving the least $b_i=q$, and let $r<s$ be its two multiplicities. Entries of $X$ crossing unequal eigenvalues are scalar multiples of input linear equations and hence equal zero in PC. The matching diagonal blocks of the forward and reverse inverse products therefore give $PQ=I_s$, $QP=I_r$ on entries of $X,Y$, in the appropriate order. To remove the unwanted terms from each product entry, multiply a vanishing crossing entry by its companion variable and add the resulting monomials with binary balanced summation. Each required inverse entry costs $O(n\log(2n))$ monomial occurrences. If $q=1$, only $r+s$ diagonal entries are needed. Their two traces differ by a nonzero constant; balancing these sums gives total size $O(n^2\log(2n))$.

For $q>1$ deriving all the block products first costs $O(n^3\log(2n))$. The coefficient of $z^q$ in $(1+z)^s-(1+z)^r$ is nonzero in the field, because $s-r$ is divisible by $q$ and $(s-r)/q$ is prime to $p$. The sums of the size-$q$ principal minors of $PQ$ and $QP$ agree identically, by Cauchy–Binet. Comparing the same coefficient at the two identity matrices therefore yields a contradiction. Here out-of-range minors contribute zero.

For the cost in ordinary PC, each term in the principal-minor expansion is a product $z_1\cdots z_q$ of entries of $PQ$ or of $QP$. Let $\delta_i$ be the corresponding identity entries. Start from $z_i-\delta_i$ and derive $f_t=\prod_{j\le t}z_j-\prod_{j\le t}\delta_j$ recursively by
$$
 f_{t+1}=z_{t+1} f_t+(\delta_1\cdots\delta_t)(z_{t+1}-\delta_{t+1}).
$$
Each $z_{t+1}$ is a sum of at most $n$ quadratic monomials. Multiply by their two variables successively and add the resulting lines by a balanced tree. The products at stage $t+1$ cost $O(n^{t+1}\log(2n))$ since $f_t$ has at most $n^t+1$ monomials. There are at most $2 n^q$ determinant terms. Adding all signed conclusions in a balanced tree costs $O(q n^{2q}\log(2n))$, including all intermediate expanded lines. The nonconstant terms cancel as polynomial identities. This proves the upper bound for the literal original equations.

## Growing gaps and the linear-degree regime

For the single family of complementary idempotents with ranks $r,r+q$ and $q=p^a$, the same argument, using one shared board for the two blocks, gives absolute constants $C_0,C_1$ such that when $r\ge C_0q$,
$$
 \left(\frac{r}{C_1 q}\right)^{2q}
 \le S \le O\!\left(q(2r+q)^{2q}\log(2r+2q)\right).
$$
For the lower estimate put $u=2q$, $v=3q$. In the small-support case $\binom{2q}{q}\le 4^q$ and $(u)_q(v)_q/((r)_q(s)_q)\le(6q^2/r^2)^q$. In the large-support case $r-u-2q\ge r/2$ once $r\ge 8q$, so the probability is at most $(2q/r+2/r)^{2q}$. This proves the displayed bound. In particular, for $q\le r^{1-\varepsilon}$ the sparse size is $r^{\Theta_\varepsilon(q)}$ for sufficiently large $r$. If $q=r^{o(1)}$ tends to infinity, $\log S/(q\log r)\to2$.

The sharp power for fixed gaps and the matching-normalization proof strengthen the earlier exponential-in-degree lower bounds. When the smallest multiplicity and its gap are proportional to $n$, the general argument gives an exponential lower bound by retaining a fixed fraction of a hard board, while the available upper bound is $n^{O(n)}$. The factorial-versus-exponential distinction there and sharp sparse bounds in arbitrary dense coordinates remain open in this analysis. No analytic number theory enters the proofs. [Earlier proportional-gap lower bound](https://github.com/Dugongue/MathProofs/blob/main/TensorSparsePCBounds/Proof.md)
