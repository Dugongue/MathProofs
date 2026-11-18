# Newton polytopes of monotone oracle circuits

Informal proof of the affirmative answer to Grochow's published Open Question 5.6. The answer includes general monotone circuit reductions, with sharing and arbitrary nesting of oracle calls. It therefore includes the bounded-depth and weakly skew cases.

Grochow's question asks whether the exponential lower bounds of Theorems 4.2–4.5 for monotone projections from the permanent persist when the reduction may use a monotone arithmetic circuit with permanent oracle gates. The substantive targets in that range are the Hamiltonian-cycle, general perfect-matching, and cut polynomials. Lemma 4.3 is the conversion between affine and simple projections used in the original proof. The earlier ECCC version has shifted theorem numbering and the same oracle-reduction direction. [Grochow, Theory of Computing 13(18), §5, Question 5.6](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf#page=10), [ECCC revision](https://eccc.weizmann.ac.il/report/2015/171/revision/2/).

## 1. A polytope bound for general monotone c-reductions

A circuit is a finite acyclic graph whose nodes are constants, input variables, sum gates, product gates, or oracle gates. An oracle gate substitutes child polynomials into the arguments of its fixed formal polynomial. Each use of a child in a gate occupies a separate input slot, including repeated uses of the same child. We first work over the formal Boolean semiring, where a polynomial is specified by its finite monomial support, with addition given by union and multiplication by all pairwise products. Exponents retain their full multiplicities.

For a polynomial $F\ne0$, write $P(F)$ for its Newton polytope. For each gate $g$ let $K_g$ be its local exponent polytope on its slots. At a sum gate this is the simplex of ways to choose one input. At a product gate it is the single point with every slot used once. At an oracle gate for $G$ this is $P(G)$. In every case discard local monomials that use any identically zero child. The remaining local exponent polytope is the face obtained by setting the coordinates of zero children to zero, since local exponents are nonnegative. A gate with no remaining local monomials evaluates to zero. In topological order this prunes all zero gates from a circuit with nonzero output. Gates with zero inputs may equivalently be retained with no flow through them.

**Theorem.** Let $f$ be the nonzero output of such a circuit. For every live gate $g$ choose a bounded extended formulation $Q_g$ of its local exponent polytope $K_g$. If $Q_g$ uses $r_g$ inequalities, then
$$
\operatorname{xc}(P(f))\ \le\ \#\{\text{live circuit nodes}\}+\sum_g r_g .
$$
The number of equations and auxiliary variables is polynomial in the explicit circuit and chosen local formulations. In particular a circuit with $s$ ordinary nodes and wires and permanent oracle calls of sizes $m_1,\ldots,m_t$ satisfies
$$
\operatorname{xc}(P(f))=O\left(s+t+\sum_{j=1}^t m_j^2\right).
$$

To prove the theorem, introduce a nonnegative variable $z_g$ for the number of occurrences of node $g$ in an expanded parse. We use its average over parses, so it can be fractional. Introduce an outgoing slot-count vector $y_g$, constrained to lie in $z_gK_g$. This relation has an extended formulation with $r_g$ inequalities. In detail, if $Q_g=\{w:A_gw\le b_g,\ E_gw=d_g\}$ with projection $w\mapsto L_gw+\ell_g$, impose
$$
A_gw_g\le z_gb_g,\qquad
E_gw_g=z_gd_g,\qquad
y_g=L_gw_g+z_g\ell_g.
$$
When $z_g>0$ divide by it to recover the stated relation. When $z_g=0$ the first two constraints describe the recession cone of the nonempty bounded polytope $Q_g$, so $w_g=0$ and $y_g=0$.

Orient every wire from a gate to one of its argument slots. For the output node $o$ set $z_o=1$ and remove gates unreachable from $o$. For every other node $h$ impose the conservation equation
$$
z_h=\sum_{g,i: \ \text{slot }i\text{ of }g\text{ uses }h}y_{g,i}.
$$
Each input leaf labelled $x_j$ contributes its $z_h$ occurrences to the $j$-th coordinate of the projected vector. Constant leaves contribute zero. The system is bounded because the graph is acyclic and every local exponent polytope and its chosen lift are bounded. Induction from $o$ bounds each $z_h$ by the sum of parent occurrence bounds times the parent slot-degree bounds. This also bounds every $w_g$.

For one direction of exactness, a parse starts at the output and at each occurrence chooses one available local monomial. It makes as many copies of each child as specified by the monomial's local exponent. This terminates along the acyclic graph, and its leaves give a monomial in $f$. Conversely every monomial of $f$ arises from such a parse by the definition of formal Boolean sum, product and substitution. Each parse satisfies the conservation equations, and its total slot-count vector at each gate is the sum of local monomial exponents across its occurrences. It therefore gives a point in the extension. Convexity puts $P(f)$ in the projection.

For the reverse inclusion, take any feasible point. For each gate with $z_g>0$ choose a probability distribution on its available local monomials with mean $y_g/z_g$, which exists by the definition of $K_g$. Expand a random parse from $o$, drawing a fresh local monomial for each occurrence. Induction in the order from parents to children shows that the expected count of occurrences at every node $g$ is exactly $z_g$. Once the expected node count is known, the expected count sent along slot $i$ is $z_g(y_{g,i}/z_g)=y_{g,i}$. A node of zero expected count occurs with probability zero. Shared gates can receive occurrences through many parent slots and the linear conservation equation adds all of them. Thus the projected vector is the expected exponent vector of a parse monomial and belongs to $P(f)$. This proves equality.

For a permanent gate of size $m$, its local Newton polytope is the Birkhoff polytope. Restricting forbidden entries gives a face. The lift above is explicitly a nonnegative $m\times m$ matrix with each row and column sum $z_g$, and zeros at forbidden entries. The matrix coordinate counts the expected number of copies sent to the child in that slot. Sums need only slot nonnegativity and one equation, and products need only equations. These facts give the claimed cost for permanent oracles. The construction does not put any bound on the degree reached by repeated squaring or nested oracle calls.

## 2. Coefficient scope

The conclusion also holds whenever the coefficient semiring is zerosumfree and has no nonzero zero divisors, since the map taking a coefficient to whether it is nonzero commutes with addition and multiplication. The same support argument applies to nonnegative arithmetic over ordered fields.

Grochow's stated scope uses a weakly ordered commutative semiring. That definition permits a product of positive coefficients to be zero. A direct support replacement would therefore need an extra hypothesis. The three target families in Question 5.6 permit the following stronger transfer, which supplies the stated scope.

Work first when $1>0$ in the semiring. On nonnegative coefficients define $b(a)=0$ if $a$ is nilpotent and $b(a)=1$ otherwise. This is a semiring homomorphism to the Boolean semiring. To check multiplication, if $a,b$ are positive and $(ab)^k=0$, assume $a\le b$ by totality and use $a^{2k}\le(ab)^k=0$. The inequality uses monotonicity under multiplication by positive factors and the fact that multiplication by zero is the constant-zero map. Thus at least one factor is nilpotent. The converse is immediate by commutativity. For addition, a sum of two nilpotents is nilpotent by the binomial expansion. If either summand is nonnilpotent, monotonicity gives $0\le a\le a+b$ for that summand. Every power of $a$ is then at most the corresponding power of the sum, so the sum is nonnilpotent. The map preserves $0$ and $1$. In particular each nonzero natural multiple of $1$ maps to $1$, because it is at least $1$.

Apply this homomorphism coefficientwise to all formal polynomials in a monotone circuit, including those used by the oracle gates. Formal addition, multiplication and substitution commute with it. Every nonzero coefficient of the permanent and the three target families is a positive integer multiple of $1$. Thus their geometric supports are unchanged while unwanted nilpotent coefficients within the circuit can be discarded by working in the Boolean image.

If one allows the convention $1<0$ in the weak order, there are no positive elements. Indeed a positive $c$ would give $c=1c\le0c=0$. Consequently the only permitted nonnegative circuit constant is $0$, and every generated coefficient is a natural multiple of $1$. A positive integer multiple of $1$ is strictly below $0$ by additive monotonicity, so these coefficients also admit direct Boolean support replacement. This includes the case of repeated terms in the cut polynomial. [Grochow's semiring hypotheses and coefficient conventions, §2](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf#page=4).

## 3. The answer to Question 5.6

Grochow records the extension-complexity lower bounds $2^{\Omega(n)}$ for the Newton polytopes of the $n$-vertex Hamiltonian-cycle and general perfect-matching polynomials and for the cut polynomials with fixed parameter $q\ge2$. Their Newton polytopes are the corresponding TSP, perfect-matching and scaled cut polytopes. Apply the theorem above to a monotone permanent-oracle circuit for any of these formal polynomials. If $S$ counts its nodes and ordinary wires and $M$ is the largest permanent query dimension, the bound is $O(S(1+M^2))$. It follows that this product is at least $2^{\Omega(n)}$, so either the circuit size or its largest oracle dimension is exponential in $n$. If all explicit argument slots are charged, the total size itself is at least $2^{\Omega(n)}$.

This handles arbitrary-depth monotone c-reductions, as well as the bounded-depth and weakly skew restrictions posed in the question, without a degree bound on intermediate polynomials. Explicit monotone affine substitutions can be installed as ordinary sum and product gates, so the argument includes them. The bound works in the named real, tropical, and formal Boolean settings and under the paper's weak general semiring order by Section 2. Formal Boolean polynomial equality is the output contract here. Questions 5.1 and 5.2 concern agreement as functions on the Boolean cube, where duplicate powers can collapse. [Grochow, Theorems 4.2–4.5](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf#page=7), [Rothvoss on matching and TSP extension complexity](https://doi.org/10.1145/3127497), [Fiorini–Massar–Pokutta–Tiwary–de Wolf on combinatorial polytopes](https://arxiv.org/abs/1111.0837).

## 4. Application to tensor-isomorphism extension spectra

Fix a finite field $\mathbb F_q$ and a simple graph $G$ on $v$ vertices. Assign distinct odd primes $p_i$ of size polynomial in $v$ to its vertices, and form the finite étale multiplication tables from the edge construction below. For each edge $ij$, set $M=p_i p_j$. One side gets $M$ singleton field factors and one factor of degree $M$. The other side gets $p_j$ factors of degree $p_i$ and $p_i$ factors of degree $p_j$. Each edge contributes dimension $2M$ on both sides. For a power $t$ of Frobenius the difference of fixed-point counts for that edge is
$$
M(1-\mathbf 1_{p_i\mid t})(1-\mathbf 1_{p_j\mid t}).
$$
All summands are nonnegative. The multiplication tensors become isomorphic over $\mathbb F_{q^m}$ exactly when the set of primes dividing $m$ meets every edge. This follows since the two powered Frobenius permutations have the same cycle type if and only if their fixed-point counts agree at every power. Every vertex cover is realized by the product of its primes.

Let $F_{A,B}(X)$ be the formal polynomial with one monomial $\prod_{i:p_i\mid m}X_i$ for each distinct prime-support vector of a successful degree. Its Newton polytope is the vertex-cover polytope of $G$, which is affinely isomorphic to its independent-set polytope. Graphs of Göös, Jain and Watson therefore give such tensor-pair polynomials with extension complexity $2^{\Omega(v/\log v)}$. The theorem supplies the same lower bound on the charged size of arbitrary-depth monotone permanent-oracle circuits. The argument also applies to oracle families with other polynomial-size local Newton extensions. The source tensor dimensions and their dense input lengths are polynomial in $v$. [Göös–Jain–Watson](https://arxiv.org/abs/1604.07062).

## 5. Prior work and scope of the claim

The local-to-global flow proof is related to the directed-hypergraph model for acyclic discrete dynamic programming of Martin, Rardin and Campbell. That model uses variables for hyperarcs and studies projections onto original decision variables. Here the scaled local polytope formulation handles exponentially many choices at a permanent gate through its compact Birkhoff description. Grochow's original main lemma uses a single projection of a Newton polytope. Hrubeš and Yehudayoff, Theorem 5.6, bound Newton extension complexity in terms of ordinary monotone formula size. [Martin–Rardin–Campbell](https://doi.org/10.1287/opre.38.1.127), [Hrubeš–Yehudayoff, §5.4](https://users.math.cas.cz/~hrubes/PDFs/BirkNew4.pdf).

Hertrich and Loho, Theorem 3.1 and Propositions 3.3 and 3.5, bound the extension complexity of a support-function polytope through a monotone maxout network and epigraph polarity. Remark 3.4 charges the explicit number of affine choices at each maxout gate. Hertrich and Stargalla, Theorem 1.1, subsequently treat the assignment support function as a hard target for tropical circuits with scalar multiplication. In Question 5.6 the assignment function is available as a gate, and one must bound the entire composition while charging this gate polynomially rather than listing its permutations. Targeted source searches located no prior explicit answer to Question 5.6 in that model. Publication priority for the oracle consequence remains to be verified. [Hertrich–Loho, §3](https://arxiv.org/html/2411.03006v4#S3), [Hertrich–Stargalla, §§1–2](https://arxiv.org/html/2607.11540v2).
