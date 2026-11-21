# VNP-complete canonical IPS certificates from a negative 2-CNF prefix

For every field $F$ with more than two elements, there is a polynomial-size family of ordered unsatisfiable 2-CNFs whose canonical Grochow–Pitassi IPS certificates are VNP-complete under ordinary p-projections. Every clause before the last two is of the form $\neg p\lor\neg q$ on distinct variables. The last two are contradictory units on a fresh variable. More generally, the construction realizes any weighted Boolean acceptance polynomial as a p-projection, using a graph of maximum degree at most $9$ for the negative prefix.

Grochow–Pitassi's Open Question 7.8 concerns the particular certificate in equation (5) of their Lemma 4.2. The earlier MathProofs result establishes completeness using width-three clauses and treats the two-element field separately. The degree and clause restrictions above are the contribution here. [Grochow–Pitassi, Lemma 4.2 and Question 7.8](https://www.cs.toronto.edu/~toni/Papers/jacm-gp.pdf#page=27), [Earlier MathProofs proof](https://github.com/Dugongue/MathProofs/blob/9ec358c590d9db8580c49d21704a900976c1ac54/CanonicalIPSCertificates/PROOF.md)

## Canonical certificate and the terminal clause

Write $b(0,x)=1-x$ and $b(1,x)=x$. For an ordered unsatisfiable CNF $K_1,\dots,K_m$, let $A_i$ be the assignments whose first false clause is $K_i$, and let $V_i$ be the variables of that clause. The certificate from equation (5) is
$$
C(X,y)=\sum_i y_i\sum_{\sigma\in A_i}\prod_{j\notin V_i} b(\sigma_j,X_j).
$$
If the CNF is a prefix $\Gamma$ followed by $(t),(\neg t)$ on a fresh variable $t$, then $A_{(t)}$ consists exactly of the satisfying assignments of $\Gamma$, extended by $t=0$. The $t$ factor is omitted. Setting all other placeholders to zero selects
$$
y_{(t)}\sum_{\sigma\models\Gamma}\prod_{j\in\operatorname{vars}(\Gamma)}b(\sigma_j,X_j).
$$
We take the prefix variable list to include all variables of the construction. Any unconstrained variable contributes a sum of $1$.

## Implementing a positive clause with negative binary clauses

Choose $r\in F\setminus\{0,-1\}$, let $s=-1-r$, and put
$$
\alpha=\frac{r}{1+r},\qquad \beta=\frac{s}{1+s},
\qquad c=(1-\alpha)(1-\beta).
$$
Both denominators are nonzero, $c\ne0$, and $\alpha/(1-\alpha)+\beta/(1-\beta)=-1$.

Given a set $S$ of variables whose positive disjunction we want to impose, introduce two fresh auxiliary variables $a,b$. Insert $\neg a\lor\neg b$, and for each $v\in S$ insert $\neg a\lor\neg v$ and $\neg b\lor\neg v$. Specialize the formal variables for $a,b$ to $\alpha,\beta$ respectively. If at least one $v\in S$ is true, only $a=b=0$ is allowed and its weight is $c$. If all $v$ are false, the allowed pairs are $00,10,01$. Their weights sum to
$$
(1-\alpha)(1-\beta)+\alpha(1-\beta)+(1-\alpha)\beta
=c(1+r+s)=0.
$$
The same formula applies to $S=\varnothing$. Distinct copies of this construction use disjoint auxiliary variables and have no clauses between their auxiliary variables. For fixed values of the original variables, their weight sums therefore multiply. Each simulated positive clause of length $k$ uses two new variables and $1+2k$ negative binary clauses.

## Projection of the weighted acceptance polynomial

Let $R_n$ be a Boolean predicate on $r_n$ inputs given by a polynomial-size circuit, and let $d_n\le r_n$. Define
$$
P_n(x)=\sum_{\substack{u\in\{0,1\}^{r_n}\\R_n(u)=1}}
             \prod_{j=1}^{d_n}x_j^{u_j}.
$$
Use AND, NOT and copy gates, with fan-in at most two, and permit constant gates. First add a final copy gate as a designated output sink. Route multiple outgoing wires from an AND or NOT gate through a single copy gate, then use binary copy trees for every remaining fan-out above two. This adds at most linear overhead in the wire count. Every AND and NOT gate now has fan-out at most one, and every other control has fan-out at most two. Write a Tseitin CNF with a control variable per input and gate, a unit clause for each constant gate, and a unit clause requiring the output to be true. For an AND gate $w=p\land q$, use $(\neg p\lor\neg q\lor w),(p\lor\neg w),(q\lor\neg w)$. For a NOT gate $w=\neg p$, use $(w\lor p),(\neg w\lor\neg p)$. For a copy gate $w=p$, use $(\neg p\lor w),(p\lor\neg w)$. For each accepted input all control variables extend uniquely to satisfy this CNF. Let $M$ be the number of controls.

Construct the negative prefix $\Gamma$ as follows.

1. For each control $v$, introduce selectors $v_0,v_1$ and the binary clause $\neg v_0\lor\neg v_1$. Implement the positive clause $v_0\lor v_1$ by the two-auxiliary construction. Its zero weight on the all-false pair induces an exact-one choice in the weighted sum.
2. For each Tseitin clause, form the positive disjunction of its literal selectors. The selector of $v$ is $v_1$, and the selector of $\neg v$ is $v_0$. Implement this positive disjunction by the two-auxiliary construction. Deduplicate repeated selectors within a clause.
3. For each input feature $u_j$, introduce a new variable $w_j$. Implement the positive disjunction $(u_j)_0\lor w_j$ by the same construction. On an exact-one input selector pair, this disjunction requires $w_j=1$ if $u_j=1$ and leaves $w_j$ free if $u_j=0$.

Let $H$ be the total number of simulated disjunctions. Choose $\lambda\in F\setminus\{0,1\}$ and $\delta=\lambda(1-\lambda)$. In the certificate $C_n$, assign both formal selectors for every control the constant $\lambda$, the gadget variables the constants $\alpha,\beta$, and the feature variables $w_j$ the corresponding formal variables $x_j$. Put $y_{(t)}=\delta^{-M}c^{-H}$, and put every other placeholder and the formal $t$ equal to zero.

After summing over auxiliary bits, the surviving control selectors and features satisfy every simulated disjunction. They contribute the common factor $c^H$. Each exact-one selector pair weighs $\delta$, whichever bit it encodes, contributing $\delta^M$ in total. These factors cancel the distinguished placeholder. The feature sum for a fixed accepted input has factor $x_j$ when $u_j=1$. In the free case its factor is $b(0,x_j)+b(1,x_j)=1$. The unique Tseitin extension gives each accepted input exactly one term. The result is $P_n(x)$ as a formal polynomial over $F$. Each substituted quantity was either one target variable or a field constant, as required by an ordinary p-projection.

For the degree bound, view $\Gamma$ as the graph whose edges are its negative binary clauses. Each selector has one edge to its mate and two edges to the auxiliaries of its own pair. Every incoming control used in a gate occurs at most once per sign and per wire in that gate's clauses, counting repeated input wires individually. An AND or NOT output occurs at most twice per sign in its defining gate clauses and has at most one outgoing wire. A copy output occurs at most once per sign in its defining clauses and has at most two outgoing wires. The designated sink instead has one extra unit and no outgoing wire. A constant has one unit and at most two outgoing wires. An input has at most two outgoing wires and one feature disjunction. Thus each signed selector occurs in at most three additional simulated disjunctions. Each disjunction adds at most two edges incident to it, giving maximum selector degree $3+2\cdot3=9$. Each auxiliary has degree at most four and each feature variable has degree two. This uses only a polynomial-size circuit and polynomially many clauses.

## Completeness and the width-one case

Briquel and Koiran established VNP-completeness for ordinary monomial-weighted enumerators of monotone binary clauses. Here the weights are the exact Grochow–Pitassi interpolation weights, including the factors $1-X_j$ for zero bits. The cancellation calculation gives a direct p-projection in those coordinates and keeps the prefix graph degree bounded. [Briquel–Koiran, §3](https://perso.ens-lyon.fr/pascal.koiran/Publis/mfcs09.dichotomy_theorem.pdf#page=6)

Take $R_n$ to recognize directed Hamiltonian cycles on $n$ labeled vertices, with one input and one feature per possible loopless arc. A polynomial-time Boolean predicate checks one incoming and one outgoing edge per vertex and follows the unique successor from a fixed start to determine whether its orbit visits every vertex. The resulting $P_n$ is the Hamiltonian-cycle polynomial, which is VNP-complete under p-projections over every field. The canonical certificate family is in VNP by the exact upper bound of Grochow–Pitassi's Lemma 4.2. This proves the claimed completeness for $|F|>2$, including characteristic-two extension fields. [Grochow's statement of Hamiltonian-cycle completeness](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf#page=2)

For any ordered unsatisfiable CNF with clauses of width at most one, the first-false condition for a fixed clause is a conjunction of fixed bit values. It is inconsistent or defines a subcube. Summing the free coordinates gives $1$ per coordinate, so each surviving coefficient of a placeholder is a single product of fixed-bit factors. For $m$ clauses on $N$ variables the canonical family has arithmetic formulas of size $O(m(N+1))$.

## Formal polynomial semantics and verification

The pinned CompPoly declaration `CPoly.CMvPolynomial.eval₂Hom` defines substitution as a ring homomorphism into an arbitrary commutative semiring. Its equation `CPoly.CMvPolynomial.eval₂Hom_apply` identifies that homomorphism with `eval₂`. Instantiate the target with the computable multivariate polynomial ring on the $d_n$ output variables and use its constant coefficient map. Then mapping the certificate sum and its products under this homomorphism gives the formal substitution above, including the terms $1-x_j$ and their cancellation. The soundness calculation evaluates in a polynomial ring, so it applies over finite fields without identifying functions by agreement on field-valued inputs. [CompPoly, pinned substitution declarations](https://github.com/Verified-zkEVM/CompPoly/blob/c72a765272497b4c52201be11be47af5718c7488/CompPoly/Multivariate/MvPolyEquiv/Eval.lean#L83-L99)

The proof above is informal. The accompanying exact check enumerates the negative-prefix independent sets for small predicates and checks every output coefficient over $\mathbb Q$, $\mathbb F_3$, and $\mathbb F_4$. It tests cancellation in both odd characteristic and characteristic two.
