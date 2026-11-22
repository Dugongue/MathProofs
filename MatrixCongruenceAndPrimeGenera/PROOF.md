# Sharp sparse Polynomial Calculus size for finite-field symmetric congruence

Let $F=\mathbb F_q$ have odd characteristic. For symmetric $n$-by-$n$ matrices $A,B$ over $F$, consider ordinary Polynomial Calculus (PC) on the entrywise equations
$$
 XAX^T-B=0,\qquad XY-I=YX-I=0,
$$
with field equations $z^q-z=0$ for every entry variable $z$ of $X,Y$. PC allows field-linear combinations and multiplication of an available line by a variable. Sparse size counts the expanded monomial occurrences in its lines.

**Theorem.** For every fixed odd $q$, all noncongruent symmetric pairs have PC refutations of degree $O_q(n)$ and expanded size $n^{O_q(n)}$, and have polynomial-size arithmetic-circuit IPS refutations. There is an explicit infinite family of nonsingular pairs requiring PC degree $\Omega(n)$ and sparse size $n^{\Omega(n)}$, with lower constants uniform over odd finite fields. The pairs are $I_n$ and $\operatorname{diag}(\nu,1,\ldots,1)$ for a fixed nonsquare $\nu\in F^\times$. In particular the lower bound concerns arithmetic noncongruence, which disappears over the algebraic closure, and persists with the field equations.

## Upper bounds for every symmetric pair

Every symmetric form over $F$ diagonalizes by elementary congruence. For completeness, a nonzero symmetric form has a vector with nonzero self-pairing by polarization, since $2$ is invertible. Split off that line and iterate until only the radical remains. Each nonzero diagonal entry can be made $1$ or $\nu$ by scaling. Any two entries equal to $\nu$ can be replaced by two entries equal to $1$. Indeed the set of squares including zero has size $(q+1)/2$, so there are $a,b\in F$ with $a^2+b^2=\nu$. The invertible matrix $K=\begin{pmatrix}a&b\\-b&a\end{pmatrix}$ satisfies $KK^T=\nu I_2$. Thus rank and the square class of the determinant of the nonsingular part classify the form.

If $\operatorname{rank}B>\operatorname{rank}A=r$, choose a nonzero $(r+1)$-minor of $B$. The matching minor of $XAX^T$ vanishes identically by rank factorization and Cauchy–Binet. Replace the entries of the determinant expansion individually using the congruence axioms. The terms telescope to the nonzero constant in degree $2(r+1)$. If $\operatorname{rank}A>\operatorname{rank}B$, put $G=XAX^T-B$ and $H=YX-I$. The identity
$$
 YBY^T-A=HA+AH^T+HAH^T-YGY^T
$$
first derives the reverse equations in degree at most four. The same argument applies to the reverse congruence.

If the ranks coincide, put both forms in constant bases with the nonsingular parts $A_0,B_0$ first, of common size $r$. This replaces $X$ by a constant linear change. Entries of its field axioms are linear combinations of those for $X$ by the $q$-Frobenius identity and the fact that its coefficients lie in $F$. The top-left principal block gives $PA_0P^T=B_0$, where $P$ is the top-left block of the changed $X$. Noncongruence means $\delta=\det B_0/\det A_0$ is a nonsquare. Put $t=\det P$. Telescoping each determinant summand gives $g=t^2-\delta$ in degree $2r$. Frobenius and determinant telescoping on the field equations give $f=t^q-t$ in degree $qr$. With $m=(q-1)/2$, set
$$
 S=\sum_{i=0}^{m-1}(t^2)^{m-1-i}\delta^i.
$$
Then $t Sg=t^q+t$ because $\delta^m=-1$. Subtraction of $f$ gives $2t$, and multiplication by $t$ and combination with $g$ gives $1$. Each multiplication by a polynomial stands for its expanded monomial-by-monomial PC derivation, and the maximum degree is at most $\max(4,qn)$. There are polynomially many variables, and expanded determinant telescoping and these multiplications take $n^{O_q(n)}$ size for fixed $q$.

The same argument yields polynomial-size circuit IPS certificates without an exponential determinant expansion. Use separate placeholder matrices for the two families of inverse axioms, the congruence axioms, and the field axioms. In the unequal-rank case with $\operatorname{rank}B>\operatorname{rank}A$, subtract the chosen minor of $XAX^T$ from the same minor with the congruence placeholders subtracted. At the zero placeholders the difference is zero, and at their true values it is the chosen nonzero constant. Divide by that constant. In the reverse direction form the polynomial with placeholders for the right-hand side of the reverse identity above, and use it in the same minor certificate. All these circuits use polynomial-size determinants.

For the equal-rank case, after the basis change let $U$ be the top-left block of changed congruence placeholders, and let $V$ be the field placeholders for the entries of $P$, obtained by the same scalar linear combinations as the actual field equations. Form
$$
 g_*=\frac{\det(PA_0P^T)-\det(PA_0P^T-U)}{\det A_0},
 \qquad f_*=\det(P+V)-\det P .
$$
They vanish when the input placeholders are zero and evaluate to $g,f$ at the true axiom values. The circuit
$$
 \frac{t(tSg_*-f_*)}{2\delta}-\frac{g_*}{\delta}
$$
has value zero in the first substitution and value one in the second. Standard division-free determinant circuits have polynomial size. The sum $S$ is computed by doubling geometric sums and repeated squaring, so the circuit size is polynomial in $n$ and $\log q$. This size statement counts field operations. In particular it does not add extension variables to ordinary PC.

## A local polynomial substitution from Tseitin

Use a family of bounded-degree expanders on $n$ vertices, with fixed maximum degree $\Delta$ and a positive lower bound on vertex expansion. Use one charge $1$ at a distinguished vertex and charge $0$ elsewhere. For each edge $e$ write the Tseitin sign variable as $s_e$, with axiom $s_e^2-1$. The equation at vertex $v$ is
$$
 \prod_{e\ni v}s_e-(-1)^{c_v}=0 .
$$
The Buss–Grigoriev–Impagliazzo–Pitassi lower bound gives degree at least $\gamma n$ for this sign system over every field of odd characteristic, with a fixed $\gamma>0$. These are precisely their mod-two binomial equations after the choice of sign convention. The graph is chosen only for the proof. The output pair of diagonal matrices does not depend on its edges.

Color the edges into at most $2\Delta-1$ matchings by the greedy edge coloring. For each sign assignment, start with the identity Gram matrix. In the round of a matching, when $s_e=-1$ at edge $uv$, toggle the square-class indicators at $u,v$ by a two-by-two basis change. For indicators $(0,0)$ use the matrix $K$ above, and for $(1,1)$ use $K^{-1}$. For unequal indicators swap the two coordinates. When $s_e=1$ use the identity. In each round the current indicator of a vertex is the parity of the negative incident signs from earlier rounds. Thus the entries of this block and its inverse are functions of only a constant number of signs at the endpoints. Write them as multilinear polynomials by interpolation on $\{-1,1\}^k$, valid since $2$ is invertible. Blocks at different edges of a round are disjoint.

Let $P_j$ and $Q_j$ be the resulting polynomial block matrices in round $j$, with $Q_j$ the pointwise inverse over sign assignments. Put $X_0=P_L\cdots P_1$, $Y_0=Q_1\cdots Q_L$, where $L\le2\Delta-1$. On every sign assignment they satisfy both inverse equations, and $X_0X_0^T$ is diagonal with entry
$$
 \frac{1+\nu}{2}+\frac{1-\nu}{2}\prod_{e\ni v}s_e
$$
at $v$. The support of a possible nonzero entry in either matrix lies at graph distance at most $L$ between its indices. Every such entry also depends on at most $b$ sign variables, for a constant $b$ depending only on $\Delta$. Indeed its product expansion follows paths of at most $L$ edge steps, and the coefficients on those steps depend only on the incident signs at the step endpoints. All these signs lie in a constant-radius ball. Take multilinear representatives modulo $s_e^2-1$ throughout.

Let $\pi$ be any permutation of the coordinate labels and let $S_\pi$ send the $j$th coordinate vector to the $\pi(j)$th. Substitute $X=X_0S_\pi,\ Y=S_\pi^{-1}Y_0$. The inverse equations and $XX^T=B$ have the same images as above because $S_\pi S_\pi^T=I$. More precisely, in the sign quotient the off-diagonal and inverse equations are zero, and each diagonal equation is $(1-\nu)/2$ times its vertex equation. The field equations also map to zero, because on each sign assignment the substituted entry belongs to $F$. Equality on all sign assignments is equality in the sign quotient, by multilinear interpolation.

For each line of a target PC refutation take its image in the sign quotient and use its unique multilinear representative. Addition gives the corresponding source linear combination. For multiplication by a target variable, multiply the mapped earlier line by its substituted polynomial, expanded into degree-at-most-$b$ monomials, then reduce powers using $s_e^2-1$. Each reduction is a monomial multiple of a sign axiom at no greater degree. Thus if the largest mapped degree is $D$, these operations give a Tseitin refutation of degree at most $\max(\Delta,2,D+b)$. Every target refutation therefore has a mapped line of degree at least $\gamma n-b$ for each permutation. Also a degree-$d$ target line maps to degree at most $bd$, which already proves the linear lower bound on target degree. No bound involving $q$ is needed for the simulation. The field axioms have zero image in the quotient directly.

## A permutation bound on sparse size

Draw $\pi$ uniformly at random. Fix one monomial in one target line and let its support graph be the bipartite graph on row and column labels, with an edge $(i,j)$ when $x_{ij}$ or $y_{ji}$ occurs at positive exponent. The same edge represents at most two target variables. Let $D_0$ bound the size of a radius-$L$ graph ball, independently of $n$. For its image to be nonzero, every edge $(i,j)$ must have $\pi(j)$ at distance at most $L$ from $i$. Thus its support graph must have maximum degree at most $D_0$ on both sides.

Each positive power of a substituted entry still depends on no more than its original $b$ sign variables, because its multilinear representative in the sign quotient uses only those coordinates. Consequently, for the monomial image to have degree at least $\gamma n-b$, the monomial must have at least $(\gamma n-b)/b$ distinct target variables. Its support graph then has at least $(\gamma n-b)/(2b)$ edges. With both degree bounds, greedily taking disjoint edges gives a matching of size at least the number of edges divided by $2D_0-1$. If a monomial meets these cardinality and degree conditions, fix a matching of size $k=\lfloor \eta n\rfloor\le n/2$ in its support graph, for a fixed $\eta>0$ small enough. This choice depends only on the monomial prior to selecting $\pi$.

The chance that all matched pairs have $\pi(j)$ in the required balls is at most
$$
 \frac{D_0^k}{n(n-1)\cdots(n-k+1)}\le \left(\frac{2D_0}{n}\right)^k .
$$
The selected columns are distinct, their images are an ordered sample without replacement, and each assigned row has at most $D_0$ permitted images. Monomials outside the cardinality or degree conditions cannot have the required nonzero image. For every $\pi$ some mapped line has degree at least $\gamma n-b$, hence some monomial occurrence has an image of that degree or higher. The union bound over all the original expanded monomial occurrences yields size at least $(n/(2D_0))^k=n^{\Omega(n)}$. This matches $n^{O_q(n)}$ for each fixed $q$. Its lower-bound constants depend on the expander family only and can be taken uniform over all odd finite fields.

## Rational forms and a simultaneous small-prime test

Let $d_1,\ldots,d_k$ be nonzero rational numbers, and consider the rational pairs $I_n,\operatorname{diag}(d_i,1,\ldots,1)$. Write each $d_i$ as $a_i/b_i$ for integers with $b_i>0$, and set $M=4\prod_i|a_i b_i|$. The rational pair is congruent exactly when $d_i$ is a rational square, by determinants and the diagonal square-root change of basis. At an odd prime $p\nmid M$, it is congruent modulo $p$ exactly when $(d_i/p)=1$. Every negative such residue gives the hard family above at that prime, with the same degree and sparse-size lower constants after adjusting the chosen nonsquare to the residue.

Under Dirichlet GRH, collect every prime $p\nmid M$ up to $3\,\operatorname{bitlength}(M)^2$. The binary matrix of quadratic-character signs at these primes has precisely the rational square-class dependencies of the $d_i$ as its kernel. For any binary exponent vector, the product of the $d_i$ taken to those exponents has a quadratic Dirichlet character of conductor dividing $M$ (use its square-free integral representative). If the product is a nonsquare, its character on units modulo $M$ is nontrivial. Bach's subgroup bound finds a prime in the list outside the kernel. If it is a square, every listed prime has character value $1$. This gives the converse too. In particular, every rational noncongruence in this family is witnessed at a listed prime with the proven PC/IPS separation. The conditional analytic input is solely this cutoff. The proof-complexity separation over any given odd finite field is unconditional.

## Relation to Open Question 7.3 and verification

Open Question 7.3 of Galesi, Grochow, Pitassi and She gives the literal congruence and inverse equations. Those equations are satisfied over the algebraic closure for the diagonal pairs above, so the arithmetic problem needs the added field equations. The earlier workspace proofs study geometric noncongruence, with degree three in characteristic zero and characteristic-sensitive degree bounds for the positive-characteristic transpose-pair method. The result here gives sharp worst-case degree and sparse size for symmetric inputs in the distinct finite-field formulation, and an explicit polynomial IPS circuit for each negative symmetric pair. It leaves arbitrary nonsymmetric inputs in this formulation unsettled.

The key new steps are the binary square-class toggle substitution and the column-permutation size argument. The Tseitin degree theorem, standard finite-field square classes, determinant identities, and Bach's conditional prime bound are prior results. The proof is written mathematics. The companion program checks 2,048 sign assignments on a fixed graph over four odd prime fields and 128 square-class products across 193 admissible primes in one list. These controls check the algebraic substitution and signature example. A Lean kernel check and independent priority review have not been performed.

[Galesi–Grochow–Pitassi–She, Question 7.3](https://arxiv.org/html/2305.19320#S7.SS3) · [Buss–Grigoriev–Impagliazzo–Pitassi, Theorem 10](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/lineargaps/journalfinal.pdf) · [Earlier geometric congruence bounds](https://github.com/Dugongue/MathProofs/tree/main/MatrixIsomorphismPC) · [Earlier characteristic-two geometric bounds](https://github.com/Dugongue/MathProofs/blob/main/IsomorphismCohomologyCrossovers/char2-matrix-congruence.md) · [Grochow–Pitassi, Ideal Proof System](https://arxiv.org/abs/1404.3820) · [Bach, small subgroup witnesses](https://doi.org/10.1090/S0025-5718-1990-1023756-8)
