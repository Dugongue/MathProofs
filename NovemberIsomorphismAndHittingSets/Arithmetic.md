# A local obstruction to 3CNF hitting sets and the status of test modules

## A negative answer for the Boolean-axiom map in Open Question 3

Grochow, Kumar, Saks, and Saraf ask for circuit classes with known hitting sets whether the polynomial map of a family of unsatisfiable 3CNFs can have an image that hits every nonzero polynomial of the class. Their question explicitly also asks whether, for certain classes, no hitting set of that form exists. The map in the preceding definition includes the standard clause-falsity polynomials and the Boolean-axiom polynomials $x_i^2-x_i$. [Original Open Question 3 and the map preceding it](https://arxiv.org/html/1701.01717#S4.SS2)

**Theorem.** Over any field, the full polynomial map of any 3CNF with at least one clause has a nonzero vanishing polynomial that uses at most four output coordinates and has total degree at most 12. Thus it cannot be a hitting set for any class that contains all polynomials of this constant arity and degree on any choice of output coordinates. This includes ordinary formulas and circuits of sufficient constant size, and read-once oblivious algebraic branching programs of a suitable fixed width in any variable order. The conclusion holds for every unsatisfiable 3CNF.

Choose a clause and let $V_1,\ldots,V_r$, $r\le 3$, be indeterminates for the Boolean-axiom coordinates of its distinct variables. Let $Y$ represent its falsity coordinate. Work in the finite free algebra

$$
R=F[V_1,\ldots,V_r][Z_1,\ldots,Z_r]/
(Z_i^2-Z_i-V_i\mid 1\le i\le r).
$$

It has the squarefree monomials in $Z_i$ as a basis of rank $2^r$, by successive division by each monic relation. Let $P(Z)$ be the clause-falsity product, with an occurrence of each literal replaced by either $Z_i$ or $1-Z_i$ according to its sign. Let $M_P$ be its multiplication matrix in this basis. The characteristic polynomial $D(Y,V)=\det(YI-M_P)$ is monic in $Y$, hence nonzero over every field. Cayley–Hamilton for matrices over the commutative coefficient ring gives $D(M_P,V)=0$. Applying this matrix identity to the vector of $1$ gives $D(P(Z),V)=0$ in $R$. Substituting each original variable for $Z_i$, and its Boolean-axiom value for $V_i$, proves the asserted vanishing on the full output image.

For the degree bound, use a field of rational functions in $r$ independent variables $z_i$ and set $V_i=z_i^2-z_i$. These $V_i$ are algebraically independent because substitution sends each monomial in $V$ to a monomial in $z$ of doubled highest degree, with distinct exponent vectors at the top degree. Over this rational function field in $z$, the defining quadratics of $R$ split into the distinct roots $z_i,1-z_i$. Thus $D$ becomes the product of $2^r$ linear factors in $Y$, whose other terms are the values of $P$ at the possible choices of roots. Each such value has total $z$-degree at most three, even for a repeated literal. The coefficient of $Y^{2^r-j}$ has $z$-degree at most $3j$, so its $V$-degree is at most $\lfloor 3j/2\rfloor$ by the same substitution degree comparison. The total degree is at most

$$
\max_{0\le j\le 2^r}\bigl(2^r-j+\lfloor 3j/2\rfloor\bigr)\le 12.
$$

An empty clause has the constant falsity value $1$ and admits the relation $Y-1$. A nonzero polynomial in at most four variables of bounded degree has a constant-size sum-of-monomials formula. The same monomials can be kept on separate paths in any variable order for the branching-program claim.

For a clause with $r>0$ distinct, noncomplementary literals, the degree in $Y$ of this particular relation is optimal among relations using just those $r+1$ output coordinates. The rational function extension $F(z)/F(V)$ has degree at most $2^r$ by the defining quadratics and has $2^r$ distinct automorphisms obtained by independently replacing $z_i$ by $1-z_i$. The images of the product under these automorphisms are pairwise different by unique factorization in $F[z_1,\ldots,z_r]$. Thus the product has minimal polynomial of degree $2^r$ over $F(V)$.

This answers the negative hitting-set alternative for the full map and the specified classes. Geometric IPS additionally requires that a vanishing polynomial take value $1$ at the zero output. In the construction with distinct literals and $r>0$, setting the Boolean-axiom coordinates to zero gives $D(Y,0)=Y^{2^r-1}(Y-1)$, so this relation takes value zero there. The result gives neither a Geometric IPS size bound nor a conclusion for the altered map that retains only clause coordinates. The construction is an informal application of finite free multiplication coordinates. The targeted literature search located no prior explicit use of this clause relation to answer Question 3, and publication priority remains unestablished. [Original question and Geometric IPS definition](https://arxiv.org/html/1701.01717#S4.SS2)

## Published result on Open Question 2

Grochow, Kumar, Saks, and Saraf ask for the complexity of the easiest nonzero metapolynomials inside a sequence of test $G_n$-modules, with highest-weight vectors for test $\mathrm{GL}_n$-modules as a specific comparison. A test module here is an irreducible subrepresentation of the relevant metapolynomial space. [Original Open Question 2](https://arxiv.org/html/1701.01717#S4.SS1)

Van den Berg, Dutta, Gesmundo, Ikenmeyer, and Lysikov explicitly address this question in Corollary 1.2 of *Algebraic metacomplexity and representation theory*. For an irreducible $\mathrm{GL}_k(\mathbb C)$-representation of degree-$\delta$ metapolynomials on the coefficient vectors of degree-$d$ homogeneous $k$-variate forms, let $s$ be the least size of a circuit for a nonzero member. Every member has circuit size at most

$$
O\!\left(s\,k^{2k^2}(\delta d)^{2k^4+k^2}\right).
$$

The bound follows by translating a minimum-size element by a generic group element, applying their projectors onto the one-dimensional Gelfand–Tsetlin components, and assembling a basis of the irreducible module from the resulting nonzero projections. A generic group element works because the orbit of the starting nonzero element spans the irreducible module. This is a quasipolynomial comparison in the authors' application regime, where $k$ is logarithmic and the degrees are polynomially bounded. It gives a polynomial-factor comparison for fixed $k$. The result belongs to those authors. It establishes comparison with the minimum, and leaves the exact minimum, arbitrary acting groups, and polynomial overhead throughout the logarithmic regime as different questions. [Corollary 1.2 and Theorem 1.1](https://arxiv.org/html/2411.03444#S1)

## Recent adjacent literature

Robert Andrews proves unconditional lower bounds for Geometric IPS certificates computed by constant-depth polynomial-size circuits, on an explicit family whose equations each depend on at most three variables. He also gives conditional bounds for formulas and branching programs. The hard systems in that paper are outside the standard 3CNF encoding above. [Andrews, CCC 2025, Theorem 1.4](https://drops.dagstuhl.de/storage/00lipics/lipics-vol339-ccc2025/html/LIPIcs.CCC.2025.15/LIPIcs.CCC.2025.15.html)

Andrews also asks in the full version whether the presence of a small annihilator and the existence of a Geometric IPS certificate together imply a small Geometric IPS certificate. For constant-depth polynomial-size circuits the implication fails even when all coordinates are affinely independent. Take his generator $G$ whose outputs are constant-size formulas and whose image hits constant-depth polynomial-size circuits. Start from the associated hard system, which admits a Geometric IPS refutation, and append the outputs $z,z^2$ for one new independent input $z$. For the resulting map $H=(G,z,z^2)$, the polynomial $Y_2-Y_1^2$ in the two new output variables is a constant-size annihilator. Any Geometric IPS refutation of $G=0$ remains a refutation of $H=0$ by ignoring the two new variables. Conversely, any purported small refutation of $H=0$, specialized at $Y_1=Y_2=0$, gives one of $G=0$. It still equals one at the origin and vanishes on $G$, by setting the new input $z=0$. This substitution preserves constant depth and polynomial size, contradicting the hardness for $G$. There is no nonzero affine relation on the output coordinates of $H$. In such a relation the coefficients of $z,z^2$ must first vanish, and any remaining affine relation would contradict the hitting property of $G$. This construction allows extra output coordinates. The lower bound applies to constant-depth certificates. The complexity of unrestricted circuit certificates remains open here. [Andrews, full version, §5.1](https://eccc.weizmann.ac.il/report/2025/063/download/)

Bhattacharjee, Kumar, Rai, Ramanathan, Saptharishi, and Saraf give a deterministic polynomial-time oracle reduction over $\mathbb Q$ from factoring explicitly provided constant-depth arithmetic circuits to white-box or black-box PIT for suitable constant-depth circuits. The running time is polynomial in the size and degree of the input circuit. The root recombination criterion uses logarithmic derivatives. This is a positive result for the bounded-degree PIT-to-factoring direction. The degree-unrestricted exact black-box factor conjecture concerns a different input and dependence on degree. [ECCC TR26-310, November 6, 2026](https://eccc.weizmann.ac.il/report/2026/310/)

The recent Hexagon paper on counting engines diagnoses barriers tied to specific counting and contraction models. It does not give a proof of the metapolynomial or Geometric IPS hitting-set assertions above. [Hexagon preprint 2611.00149v1](https://hexagonmath.org/2611.00149v1)
