# Exponential Geometric IPS degree and sparse Frobenius elimination

These are informal proofs. The main example gives an exact exponential degree separation between ordinary and Geometric IPS over a fixed finite field, on a system including the usual Boolean equations when the field is $\mathbb F_2$. A second example works over every field with only quadratics and linears. The positive result gives small Geometric IPS circuits for low-degree or sparsely supported dependence on the original variables. A final example addresses the flat, zero-dimensional-fiber extension proposed by Grochow and Pitassi.

We write $X$ for original variables and $Y$ for the variables replacing the axiom polynomials $f(X)$. An ordinary IPS refutation is a polynomial $H(X,Y)$ with $H(X,0)=0$ and $H(X,f(X))=1$. A Geometric IPS refutation is a polynomial $G(Y)$ with $G(0)=1$ and $G(f(X))=0$. These are formal polynomial identities. [Grochow–Pitassi, Definition C.1 and Open Question C.2](https://arxiv.org/pdf/1404.3820)

## An exact exponential degree separation on Boolean systems

**Theorem.** Let $F$ be any field containing $\mathbb F_q$ and let $n\ge 1$. Use the axiom polynomials
$$
u_i(X)=X_i^q-X_i\quad(1\le i\le n),\qquad
v(X)=1+\sum_{i=1}^n X_i u_i(X).
$$
There is a degree-two ordinary IPS refutation of formula size $O(n)$. Ordinary Polynomial Calculus has a degree-$(q+1)$ refutation with $O(n)$ lines and polynomial sparse size. Every Geometric IPS refutation has total degree at least $q^n+q^{n-1}$, and this exact degree is attained by a polynomial with a division-free circuit of size polynomial in $n,\log q$. In particular, when $q=2$, this gives the standard quadratic Boolean axioms and one cubic over the fixed field $\mathbb F_2$, with minimum Geometric IPS degree $3\cdot 2^{n-1}$.

For the ordinary proof take $H=Z-\sum_i X_iY_i$, where $Y_i,Z$ correspond to $u_i,v$. Its substitution value is identically one. For PC multiply each $u_i$ by $X_i$ and subtract the resulting lines from $v$. The maximum degree is $q+1$, and the intermediate sums have at most $2n+1$ terms.

Put $K=F(U_1,\ldots,U_n)$, with $U_i$ independent placeholders for $u_i$. Substituting $U_i=X_i^q-X_i$ gives an inclusion $F[U]\hookrightarrow F[X]$. In fact $F[X]$ is free of rank $e=q^n$ over $F[U]$, with basis the monomials $X^\alpha$ for $0\le \alpha_i<q$. The relations $X_i^q=X_i+U_i$ give spanning. For independence, the leading multidegrees of $X^\alpha\prod_i(X_i^q-X_i)^{b_i}$ under lexicographic order are $\alpha+qb$, distinct for distinct $(\alpha,b)$. Localizing at all nonzero polynomials in $U$ gives a finite-dimensional domain over $K$, hence a field, namely $F(X)$. The substitutions $X_i\mapsto X_i+a_i$ for $a=(a_i)\in\mathbb F_q^n$ define $e$ distinct automorphisms fixing $K$. Under them $v$ has $e$ distinct conjugates $v+\sum_i a_iU_i$, by the algebraic independence of the $U_i$. Its minimal polynomial over $K$ therefore has degree exactly $e$.

Define the additive polynomial
$$
L(T)=\prod_{a\in\mathbb F_q^n}\left(T-\sum_i a_iU_i\right)=\sum_{j=0}^n c_j(U)T^{q^j}.
$$
For the second equality, start with $L_0(T)=T$ and adjoin one coefficient at a time by
$$
L_{i+1}(T)=L_i(T)^q-L_i(U_{i+1})^{q-1}L_i(T).
$$
An additive polynomial supported on $q$-powers is $\mathbb F_q$-linear. Thus the displayed recurrence follows from taking the product of $L_i(T)-\beta L_i(U_{i+1})$ over $\beta\in\mathbb F_q$. Write $c_j$ for the final coefficients. Each $c_j$ is homogeneous of degree $e-q^j$ when nonzero, since the defining product is homogeneous of degree $e$ in $U,T$, and $c_n=1$.

Substituting the $u_i(X)$, the identities $X_i^{q^j}=X_i+\sum_{k<j}U_i^{q^k}$ follow by telescoping. As $L(U_i)=0$, this yields
$$
R(U,Z)=L(Z-1)-W(U),\qquad
W(U)=\sum_{j=0}^{n} c_j(U)\sum_i U_i^{q^j}\sum_{k<j}U_i^{q^k},
\qquad R(u(X),v(X))=0.
$$
This $R$ is monic of $Z$-degree $e$. Division by $R$ in $F[U][Z]$ shows that every polynomial relation among $u,v$ is a multiple of $R$, since any nonzero remainder of smaller $Z$-degree would contradict minimality over $K$.

The terms of $L(Z-1)$ have degree at most $e$. The unique summand of $W$ of degree $e+q^{n-1}$ is $\sum_i U_i^{e+q^{n-1}}$, which comes from $j=n,k=n-1$. Its monomials are distinct, also when the characteristic divides $n$. This proves the exact total degree of $R$. At $U=0$ we have $R(0,Z)=(Z-1)^e$, so $R(0,0)=(-1)^e$ is a unit. Consequently $R/R(0,0)$ is a Geometric IPS refutation, and every other refutation is a nonzero multiple of $R$ and has total degree at least $\deg R$. The recurrence gives explicit circuits for the $c_j$ and then for $W$, using repeated squaring for powers with binary length $O(n\log q+1)$. It shares the coefficient circuits through the recurrence, so its cost is polynomial in $n,\log q$.

### Consequences for bounded-depth circuits, formulas and branching programs

In the usual model with variables and constants as input leaves, an arithmetic formula has degree at most its number of variable leaves. In an arithmetic branching program with affine-linear edge labels, degree is at most the longest path length. The degree theorem forces size at least $q^n+q^{n-1}$ in either model. For unbounded fan-in arithmetic circuits of wire size $s$ and depth $D$, induction gives a degree bound $s^D$. Therefore every depth-$D$ Geometric IPS refutation on these instances has size at least $q^{n/D}$, while the ordinary IPS refutation has constant depth and $O(n)$ wires. The finite-field example is a Boolean polynomial system in the sense of including Boolean axioms. The extra polynomial is a sum of cubic terms and is given as one axiom. The result does not use a system consisting only of Boolean axioms and the standard clause polynomials of a 3CNF. The exponential degree lower bound is compatible with polynomial-size unrestricted circuits.

The additive polynomial recurrence is the one used in the earlier one-linear-form Geometric IPS construction. Here the Artin–Schreier translation orbit proves that its output has provably minimum degree. A federated DAG search connected this calculation with the Artin–Schreier algebra constructions in the imported Mazur formalization and with linearized polynomials in the imported Complexity library. The formal algebraic proofs above are independent of any kernel claim. [A standard Artin–Schreier reference](https://stacks.math.columbia.edu/tag/09I7)

## The same degree separation over every field with only quadratic and linear axioms

**Theorem.** Over any field, the system
$$
f_0=1-X_1,\qquad
f_i=X_i^2-X_{i+1}\quad(1\le i<n),\qquad
f_n=X_n^2
$$
has a degree-two polynomial-size PC refutation and an ordinary IPS refutation of circuit size $O(n)$. Its minimum Geometric IPS degree is exactly $2^n$, with a size-$O(n)$ unrestricted Geometric IPS circuit.

In PC, use the line $1-X_1=f_0$. From a line $1-X_i$, derive $(1+X_i)(1-X_i)$ by one variable multiplication and addition. Adding $f_i$ gives $1-X_{i+1}$ if $i<n$ and gives 1 when $i=n$. Every line has degree at most two. For an explicit ordinary IPS circuit perform the same recurrence with the placeholders for $f_i$ and the multipliers $1+X_i$.

The first $n$ coordinates $Y_0,\ldots,Y_{n-1}$ give a polynomial automorphism from the $X$-space to affine $n$-space. Its inverse is $A_1=1-Y_0$ and $A_{i+1}=A_i^2-Y_i$. The full image is the graph of $A_n^2$ in the last coordinate $Y_n$. Hence the kernel of substitution is generated by the monic relation $Y_n-A_n^2$. Its total degree is $2^n$ because the highest-degree term of $A_n^2$ is $Y_0^{2^n}$. Its value at the origin is $-1$, so rescaling proves exactness. This gives all-field formula and branching-program lower bounds of at least $2^n$ and the corresponding fixed-depth lower bound as above. These examples place no polynomial degree bound on the resulting Geometric IPS certificate. Compare [Andrews’s Geometric IPS lower-bound arguments via algebraic pseudorandomness](https://drops.dagstuhl.de/storage/00lipics/lipics-vol339-ccc2025/html/LIPIcs.CCC.2025.15/LIPIcs.CCC.2025.15.html).

## Simulation by Frobenius triangularization

**Theorem.** Let $F\supseteq\mathbb F_q$, assume that all $X_i^q-X_i$ occur among the axiom polynomials $f$, and let $U_i$ denote their placeholders. Suppose the supplied ordinary IPS certificate $H(X,Y)$ is written as $\sum_{\alpha\in S} a_\alpha(Y)X^\alpha$ by circuits for its coefficients. Write $p=\operatorname{char}(F)$. Assume $S$ contains 0 and is downward closed in the coordinatewise base-$p$ digit order, in which each digit of a smaller exponent is at most the matching digit of the larger one. There is a Geometric IPS refutation with a division-free circuit of size polynomial in $n,\lvert S\rvert,\log q$, the bit lengths of the explicit exponents, and the total size of the coefficient circuits. In particular, for each fixed constant $D$, Geometric IPS simulates arbitrary ordinary IPS certificates of $X$-degree at most $D$ in polynomial circuit size, with arbitrary dependence on $Y$. The degree bound in this last assertion is on the final $H$. The construction assumes this degree bound and does not test it.

Work with representative polynomials in $X,Y$ and apply the semilinear operator
$$
\mathcal F\left(\sum_\alpha b_\alpha(Y)X^\alpha\right)
  =\sum_\alpha b_\alpha(Y)^q(X+U)^\alpha.
$$
The output uses only monomials in $S$, since in characteristic $p$ a nonzero term in $(X+U)^\alpha$ has exponent digitwise at most $\alpha$. This follows by factoring each binomial power with $(X_i+U_i)^{p^j}=X_i^{p^j}+U_i^{p^j}$ and expanding the smaller powers. After $Y=f(X)$, $\mathcal F$ evaluates to the $q$-th power of the original polynomial, since $X_i^q=X_i+u_i(X)$ and the coefficient field has characteristic dividing $q$. The substitution operator is triangular in any order extending coordinatewise comparison. Its effect on the coefficient of the highest remaining monomial $X^\alpha$ is therefore raising that coefficient to the $q$-th power.

Start with $P=H$ and $s=1$. Process the nonconstant monomials in descending order. If $b(Y)$ is the current coefficient of the selected monomial, update both objects by
$$
P\gets\mathcal F(P)-b^{q-1}P,\qquad s\gets s^q-b^{q-1}s.
$$
The monomial is killed by triangularity, even if $b=0$, and all earlier killed monomials stay zero. At every step $P(X,f(X))=s(f(X))$, starting from the IPS identity. All coefficients of $P$ vanish at $Y=0$ initially and continue to do so. It follows also that $s(0)=1$ throughout. At the end $P=b_0(Y)$ is constant in $X$, so $s-b_0$ is the required certificate.

For the uniform size bound, expand $(X+U)^\alpha$ only on the displayed support, with coefficients $\prod_i\binom{\alpha_i}{\beta_i}U_i^{\alpha_i-\beta_i}$. Compute the binomial coefficients in the prime subfield by Lucas digits. If a base-$p$ exponent digit is $a$, closure puts at least $a+1$ exponents in $S$ by retaining only that digit and lowering it. Hence every digit binomial computation is bounded polynomially in $\lvert S\rvert$, even when $q$ varies. Repeated squaring handles powers with large exponents, and arithmetic DAG sharing avoids expanding any coefficient as a polynomial in $Y$. For the fixed-degree case, take $S=\{\alpha:\sum_i\alpha_i\le D\}$. From a circuit for $H$, carry a truncated coefficient array at each gate and convolve at products, dropping $X$-degree above $D$. The quotient by monomials of degree greater than $D$ makes this exact for the retained degrees, even if intermediate circuit gates have higher degree. Since $\lvert S\rvert=\binom{n+D}{D}$, the circuit blowup is polynomial for fixed $D$.

This positive theorem covers arbitrary quadratic or cubic dependence on all original variables, with arbitrary coefficient polynomials in the placeholders. The input is the bounded-degree or explicit-support certificate. The general simulation problem in Open Question C.2 remains open.

## Flatness and finite fibers do not ensure Geometric IPS completeness

Grochow and Pitassi propose that a flat axiom map with zero-dimensional fibers may furnish a sufficient condition for Geometric IPS completeness beyond their coordinatewise univariate hypothesis. The following gives a negative answer to this proposed condition, whether the target in the footnote is taken to mean the reduced image closure or the actual image with its induced open-variety structure. [Grochow–Pitassi, Proposition C.3, footnote 7](https://arxiv.org/pdf/1404.3820#page=50)

Let $F$ be algebraically closed and set
$$
a=xy-1,\qquad b=x+ay.
$$
The map $(x,y)\mapsto(a,b)$ has image $\mathbb A^2\setminus\{(0,0)\}$. At $a=0$ we have $xy=1$ and $b=x$, so the fiber is one point for $b\ne0$ and empty for $b=0$. At $a\ne0$, solve $x=b-ay$ and obtain $ay^2-by+(a+1)=0$. It has at least one and at most two distinct roots. Consequently the map is quasi-finite and has dense image.

For flatness, work over the target ring $F[A,B]$. On the source chart $D(a)$, the coordinate ring is
$$
F[A,A^{-1},B,Y]/\bigl(Y^2-(B/A)Y+(A+1)/A\bigr),
\qquad X=B-AY.
$$
This is finite free of rank two over $F[A,A^{-1},B]$ and hence flat over $F[A,B]$. The source chart $D(x)$ has coordinate ring
$$
\left(F[A,B,X]/(X^2-BX+A(A+1))\right)[X^{-1}],
\qquad Y=(A+1)/X.
$$
Before localizing at $X$ the algebra is again free of rank two over the target ring, and localization preserves flatness. The charts cover the source since $xy-a=1$. This proves flatness to the whole target and hence to the actual open image.

The axioms $a=b=0$ have the constant-size ordinary IPS refutation $yY_2-(y^2+1)Y_1$, because $yb-(y^2+1)a=1$. No Geometric IPS refutation exists, since every polynomial vanishing on the dense image vanishes identically. The example differs from the paper's earlier Example C.4 in that every nonempty geometric fiber is zero-dimensional and the map is flat. The finite-map variant of the proposed sufficient condition does hold: a finite axiom map to the image closure has closed image, so absence of a preimage of the origin gives a polynomial vanishing on the image and nonzero at the origin, which can be normalized. [Stacks Project on finite morphisms](https://stacks.math.columbia.edu/tag/01WG) · [Stacks Project on flatness](https://stacks.math.columbia.edu/tag/01U2)

The targeted literature search located the original completeness question, previous Geometric IPS lower bounds using hitting-set constructions, and standard algebraic references. Publication priority for these exact examples and for the triangular simulation remains unestablished.

For the finite controls, an exact sparse-polynomial replay checked the orbit-polynomial recurrence against the expanded product, the full substitution identity and the claimed total degree in eight instances over $\mathbb F_2,\mathbb F_3,\mathbb F_5$, for $n$ up to four. A separate enumeration checked the flat counterexample's polynomial certificate and the bound of two points per fiber over five prime fields. The flatness and minimality proofs use the symbolic arguments above.
