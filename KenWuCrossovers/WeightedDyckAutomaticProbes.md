# Exact finite-precision tests for every index of a weighted Dyck sequence

Let \(p\) be prime and let \(a,b\colon\mathbb N\to\mathbb Z_p\) be height weight sequences. Assume that for every \(r\ge1\) one can compute an eventual period and preperiod, with its values, for each sequence modulo \(p^r\). Write \(L_n(a)\) for the weighted sum over Dyck paths of semilength \(n\), multiplying \(a(h)\) for every up-step from height \(h\). Put \(D_n=L_n(a)-L_n(b)\) and write \(s_p(n)\) for the base-\(p\) digit sum.

**Theorem.** Given \(r\), one can compute an automaton giving \(D_n\bmod p^r\) on every input \(n\). Given also a starting index \(N\), a nonnegative integer \(c\), and a residue \(\alpha\bmod p^r\), one can decide the universal statement

\[
\min(r,v_p(D_n))=\min(r,s_p(n)+c+v_p(n-\alpha))\qquad \forall n\ge N.
\tag{1}
\]

If the statement fails, the algorithm returns a failing index. For the higher precision-compatible valuation equation, suppose there is a known index \(n_0\ge N\) with \(D_{n_0}\ne0\). Its exact solutions \((\alpha,c)\in\mathbb Z_p\times\mathbb N\) are the inverse limit of the finite lists of solutions to (1), where \(0\le c\le v_p(D_{n_0})-s_p(n_0)\). In particular absence of an exact solution has a terminating finite-precision certificate. If an exact solution exists, it is unique.

For the Morse-link weights \(a_k(h)=(2h+1)^{2k}\), \(b(h)=1\), and nonzero \(k\in\mathbb Z_2\), the input to the test depends only on \(k\bmod 2^{\max(r-3,0)}\) at precision \(r\). On every annulus \(v_2(k)=v\) and for every fixed \(N\ge2\) for which a uniform bound on \(c\) is known, the set of exponents admitting a solution is an effective intersection of computable clopen conditions. For \(N=2\), the bound is \(c\le v+2\). This combines the uniform finite-probe viewpoint from the relative affine arithmetic program with the finite-automaton and Dyck path methods in the lab. [Ken Wu Lab on Pell automata](https://kenwu-lab.wooqianghao.workers.dev/papers/pell-automatic-repetition-threshold/) · [Ken Wu Lab on the Morse-link conjecture](https://kenwu-lab.wooqianghao.workers.dev/papers/morse-link-2adic-conjecture/) · [MathProofs on uniform bounded-depth probes](https://github.com/Dugongue/MathProofs/blob/main/AffineSchemeCrossovers/ProbeIndistinguishability.md).

## A rational diagonal with an integral denominator

At a given precision, choose an integer lift of the stated eventually periodic table, including its preperiod. Coefficientwise reduction modulo \(p^r\) of the resulting weighted Dyck series agrees with that of the actual weights. For an absolute height \(h\), let \(F_h(x)\) count excursions beginning and ending at that height and staying weakly above it. First return gives

\[
F_h=\frac1{1-x a(h) F_{h+1}}.
\]

Suppose the period begins at \(H\) and has length \(d\). The integer-lift series satisfy \(F_H=F_{H+d}\). Composition over the period is represented by the product of matrices

\[
\begin{pmatrix}0&1\\-x a(h)&1\end{pmatrix},\quad H\le h<H+d.
\]

At \(x=0\) the product is \(\left(\begin{smallmatrix}0&1\\0&1\end{smallmatrix}\right)\). Thus the fixed-point equation for \(F_H=1+y\) is a polynomial \(P(x,y)=0\) with \(P(0,y)=y\). It has a unique formal root \(y=f(x)\in x\mathbb Z[[x]]\), by coefficient recursion. Its rational diagonal representation is the diagonal of

\[
\frac{Y^2 P_y(XY,Y)}{P(XY,Y)}.
\tag{2}
\]

To verify this formula, write \(P(x,y)=(y-f(x))U(x,y)\) in the integer formal power series ring, with \(U(0,0)=1\). Extracting equal powers of \(X,Y\) is equivalent to taking the constant term in \(y\) after substituting \(X=x/y,Y=y\). The summand \(y^2/(y-f(x))\), expanded as \(\sum_{j\ge0}y^{1-j}f(x)^j\), has constant term \(f(x)\). The remaining summand \(y^2 U_y/U\) has zero constant term. In (2), the factor \(Y\) cancels and the denominator has constant coefficient one. This calculation is the usual simple-root diagonal formula. [Rowland and Yassawi](https://arxiv.org/abs/1310.8635).

For the finite preperiod write the periodic tail as \(F_H=1+z\). Composing the remaining first-return maps makes \(F_0\) a rational function \(R(x,z)\) with integer numerator and denominator and denominator value one at \((0,0)\). The diagonal formula above extends to this substitution. The diagonal of

\[
R(XY,Y)\frac{Y P_y(XY,Y)}{P(XY,Y)}
\tag{3}
\]

is \(R(x,f(x))\). In fact the constant term of \(R(x,y)y/(y-f(x))\) is \(R(x,f(x))\); the other summand contains a positive power of \(y\). The denominator in (3) again has constant coefficient one after cancellation. This proves the required rational representation even for a nonempty preperiod.

## Effective digit sections over a prime-power ring

For completeness take a bivariate rational series \(A/Q\) with \(Q(0,0)=1\) and work modulo \(p^r\). Put \(e=p^{r-1}\) and represent the series with denominator \(Q^e\). The binomial theorem gives

\[
Q(X,Y)^{pe}\equiv Q(X^p,Y^p)^e\pmod {p^r}.
\]

Indeed the two bases \(Q(X,Y)^p\) and \(Q(X^p,Y^p)\) agree modulo \(p\), and raising congruent quantities to a \(p\)-th power increases that precision by at least one. For digit \(d\), the section \(\Lambda_d\) keeps coefficients with both indices congruent to \(d\bmod p\) and divides their shifted indices by \(p\). From a numerator \(U\) the new numerator is \(\Lambda_d(UQ^{(p-1)e})\), with the same denominator \(Q^e\). Each variable degree is bounded along every transition by the maximum of its initial numerator degree and \(e\) times its degree in \(Q\). There are finitely many numerators with those bounds over \(\mathbb Z/p^r\). Each output is the constant coefficient of the numerator. Reading \(n\) from its least significant digit selects the coefficient indexed by \((n,n)\). Carry this out for both weight tables and subtract their outputs. It yields the desired automaton. This argument specializes the rational diagonal method to the denominator with unit constant coefficient used here.

The truncated valuation of \(D_n\) is a lookup on the output residue. On the right of (1), the digit sum can be accumulated with saturation at \(r\); the valuation of \(n-\alpha\) truncated at \(r\) is the first disagreeing digit among the first \(r\) digits. A fixed residue automaton or zero padding deals with inputs having fewer than \(r\) digits. The range \(n\ge N\) also has a finite automaton. The product accepts exactly the failing indices. Reachability from the initial state decides emptiness, and a path to an accepting state supplies an explicit counterexample.

## Passing to full precision

A solution at precision \(r+1\) projects to one at precision \(r\). All candidate \(c\)'s can be restricted to the displayed finite range using \(n_0\) since the actual valuation at that index is finite. If the range is empty, there is no solution. Otherwise the solution lists form a finitely branching tree. If each level is nonempty there is an infinite branch and hence a compatible \(\alpha\in\mathbb Z_p\) with a fixed \(c\). Equality at all truncations is exactly equality of the extended valuations. This proves both directions of the inverse-limit statement.

For an exact solution, the minimum of \(v_p(D_n)-s_p(n)\) at any two consecutive indices in the range equals \(c\), since at least one has the opposite residue from \(\alpha\) modulo \(p\). Knowing \(c\), the indices for which the normalized valuation is at least \(c+j\) are exactly one residue class modulo \(p^j\). This determines every digit of \(\alpha\) uniquely.

For the Morse weights, height classes modulo \(2^r\) suffice at precision \(r\), since the odd squares reduce compatibly and their 2-adic powers are given by binomial series. Every odd square lies in \(1+8\mathbb Z_2\), whose image has exponent dividing \(2^{\max(r-3,0)}\) modulo \(2^r\). On a fixed annulus and under a uniform bound on \(c\), project the finite lists at precision \(r\) to the finitely many residue classes of \(k\). The resulting clopen tests are nested, and compactness as above describes the accepted set by their intersection. For \(N=2\), \(D_2(k)=9^k-1\) has valuation \(v+3\). For positive integers this follows by odd powers and successive squaring of \(9\); for 2-adic \(k\) the same result follows by continuity on its annulus. Since \(s_2(2)=1\), it gives the claimed bound.

The automaton decides every prescribed precision for all indices, including the range starting at four. The theorem gives a semidecision for failure of the full conjectural identity when the finite bound is available.
