# Finite-prime certificates for bounded-degree arithmetic circuits

**Status.** Written proof. The transfer from modular circuits to complex circuits is unconditional. The converse uses the prime-counting consequence of Dedekind GRH. The specialization of supplied abelian realizations uses Dirichlet GRH alone. These results concern circuit realizations and give a sufficient modular criterion for characteristic-zero lower bounds.

## Theorem

Let \(f\in\mathbb Z[x_1,\ldots,x_m]\) have total degree at most \(d\), where \(m,d,s\ge1\). Put \(\tau=\log(1+\max_\alpha |[x^\alpha]f|)\), using \(\tau=0\) for \(f=0\). Count input gates in the size of fan-in-two, division-free \(+,-,\times\) circuits. For a field \(K\), a size-\(s\) truncated realization of \(f\) is a circuit over \(K\) with at most \(s\) gates whose output agrees with \(f\) through total degree \(d\). Over \(\mathbb F_p\) interpret \(f\) coefficientwise modulo \(p\).

There are absolute constants \(C,c>0\) such that, with
\[
 B=(4(m+s+d+1))^{C(s+1)}(2+\tau),
\]
the following hold.

1. If distinct primes admitting size-\(s\) truncated realizations have product greater than \(\exp B\), then \(f\) has a size-\(s\) truncated realization over \(\mathbb C\). It follows that \(f\) has an ordinary complex circuit of size \(O(s(d+1)^2)\).
2. Under Dedekind GRH, if \(f\) has a size-\(s\) truncated realization over \(\mathbb C\), then for each \(X\ge B^4\) there are at least \(cX/(B\log X)\) primes at most \(X\) admitting one. One fixed circuit topology suffices at all those primes. Consequently the certificate in part 1 is necessary and sufficient when restricted to primes up to \(B^4\), under Dedekind GRH.
3. Parts 1 and 2 also hold with both sides restricted to topologies of syntactic \(x\)-degree at most \(d\). A scalar input has syntactic \(x\)-degree zero, a variable has degree one, addition and subtraction take the maximum, and multiplication adds degrees. With this restriction both sides compute the entire formal polynomial and the transfer preserves the original size \(s\).

In particular, a size-\(s\) complex circuit of output degree \(d\) gives ordinary prime-field circuits of size \(O(s(d+1)^2)\) at primes of bit length \(O(s\log(2(m+s+d))+\log(2+\tau))\). Conversely, ordinary size-\(s\) circuits at primes whose log-product exceeds \(B\) give an ordinary complex circuit of size \(O(s(d+1)^2)\).

## Proof

Fix a topology, consisting of an ordered list of gates and their types, variable indices, and predecessor indices, with the output last. At each gate \(g\) introduce a scalar parameter \(c_g\) for its evaluation at \(x=0\). At variable inputs impose \(c_g=0\). At scalar inputs leave \(c_g\) free. For each binary gate \(g=(i,j,\circ)\), add the equation \(c_g=c_i\circ c_j\). These equations have degree at most two and coefficient \(\ell_1\) norm at most three.

Compute the positive \(x\)-degree part \(V_g\) at a gate by the following recurrence in \(\mathbb Z[\mathbf c][\mathbf x]\), discarding \(x\)-degrees exceeding \(d\):
\[
 V_g=
 \begin{cases}
 x_k & \text{at input }x_k,\\
 0 & \text{at a scalar input},\\
 V_i\pm V_j & \text{at an addition or subtraction gate},\\
 V_iV_j+c_iV_j+c_jV_i & \text{at a multiplication gate}.
 \end{cases}
\]
Both the omitted constant term and the discarded higher-degree terms are handled by exact operations. In the quotient \(K[\mathbf x]/(x_1,\dots,x_m)^{d+1}\), the output of gate \(g\) is \(c_g+V_g\) for every solution to the scalar equations. This follows by induction, since the constant term of a product at \(g\) is \(c_ic_j\). Conversely every evaluation of the scalar inputs gives a solution of the scalar equations by evaluating the gates at zero. Impose coefficient equality of \(c_o+V_o\) with \(f\) at the output \(o\) through degree \(d\). Thus the resulting polynomial system \(S\) is soluble over \(K\) exactly when the topology admits the specified truncated realization over \(K\).

Let \(h_g\) be the depth of a gate, with zero for inputs. For its homogeneous \(x\)-degree \(j\) part, \(1\le j\le d\), every scalar monomial has \(\mathbf c\)-degree at most \(h_gj\), and the sum of absolute coefficients in both sets of variables is at most \(2^{h_gj}\). At an input the bounds hold directly. For \(+\) or \(-\), adding the child norms costs a factor at most two. At a multiplication gate, the \(j-1\) products of positive-degree parts and the two terms with a scalar each have norm at most \(2^{(h_g-1)j}\) per term, by multiplicativity of the upper bound for coefficient \(\ell_1\) norms. The factor \(j+1\) is at most \(2^j\). The product terms have scalar degree at most \((h_g-1)j\). Each scalar-times-part term has scalar degree at most \(1+(h_g-1)j\le h_gj\). The recurrence uses no division, including in positive characteristic.

For this topology there are at most \(s\) unknowns. Its system has degree bound \(D=\max(2,sd)\), coefficient \(\ell_1\) norm at most \(W=4+2^{sd}+\exp(\tau)\) in each equation, and at most \(s+\binom{m+d}{d}\) equations. The size of the integer coefficients is relevant only logarithmically in the analytic estimate, and these bounds are independent of the sizes of the constants in a complex realizing circuit.

To compile a truncated realization into an ordinary circuit, compute the \(d\) positive homogeneous pieces gate by gate and then add the output constant \(c_o\). Sums of pieces use \(O(d)\) gates per gate and the convolution for a product uses \(O((d+1)^2)\). The \(c_g\) can be inserted as scalar constants. This gives \(O(s(d+1)^2)\) gates in any field. If the original topology has syntactic \(x\)-degree at most \(d\), use the original circuit with the scalar inputs specified by the solution, since the polynomial degree of its output is at most \(d\) for every scalar assignment.

### Modular realizations imply a complex realization

If \(S\) has no complex zero, the arithmetic Nullstellensatz gives a nonzero integer \(A_S\) in the ideal of its equations over \(\mathbb Z[\mathbf c]\). Its logarithmic height is at most \(D^{O(s+1)}(\log W+\log(2+s+\binom{m+d}{d})+O((s+1)D\log(s+2)))\). For example, apply the D’Andrea–Krick–Sombra estimate quoted in Proposition 6 of Rojas–Zhu. Any prime admitting the topology over \(\mathbb F_p\) divides \(A_S\), by reduction of the polynomial certificate and substitution at the modular witness. [D’Andrea–Krick–Sombra](https://www.numdam.org/item/ASENS_2013_4_46_4_549_0/) · [Rojas–Zhu, Proposition 6](https://arxiv.org/abs/1803.04104v1)

There are at most \((4(m+s+1))^{O(s+1)}\) topologies, by encoding each gate using one of \(m\) input indices, the scalar marker, or an operation and two predecessor indices. If every topology fails over \(\mathbb C\), then the log absolute value of the product of their obstruction integers is at most \(B\), for \(C\) large enough. Every modular success prime divides that product. Its distinct prime divisors therefore cannot have log-product greater than \(B\). This proves part 1 and also works with only the topologies whose syntactic \(x\)-degree is at most \(d\).

The certificate also works with precision. For a size-\(s\) truncated realization over \(\mathbb Z/p^e\mathbb Z\), the same substitution forces \(p^e\mid A_S\). Thus witnesses at distinct primes with possibly different precisions \(e_p\) suffice whenever \(\sum_p e_p\log p>B\). A single prime suffices at precision \(e>B/\log p\). This direction uses no zero-location hypothesis.

### A complex realization supplies many modular realizations

Fix one topology that works over \(\mathbb C\). The prime-counting form of the effective Nullstellensatz used by Bürgisser gives, under Dedekind GRH,
\[
 \#\{p\le X:S(\mathbb F_p)\ne\varnothing\}
 \ \ge\ \frac{\pi(X)}{D^{O(s)}}-O\!\left(\sqrt X\log(WX)\right).
\]
This estimate applies to the coefficient system itself, regardless of how the bounded-degree polynomial \(f\) was supplied. The variables of \(S\) are the gate offsets only. [Koiran](https://cs.uwaterloo.ca/~r5olivei/courses/2025-spring-cs860/K96-HN-PH.pdf) · [Fournier–Perifel–de Verclos, Lemma 2, citing Bürgisser](https://arxiv.org/html/1304.5910)

Using \(\pi(X)\gg X/\log X\), enlarge the absolute constant \(C\) in \(B\) so that the denominator \(D^{O(s)}\) is at most \(B^{1/4}\) and \(\log W\le B\). The ratio of the error term to the lower bound on the main term is at most an absolute constant times
\[
 B^{1/4}(B+\log X)\frac{\log X}{\sqrt X}.
\]
For \(X\ge B^4\), both terms decrease with \(X\) once \(B\) is sufficiently large. At \(B^4\) the ratio tends to zero as \(B\) increases. Thus the prime count is at least \(cX/(B\log X)\). At \(X=B^4\) their log-product is at least \(cB^3\log(2)/(4\log B)>B\), after another absolute increase in \(C\). This proves the other direction.

## Consequence for the permanent

For \(f=\operatorname{per}_n\), \(m=n^2\), \(d=n\), and \(\tau=\log 2\). Any size-\(s\) complex realization yields size-\(O(sn^2)\) prime-field realizations with \(\log p=O(s\log(2(s+n)))\) under Dedekind GRH. Moreover there are enough such primes to select one with \(p>n!\). Indeed a circuit computing \(\operatorname{per}_n\) uses all \(n^2\) variables, so \(s\ge n^2\), and the prime-count lower bound at \(B^4\) eventually exceeds \(n!\), with the finite small cases absorbed by enlarging \(C\). A permanent of a Boolean matrix is in \([0,n!]\), so taking the least nonnegative residue at this prime computes the exact integer. Standard quadratic-size Boolean arithmetic on \(\log p\)-bit residues gives a nonuniform bound \(O(s^3n^2\log^2(2(s+n)))\) for exact evaluation on Boolean matrices, including all output bits.

In particular, let \(B_n\) be \(B\) evaluated at \(m=n^2\), \(d=n\), \(s=n^k\), and \(\tau=\log 2\), and let \(C_{\rm g}\) be an absolute constant for the gate overhead \(C_{\rm g}s(d+1)^2\). The following is sufficient for \(\mathsf{VP}_{\mathbb C}\ne\mathsf{VNP}_{\mathbb C}\) under Dedekind GRH. For each integer \(k\ge2\), at infinitely many \(n\), fewer than \(cB_n^3/(4\log B_n)\) primes up to \(B_n^4\) admit ordinary size-\(C_{\rm g}n^k(n+1)^2\) circuits for \(\operatorname{per}_n\bmod p\). A polynomial-size complex family would have size at most \(n^k\) for some \(k\) and all sufficiently large \(n\), so part 2 and the gate overhead exclude the stated prime count.

## Abelian realizations under Dirichlet GRH

Suppose an ordinary size-\(s\) realization is supplied over a finite abelian number field \(E\) of degree \(r\) and absolute discriminant \(\Delta\), with all constants in \(\mathcal O_E[1/Q]\) for some positive integer \(Q\). Under Dirichlet GRH, for every \(X\ge C_1\log^2(2\Delta Q)\), at least \(c_1X/(r\log X)\) primes in \((X/2,X)\) give ordinary size-\(s\) realizations of \(f\bmod p\) by reducing the original circuit.

For completeness, choose a fixed nonnegative \(C^2\) weight \(w\) supported on \([1/2,1]\) with positive integral \(I_w\). On primes unramified in \(E\), the indicator of complete splitting is the average of the Dirichlet characters of \(\operatorname{Gal}(E/\mathbb Q)\). The smoothed Dirichlet explicit formula and the conductor–discriminant identity give
\[
 \sum_{\substack{p\nmid \Delta Q\\ p\ \mathrm{splits\ completely\ in}\ E}}
    \log p\,w(p/X)
 = \frac{I_w X}{r}
  + O_w\!\left(\sqrt X\left(1+\frac{\log\Delta}{r}\right)+\log(2\Delta Q)\right).
\]
For a primitive conductor \(q_\chi\), the zero sum is \(O_w(\sqrt X\log(2q_\chi))\), since the Mellin transform of \(w\) decays quadratically on the critical line and the zero count per unit interval is \(O(\log(2q_\chi(2+|t|)))\). Higher prime powers contribute \(O_w(\sqrt X)\). Removing the primes dividing \(\Delta Q\) costs \(O_w(\log(2\Delta Q))\). Averaging over characters replaces their log conductors by \(\log\Delta/r\). Also \(r\le 1+(\log\Delta)/\log 3\) since all nontrivial primitive conductors are at least three. The stated \(X\) makes the error at most half the main term. Each summand is \(O_w(\log X)\). At every counted prime, reduction at any prime of \(E\) above \(p\) evaluates the constants in \(\mathbb F_p\) and preserves the polynomial identity over \(\mathcal O_E[1/Q]\). [Bach–Sorenson, character-weighted prime sums](https://www.ams.org/mcom/1996-65-216/S0025-5718-96-00763-6/S0025-5718-96-00763-6.pdf)

This is the circuit version of the shared project’s conductor-budgeted prime tests for abelian multiplication tensors. The unrestricted theorem needs effective prime counts for a point field of a potentially nonabelian circuit realization. Alpöge's Dirichlet zero-location development marks the analytic input for the abelian part. Both analytic statements here retain their hypothesis. [Alpöge, release note](https://alpo.ge/remark.pdf)

## Univariate hard polynomials of degree \(O(s\log s)\)

Fix an integer \(k\ge1\) and write \(s=n^k\). Under Dedekind GRH there is a univariate family \(P_n\) with coefficients in \(\{0,1\}\), degree \(O(n^k\log(n+2))\), and coefficients decidable in \(\mathsf{PH}\), such that \(P_n\) has no size-\(s\) complex circuit. The lower bound holds even for truncated realizations through the chosen degree cutoff. This sharpens the degree \(s^4\) in Fournier–Perifel–de Verclos, Theorem 5, to within a logarithmic factor of the linear degree bound imposed by Horner evaluation. The family itself has polynomial-size circuits by Horner evaluation, so its lower bound is for the fixed budget \(n^k\).

For a univariate topology, compute the map
\[
 \mathbf c\longmapsto
 ([x^0](c_o+V_o),\ldots,[x^d](c_o+V_o))
\]
without imposing the scalar consistency equations. The image contains every truncated coefficient vector realized by that topology. The coordinate polynomials have total degree at most \(sd\) in at most \(s\) variables. The Hrubeš–Yehudayoff bound on Boolean points in the image of a polynomial map gives at most \((2sd)^s\) coefficient vectors in \(\{0,1\}^{d+1}\) per topology. Briefly, the equations \(F_i(\mathbf c)(F_i(\mathbf c)-1)=0\) define the inverse image of the cube. By affine Bézout this inverse image has at most \((2sd)^s\) irreducible components, and each \(F_i\) takes a single value on each such component. The number of univariate topologies with at most \(s\) gates is at most \(s(5s^2)^s\) from the gate encoding above. Thus \(d=20s\lceil\log_2(s+2)\rceil\) gives strictly fewer than \(2^{d+1}\) realized binary vectors. [Fournier–Perifel–de Verclos, Lemma 5 and Theorem 5](https://arxiv.org/html/1304.5910)

Take the lexicographically first vector missed by all size-\(s\) topologies, now using the scalar-consistency equations to test exact membership. Given a vector and a candidate topology, whether it is realized is a Hilbert Nullstellensatz instance of length polynomial in \(s+d\). Introduce one variable for each positive-degree coefficient through \(d\) at each gate. Express the recurrence using \(O(s(d+1)^2)\) monomial occurrences in quadratic equations and equate the output coefficients to the prescribed bits. The circuit topology can be guessed with polynomially many bits. Under Dedekind GRH, \(\mathsf{HN}\in\mathsf{AM}\subseteq\mathsf{PH}\) by Koiran, so the existence of a realizing topology is in a fixed level of \(\mathsf{PH}\). Taking complements and asking whether an input prefix has a missed extension both stay in \(\mathsf{PH}\). Polynomially many adaptive prefix queries recover the lexicographically first missed vector in \(\mathsf{PH}\) on unary input \(1^n\), because \(k\) is fixed. [Koiran](https://cs.uwaterloo.ca/~r5olivei/courses/2025-spring-cs860/K96-HN-PH.pdf)

## Scope relative to earlier work

Bürgisser’s and Fournier–Perifel–de Verclos’s specialization framework already connects complex circuit constants to prime fields and then to Boolean circuits. For the direct unnormalized route, replacing constants by unknowns can give degree \(2^s\). Using that degree in the same prime-count estimate yields an \(O(s^2+\log(2+\tau))\) bit bound. The degree estimate here changes \(2^s\) to \(O(sd)\) while keeping at most \(s\) unknowns. This is what improves the prime bit bound for small \(d\). The comparison concerns the displayed unnormalized argument and trades additional ordinary gates for smaller moduli when the output degree bound is semantic. The coefficient-map idea and use of homogeneous parts are established tools. The claimed quantitative feature is the combination of one offset per gate, the low parameter degree, and the finite weighted prime criterion. [Fournier–Perifel–de Verclos, Lemmas 2 and 6](https://arxiv.org/html/1304.5910) · [Forbes, low-depth transfer over fields](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2024.31)

The existing permanent determinantal bound concerns affine determinant representations. This theorem concerns arbitrary arithmetic circuits. Restriction of scalars across finite extensions in one characteristic is a separate operation from the transfer of a coefficient identity across different characteristics.
