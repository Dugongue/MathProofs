# Deterministic output-sensitive root extraction for ordered branching programs

**Theorem.** Let $F$ be given by a read-once oblivious algebraic branching program (ROABP) in a specified variable order over a field $K$ of characteristic zero. Given positive integers $d$ and $W$, one can deterministically decide whether $F=\lambda G^d$ for a scalar $\lambda$ and a polynomial $G$ of ROABP width at most $W$ in that order. On a positive instance the algorithm outputs $\lambda$ and a minimum-width program for $G$ in the supplied order. For nonzero $F$, the output is normalized by $G(a)=1$ at a computed point $a$, so $\lambda=F(a)$. The field-operation count is polynomial in the input program size, its local degrees, $W$ and $1+\log d$. With rational coefficients and dense univariate transition entries, the same algorithm takes polynomial bit time in the binary input length and $W$. Over $\mathbb Q$, it also decides whether $F=G^d$ literally and produces a minimum-width literal root when one exists within the width cap. No perfect-power promise is needed.

The same method reconstructs a wider class of expressions. Given nonzero same-order ROABP polynomials $F_1,\ldots,F_m$, rational exponents $c_1,\ldots,c_m$ in binary, and total-degree and width caps $D,W$, compute $a$ with all $F_j(a)\ne0$. In the local coordinates $x$ at $a$, set $A_j(x)=F_j(a+x)/F_j(a)$. The algorithm decides whether the normalized formal series
$$
R(x)=\prod_{j=1}^m A_j(x)^{c_j}
$$
is a polynomial of total degree at most $D$ and same-order width at most $W$, and gives its optimal-width ROABP on positive inputs. The costs are polynomial in $D,W$, the input sizes, and the product of the maximum widths of the $m$ input programs. In particular this bound is polynomial for fixed $m$, regardless of the values of the exponents. It covers exact quotients and rational powers of quotients of two programs. The exponents are interpreted by formal binomial expansion at constant term $1$.

For explicitly represented finite fields, the width-capped root decision up to scalar and minimum-width reconstruction are also deterministic polynomial-time for every fixed exponent $d$. With variable $d$, one may charge polynomially in $W^e$, where $e$ is the part of $d$ prime to the characteristic. When the characteristic exceeds the input total-degree bound, the algorithm instead has polynomial dependence on $W$ and $1+\log d$.

## 1. Basic operations in one supplied order

Write an ROABP as a scalar product of $n$ univariate polynomial matrices, with input and output vectors folded into the first and last layers. Taking block direct sums gives sums, and taking layerwise tensor products gives products. Translation of any variable just translates its own matrix entries. Multiplying the $i$-th transition derivative by $x_i$ and summing the resulting $n$ programs implements the Euler operator
$$
\mathcal E=\sum_{i=1}^n x_i\partial_{x_i}.
$$
For each nonnegative integer $D$, one can retain the terms of total degree at most $D$ by carrying a running degree $0,\ldots,D$ as an additional state coordinate. A term of degree $e$ in any transition moves the degree state from $s$ to $s+e$ if $s+e\le D$. The initial state has degree zero, and all final degree states are summed. Denote this truncation by $J_{\le D}$. Its width increases by at most a factor $D+1$.

A known-order ROABP admits deterministic white-box identity testing with a nonzero evaluation witness. For each $i$, fix an integer grid with one more point than the largest degree of an entry of its transition. Carry a basis of the span of the row states reachable by grid prefixes. Each basis can be chosen from actual reachable rows and accompanied by the words that produced them. To update, multiply each retained row by every grid specialization of the next transition and retain a basis. Bilinearity proves by induction that discarding dependent rows does not change the final span. If a final row gives nonzero output it specifies a witness. Otherwise every grid evaluation vanishes, and coordinatewise interpolation shows the program is zero. The work is polynomial in the explicit program dimensions and transition degrees. This is a direct version of the standard white-box branching-program test.

The product of the $F_j$ is a nonzero polynomial and has a program of width at most the product of their widths. Applying the test to that product supplies the simultaneous anchor $a$. Below, all polynomials are in the translated coordinates where $a$ is the origin.

## 2. Formal root values and a linear differential check

Put
$$
B=\prod_j A_j,\qquad
C=\sum_j c_j\,\mathcal E(A_j)\prod_{k\ne j} A_k .
$$
Then $B(0)=1$ and $C(0)=0$. Formal differentiation of $(1+T)^c$ gives $(1+T)\frac{d}{dT}(1+T)^c=c(1+T)^c$. Substitution and the product rule yield
$$
B\,\mathcal E(R)=CR .
$$
For a candidate polynomial $P$ with $P(0)=1$, define $L(P)=B\mathcal E(P)-CP$. If $P-R\ne0$ and its lowest nonzero homogeneous component is $H_k$ of degree $k\ge1$, the lowest nonzero homogeneous component of $L(P)=L(P-R)$ is $kH_k$. The reason is that $\mathcal E$ acts as multiplication by $k$ in degree $k$, $B$ has constant $1$, and $C$ has zero constant. Characteristic zero ensures $kH_k\ne0$. In particular,
$$
J_{\le D}L(P)=0 \quad\Longleftrightarrow\quad J_{\le D}P=J_{\le D}R,
\qquad
L(P)=0 \quad\Longleftrightarrow\quad P=R .
$$
The verification programs are explicit by Section 1. Their widths are polynomial in the input width product and the candidate width, with no dependence on the numerical values of the $c_j$.

Let $T=J_{\le D}R$, with $T(0)=1$. Its value at any point $b$ can be found without forming its multivariate coefficient array. Substitute $x=tb$ into each normalized input $A_j$, computing the univariate program product modulo $t^{D+1}$. Each $A_j(tb)$ has constant $1$. Expand its power modulo $t^{D+1}$ by
$$
A_j(tb)^{c_j}=\sum_{k=0}^{D}\binom{c_j}{k}\bigl(A_j(tb)-1\bigr)^k\pmod {t^{D+1}}.
$$
Multiply the truncated powers and evaluate the resulting degree-$D$ univariate polynomial at $t=1$. Scaling $x$ by $t$ grades every monomial by total degree, so the result is exactly $T(b)$.

## 3. A deterministic counterexample for a candidate

Fix the interpolation alphabet $I=\{0,\ldots,D\}$. A candidate $P$ in the learner below has individual degree at most $D$, although its total degree can be as large as $nD$. If $P(0)\ne1$, the origin distinguishes it from $T$. Otherwise test $J_{\le D}L(P)$ and $P-J_{\le D}P$ by Section 1.

If both vanish then $P=T$ by Section 2. If the first program is nonzero, its witness $b$ makes $J_{\le D}L(P)(tb)$ nonzero as a polynomial in $t$. If $P(tb)$ equalled $T(tb)$, then $P(tb)$ would agree with $R(tb)$ through degree $D$. Euler differentiation commutes with this substitution, becoming $t\,d/dt$, so the restricted truncated residual would vanish. Thus this witness makes $P(tb)-T(tb)$ nonzero as a polynomial. If the second program is nonzero, its witness $b$ makes $P(tb)$ have some nonzero term above degree $D$, giving the same conclusion.

Try $t=0,\ldots,nD$ with the exact value algorithm, and keep a point $tb$ where $P$ and $T$ differ. Convert it to a word in $I^n$ one coordinate at a time. Holding the other coordinates fixed, their difference is a nonzero polynomial of degree at most $D$ in the current coordinate because it has a known nonzero value. One of the $D+1$ grid values preserves a nonzero difference. This produces a counterexample in the fixed alphabet using polynomially many evaluations. The test separates $P$ from the truncated series even if the whole series has no polynomial representation.

## 4. Exact ordered reconstruction

Regard $T$ on $I^n$ as a table with one axis per coordinate, accessible by the value algorithm. At cut $i$, its matrix has rows indexed by prefixes in $I^i$ and columns indexed by suffixes in $I^{n-i}$, with entry $T(p,s)$. A width-$w_i$ representation at that cut implies matrix rank at most $w_i$, by separating the product at the cut.

For each cut maintain finite prefix and suffix lists $P_i,S_i$ of equal sizes $r_i$ such that the square matrix $H_i=T(P_i,S_i)$ is nonsingular. Initialize both lists with the all-zero prefix or suffix, so $H_i=[1]$. The endpoint sizes are fixed at one. For the current lists, construct transitions on the alphabet by
$$
M_i(u)=H_{i-1}^{-1}T(P_{i-1}u,S_i)\qquad(u\in I).
$$
Interpolate each entry to degree at most $D$. The candidate is the scalar product of these matrices, with initial state $T(\varnothing,S_0)=1$. Ask for a counterexample by Section 3.

If the returned word is $p=u_1\cdots u_n$, let $v_i=T(u_1\cdots u_i,S_i)$ be its true row at cut $i$. If all $v_{i-1}M_i(u_i)=v_i$, the candidate would give the true final value, contradicting the counterexample. At a failing transition choose a coordinate $s'\in S_i$ of the difference, and let $q=u_1\cdots u_{i-1}$, $s=u_i s'$. Then
$$
T(q,s)-T(q,S_{i-1})H_{i-1}^{-1}T(P_{i-1},s)\ne0.
$$
This is the Schur complement for appending $q$ to the prefix list and $s$ to the suffix list of cut $i-1$. The enlarged minor is nonsingular. Neither index was already present, since a repeated row or column would make the displayed residual zero. The endpoint minor cannot fail at $i=1$, because its single prefix is the empty word. Thus the update increases one internal $r_i$.

If any minor reaches size $W+1$, it proves that $T$ has no program of width at most $W$. Otherwise there can be at most $(n-1)(W-1)$ rank increases. On acceptance by Section 3 the candidate equals $T$. At every cut its dimension is $r_i$, while the true table has a nonsingular $r_i$-minor there. Hence the exact width is minimal in the supplied order, cut by cut. This proof uses polynomially many true evaluations, interpolation steps and counterexample searches. Missing endpoint cases with $n=0$ reduce to the scalar $1$.

## 5. Full expression and perfect-power decisions

If the learner rejects by a width witness, the normalized series cannot equal a polynomial satisfying both caps. If the learner produces $P=T$, test the untruncated $L(P)$. Its vanishing proves $P=R$, and its nonvanishing rules out any polynomial of degree at most $D$ representing $R$. This proves the general expression statement.

For a single $F$ and exponent $1/d$, handle $F=0$ by returning its trivial root. For nonzero $F$, let $\Delta$ be the sum of the local degree bounds of the input program. Any polynomial $d$-th root has total degree at most $D=\lfloor\Delta/d\rfloor$, since $\deg G^d=d\,\deg G$. The normalized series is the unique formal $d$-th root with constant $1$. If a polynomial root up to scalar exists, evaluation at the anchor and rescaling put it in this normalized form. Conversely if the algorithm finds $P=R$, then $F(a+x)=F(a)P(x)^d$. Translating $P$ back preserves every cut rank, since translating variables is an invertible linear map on each polynomial space and acts independently on the two sides of every cut. Multiplication by a nonzero constant also preserves width. For a literal root over $\mathbb Q$, it remains to test whether $F(a)\in\mathbb Q^\times$ is a rational $d$-th power. For a fraction in lowest terms, test numerator and denominator by integer $d$-th-root algorithms and check the sign. Ordinary integer binary search with exponentiation capped above the input suffices for polynomial bit time even for $d$ in binary.

Over $\mathbb Q$ there is no uncontrolled coefficient build-up. The anchor and the white-box PIT witnesses use integer coordinates bounded by the explicit local degrees of their respective programs. The scaling and coordinate resets in Section 3 keep integer coordinates of polynomial bit length. For each direct product of explicit univariate matrices, clear coefficient denominators layer by layer. Numerators of coefficients of the univariate line specialization are sums over paths and local exponents, whose count has polynomial logarithm. Each summand is a product of polynomially many integers of polynomial bit length. Normalizing at the anchor and computing the binomial series through degree $D$ only use denominator powers of order $O(D)$, together with denominators dividing a product of $(D!)^m$ and the denominator of each $c_j$ to the $D$-th power. Thus each membership value has polynomial bit length. Candidate transition interpolation and inversion operate on matrices whose entries come directly from those true values, so determinant bounds and fraction-free linear algebra give polynomial bit costs at every learner step. The explicit verification programs have polynomial encoding lengths by the layer constructions. In their PIT computations, row bases can be chosen from actual evaluated prefix products, giving the same layerwise height bound. This handles the full bit-time claim.

## 6. Finite-field root search

Let the characteristic be $p$ and write $d=p^k e$ with $p\nmid e$. In the input program, discard local monomials whose exponents are not divisible by $p^k$. Since each variable occurs in just one layer, this operation discards exactly those output monomials with at least one exponent not divisible by $p^k$. A white-box identity test detects whether this changes $F$. For tests before extending the field, multiply the reachable row bases by all transition coefficient matrices instead of all grid evaluations. This gives the span of all coefficient rows and works over any field. If the projection changes $F$, it cannot be a scalar times a $d$-th power. Otherwise divide all remaining transition exponents by $p^k$ and apply inverse scalar Frobenius to their coefficients. This gives $F_0$ with $F_0^{p^k}=F$, because Frobenius is an automorphism of a finite field. The root equation up to scalar is now $F_0=\lambda_0G^e$. We can handle zero and constant cases directly and also reject nonconstant inputs when $e>\Delta$, where $\Delta$ is the degree bound for $F_0$.

Work over a finite auxiliary extension when the base field is too small for the grids. Choose its cardinality to exceed $1+\Delta+2n\Delta$, which suffices for evaluation, interpolation, and the line searches below. If the base cardinality $q$ already exceeds the bound, use the base field. Otherwise the least adequate extension degree gives cardinality at most $q(1+\Delta+2n\Delta)$. Enumerating monic polynomials of that degree and applying the deterministic finite-field irreducibility test gives an explicit extension in polynomial time. A grid means any fixed list of distinct elements of the requisite size, including zero. No root or discrete logarithm operation is needed in this extension.

Find an anchor over this working field and let $A=F_0(a+x)/F_0(a)$. There is a unique formal series $R$ with constant $1$ and $R^e=A$. One way to compute its coefficients by homogeneous degree is to extend the known terms below degree $j$ by $H_j$. This changes the degree-$j$ component of the power by $eH_j$. The same recurrence on the univariate line $x=tb$ gives exact evaluations of $J_{\le D}R$ for $D=\lfloor\Delta/e\rfloor$ in polynomial time by truncated polynomial arithmetic. Exponentiation here is ordinary univariate repeated squaring.

For the equivalence oracle in Section 3 use
$$
J_{\le D}(A-P^e)
\qquad\text{and}\qquad
P-J_{\le D}P
$$
and handle $P(0)\ne1$ separately. The factorization of $R^e-P^e$ has one factor $R-P$ and the other has constant $e$, a unit. Thus the first residual is zero exactly when $P$ and $R$ agree up to degree $D$. The line argument from Section 3 works for this residual as well. The first residual has a program built with $e$ layerwise tensor products of the candidate, so the equivalence checks take time polynomial in $W^e$. Each variable has degree at most $\max(\Delta,eD)\le\Delta$ in this untruncated residual. Once $P=J_{\le D}R$, verify $A=P^e$ by the corresponding untruncated test. This decides existence and gives a minimum-width root up to scalar in the working field.

If $p>\Delta$, the linear Euler residual replaces the tests involving $P^e$. For the truncated check, the first nonzero degree under consideration is at most $D<p$, so the lowest-term argument of Section 2 still applies. For the final check, the learned $P$ has degree at most $D$. Write $Q=A-P^e$, of degree at most $\Delta$. The untruncated residual is
$$
eA\mathcal E(P)-P\mathcal E(A)=eQ\mathcal E(P)-P\mathcal E(Q).
$$
If $Q\ne0$, its lowest nonzero term has some degree $1\le j\le\Delta<p$ and contributes $-jQ_j$. The verification program's width is therefore linear in the candidate width with factors polynomial in the input dimensions. In both field regimes, grid sizes and line-degree bounds are polynomial in the stated parameters.

Translate the learned polynomial back to the original variables and divide by its leading coefficient in lexicographic monomial order. A leading coefficient can be extracted by backward suffix-span computation on the coefficient transitions and then greedily choosing the largest exponent at each layer with a nonzero suffix continuation. Call the resulting monic polynomial $G$. Since $F_0$ belongs to the base field, applying the scalar $q$-Frobenius to the identity $F_0=\lambda_0G^e$ gives another monic root up to scalar. Such a monic root is unique by unique factorization, so Frobenius fixes $G$ and $\lambda_0$. Hence their coefficients are in the base field.

To recover a base-field program, represent each working-field entry by its multiplication matrix on a fixed base-field basis of the extension. Start at the basis coordinate of $1$ and apply a base-field linear functional taking $1$ to $1$ at the end. This outputs $G$, because its coefficients already lie in the base field. The temporary width increases by the extension degree. Minimize the program by computing the spans of all prefix coefficient rows and suffix coefficient columns at each cut. Restrict to the reachable row span and quotient by the rows annihilating the suffix span. Every coefficient transition descends to these quotients, since an unobservable row remains unobservable after adjoining a letter. The quotient dimension is exactly the coefficient-matrix rank across the cut. These ranks are unchanged by extension and by scaling, so the resulting base-field program has the required minimum width. Finally return the scalar $\lambda_0^{p^k}$ for the original input. Over a fixed finite field one can also decide literal roots by testing the finitely many scalar values.

## Relation to earlier work

The earlier [high-power root result](../ROABPHighPowerRoots/PROOF.md) provides structural width one when the exponent is at least the power's width. The algorithm above permits every exponent, and depends on the width of the requested output. The characteristic-zero question of a general polynomial upper bound on the output width in terms of the power's width and degree remains open here. The exact-learning method uses finite Hankel minors as in the earlier [learning algorithms for weighted automata](https://cs.nyu.edu/~mohri/pub/cai.pdf) and the rank characterization of ordered programs. The identity-testing step is the elementary row-span argument underlying [Raz–Shpilka](https://doi.org/10.1007/s00037-005-0188-8).

The differential criterion uses the same broad idea as the logarithmic-derivative recombination step in [Bhattacharjee, Kumar, Rai, Ramanathan, Saptharishi and Saraf, *Deterministic factorization of constant depth circuits from whitebox PIT*](https://arxiv.org/abs/2611.09035), which also relates to the project's earlier white-box PIT-to-factorization result. The new combination uses a homogeneous truncation of the linear differential equation as an exact equivalence oracle for ordered reconstruction. This avoids constructing a high power of the candidate and returns a minimum-width same-order program when the width cap permits. [Andrews et al., Section 6](https://drops.dagstuhl.de/storage/00lipics/lipics-vol362-itcs2026/html/LIPIcs.ITCS.2026.9/LIPIcs.ITCS.2026.9.html#S6) ask the structural power/root question. The related [Huang, Cao, Qiu and Gao, *Deterministic Polynomial-time Exact-root Computation for Sparse Polynomials with Bounded Total Degree*](https://arxiv.org/abs/2607.02364) treats sparse input and output. A targeted search found these ingredients and related algorithms. Publication priority for their ordered-program combination remains unestablished. This is an informal proof.
