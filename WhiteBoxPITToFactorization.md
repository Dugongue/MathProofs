# White Box Identity Testing and Deterministic Factorization in Restricted Algebraic Models

**MathProofs project — Informal proposed proof — 31 October 2026**

## Abstract

We give a deterministic reduction from complete polynomial factorization to white-box polynomial identity testing for effectively robust algebraic models. The reduction applies to arithmetic formulas, ordinary commutative algebraic branching programs, and the family of constant-depth arithmetic circuits. It works over fields of characteristic zero and fields of sufficiently large positive characteristic, with dense univariate factorization over the base field retained as an explicit numerical resource. For constant-depth circuits, the queries and factor representations have depth at most the input depth plus an absolute constant. Every candidate factor is rebuilt directly from the original input, so adaptive reconstruction does not accumulate symbolic depth or repeatedly enlarge earlier candidates.

The construction uses a critical-value polynomial to find a regular fiber, an explicit residue and finite logarithm decoder for coprime primary clusters, and a partition refinement algorithm driven by failed product identities. A failed identity yields a witness line whose dense factorization strictly joins the current partition. There are at most as many strict joins as the number of initial fiber factors minus one. The entire algorithm needs at most one initial dense univariate factorization; subsequent line computations reuse its factors.

This manuscript presents an informal proposed resolution of the first question in Section 7 of [Bhattacharjee et al., *Closure under factorization from a result of Furstenberg*](https://arxiv.org/html/2506.23214v1#S7), under the explicit constructive interpretation of robustness stated below. It incorporates an internal mathematical audit. It has not received independent human peer review, and no Lean verification is claimed for the general class and field extensions developed here.

## 1 The question and its computational setting

The first open question in Section 7 of [1] asks whether the connection between identity testing and deterministic factorization extends to white-box identity testing for restricted algebraic models. The accompanying formulation in Section 5.7 starts with a robust class $\mathscr C$ and a class $\mathscr C'$ obtained by placing polynomial-size constant-depth arithmetic circuits over $\mathscr C$ computations. The issue is whether a white-box PIT algorithm for $\mathscr C'$ can replace the black-box identity-testing resource in deterministic factorization of $\mathscr C$ inputs.

We make the representation and algorithmic assumptions in that formulation explicit. In particular, Remark 5.3 of [1] retains deterministic univariate factorization when extending beyond the rational field. The theorem below uses the same numerical baseline. It does not assert that a Boolean identity-testing oracle produces new algebraic field constants.

An **effective robust representation system** $\mathscr C$ over a field $K$ has explicit finite descriptions with the following uniform operations:

1. Field constants and coordinate variables have elementary descriptions.
2. A list of descriptions can be compiled into a description of its sum or product in time and size polynomial in the total list encoding, variable count, and the degree budgets being used.
3. Substitution of explicitly given sparse polynomials of polynomial degree and description length can be compiled with polynomial overhead.
4. A description can be evaluated using polynomially many field operations.

The second condition concerns polynomial-length lists. Semantic closure alone, or a binary constructor with a polynomial bound that is then iterated an unbounded number of times, is not a sufficient construction guarantee.

For a fixed integer $k$, a $\mathscr C'_k$ description is a polynomial-size, depth-at-most-$k$, unbounded-fan-in arithmetic circuit whose leaves refer to explicit $\mathscr C$ descriptions. All wrapper gates, wires, constants, and referenced descriptions are charged. The notation $\mathscr C'$ denotes the resulting constant-depth wrapper family. PIT means formal polynomial identity testing, not merely testing whether a polynomial vanishes as a function on a finite field.

The field-arithmetic model provides addition, subtraction, multiplication, equality, and inversion after a nonzero test. Dense univariate factorization over $K$ is a separately paid routine returning factors over $K$. Binary-time conclusions will be stated only for explicit field encodings with the necessary operation and height bounds.

The ABP implication itself is already known: Sinhababu and Thierauf prove a white-box reduction in [2, Theorem 5.1 and the discussion on pp. 38–39]. Here it is recovered by the same construction used for the other models. No new-result priority is claimed for that ABP theorem.

## 2 Main theorem

Let

$$
h(D)=100(D+1)^8.
$$

**Theorem 1.** Let $K$ have characteristic zero or characteristic $p>h(D)$, where $D\ge 1$ is a supplied upper bound on the actual total degree of the input polynomial, represented in unary. Let $\mathscr C$ be an effective robust representation system as defined above. There is an absolute wrapper depth $k_0$ and a deterministic algorithm which, given a $\mathscr C$ description of a polynomial $P$, computes its complete irreducible factorization over $K$ using:

- polynomially many field operations and equality tests;
- polynomially many white-box PIT calls on polynomial-size $\mathscr C'_{k_0}$ descriptions;
- at most one dense univariate factorization over $K$, of degree at most $D$.

Every nonzero output has the form

$$
P=c\prod_{j=1}^{q} G_j^{e_j},
$$

where $c\in K^\times$, each $e_j$ is a positive integer, the $G_j$ are irreducible over $K$, and no two are associates. The factors have polynomial-size $\mathscr C$ descriptions. Zero has a separate output tag; a nonzero constant has an empty factor list and its value as unit.

All polynomial bounds are in the input description length, the variable count, and $D$, with the effective representation system fixed. If PIT has cost $T$ and dense univariate factorization has cost $U$, a safe resource expression is

$$
\operatorname{poly}(N)
+\operatorname{poly}(N)\,T(\operatorname{poly}(N))
+U(\operatorname{poly}(N)).
$$

No regularity assumption on an arbitrary function $T$ is hidden by absorbing the multiplicative overhead. In particular, polynomial-time PIT and polynomial-time univariate factorization give polynomial total time in the applicable computational model.

**Corollary 2.** The theorem gives polynomial-size formula outputs from formula inputs, and polynomial-size ordinary commutative ABP outputs from ordinary commutative ABP inputs. For every fixed input circuit depth $\Delta$, there is an absolute constant $c$ such that white-box PIT through depth $\Delta+c$ suffices for complete factorization of depth-$\Delta$ inputs, with factor circuits of depth at most $\Delta+c$.

The constant-depth corollary concerns the family of constant depths. It does not assert that PIT restricted to exactly the input depth $\Delta$ suffices.

**Corollary 3.** Over $\mathbb Q$ and over every fixed algebraic number field in its usual power-basis encoding, the corresponding polynomial-time PIT assumption alone gives polynomial binary-time complete factorization for these concrete models. The numerical factorization routines in these fields are supplied by classical algorithms [4,5]. For fixed circuit depth, the binary-time polynomial may depend on that depth.

We prove Theorem 1 first in the field-arithmetic model, and then justify the representation and binary-time conclusions.

## 3 Interpolation and nonzero witnesses

If a polynomial $R(z)$ has degree at most $M$ and $\alpha_0,\ldots,\alpha_M$ are distinct field elements, every coefficient is a known linear combination of evaluations:

$$
[z^j]R=\sum_{i=0}^{M}\lambda_{j,i}R(\alpha_i).
$$

The weights are obtained by ordinary Lagrange interpolation. Thus a coefficient projection introduces a polynomial-length weighted sum of specializations. A fixed number of successive projections is still a fixed-height expression. We always use a bound on the polynomial **before** projection; a desired truncation order is not itself an interpolation degree bound.

**Lemma 4.** Given a nonzero polynomial $W(x_1,\ldots,x_n,y)$ of total degree at most $M$ and a white-box PIT routine for its representation class, one can find $b\in\{0,\ldots,M\}^n$ such that $W(b,y)$ is a nonzero polynomial, using at most $n(M+1)$ PIT calls, provided these grid elements are distinct in $K$.

**Proof.** Fix the coordinates in order. If every one of the $M+1$ substitutions for the next coordinate made the remaining polynomial zero, interpolation in that coordinate would imply that the current polynomial was zero. At least one substitution therefore preserves nonzeroness. Use PIT to select it, and continue. All other variables, including $y$, remain symbolic during each test. ∎

This is a white-box decision-to-search procedure on known constructed sources. It requires no hitting set for an unknown factor.

## 4 Degree discovery and monicization

First test whether $P$ is zero. Otherwise extract the homogeneous components of $P$ from $P(t\mathbf x)$ by degree-$D$ interpolation and use PIT to determine its actual total degree $d\le D$. If $d=0$, evaluate the nonzero constant and return it with an empty factor list.

For $d>0$, let $P_d$ be the highest homogeneous component. Lemma 4 gives a vector $v$ such that

$$
\gamma=P_d(v)\ne0.
$$

Because $P_d$ has positive degree, some coordinate $v_j$ is nonzero. Make the invertible change of variables

$$
x_j=v_jy,\qquad x_i=z_i+v_i y\quad(i\ne j),
$$

and divide the source by the computed scalar $\gamma$. Write the normalized polynomial as $f(\mathbf z,y)$. It has total degree $d$, is monic in $y$, and has $y$-degree $d$. The inverse substitution is

$$
y=x_j/v_j,\qquad z_i=x_i-v_i x_j/v_j.
$$

Record this map and $\gamma$ for the final output. Only sparse linear substitutions and a nonzero scalar inverse have been used.

Every nonconstant divisor of $f$ has positive $y$-degree. Otherwise a nonconstant polynomial in $\mathbf z$ alone would divide its leading $y$-coefficient, which is $1$. Moreover, every irreducible factor can be normalized to be monic in $y$: the product of its leading coefficients is $1$ in $K[\mathbf z]$, so each such coefficient is a nonzero field constant.

## 5 Computing a regular center from the input

A center $a$ will be called **regular** if the fibers of the distinct monic irreducible factors of $f$ are squarefree and pairwise coprime. These factors are used only as mathematical witnesses; the algorithm does not know them.

For $d=1$, every center is regular and we use the constant critical polynomial $1$. Suppose $d>1$, put $m=d-1$, and define

$$
U=\frac{1}{d}\partial_y f,\qquad
V(w)=w^m U(1/w).
$$

The polynomial $U$ is monic and $V(0)=1$. The derivative can be constructed as $[u]f(\mathbf z,y+u)$, avoiding recursive product-rule depth.

Let $p_j(U)$ denote the Newton power sum of the roots of $U$, counted with multiplicity. We compute these without finding any roots. Set $p_0(U)=m$ and, for $j\ge1$, use

$$
p_j(U)=
-[w^{j-1}]\left(
V'(w)\sum_{\ell=0}^{j-1}(1-V(w))^\ell
\right).
$$

Indeed, $-V'(w)/V(w)=\sum_{j\ge1}p_j(U)w^{j-1}$, and $1-V$ is divisible by $w$. This identity involves no division by $j$, so it remains valid even for indices at least the characteristic.

For $1\le k\le m$, compute

$$
q_k=\sum_{j=0}^{Dk}([y^j]f^k)\,p_j(U).
$$

Over a splitting field, $q_k=\sum_\beta f(\mathbf z,\beta)^k$, where $\beta$ ranges over the roots of $U$. Therefore, if

$$
E_C(w)=
\left[
\sum_{r=0}^{m}\frac{1}{r!}
\left(-\sum_{k=1}^{m}\frac{q_k}{k}w^k\right)^r
\right]_{\deg_w\le m},
$$

then the explicitly constructed polynomial

$$
C_f(T)=T^m E_C(1/T)
$$

satisfies

$$
C_f(T)=\prod_{U(\beta)=0}\bigl(T-f(\mathbf z,\beta)\bigr).
$$

Here and below reversal is implemented by a finite coefficient table; it does not introduce a symbolic division gate.

**Lemma 5.** If $r$ is the number of distinct roots of $f$ over an algebraic closure of $K(\mathbf z)$, then

$$
\operatorname{ord}_{T=0}C_f=d-r.
$$

**Proof.** A root of $f$ of multiplicity $e$ is a root of $f_y$ of multiplicity exactly $e-1$, since $e\le D$ is invertible in $K$. The remaining derivative roots have nonzero values under $f$. Thus precisely $\sum(e-1)=d-r$ factors in the product defining $C_f$ vanish at $T=0$. ∎

The polynomial $C_f$ is monic in $T$, so some coefficient is nonzero. Use PIT to find its lowest nonzero coefficient $c_\nu(\mathbf z)$, then use Lemma 4 to select $a$ with $c_\nu(a)\ne0$. Every lower coefficient is identically zero and remains zero after specialization. Consequently $f(a,y)$ has the same number $r$ of distinct roots as the generic polynomial.

For completeness, write the proof-only factorization

$$
f=\prod_{j=1}^{q}g_j^{e_j}
$$

with distinct monic irreducibles. Gauss's lemma and characteristic zero, or $p>D$, make each $g_j$ separable over $K(\mathbf z)$. Hence $r=\sum_j\deg_y g_j$. Monicity preserves each degree at every specialization. The number of distinct roots of their union can attain this sum only if each fiber $g_j(a,y)$ is squarefree and different fibers are coprime. The computed center is therefore regular.

## 6 Primary fiber labels

Perform the one dense univariate factorization of

$$
f_0(y)=f(a,y)=\prod_{i=1}^{r_0}a_i(y)^{\mu_i},
$$

where the $a_i$ are distinct monic irreducibles over $K$ and $\mu_i>0$. There are at most $d$ labels.

Regularity has two consequences. Each $a_i$ belongs to the fiber of exactly one global irreducible $g_j$, and its observed exponent $\mu_i$ is exactly the global exponent $e_j$. This defines an unknown ancestor partition of the labels. The partition is a proof device; it is not supplied to the algorithm.

For a subset $I$ of labels, compute the dense numerical polynomials

$$
A_I=\prod_{i\in I}a_i^{\mu_i},\qquad
B_I=f_0/A_I.
$$

They are monic and coprime, even though they may have repeated roots internally. We next construct a candidate $G_I$ using only $f$, $a$, $A_I$, and $B_I$.

The boundary cases are explicit:

$$
\operatorname{Decode}(1,f_0)=1,\qquad
\operatorname{Decode}(f_0,1)=f.
$$

In particular, an all-label block has a well-defined complementary decoder. The formulas with coefficient index $m\ell-1$ below are used only for $m>0$.

## 7 Coprime Hensel clusters and a residue functional

Fix monic coprime $A,B\in K[y]$ of positive degrees $m,n$, with $AB=f_0$. Let $R=K[\mathbf z]$ and radialize the original normalized source:

$$
F(t,\mathbf z,y)=f(a+t(\mathbf z-a),y)=AB+E.
$$

Then $t$ divides $E$, $F$ is monic in $y$, and its $y$-degree is $m+n=d$.

**Lemma 6.** There are unique formal polynomials

$$
H,K_1\in R[[t]][y]
$$

that are monic of $y$-degrees $m,n$, satisfy $H(0)=A$, $K_1(0)=B$, and obey $F=HK_1$.

**Proof.** Suppose the coefficients below $t^s$ have been found. At the next order we must solve

$$
B h_s+A k_s=c_s,
\qquad \deg_y h_s<m,\quad\deg_y k_s<n,
$$

for a known polynomial $c_s$ of degree below $m+n$. Since $A,B$ are coprime numerical polynomials, this is an invertible linear map over $K$ and remains invertible over $R$. Explicitly, reduce modulo $A$ and multiply by the inverse of $B$ modulo $A$ to find $h_s$; then obtain $k_s$ by exact division by $A$. The degree bounds give uniqueness. Recursion constructs the formal witnesses. No squarefreeness of $A$ or $B$ is required. ∎

The recursive construction proves existence and uniqueness only. The algorithm will use a noniterative finite expression.

Work in rational functions of $y$ whose denominators divide powers of $AB$. Define $\Pi_A$ by the unique coprime partial-fraction decomposition: retain the proper part supported on $A$, and discard the polynomial part and the proper part supported on $B$. This operator is independent of the chosen denominator powers. Define

$$
\operatorname{res}_A(Q)=[y^{-1}]_\infty\Pi_A(Q),
$$

where the coefficient is taken in the Laurent expansion at infinity. This is an algebraic coefficient functional. No analytic integration or evaluation at unknown roots is involved.

For $\ell\ge1$, compute a numerical polynomial $J_\ell$ satisfying

$$
J_\ell B^\ell\equiv1\pmod{A^\ell},
$$

and define

$$
\Lambda_\ell(P)=
[y^{m\ell-1}]\bigl((PJ_\ell)\bmod A^\ell\bigr).
$$

**Lemma 7.** For every polynomial $P$ over $R$,

$$
\Lambda_\ell(P)=
\operatorname{res}_A\left(\frac{P}{(AB)^\ell}\right).
$$

**Proof.** Put $N=(PJ_\ell)\bmod A^\ell$. Then $P-NB^\ell$ is divisible by $A^\ell$, so for a polynomial $T$,

$$
\frac{P}{A^\ell B^\ell}
=\frac{N}{A^\ell}+\frac{T}{B^\ell}.
$$

The second summand has no $A$-supported proper part. Since $\deg N<m\ell$ and $A^\ell$ is monic, the $y^{-1}$ coefficient of $N/A^\ell$ is precisely $[y^{m\ell-1}]N$. ∎

This proves consistency between the denominator-specific implementations $\Lambda_\ell$ and the single operator $\Pi_A$. It also proves that repeated roots inside a primary cluster cause no problem.

## 8 A finite cluster decoder

For a monic degree-$m$ polynomial $Q$, write

$$
\operatorname{rev}_m Q(w)=w^m Q(1/w).
$$

This polynomial has constant coefficient $1$. Define the known numerical coefficients

$$
b_k=[w^k]\log\operatorname{rev}_m A(w),\qquad 1\le k\le m.
$$

Every logarithm and exponential in this construction is a finite, explicitly truncated polynomial expression. Let

$$
R_k(t,\mathbf z)=
\sum_{\ell=1}^{D}\frac{(-1)^{\ell+1}}{\ell}
\Lambda_\ell\bigl(y^{k-1}E^\ell\bigr).
$$

**Lemma 8.** For $1\le k\le m$,

$$
b_k+R_k
\equiv[w^k]\log\operatorname{rev}_m H(w)
\pmod{t^{D+1}}.
$$

**Proof.** In the $t$-adic quotient through order $D$,

$$
\log(F/(AB))=
\log(H/A)+\log(K_1/B).
$$

Expand the left side as

$$
\sum_{\ell=1}^{D}
\frac{(-1)^{\ell+1}}{\ell}\frac{E^\ell}{(AB)^\ell}.
$$

Apply the same functional $\operatorname{res}_A$ to $y^{k-1}$ times every coefficient. Lemma 7 identifies the result with $R_k$. The $K_1/B$ contribution has poles only on $B$, so its contribution is zero. The $H/A$ contribution is its coefficient of $y^{-k}$ at infinity. After $y=1/w$, this is

$$
[w^k]\bigl(\log\operatorname{rev}_m H
-\log\operatorname{rev}_m A\bigr).
$$

The comparison is valid in the rectangular quotient modulo $t^{D+1}$ and $w^{m+1}$. Indeed, $H/A-1$ is divisible by $t$ and, at infinity, by $w$ as well. The required logarithmic identities use only indices at most $\max(D,m)=D$. All their denominators are therefore invertible under our characteristic assumption. ∎

Equivalently, for Newton sums,

$$
p_k(H)\equiv p_k(A)-kR_k\pmod{t^{D+1}}.
$$

Now form the explicit polynomials

$$
L(t,\mathbf z,w)=\sum_{k=1}^{m}(b_k+R_k)w^k,
\qquad
S(t,\mathbf z,w)=\sum_{r=0}^{m}\frac{L^r}{r!}.
$$

Define the computed candidate by

$$
G_A(\mathbf z,y)=
\sum_{k=0}^{m}y^{m-k}
\sum_{i=0}^{D}[t^iw^k]S.
$$

**Lemma 9.** The candidate is monic of $y$-degree $m$, has center fiber $A$, and is the order-$D$ $t$-jet of $H$ evaluated at $t=1$. The construction commutes with every specialization of the parameter variables $\mathbf z$. If $H$ is the radialization of a polynomial factor of total degree at most $D$, the candidate is that factor exactly.

**Proof.** Lemma 8 identifies $L$ with the reversed logarithm through the retained coefficient rectangle. Since $w$ divides $L$, terms of exponential order greater than $m$ cannot affect a retained $w$ coefficient. The finite exponential inverts the finite logarithm modulo $w^{m+1}$, and multiplication cannot introduce a contribution from a discarded $t$ coefficient into a smaller $t$ coefficient. Thus the retained coefficients of $S$ equal those of $\operatorname{rev}_m H$.

The coefficient of $w^0$ is $1$, proving monicity. At $\mathbf z=a$, the radial source is constant in $t$, so $E=0$ and the construction returns $A$. Numerical inverses, polynomial operations, monic remainders, and coefficient projections commute with specialization; this proves naturality. Finally, radialization of a total-degree-at-most-$D$ polynomial has $t$-degree at most $D$, so its retained jet is exact. The explicit empty and full seed branches have the same properties. ∎

No unknown global factor, splitting-field computation, or formal-series oracle is an input to $G_A$.

### Full degrees before coefficient projection

The symbolic expressions above must be interpolated at their full degrees:

- $E$ has degree at most $D$ separately in $t$, $y$, and the parameter group $\mathbf z$.
- For $\ell\le D$, $E^\ell$ has those degrees at most $D^2$.
- $L$ has $w$-degree at most $m\le D$ and $t$- and parameter degrees at most $D^2$.
- Before projection, $S$ has $w$-degree at most $m^2\le D^2$ and $t$- and parameter degrees at most $mD^2\le D^3$.

For example, using only $D+1$ values of $t$ to interpolate the unprojected $S$ would be invalid. We use the full bound before retaining its order-$D$ jet.

The functional itself is also explicit. Precompute

$$
\omega_{\ell,k,i}=
[y^{m\ell-1}]
\bigl((y^{i+k-1}J_\ell)\bmod A^\ell\bigr).
$$

Then

$$
\Lambda_\ell(y^{k-1}E^\ell)=
\sum_{i=0}^{\ell D}\omega_{\ell,k,i}[y^i]E^\ell.
$$

This expresses the decoder using only polynomially many powers, weighted sums, and coefficient projections of the original source.

## 9 Dense factorization on a witness line

We next supply the numerical subroutine used by the selector. It is not an assumed multivariate factor oracle.

Let $b$ be any parameter point and set

$$
\mathcal F_b(t,y)=f(a+t(b-a),y).
$$

It is monic of $y$-degree $d$ and total degree exactly $d$. Every nonconstant factor has positive $y$-degree and can be made monic. Degree additivity forces the total degree of each factor to equal its $y$-degree: the nonnegative differences between the two degrees sum to zero in their product.

Each line image $g_j(a+t(b-a),y)$ is squarefree. Otherwise a repeated monic line factor would give a repeated factor in its squarefree zero fiber $g_j(a,y)$. Line images from different global ancestors are coprime, because a common positive-$y$-degree monic factor would have a nonconstant zero fiber dividing both coprime ancestor fibers.

Compute the dense monic gcd over $K(t)[y]$ and set

$$
Q_b=\frac{\mathcal F_b}{\gcd(\mathcal F_b,\partial_y\mathcal F_b)}.
$$

Since all positive multiplicities are at most $D<p$ in positive characteristic, this is the squarefree part. Gauss's lemma puts both the monic gcd and $Q_b$ in $K[t,y]$. Their dense computation uses fraction-free subresultants: the matrices have polynomial order and polynomial-degree entries in $t$, and all zero tests are literal coefficient tests.

Write $\delta=\deg Q_b$. The preceding observations give

$$
\deg_y Q_b=\deg Q_b=\delta\le d,
\qquad
Q_b(0,y)=\prod_{i=1}^{r_0}a_i(y).
$$

Thus $Q_b$ satisfies the monic and squarefree-zero-fiber hypotheses of Lecerf's revised deterministic algorithm [3, Algorithm 1 and Proposition 4]. For two variables, with lifting precision $2\delta$, that algorithm uses polynomially many field operations and the univariate factorization of $Q_b(0,y)$, under characteristic zero or $p>\delta(\delta-1)$.

The required univariate factors are already available: they are exactly the $a_i$ from Section 6. Supply that list to the lifting stage rather than repeating the initial factorization. Dense exact division recovers the multiplicity of each resulting irreducible in $\mathcal F_b$. Therefore every witness-line factorization uses polynomially many numerical field operations and **no further univariate factorization call**. The main characteristic bound dominates the backend's explicit characteristic requirement.

## 10 The adaptive partition algorithm

Maintain a partition $\mathcal P$ of the $r_0$ fiber labels. Initially every block is a singleton. Its correctness invariant is:

> Every current block is contained in the fiber-label set of one global irreducible factor.

For a current block $I$, compute $A_I,B_I$ and the two complementary candidates $G_I,G_{I^c}$, each rebuilt from the original normalized source. Test the known expression

$$
W_I(\mathbf z,y)=G_I(\mathbf z,y)G_{I^c}(\mathbf z,y)-f(\mathbf z,y)
$$

by white-box PIT.

If every block passes, terminate. If a block fails, apply Lemma 4, leaving $y$ symbolic, to find $b$ for which $W_I(b,y)$ is nonzero. Factor $\mathcal F_b$ by Section 9. For each monic irreducible line factor $u(t,y)$, determine which known $a_i$ divide $u(0,y)$ by dense division. Join the resulting incidence partition with $\mathcal P$ and restart the scan.

### Safety of a partition join

Every line factor divides the line image of at least one global irreducible. It cannot divide two different ancestors: its positive-degree monic zero fiber would divide two coprime ancestor fibers. Moreover its zero fiber is squarefree, since it divides the squarefree fiber of its ancestor. It is consequently a product of a subset of that ancestor's $a_i$, each once. These subsets partition the labels. Joining their incidence blocks therefore preserves the invariant.

### A failed test forces a crossing

**Lemma 10.** Every failed test strictly decreases the number of current partition blocks.

**Proof.** Suppose no line-factor incidence block crosses the failed cut $I$. Group the line factors, with their actual multiplicities, into complementary products $H_I(t,y)$ and $H_{I^c}(t,y)$. They have initial fibers $A_I$ and $B_I$, multiply to $\mathcal F_b$, and each has $t$-degree at most $d\le D$.

Since $A_I$ and $B_I$ are coprime, Lemma 6 identifies these products with the two formal Hensel clusters of the specialized radial source. Lemma 9 and specialization naturality identify their retained jets with the two computed candidates at $b$. Their degree bounds make those jets exact. Evaluating at $t=1$ yields

$$
G_I(b,y)G_{I^c}(b,y)=f(b,y),
$$

contradicting the choice of $b$. Thus some incidence block crosses $I$. As $I$ is an entire current block, the join strictly merges current blocks. ∎

There are at most $r_0-1$ strict joins. Restarting after each join gives at most $r_0$ scans and at most $r_0^2$ inspected block tests. No subset enumeration or exhaustive search over directions occurs.

## 11 Terminal purity and the complete output

**Lemma 11.** At termination each current block is the complete label set of one global irreducible, and its candidate is that irreducible raised to its full multiplicity.

**Proof.** The accepted product identity makes $G_I$ a genuine divisor of $f$. By unique factorization it is a product of powers of global irreducibles. Its center fiber is exactly $A_I$, and the invariant puts every label in $I$ inside one ancestor class, say that of $g_j$. Any other global factor would contribute a center label outside $I$. Therefore

$$
G_I=g_j^k.
$$

There is no extra scalar because both sides are monic in $y$. Choose any $i\in I$. Its exponent in the candidate's fiber is $\mu_i$, whereas its exponent in $g_j(a,y)^k$ is $k$, because $g_j(a,y)$ is squarefree. Thus

$$
k=\mu_i=e_j.
$$

The candidate contains the entire global power and hence every label of that ancestor. Distinct terminal blocks cannot have the same ancestor, and every ancestor has a nonempty label set. This proves completeness, irreducibility of the underlying roots, and absence of associated duplicates. ∎

It remains to construct the root source from the accepted source, rather than assume it. Let $G_I=g^e$ be monic of degree $eh$ in $y$. Then

$$
\operatorname{rev}_{eh}G_I=(\operatorname{rev}_h g)^e
$$

has constant coefficient $1$. Put $U=\operatorname{rev}_{eh}G_I-1$, and compute

$$
\left[
\sum_{j=0}^{h}\binom{1/e}{j}U^j
\right]_{\deg_w\le h}.
$$

The finite binomial identity shows that this is $\operatorname{rev}_h g$. Equivalently, it is the unique constant-one $e$-th root in the truncated ring, since $e$ is invertible. All factorial indices and $e$ are at most $D$. Reverse back, apply the recorded inverse linear substitution, restore the original variable names, and return the factors with their observed multiplicities and scalar $\gamma$.

The inverse coordinate map is a polynomial-ring automorphism, so it preserves irreducibility and nonassociation. The final factors need not be monic in the original coordinates; that is not part of the output contract. Their powered product, multiplied by $\gamma$, is the original input exactly.

## 12 Uniform source construction and constant depth

Every symbolic construction above is assembled from a fixed list of stages:

1. Sparse substitutions into the original input, including monicization and radialization.
2. Weighted sums, polynomially bounded products and powers.
3. Coefficient projections in a fixed number of auxiliary variables.
4. Finite logarithmic, exponential, and binomial expressions.
5. Coefficient-table reconstruction and the inverse linear substitution.

A power of exponent $j$ uses $j$ repeated inputs to one unbounded-fan-in product gate, with all wires counted. A weighted sum uses a scalar-product layer and a sum layer. Coefficient interpolation has the same form. The finite ranges are polynomial in $D$, and the number of nested stages is an absolute constant. Thus all these expressions have polynomial size and absolute wrapper depth over sparse substitutions of the original source.

It is important that the partition loop does not replace the original source by the previous candidate. Each new block changes only numerical seed products, inverse weights, and label data. The next candidate is rebuilt from the same original source. The number of adaptive rounds therefore does not occur inside the symbolic depth or inside an iterated polynomial source-size recurrence.

For the general class statement, sparse substitution builds the leaf descriptions in $\mathscr C$. The upper expression is a $\mathscr C'_{k_0}$ description for an absolute $k_0$. To compile an output back into $\mathscr C$, process its fixed number of wrapper layers using the effective list-sum and list-product compilers. If one layer increases a total description bill $L$ by at most a fixed polynomial, a fixed number of layers gives a fixed composition of polynomial bounds. This remains polynomial. Thus the hypothesis concerns known PIT inputs in $\mathscr C'$, and the output sources belong to $\mathscr C$.

For formulas, concatenate the explicit trees; the fixed template has polynomial expanded size. For ordinary ABPs, sums use disjoint parallel copies, products use serial copies, and powers use the corresponding number of serial copies. Sparse edge substitutions are implemented by sums of monomial paths. An affine-edge label under radial substitution becomes a sparse degree-two polynomial, so short ordinary ABP gadgets suffice.

For constant-depth circuits, the displayed shallow construction adds an absolute number of layers to the original depth. Recursive binary formula syntax for derivatives or powers is not used to establish this depth bound. With the explicit shallow implementations, all queries and outputs have depth at most $\Delta+c$ for one absolute constant $c$. A numerical value of $c$ is not needed and is not claimed.

These statements do not preserve read-once order, obliviousness, a fixed ABP width, or noncommutative semantics. Such restrictions are different representation systems and are not conclusions of the concrete ABP corollary.

## 13 Characteristic and degree budgets

The characteristic bound has three distinct purposes: invertibility of the series denominators, enough distinct interpolation and witness nodes, and the dense line backend.

The cluster logarithms use indices at most $D$. Their exponentials use factorials of order at most $m\le D$. The critical-value polynomial uses elementary-symmetric reconstruction of degree $d-1$, and the final root recovery uses $e$ and factorials with indices at most $D$. The Newton sums through index $D^2$ use the logarithmic-derivative formula of Section 5, without division by those indices. Hence $p>D$ suffices for these algebraic denominators and for the relevant generic separability statements.

Interpolation needs a stronger bound. The following conservative budgets suffice; no optimization is intended.

| Construction before projection | Sufficient degree budget |
|---|---:|
| Critical Newton reciprocal through index $D^2$ | $2(D+1)^3$ total degree |
| Critical traces $q_k$ | $3(D+1)^3$ parameter degree |
| Critical finite exponential and reconstruction | $4(D+1)^4$ total degree |
| Cluster finite exponential | $D^3$ in $t$ and parameters and $D^2$ in $w$ |
| Complementary product test | $4(D+1)^3$ total degree |
| Final reversed binomial expression | $2(D+1)^4$ total degree |

For example, $V$ has total degree at most $2D$ in parameters and its generating variable. Its geometric reciprocal through index $j\le D^2$ has total degree at most $2(D+1)^3$. Combining a coefficient of $f^k$ with the corresponding Newton sum gives the displayed conservative trace bound; the final exponential has exponent at most $D$, yielding the quartic budget. The cluster estimates follow directly from Section 8. Reversal and the terminal binomial expression introduce only a further polynomial-degree bound, as displayed.

Thus every symbolic coefficient projection and coordinate witness can use nodes from

$$
\{0,1,\ldots,4(D+1)^4\}.
$$

In characteristic zero these are distinct. If $p>100(D+1)^8$, they are also distinct in the prime subfield. This bound dominates all the denominator requirements and the line backend condition $p>\delta(\delta-1)$. All constructions therefore run in the original field, without an extension-field PIT assumption or a field-descent argument.

The supplied bound $D$ is a semantic total-degree promise, as in the polynomial-in-size-and-degree formulation of the question. It is legitimate to interpolate a promised degree-$D$ polynomial even if its circuit has much larger formal degree because of cancellations. If no such promise is supplied, use a computable syntactic upper bound instead. Formula and affine-edge ABP degrees are bounded by their source sizes. For an explicit-wire circuit of fixed depth $\Delta$ and size $S$, a safe bound is $(S+1)^{\Delta+1}$. The positive-characteristic requirement must then apply to the bound actually used.

## 14 Arithmetic cost and binary cost

### Polynomial arithmetic resources

The critical-value construction, residue-weight tables, candidate sources, and all relevant dense tables have polynomial dimensions and polynomial degrees. The center search and each failed-test witness use polynomially many PIT calls. There are at most $r_0^2\le D^2$ inspected blocks and $r_0-1$ witness-line updates. Section 9 gives polynomial numerical work for each line, reusing the initial seed factorization.

All numerical inversions are either tested nonzero field-element inversions or computations of inverses of coprime numerical polynomials. There is no symbolic division by an unknown polynomial in the PIT queries. Dense extended gcd and subresultant algorithms operate on explicitly stored univariate coefficient tables. The numerical controller may be sequential; the constant-depth requirement applies to the symbolic queries and factor representations, not to the Turing machine or field-operation schedule that constructs them.

The factor outputs have polynomial description length by Section 12, so writing the complete output is included in the resource bound. These observations establish the algorithmic and size claims of Theorem 1.

### Rational coefficients

For a division-free formula over $\mathbb Q$, the bit lengths of exact values at polynomial-height rational points are polynomially bounded in the complete literal source length. A common denominator is obtained from the leaf denominators, and the logarithmic numerator bound is controlled by the sum of leaf heights and the expression-tree size.

For an acyclic affine-edge ABP, a path uses each edge at most once. The product of all edge-coefficient denominators is a common denominator for path-monomial coefficients. The logarithm of the number of paths and choices of edge monomials is polynomial in the graph encoding. Substitution of rational coordinates of height $H$ contributes at most the path length times $H$ to this bound. Dynamic programming therefore evaluates the source and constructs fixed-variable dense tables with polynomial numerator and denominator lengths.

A circuit of each fixed depth $\Delta$ has a formula unfolding of polynomial size in its complete explicit-wire input encoding. The preceding formula bound then controls exact evaluation and coefficient heights. The exponent of this polynomial may depend on the fixed depth; no depth-independent polynomial for unbounded input depth is asserted.

The initial numerical factorization has polynomial binary cost and returns polynomial-height factors by classical rational factorization algorithms. Products of the primary seeds have total degree at most $D$, so their coefficients retain polynomial height. The inverse $J_\ell$ can be obtained from a nonsingular Sylvester linear system of order $O(D^2)$. After clearing rational denominators, determinant bounds give polynomial numerator and denominator lengths for the solution. Fraction-free elimination realizes that bound algorithmically. The complete residue-weight and interpolation tables therefore have polynomial binary descriptions.

The numerical line stage can also be implemented with polynomial-height data. Dense subresultants have polynomial-size determinant representations. If a lifting implementation needs an explicit height guarantee, construct its jets through order $2D$ by the same finite cluster formulas, with the jet cutoff changed from $D$ to $2D$. These have polynomial expanded formula size and polynomial-height numerical leaves. The resulting jet coefficients therefore have polynomial height. Lecerf's recombination stage is linear algebra on these dense tables, followed by bounded-degree products and divisions. This supplies polynomial binary cost without presuming that an arbitrary recursive field-arithmetic implementation has small intermediate expressions.

All original variable-name bits are charged. A finite dictionary compacts the names occurring in the input; there are at most the input length many, and each original name has at most that length. Restoring names adds only a polynomial factor to the output bound. Adjoining unused variables preserves irreducibility of a polynomial over a field, so the compacted and original naming conventions give the same factorization statement.

Thus polynomially many polynomial-size calls to a fixed polynomial-time formula, ABP, or bounded-depth PIT machine give a complete polynomial binary-time algorithm over $\mathbb Q$.

### Fixed algebraic number fields

Fix $K=\mathbb Q(\alpha)$ in a power basis. Its dimension and multiplication structure constants are fixed. The tree, path, and fixed-depth unfolding bounds above become bounds on rational basis coordinates. Field inversion is linear algebra in fixed dimension, and the numerical coefficient systems remain polynomial in size and coordinate height. Classical deterministic factorization over number fields supplies the initial univariate routine [4]; dense factorization over number fields also has a classical polynomial-time treatment [5]. Consequently the same construction gives the binary-time conclusion of Corollary 3 for every fixed number field.

### Other field presentations

For an arbitrary abstract field, the proved bound counts field operations, equality tests, and the explicit univariate routine. A binary theorem additionally requires an effective encoding, paid field arithmetic, paid univariate factorization, and output-length bounds. For finite fields in standard encodings there is no coefficient-height growth, but polynomial-time deterministic univariate factoring in $\log|K|$ remains an explicit condition. A polynomial-in-characteristic algorithm must not be relabeled polynomial in its logarithm.

## 15 Proof of the main theorem and relation to the open question

The constructions establish Theorem 1 by the following composition. Sections 3–5 compute the actual monic source and a regular center using known white-box queries. Section 6 performs the initial univariate factorization and obtains all numerical labels and exponents. Sections 7–8 construct every candidate from the original source, with proved semantics and specialization behavior. Section 9 implements every dense witness-line factorization from the already known seeds. Section 10 proves safe strict progress and polynomial termination. Section 11 proves complete irreducibility, multiplicities, distinctness and exact restoration. Sections 12–14 establish uniform construction, representation membership, depth, and resource bounds. No unknown global factor, correct partition, irreducibility-preserving projection, symbolic factorizer, or factor source has been made an algorithm input. ∎

The explicit effective-robustness conditions give the constructive interpretation of the robust class in [1, Section 5.7]. Every query is a bounded-depth wrapper over known $\mathscr C$ sources. Thus white-box PIT for the stated wrapper class suffices, and the output compiles back into $\mathscr C$. This supplies the claimed affirmative answer to the first question in [1, Section 7], in its characteristic-zero and sufficiently-large-characteristic framework with the numerical assumption retained from Remark 5.3.

For formulas and ordinary ABPs, the wrappers compile into the same respective representation with polynomial overhead. For the constant-depth family, the conclusion is the additive-depth statement of Corollary 2. Over $\mathbb Q$ and fixed number fields the numerical hypothesis is discharged, leaving the specified model's PIT assumption as the only algorithmic hypothesis.

The statement does not resolve unconditional PIT, $P$ versus $NP$, or $VP$ versus $VNP$. It does not extend the result to small characteristic, unrestricted field encodings, or an oracle restricted to exactly the input depth. Small-characteristic extraction of a factor from its Frobenius power is the separate issue discussed in [1, Appendix A and the second question of Section 7]. These distinctions are part of the theorem's scope, not omitted steps in its proof.

## 16 A worked nonlinear example

Work over $\mathbb Q$ and take

$$
f(x,y)=y^2-y-x.
$$

The center $a=0$ is regular and its fiber is $y(y-1)$. Start with the two singleton labels $a_1=y$ and $a_2=y-1$. Through $t$-order $D=2$, the two decoded candidates are

$$
G_1=y+x-x^2,\qquad
G_2=y-1-x+x^2.
$$

Their product test is

$$
G_1G_2-f=2x^3-x^4,
$$

which is nonzero at $x=1$. The corresponding line polynomial is

$$
f(t,y)=y^2-y-t.
$$

It is irreducible in $\mathbb Q[t,y]$: it is, up to a nonzero constant, $t-(y^2-y)$, whose quotient ring is the domain $\mathbb Q[y]$. Its one line factor therefore joins both fiber labels. The full-seed decoder returns $f$, and the algorithm terminates with this irreducible factor of multiplicity one.

This example illustrates why the decoder is allowed to construct truncated branches that are not global factors, why the product test detects them, and how a witness line forces the required join. It is an illustration of the proved lemmas, not a substitute for them.

## References and attribution

[1] Somnath Bhattacharjee, Mrinal Kumar, Shanthanu S. Rai, Varun Ramanathan, Ramprasad Saptharishi, and Shubhangi Saraf. **Closure under factorization from a result of Furstenberg.** arXiv:2506.23214v1, 2025. The target is Section 7, first question, read with Section 5.7 and Remark 5.3. [Paper](https://arxiv.org/html/2506.23214v1)

[2] Amit Sinhababu and Thomas Thierauf. **Factorization of Polynomials Given by Arithmetic Branching Programs.** *Computational Complexity* 30, article 15, 2021. Theorem 5.1 and the explicit white-box discussion on pp. 38–39 establish the earlier ABP result. [Paper](https://d-nb.info/1251198279/34) · [DOI](https://doi.org/10.1007/s00037-021-00215-0)

[3] Grégoire Lecerf. **Improved Dense Multivariate Polynomial Factorization Algorithms.** *Journal of Symbolic Computation* 42(4), 477–494, 2007. We use the revised version dated 18 January 2007, Hypotheses C and H, Algorithm 1 and Proposition 4. This version includes corrections to earlier lifting and recombination papers. [Author's manuscript](https://www.lix.polytechnique.fr/~lecerf/publications/Lecerf%3A2005%3Aidmpfa.pdf) · [DOI](https://doi.org/10.1016/j.jsc.2007.01.003)

[4] Arjen K. Lenstra. **Factoring polynomials over algebraic number fields.** EUROCAL 1983; earlier report version, 1982. Supplies deterministic polynomial-time univariate factorization over number fields. [Primary manuscript](https://ir.cwi.nl/pub/2541/2541D.pdf)

[5] Arjen K. Lenstra. **Factoring Multivariate Polynomials over Algebraic Number Fields.** *SIAM Journal on Computing*, 1987. [Paper and DOI](https://doi.org/10.1137/0216040)

[6] Swastik Kopparty, Shubhangi Saraf, and Amir Shpilka. **Equivalence of Polynomial Identity Testing and Deterministic Multivariate Polynomial Factorization.** *Computational Complexity* 24, 295–331, 2015. The general-circuit predecessor to the question addressed here. [Author's manuscript](https://www.math.utoronto.ca/swastik/pit-factor.pdf)

The proof uses classical coprime Hensel lifting, finite logarithm and exponential identities, Newton sums, polynomial-ring unique factorization, and deterministic dense numerical factorization. The noniterative reconstruction viewpoint is related to the factor-closure work in [1]; the numerical lifting and recombination backend is credited to [3]. The proposed construction here combines the explicit residue decoder with the witness-line partition selector and the uniform representation and field analysis given above. The ABP implication is credited to [2]. This manuscript was developed with AI assistance and is offered for independent mathematical checking before formalization and publication as a validated result.
