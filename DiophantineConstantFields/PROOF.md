# Diophantine Definitions of Constants by Rational Specialization

## Scope and arithmetic input

Assume there is a polynomial $P(z,\mathbf w)$ with integer coefficients such that
$$
z\in\mathbb Z\ \Longleftrightarrow\
\exists\mathbf w\in\mathbb Q^m\ P(z,\mathbf w)=0
\qquad(z\in\mathbb Q).
$$
This is the claim of [Glazer's manuscript](https://github.com/elliotglazer/diophantine-z-q). All conclusions below that use this premise are conditional on it.

The Matiyasevich–Robinson–Davis–Putnam theorem and $P$ give a Diophantine definition over $\mathbb Q$ of every computably enumerable relation on rational tuples. Encode each rational input $q_i$ by an integer numerator $a_i$ and positive integer denominator $b_i$. The relation on integer tuples of codes whose decoded tuple belongs to the given relation is computably enumerable. Use MRDP on the codes and $P$ to enforce the integer restrictions on both the codes and the MRDP witnesses. Impose $b_iq_i=a_i$ and $b_i c_i=1$, where the latter is a polynomial equation in a fresh variable. The equations have rational solutions exactly for inputs in the original relation. Conversely, rational solutions to a fixed finite polynomial system can be enumerated. See [Pasten, Proposition 4.12 and Theorem 4.6](https://arxiv.org/pdf/2012.14054#page=17) for the listability and catalogue framework.

## 1. Pheidas's constants question

**Theorem.** The same parameter-free polynomial $P$ defines the constant copy of $\mathbb Z$ in every purely transcendental field extension of $\mathbb Q$. Consequently the constant copy of $\mathbb Q$ has one parameter-free Diophantine definition uniform over all these extensions.

For one indeterminate $t$, suppose $P(f(t),\mathbf g(t))=0$ in $\mathbb Q(t)$. Outside the finitely many poles of the entries, specializing $t$ to a rational $a$ gives a solution over $\mathbb Q$, so $f(a)$ is an integer. On any nonempty real interval free of those poles, rational arguments are dense. Since $\mathbb Z$ is closed in $\mathbb R$, continuity forces $f$ to be integer valued throughout the interval. Its image is connected, so it is a single integer. A rational function that agrees with a constant on an interval equals that constant in the function field. Conversely, each integer has a tuple of constant witnesses.

In several indeterminates choose a real open ball on which all finitely many denominator polynomials are nonzero. Their product is nonzero and cannot vanish on all of real affine space. The rational points of the ball are dense and every specialization there is valid. The same continuity argument makes $f$ constant on the ball, so the numerator of $f-c$ is the zero polynomial. In arbitrary transcendence degree, any solution involves only finitely many indeterminates and reduces to this argument.

Now define a constant $x$ by
$$
\exists a,b,c,\mathbf u,\mathbf v\quad
 P(a,\mathbf u)=P(b,\mathbf v)=0,\qquad bx=a,\qquad bc=1.
$$
In every field at issue this forces $x$ to be a quotient of constant integers with nonzero denominator, and every rational number has such witnesses. Over these formally real fields the equations can also be combined as a sum of squares. The formula uses only integer coefficients and no name for the indeterminate.

This answers [Pheidas's Question 4 in the 2013 AIM problem list](https://aimath.org/pastworkshops/definabilityinntproblems.pdf#page=1) in full under the stated premise. [Garcia-Fritz and Pasten, Theorems 1.3 and 8.2](https://arxiv.org/html/2208.11616#S8.SS2), gave a positive answer under two conjectures on elliptic surfaces. The specialization argument uses the integrality premise above in place of those conjectures. A targeted search did not locate this exact argument in the cited papers or Glazer's public summary. Publication priority remains unverified.

## 2. Function fields of varieties with Zariski-dense rational points

**Theorem.** Let $X$ be an integral variety of finite type over $\mathbb Q$, with $X(\mathbb Q)$ Zariski dense. Both $\mathbb Z$ and $\mathbb Q$ are Diophantine in $\mathbb Q(X)$ by formulas with integer coefficients. More generally, every computably enumerable relation on constant rational tuples is Diophantine in $\mathbb Q(X)$.

Take a nonempty affine open with coordinate ring $A$, an integral finitely generated $\mathbb Q$-algebra, and put $F=\operatorname{Frac}(A)$. We first construct a computable $S\subseteq\mathbb Z_{>0}$ with $S-S=\mathbb Z$ and the following property. For every $f\in F\setminus\mathbb Q$ and every nonempty principal open $U$ of this affine chart on which $f$ is regular, some $x\in U(\mathbb Q)$ satisfies $f(x)\notin S$.

Enumerate all triples $(a,b,g)$ in $A$ with $b,g\ne 0$ and $a/b\notin\mathbb Q$, using $f=a/b$ and $U=D(bg)$. This covers every needed $f$ and every possible additional denominator $g$. The tests are effective. Present $A$ as a polynomial ring modulo a fixed prime ideal and compute normal forms for the given representatives using a Gröbner basis. Nonzeroness is a normal-form test and $a/b\in\mathbb Q$ is proportionality of the two normal forms over $\mathbb Q$. If $F=\mathbb Q$, the theorem is already the arithmetic input. Otherwise this enumeration is infinite.

At stage $n\ge1$ consider the next triple. The image $f(U(\mathbb Q))$ is infinite. Indeed, $U(\mathbb Q)$ is Zariski dense and a nonconstant function has proper level sets, so a finite union of level sets cannot cover those points. Search the computable enumeration of rational points of $U$ until a value is found outside the finite part of $S$ already chosen. Permanently reserve this value against future inclusion. Nonintegral values are automatically excluded. Then choose a positive integer $h$ larger than every previously added integer such that both $h$ and $h+n$ avoid the finitely many reserved values. Add these two integers to $S$. The search terminates at every stage. All positive integers are differences, hence all integers are differences by reversing the order or using a point twice. The added pairs are above the preceding maximum, so membership in $S$ is computable by running stages past the candidate. Each reserved value is outside the final set.

Let $D_S(z,\mathbf y)=0$ denote a finite polynomial system over $\mathbb Q$ defining $S$ over $\mathbb Q$ by the arithmetic input. Clear denominators in its coefficients. Suppose $D_S(f,\mathbf y)=0$ in $F$. Represent $f=a/b$ and take a product $g\ne 0$ of the denominators of the witness entries. Every rational point in $D(bg)$ specializes the system to a solution over $\mathbb Q$. Thus $f$ takes values in $S$ on all those points. If $f\notin\mathbb Q$ this contradicts the reserved value for $(a,b,g)$. If $f\in\mathbb Q$, specialize at one point to get $f\in S$. Conversely $f\in S$ has constant witnesses. Thus the system defines exactly $S$ in $F$. Take differences to define $\mathbb Z$, then quotients to define $\mathbb Q$.

For a computably enumerable relation on rational tuples, use its defining polynomial system over $\mathbb Q$ and require each input to satisfy the constant-field definition. Solutions over $F$ with constant inputs specialize at a rational point of a nonempty affine open, giving solutions over $\mathbb Q$. The converse uses constant witnesses. This proves the claimed extension, with the formula for constants allowed to depend on $X$.

The definition can be constructed effectively from an affine presentation with prime defining ideal and the fixed polynomial $P$, under the density promise. The program constructing $S$ uses that presentation, and the MRDP compiler turns the program into equations. This effectiveness does not require a decision procedure for the density promise.

## 3. Consequences for four of Pasten's conjectures

Write $\Lambda$ for the left-computably-enumerable real numbers. Such a real $\alpha$ is characterized by computable enumerability of its lower rational cut $\{q\in\mathbb Q:q<\alpha\}$. Write $D$ for the real numbers whose lower rational cut is Diophantine over $\mathbb Q$.

The arithmetic input proves the exact equality $D=\Lambda$. Every Diophantine cut is enumerable by listing rational witnesses. Conversely, every enumerable cut is Diophantine by MRDP and the assumed integer definition. This refutes [Pasten's Conjecture 5.16](https://arxiv.org/pdf/2012.14054#page=25).

For completeness, let $H\subseteq\mathbb N$ be the halting set and put $\alpha=\sum_{e\in H}4^{-(e+1)}$. Finite partial sums obtained by enumerating $H$ increase to $\alpha$, so the lower cut is enumerable. The number is noncomputable. Having recovered the earlier digits, the remaining value is at most $4^{-(e+1)}/3$ if $e\notin H$, and at least $4^{-(e+1)}$ if $e\in H$. A sufficiently accurate approximation to $\alpha$ therefore decides each digit. Every real algebraic number is computable by root isolation. Thus $\alpha\in D$ is transcendental, refuting Pasten's algebraicity Conjecture 5.13. Moreover, $-\alpha\notin\Lambda$, since enumerating both lower cuts would produce upper and lower rational bounds of arbitrarily small width and make $\alpha$ computable. Hence $D$ is not closed under negation, refuting the field Conjecture 5.14. These implications fit Pasten's Proposition 5.17 and are consequences of the arithmetic premise.

For each fixed arity $r$, let $U_r(e,\mathbf q)$ say that $e$ is a natural-number program index and the indicated program enumerates the code of $\mathbf q\in\mathbb Q^r$. This is a single computably enumerable relation, so it has one finite Diophantine definition. Fixing $e$ to an integer gives every computably enumerable $r$-ary relation, hence every Diophantine one. Therefore the number of existential variables can be bounded in terms of $r$, independent of the set. The unary bound refutes the universal global-field claim of [Pasten's Conjecture 5.20](https://arxiv.org/pdf/2012.14054#page=25) at $\mathbb Q$. Pasten's Theorem 4.6 already supplies the abstract implication from the DPRM property to this catalogue, and Proposition 5.23 already gives the corresponding obstruction to an integer definition.

## 4. Pheidas's denominator-support question over the rationals

For any computable set of rational primes $T$, there is an existential formula over $\mathbb Q$ for the relation
$$
\{(a,b)\in\mathbb Q^2:\ \forall p\in T,\ v_p(a)<0\ \Longrightarrow\ v_p(b)<0\}.
$$
Write $a,b$ in reduced form with positive denominators, using denominator $1$ for zero. Factor the denominator of $a$. For every prime divisor belonging to $T$, check that it divides the denominator of $b$. This terminates, so the relation is computable and the arithmetic input gives its Diophantine definition. Taking $T$ to be the primes congruent to $1$ modulo $4$ answers the $\mathbb Q$ instance of [Pheidas's Question 2](https://aimath.org/pastworkshops/definabilityinntproblems.pdf#page=1). The general question in that list ranges over number fields.
