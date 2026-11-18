# VNP-complete canonical Ideal Proof System certificates

The specific canonical construction in Grochow–Pitassi Theorem 1.2 gives VNP-complete certificates for a family of polynomial-size unsatisfiable 3-CNFs over every field with more than two elements. Over $\mathbb F_2$, no canonical certificate family is VNP-hard under p-projections. This gives a field-by-field answer to the VNP-completeness clause of their Open Question 7.8. The more general assertion that every p-projection degree in VNP occurs is false over every field. [Grochow–Pitassi, Lemma 4.2 and Question 7.8](https://www.cs.toronto.edu/~toni/Papers/jacm-gp.pdf#page=42)

## The exact certificate used by the paper

For an ordered unsatisfiable CNF $K_1\wedge\cdots\wedge K_m$ on Boolean variables with formal counterparts $X_1,\ldots,X_N$, let $A_i$ consist of assignments that satisfy all clauses before $K_i$ and falsify $K_i$. Let $V_i$ be the set of variables appearing in $K_i$. Write $b(0,X)=1-X$ and $b(1,X)=X$. In the proof of Lemma 4.2, equation (5) is the following polynomial with chapter-specific placeholder notation changed to $z_i$:

$$
C(X,z)=\sum_{i=1}^m z_i\sum_{a\in A_i}\prod_{j\notin V_i} b(a_j,X_j).
$$

Indeed, substituting the clause-falsity polynomial for $z_i$ restores the omitted factors for $j\in V_i$. Summation over the first-falsified-clause partition gives $\sum_{a\in\{0,1\}^N}\prod_j b(a_j,X_j)=1$. The paper proves that this precise family of certificates is in constant-free VNP for polynomial-size ordered CNFs. We use its actual polynomial, with clause order fixed by the construction below. [Equation (5) and proof of Lemma 4.2](https://www.cs.toronto.edu/~toni/Papers/jacm-gp.pdf#page=27)

## Any Boolean acceptance polynomial is a projection of a canonical certificate

Let $R_n$ be a family of Boolean predicates with polynomial-size circuits, on $r_n=\operatorname{poly}(n)$ bits. Fix $d_n\le r_n$. The associated polynomial is

$$
P_n(x)=\sum_{\substack{u\in\{0,1\}^{r_n}\\R_n(u)=1}}\prod_{j=1}^{d_n}x_j^{u_j}.
$$

**Claim.** Over a field with more than two elements, $P$ is an ordinary p-projection of the canonical certificate family for an explicit polynomial-size ordered family of unsatisfiable CNFs. The CNFs have width at most three and can be generated in polynomial time from the Boolean predicate circuits. A version with exactly three distinct variables per clause is given below.

Write the Boolean circuit using fan-in-two gates, then translate it to a CNF with a variable per gate. Enforce the truth table of each gate and require output one by a unit clause. Thus each accepted input $u$ extends uniquely to an assignment to the input and gate variables satisfying these clauses. Rejected inputs have no extension. Call these input and gate variables the control variables. Let their number be $M_n$.

For each control variable $p$, introduce a new variable $p'$ and enforce $p'=p$ with two clauses. For each of the first $d_n$ input bits $u_j$, introduce a variable $w_j$ and impose the single implication $u_j\Rightarrow w_j$. Append a fresh unit clause $(s)$ after every one of these constraints, then append $(\neg s)$. This makes the whole CNF unsatisfiable. The assignments whose first false clause is $(s)$ are exactly the accepted inputs with their unique controls and copies, the independent choices of each $w_j$ permitted by the implication, and $s=0$.

Choose $\lambda\in F\setminus\{0,1\}$ and put $\delta=\lambda(1-\lambda)\ne0$. In the canonical certificate, replace the formal variable for each $p$ by $\lambda$ and that for each $p'$ by $1-\lambda$. Replace the formal variable for $w_j$ by $x_j$. Set every clause placeholder to zero except the one for $(s)$, which is set to $\delta^{-M_n}$. The formal variable for $s$ can be set to zero. It is omitted in the surviving summand of the certificate.

Every equal pair $p,p'$ contributes exactly $\delta$, for either Boolean value of $p$. Their product cancels the placeholder constant. If $u_j=1$ the implication forces $w_j=1$ and gives factor $x_j$. If $u_j=0$ both $w_j$ values can be summed independently, giving $(1-x_j)+x_j=1$. Thus the remaining terms are precisely the monomials in $P_n$, each accepted input contributing once. The substitution uses a field constant or an input variable at each formal variable, exactly as an ordinary p-projection requires.

If exactly three distinct variables per clause are desired, replace a two-literal prefix clause $A\vee B$ by $(A\vee B\vee t)\wedge(A\vee B\vee\neg t)$ with a fresh $t$. Replace a unit prefix clause by the four clauses using all signs on two fresh padding variables. These padding variables are unconstrained when the underlying clause is true. Assign their formal variables any fixed field constants, so each independent sum of their two weights is one. A clause with repeated literals can first be simplified. Replace the final contradictory units by all eight clauses on three fresh variables, each clause excluding just one of the eight assignments. Order the clause excluding $(0,0,0)$ first among those eight and use it as the distinguished clause. It fixes its three variables on failure and omits their factors just as before. These changes preserve the projection.

## Application to VNP-completeness

For the Hamiltonian-cycle polynomial, let $u$ have one bit per possible directed arc of the complete loopless graph on $n$ vertices. Take all these bits as the features. The predicate tests that the arcs selected by $u$ are one directed spanning cycle. It can be computed by a polynomial-size Boolean circuit, by checking one incoming and one outgoing arc per vertex and following successors for exactly $n$ steps. There is exactly one accepted bit vector for each directed Hamiltonian cycle. So the projected polynomial is exactly the Hamiltonian-cycle polynomial, which is VNP-complete under p-projections over every field. The canonical certificate is already in VNP by Lemma 4.2. This proves VNP-completeness of the certificate family over all fields with more than two elements. The same argument applied to bipartite perfect-matching bit vectors gives the permanent as a projection, without requiring it to be VNP-complete in characteristic two. [Valiant's completeness theorem as cited in Grochow, §1](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf#page=2)

## The general p-degree assertion fails

Every canonical certificate above is a nonzero polynomial homogeneous of degree one in the clause placeholders. It vanishes when all those placeholders are zero. Consider the nonconstant VP family with the same polynomial $x^2$ at every index. A p-projection of $x^2$ is a constant or the square of a single input variable. No nonzero polynomial of the certificate form can be either. A square in an ordinary input is independent of the placeholders. A square in one placeholder has degree two in them. Thus no canonical certificate family has the p-projection degree of this family, irrespective of characteristic. This disproves the every-p-degree generalization in Question 7.8. The every-c-degree generalization remains open.

The same failure includes p-degrees of VNP-c-complete families, over every infinite field of characteristic different from two. Let $F_n$ be the Hamiltonian-cycle polynomial and set $H_n(x)=F_n(x_1^2,\ldots,x_m^2)$. The family is in VNP. Every p-projection of $H_n$ has even exponents in all its variables, so none equals a canonical certificate. To see that $F\le_c H$, let $d=\deg F_n$ and use the polynomial $R_i(t)$ of degree at most $d$ that agrees with the square root of $1+t(x_i-1)$ to order $d$ in $t$. Such truncated roots can be computed coefficient by coefficient with a constant factor of $1/2$. Then $H_n(R_1(t),\ldots,R_m(t))$ agrees to order $d$ with $F_n(1+t(x-1))$. Its degree in $t$ is at most $2d^2$, so polynomially many evaluations at field constants recover the first $d+1$ coefficients. Their sum at $t=1$ is $F_n(x)$. This establishes c-hardness and gives a further p-degree omitted by all canonical certificates.

## No p-projection completeness over the two-element field

On Boolean input $X$ each nonzero summand must come from an assignment agreeing with $X$ outside its first false clause. Such an assignment can disagree on that clause's variables, so the certificate evaluation is not necessarily the placeholder of the first clause false on $X$. We use the fact that a fixed clause determines uniquely the Boolean values on its own variables that falsify it, unless it is tautological, in which case its summand is zero.

Thus for a nontautological clause $K_i$ there is exactly one candidate assignment $a^{(i)}(X)$ that can contribute: copy $X$ outside $V_i$ and set the variables in $V_i$ to their falsifying values. Its contribution coefficient is one exactly when $a^{(i)}(X)$ satisfies all earlier clauses. Each of those satisfaction tests is an OR of literals evaluated at $X$ or at constants. It follows that each individual placeholder coefficient evaluates to a polynomial-size Boolean CNF, even when the original CNF has large clauses.

Over $\mathbb F_2$ the full certificate is the parity of its active placeholder values. Its evaluation on the Boolean cube is therefore in nonuniform $\mathsf{AC}^0[2]$: use a parity gate above the polynomially many terms consisting of a placeholder AND its coefficient's CNF. Replacing any input by another input or a constant preserves these constant-depth polynomial-size bounds.

The Boolean function $\mathrm{MOD}_3$ has a polynomial-size arithmetic representation over $\mathbb F_2$. With residue indices $r\in\mathbb Z/3$, set $P_{0,0}=1$, $P_{0,1}=P_{0,2}=0$, and use

$$
P_{i,r}=(1-x_i)P_{i-1,r}+x_i P_{i-1,r-1}.
$$

The polynomial $P_{n,0}$ has degree at most $n$ and arithmetic circuit size $O(n)$. On Boolean input it is the indicator that the number of ones is divisible by three. Thus this family is in VP, hence in VNP. A p-projection from a canonical certificate family would give polynomial-size constant-depth circuits with parity gates for $\mathrm{MOD}_3$. Smolensky's lower bound rules this out. This proves the negative case over $\mathbb F_2$, even for hardness under p-projections for VP. [Smolensky, *Algebraic Methods in the Theory of Lower Bounds for Boolean Circuit Complexity*](https://doi.org/10.1145/28395.28404)
