# Ordinary DNF and parity tests for canonically labelled 2-groups

**Theorem.** For $n=2^{3r}$ there is a promise class of valid Cayley tables of groups of order $n$, nilpotency class two and exponent four, with the following property. Isomorphism on pairs from the class has ordinary DNF term complexity
$$
2^{(2/27)(\log_2 n)^3+O((\log n)^2)}.
$$
For the same promise, an OR of conjunctions of affine Boolean tests on input table bits uses at most $2^{5r^2}$ conjunctions, each with a polynomial number of tests in $r$. Ordinary depth-3 OR–AND–OR circuits of size $2^{O(r^2)}$ also suffice on that promise. The ordinary DNF lower bound applies to isomorphism on arbitrary pairs of valid Cayley tables of order $n$.

## The common promise

Set $V=\mathbb F_2^{2r}$ and $W=\mathbb F_2^r$. Each parameter $T$ is an array of vectors $t_{ij}\in W$ for $1\le i\le j\le 2r$. Define the bilinear map
$$
c_T(v,v')=\sum_{i\le j}v_i v'_j t_{ij}.
$$
Use the binary labels $(v,w)\in V\oplus W$ on a group $G_T$, with product
$$
(v,w)(v',w')=(v+v',w+w'+c_T(v,v')).
$$
Bilinearity gives associativity, identity $(0,0)$, and inverse $(v,w+c_T(v,v))$. The square is $(0,q_T(v))$, where $q_T(v)=c_T(v,v)$. The commutator is $(0,\beta_T(v,v'))$, where $\beta_T(v,v')=c_T(v,v')+c_T(v',v)$. Impose that the radical of $\beta_T$ is zero and its values span $W$. Then the center and derived group both equal $0\oplus W$. The group has class exactly two and exponent exactly four, since $\beta_T$ is nonzero. Cayley-table labels are part of this promise.

The parameter count is $2^M$ for $M=r\binom{2r+1}{2}=2r^3+r^2$. At least half satisfy the promise for all sufficiently large $r$. For any nonzero $v$, the condition $\beta_T(v,-)=0$ imposes $r(2r-1)$ independent linear conditions on off-diagonal coefficients. Extend $v$ to a basis of $V$ and note that every $W$-valued alternating form is allowed. The chance of a nonzero radical is at most $(2^{2r}-1)2^{-r(2r-1)}$. Failure to span $W$ requires a nonzero functional of $W^\ast$ to kill all $\binom{2r}{2}$ independent off-diagonal coefficient vectors. Its chance is at most $(2^r-1)2^{-\binom{2r}{2}}$. The two bounds sum to less than $1/2$ for all sufficiently large $r$.

## Exhausting the possible actions on the center and quotient

Every isomorphism $G_T\to G_S$ induces some $A\in\operatorname{GL}(V)$ on the quotient by the center and $B\in\operatorname{GL}(W)$ on the center. It preserves squares, so
$$
q_S(Av)=Bq_T(v)\qquad(v\in V).
$$

Conversely, fix any such $A,B$ satisfying this equality. The bilinear map $d(v,v')=c_S(Av,Av')+Bc_T(v,v')$ has zero diagonal. In characteristic two this makes $d$ symmetric. Its quadratic correction
$$
f(v)=\sum_{i<j}v_i v_j d(e_i,e_j)
$$
satisfies $f(v+v')+f(v)+f(v')=d(v,v')$. Substitution into the two multiplication laws verifies that $(v,w)\mapsto(Av,Bw+f(v))$ is an isomorphism. The map is bijective by invertibility of $A$ and $B$. Thus the possible $(A,B)$ are an exhaustive family of cases, and each case has an exact test.

The coefficients $t_{ij}$ are literal bits of the input table, obtained by taking the $W$ component of the product of $(e_i,0)$ and $(e_j,0)$ for $i\le j$. The map $q_T$ determines these coefficients by evaluation on $e_i$ and $e_i+e_j$. For fixed $(A,B)$ the required equality of the two quadratic maps is an affine test in their coefficients. One can check it on basis elements and sums of two distinct basis elements because a quadratic map on $V$ is determined by these evaluations. Each resulting coordinate equation is a parity of input table bits. The number of cases is
$$
|\operatorname{GL}(V)|\,|\operatorname{GL}(W)|\le 2^{(2r)^2+r^2}=2^{5r^2}.
$$
The disjunction accepts exactly when one case succeeds. If every case fails, no isomorphism exists. The parity tests can use bits from both tables. In fact $q_T(v)$ is read directly from the $W$-coordinates of the table entry $(v,0)(v,0)$. In each equality $q_S(Av)=Bq_T(v)$, a coordinate test is a parity of at most $r+1$ bits from the two tables. Such a parity condition is expressible as a CNF with at most $2^r$ clauses, one for each forbidden assignment. Merging those clauses into the conjunction for the case gives the claimed ordinary depth-3 circuit, with bottom fan-in at most $r+1$.

## Why ordinary DNF has a different size

Every ordinary conjunction of literals in the two tables separates as a condition on the first table and a condition on the second. It therefore accepts a rectangle of table pairs. Within the promise, a rectangle that accepts an isomorphic pair can only accept pairs in one isomorphism class. Accepting $(T,T)$ and $(S,S)$ for two nonisomorphic groups would make it accept $(T,S)$ as well.

For any $T$ and fixed $A,B$, the equation in the preceding section determines at most one $S$, since $A$ is invertible and $q_S$ determines the coefficients of $S$. Thus one class has at most $2^{5r^2}$ parameters. The at least $2^{M-1}$ promised parameters give at least $2^{M-1-5r^2}$ classes, hence as many DNF terms. For the upper bound on this particular promise, enumerate every accepted ordered pair of parameters, at most $2^{M+5r^2}$ pairs. Each pair is represented by one conjunction fixing its $2M$ parameter bits. Thus the base-two logarithm of ordinary DNF term complexity is $M+O(r^2)$. Replacing $r$ with $(\log_2 n)/3$ gives the theorem.

## Exact scope and sources

- The lower bound counts ordinary Boolean conjunctions, which separate across the two input tables. The parity upper bound depends on the canonical labels and may compare bits from opposite sides of the input. Both bounds are for this one valid-table promise. The lower bound extends to the larger valid-table promise by restriction.
- Grochow–Kardeş–Levet Section 4.1 gives a stronger exponential lower bound for the *total* problem using invalid inputs. This proof gives the displayed bound under a validity promise. Their Question 7.1 asks about CNFs and is a separate problem. The paper already gives the odd-characteristic Baer-parameter approach and records the Higman–Sims isomorphism-type count. The sharp ordinary-DNF exponent and the explicit same-promise parity upper bound follow together here.
- The classification of special 2-groups by quadratic maps is established literature. The derivation here verifies the exact gate interface directly. The literature check did not locate the same circuit comparison. This proof is informal.

[Grochow–Kardeş–Levet, Group Isomorphism and the Polylogarithmic-Time Hierarchy, §§4.1–4.3 and 7](https://arxiv.org/html/2608.26257v2) · [Kaur–Kulshrestha, Strongly Real Special 2-Groups](https://arxiv.org/abs/1210.3790)
