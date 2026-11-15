# Exponential sparse Polynomial Calculus lower bounds for tensor nonisomorphism in positive characteristic

This informal proof uses Søren Riis's rectangle degree obstruction (Lemma 14.1 of his November 2026 preprint). It addresses the sparse-size lower-bound part of Open Question 7.2 of Galesi, Grochow, Pitassi and She, and the positive-characteristic lower-bound parts of Open Question 7.3 for matrix conjugacy and congruence. Sparse size counts nonzero monomials across all proof lines.

**Theorem.** Fix a prime $p$. Over every field of characteristic $p$, for every sufficiently large $n$ there are explicit $n\times n\times n$ nonisomorphic tensors with entries in $\{0,1\}$ whose ordinary Polynomial Calculus (PC) refutations require degree $\Omega_p(n)$ and sparse size $2^{\Omega_p(n)}$. The equations are the cubic action equations and the quadratic inverse equations. The same bounds hold when field equations are added over any fixed finite field. There are explicit $n\times n$ matrix nonconjugacy, noncongruence and inequivalence instances with the same bounds.

## 1. Turning the rectangular degree bound into a sparse-size bound

Write $B_{r,s}$ for the rectangular bijection encoding in variables $x_{ij}$, with $i\in[r]$ and $j\in[s]$. The axioms are row and column sums minus 1, Boolean axioms $x_{ij}^2-x_{ij}$, and collision products $x_{ij}x_{ik}$ for $j\ne k$ and $x_{ij}x_{\ell j}$ for $i\ne\ell$. Transposing variables exchanges $B_{r,s}$ and $B_{s,r}$. Let $q=p^a\ge 3$, and take $r=4q$, $s=3q$. Riis's Lemma 14.1 states that $B_{u,v}$ has no ordinary PC refutation of degree at most $D$ if $1\le u\le v$, $2D\le u$, $D<q$ and $q\mid v-u$. In particular $B_{3q,2q}$, after transpose, has no refutation of degree at most $q-1$. The same holds for $B_{4q,3q}$.

### A random restriction

Choose uniformly $q$ distinct rows of the $4q\times3q$ rectangle, then assign them injectively and uniformly to $q$ columns. Set the matched variables to $1$, every other variable incident with any matched row or column to $0$, and retain the variables of the remaining $3q\times2q$ rectangle. Each original row or column axiom maps to zero or its corresponding axiom in the remaining rectangle. The same holds for Boolean and collision axioms.

In the remaining polynomial ring, take the quotient by Boolean and collision axioms alone. Its monomial basis consists of squarefree products indexed by partial matchings, including the empty product. Indeed every monomial either contains a collision and vanishes, or reduces to the squarefree monomial on its support. These reductions define a multiplicative normal form by taking unions of supports and discarding collisions. Linear extension gives a ring homomorphism to the algebra with that basis, verifying uniqueness of normal form.

For any original partial matching $E$ of $k$ edges, its product can survive only if every selected row of $E$ is assigned to the prescribed column of its edge. Let $K$ be the number of those selected rows. Conditional on the selected rows, the probability of this necessary event is $(3q)_K^{-1}$, where $(b)_K=b(b-1)\cdots(b-K+1)$. Since $K\le q$, this is at most $a_0^K$ for $a_0=(2q+1)^{-1}$. Let $I_i$ be the indicator that the $i$th row of $E$ is unselected. Then

$$
\mathbb E[a_0^K]
=\mathbb E \prod_{i=1}^k\bigl(a_0+(1-a_0)I_i\bigr)
\le \bigl(a_0+(1-a_0)\tfrac34\bigr)^k
\le (5/6)^k.
$$

For the first inequality, expand the product with nonnegative coefficients. For any $j$ distinct rows, the probability that all are unselected is $(3q)_j/(4q)_j\le (3/4)^j$, with probability zero for $j>3q$. The last inequality uses $a_0\le 1/3$. Restriction and normalization never increase the support size of a surviving monomial.

### Simulating bounded-degree quotient lines

Suppose a PC proof of $B_{4q,3q}$ has fewer than $(6/5)^{q-1}$ nonzero monomial occurrences. A collision monomial is zero in the quotient after every restriction. Apply the survival bound to every other monomial whose support has at least $q-1$ edges. The union bound gives a restriction killing all of them. Restrict every proof line and pass to normal form. The resulting quotient proof derives $1$, and all of its lines have matching degree at most $q-2$.

The quotient proof yields an ordinary PC proof of $B_{3q,2q}$ of degree at most $q-1$. Represent each quotient line by its normal form. Initial nonzero lines are unchanged row or column axioms of the remaining rectangle. Linear combinations preserve normal form. For multiplication by a retained variable $x$, first derive $xP$, where $P$ is the preceding ordinary line of degree at most $q-2$. For each term of $xP$ with a collision, subtract the corresponding monomial multiple of a collision axiom. For each repeated variable, subtract a monomial multiple of $x^2-x$. The corrections and all partial sums have degree at most $q-1$. Multipliers $0$ and $1$ arising from restricted variables give zero or unchanged lines. The final line is an ordinary degree-$(q-1)$ derivation of $1$, contrary to Riis's bound. Thus every sparse PC refutation of $B_{4q,3q}$ contains at least $(6/5)^{q-1}$ nonzero monomial occurrences. This argument places no degree restriction on the original sparse proof.

## 2. Projecting tensor action and inverse equations

Use dimension $n_0=r+s=7q$. For $h\in\{r,s\}$, define $T_h=\sum_{i=1}^{h} e_i\otimes e_i\otimes e_i$ in $(F^{n_0})^{\otimes3}$. The mode-1 flattening has rank $h$, so $T_r$ and $T_s$ are nonisomorphic over every extension of $F$. Put $P=(x_{ij})$ in size $r\times s$. Substitute the same matrix $U$ into all three action matrices.

$$
U=\begin{pmatrix}P^{\mathsf T}&0\\0&P\end{pmatrix}.
$$

The source column partition is $r,s$ and the target row partition is $s,r$. For each inverse matrix substitute $U^{\mathsf T}$. Every variable maps to zero or an original variable.

The products $UU^{\mathsf T}$ and $U^{\mathsf T}U$ are block diagonal with blocks $P^{\mathsf T}P$ and $PP^{\mathsf T}$ in the respective orders. The off-diagonal entries of each block are sums of collision axioms. The diagonal entries minus 1 are sums of Boolean axioms and a row or column sum axiom. Hence every image of an inverse equation has a degree-2 derivation of polynomial sparse size from $B_{r,s}$.

The image of an action coefficient equation is zero unless all its output indices $j,k,\ell$ lie in the first $s$ rows. In that part the image is

$$
\sum_{i=1}^r x_{ij}x_{ik}x_{i\ell}-\boldsymbol 1_{j=k=\ell}.
$$

When two of the three column indices differ, each summand is a monomial multiple of a row collision axiom. When all coincide, subtract the column-sum axiom and use $x^3-x=(x+1)(x^2-x)$ on each summand. This gives a degree-3 derivation of polynomial sparse size.

For a fixed finite field $F$, the added equation $z^{|F|}-z=0$ maps to zero or to a polynomial multiple of $x^2-x$ via

$$
x^{|F|}-x=(x^2-x)(1+x+\cdots+x^{|F|-2}).
$$

Its derivation has degree at most $|F|$ and constant size in $n$ for a fixed field.

A substitution sending variables to variables, zero or one never expands a monomial. Multiplication and linear combinations remain valid PC inferences or trivial steps. Replacing projected axioms by the derived lines above turns any TI proof of sparse size $S$ into a proof of $B_{r,s}$ of size at most $S+\operatorname{poly}(n_0)$ for fixed field. The overhead can be charged once per distinct axiom, of which there are polynomially many. In particular, $S\ge (6/5)^{q-1}-\operatorname{poly}(n_0)=2^{\Omega(q)}$. Likewise the projection preserves the degree of a proof because the simulations of all projected axioms stay within their original degrees. Riis's obstruction forces degree at least $q$.

For arbitrary sufficiently large $n$, take the largest power $q$ of $p$ with $7q\le n$, pad the tensors with zeros, and pad the witness substitutions with an identity on the supplementary coordinates. Inverse equations on the new block and action equations involving new coordinates have zero image. Now $q>n/(7p)$.

## 3. The same projection for matrix problems

Put $A=\operatorname{diag}(I_r,0_s)$ and $B=\operatorname{diag}(I_s,0_r)$. They have different ranks, hence are inequivalent, noncongruent and nonconjugate.

- For conjugacy, use $X=U$ and $X'=U^{\mathsf T}$ in the notation of Galesi et al. The entries of $XA-BX$ vanish identically.
- For congruence, use the same substitution. The matrix $XAX^{\mathsf T}-B$ becomes $\operatorname{diag}(P^{\mathsf T}P-I_s,0_r)$.
- For equivalence with action $XAY^{\mathsf T}=B$, likewise take $Y=U$ and $Y'=U^{\mathsf T}$. If the action is written $XAY=B$, exchange the substitutions for $Y$ and $Y'$.

The Gram blocks account for every projected inverse equation and every remaining action equation. The same argument gives both lower bounds for all sufficiently large dimensions.

## Scope and attribution

- Riis proves the base PC degree obstruction, including degree falls in ordinary PC. His stated size measure uses dense coefficient lists, including zero coefficients. The restriction argument above establishes a lower bound for the sparse monomial count specified by Galesi et al.
- The hard TI instances are diagonal tensors distinguished by flattening rank. The lower bound rules out a uniform $2^{o(n)}$ sparse bound in common mode dimension in positive characteristic. There are $V=6n^2$ equation variables, so the lower bound is $2^{\Omega_p(\sqrt{V})}$ on that scale and leaves open $2^{o(V)}$ bounds.
- The larger tensor rank is $4q$. Thus the examples give a linear lower bound on the rank scale in positive characteristic, addressing the lower-bound side of Open Question 7.1.
- The matrix projection reuses the rectangular inverse-matrix construction from earlier MathProofs work on Open Question 7.3. One copy of the rectangular variables suffices for both blocks.

## References

- Nicola Galesi, Joshua A. Grochow, Toniann Pitassi and Adrian She, [On the Algebraic Proof Complexity of Tensor Isomorphism](https://doi.org/10.4230/LIPIcs.CCC.2023.4), CCC 2023, especially Sections 2.3, 3 and 7. See also [the arXiv version](https://arxiv.org/abs/2305.19320).
- Søren Riis, [Degree profiles of uniform polynomial consequences](https://arxiv.org/html/2611.07280v1), arXiv:2611.07280v1, 2026, especially Definition 2.6 and Lemma 14.1.
