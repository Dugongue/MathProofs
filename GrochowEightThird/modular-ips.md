# Polynomial-size symmetric linear IPS for the pigeonhole principle

For every `N > m`, the matrix pigeonhole equations of Definition 19 over a characteristic-zero field have a placeholder-linear IPS refutation symmetric under `S_N × S_m`, of size `O(N^4)` counting gates and wires when `m < N`. For `N = m+1` over the rationals, the authors later announced polynomial size in their workshop slides. The following construction gives an independent proof and leads to an exact positive-characteristic criterion. [Dawar–Grädel–Kullmann–Pago, Section 6.3](https://arxiv.org/html/2504.16820#S6.SS3) [Proof Complexity Workshop slides, page 16](https://www.cl.cam.ac.uk/~btp26/slidesPC25workshop.pdf#page=16)

Let `X = (x_ij)` be the `N × m` variable matrix and `A=XX^T`. Use placeholders `r_i` for the row axioms `sum_j x_ij−1`, `b_ij` for the Boolean axioms `x_ij^2−x_ij`, and `c_ii'j` for the collision axioms `x_ij x_i'j` with `i≠i'`. Form a matrix `B(Y)` with diagonal entries `r_i + sum_j b_ij` and off-diagonal entries `sum_j c_ii'j`. When collision axioms are indexed by unordered row pairs, use their same placeholder at both positions. If the axiom list uses ordered pairs as distinct occurrences, use the indicated ordered placeholder in each position. It follows that `B(0)=0` and after axiom substitution `B=A−I`.

For `i=1,...,N`, let `p_i = tr(A^i)` and `q_i = tr(B(Y)(I+A+...+A^(i−1)))`. The polynomials `q_i` are placeholder-linear. After substitution `q_i=p_i−N` by the matrix geometric sum. Define `c_r = binom(N,r)` and `D_0=0`, then recursively define `D_r` by

```text
r D_r = sum_{i=1}^r (−1)^(i−1) (D_{r−i} p_i + c_{r−i} q_i).
```

Every `D_r` is placeholder-linear and vanishes at `Y=0`. If `e_r(A)` denotes the `r`-th coefficient with alternating sign of the characteristic polynomial, the difference between the Newton identities for `A` and `I` satisfies exactly the recurrence for `D_r` after axiom substitution. This follows term by term from

```text
e_{r−i}(A) p_i − c_{r−i} N
= (e_{r−i}(A) − c_{r−i}) p_i + c_{r−i}(p_i−N).
```

Thus `D_N` at the axioms is `det A−1=−1`, since `X` has fewer columns than rows. The output `−D_N` is a valid IPS certificate.

Here is an explicit syntactically symmetric circuit. Construct the entries of `A` with sums over hole indices, and the entries of all powers incrementally with ordinary matrix-multiplication gates indexed by row pairs and by summation indices. Row permutations relabel every row index in all such gates, and hole permutations relabel the hole indices in the first matrix products and in the placeholder entry sums. Thus `A`, its powers, and `B` transform by simultaneous row-index permutations, while the traces and all `D_r` gates are invariant. Sums over relabeled indices are unbounded-fan-in gates. The `N−1` matrix products use `O(N^4)` gates and wires, and the entry sums, traces, and scalar recurrence fit within that bound. This is an informal proof of the polynomial upper bound.

## Exact positive-characteristic threshold

Let `K` have characteristic `p>0`. For `N>m`, the fully `S_N × S_m`-symmetric placeholder-linear IPS refutation exists if and only if the least nonnegative residue `r=N mod p` satisfies `r>m`. For the original family `N=m+1`, the condition is `p>N`. The paper gives nonexistence for some finite-field instances. The criterion specifies every size and characteristic. [Dawar–Grädel–Kullmann–Pago, Section 6.3](https://arxiv.org/html/2504.16820#S6.SS3)

If `r>m`, put `k=m+1`. Then `k<p`, so the preceding recurrence works through index `k` over `K`. All `k × k` principal minors of `A` vanish by the rank bound, so `e_k(A)=0`. Moreover, `binom(N,k)=binom(r,k)` in `K`, by taking the coefficient of `t^k` in `(1+t)^N=(1+t^p)^((N-r)/p)(1+t)^r`. This coefficient is nonzero since `k≤r<p`. Hence `−D_k/binom(N,k)` is a symmetric placeholder-linear refutation. Computing only powers and recurrences through `k` has size `O((m+1)N^3)`.

If `r≤m`, then `N≥p`. Choose a permutation of the rows consisting of `(N-r)/p` disjoint `p`-cycles and `r` fixed rows, and fix all columns. Assign the fixed rows injectively to holes, with a single one in each such row, and assign zero elsewhere. The point is fixed by the chosen row permutation. Every fixed row axiom vanishes there, and every Boolean and collision axiom vanishes there. In a symmetric placeholder-linear certificate, contributions after axiom substitution are constant along each orbit of the chosen permutation, because the assignment is fixed. Each non-singleton orbit has size `p` and contributes zero. Each singleton orbit contributes zero because its axiom vanishes. The certificate would therefore evaluate to zero at this point, contradicting the required identity `1`. This argument applies to either ordered or unordered collision labels.

# Fixed-locus criterion for symmetric linear IPS in positive characteristic

Let `K` be any field of characteristic `p>0`. Let a finite group `G` permute the variables `X` and the labels of a finite axiom list `f_i(X)`, compatibly with substitution. There exists a `G`-symmetric placeholder-linear IPS refutation over `K` if and only if the following holds for every `p`-subgroup `P≤G`, including the trivial subgroup. On the `P`-fixed locus in the algebraic closure, the axioms whose labels are fixed by `P` have no common zero. This classifies existence, with no bound on circuit size. The modular failure of linear symmetric refutations is exhibited in Example 6 of the IPS paper. The orbit sums below are weighted relative transfers, related to the transfer-ideal and fixed-locus methods of Feshbach, Fleischmann, and Symonds. [Dawar–Grädel–Kullmann–Pago, Example 6](https://arxiv.org/html/2504.16820#S4) [Symonds, The module structure of a group action on a ring, Section 3 and Theorem 3.1](https://link.springer.com/article/10.1007/s00029-024-00968-w)

An invariant placeholder-linear polynomial has the form `C(X,Y)=sum_i a_i(X)y_i`, with `g(a_i)=a_(g i)`. The constant-in-`Y` part is zero because `C(X,0)=0`. Conversely any such invariant polynomial has a syntactically `G`-symmetric circuit. Use one product gate per distinct monomial, with its scalar coefficient, and an outer sum. Invariance and the permutation action make these gates permute literally under `G`.

Necessity follows by evaluating `C(X,f(X))` at a point fixed by `P` where all `P`-fixed axioms vanish. The summands over every non-singleton `P`-orbit give zero since their values are equal and the orbit size is divisible by `p`. Each singleton vanishes by assumption. A refutation would give one instead.

For sufficiency first pass to the algebraic closure `L` of `K` and set `R=L[X]`. Let `J` be the ideal of `R^G` consisting of the outputs `C(X,f(X))` from invariant placeholder-linear polynomials. It is an ideal because multiplying a certificate by an invariant coefficient preserves invariance and placeholder linearity. We show that `J` has no common zero on affine space over `L`.

Fix a point `a`. Set `H=G_a` and choose a Sylow `p`-subgroup `P` of `H`. By assumption there is a `P`-fixed axiom label `i` with `f_i(a)≠0`. Let `G_i` be its label stabilizer. The index `[H:H∩G_i]` is prime to `p`, since `H∩G_i` contains `P`. In the finite point orbit `G a`, choose a polynomial `v` taking the value one on `G_i a` and zero at every other point. Such a polynomial exists by interpolation on a finite collection of distinct points. The polynomial `u=prod_(h∈G_i) h(v)` is `G_i`-invariant and has the same designated values on `G a`. Consequently `sum_(gG_i∈G/G_i) g(u y_i)` is an invariant placeholder-linear polynomial. Its value after substitution at `a` receives a nonzero summand only for cosets in `H G_i/G_i`, since `g(u)(a)=u(g^(-1)a)`. On those cosets the axiom value is `f_i(a)` because the coset has a representative in `H`. Thus the total value is `[H:H∩G_i] f_i(a)≠0`.

By the Nullstellensatz there is a finite expression `1=sum_j b_j j_j` with `b_j∈R` and `j_j∈J`. Multiply all `G`-conjugates of that expression, first using formal variables `Z_j` in place of the `j_j`. The product `prod_(g∈G) (sum_j g(b_j) Z_j)` is invariant and has no constant term in the `Z_j`. Every coefficient therefore lies in `R^G`, and upon substituting `Z_j=j_j` the value belongs to `J`. Since every conjugate evaluates to one, this proves `1∈J` and gives an invariant placeholder-linear certificate over `L`.

Finally apply a `K`-linear functional `L→K` fixing one to the certificate coefficients. Axiom coefficients are in `K`, so coefficientwise application commutes with substitution, the variable and placeholder permutations, and both IPS identities. It yields an invariant placeholder-linear certificate over `K`. This is an informal proof.
