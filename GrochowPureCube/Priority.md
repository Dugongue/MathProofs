# Priority check for exact characteristic-three cubic equivalence

The result under review decides equivalence of arbitrary formal homogeneous cubics over $\mathbb F_{3^k}$, finds a linear transporter, and counts all linear transporters in time $q^{\widetilde O(c^{3/2})}\operatorname{poly}(n,\log q)$, with $c$ the polarization contraction rank. The proof uses $q^{O(c)}$ queries to ordinary tensor isomorphism on side lengths $O(c)$, followed by an orbit computation on the pure-cube fiber and separate radical lift counts. The [ordered-system algorithm](Systems.md) recovers the scalar theorem by taking one output.

## What precedes it

| Primary source | Coverage |
|---|---|
| [Agrawal and Saxena, Theorem 2.3](https://www.cse.iitk.ac.in/%75sers/nitin/papers/cubic-forms.pdf) | A polynomial many-one reduction of degree-$d$ forms to algebra isomorphism over fields with $d$-th roots. This includes cubics over every finite field of characteristic three because cubing is bijective. For nonzero cubics the truncated algebra has dimension $n+\binom{n+1}{2}+\binom{n+2}{3}$. Substituting that dimension into a fast algebra-isomorphism backend gives a different, larger bound. |
| [Grochow and Qiao I, Figure 2 and Corollary B](https://doi.org/10.1137/21M1441110) | Establishes the general TI-completeness framework and discusses the cubic-to-algebra route and the case where $6$ is a unit. Polynomial reducibility of finite characteristic-three cubic equivalence to TI is prior. |
| [Grochow, Qiao, and Tang, Theorem 3.1](https://arxiv.org/html/2012.01085#S3.SS1) | Gives a $q^{O(n)}$ bound for cubic equivalence over fields of odd order for all but a $q^{-\Omega(n)}$ fraction of first inputs. Characteristic three belongs to that guarantee. |
| [Grochow and Qiao IV, arXiv Corollary 1.11](https://arxiv.org/html/2306.16317#S1.SS4) | The earlier explicit cubic decision corollary assumes characteristic greater than three. |
| [Grochow and Qiao IV, STOC 2025 Corollaries 1.6–1.7](https://opus.lib.uts.edu.au/bitstream/10453/189643/2/3717823.3718282.pdf) | Corollary 1.6 broadly lists commutative cubic equivalence in its $q^{\widetilde O(n^{3/2})}$ decision statement. Its hypothesis calls for linear-length queries with $q^{O(n)}$ reduction time. Corollary 1.7 gives the conditional $q^{O(n)}$ cubic bound for prime characteristic greater than three, and its explicit polarization argument invokes that restriction. The broad statement in 1.6 takes precedence in any priority claim about the exponent itself. |
| [Ivanyos, Mendoza, Qiao, Sun, and Zhang, Theorem I.4](https://chuanqizhang.com/assets/pdf/pdf/focs24.pdf) | Supplies the alternating matrix-space congruence exponent used by the new algorithm. |
| [Sun, 2026, Sections 1.3 and 5](https://arxiv.org/html/2611.05920) | Uses a tensor stabilizer to recover missing central power data in class-two group isomorphism. This is close in strategy, with a different input category and residual invariant. |
| [Grochow, Qiao, Stange, and Sun V](https://arxiv.org/html/2611.00735) | Studies TI and algebraic isomorphism reductions over commutative rings. Its scope and general reductions do not settle the rank-sensitive decision, search and count statement under review. |

## Interpretation

The audit found a prior published statement that can be read to include the decision exponent in characteristic three. It did not find an explicit proof of that case at linear query length or a prior statement with the combined scope of all finite characteristic-three extension fields, contraction-rank dependence, exact witness extraction, and exact transporter counting. The addition that can be described precisely is the proof of this combined statement, including orbits inside a polarization fiber and exact lift counts on the radical. The search covered the primary TI papers and the recent analogous power-data recovery. It leaves publication priority open.

The distinction matters because polarization alone is incomplete. Over $\mathbb F_3$, the cubics $x^2y$ and $x^2y+y^3$ have the same polarization and different factorization types. The latter is $y(x^2+y^2)$, with an irreducible quadratic factor. The pure-cube fiber algorithm handles such pairs in the worst case.
