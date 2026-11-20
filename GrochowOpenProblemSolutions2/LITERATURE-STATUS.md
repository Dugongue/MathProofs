# Catalog entries settled in the literature

## GP197 · Bounded-arithmetic proofs of nonuniform identity testing

Atserias and Tzameret’s Theorem 4.6 proves bounded and unrestricted evaluation-form PIT in $\mathsf{P}/\mathsf{poly}$ inside $S^1_2+\mathrm{dWPHP}(\mathrm{PV})$. Jeřábek states the provability of the latter axiom scheme in $T^2_2$, a fragment of $T_2$. Hence the requested theory proves the finite-circuit statement for binary-encoded integer arithmetic formulas. [Atserias–Tzameret, Theorem 4.6](https://arxiv.org/html/2411.07966#S4.SS2) · [Jeřábek, Chapter 2, p. 14](https://eccc.weizmann.ac.il/resources/pdf/jerabek.pdf)

For formula inputs of bit length at most $s$, relabel variables by occurrence, bound the syntactic degree by the leaf count, and use the resulting polynomial bounds in that theorem. A fixed polynomial-size decoder and the Boolean circuit of Theorem 4.6 together accept precisely when all integer evaluations vanish. Rejection already has a witness in a polynomial-side grid on at most $s$ variables. The circuit and one grid point both have polynomial-length descriptions, absorbed into the common exponent in Problem 15 for sufficiently large $s$. The resulting equivalence holds with the stated bounded input quantifier. This uses the usual finite conventions for short codes and ill-formed strings. [Problem 15](https://wiki.simons.berkeley.edu/doku.php?id=mc23:list-of-open-problems)

## GP200 · Graph isomorphism reduces to total MCSP

The required bounded-error randomized polynomial-time oracle reduction is already a consequence of Allender and Das’s inclusion $\mathsf{SZK}\subseteq\mathsf{BPP}^{\mathsf{MCSP}}$, together with graph isomorphism in $\mathsf{SZK}$. The oracle in their result takes a full single-output truth table and a circuit-size threshold. The subsequent Grochow–van Melkebeek–Moore–Morgan paper explicitly records this earlier consequence for MCSP and establishes the different zero-sided-error result for MKTP. [Allender–Das, Zero Knowledge and Circuit Minimization](https://doi.org/10.1016/j.ic.2016.10.004) · [Grochow et al., introduction](https://arxiv.org/pdf/1710.09806)


## GP089 · Third-minor flattenings of complex Gorenstein algebras

Doležálek, Jagiełła, Oszer, Seynnaeve and Stastny established the requested complex Gorenstein identity in Corollary 7.9. Their Theorem 1.5 also gives the conormal comparison over algebraically closed fields of characteristic zero. The [third-minor proof in this package](MINOR-FLATTENING.md) establishes the conormal formula over all fields of characteristic different from two, including characteristic three. [Prior result, Theorem 1.5 and Corollary 7.9](https://arxiv.org/html/2610.17875v1)

The related [GP088 proof](TANGENCY-FLATTENING.md) follows the original multiplication-output convention. The later paper's Corollary 4.8 studies the multiplication-input factor, as specified in its Setting 5.2. [Original Conjecture 6.1 and convention](https://arxiv.org/html/2602.12762v1#S6.SS1) · [Later tangency formula](https://arxiv.org/html/2610.17875v1#S4)
