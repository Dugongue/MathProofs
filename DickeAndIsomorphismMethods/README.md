# Fixed-type tensor rates and isomorphism methods

Four reviewed written proofs on tensor subrank, local arithmetic, random symmetries, and small-space group algorithms. The Dicke result uses a reproducible exact finite certificate. Publication priority, human review, and Lean verification remain pending.

| Result | Scope |
|---|---|
| [Fixed-type Dicke subrank](TENSORS.md) | The entropy formula holds for 19 listed binary and 15 listed ternary types, with arbitrary nonzero coefficients on each prescribed support. It gives monomial and ordinary asymptotic subrank over every field and border asymptotic subrank over algebraically closed fields. |
| [Sharp local–global failure at diagonal rank six](GEOMETRY.md) | Classifies the first failures among geometrically diagonal ordinary tensors over number fields. The two patterns have splitting groups \(V_4\) and \(D_8\). Both have explicit integral realizations over the rationals which are isomorphic modulo every positive integer and nonisomorphic over the rationals. |
| [Random concise tensor stabilizers](RANDOM-TENSORS.md) | Computes the leading probability of a nontrivial effective stabilizer and the first orbit-count correction at fixed finite-field size. It identifies the additive and multiplicative rank-one subgroups accounting for almost every exception. |
| [Low-space Fitting-free group isomorphism](GROUPS.md) | Gives deterministic logspace decision, witness output, and exact counting under either a socle multiplicity-factorial bound or bounded generator rank of the socle quotient. It gives an unconditional \(O(\log N\log\log(N+2))\) space bound on this class. |

The [Dicke certificate](check_tensors.py) exhausts 8,733,144 binary and 59,537 ternary nonzero subspaces and checks the entropy inequalities with exact integers. The [stabilizer replay](check_random_tensors.py) checks paired rank-one event counts and overlap bounds over the fields of orders two and three. The [group replay](check_groups.py) checks factoradic access and synchronized factor intertwiners, including twisted swaps on \(A_5^2\). Independent arithmetic checks verified the integral quartic bases and subgroup restrictions in the two diagonal patterns. The cited precedents distinguish established ingredients from the statements proved here.
