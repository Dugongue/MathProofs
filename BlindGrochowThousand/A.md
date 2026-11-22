# First collisions in finite permutation test panels

This file gives 250 kernel-checked finite results on when tests distinguish the cycle types of an unknown permutation of known degree. Each panel records its first collision degree, two explicit cycle types that agree there, and the exact number of distinguishable classes in a stated follow-on degree. The five families each contain 50 panels.

| Family | Observations |
|---|---|
| Fixed-point counts | Number of fixed points after selected powers, exactly or modulo specified integers |
| Nullities | Dimension of the kernel of $P^k-I$ for the permutation matrix $P$, exactly or modulo specified integers |
| Mixed | Fixed-point counts and nullities |
| Extension | Cycle type of a powered permutation with fixed-point or nullity observations |
| Characteristic polynomial | Coefficients of $\det(I-XP)$ modulo an integer with fixed-point or nullity observations |

The formulas differ. A length-$d$ cycle contributes $d$ to the fixed-point count exactly when $d$ divides $k$. It contributes $\gcd(d,k)$ to the nullity since the kernel is spanned by one vector constant on each orbit of $P^k$. This calculation holds in every field characteristic. The powered cycle type replaces a length-$d$ cycle by $\gcd(d,k)$ cycles of length $d/\gcd(d,k)$. The polynomial of a single cycle is $1-X^d$, and the polynomial of the profile is the product of these factors. The powered cycle type also models Frobenius after scalar extension for a finite étale algebra. [Cherniavsky and Sklarz on permutation matrix similarity](https://arxiv.org/abs/math/0411554) · [The Stacks Project on finite étale Galois sets](https://stacks.math.columbia.edu/tag/04JI)

The first failures across the selected panels occur in degrees 6 (10 panels), 7 (4), 8 (118), 9 (60), and 10 (58). The search rejects any panel inducing the same equivalence relation as an already retained panel across degrees 2 through 11. Thus the choices vary in actual distinguishing information, even when two observations have different names or use different moduli. They can still agree on which first pair collides. The corpus consists of finite results about these panels. The general formulas below are deductions from the cycle model.

## Two exact formulas suggested by the search

Let $p$ be prime and $t\ge1$. Supply the cycle type of the $p$-th power and one extra observation modulo $m>0$. Put $q=3$ for $p=2$ and $q=2$ otherwise. If $m=0$, read the extra observation as an exact count and omit the residue term in the formulas.

- For the number of fixed points of the $t$-th power, the first collision is at degree $p$ if $p\mid t$. Otherwise it is $p\min(m/\gcd(m,p),b,2a)$, where $b$ is the least positive integer prime to $p$ that does not divide $t$ and $a$ is the least divisor of $t$ greater than 1. Interpret $a$ as infinity if $t=1$.
- For the nullity of $P^t-I$, the first collision is likewise at degree $p$ if $p\mid t$. Otherwise it is $p\min(m/\gcd(m,p-1),q+\gcd(q,t))$.

For instance, the fifth-power cycle type and fixed points modulo 3 determine every permutation conjugacy class in degree at most 9. In degree 10, one 10-cycle and five 2-cycles give identical observations. As another example, the fifth-power cycle type and the nullity of $P^9-I$ modulo 8 first fail in degree 10, where two 5-cycles agree with ten fixed points. Both examples have Lean certificates in the corpus.

To prove the formulas, a common $p$-th power profile forces the signed difference between original multiplicities to vanish at every length divisible by $p^2$. Each remaining fiber consists of $u$ and $pu$, with $p\nmid u$. It permits difference $z_u$ at length $pu$ and difference $-p z_u$ at length $u$. The two profiles have common degree at least $p\sum_u u|z_u|$. Positive and negative parts of any such nonzero difference realize exactly that common degree. If $p\mid t$, both extra observations cancel on each fiber, and the least nonzero choice uses $u=1$ with $|z_1|=1$.

Suppose $p\nmid t$. For fixed points, the added difference is $-p\sum_{u\mid t} u z_u$. If a nonzero coordinate has $u\nmid t$, the cost in units of $p$ is at least $b$, attained by using only $u=b$. Within the divisors of $t$, a nonzero sum divisible by $m/\gcd(m,p)$ costs at least that residue period, attained at $u=1$. A zero sum with nonzero coordinates uses at least one $u>1$ and requires both signs to carry mass at least $a$, giving cost $2a$. Equality uses $z_a=1,z_1=-a$.

For nullity, the extra difference is $-(p-1)\sum_u \gcd(u,t)z_u$. The nonzero sum costs at least $m/\gcd(m,p-1)$ since $\gcd(u,t)\le u$. Again a repetition at $u=1$ attains equality. A nonzero zero-sum configuration contains some $u>1$, contributing at least $u$ to the cost and requiring compensation of absolute weight at least $\gcd(u,t)$. The lower bound $u+\gcd(u,t)$ is attained by assigning $z_u=1$ and $z_1=-\gcd(u,t)$. The minimum over $u>1$ prime to $p$ is at $q$. If $u>q$, then $u+1\ge q+\gcd(q,t)$ since $q=2$ or $q=3$ and the next odd integer after 3 is 5. This proves both formulas. Their verification here is the written argument. The Lean file verifies concrete instances and the finite verification rules.

## Replay and structural provenance

The anonymous queue supplied, among others, consumer 44854 with divisor producers 287385, 109675 and 382585 at position 2. Position 15 joined coprime multiplication, a modular congruence and primitive-root divisibility at consumer 330413. Position 60 paired cyclotomic evaluation with arithmetic bound and characteristic ports, and positions 159 and 166 exposed permutation cycle type producer 74081. These motifs suggested composing fixed-point and matrix invariants through the cycle profile. The finite search and mathematical deductions followed the reveal.

Run `python A-gen.py` from any working directory. The generator uses its companion template and a fixed seed to replay the search and regenerate the Lean source and target list. It uses only the Python standard library. The Lean enumerator independently recomputes positive nonincreasing cycle lists and test observations. Three supporting universal Lean theorems establish completeness of enumeration, separation below each certified cutoff, and collision at the given witnesses. The count of 250 consists of the finite certificates alone. [Lean source](A.lean) · [Generator](A-gen.py) · [Template](A-Template.lean)
