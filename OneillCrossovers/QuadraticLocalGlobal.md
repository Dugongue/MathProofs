# Uniform local–global undecidability across analytically nonvanishing quadratic fields

This combines the Top 30 restricted integral Hilbert’s tenth problem construction with the quadratic nonvanishing release. The field is a varying input. [Quadratic nonvanishing, Theorem 2](https://charlesponeill.com/maths-releases/chowla-nonvanishing/chowla-nonvanishing.pdf) and [restricted integral HTP construction](https://github.com/Dugongue/MathProofs/blob/main/Top30InformalProofs/26/integral-local-conditions.md).

## A uniform integer definition

Let $K=\mathbb Q(\sqrt d)$ with $d>1$ squarefree. A single existential quadratic system, with parameter $d$, defines $\mathbb Z$ in $\mathcal O_K$. Start with $x^2-dy^2=1$ and $M=y^2$. For any Pell pair in $\mathcal O_K$, the unit $t=x+\sqrt d\,y$ has norm $\pm1$, and its quadratic conjugate is $\pm t^{-1}$. Hence the conjugate of $y$ is $\pm y$. In particular $M$ is a nonnegative ordinary integer. Require

$$
Mv=(2w+1)(3w+1).
$$

Both factors are nonzero for algebraic integers $w$. Conversely for any nonzero integer $M$, choose integral $w$ such that each prime power dividing $M$ divides one factor, using the invertible coefficient $2$ or $3$ and the Chinese remainder theorem.

For four more Pell pairs impose $MW_i=y_i^2$, $z-\sum_iW_i=Mu$, and express each of $M+4z$ and $M-4z$ as a sum of four squares in $\mathcal O_K$. Each $y_i^2$ is rational by the same conjugation argument, so $W_i\in\mathbb Z$. At both real embeddings $|\sigma(z)|\le M/4$. If $u$ is irrational, the difference of its embeddings has magnitude at least $\sqrt d$, by the integral basis of $\mathcal O_K$. The congruence for $z$ then forces the difference of its embeddings to have magnitude at least $M\sqrt d$, a contradiction. Thus $z$ is an ordinary integer.

Conversely, given $z\in\mathbb Z$, take an ordinary integral Pell solution $X+Y\sqrt d$ with $Y^2>4|z|$ and put $M=Y^2$. Write $z\bmod M$ as the sum of four integer squares $k_i^2$, using the four-squares theorem on a nonnegative representative. For the $i$th additional pair use the coefficients of $(X+Y\sqrt d)^{k_i}$, with $k_i\ge0$. The binomial expansion gives $y_i/Y\equiv k_iX^{k_i-1}\pmod{Y^2}$ for $k_i>0$, and the $k_i=0$ solution gives $y_i=0$. Since $X^2\equiv1\bmod Y^2$, the integer $W_i=(y_i/Y)^2$ is congruent to $k_i^2\bmod M$. Finally $M\pm4z$ are nonnegative ordinary integers and have four-square representations. All terms can be encoded with a fixed number of quadratic equations using intermediate variables.

## The uniform reduction

Take one fixed MRDP polynomial for the halting predicate and attach the integer definition to every quantified variable. This gives a single computable construction over every real quadratic ring of integers, with a fixed number of variables and bounded degree. For a prescribed connectivity parameter, apply the restricted integral HTP construction to this system, using the intersective polynomial over the totally real field and the two-quartic compiler. Its coefficients are obtained effectively from the field and the halting index. The output is in the same fixed format for all real quadratic fields, has the stated geometric connectivity and rationality, has an integral adelic point surviving the étale–Brauer–Manin condition, and has a global integral point exactly when the machine halts.

Now fix a positive sign and 2-adic shell class and prescribe any pattern of splitting types at the odd primes up to $z(X)=o(\log X)$. Theorem 2 gives a proportion at least $0.9453419890-o(1)$ with nonzero central quadratic $L$-value, uniformly in the pattern. For these fields the central Dedekind zeta value is nonzero as well. On this nonempty analytic subfamily the reduction’s global-solvability proportion is exactly $1$ on a halting index and $0$ on a nonhalting index, while all its local solvability conditions hold. Consequently even deciding between these two promised outcomes for uniform families would decide halting.
