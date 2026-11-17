# Fixed-format tensor isomorphism over finite fields in polynomial bit time

The Shonan Meeting 246 report records Youming Qiao's question of whether $3\times3\times3$ tensor isomorphism over $\mathbb F_q$ can be decided in time polynomial in $\log q$. The answer is yes, by a direct application of Kayal's existing finite-field decision theorem. This observation credits Kayal for the algorithmic result and makes no claim of novelty for that theorem. [Shonan Meeting 246, printed p. 14](https://shonan.nii.ac.jp/docs/No.246.pdf#page=15) · [Kayal, dissertation, Theorem 6.1.1](https://eccc.weizmann.ac.il/resources/pdf/kayal.pdf)

**Theorem.** Fix a tensor format $n_1\times\cdots\times n_r$, including the order $r$. On two tensors over a supplied finite field $F=\mathbb F_q$ presented in a power basis over its prime field, ordinary tensor isomorphism is decidable deterministically in time polynomial in $\log q$. The polynomial may depend on the fixed format.

Write $A,B$ for the inputs. Introduce $r$ variable matrices $X_i$ of size $n_i\times n_i$ and $r$ scalar variables $u_i$. For each output multi-index $\boldsymbol a$, impose

$$
 \sum_{\boldsymbol b} A_{\boldsymbol b}\prod_{i=1}^r (X_i)_{a_i b_i}-B_{\boldsymbol a}=0.
$$

Also impose $u_i\det X_i-1=0$ for every $i$. The first equations express the tensor action, and the last equations hold for some $u_i$ precisely when all of the matrices are invertible over $F$. Thus solutions over the supplied field are equivalent to isomorphisms. The equations have $\sum_i n_i^2+r$ variables, $\prod_i n_i+r$ members and degree at most $\max(r,1+\max_i n_i)$. They can be constructed explicitly with a number of finite-field operations bounded in terms of the format. For $3\times3\times3$, there are 30 variables, 30 equations and degree at most four.

Kayal's theorem decides common-zero existence over $\mathbb F_q$ for a fixed number of variables in deterministic time polynomial in the degree, number of equations and $\log q$. Here all parameters except $q$ are constant. The algorithm considers rational solutions over the supplied field itself. Consequently the reduction applies to every characteristic, including degenerate tensors. No assumption about geometric orbits enters the equivalence. The output is a decision. Recovering a transporter or proving a small practical runtime would require separate arguments. [Kayal's published solvability result](https://www.microsoft.com/en-us/research/publication/solvability-of-a-system-of-bivariate-polynomial-equations-over-a-finite-field/)

The same proof allows additional transporter constraints described by a fixed polynomial system in a fixed number of variables, with coefficients computable in time polynomial in $\log q$. For example, replacing $u_i\det X_i-1$ by $\det X_i-1$ gives the same asymptotic decision bound for fixed-format special-linear tensor isomorphism. This consequence leaves the relations between the two problems in growing dimension open.
