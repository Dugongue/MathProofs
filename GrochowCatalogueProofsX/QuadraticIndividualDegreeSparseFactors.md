# Factor sparsity from shared nonlinear variables

**GP-0606, a shared-variable bound.** If $f=gh\ne0$ and $J=\{i\colon \deg_{x_i}g\ge2,\ \deg_{x_i}h\ge1\}$, then
$$
|\operatorname{supp}(g)|
\le |\operatorname{supp}(f)|\prod_{i\in J}(\deg_{x_i}g+1).
$$
As a direct special case it recovers the Volkovich linear bound for individual degree two over every field. It also gives a polynomial sparsity bound at every fixed individual degree $d$ when $|J|=O(\log|\operatorname{supp}(f)|)$.

## Proof

Put all variables absent from $h$ in a set $E$, and write $g=\sum_a x_E^a g_a$ and $f=\sum_a x_E^a f_a$ with coefficients in the remaining variables. Then $f_a=g_a h$ for each $a$. Both sparsities are the sums of the corresponding coefficient-polynomial sparsities. It suffices to prove the bound for each nonzero pair $f_a,g_a$.

For nonzero polynomials $u,v$, their Newton polytopes satisfy $P_{uv}=P_u+P_v$. To see this, for any real linear functional the extremal-weight terms of the product are the product of the extremal-weight polynomials, which is nonzero over a field. The support functions therefore add. The number of vertices of a Minkowski sum is at least the number of vertices of either summand. Indeed, for a given vertex $w$ of $P_u$, choose a functional uniquely maximizing there and perturb within the open strict inequalities so it uniquely maximizes at a vertex of $P_v$ as well. The resulting vertex of the sum determines $w$ uniquely: in any decomposition of that sum vertex, both summands must separately maximize the chosen functional.

Now project the exponent vectors of $g_a$ to the coordinates outside $E\cup J$. They are binary in those coordinates, since every remaining variable occurs in $h$. Every distinct projected exponent vector is a vertex of the projected Newton polytope: a coordinate functional with signs chosen according to that binary vector uniquely exposes it. Each projected vertex lifts to at least one vertex of $P_{g_a}$ by taking a vertex of its maximizing face. Each projected exponent has at most $\prod_{i\in J}(\deg_{x_i}g+1)$ lifts in the support, by the available coordinate ranges. Hence
$$
|\operatorname{supp}(g_a)|
\le |V(P_{g_a})|\prod_{i\in J}(\deg_{x_i}g+1)
\le |\operatorname{supp}(f_a)|\prod_{i\in J}(\deg_{x_i}g+1).
$$
Summing over $a$ proves the general bound. If $f$ has individual degree at most two, degrees add in each variable in the nonzero product. A variable of degree at least two in $g$ is therefore absent from $h$, so $J$ is empty. The coefficient one is sharp even for a proper factor, since multiplying $g$ by a new variable preserves its sparsity and the individual-degree bound.

Volkovich already established the linear bound for multiquadratic inputs. The extension here bounds each oriented factor by the shared nonlinear variables of that factor, even for higher individual degree. The general sparse-factor question and quasipolynomial vertex bound appear in [Bhargav, Dwivedi and Saxena, §8.1](https://arxiv.org/html/2506.19604v2#S8.SS1). The unrestricted constant-individual-degree question for degrees above two remains open in this argument. [Volkovich, multiquadratic factors](https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2017.48)
