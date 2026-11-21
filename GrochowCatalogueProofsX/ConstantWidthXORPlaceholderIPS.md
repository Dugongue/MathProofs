# Constant-width placeholder certificates for inconsistent XOR CNFs

**GP-0713, an upper bound for the XOR subclass.** Encode an inconsistent system of Boolean parity equations by one standard clause for every violating local assignment, with the equation for that clause its multilinear violation indicator $F_{j,a}$. Include the Boolean axioms $x_i^2-x_i$. Using the displayed clause list, a placeholder-only IPS refutation of ROABP width at most three can be constructed in polynomial time. The clause placeholders can be ordered in blocks by parity equation, followed by the Boolean placeholders. The same construction gives a Geometric IPS refutation. It applies to every odd-charge Tseitin CNF, independent of graph structure, as well as general inconsistent XOR systems. Over characteristic two, the refutation is linear in the clause placeholders and has width at most two in every order.

## Characteristic different from two

Use Gaussian elimination over $\mathbb F_2$ to select a subset $J$ of parity equations whose left sides sum to zero and whose right sides sum to one. Write $c_j=(-1)^{b_j}$ for right-hand side bit $b_j$, and write $S_j$ for the variable set of equation $j$. The multilinear identity
$$
c_j\left(1-2\sum_{a\text{ violates }j}F_{j,a}(x)\right)
=\prod_{i\in S_j}(1-2x_i)
$$
holds by checking Boolean inputs. A multilinear polynomial vanishing on the Boolean cube has all coefficients zero, which follows by induction on the number of variables by setting the last variable to zero and one.

Let $Y_{j,a}$ be the corresponding clause placeholders and $Z_i$ the Boolean placeholders. Let $2r_i$ be the number of occurrences of $i$ among the equations in $J$. Define
$$
A(Y)=\prod_{j\in J}c_j\left(1-2\sum_{a\text{ violates }j}Y_{j,a}\right),
\qquad
B(Z)=\prod_i(1+4Z_i)^{r_i}.
$$
Under simultaneous substitution of the equations for all placeholders, the two polynomials become equal, since $(1-2x_i)^2=1+4(x_i^2-x_i)$. At the zero placeholder assignment they have values $A(0)=-1$ and $B(0)=1$. Thus $(B-A)/2$ is a Geometric IPS certificate, equal to one at the origin and zero on the equation map. Its complement $1+(A-B)/2$ is the ordinary IPS refutation.

In the $Y$ layers, compute $A$ block by block. Within a block keep the preceding product and the accumulator obtained by multiplying that product by the affine partial sum in the current block. This needs two states, and a third state retains the constant one. At the end of the $Y$ layers, keep $1+A/2$ in one state and initialize the running product for $B$ in a second state. Read each $Z_i$ just once with label $(1+4Z_i)^{r_i}$ for the running product. Use final output $1+A/2-B/2$. The widths never exceed three; fixed linear transitions between blocks may be folded into adjacent layers. The same widths compute the geometric variant. The total univariate coefficient count is linear in the displayed clause and variable-incidence size, since $\sum_i r_i=\frac12\sum_{j\in J}|S_j|$. Over $\mathbb Q$ their integer binomial coefficients have polynomial bit length.

## Characteristic two

The multilinear polynomial $\sum_{a\text{ violates }j}F_{j,a}(x)$ equals $b_j+\sum_{i\in S_j}x_i$, again by its Boolean values. Summing these identities over $J$ gives 1. Thus $\sum_{j\in J,a}Y_{j,a}$ is already a width-two IPS refutation, and its complement is geometric.

For bounded arity the standard clauses can be generated in polynomial time from the parity-system input. The statement uses one placeholder per clause occurrence. For simple connected Tseitin graphs of order at least three, two distinct vertices cannot have the same nonempty incident edge set, so suppression does not affect this family. This is an upper bound on a concrete class and does not decide the general nonlinear ROABP-IPS lower-bound question. The earlier Tseitin upper bound in the linear-coefficient model is [Hakoniemi, Limaye and Tzameret, Proposition 20](https://arxiv.org/html/2605.04544#S5.SS2).
