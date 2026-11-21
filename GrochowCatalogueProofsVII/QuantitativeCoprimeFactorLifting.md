# Bounded parameter degree in coprime border factor lifting

## GP-0600

Let $F(x,y)\in K[x,y_1,\dots,y_n]$ be monic in $x$ of degree $D$ and factor as $gh$, with both factors monic in $x$. Suppose $g$ has total degree at most $d$, and the two slices $g_0=g(x,0)$ and $h_0=h(x,0)$ are coprime. Let $P(\epsilon,x,y)$ be represented by a circuit of size $s$ using additions and multiplications in $x,y$ over $K(\epsilon)$, be of $x$-degree at most $D$, and satisfy $P=F+O(\epsilon^a)$ at $\epsilon=0$, where $a\ge1$. Suppose all coefficients in $x,y$ of $P$ share a denominator $b(\epsilon)$ nonzero at zero, with numerator degrees and denominator degree at most $R$. Then $g$ has an approximation $G(\epsilon,x,y)=g+O(\epsilon^a)$ with arithmetic-circuit size polynomial in $s,D,d,n$, independent of the numerical parameter degree $R$. Its coefficients have common denominator $b^d$ and numerator degrees at most $dR$. In particular a polynomial parameter approximation remains polynomial and its parameter degree grows by at most a factor $d$. The same bound works when $a$ and $R$ are given in binary. Size here counts field and circuit operations, with the known univariate slices of the factors available as constants.

The coprime slice is available after a generic affine coordinate choice over an infinite field for a complementary factor coprime to $g$. Choose an $x$ direction on which the top homogeneous parts of both factors are nonzero. Then both can be normalized to be monic in that variable. Their resultant in $x$ is a nonzero polynomial of the other variables, so translating a point off its zero set gives the desired slice. This explains the scope for simple factors of a polynomial of bounded total target degree. [Border factor closure context](https://arxiv.org/html/2506.19604v2)

To construct $G$, first enforce exact agreement with $F$ on the $x^D$ coefficient and on the specialization $y=0$. Replace the coefficient of $x^D$ by one, then add the difference between $F(x,0)$ and the current specialization. This produces $\widetilde P$ with the same accuracy and parameter bounds. Introduce $\tau$ and take the terms up to degree $d$ of $\widetilde P(\epsilon,x,\tau y)$ in $\tau$. Write them as $F_j(\epsilon,x,y)$, with $F_0=g_0h_0$. Each $F_j$ for $j\ge1$ has $x$-degree less than $D$, as the leading coefficient is exactly one. Coefficient arrays through $\tau$-degree $d$ and $x$-degree $D$ can be evaluated by running the supplied circuit over the truncated polynomial rings in $x,\tau$. This costs polynomially many gates per original gate and is valid even if some original intermediate $x$-degrees are large. Normalize the result by the preceding replacements on these arrays.

For $j=1,\dots,d$ set
$$
E_j=F_j-\sum_{i=1}^{j-1}G_iH_{j-i}.
$$
Use the unique solutions with $\deg_x G_j<\deg_x g_0$ and $\deg_x H_j<\deg_x h_0$ of
$$
h_0G_j+g_0H_j=E_j .
$$
They are given by $G_j=(h_0^{-1}E_j)\bmod g_0$ and $H_j=(E_j-h_0G_j)/g_0$. The inverse in the formula is computed once in $K[x]/(g_0)$, and all steps on the $x$-coefficient vectors are linear operations over $K$. A constant factor is handled directly. The recurrence computes exactly the monic Hensel factors modulo $\tau^{d+1}$. Reduction modulo $\epsilon^a$ commutes with the recurrence, because it divides only by fixed scalar coefficients over $K$. Consequently each $G_j$ modulo $\epsilon^a$ is the degree-$j$ piece of $g(x,y)$ in $y$. Their sum through $d$ is the claimed approximation.

Inductively $G_j$ and $H_j$ have common denominator $b^j$ and numerator degrees at most $jR$. Multiplying two earlier coefficient arrays adds their denominator exponents and numerator degree bounds. The input $F_j$ can be put over $b^j$ by multiplying its numerator by $b^{j-1}$. Fixed linear operations in $x$ preserve these bounds. Summing the $G_j$ over the denominator $b^d$ gives the final result, including the constant slice $g_0$. All convolution and linear operations take polynomially many arithmetic gates, without extracting any coefficients in $\epsilon$. The bound keeps the input accuracy and controls parameter degree even when the interpolation variable is represented succinctly.
