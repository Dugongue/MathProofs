# A prefix-rank bound for ROABP power roots

**GP-0603, width-degree tradeoff.** Let $K$ have characteristic zero and let $g\in K[x_1,\ldots,x_n]$ have total degree at most $D$. If $g^d$ has an ROABP of width at most $w$ in a specified order, where the positive integer $d$ is arbitrary, then $g$ has an ROABP in that same order of width at most
$$
\binom{w-1+D}{w-1}.
$$
At an individual cut one may use the actual rank of $g^d$ at that cut and the total degree of $g$ in the suffix variables. In particular fixed-width inputs have polynomial-width roots.

## Proof

The zero case is immediate. Split the variables at a cut into prefixes $x$ and suffixes $y$. The coefficient matrix of $g^d$ across this cut has rank $r\le w$. Choose $y_0\in K^{|y|}$ with $g_0(x)=g(x,y_0)\ne0$, which exists over the infinite field $K$. The coefficient space in $x$ of $g^d(x,y_0+z)$ contains $g_0^d$. Extend it to a basis $g_0^d,a_1,\ldots,a_{r-1}$, and write
$$
g^d(x,y_0+z)=g_0^d b_0(z)+\sum_{j=1}^{r-1}a_j(x)b_j(z),\qquad
b_0(0)=1,\quad b_j(0)=0\ (j\ge1).
$$
Set $c_j=a_j/g_0^d\in K(x)$. With a formal variable $T$, the series $g(x,y_0+Tz)/g_0$ is the unique $d$-th root with constant term 1 of $b_0(Tz)+\sum_{j\ge1}c_j b_j(Tz)$. Uniqueness follows by comparing the first coefficient where two candidate roots differ, since $d$ is invertible. Write the root as the binomial series in
$$
B=b_0(Tz)-1+\sum_{j=1}^{r-1} c_j b_j(Tz).
$$
Each term $B^i$ starts at order $T^i$ and has degree at most $i$ in the $c_j$ when those ratios are treated as formal placeholders. If $D_y$ is the suffix degree of $g$, retaining $T$-degrees at most $D_y$ and then setting $T=1$ gives the entire polynomial $g/g_0$. Consequently its suffix coefficients after multiplying by $g_0$ lie in the $K$-span of
$$
g_0 c_1^{e_1}\cdots c_{r-1}^{e_{r-1}},\qquad \sum_j e_j\le D_y .
$$
This bounds the coefficient rank by $\binom{r-1+D_y}{r-1}$, even though the spanning functions were found in $K(x)$, because the polynomial coefficient space embeds in $K(x)$. Translating $y$ back leaves that rank unchanged.

For completeness, the maximum prefix coefficient rank is the minimum possible width in a specified order. A width-$w$ ROABP gives a sum of $w$ separated products at each cut. Conversely, take a basis of the suffix polynomials obtained by coefficient extraction on each prefix. The coefficient of any power of the next variable in each current basis vector belongs to the next basis span. Expressing these coefficients in that basis gives the next univariate transition matrix. Use the singleton bases $g$ and $1$ at the two endpoints. Multiplying all transition matrices computes $g$ with the claimed width.

**Scope.** The bound is polynomial in $D$ for fixed $w$. A bound polynomial jointly in the width and degree remains open here. [Andrews, Armand, Dwivedi, Hansen, Limaye, Srinivasan and Tavenas, Section 6](https://drops.dagstuhl.de/storage/00lipics/lipics-vol362-itcs2026/html/LIPIcs.ITCS.2026.9/LIPIcs.ITCS.2026.9.html).
