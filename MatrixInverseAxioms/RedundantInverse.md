# Deriving one reverse inverse equation is already factorial-scale

Let $X,Y$ be independent $n$-by-$n$ variable matrices over any field. Consider ordinary Polynomial Calculus **derivations** from only the entries of $XY-I$, and set $E=I-YX$. For $n\ge2$ every diagonal equation $E_{ii}=0$ requires degree at least $n+1$. For $n\ge3$ every individual off-diagonal equation $E_{ij}=0$ requires degree at least $n$. Every entry has a derivation in degree at most $n+3$. For each individual entry, the minimum sparse derivation size is $n^{\Theta(n)}$ as $n$ grows, with absolute constants, allowing unrestricted degree in the lower bound.

These are consequences between satisfiable systems in the original variables. At every point satisfying $XY=I$ over any commutative ring, the determinant and adjugate identities imply $YX=I$. Adding both directions as input can therefore greatly strengthen Polynomial Calculus without changing the solution scheme. The consequences use no coordinate field equations. [Context in Question 7.3](https://arxiv.org/html/2305.19320#S7.SS3)

## Lower bounds by restriction

For an indicated diagonal entry set column $i$ of $X$ and row $i$ of $Y$ to zero. Their remaining entries are independent rectangular matrices $P,Q$ with inner size $n-1$ and outer size $n$. Every forward axiom becomes an entry of $PQ-I_n$. The alleged consequence becomes the constant one. This turns the derivation into a refutation of the one-sided Rank Principle. Its exact degree is $n+1$ and its minimum sparse size is $(n-1)^{\Theta(n-1)}$. [One-sided Rank Principle](OneSidedMatrix.md)

For an indicated off-diagonal $(i,j)$, make $i,j$ the final two source coordinates in that order and use one final target coordinate. Substitute
$$
 X=\operatorname{diag}(P,U),\quad
 Y=\operatorname{diag}(Q,V),\quad
 U=\begin{pmatrix}1&1\end{pmatrix},\quad
 V=\begin{pmatrix}1\\0\end{pmatrix}.
$$
Here $P$ is $(n-1)$-by-$(n-2)$ and $Q$ its reverse shape, with independent entries. The constant block satisfies $UV=I_1$ and the $(i,j)$ entry of $I_2-VU$ equals $-1$ in every field. All axioms therefore become zero or the one-sided Rank Principle of inner size $n-2$ and outer size $n-1$, and the alleged consequence becomes a unit. Apply its degree and size lower bounds. Both restrictions send each variable to a variable, zero or one, so every PC step specializes without increasing the degree or sparse size. A multiplication by a substituted scalar is a scalar combination and needs only that one premise and a zero coefficient.

## An upper bound by descending cofactors

First derive $XE=0$ in degree three from $XE=-(XY-I)X$ entry by entry. Left multiply those equations by the cofactors from $\operatorname{adj}(X)$, expanding each into monomial multiples and taking scalar sums. This gives $(\det X) E_{ab}=0$ for each fixed pair $(a,b)$ in degree at most $n+2$, by the adjugate identity.

Fix $(a,b)$ and write $e=E_{ab}$. Suppose all size-$(j+1)$ minors of $X$, multiplied by $e$, have been derived as zero. Choose $j+1$ rows and $j$ columns and form the row vector $c$ of signed $j$-minors supported on those rows. Each entry of $cX$ is a $(j+1)$-minor up to sign, or is identically zero by repetition of a column. Thus each entry of $e(cX)$ vanishes. Multiplying each by one entry of $Y$ and summing gives $e(cX)Y=0$. Separately, $ec(XY-I)=0$ follows by expanding the coefficients $ec_\ell$ into monomials and multiplying each forward inverse input by those monomials. Subtracting gives $ec=0$. Both derivations have degree at most
$$
 \max\big((j+1)+2+1,\ j+2+2\big)=j+4 .
$$
Every $j$-minor is obtained since there is a spare row. Descending from $j=n-1$ to $j=0$ gives $e=0$, at degree at most $n+3$.

There are at most $2^{2n}$ minors at each level, each $j$-minor has support at most $j!$, and $e$ has support at most $n+1$. All intermediate products by the selected $Y$ entry or the selected inverse axiom can be charged term by term, with binary summation trees. Their total monomial cost is $2^{O(n)} n!\operatorname{poly}(n)$, including the initial adjugate step. In particular the bound uses no extension variables or circuit abbreviation for a polynomial line. The proof gives the degree order and sparse factorial scale. The exact minimum degree of an individual missing inverse equation within the indicated interval is left open. These are written arguments.
