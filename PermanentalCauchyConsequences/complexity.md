# Sharp monomial certificates in ideals of maximal permanents

These are informal proofs. We use the full-support Cauchy examples of result #40 to determine a sharp row-localization threshold for permanental ideals and to give exact monomial membership criteria for two support classes. [Cauchy construction and Borchardt identity](https://github.com/Dugongue/MathProofs/blob/main/GrochowEightEleventh/complexity.md#permanental-rank)

Let $X=(x_{ij})$ be a generic $n\times m$ matrix over a field $K$, with $m\ge n$. Let $I_r$ be the ideal of the $r\times r$ subpermanents in the first $r$ rows, viewed in the full polynomial ring. Put $I_0=(1)$. For an ideal $I$, $I:D^\infty$ is the union of $I:D^a$ over $a\ge1$. The proofs use coefficient vectors of the rows' product in the square-zero algebra
$$
A=K[X][y_1,\ldots,y_m]/(y_1^2,\ldots,y_m^2).
$$
Write $L_i=\sum_j x_{ij}y_j$ and $f_r=\prod_{i=1}^r L_i$. The coefficient of $\prod_{j\in J}y_j$ in $f_r$ is the permanent on columns $J$, so these coefficients generate $I_r$.

## 1. The exact threshold for removing one row from the ideal

**Theorem.** Let $2\le r\le n$, take $S\subseteq[m]$, and put $D_S=\prod_{j\in S}x_{rj}$. Then
$$
I_r:D_S=I_{r-1}
\quad\Longleftrightarrow\quad
I_r:D_S^\infty=I_{r-1}
\quad\Longleftrightarrow\quad
\bigl(\operatorname{char}K=0\text{ or }\operatorname{char}K>r\bigr)
\text{ and } |S|\ge 2r-1.
$$
The positive implication holds over any commutative base ring in which $r!$ is a unit. This strengthens the one-row coefficient identities in Kirkup's Proposition 5 by giving a single colon and a sharp condition. [Kirkup, *Minimal Primes Over Permanental Ideals*, Proposition 5](https://arxiv.org/pdf/math/0510025)

**Unweighted left inverse.** In a square-zero algebra on a set $T$ of $2u+1$ variables, write $L_0=\sum_{j\in T}y_j$. Multiplication by $L_0$ from degree $u$ to degree $u+1$ sends a coefficient vector $(a_B)_{|B|=u}$ to $b_C=\sum_{B\subset C}a_B$ for $|C|=u+1$. For a fixed $u$-set $E$, take the linear combination
$$
\sum_{|C|=u+1} w_{|E\cap C|}b_C,
\qquad
w_u=\frac1{u+1},\qquad
w_h=-\frac{u-h}{h+1}w_{h+1}\quad (h<u).
$$
A coefficient $a_B$ with $h=|E\cap B|$ occurs with weight $(u-h)w_{h+1}+(h+1)w_h$ for $h<u$, and $(u+1)w_u$ for $h=u$. This is $0$ unless $B=E$, when it is $1$. For a larger set of variables, recover $a_E$ by specializing to any $2u+1$ variables containing $E$. Thus the unweighted multiplication has a constant left inverse whenever there are at least $2u+1$ variables and $(u+1)!$ is a unit.

**Including the other columns and clearing the denominator once.** Suppose $|S|\ge2r-1$. Write $L_0=\sum_{j\in S}y_j$, and $L_{\mathrm{out}}=\sum_{j\notin S}x_{rj}y_j$. Multiplication by $L_0+L_{\mathrm{out}}$ in total degree $r-1$ has a left inverse over the polynomial ring in the outside coefficients. To construct it, decompose an input $a$ by the set $J$ of its outside variables, so $a_J$ is a form of degree $r-1-|J|$ in the variables of $S$. If $b=(L_0+L_{\mathrm{out}})a$, then
$$
b_J=L_0a_J+\sum_{j\in J}x_{rj}a_{J\setminus\{j\}} .
$$
Recover the $a_J$ in order of increasing $|J|$ by the preceding left inverse for $L_0$. No inverse of an outside coefficient is needed.

Localize at the variables $x_{rj}$, $j\in S$, and let $\sigma$ scale $y_j$ by $x_{rj}$ for $j\in S$, fixing other variables and all coefficients. This conjugates multiplication by $L_0+L_{\mathrm{out}}$ to multiplication by $L_r$. If $B$ is the polynomial left inverse just built, then $\sigma B\sigma^{-1}$ is a left inverse for multiplication by $L_r$. In the squarefree monomial bases, each of its entries is an outside polynomial times a product of some $x_{rj}$ divided by a product of distinct $x_{rj}$, with $j\in S$. Multiplying by $D_S$ therefore clears all denominators once. The resulting polynomial matrix recovers $D_Sa$ from $L_ra$. Since the indeterminates have injective localization, this is a polynomial identity over the base ring.

Apply it to $a=f_{r-1}$. It shows $D_S I_{r-1}\subseteq I_r$. The opposite colon inclusion follows from $I_r\subseteq I_{r-1}$ and $I_{r-1}:D_S=I_{r-1}$, the latter because the variables in $D_S$ are independent of the first $r-1$ rows. Iterating the colon gives the same equality after any positive power of $D_S$.

**Sharpness in the field case.** If $p=\operatorname{char}K\le r$, take the last row and $p-1$ of the earlier rows all ones, and the other $r-p$ rows equal to distinct coordinate rows. Their product $f_r$ is zero because $(\sum_j y_j)^p=0$. The deleted row product $f_{r-1}$ is nonzero because $(p-1)!\ne0$ and one can select $p-1$ distinct coordinates outside the $r-p$ chosen coordinate rows. The last row makes $D_S=1$.

If the characteristic is zero or greater than $r$, yet $|S|\le2r-2$, use over an algebraic closure a full-support Cauchy example of size $r\times(2r-2)$ with zero maximal permanents and permanental rank exactly $r-1$. Permute rows so a nonzero $(r-1)$-permanent uses the first $r-1$ rows. Retain $\min(m,2r-2)$ columns including those of that subpermanent, place them so every position in $S$ gets a retained column, and pad any extra columns with zero. At this point $I_r$ vanishes, $D_S\ne0$, and an element of $I_{r-1}$ is nonzero. Evaluating an identity over $K$ at this point would give a contradiction if any power of $D_S$ put that element in $I_r$. This proves sharpness. $\square$


## 2. Exact membership for nested row supports

For a monomial $M$, let $S_i$ be the columns in which it uses a variable from row $i$, ignoring exponents. Suppose $\operatorname{char}K=0$ or $\operatorname{char}K>n$. If the row supports can be ordered so that $|S_i|\ge2i-1$, then the squarefree product $D=\prod_i\prod_{j\in S_i}x_{ij}$ belongs to $I_n$. In fact, Section 1 gives $I_i:D_{S_i}=I_{i-1}$ in this ordering for $i\ge2$, and at $i=1$ the same equality follows because the nonempty product is divisible by a row entry. Repeated colons give $I_n:D=I_0=(1)$. Since $D$ divides $M$, this proves $M\in I_n$, with no power needed.

Conversely, if a set $R$ of $u$ rows has $\left|\bigcup_{i\in R}S_i\right|\le2u-2$, then $M\notin\sqrt{I_n}$. Put $C=\bigcup_{i\in R}S_i$, and work over an algebraic closure. If $|C|\ge u$, fill the $u\times |C|$ submatrix on these rows and columns using a restriction of the full-support Cauchy example of width $2u-2$, with all maximal permanents zero. If $|C|<u$, use all ones in that block, so the $u$ row forms have zero product simply by degree in their $|C|$ square-zero variables. Set all entries of rows in $R$ outside $C$ to zero, and all entries of the other rows to one. Every marked entry is nonzero, but the full row product vanishes, so this point refutes radical membership.

In particular, for nested supports $S_1\subseteq\cdots\subseteq S_n$, these two arguments give the exact characterization
$$
M\in I_n\ \Longleftrightarrow\ M\in\sqrt{I_n}
\ \Longleftrightarrow\ |S_i|\ge2i-1\text{ for all }i.
$$
Thus the smallest degree of a monomial with nested row supports in $I_n$ is $n^2$ when $m\ge2n-1$. Equality is attained by the squarefree staircase using the first $2i-1$ columns in row $i$. For $m<2n-1$, take all $n$ rows in the necessity argument, which rules out every monomial even in the radical. For positive characteristic $p\le n$, the all-ones matrix gives the same negative conclusion at every width, since its maximal permanents are $n!=0$. Hence $I_n$ contains a monomial exactly in characteristic zero or greater than $n$ and at width at least $2n-1$. In these cases the staircase gives an explicit monomial of degree $n^2$. Kirkup previously constructed a monomial at this width using the product of all entries. [Kirkup, Corollary 6](https://arxiv.org/pdf/math/0510025)

For arbitrary support patterns, the unresolved converse of the row-union obstruction above is equivalent to Saxton–Yu's Conjecture L7.2 over an algebraically closed field of characteristic zero. Indeed, if that conjecture holds, every matrix nonzero on the marked entries of a pattern satisfying the row-union bounds also satisfies those bounds on its actual supports. Its full row product is nonzero, so the marked monomial belongs to the radical by the Nullstellensatz. Conversely, apply the proposed radical criterion to the actual supports of any matrix meeting the conjecture's row-union condition. The matrix must then have a nonzero maximal permanent. The nested criterion proves the converse in that support class. [Yang Yu, Conjecture L7.2](https://www.preprints.org/manuscript/202603.0035)

## 3. Exact membership for products using each column at most once

**Theorem.** Suppose $\operatorname{char}K=0$ or $\operatorname{char}K>n$. Let $M$ be a monomial of degree at most one in the variables of each column. Write $c_1\le\cdots\le c_n$ for its sorted row degrees. Then $M\in I_n$ if and only if $c_i\ge i$ for every $i$. In particular, the minimum degree in this class is $n(n+1)/2$, attained whenever enough columns are available.

**Sufficiency.** After reordering rows, select exactly $i$ of the marked columns in row $i$ and let $T_i$ be that set. The sets $T_i$ are disjoint. Write $D_i=\prod_{j\in T_i}x_{ij}$, and induct on $i$ to show $\prod_{r=1}^iD_r\in I_i$. The case $i=1$ is a row entry. For $i>1$, the induction certificate can be taken to use only $(i-1)$-permanents on columns $J\subseteq\bigcup_{r<i}T_r$. This follows by retaining the column multihomogeneous component of the monomial on both sides of any certificate.

For each such $J$, restrict the row multiplication $L_i f_{i-1}$ to the $2i-1$ variables in $J\cup T_i$. In the constant left inverse of Section 1, recover the coefficient of $y_J$. In the weighted inverse obtained by scaling all the variables in $J\cup T_i$, each input coefficient on an $i$-set $B$ receives the variable ratio
$$
\frac{\prod_{j\in J}x_{ij}}{\prod_{j\in B}x_{ij}} .
$$
All possible denominator factors in $J$ already cancel, and multiplication by $D_i$ clears the others. It follows that $D_i\operatorname{per}(X_{[i-1],J})\in I_i$, the coefficient identity of Kirkup's Proposition 5. Multiplying the induction certificate by $D_i$ now gives the assertion at step $i$. The resulting product divides $M$. [Kirkup, Proposition 5](https://arxiv.org/pdf/math/0510025)

**Necessity.** If $c_i<i$, choose a set $R$ of $i$ rows each carrying at most $i-1$ marked columns. Let $C_R$ be the marked columns whose marked row lies in $R$, and $C_{\overline R}$ the other marked columns. If a certificate existed, take its component in the target column multidegree. Each permanent then uses only marked columns, and the accompanying multiplier is independent of the selected columns of that permanent.

Now set entries between $R$ and $C_{\overline R}$, and between its complementary rows and $C_R$, to zero. The monomial $M$ survives. Every selected maximal permanent vanishes unless it uses exactly $i$ columns in $C_R$. In that case it factors as the $i$-permanent on the corresponding $R$ block times the permanent on the complementary block. Partition $C_R$ into at most $i-1$ groups by the occurrence number of each marked column within its marked row. Each group has pairwise distinct marked rows. If $i=1$, $C_R$ is empty and every projected generator is already zero. Otherwise alternate the columns within every group, by summing signed images under all such column permutations.

In every nonzero certificate term, two of the $i$ selected columns of its $R$-permanent are in the same group. The term is fixed by their transposition because the selected permanent is symmetric and the multiplier is independent of both columns. Hence the alternation kills that term, by pairing permutations with their compositions with this transposition. The same argument works in characteristic two, where the paired sum is still zero. But in the alternation of $M$, its own coefficient is $1$ from the identity permutation, with no other contribution. Indeed each group's marked rows are distinct, so its nontrivial permutations change the monomial. This contradiction proves necessity. The least possible sum of the row degrees is therefore $1+\cdots+n$. $\square$

**An exact distinction between ideal membership and the Saxton–Yu problem.** For $n\ge3$ over an algebraically closed field of characteristic zero, let $M$ mark a perfect matching on the first $n$ columns together with a matching of size $n-1$ on the remaining $n-1$ columns of an $n\times(2n-1)$ matrix. Its sorted row degrees are $1,2,\ldots,2$, so Section 3 proves $M\notin I_n$. However, $M\in\sqrt{I_n}$ is equivalent to Saxton–Yu's Conjecture L7.1 in this dimension. Indeed, a matrix with $M\ne0$ has the two asserted full term ranks. Conversely, any two blocks of those sizes and full term ranks can be relabelled to make the chosen marked matchings nonzero, by a common row permutation and independent column permutations in the blocks. The Nullstellensatz now identifies radical membership with the assertion that every such concatenation has a nonzero maximal permanent. [Yang Yu, Conjecture L7.1](https://www.preprints.org/manuscript/202603.0035)
