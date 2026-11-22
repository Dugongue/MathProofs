# Exact number of linear constraints needed for semisimple nonconjugacy

Let $A,B$ be nonconjugate matrices of size $n$ diagonalizable over an algebraic closure of their field. For an eigenvalue $i$ write $a_i,b_i$ for its source and target multiplicity, allowing zero. Set
$$
 m=\min_{a_i\ne b_i}\min(a_i,b_i).
$$
Every ordinary Polynomial Calculus refutation of $XA=BX$, $XY=YX=I$ in any input bases uses at least
$$
 (m+1)(n-m)
$$
distinct forward entries of $XA-BX$. In diagonal coordinates over a splitting field, this number is **attainable** as the exact minimum count of forward equations used, with the inverse equations freely available. Even choosing arbitrary scalar linear consequences of $XA=BX$ as the forward inputs cannot reduce this count. This is an exact input-count theorem. Sparse size charges each monomial of each used input, as well as subsequent proof lines. [Published question and encoding](https://arxiv.org/html/2305.19320#S7.SS3)

## Proof

It suffices for the lower bound to work over the algebraic closure and pass to eigenspace coordinates for the argument, keeping every original forward entry as one linear functional. The full intertwiner space $H$ is the coordinate space spanned by the cells at which the target row and source column have the same eigenvalue. Any set of $t$ linear consequences of the forward equations has a common kernel $L$ containing $H$, with codimension at most $t$ in the matrix space. If there is a refutation using those inputs and the inverse equations, all matrices in $L$ must be singular.

Degenerate $L$ by independent row and column diagonal scalings with distinct additive entry weights, using the pivot-basis argument in the [dense-coordinate proof](DenseConjugacy.md). Its limit $L_0$ is a coordinate subspace of the same dimension and is still entirely singular. It contains $H$. For example, every unit of $H$ belongs to $L$, so its only nonzero position is a pivot position for $L$: in a basis in reduced row-echelon form the first nonzero coefficient of every nonzero vector lies at a pivot. Thus every missing cell of $L_0$ is a crossing between unequal labels.

The pivot graph has no perfect matching, since permutation matrices are invertible. By Hall's theorem its missing cells contain a rectangular set $U\times W$ of target rows and source columns with $|U|+|W|=n+1$. Indeed some set of target rows has fewer neighbors than its size; take the required number of nonneighboring source columns. Let $I$ be the set of labels occurring in $U$. No column of $W$ has a label in $I$. Hence $|U|\le b_I$ and $|W|\le n-a_I$, where $a_I,b_I$ are total multiplicities on $I$. It follows that $b_I>a_I$. At least one label in $I$ has positive gap $b_i-a_i$, and at least one outside $I$ has negative gap, by equality of the total sizes. In particular $a_I\ge m$ and $n-b_I\ge m$. We now have
$$
 |U|\ge a_I+1\ge m+1,\qquad |W|\ge n+1-b_I\ge m+1.
$$
For two integers of sum $n+1$, both at least $m+1$, the smallest possible product is $(m+1)(n-m)$ by concavity. Therefore $t\ge\operatorname{codim}L_0\ge |U||W|\ge(m+1)(n-m)$.

For attainment, choose a mismatched label whose smaller multiplicity is $m$. If its target multiplicity exceeds its source multiplicity $m$, take $m+1$ rows of that label and all $n-m$ source columns of other labels. If its source multiplicity is larger, transpose these roles. Requiring every cell of this rectangle to vanish uses exactly the proposed number of displayed forward equations. Every such matrix is singular by Hall's condition. Equivalently, the $m+1$ chosen rows can only use $m$ columns, or vice versa. By the Nullstellensatz, the equations together with both inverse equations admit an ordinary PC refutation. This proves attainment without imposing a degree bound.

## A sparse size consequence for growing gaps

Suppose $m\ge c n$ for a fixed $c>0$. Every coordinate presentation requires $\Omega(n^2)$ monomial occurrences just among its forward inputs. For example, every used nonzero linear equation has at least one monomial. In displayed diagonal coordinates, if any multiplicity difference is nonzero in the coefficient field, that eigenvalue block has a rectangular trace discrepancy. The trace construction in the [sparse conjugacy proof](SparseConjugacy.md) gives size $O(n^2\log(2n))$ even if the gaps grow. Thus the sparse exponent is two for this class, over every characteristic, including all characteristic-zero displayed diagonal pairs with $m\ge c n$.

For integral complementary idempotents an explicit dense presentation makes each forward input have $\Omega(n)$ terms when both complementary ranks are proportional to $n$. This explains the cubic worst-case exponent on unequal traces and gives a lower bound in any characteristic even when both traces coincide. [Dense family and proof](DenseConjugacy.md)
