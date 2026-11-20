# DNF lower bound for promised abelian group isomorphism

**Theorem.** For each $k\ge 1$, put $N=4^k$. Any Boolean DNF deciding isomorphism of two valid abelian Cayley tables of order $N$ needs at least
$$
\prod_{j=1}^{k}(2^j-1) \ \ge\ 2^{k(k+1)/2-2}
$$
terms. The bound holds with the second table fixed to a coordinate-labeled copy of $(\mathbb Z/4\mathbb Z)^k$ and when the first table is promised to have exponent dividing four. Thus the DNF size is $N^{\Omega(\log N)}$ in the promise of Question 7.3. [Grochow–Kardeş–Levet, Question 7.3 and Proposition 4.5](https://arxiv.org/html/2608.26257v2#S7)

## A family of valid tables

Use the construction of Grochow, Kardeş and Levet, Proposition 4.5. Let $V=\mathbb F_2^k$. Write $u\odot v$ for coordinatewise multiplication. For each binary matrix $M$ take the group $G_M$ on $V\times V$ with
$$
(u,z)\cdot_M(v,w)=(u+v,\ z+w+M(u\odot v)).
$$
Bilinearity gives associativity, symmetry gives commutativity, and $(0,0)$ is the identity. A square is $(0,Mu)$, so every element has fourth power equal to the identity, which also supplies inverses. The squaring image has size $2^{\operatorname{rank}M}$. By the classification of finite abelian groups of exponent dividing four, $G_M\cong G_I$ exactly when $M$ is invertible. Label a pair by its $2k$ coordinate bits. This is a valid binary Cayley table under the question's encoding. Therefore every test input $(G_M,G_I)$, including when $M$ is singular, satisfies the promise. [Grochow–Kardeş–Levet, Construction 4.4 and Proposition 4.5](https://arxiv.org/html/2608.26257v2#S4.SS2)

For a fixed pair of input labels, each bit of a table entry is either constant or an affine linear function of a single row of $M$. More explicitly the $i$-th bit of the second coordinate is $z_i+w_i+M_{i,*}\cdot(u\odot v)$. Thus each literal restricted to the slice either has a constant truth value or imposes one affine equation on a single row. Each DNF term that is true for at least one matrix has a satisfying set on the slice of the form
$$
\mathcal C=A_1\times\cdots\times A_k,
$$
where each $A_i$ is a nonempty affine subspace of possible $i$-th rows. These row choices are independent because the term is a conjunction. Every matrix in $\mathcal C$ must be invertible, since a term that accepts a singular matrix would give an incorrect answer on a valid promised input.

## Size of one term

Pick $P\in\mathcal C$. Right multiplication by $P^{-1}$ preserves invertibility, maps $\mathcal C$ bijectively to another product of affine row sets, and sends $P$ to the identity. Write the normalized row sets as $e_i+U_i$ for vector subspaces $U_i\le\mathbb F_2^k$.

For any $u\in U_i$, use $e_i+u$ in row $i$ and keep all other rows equal to those of the identity. The determinant is $1+u_i$. Every choice is invertible, so $u_i=0$. For distinct $i,j$, choose $u\in U_i$ and $v\in U_j$, and change just those two rows of the identity. The determinant is the determinant of the principal $2\times2$ block, namely $1+u_jv_i$. Consequently one cannot have both a vector in $U_i$ with $j$-th coordinate nonzero and a vector in $U_j$ with $i$-th coordinate nonzero.

Let $E_i$ be the set of coordinates that are nonzero for some vector of $U_i$. Coordinate restriction to $E_i$ is injective on $U_i$. The last two observations show that $i\notin E_i$ and that each unordered pair of distinct coordinates contributes to at most one of the $E_i$. Hence
$$
\sum_i\dim U_i\le\sum_i|E_i|\le\binom{k}{2},\qquad
|\mathcal C|\le 2^{\binom{k}{2}}.
$$

## Counting terms and attaining the bound on the slice

The invertible matrices are all accepted, and no term accepts more than $2^{\binom{k}{2}}$ of them. Counting linearly independent rows gives
$$
|\mathrm{GL}_k(\mathbb F_2)|=\prod_{i=0}^{k-1}(2^k-2^i)
=2^{\binom{k}{2}}\prod_{j=1}^k(2^j-1).
$$
Their cover therefore has at least $\prod_{j=1}^k(2^j-1)$ terms. For the stated estimate, use $\prod_{j=1}^{k}(1-2^{-j})\ge 1/4$. Indeed, the factor at $j=1$ is $1/2$, and the product of the remaining factors is at least $1-\sum_{j=2}^k2^{-j}\ge 1/2$. This proves the theorem.

On this particular family $(G_M,G_I)$, the lower bound equals the minimum DNF term count. The subgroup $U$ of upper unitriangular matrices has size $2^{\binom{k}{2}}$, and the translates $UP$, for one $P$ per coset, partition $\mathrm{GL}_k(\mathbb F_2)$. Each $UP$ is a product of affine sets of rows. Any affine equation on row $i$, such as $M_{i,*}\cdot a=\epsilon$, is expressible by a literal on the $i$-th bit of the second coordinate of the table entry $(a,0)\cdot_M(a,0)=(0,Ma)$. Thus each translate has a defining conjunction on the family. The OR of these conjunctions has exactly the claimed number of terms.

The proof is written mathematics. The finite replay checks the table construction, the row-product bound, and the matching coset cover in small dimensions.
