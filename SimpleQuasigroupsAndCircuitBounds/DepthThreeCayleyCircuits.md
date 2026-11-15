# A top fan-in lower bound for depth-three Group Isomorphism

Let $n$ be the group order. For infinitely many $n$, there is a constant $c>0$ such that every alternating depth-three Boolean circuit for Group Isomorphism on pairs of valid binary-encoded Abelian Cayley tables of exponent dividing nine, with $s$ gates and output fan-in $t$, satisfies
$$
(s+2N+2)^t\ge 2^{c\sqrt n},
$$
where $N=2n^2\lceil\log_2 n\rceil$ is the number of input bits. In particular, for each fixed $0<\varepsilon<1/2$, circuits in this model with $t\le n^{1/2-\varepsilon}$ need $2^{\Omega(n^\varepsilon)}$ gates. Both alternating gate orders are covered and bottom fan-in is arbitrary. The proof uses the random relabeling and partial-table completion lower bound from the companion paper. [CNF and DNF lower bounds](GroupIsomorphismCNF.md)

## 1. Carrying the depth-two bounds through the extra layer

The previous proof gives, at the same orders $n=3^k$ for all sufficiently large $k$, a lower bound $2^{c\sqrt n}$ for both CNFs and DNFs. All hard inputs are valid Cayley tables of groups of exponent dividing nine, with identity label zero. The two polarity proofs can use different fixed second tables because the present circuit has to work on every pair in the promise.

For an OR of $t$ CNFs, write $b_i$ for the number of distinct clauses in the $i$-th CNF. For each tuple of choices of one clause per CNF, form the disjunction of the chosen clauses. The conjunction of all these disjunctions is an equivalent CNF. If one original CNF holds, each tuple contains a true clause. If every original CNF fails, there is a tuple of false clauses, so the new CNF also fails. Shared bottom gates do not affect the bound $b_i\le s+2N+2$, which includes all input literals and constants used directly. Thus there are at most $\prod_i b_i\le (s+2N+2)^t$ clauses. A top AND of DNFs gives the dual DNF with at most that many terms. The original bounds give the asserted tradeoff. When $t\le n^{1/2-\varepsilon}$, the size lower bound survives subtracting the polynomial $2N+2$.

## 2. Polynomial depth-three circuits on the two-group promise

The random-relabeling hard pair in the exponent-nine lower bound is
$$
K=C_3^k,\qquad J=C_9\times C_3^{k-2}.
$$
On binary-encoded tables with identity label zero, let $E(T)$ hold if every element has cube equal to zero. This is the polynomial-size CNF formed by the clauses
$$
[T(x,x)\ne z]\lor [\operatorname{bit}_j(T(z,x))=0]
$$
for every label $x,z$ and bit $j$. The inequality against the constant $z$ is a disjunction of bit literals. For each $x$ the clauses at $z=T(x,x)$ enforce $T(T(x,x),x)=0$. Hence $E(T)$ holds on exactly the relabelings of $K$ in the two-group promise.

For a pair of inputs from the promise, isomorphism is the disjunction of $E(T_1)\land E(T_2)$ and $\neg E(T_1)\land\neg E(T_2)$. The first is a CNF. The second is a polynomial-size DNF since a conjunction of two polynomial-size DNFs can be expanded using a product of their term counts. A DNF term is also a CNF of unit clauses, giving an OR of polynomially many polynomial-size CNFs. An OR of CNFs for nonisomorphism is obtained the same way, by disjoining the two mismatched pairs of truth values. De Morgan duality therefore gives a polynomial-size AND of DNFs for isomorphism on the same promise. This verifies that arbitrary top fan-in changes what can be proved using this particular pair, even when both input tables are relabeled independently.

## 3. Polynomial depth-three circuits on the canonical rank family

The same phenomenon holds for a different depth-two hard promise. In Grochow–Kardeş–Levet's Construction 4.4 the elements of $G_M$ have canonical labels $(u,z)\in\mathbb F_2^k\times\mathbb F_2^k$, where $M$ is a $k\times k$ binary matrix and the order is $2^{2k}$. The square of $(u,0)$ has label $(0,Mu)$. Thus the table contains, as a single designated input bit for each $i,u$, the Boolean value $a_i(u)=(Mu)_i$. Isomorphism for two such tables is equality of their matrix ranks. [Construction 4.4 and Proposition 4.5](https://arxiv.org/html/2608.26257v2#S4.SS2)

For a fixed $r$, choose sets $I,J$ of $r$ row and column indices, respectively. Construct a CNF with the following two collections of clauses:

1. For every nonzero $u$ supported on $J$, require $\bigvee_{i\in I} a_i(u)$. This says that the chosen $r\times r$ minor is invertible, since its kernel is trivial.
2. For every $u\in\mathbb F_2^k$ and every row $i$, require $a_i(u)\lor\bigvee_{j\in I}\neg a_j(u)$. This says that every vector annihilated by the chosen rows is annihilated by all rows. Equivalently all rows belong to the span of the chosen rows, by taking orthogonal complements of the kernels.

The conjunction asserts rank exactly $r$ and that $I,J$ select an invertible minor. It works for $r=0$ with the first collection empty. Conversely every rank-$r$ matrix has such a minor, and the selected rows span the row space. Disjoining over $I,J$ is an OR of CNFs for rank $r$, using at most $2^{O(k)}$ gates in total. For the comparison of two matrices, choose $r$ and a minor in each matrix, merging the two CNFs. To test unequal ranks, choose $r_1\ne r_2$ instead. Both tests cost $2^{O(k)}$, polynomial in the group order, so equal rank also has a polynomial-size AND of DNFs by duality. The circuit uses the canonical cell addresses for the squares.

## Scope

The fan-in theorem is an informal extension of the partial-table proof. The two upper bounds concern explicit promises used for depth-two lower bounds. For unrestricted depth-three Group Isomorphism, the top fan-in may be polynomial with arbitrary exponent, and Question 7.2 remains open here. [Question 7.2](https://arxiv.org/html/2608.26257v2#S7)
