# Recognizing simple groups and computing finite group socles in FOLL

**Theorem.** For every finite group given by its binary Cayley table, logspace-uniform polynomial-size Boolean circuits of depth $O(\log\log n)$ decide simplicity and triviality of the solvable radical. They also output the minimal normal subgroups, the socle, and all nonabelian simple direct factors of the socle as subsets of the input labels. Here $n$ is the group order. Only unbounded fan-in AND and OR gates with input negations are needed. This answers Collins–Levet Question 8.2 for the full Cayley-table input model. [Original question](https://arxiv.org/html/2212.11247#S8).

## Short products in minimal normal subgroups

For each $x\in G$, form the conjugation-invariant set
$$
A_x=\{g x^i g^{-1}:g\in G,\ 0\le i\le n\}.
$$
It contains the identity. Choose an absolute constant $K$ large enough for the argument below and let $L$ be a power of two with $K\log_2(n+1)\le L<2K\log_2(n+1)$. Set $B_x=A_x^L$.

If $N$ is a nontrivial minimal normal subgroup of $G$, then
$$
B_x=N\qquad\text{for every }x\in N\setminus\{1\}.
$$
Certainly $A_x\subseteq N$. If $N$ is abelian, it is an elementary abelian $p$-group, and the conjugates of $x$ span it by minimality. Some subset of at most $\log_2 n$ conjugates is a basis, and every element of $N$ is a product of that many powers of those conjugates. All these powers are in $A_x$.

If $N$ is nonabelian, it is a direct product $S_1\times\cdots\times S_t$ of isomorphic nonabelian simple groups. Its simple factors are permuted transitively by conjugation in $G$, because the product of any union of factor orbits is normal in $G$. Choose a factor in which $x$ has nonidentity coordinate and choose $y$ supported in that factor with $[x,y]\ne1$, possible since the factor is centerless. Then $[x,y]$ belongs to that factor and is a product of two elements of $A_x$. For example, with $[x,y]=x^{-1}y^{-1}xy$, both $x^{-1}$ and $y^{-1}xy$ belong to $A_x$. Conjugating $[x,y]$ in $G$ places a nonidentity element in every simple factor, always in $A_x^2$.

Liebeck–Shalev's Theorem 1.1 implies that every element of a nonabelian simple group $S$ is a product of at most $C\log_2|S|$ elements from any fixed nonidentity conjugacy class, for an absolute constant $C$. Apply the theorem inside each factor to the nonidentity element just found there. Since $A_x$ is conjugation-invariant, the whole factor is contained in $A_x^{\lceil 2C\log_2|S_i|\rceil}$ after adjusting the constant. Multiplying across factors takes at most $O(\sum_i\log |S_i|)=O(\log n)$ elements of $A_x$. The identity allows padding every product to length $L$. This proves the asserted equation for each minimal normal $N$. [Liebeck–Shalev, Diameters of finite simple groups, Theorem 1.1](https://annals.math.princeton.edu/articles/11021).

## The recognition and output rules

Retain $B_x$ for $x\ne1$ precisely when it is a subgroup and every nonidentity $y\in B_x$ satisfies $B_y=B_x$. Each $B_x$ is conjugation-invariant, so a retained subgroup is normal in $G$. Every minimal normal $N$ is retained, by the short-product argument. Conversely, $B_x$ is nontrivial since $x\in A_x$, and contains some minimal normal $N$ of $G$ because it is normal. For any $1\ne y\in N$ the preceding equation gives $B_y=N$. The retention test therefore forces $B_x=N$. Duplicate sets can be eliminated using equality of their membership vectors, retaining the least label that produces each set.

The group is simple exactly when it is nontrivial and a retained minimal normal subgroup equals $G$. For the socle, let $U$ be the union of the retained minimal normal subgroups together with the identity. Their product generates the socle. One can choose at most $\lfloor\log_2 n\rfloor$ of them whose product is already the socle: start with the identity subgroup, and whenever possible adjoin a minimal normal subgroup outside the current product. Each step at least doubles the group order, and products of normal subgroups are subgroups. Thus $U^L$ is precisely the socle.

For each retained nonabelian minimal normal subgroup $N$, and each $x\in N\setminus\{1\}$, repeat the construction of $A_x^L$ using $N$-conjugation instead of $G$-conjugation, with the same ambient bound $L$. Keep the resulting set if it is a nonabelian simple subgroup. Simplicity of that subgroup is checked by the same bounded power test on its own labels. The cutoff based on ambient $n$ is valid for every smaller group. Each retained subgroup is normal in $N$. Normal subgroups of a direct product of nonabelian simple groups are products of the simple factors: if a normal subgroup has nontrivial projection onto a factor, a commutator with an element supported there gives a nonidentity element of its intersection with that factor. Therefore every retained nonabelian simple subgroup is a direct factor. Conversely for an $x$ supported in one such factor the Liebeck–Shalev bound within that factor yields exactly the entire factor. This outputs the nonabelian simple direct factors of the socle after duplicate removal.

Let $S$ be the product of the nonabelian minimal normal subgroups. The circuit can test whether $C_G(S)$ is trivial by requiring each nonidentity element of $G$ to fail to commute with some element of their union. If the solvable radical $R$ is nontrivial, then $R\cap S=1$, since a product of nonabelian simple groups has no nontrivial solvable normal subgroup. As both are normal, $[R,S]\le R\cap S$, giving $R\le C_G(S)$. Conversely, if that centralizer is nontrivial, it is normal and hence contains a minimal normal subgroup $M$ of $G$. If $M$ were nonabelian, it would lie in $S$, contradicting $C_G(S)\cap S=Z(S)=1$. Thus $M$ is abelian, so the radical is nontrivial. The centralizer test exactly recognizes the groups whose solvable radical is trivial.

## Circuit construction and uniformity

Table multiplication and inversion at given labels are constant-depth relations, including the comparisons required to convert a binary table to ternary multiplication predicates. Constructing $A_x$ uses the uniform FOLL group-power algorithm plus a constant-depth disjunction over all $g,i$. It suffices to list exponents $1,\ldots,n$ and include the identity. For the product of two subsets with membership bits $D,E$, the output bit at $z$ is
$$
\bigvee_{a,b\in G}\bigl(D(a)\land E(b)\land[T(a,b)=z]\bigr).
$$
Given the power-of-two $L=O(\log n)$, compute $A_x^L$ by $O(\log\log n)$ rounds of set squaring. The same holds when the conjugators are restricted to a dynamic subset representing a subgroup. Subgroup tests, duplicates, equality, normality and the retention criterion use a bounded number of additional layers on polynomially many membership bits. For simplicity of an internally constructed subgroup, the circuit runs the same power and retention tests restricted to its dynamic membership set: group powers are still computed in the original group. The number of serial applications of these stages is constant. All tuple indices, gate copies and squaring levels can be generated in logarithmic work space. Binary table validity can also be checked at constant depth if a total language is desired. [Barrington–Kadau–Lange–McKenzie, group powering](https://doi.org/10.1006/jcss.2001.1764).

The proof uses the classical class-covering theorem and applies it through Boolean products of explicit subsets. Collins and Levet note that unrestricted normal-closure membership was an obstacle to simplicity recognition. The test here computes bounded sets of products and recognizes precisely the minimal normal subgroups using closure and the retained-set comparisons. It does not assert that every bounded product set equals the normal closure of its generator. The manuscript is an informal proof. A targeted search found the explicit question and the classical covering theorem, and did not establish priority for this circuit construction.
