# Linear-dimensional evaluations of free nonassociative circuits

## GP-0658

There is an explicit unital algebra of dimension $2d$ over a purely transcendental extension of any field $F$ that detects every nonzero free nonassociative polynomial with coefficients in $F$ and degree at most $d$. It works both with commutative multiplication and with ordered multiplication. Specializing the multiplication table along with the input gives a randomized black-box identity test of polynomial evaluation cost over any field with sufficiently many elements, or over a suitably large finite extension. Any universal algebra over any field for all such degree-$d$ polynomials has dimension at least $d-1$ in the commutative case and at least $d$ in the ordered case. Thus the extension-field construction is within a factor of two of the optimal dimension, up to an additive constant.

### An explicit generic table and its evaluation

Let $m=2d-1$ and start with a basis $e_1,\ldots,e_m$. Set
$$
e_i e_j=\sum_{k=1}^m T_{ij,k}e_k
$$
with independent scalar indeterminates $T_{ij,k}$. For a commutative algebra label the parameters by the unordered multiset $\{i,j\}$, so $T_{ij,k}=T_{ji,k}$. Form the algebra over $F(T)$ and adjoin a unit $1$ in one extra dimension. Its multiplication uses at most $O(d^3)$ field operations. For each input variable $x_j$, substitute $\sum_i Y_{j,i}e_i$ with independent scalar variables. Fix a nonzero coefficient of a free monomial $w$ of degree $k$ in the input polynomial, with $1\le k\le d$.

Every rooted labeled subtree of $w$ itself represents a free monomial. Assign a different basis color to each distinct such monomial. There are at most $2k-1$. In the expansion of the evaluation of $w$, take the summand using these colors at all leaves and internal nodes. It is a monomial in the $T$ and $Y$ variables in the output coordinate for the root color. Repeated identical subtrees use the same color. The multiplicity of a table symbol in this chosen monomial reflects repeated use of its production rule, and every output color used for an internal node has exactly one production rule. Each leaf color has exactly one variable label. No color represents both a leaf and an internal subtree.

Any other expansion yielding the same scalar monomial and output coordinate must obey those same productions, read from the root. Because all rules decrease subtree size, they specify a unique free monomial after unfolding. In the commutative version the unordered pair of child colors gives the same free monomial regardless of order. In a fixed representative of that free monomial, the matching coloring is unique. Whenever the two child monomials differ, the color of each is specified by that monomial. Whenever they agree, the matching colors are equal. Thus there is exactly one contribution from $w$ and none from competing monomials, even in characteristic two. A nonzero constant coefficient can be detected separately by evaluating at zero.

The surviving output coordinate is therefore a nonzero ordinary polynomial in $T,Y$ of degree at most $2d-1$. This also proves nonvanishing as a polynomial in $Y$ over $F(T)$, giving the universal algebra in the statement. For an effective randomized evaluation, specialize $T$ and $Y$ independently from a set of at least $4d$ elements. The usual polynomial identity lemma bounds failure by $(2d-1)/(4d)$. A query uses the specialized table and the corresponding numeric input tuple. Explicit dimension and coefficient count are both polynomial in $d$. For a fixed finite base field, an extension of logarithmic degree can be constructed by deterministic search over monic polynomials, and arithmetic in it is polynomial time. The guarantee is for the one explicit universal algebra over the transcendental extension, or for the randomized family of table specializations. It does not assert that one predetermined numeric table over the original field works for every input.

### Matching linear lower bounds

In an ordered free algebra on $m+1$ different variables, alternate the fully left-associated word over all permutations of the variables. The sum is a nonzero free polynomial, since its words are distinct with coefficients $1$ or $-1$. Evaluated on an $m$-dimensional algebra this becomes an alternating multilinear function of $m+1$ vectors, hence vanishes. The alternating assertion works in characteristic two because terms pair off when two inputs are equal. Thus an ordered universal algebra for degree $d$ must have dimension at least $d$.

In the commutative free algebra add a distinguished marker $y$ and alternate the words
$$
(\cdots((y x_{\pi(1)})x_{\pi(2)})\cdots)x_{\pi(m+1)}.
$$
The free words are distinct, since the bottom pair is identified by the marker, and each successive leaf is recoverable along the left-associated nesting. When evaluated on an $m$-dimensional algebra the expression is again an alternating multilinear function in the $m+1$ ordinary inputs and therefore vanishes. Its degree is $m+2$, giving dimension at least $d-1$. These lower bounds concern universal degree detection, with circuit size large enough to express the displayed identities.

The earlier cubic-dimensional construction records an ordered leaf interval and a depth. Here a generic multiplication table records the few subtree productions of any one free monomial and supplies the linear dimension bound over an explicit extension. [Mukhopadhyay–Ramya–Shastri, Section 5](https://drops.dagstuhl.de/storage/00lipics/lipics-vol353-approx-random2025/html/LIPIcs.APPROX-RANDOM.2025.56/LIPIcs.APPROX-RANDOM.2025.56.html#S5)
