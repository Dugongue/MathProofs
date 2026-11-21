# Bit-polynomial reconstruction of grouped read-once formulas

## GP-0685

There is a deterministic algorithm with a polynomial number of exact rational oracle queries, polynomial bit lengths of query points, and polynomial bit complexity in the number of variables and the answer lengths. It reconstructs a valid grouping and read-once formula over the rationals. The returned grouping can use singleton groups. The original grouping can be nonidentifiable, since $x+y$ can be written using either one group or two.

Expand each unknown affine input block as a read-once formula in its variables, using affine operations and constants. The disjointness of the original blocks makes the resulting polynomial read-once, with degree at most $n$ and individual degrees at most one. Any first derivative is also read-once, since it is a product of the disjoint sibling subformulas at multiplication nodes on the path from that variable to the root, with constant factors absorbed.

### A common point for all active variables

Use the two-parameter generator $G_i(y,z)=zL_i(y)$, where $L_i$ are the Lagrange polynomials at $1,\ldots,n$. Minahan and Volkovich, Theorem 20, prove that it preserves nonzeroness of any read-once polynomial, including nonzero constants. Substitute it into the product of all nonzero first derivatives of $f$. That product is nonzero and has bidegree at most $(n^3,n^2)$. A grid larger than these bounds in each coordinate contains a point at which every active derivative is nonzero. Evaluate first derivatives by querying $f$ at the generated point and its shifts by coordinate unit vectors. Pick the point with the largest number of nonzero derivatives. The maximum is the number of active variables. Call the resulting point $\alpha$. It stays a valid common nonvanishing point for every restriction that fixes some coordinates to $\alpha$. [Minahan–Volkovich, Definition 14 and Theorem 20](https://drops.dagstuhl.de/storage/00lipics/lipics-vol079-ccc2017/LIPIcs.CCC.2017.32/LIPIcs.CCC.2017.32.pdf)

### Recovering each split

Let $g$ be the current restriction. Write $g_0=g(\alpha)$, $g_i=\partial_i g(\alpha)$ and $g_{ij}=\partial_i\partial_j g(\alpha)$, all obtainable by evaluations at $\alpha$ and at shifts by at most two distinct coordinate vectors. On at least two active variables a read-once function has a top structural split as a sum of functions on two disjoint nonempty sets or as a product on such sets plus a constant. To see this, first eliminate inactive and constant subtrees. Skip any top unary affine operations, absorbing scalar multiples into the two children. The top constant can be absorbed into one child in the additive case. The same structural observation applies to any restriction.

First form the graph with edge $ij$ when $g_{ij}\ne0$. Its components partition additive summands if the graph is disconnected. Indeed, an additive split gives no cross edges, and a product-plus-constant split gives all cross edges because every active first derivative is nonzero. Induction on the additive children's variable counts shows that their components also split additively. Taking one component $L$ and its complement $R$ therefore gives
$$
g=g|_L+g|_R-g_0,
$$
where $g|_S$ fixes variables outside $S$ to $\alpha$.

If the graph is connected, there is a product-plus-constant split $g=A B+c$ and $A(\alpha),B(\alpha)\ne0$. Test each candidate $c'=g_0-g_i g_j/g_{ij}$ coming from a nonzero $g_{ij}$. The true $c$ is given by every pair across the split. For a candidate form the graph with edge $ij$ when $g_{ij}(g_0-c')\ne g_i g_j$. For the true $c$, every cross pair is a nonedge. For any other $c'$, every cross pair is an edge, giving connectivity. Thus the disconnected graph identifies the true shift.

Its components refine $g-c$ into factors. The following induction justifies using any union of components as one side of a factorization. For a read-once $h$ with nonzero value and every first derivative nonzero at $\alpha$, connect $ij$ when $h_{ij}h_0\ne h_i h_j$. In the case $h=A+B$, every cross edge is present. For $h=A B+e$ the cross difference is $e A_iB_j$. It is nonzero when $e\ne0$, giving connectivity. When $e=0$, there are no cross edges. On each side the edges are exactly those from the same rule for that factor: both terms in the difference acquire the same nonzero squared value of the other factor. Induct on the factors. Apply this to $h=g-c$ and choose one component $L$ and its complement $R$. The identity now used is
$$
g=c+\frac{(g|_L-c)(g|_R-c)}{g_0-c}.
$$
The denominator is nonzero. Recur on the two restrictions. A constant restriction and a single active variable are reconstructed from one or two evaluations. Each recursion node uses disjoint variable supports in its two children, so the output has only one occurrence of every active input variable.

### Bit costs

The Lagrange generators on the polynomial-size integer grids have rational bit length polynomial in $n$. This follows directly from the $n-1$ numerator and denominator factors defining each $L_i$. All oracle calls are on these small points or their coordinate shifts. There are $O(n)$ recursion nodes, and all arithmetic for each comparison, candidate shift or output gate is a fixed number of rational operations on original query values, even deep in the recursion. In particular recursion never evaluates the previously recovered subexpressions to obtain a new coefficient. Every output constant has bit length polynomial in the maximum oracle answer length.

For an ordinary input bit bound in terms of a hidden formula of encoding length $B$, every such answer has bit length polynomial in $B$ and the query length. After expanding the formula, each scalar or input occurrence divides the denominator through at most one copy of its original denominator, because there is no reuse of formula nodes. A common denominator is their product, and a bound on the numerator follows from at most $2^{O(B)}$ expansion terms with polynomial-bit products. This gives the claimed bit-polynomial oracle algorithm and coefficient-size bound. The preceding argument concerns formulas using addition, multiplication and rational scalar operations, with no division gates involving the input variables.
