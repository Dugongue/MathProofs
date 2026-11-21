# Frobenius roots of constant-depth formulas with bounded interfaces

**GP-0601, restricted class.** Fix a prime $p$, an interface bound $k$, and a depth bound $h$. Let $F=G^p$ be represented by a size-$s$, depth-$h$ arithmetic formula over an infinite perfect field $K$ of characteristic $p$. Addition and multiplication can have unbounded fan-in. For each gate $v$, let $\partial v$ be the set of variables with at least one occurrence in the subtree at $v$ and at least one occurrence outside that subtree. Suppose that at each internal gate the union of the children's boundaries has size at most $k$. Then $G$ has a formula of size $s^{O_{p,k,h}(1)}$ and depth $O(h+1)$. The construction uses the $p$-th roots of scalar leaves and a polynomial-size grid of distinct field constants.

## Proof

For the polynomial $F_v$ of a gate $v$, keep the monomials whose exponents on variables outside $\partial v$ are divisible by $p$. For every $\alpha\in\{0,\ldots,p-1\}^{\partial v}$, keep a sector $R_{v,\alpha}$ by taking the monomials with remainder $\alpha$ and replacing $c x^{pu+\alpha}$ by $c^{1/p}x^u$. Here $\alpha$ is padded by zero outside the boundary. The inverse Frobenius on $K$ is a field homomorphism, so additions and products of coefficients commute with this operation. For constant leaves the only sector is the scalar root. For a variable leaf the sector with remainder 1 is the constant 1 if the variable belongs to the boundary. Otherwise the only sector is zero.

At an internal gate let $I$ be the union of the child boundaries. Any variable of $\partial v$ occurs at a child and outside that child, so $\partial v\subset I$. Extend all child residues by zero on $I$. A monomial omitted at a child has a nonzero residue in a variable occurring nowhere outside that child. Such an exponent cannot be repaired at a product gate. At an addition gate an omitted monomial still has that nonzero interior residue. Thus child sectors retain all contributions needed by the parent.

For an addition gate, add child sector polynomials with the same extended residue and discard each sector whose residue on $I\setminus\partial v$ is nonzero. For a multiplication gate, first form
$$
P(x,z)=\prod_{w\text{ child}}\left(\sum_{\alpha}R_{w,\alpha}(x)z^\alpha\right).
$$
For each exponent $\rho$ in the $z$ variables, discard its contribution unless $\rho\equiv0\bmod p$ on $I\setminus\partial v$. Multiply the coefficient of $z^\rho$ by $x^{\lfloor\rho/p\rfloor}$, with the floor taken separately on each coordinate of $I$. Add the result to the parent sector of residue $\rho\bmod p$ on $\partial v$. This accounts for precisely the carry when adding exponents.

There are at most $k$ auxiliary variables, of degree at most $(p-1)s$ each. Evaluate $P$ on a tensor grid of $(p-1)s+1$ distinct scalars in each auxiliary variable. Each evaluation is a layer of linear combinations followed by an unbounded-fan-in product. Invert the tensor Vandermonde matrix to obtain each coefficient by a linear combination of these evaluations. In characteristic $p$ the matrix is invertible because grid points are distinct. Recover parent sectors using one more product layer for the carry monomials and one sum layer. Each monomial can use repeated factors with $O(ks)$ wires. Thus each gate update has constant depth and size polynomial in $s$. Sharing gives a depth $O(h+1)$ circuit of polynomial size, and unfolding the constant-depth polynomial-fan-in circuit yields a formula of polynomial size.

At the root the boundary is empty, and since $F=G^p$ all of its monomials are kept. The unique root sector is $G$.

**Scope.** Bounded interfaces allow arbitrarily many variables, for instance a product of disjoint-variable subformulas each with bounded interfaces. The theorem uses an infinite field, a formula, and an interface bound. [Bhargav, Dwivedi and Saxena, factoring survey](https://arxiv.org/html/2506.19604v2).
