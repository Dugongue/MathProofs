# Binary permutation containment by parity and integral transport

Let $G$ generate the source code and let $H$ check the target code, both of length $r$. Group the equal columns of $G$ into $s$ types $u_i$ of multiplicities $m_i$. Group the equal columns of $H$ into $t$ types $v_j$ of multiplicities $n_j$. Retain the zero column type if present. For $r=0$ the empty permutation is the unique witness. In the sequel assume $r>0$.

**Theorem.** Write $u,v$ for the affine ranks of the two type sets over $\mathbb F_2$ and put
$$
\kappa=(s-1)(t-1)-uv .
$$
One can find a permutation taking the source code into the target, or decide none exists, in deterministic $2^\rho\operatorname{poly}(r)$ bit time and polynomial space. Here $\rho\le\kappa$ is a dimension obtained by one Gaussian elimination and projection, specified below. Put $M=\min\{\prod_i(m_i+1),\prod_j(n_j+1)\}$. One can count all witness permutations in $O^*(M\,2^{\min(uv,\kappa)})$ bit time and polynomial space. The decision and search algorithms take polynomial time in either of the following cases.

- Each set of distinct column types is affinely independent.
- Every source multiplicity is at least $t-1$ and every target multiplicity is at least $s-1$.

Changing generator or parity-check bases preserves the parameters. Neither condition puts a bound on the dimension gap. For example, take $r=4d$ and let the columns on each side consist of four copies of each of the $d$ coordinate vectors. The source is a direct sum of repetition codes of length four. The target is a direct sum of even-weight codes of length four. Their dimensions are $d$ and $3d$ and the first case applies. The same case decides every multiplicity pattern on those two affinely independent type sets.

## The parity table

A permutation defines a nonnegative integer table $X_{ij}$ counting source coordinates of type $i$ sent to target coordinates of type $j$. Every integer table with margins $m,n$ lifts to an actual permutation by pairing labeled positions in each cell. If $U,V$ have columns $u_i,v_j$, the matrix of dot products between permuted generator rows and parity-check rows is $U(X\bmod2)V^\mathsf{T}$. Thus an exact feasible parity table $E$ is characterized by
$$
 UEV^\mathsf{T}=0,\qquad E\mathbf1=m\bmod2,\qquad
 E^\mathsf{T}\mathbf1=n\bmod2,\qquad
 |E_{i,*}|\le m_i,\quad |E_{*,j}|\le n_j.
$$
The first three equations are binary and the last two families use integer Hamming weight. For the converse, take the entries of $E$ in $\{0,1\}$. Subtract their row and column sums from the prescribed margins, and divide both residual margins by two. They are nonnegative integers of equal total. A greedy transport on the complete bipartite graph supplies an integer table $Y$ with these residual margins: repeatedly transfer the smaller of the two current positive margins and advance each exhausted index. The table $X=E+2Y$ lifts to a witness.

## The search exponent

The homogeneous row and column sum constraints give $L_s\otimes L_t$, where $L_s,L_t$ are the even-weight subspaces in the two type spaces. For example the free upper-left $(s-1)\times(t-1)$ entries determine the last row and column. On this space the homogeneous syndrome map is $U|_{L_s}\otimes V|_{L_t}$. Its two factor ranks are $u,v$, since the images are spanned respectively by $u_i+u_s$ and $v_j+v_t$. Its rank is therefore $uv$. If the affine system is consistent, its translation space $N$ has dimension exactly $\kappa$.

**An exact classification for saturated multiplicities.** Write $C$ for the source code, $D$ for the target and $\mathbf1$ for the all-ones word. The affine equations are consistent precisely when
$$
 \mathbf1\in C\ \Longrightarrow\ \mathbf1\in D,\qquad
 D\subseteq\mathbf1^\perp\ \Longrightarrow\ C\subseteq\mathbf1^\perp .
$$
In particular these two implications completely decide containment if every $m_i\ge t-1$ and every $n_j\ge s-1$.

To prove this, put $A=\operatorname{im}U$, $A_0=U(L_s)$ and similarly $B,B_0$ for $V$. The syndrome $M_0$ of the identity permutation is one particular syndrome allowed by the affine margins; the set of all such syndromes is $M_0+A_0\otimes B_0$. Since every $u_i$ has the same image in $A/A_0$, this quotient is zero or one-dimensional. In the latter case its unique nonzero functional takes value one on every $u_i$, exactly the condition $\mathbf1\in C$. Contracting $M_0$ with that functional gives $\sum_jn_jv_j$, which vanishes exactly when $\mathbf1\in D$. On the other side the quotient functional exists exactly when $\mathbf1\in D^\perp$, and contracting then gives $\sum_i m_i u_i$, which vanishes exactly when $C\subseteq\mathbf1^\perp$. The identities $(A_0\otimes B)\cap(A\otimes B_0)=A_0\otimes B_0$ and $\mathbf1\in D^\perp\iff D\subseteq\mathbf1^\perp$ complete the proof. Saturated multiplicities make the Hamming inequalities automatic as shown below.

Call a row critical when $m_i<t-1$, and a column critical when $n_j<s-1$. A noncritical row automatically meets its capacity. If $m_i=t-1$, its parity precludes the only larger possible weight $t$; for $m_i\ge t$ the bound is immediate. The same argument applies to columns. Let $B$ be the union of all entries of critical rows or columns, and put $\rho=\dim(N|_B)$. Solve the affine linear equations once. Keep a basis of full kernel vectors whose restrictions form a basis of $N|_B$ by elimination. Adding any subset of those lifts to one particular solution visits every projected solution exactly once. Test the Hamming bounds and apply greedy transport to the first feasible table. Keeping a binary counter and one current table gives the space bound. If $\kappa=0$ or $B$ is empty this requires only linear algebra and one lift.

More generally, put $a=s-1-u$, $b=t-1-v$. The exponent before projection is $a(t-1)+b(s-1)-ab$, giving singly exponential search whenever the two affine dependency dimensions $a,b$ are bounded, with arbitrary multiplicities.

**Removing paired repetitions.** When $s,t\ge2$, one can reduce the length to at most $st$ in polynomial time while preserving existence and lifting witnesses. Whenever $r>st$, choose a source type with $m_i>t$ and a target type with $n_j>s$, which exist by averaging. Delete two coordinates of the chosen type on each side, independently. All types stay present. The affine parity equations are unchanged, and the two affected Hamming bounds were automatic and remain automatic. Thus every feasible parity table survives. A witness of the reduced instance extends by matching the two deleted source coordinates to the two deleted target coordinates, whose combined binary syndrome is zero. Iteration gives the bound. If $s=1$ or $t=1$, every permutation has the same syndrome, so checking the identity decides the instance in polynomial time. This reduction preserves decision and witness recovery. Its counts can change.

## Exact counting

For a fixed feasible parity table $E$, count labeled bijections by inclusion-exclusion over the available target positions $X$. If $d_j$ positions of type $j$ are available, the number of ways of choosing the targets of the source positions of type $i$ is
$$
 p_i(d)=m_i! [z^{m_i}]\prod_j\sum_{0\le l\le d_j,\ l\equiv E_{ij}\pmod 2}
                     \binom{d_j}{l}z^l .
$$
Polynomial multiplication truncated at $r$ computes this number in polynomial time. Choices for distinct source types are independent until we require their union to cover the target. Since the sizes sum to $r$, full coverage forces disjointness. Inclusion-exclusion therefore gives the count for $E$ as
$$
 \sum_{0\le d_j\le n_j}(-1)^{r-\sum_jd_j}\prod_j\binom{n_j}{d_j}\prod_i p_i(d).
$$
Every permutation contributes through exactly one $E$. Transposing the tables interchanges the two sets of multiplicities, so summing over $2^\kappa$ full tables costs $O^*(M2^\kappa)$. The exponential loop uses polynomial space.

For a complementary algorithm, let $W=U(L_s)\otimes V(L_t)$ of dimension $uv$. The syndrome of any permutation lies in the coset of $W$ through the syndrome of the identity, by the homogeneous margin equations. If the coset excludes zero, the count is zero. Otherwise the syndrome is always in $W$. Choose a basis of $W$ and extend its dual basis to linear forms on the ambient matrix space by Gaussian elimination. For every linear character $\chi:W\to\{1,-1\}$ this defines an extension $\widetilde\chi$ to the ambient space. Give the edge from a labeled position of type $i$ to one of type $j$ the sign $c_{ij}=\widetilde\chi(u_i\otimes v_j)$. The product along a permutation is its syndrome character. Average its signed sum over all $2^{uv}$ characters. The average of a character evaluation at zero is one, and a nonzero syndrome has average zero. The result counts exactly the valid permutations.

For a fixed character the signed sum is a permanent. Its elementary coverage inclusion-exclusion is
$$
 \sum_{0\le d_j\le n_j} (-1)^{r-\sum_jd_j}
      \prod_j\binom{n_j}{d_j}\prod_i\left(\sum_jd_j c_{ij}\right)^{m_i}.
$$
Here unrestricted maps into the available targets may reuse a position, and covering all $r$ targets forces bijectivity. Transposition again gives $O^*(M)$ evaluations per character. Combining the two algorithms proves the claimed bound. All intermediate integers have polynomial bit length, including before cancellation. In particular $M\le 2^r$, so $\min(uv,\kappa)=O(r)$ suffices for singly exponential exact counting. The count retains all coordinate permutations, including the multiplicities caused by code automorphisms.

## Executable decision and counting check

This reference takes the generator columns and check columns as nonnegative integers whose bits encode binary column vectors. It returns a source-to-target permutation or `None` in search mode and an integer in counting mode.

```python
from collections import Counter
from math import comb, factorial, prod
from itertools import product


def character_count(source, target):
    if not source:
        return 1
    m, n = Counter(source), Counter(target)
    us, vs = list(m), list(n)
    width = max(vs).bit_length()

    def tensor(x, y):
        return sum(y << (i*width) for i in range(x.bit_length()) if (x >> i) & 1)

    basis = {}
    for u in us:
        for v in vs:
            x = tensor(u ^ us[0], v ^ vs[0])
            while x:
                p = x.bit_length()-1
                if p not in basis:
                    basis[p] = x
                    break
                x ^= basis[p]
    ordered = sorted(basis, reverse=True)

    def coordinates(x):
        coeffs = 0
        for index, p in enumerate(ordered):
            if (x >> p) & 1:
                coeffs |= 1 << index
                x ^= basis[p]
        return coeffs, x

    syndrome = 0
    for x, y in zip(source, target):
        syndrome ^= tensor(x, y)
    if coordinates(syndrome)[1]:
        return 0
    edges = [[coordinates(tensor(u, v))[0] for v in vs] for u in us]
    total = 0
    for char in range(1 << len(ordered)):
        signs = [[(-1)**((char & edge).bit_count() % 2) for edge in row] for row in edges]
        for sizes in product(*(range(n[v]+1) for v in vs)):
            value = (-1)**(len(source)-sum(sizes))
            value *= prod(comb(n[v], size) for v, size in zip(vs, sizes))
            for u, row in zip(us, signs):
                value *= sum(d*sign for d, sign in zip(sizes, row)) ** m[u]
            total += value
    return total // (1 << len(ordered))


def parity_tables(source, target, count=False):
    r = len(source)
    if len(target) != r or any(x < 0 for x in (*source, *target)):
        raise ValueError("Expected equal lengths and nonnegative binary columns.")
    if not r:
        return 1 if count else ()
    m, n = Counter(source), Counter(target)
    if count and prod(x+1 for x in m.values()) < prod(x+1 for x in n.values()):
        return parity_tables(target, source, True)
    us, vs = list(m), list(n)
    s, t = len(us), len(vs)
    rows = [((1 << t) - 1) << (i*t) for i in range(s)]
    cols = [sum(1 << (i*t+j) for i in range(s)) for j in range(t)]
    eqs = [(row, m[u] % 2) for row, u in zip(rows, us)]
    eqs += [(col, n[v] % 2) for col, v in zip(cols, vs)]
    for a in range(max(us).bit_length()):
        for b in range(max(vs).bit_length()):
            mask = sum(1 << (i*t+j) for i, u in enumerate(us) if (u >> a) & 1
                       for j, v in enumerate(vs) if (v >> b) & 1)
            eqs.append((mask, 0))
    pivots = {}
    for mask, rhs in eqs:
        while mask:
            p = mask.bit_length()-1
            if p not in pivots:
                pivots[p] = mask, rhs
                break
            basis_mask, basis_rhs = pivots[p]
            mask ^= basis_mask
            rhs ^= basis_rhs
        if not mask and rhs:
            return 0 if count else None

    def lift(free, homogeneous):
        result = free
        for p in sorted(pivots):
            mask, rhs = pivots[p]
            bit = ((result & mask).bit_count() % 2) ^ (rhs and not homogeneous)
            result |= bit << p
        return result

    kernel_dim = s*t-len(pivots)
    syndrome_dim = (s-1)*(t-1)-kernel_dim
    if count and syndrome_dim < kernel_dim:
        return character_count(source, target)
    base = lift(0, False)
    relevant = (1 << (s*t))-1 if count else 0
    for row, u in zip(rows, us):
        if m[u] < t-1:
            relevant |= row
    for col, v in zip(cols, vs):
        if n[v] < s-1:
            relevant |= col
    projected, basis = {}, []
    for cell in range(s*t):
        if cell not in pivots:
            vec = lift(1 << cell, True)
            probe = vec & relevant
            while probe:
                p = probe.bit_length()-1
                if p not in projected:
                    projected[p] = probe
                    basis.append(vec)
                    break
                probe ^= projected[p]

    total = 0
    positions = [[j for j, val in enumerate(target) if val == v] for v in vs]
    for choice in range(1 << len(basis)):
        table = base
        for p, vec in enumerate(basis):
            if (choice >> p) & 1:
                table ^= vec
        left = [m[u]-(table & row).bit_count() for row, u in zip(rows, us)]
        right = [n[v]-(table & col).bit_count() for col, v in zip(cols, vs)]
        if min(left+right) < 0:
            continue
        if count:
            for sizes in product(*(range(n[v]+1) for v in vs)):
                term = (-1)**(r-sum(sizes))
                for size, v in zip(sizes, vs):
                    term *= comb(n[v], size)
                for i, u in enumerate(us):
                    limit = m[u]
                    coeffs = [1]+[0]*limit
                    for j, size in enumerate(sizes):
                        parity = (table >> (i*t+j)) & 1
                        factor = [(a, comb(size,a)) for a in range(parity,min(size,limit)+1,2)]
                        out = [0]*(limit+1)
                        for a, multiplier in factor:
                            for b in range(limit-a+1):
                                out[a+b] += multiplier*coeffs[b]
                        coeffs = out
                    term *= factorial(limit)*coeffs[limit]
                total += term
        else:
            pools = [pos.copy() for pos in positions]
            witness = [-1]*r
            for i, u in enumerate(us):
                assigned = []
                for j in range(t):
                    extra = min(left[i], right[j])
                    left[i] -= extra
                    right[j] -= extra
                    used = ((table >> (i*t+j)) & 1) + extra
                    assigned.extend(pools[j].pop() for _ in range(used))
                for h, dest in zip((h for h, val in enumerate(source) if val == u), assigned):
                    witness[h] = dest
            return tuple(witness)
    return total if count else None
```

The implementation was compared with exhaustive permutation search for all 4,775 ordered pairs of binary subspaces through length four, including zero-dimensional cases. It recovered every positive-instance witness and agreed on the exact counts, totaling 12,736 permutations. On 36 further pairs of length five through seven the counts totaled 5,040. The signed-permanent routine was also checked separately on every pair.

The multidimensional permuted kernel problem and its equivalence with subcode equivalence are established in the literature. The parameter analyzed here concerns the projected parity-table solutions and their complementary syndrome characters. Publication priority for these bounds has not been established. [Santini, Baldi and Chiaraluce, Computational Hardness of the Permuted Kernel and Subcode Equivalence Problems](https://iris.univpm.it/handle/11566/325875) · [Grochow, Srivastava and Thakkar, Algorithms for Finite Group Epimorphism Testing](https://doi.org/10.4230/LIPIcs.ICALP.2026.104)
