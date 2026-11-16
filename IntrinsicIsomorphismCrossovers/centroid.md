# Deterministic recovery from a Hochschild Lie bracket

**Theorem.** Let $k$ be $\mathbb Q$ or a finite field in an explicit binary representation, with no bound on the field size. Let $B$ be a finite-dimensional commutative unital $k$-algebra of dimension $d\ge 2$. Set $m$ to the first member of $\{d+3,d+4\}$ that is invertible in $k$. Form the three-vertex algebra $A(B)$ with diagonal rings $k,k,k$ and successive off-diagonal corners $B^m,B,B^m$, where the corner product is the regular action $(b,v)\mapsto bv$. Given just structure constants for a $k$-Lie algebra isomorphic to $HH^1(A(B))$ with the Gerstenhaber bracket, there is a deterministic polynomial-time algorithm that outputs a multiplication table for $B$ up to $k$-algebra isomorphism. The algorithm also outputs a basis of the characteristic ideal corresponding to $\mathfrak{sl}_m(B)$, expressed in the given Lie algebra. Its only algebra-decomposition subroutine computes an associative Jacobson radical.

The proof gives a general algorithm for extracting characteristic ideals from bounded-size gaps in adjoint composition factors. The Hochschild application replaces the set-theoretic ideal intersection in the earlier dimension-two reduction by an effective inversion. In particular, $HH^1$-Lie-algebra isomorphism on this family and commutative-algebra isomorphism reduce to each other in deterministic polynomial time. An isomorphism of the presented Lie algebras gives an isomorphism of the recovered commutative algebras by conjugation on their centroids. Every commutative-algebra isomorphism lifts to the Hochschild Lie algebras through $A(B)$.

## 1. Separate simple components by matrix degree without factoring

Let $E$ be a finite-dimensional unital associative $k$-algebra given by structure constants. Compute $J=\operatorname{Jac}(E)$ by the deterministic radical algorithm, set $Q=E/J$, and compute its center $Z=Z(Q)$ by solving linear equations. The commutative semisimple algebra $Z$ is a product $\prod_i K_i$ of finite field extensions of $k$. The argument works without exhibiting individual $K_i$ or their primitive idempotents. [Friedl and Rónyai, *Polynomial Time Solutions of Some Problems in Computational Algebra*](https://www.cs.uoregon.edu/Reports/TR-1985-003.pdf) · [Cohen, Ivanyos and Wales, *Finding the Radical of an Algebra of Linear Transformations*](https://doi.org/10.1016/S0022-4049(97)00010-8)

For a finite $Z$-module $M$, the dimension over $K_i$ of its part at $i$ will be called its rank at $i$. One can compute the idempotents that partition $Z$ into the loci of constant rank as follows. Start with $M_0=M$. While $M_t\ne 0$, choose some nonzero $v_t\in M_t$ and compute the ideal
$$
I_t=\{z\in Z:zv_t=0\}.
$$
It is the kernel of a linear map. Every ideal in a product of fields has an identity, with the zero ideal having identity $0$. Find its identity $p_t$ by solving $p_t\in I_t$ and $p_t z=z$ for each vector in a basis of $I_t$. The support of $Z v_t$ is $s_t=1-p_t$. At each field factor this cyclic submodule has dimension one if $s_t$ has coordinate $1$, and zero otherwise. Pass to $M_{t+1}=M_t/(Zv_t)$. Consequently the rank of the original module at each $i$ is the number of $s_t$ with coordinate $1$ there.

Maintain a partition of $1$ into orthogonal idempotents with integer labels, initially the unit labelled zero. At step $t$, replace each current $e$ with its nonzero parts $e(1-s_t)$ and $e s_t$, incrementing the label for $e s_t$. Every partition has at most $\dim_k Z$ parts, because its nonzero orthogonal idempotents are linearly independent. There are at most $\dim_k M$ steps. Adding the parts with a specified label gives exactly the idempotent of that rank locus.

Apply this to $M=Q$. If the simple component of $Q$ over $K_i$ has degree $r_i$ as a central simple algebra, then its rank over $K_i$ is $r_i^2$. Since $k$ is perfect, after extension to $\overline{k}$ the factor $K_i$ splits into one copy of $\overline{k}$ per embedding of $K_i$, and each corresponding component of $Q$ becomes $M_{r_i}(\overline{k})$. The simple modules for these components have dimension $r_i$. For any positive integer cutoff $h$, sum the rank-locus idempotents with labels at least $h^2$. This gives a central idempotent $\overline e_{\mathrm{high}}\in Q$ that acts as identity precisely on the simple $(E\otimes_k\overline{k})$-modules of dimension at least $h$. Here the radical of $E\otimes_k\overline{k}$ is $J\otimes_k\overline{k}$. The latter is nilpotent, and the remaining quotient is semisimple by the splitting just described.

## 2. Extract large constituents from an arbitrary adjoint module

Let $V$ be a finite-dimensional $E$-module, with $n=\dim_k V$. Choose any lifts $a,b\in E$ of $1-\overline e_{\mathrm{high}}$ and $\overline e_{\mathrm{high}}$, respectively. Call a module high if all its simple constituents after extension to $\overline k$ have dimension at least $h$. Define
$$
V_{\mathrm{high}}=\{v\in V : a^n x v=0 \text{ for every }x\in E\}.
$$
The defining equations need only be tested on a basis of $E$, so they give $V_{\mathrm{high}}$ by one kernel computation. This subspace is an $E$-submodule. In fact, for $y\in E$ replace $x$ by $xy$ in the defining equations. It is high, since $a^n$ vanishes on it and $a$ acts as identity on each low simple factor. Conversely, $a$ acts as zero on every constituent of a high module, so it maps each term in a composition series into the preceding term after scalar extension. Thus $a^n$ kills every high submodule of $V$. This proves that $V_{\mathrm{high}}$ is the largest high submodule and is independent of all choices. The proof uses $\overline{k}$, while the computations take place over $k$.

The extraction has a simpler formula when a high submodule $U$ has low quotient $V/U$, meaning all simple constituents of the quotient after scalar extension have dimensions less than $h$. On $U$, $b$ is invertible since its action on every composition factor is the identity. On $V/U$, it is nilpotent with exponent at most $n$. Therefore $U=\operatorname{im} b^n$.

For any finite-dimensional Lie algebra $L$, use $V=L$ and take $E$ to be the unital associative subalgebra of $\operatorname{End}_k(L)$ generated by $\operatorname{ad} L$. An $E$-submodule is a Lie ideal. Every Lie isomorphism conjugates the two adjoint envelopes, and hence transports the largest high ideal for each cutoff. The proof gives its basis from arbitrary structure constants. To construct a basis of $E$, start with the identity and repeatedly add independent products of a generating adjoint matrix with a current basis element. There are at most $n^2$ independent words of length at most $n^2$. Matrix multiplication and linear algebra then give its multiplication table.

## 3. Apply the extraction to the first Hochschild Lie algebra

Write $H=HH^1(A(B))$. We recall the explicit structure of $H$. A derivation represents an outer derivation after it is normalized to vanish on the three vertex idempotents. Such representatives preserve the off-diagonal corners. For maps $P,Q,R$ on the first $B^m$, the last $B^m$, and the $B$ corner, their entire Leibniz condition is
$$
Q L_b-L_b P=L_{R(b)} \qquad (b\in B),
$$
where $L_b$ acts by multiplication on $B^m$. With $a=R(1)$, this yields $Q=P+L_a$ and $[P,L_b]=L_{\delta(b)}$ for $\delta(b)=R(b)-ab$. The commutator identity proves that $\delta$ is a derivation of $B$. Subtracting its entrywise action from $P$ gives $D\in M_m(B)$, and all triples $(D,a,\delta)$ occur. The remaining inner derivations, those from diagonal vertex scalars, identify $D$ modulo $kI_m$ and $a$ modulo $k1$. The resulting Lie algebra is
$$
\left((\mathfrak{gl}_m(B)/kI_m)\oplus (B/k1)\right)\rtimes \operatorname{Der}_k(B).
$$
Here $\operatorname{Der}_k(B)$ acts by derivations on entries, and the two summands in parentheses commute. The trace-zero part $S=\mathfrak{sl}_m(B)$ embeds as an ideal because $m$ is invertible. Its codimension is $2d-2+\dim_k\operatorname{Der}_k(B)\le d^2+2d-2$.

The correct $d$ can be computed from the input dimension of $H$. For each $d$, its dimension lies in
$$
\big[(m(d)^2+1)d-2,\ (m(d)^2+1)d-2+d^2\big].
$$
The intervals are disjoint. The function $m(d)$ is nondecreasing, and the gap between consecutive left endpoints is at least $m(d)^2+1>d^2$. Checking $2\le d\le \dim_k H$ is sufficient.

For cutoff $h=m^2-1$, the quotient $H/S$ has dimension smaller than $h$. Every constituent of $S\otimes_k\overline k$ under the full adjoint envelope has dimension at least $h$, because its restriction to the constant subalgebra $\mathfrak{sl}_m(\overline k)$ is a nonzero subquotient of a direct sum of copies of the simple adjoint module. The trace-zero classical Lie algebra is absolutely simple for $m\ge 5$ prime to $\operatorname{char} k$. More explicitly, over the algebraic closure diagonal brackets isolate each off-diagonal root space, or in characteristic two each paired opposite-root space. An elementary off-diagonal bracket separates the latter pair. A nonzero trace-zero diagonal matrix gives a nonzero root vector by a bracket since the only trace-zero scalar is zero. Matrix-unit brackets then generate all off-diagonal units and diagonal differences. It follows that the separated-submodule formula returns the required $S$ exactly.

Finally compute its centroid by linear equations for $c\in\operatorname{End}_k(S)$:
$$
c([x,y])=[c(x),y]=[x,c(y)] \qquad (x,y\in S).
$$
Every such $c$ commutes with the constant adjoint action. Absolute simplicity and Schur's lemma imply $c=1\otimes f$ on $\mathfrak{sl}_m(k)\otimes_k B$ for some $k$-linear $f:B\to B$. Evaluating the centroid equality on a pair of constant matrices with nonzero bracket and arbitrary coefficients $u,v\in B$ gives $f(uv)=f(u)v$. Hence $f(v)=f(1)v$. Conversely multiplication by each coefficient gives a centroid element. The centroid table under composition is therefore a multiplication table for $B$. Conjugation by any isomorphism of $H$'s restricts to the recovered ideals and induces an algebra isomorphism of their centroids. The formulas for $A(B)$ give the lift in the other direction.

The algorithm uses polynomially many field operations apart from the radical algorithm, which has deterministic polynomial bit complexity in the stated field models. Over $\mathbb Q$, choose the envelope basis from matrix words of bounded length, and represent the successive cyclic quotients in §1 by spans of products of fixed original basis vectors. This keeps the rational matrix entries in the linear systems of polynomial bit size by exact elimination bounds. Each partition idempotent is a product of at most $\dim Q$ support idempotents, each of polynomial bit size by the same bounds. Lifting their sum and raising the resulting matrix to an exponent at most $\dim H$ likewise keeps bit sizes polynomial. There is no call to a Lie-ideal enumeration, Lie isomorphism, field factorization, or central-simple-algebra splitting algorithm.

## 4. Graph-isomorphism completeness from a computable derivation promise

**Theorem.** For every fixed finite field $k$, the following is a polynomial-time recognizable tensor promise. Let $T:U\times V\to W$ be a bilinear map and compute its derivation Lie algebra
$$
D(T)=\{(A,B,C):C T(u,v)=T(Au,v)+T(u,Bv)\}.
$$
On each of the three mode spaces, require that the unital associative algebra generated by the corresponding projection of $D(T)$ be conjugate to the entire algebra of diagonal matrices. Ordinary three-tensor isomorphism on this promise is Graph Isomorphism-complete under deterministic polynomial-time many-one reductions. The forward construction recovers isomorphisms from graph witnesses. The hardness reduction uses only $0$ and $1$ coefficients and has total side length linear in the number of vertices and edges of the source graph.

### Recovering the coordinate lines

Write the three projected algebras as $E_U,E_V,E_W$. The equations for $D(T)$ are linear in the unknown matrix entries, so a basis follows by Gaussian elimination. On a mode of dimension $n$, obtain a basis of its associative algebra by taking the spans of products of the given generators with successive independent matrix words. Test that its dimension is $n$, that all pairs of basis matrices commute, and that $A^q=A$ on each basis matrix, where $q=|k|$. The last condition ensures that each matrix is diagonalizable over $k$ since $x^q-x$ splits there with distinct roots. Commuting split semisimple operators are simultaneously diagonalizable. In joint eigenbases their algebra is contained in the algebra of diagonal matrices, and equality follows from the dimension test. Conversely the full split diagonal algebra passes all three tests.

Obtain all joint eigenspaces by successively splitting the current eigenspaces into the kernels of $A-\lambda I$ for $\lambda\in k$. There are at most $n$ nonzero pieces at any point. Their final dimensions are all one because the diagonal algebra separates each pair of distinct coordinate positions. Thus the computation recovers an unordered direct-sum decomposition into lines in each mode, from the tensor in its input coordinates. If $(g_U,g_V,g_W)$ is a tensor isomorphism, conjugation by these maps identifies the derivation algebras, hence the three associative algebras. It follows that every tensor isomorphism carries the recovered sets of lines onto the corresponding sets of lines.

### Building the graph

Use a vertex for every recovered line, with its mode as colour. Also use vertices for the nonzero vectors of each line, with incidence to their line vertex. Retain the mode distinction there as well. For each fixed scalar $s\in k^\times$, use a directed labelled binary relation $x\mapsto sx$ within each line. A graph isomorphism preserving these relations sends the nonzero vectors of a line to those of a corresponding line by a unique $k$-linear isomorphism on that line. Indeed, its value at any chosen generator determines its value at all nonzero multiples, and the linear map also sends zero to zero.

For lines $L\subset U$, $M\subset V$, $N\subset W$, add a typed ternary relation on nonzero vector vertices consisting of the triples
$$
(u,v,w)\in L^\times\times M^\times\times N^\times
\quad\text{with}\quad
\pi_N T(u,v)=w .
$$
Here $\pi_N$ is projection along the direct sum of the other recovered lines of $W$. In particular, a zero component produces no such relation. Take the labels for scalars and the three argument positions as part of the relation types. Encode this relational structure by a vertex-coloured simple graph. For each relation tuple add a centre vertex of its relation colour and one position-coloured intermediate vertex for each entry, connecting the centre to that intermediate vertex and the intermediate vertex to its entry. Give the original vertices and line incidences their separate designated roles. Colour-preserving graph isomorphisms then give exactly the stated relational isomorphisms on the original vertices. There are constantly many colours since $k$ is fixed. To remove the colours when comparing two graphs, use their common vertex count plus two as a bound $D$, and attach $cD$ private leaves to each vertex of colour $c$, with colours numbered starting at one. Every original vertex then has degree in $[cD,cD+D-1]$, and the new leaves have degree one. If the vertex counts differ, output a fixed negative Graph Isomorphism instance.

A tensor isomorphism gives a graph isomorphism because the line projections and bilinear-component relations intertwine. Conversely the scalar relations give three invertible linear maps by taking the direct sums of the induced maps on lines. Preservation of the ternary relation proves the transport equation on each triple of lines and includes the vanishing components by absence of tuples. Bilinearity extends this to the entire spaces. This also tells how to recover the three matrices from a graph witness.

To build the graph, use one representative generator per line to compute all bilinear coefficients. For each nonzero coefficient and each pair of nonzero scalar multiples of the input generators add the one indicated output relation tuple. There are at most $(q-1)^2\dim U\,\dim V\,\dim W$ such tuples. The line vertices, vector vertices and scalar relations contribute at most $O(q^2(\dim U+\dim V+\dim W))$. All linear algebra, coordinate changes and graph work are deterministic polynomial bit time in the ordinary dense tensor input for fixed $q$. For three positive mode dimensions this input has at least their maximum many entries. Zero mode dimensions are also allowed with trivial shape comparisons and fixed graph answers before the construction.

### Graph hardness inside the promise

Start with the bipartite incidence graph of a simple graph $G$, with original vertices on the left and edges on the right. Attach two private six-cycles at every vertex of the incidence graph, each meeting the rest of the graph only at that vertex. Extend the bipartition along the cycles. Call the resulting bipartite graph $H$. Its old vertices have degree at least four and its cycle vertices have degree two, so the incidence graph is exactly the subgraph on vertices of degree at least four. Every isomorphism of $G$'s induces a side-preserving isomorphism of their $H$'s, and the converse follows by recovering the incidence graph. If $G$ is empty, the reduction can answer the trivial size case directly with a fixed pair of promised tensors.

In either side of $H$, the neighbourhoods of distinct vertices are incomparable under inclusion. To see this for an old vertex $v$, consider its four private neighbours. Each has just one other neighbour, and those four other neighbours are distinct. Any $u\ne v$ on the same side misses at least one of the four. For a private vertex $v$, any other same-side vertex containing its two neighbours would create a four-cycle through $v$. A four-cycle cannot contain any of the private vertices since a private six-cycle is chordless and attached at only one vertex.

Let $U$ and $V$ have bases per left and right vertex of $H$, and $W$ a basis per edge. Define
$$
T_H(u_i,v_j)=
\begin{cases}
w_{ij}&(i,j)\in E(H),\\
0& (i,j)\notin E(H).
\end{cases}
$$
For a nonedge $(i,j)$, the derivation equation gives
$$
0=\sum_{r\colon ,(r,j)\in E(H)} A_{ri}\, w_{rj}
  +\sum_{s\colon ,(i,s)\in E(H)} B_{sj}\, w_{is}.
$$
The two sets of basis vectors in this equation are disjoint because $(i,j)$ is a nonedge. For each $r\ne i$ use a neighbour $j$ of $r$ that is absent from the neighbourhood of $i$. This forces $A_{ri}=0$. The analogous right-side argument gives $B_{sj}=0$ for $s\ne j$. For an edge the derivation equation then forces $C w_{ij}=(a_i+b_j)w_{ij}$, where $a_i,b_j$ are the diagonal entries of $A,B$. Conversely every choice of the diagonal entries gives these derivations.

Both input projections already contain the full diagonal algebras. In the output projection, given two distinct edges, one can choose a single $a_i$ or $b_j$ so that the corresponding diagonal operator is $1$ on the first and $0$ on the second. Taking, for each fixed first edge, the product of these operators over all other edges yields its coordinate projector. This works in every characteristic. Hence the output projection also generates the full diagonal algebra. Every $T_H$ satisfies the promise, with the intrinsic lines exactly the displayed coordinate lines.

A side-preserving isomorphism of $H$'s gives an isomorphism of the tensors by permuting the three bases. Any tensor isomorphism permutes the left and right lines and transports the zero-versus-nonzero pattern of $T_H$ on pairs of such lines, hence yields a side-preserving isomorphism of $H$'s. The padded incidence graph has $O(|V(G)|+|E(G)|)$ vertices and edges, giving the promised size bound in the three tensor dimensions.

### Corollary for prescribed determinants

On the same promise over a fixed $k$, a deterministic polynomial-time Turing algorithm with an ordinary Graph Isomorphism decision oracle finds a tensor transporter with any prescribed determinant triple $\eta\in(k^\times)^3$, or determines that there is none. In particular this includes the determinant-one decision and search problems. Determinants here refer to the maps in the displayed bilinear convention. With the ordinary tensor convention, invert the first two coordinates of the prescribed triple.

Use graph isomorphism decision to find one graph isomorphism by individualizing paired vertices and testing extensions. Reject if no graph isomorphism exists. The preceding construction turns a graph witness into one tensor transporter $g_0$. To compute generators of the automorphism group of the source graph, fix an ordering of its vertices. For each position, individualize all earlier vertices and use the same decision-and-search procedure to obtain one witness for every possible image of the current vertex. The union of those stabilizer-chain representatives generates the group. All the queries with extra colours can be converted to ordinary Graph Isomorphism by the degree construction above, which remains polynomial when the number of colours grows at most linearly with graph size.

Restrict the graph automorphisms to the recovered line vectors and extend linearly on each mode. This gives a group homomorphism onto the source tensor stabilizer, since every tensor automorphism extends to a graph automorphism. The images of the graph generators thus generate the tensor stabilizer, even though additional vertices of the graph can add automorphisms acting trivially on the tensor. The determinant triples of these generators generate a subgroup $D\le(k^\times)^3$. Enumerate $D$ and correction words by closure under the generators and their inverses. There are at most $(q-1)^3$ elements, constant for fixed $k$. Every tensor transporter is $g_0h$ for some source stabilizer element $h$. The prescribed triple is attainable exactly when $\det(g_0)^{-1}\eta\in D$, and a stored correction word supplies the desired $h$.

### Relation to earlier methods

Derivation algebras already underpin the derivation tensor space method of Brooksbank–Maglione–Wilson, which uses conjugacy of derivation algebras and gives a polynomial case with a one-dimensional derivation tensor space and classical Lie conditions. Monomial tensor isomorphism likewise has an established literature. The claim here is a recognizable condition on the Lie algebra of an ordinary tensor, under which all three monomial frames are recovered from that tensor and the resulting promise is exactly GI-complete. The graph construction and hardness use the old incidence interpretation of graph isomorphism, with private six-cycles enforcing the particular derivation-algebra promise. Publication priority for this promise theorem is unverified. [Brooksbank–Maglione–Wilson, *Tensor Isomorphism by Conjugacy of Lie Algebras*](https://arxiv.org/abs/2005.04046) · [D’Alconzo, *Monomial Isomorphism for Tensors and Applications to Code Equivalence Problems*](https://iris.polito.it/retrieve/handle/11583/2986946/5898c9cb-0f0d-4fa1-9e18-10fcf9461380/s10623-024-01375-0.pdf)

## Scope

The Hochschild result is an effective inverse for the Lie family supplied by the three-vertex construction. It gives a polynomially computable complete invariant with values in finite-dimensional commutative algebra tables. The output basis can depend on elimination choices, and comparing the tables retains the full isomorphism problem that the construction encodes. The adjoint extraction also applies to any Lie algebra with a specified absolute-dimension threshold. The separate Graph Isomorphism result requires the full split diagonal promise in all three modes and uses a fixed finite field. Both proofs are informal. [MathProofs, *Tensor isomorphism in global dimension two*](https://github.com/Dugongue/MathProofs) · [Keller, *Derived invariance of higher structures on the Hochschild complex*](https://webusers.imj-prg.fr/~bernhard.keller/publ/dih.pdf)
