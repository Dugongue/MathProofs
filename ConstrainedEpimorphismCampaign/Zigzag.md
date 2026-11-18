# Marked epimorphisms of zigzag persistence modules

**Theorem.** Fix any finite field $K$ of size $q\ge2$. The following problem on raw matrices is #P-complete under polynomial-time metric reductions. An input consists of three representations $A,B,C$ of the same oriented type-$A$ path and two pointwise surjective morphisms $\rho:A\to C$ and $\psi:B\to C$. Count the pointwise surjective morphisms $f:A\to B$ with $\psi f=\rho$. Deciding whether such an $f$ exists is NP-complete. The claims already hold on strictly alternating paths, with every transition of $B$ surjective and with $A$ supplied in interval form. They include $K=\mathbb F_2$.

A morphism here is a family of vertex matrices that commutes with every arrow, and epimorphism means surjectivity at every vertex. The interval module on consecutive vertices has a one-dimensional space at each of those vertices, identity on arrows between them, and zero outside. These are standard zigzag persistence modules. The proof below uses explicit matrices and does not require an interval decomposition algorithm. The complexity claims are informal, and publication priority remains unverified. [Botnan–Lesnick, *An introduction to multiparameter persistence*](https://arxiv.org/abs/2203.14289)

## Turning a subspace avoidance condition into one local rank test

Let $W_1,\ldots,W_m$ be explicitly given subspaces of $K^d$, each of codimension $r_i\ge1$. Assume $d\ge1$ and $m\ge1$. We construct an instance whose marked epimorphisms are indexed, up to a computable constant fiber, by
$$
\{\,t\in K^d:t\notin W_i\text{ for all }i\,\}.
$$

The vertices of the path, in order, begin as follows:
$$
s_0\leftarrow v_1\to s_1\leftarrow w_1\to s_2
          \leftarrow v_2\to s_3\leftarrow w_2\to s_4
          \leftarrow\cdots\to s_{2m}.
$$
Thus each checker $v_i$ has adjacent sinks $s_{2i-2},s_{2i-1}$, and each auxiliary source $w_i$ has adjacent sinks $s_{2i-1},s_{2i}$. There is a subrepresentation $Z$ of $B$ that is $K^d$ everywhere with identity arrows. The only extra coordinates of $B$ are
$$
B_{w_i}=K^d\oplus E_i,\qquad E_i=K^{d-r_i}.
$$
Choose a linear isomorphism from $E_i$ to $W_i$, written as an injective matrix $L_i:E_i\to K^d$. The left arrow from $w_i$ acts as $(z,e)\mapsto z+L_i(e)$, and its right arrow acts as $(z,e)\mapsto z$. All checker arrows are identity maps. In particular every arrow of $B$ is onto. The quotient $C=B/Z$ has only the spaces $E_i$ at $w_i$, with zero arrows, and $\psi$ is its projection.

Use the following explicit direct sum for $A$.

- One interval on the entire path, on which $\rho=0$.
- For each $i$, one tester interval $[s_{2i-2},w_i]$ for each standard basis element $e_j$ of $E_i$. On this interval the only nonzero component of $\rho$ sends its unit at $w_i$ to $e_j$.
- For each $i$, $r_i-1$ intervals $[s_{2i-2},s_{2i-1}]$ with zero mark, called the checker fillers.
- For each $i$, $d-1$ intervals $[s_{2i-1},s_{2i}]$ with zero mark, called the auxiliary fillers.

Each zero mark is a morphism. The tester marks are also morphisms, because all arrows of $C$ are zero and its only nonzero components occur at sources. The tester marks span every $C_{w_i}$, so $\rho$ is pointwise onto.

An admissible map from the full interval has mark zero and lies in $Z$. Its image is the same vector $t$ at every vertex, since all arrows of $Z$ are identity. For the tester indexed by $e_j$ at $w_i$, its image there is $(z,e_j)$. The tester interval ends at $w_i$ and has no space at the next sink $s_{2i}$. The omitted right arrow forces $z=0$. The left arrow now forces the image $L_i(e_j)$ at the shared sink $s_{2i-1}$. The identity checker arrows force the same image at $v_i$ and $s_{2i-2}$. These values give the unique admissible tester morphism. No boundary arrow leaving the interval on its left imposes another condition, since that endpoint is a sink.

Each filler interval begins and ends at sinks. Since it has zero mark, its map lands in $Z$ and consists of one freely chosen vector of $K^d$, repeated across the interval. Conversely every such vector gives a morphism. These choices are independent across direct summands.

At $v_i$, the columns of $f$ are the fixed tester basis of $W_i$, the full-interval vector $t$, and $r_i-1$ checker filler vectors. Their images in $K^d/W_i$ span if and only if the projected $t$ and the projected fillers form a basis. Thus an admissible choice exists precisely for $t\notin W_i$. For any such $t$, the number of checker filler choices is
$$
\alpha_i=q^{(d-r_i)(r_i-1)}\prod_{j=1}^{r_i-1}(q^{r_i}-q^j).
$$
The product counts ordered basis completions of the fixed nonzero projection of $t$, and each filler projection has $q^{d-r_i}$ lifts.

At $w_i$, the fixed tester columns are $(0,e_j)$. The other columns span the $K^d$ summand exactly when $t$ and the $d-1$ auxiliary fillers form a basis. Since every admissible $t$ lies outside at least one subspace, it is nonzero. The auxiliary completion count for each such $t$ is
$$
\beta=\prod_{j=1}^{d-1}(q^d-q^j).
$$
Finally, surjectivity at every source implies surjectivity at every sink. Indeed, each sink has an incoming arrow of $B$ that is onto, and its composite with the already onto source map factors through the sink map by naturality.

There are no additional choices in the morphism, since the images of the interval basis vectors determine it. Thus the total count equals
$$
\beta^m\Bigl(\prod_{i=1}^m\alpha_i\Bigr)
\left|\{t\in K^d:t\notin W_i\text{ for every }i\}\right|.
$$
Each factor is a positive integer, using the empty product convention, and can be computed in polynomial bit time. The construction has $4m+1$ vertices, spaces of dimension $O(d)$, and explicit matrix entries. At each source the dimensions of $A$ and $B$ are equal.

## Encoding Boolean satisfiability by subspace avoidance

Use a Boolean 3CNF formula in $n$ variables. Delete tautological clauses and repeated literals. An empty clause can be handled by a fixed infeasible instance. Put $d=n+1$ and write $t=(t_0,t_1,\ldots,t_n)$. Add the condition $t_0\ne0$ by avoiding its kernel. For each variable $j$ and each $a\in K\setminus\{0,1\}$, also avoid the hyperplane $t_j-a t_0=0$. With these conditions the normalized value $b_j=t_j/t_0$ is a Boolean bit.

For a positive literal on variable $j$, its falsity is the vanishing of $t_j$. For a negative literal on that variable, its falsity is the vanishing of $t_j-t_0$. A clause is false precisely when all its literal-falsity forms vanish. Impose avoidance of this common kernel as one $W_i$. The variables within the clause are distinct, so these forms are independent and its codimension is the clause length, at most three. The list of avoidance constraints is polynomial in the input size because $q$ is fixed.

Each Boolean satisfying assignment has exactly $q-1$ valid vectors $t$, one for each nonzero value of $t_0$. No other vectors qualify. In particular over $\mathbb F_2$ there is precisely one valid vector per satisfying assignment. If an empty clause needs a fixed infeasible instance, for $d=2$ require avoidance of each of the $q+1$ one-dimensional subspaces of $K^2$, whose union is $K^2$. The local matrix construction applies to that list as well.

An oracle for the marked epimorphism count gives the #3SAT answer by dividing its one response by
$$
(q-1)\,\beta^m\prod_i\alpha_i.
$$
This is a metric reduction. Its positive fibers also give a polynomial-time many-one reduction for decision. Membership in #P follows by guessing one canonical encoding of the vertex matrices, verifying every commutative square and marked equality, and testing the vertex ranks. The same verifier gives NP membership for decision. The input promises can themselves be checked by matrix operations.

The difficulty arises even though both maps to the mark are onto. A single full-interval vector is tested at many different sources. The marked tester intervals define different fixed subspaces there, so independent rank counts at individual vertices cannot be multiplied before accounting for that shared vector.
