# Sharp height and dimension thresholds for counting antichains in lattices

An antichain of a finite poset corresponds to the order ideal obtained by taking its downward closure. The inverse takes the maximal elements. We use height to mean the maximum number of elements in a chain.

**Theorem.** Exact counting of antichains or ideals of an explicitly presented finite lattice is #P-complete under polynomial-time metric reductions, even for graded lattices of height four and order dimension exactly three. Testing the parity of either count is ⊕P-complete under polynomial-time many-one reductions on this class. Counting is polynomial-time at height at most three, or at order dimension at most two.

This proves simultaneous sharp thresholds for two natural ways to constrain explicit finite lattices. The hardness is for lattices without a distributivity promise. On the order dimension question without a lattice promise, Kozma states the known polynomial result in dimension two and the hardness for unrestricted posets. The stronger structural promises here follow from combining planar counting hardness, path subdivision, and incidence lattices. Searches found each of these ingredients in prior work. Priority for this precise combined statement has not been established. [Kozma, SWAT 2020, p. 12](https://drops.dagstuhl.de/storage/00lipics/lipics-vol162-swat2020/LIPIcs.SWAT.2020.30/LIPIcs.SWAT.2020.30.pdf#page=12) · [Amarilli’s restricted counting questions](https://a3nm.net/work/research/questions/#complexity-of-counting-antichains-in-restricted-poset-classes)

## The lattice construction

For a simple graph $H$, put its vertices below its edges, with $u<e$ if $u$ is an endpoint of $e$. Adjoin global bottom and top to this vertex–edge incidence poset to obtain $L(H)$. This is a lattice. Two distinct vertices have a unique common incident edge when adjacent, and otherwise have top as their join. Their meet is bottom. Two distinct edges have an endpoint as meet if they share one, and otherwise have bottom as meet. Their join is top. For a nonincident vertex–edge pair, the meet and join are bottom and top. Comparable pairs have the usual meet and join. All of these cases follow from the absence of loops and parallel edges.

If $H$ has an edge and has no isolated vertices, $L(H)$ is graded of height four. Every maximal chain consists of bottom, a vertex, an incident edge and top. Each antichain either avoids both extremes or is a singleton containing one of them. The former are exactly independent sets in $S(H)$, the graph obtained by replacing every edge of $H$ by a path of length two. Thus
$$
\#\operatorname{Antichains}(L(H))=\#\operatorname{IS}(S(H))+2.
$$

For planar $H$, Schnyder’s theorem gives order dimension at most three for its incidence poset. Adjoining extremes leaves this bound unchanged. If $H$ contains a triangle, the three vertices and three opposite edges of that triangle induce the standard example $S_3$. In one linear extension no two of the vertex–opposite-edge incomparable pairs can be reversed simultaneously, because each vertex is below the opposite edge of the other vertex. A realizer therefore requires at least three orders. These inputs have order dimension exactly three. [Schnyder, *Planar graphs and poset dimension*](https://doi.org/10.1007/BF00353652)

## Exact counting with one oracle value

We first reduce total independent-set counting for simple planar graphs to one value of the lattice count. Let $G$ have $n$ vertices and $m$ edges. Remove isolated vertices and record their factor of two, or directly handle an edgeless graph. Use the remaining $n,m$ in the construction. Fix
$$
t_2=9(n+2),\qquad t_1=4(mt_2+n+2).
$$
Form a planar simple graph $H$ by replacing every edge of $G$ by $t_2$ internally disjoint length-two paths, and adjoining $t_1\deg_G(v)$ private leaves to each original vertex $v$. Draw parallel paths in separate thin strips along the original edge and place leaves locally at their root. All intermediate and leaf vertices are fresh. The graph is simple, has polynomial size, and has no isolated vertices.

In $S(H)$ the replacement paths have length four and each leaf attachment is a length-two path. To count their internal binary choices conditional on original vertices, use the adjacency interaction matrix
$$
M=\begin{pmatrix}1&1\\1&0\end{pmatrix}
$$
for independent sets, with state one meaning chosen. A path of length four has conditional weights $5,3,2$ for endpoint patterns $00$, $01/10$, $11$, respectively, by
$$
M^4=\begin{pmatrix}5&3\\3&2\end{pmatrix}.
$$
A length-two pendant path has weights $3,2$ by root state, given by the row sums of $M^2$. Conditional on the original vertex states, all the new choices are independent across gadgets.

For an original bit assignment let $a,b,c$ count the edges of the three endpoint types, and let $k=b+2c$ be the sum of degrees of the chosen vertices. The number of extensions to $S(H)$ depends only on $(k,c)$ and equals
$$
B_{k,c}=3^{t_1(2m-k)}2^{t_1k}
5^{t_2(m-k+c)}3^{t_2(k-2c)}2^{t_2c}.
$$
Therefore
$$
\#\operatorname{IS}(S(H))=\sum_{k,c} N_{k,c}B_{k,c},
$$
where the sum ranges over the $O(m^2)$ feasible triples $a,b,c\ge0$ with $a+b+c=m$, and $N_{k,c}$ counts original assignments of each type.

These bases have large multiplicative gaps. At fixed $k$, increasing $c$ by one multiplies the base by $(10/9)^{t_2}>2^{n+2}$, since $(1+1/9)^9>2$. For each increase of $k$ by at least one, the pendant-path contribution shrinks by at least $(3/2)^{t_1}$. The ratio of any two edge-path contributions is at most $(5/2)^{mt_2}$. Our choice of $t_1$ makes $(3/2)^{t_1}/(5/2)^{mt_2}>2^{n+2}$. Thus every base at smaller $k$ exceeds every base at larger $k$ by that factor. All feasible bases, when sorted in decreasing order, have consecutive ratios greater than $2^{n+2}$.

The total multiplicity $\sum_{k,c}N_{k,c}$ is $2^n$. Divide the returned count by its largest candidate base and take the integer part. Contributions of all smaller bases total less than the largest base, so the integer part is its coefficient. Subtract that term and continue down the sorted list. The same bound applies at every stage and recovers all coefficients exactly. Summing those with $c=0$ gives the independent-set count of $G$. The integer bases, answer, and all intermediate values have polynomial bit length because the graph has polynomial size and every value counts at most exponentially many subsets of that graph.

Query $L(H\sqcup K_3)$ to force dimension exactly three. As $S(K_3)=C_6$ has 18 independent sets, the one oracle value is $18\#\operatorname{IS}(S(H))+2$. Subtracting two and dividing by 18 provides the input to the preceding decoding procedure.

For completeness under metric reductions from arbitrary #P functions, the planar independent-set source itself can be made complete under metric reductions. Hunt, Marathe, Radhakrishnan and Stearns first give parsimonious reductions to planar monotone exact-one 3SAT and then a reduction to counting vertex covers of a specified size $K$ in a simple planar graph $G_0$. Their Claim 4.3 gives the known multiplicity $2^q$ where $q$ is the number of clause groups. By taking complements, the returned quantity needed is the number $N_s$ of independent sets of size $s=|V(G_0)|-K$. Attach $N+1$ private leaves to each vertex of $G_0$, where $N=|V(G_0)|$, and call the resulting planar graph $J$. Its total count is
$$
\#\operatorname{IS}(J)=\sum_{s=0}^{N}N_s (2^{N+1})^{N-s}.
$$
Each coefficient $N_s$ is at most $2^N$, so a specified coefficient is recovered by extracting a base-$2^{N+1}$ digit. This needs one total count of $J$, itself recoverable from one lattice query by the construction above. Postprocessing uses only polynomial-time exact integer arithmetic. Membership in #P follows by guessing a subset once and checking the antichain condition. [Hunt–Marathe–Radhakrishnan–Stearns, Corollary 3.11, Theorem 4.2 and Claim 4.3](https://arxiv.org/pdf/cs/9809017#page=15)

An alternative polynomial-query proof follows from Vadhan's planar independent-set theorem and the transfer identity $M^\ell=F_\ell M+F_{\ell-1}I$ with Fibonacci numbers $F_i$. Taking even path lengths and interpolating the resulting degree-$m$ polynomial yields the original independent-set count. The separation of weights above is what permits one exact response. [Vadhan, *The Complexity of Counting in Sparse, Regular, and Planar Graphs*](https://doi.org/10.1137/S0097539797321602)

## Parity

Valiant proves parity hardness for independent sets of planar graphs, even with a prescribed degree pattern. Parallel edges, if present in an input representation, can be discarded because they do not change the independent sets. For graphs with isolated vertices, parity is zero and the reduction can return the fixed even lattice $L(K_3)$. It can also return one fixed odd lattice when the source is empty. [Valiant, *Accidental Algorithms*](https://people.seas.harvard.edu/~valiant/focs06.pdf)

Over $\mathbb F_2$, $M^3=I$, so $M^4=M$. Replacing every edge by a path of length four preserves the parity of the independent-set count. Given a source $G$ with no isolated vertices and at least one edge, use $H=G_2\sqcup K$, where $K$ is a triangle with one pendant edge. This planar $H$ contains a triangle, and $S(H)=G_4\sqcup S(K)$. To count the independent sets of $S(K)$, condition on the attachment vertex of its 6-cycle. Excluding that vertex gives 13 choices along the rest of the cycle and 3 choices on the pendant path. Including it gives 5 and 2 choices, respectively. Thus $S(K)$ has $13\cdot 3+5\cdot 2=49$ independent sets, which is odd. Consequently
$$
\#\operatorname{Antichains}(L(H))=49\#\operatorname{IS}(G_4)+2
\equiv\#\operatorname{IS}(G)\pmod 2.
$$
The fixed odd lattice for the empty graph can be $L(K)$. The construction gives a single instance, and the rejecting or accepting count parity is computable as a parity-machine language. Thus the claimed parity completeness holds under many-one reductions.

## The polynomial cases

A lattice of height at most three has no two comparable interior elements. If those extremes are distinct and there are $k$ interior elements, its antichain count is $2^k+2$. The one-element lattice has two antichains.

At dimension at most two, take a realizer by two linear orders. Read points in the first order and list their ranks in the second. The antichains are exactly the decreasing subsequences, including the empty one. A dynamic program that adds up preceding larger ranks counts these subsequences in $O(n^2)$ additions of $O(n)$-bit integers. A realizer can be recovered in polynomial time by transitively orienting the incomparability graph. Uniting that orientation or its reverse with the given order produces the two linear orders. [McConnell–Spinrad, *Modular decomposition and transitive orientation*](https://doi.org/10.1016/S0012-365X(98)00319-7)

## Scope

Amarilli’s separate question asks for the complexity when an explicit lattice is distributive. The lattices $L(H)$ in the hardness proof are not in that class. In a distributive lattice of height four there are at most eight elements, since it is the ideal lattice of a three-element poset by Birkhoff’s representation theorem. The argument therefore settles a sharp height threshold for arbitrary lattices and does not settle the distributive-lattice question.

## Approximation and validation

On incidence lattices $L(H)$, the known FPTAS of Liu–Lu applies to $S(H)$ because all inserted subdivision vertices have degree two and lie on one side of its bipartition. Adding two to a relative approximation preserves the same relative error bound. This also works when $H$ is not planar. Thus the hardness results coexist with deterministic polynomial-time relative approximation. [Liu–Lu, *FPTAS for #BIS with Degree Bounds on One Side*](https://arxiv.org/abs/1412.0073)

An independent finite computation checked the separated-base decoding and the specified-size digit extraction on all 75 simple graphs on one to four labeled vertices. It checked 1,098 original assignments, 731 candidate bases, and independently enumerated the fixed gadget counts 18 and 49. The counting arguments above cover all input sizes.
