# Quadratic-dimensional test algebras for nonassociative identities

**Informal theorem.** For \(d\ge1\) and a field \(F\) with \(|F|>d\), there is a unital algebra of dimension \(1+d(d+1)\) with no nonzero polynomial identity of degree at most \(d\) in the free nonassociative noncommutative algebra. If \(\operatorname{char}F\ne2\), there is a unital commutative algebra of dimension \(1+\binom{d+1}{2}\) with the corresponding identity-free property for commutative nonassociative polynomials. The constructions have structure constants 0 and 1.

This improves the cubic upper bounds in [Mukhopadhyay–Ramya–Shastri, Section 5, Question 2](https://arxiv.org/html/2509.11349#S5). The exact minimum dimension remains open.

## Ordered multiplication

Take \(d+1\) distinct priorities \(1,\ldots,d+1\). The nonunital vector space has basis \(e_{ab}\) for ordered distinct priorities. Set
\[
e_{ab}\,e_{bc}=e_{ac}\quad\text{if }a,b,c\text{ are distinct and }b<\min(a,c),
\]
and set all other products of basis elements to zero. Adjoin a unit. Substitute the generic vector \(\sum_{a\ne b} z_{x,a,b} e_{ab}\) for each variable \(x\).

A word of the free algebra is an ordered full binary tree with labelled leaves. Choose a nonzero coefficient of a tree with \(m\le d\) leaves in the given polynomial. Place its \(m-1\) internal nodes at the unique cuts separating their left and right leaf intervals. Assign the cuts distinct priorities increasing from descendants to ancestors. Assign the two outer endpoints the two largest priorities. Consecutive endpoints form a directed simple path in leaf order. At each leaf select the generic coordinate of the corresponding edge. Their product is a squarefree monomial in generic coordinates even when a variable label repeats, since all edges are distinct.

This monomial occurs in the output coordinate indexed by the two outer endpoints. It can occur only from the chosen labelled tree. In fact, a basis evaluation using these edges must concatenate directed connected path intervals, so the leaf order is forced. Induction on a subtree shows that the split priority exceeds every interior priority of either child. The child's exterior endpoint at the parent split exceeds its own split, and the same inequality recurs through descendants. Thus each root split is the unique maximum internal priority of its interval. This determines the entire ordered tree. Conversely, the chosen tree has this property and each split priority is smaller than both exterior priorities, so every product is allowed. There is exactly one contributing leaf assignment in the chosen tree. Its coefficient in the output is the original nonzero coefficient.

## Unordered multiplication

Use basis elements indexed by unordered pairs of distinct priorities. Two basis elements multiply to the pair of their other endpoints when they share exactly one endpoint and that common priority is smaller than the other two. Every other basis product is zero. This multiplication is symmetric. Choose a planar representative of the desired unordered tree to assign priorities and construct the witness path.

The product of generic leaf coordinates now specifies the undirected path. Every nonzero basis evaluation contributing this monomial must use connected subpaths. Its unordered splitting tree is again determined by the unique maximum internal priority at each split. Reversing orientations gives the same unordered tree, and the coordinate labels on the edges fix the leaf labels. A contributing assignment to the fixed syntactic leaf occurrences is precisely the leaf map of a rooted label-preserving isomorphism to the path's splitting tree. For the selected tree these maps form a set of size \(|\operatorname{Aut}(T)|\). A rooted binary tree automorphism group preserving leaf labels has order a power of two, by the recursion allowing at most a swap at a vertex. This factor is nonzero in characteristic different from two. It follows that the witness monomial has nonzero coefficient.

In both variants the resulting nonzero ordinary polynomial in generic coordinates has degree at most \(d\). Schwartz–Zippel gives an evaluation over \(F\) that is nonzero. A nonzero constant term can also be separated by evaluating at zero. The same proof gives randomized evaluation hitting probability at least \(1-d/|S|\) for independent generic coordinates sampled from any finite \(S\subseteq F\) with \(|S|>d\).

## Lower bounds and characteristic two

If an algebra has dimension \(m\), every alternating \((m+1)\)-linear map into it vanishes. Alternating a fixed comb word in \(m+1\) labelled leaves gives a nonzero formal identity in the noncommutative case. In the commutative case add a separate fixed marker leaf as the first entry of the comb, and alternate the other \(m+1\) labels. The marker prevents the first sibling swap from identifying two terms, so the formal polynomial is nonzero. This gives the elementary lower bounds \(m\ge d\) and \(m\ge d-1\), respectively, for the two test-algebra problems.

The characteristic restriction matters. The commutative algebra in Section 3.2 of the cited arXiv version is obtained from an anticommutator before adjoining a unit. In characteristic two its nonunital part squares to zero, and every square in its unitization is a scalar multiple of the unit. Consequently it satisfies the nonzero degree-four free commutative nonassociative identity
\[
((xx)y)z-(xx)(yz)=0.
\]
The two trees are distinct, and substitution of a scalar multiple of the unit for \(xx\) makes the two evaluations equal. Thus large field cardinality alone cannot justify the claimed use of that particular commutative construction in characteristic two for \(d\ge4\). The unordered quadratic construction above also makes no characteristic-two claim. The ordered construction works in characteristic two. Publication priority has not been established.
