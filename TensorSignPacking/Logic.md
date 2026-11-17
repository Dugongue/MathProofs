# Determinant tests on small centroid blocks

All tensors are explicit over $F=\mathbb F_3$. Write $A$ for requiring determinant $+1$ in the first mode and $O$ for ordinary tensor isomorphism. These proofs are informal.

## Theorem

Fix a nonempty set $J$ of tensor modes. The comparison asks for a transporter whose product of determinants in the modes in $J$ is $+1$. Each intrinsic centroid block must have dimension $O(\log L)$ in each of these modes, for written input length $L$. Choose any fixed polynomial-time ordinary-isomorphism invariant $\kappa$ of a block that includes its ordered format. It partitions the blocks into buckets. A bucket with format $(d_1,d_2,d_3)$ has weight $w=\sum_{i\in J} d_i\bmod 2$.

For each source bucket of weight zero, suppose either it has $O(\log L)$ members, or all its blocks are ordinarily isomorphic. Buckets of weight one are unrestricted in size and may mix arbitrary ordinary types. Then the determinant test reduces to one ordinary TI comparison in deterministic polynomial time. A total version of the reduction checks the bucket homogeneity promise by ordinary comparisons. No correspondence, local determinant or transporter is supplied. There may be arbitrarily many blocks overall, including arbitrarily many repetitions of a given ordinarily isomorphic even-weight type.

Taking $J$ to be the first mode gives a reduction of two independent one-sign comparisons to one, whenever one input belongs to this domain. First reduce the indicated comparison to ordinary TI, then use the earlier neutral conjunction theorem on the other unrestricted signed comparison.

## Recover the blocks and their raw orientations

Unequal formats or unequal support dimensions exclude ordinary TI. If a tested mode is support-deficient, independently reflect its unused complement to adjust its determinant. In this case ordinary TI suffices. Otherwise compact the untested modes to their actual supports without changing any tested-mode basis. An all-zero pair also has a straightforward positive verdict. Work with the resulting concise tensors $T,T'$.

Solve the linear centroid equations. The centroid acts faithfully on each mode by conciseness. It is commutative: if $a,b$ are centroid elements and subscripts denote action on one mode, then
$$
a_1 b_1 T
=a_1 b_2 T=b_2 a_1 T=b_2 a_3 T
=a_3 b_2 T=a_3 b_1 T=b_1 a_3 T=b_1 a_1 T .
$$
The same proof works on the other modes. Moving a commuting product across modes verifies closure. Orthogonality of distinct primitive idempotents makes mixed tensor components vanish, because the action of an idempotent on any one mode agrees with its action on the others. The centroid is therefore the product of the block centroids. Its primitive idempotents recover the intrinsic indecomposable summands over $F$. A transporter must permute their identities and restrict to block isomorphisms. Conversely a block matching with individual witnesses extends by direct sum.

These idempotents can be found in polynomial time. If the centroid has dimension $r$, choose $3^k\ge r$ and compute the linear map $a\mapsto a^{3^k}$ by repeated cubing on a basis. Its kernel is the nilradical, since a nilpotent element has nilpotence index at most $r$. The semisimple quotient is a product of finite fields. Its subalgebra fixed by $a\mapsto a^3$ is a product of copies of $F$. Find the one-dimensional common eigenspaces in this fixed subalgebra for multiplication by its basis, splitting with eigenvalues in $F$. Each space gives its unique nonzero idempotent by rescaling a generator by its multiplication scalar. Lift these elements to the centroid and take their $3^k$-th powers. The powers are idempotent and orthogonal since the respective square-minus-element and pairwise products are nilpotent before taking the powers. Their sum is the unit for the same reason. No algebraic closure is needed.

Sort the blocks by the values of $\kappa$, and choose arbitrary deterministic internal orders and ordered bases on each block. Let $\eta$ be the product of the determinant signs of the two concatenated frame changes in each tested mode. It is computable by Gaussian elimination. A witness has raw determinant character equal to $\eta$ times the product of all block-local characters times the permutation characters. The block permutation has no crossings between different buckets: the common invariant and balanced multiplicities guarantee matching contiguous lists in the same bucket order. Within one bucket the transposition sign in mode $i$ is $(-1)^{d_i^2}$, so the product across $J$ is precisely $(-1)^w$. Thus only odd-weight buckets need permutation signs.

Write $G$ for the conjunction of the entire ordinary comparison and, for each large even-weight source bucket, the ordinary comparisons asserting homogeneity, obtained by comparing every member to its first member. On $G$ all bucket counts agree. The total-language version requires $G$ in the nontrivial branch; size conditions are checked directly. In the support-deficient branch the same promise can be omitted by defining that branch as ordinary TI.

## Local signs are ordinary tests

For any candidate matching edge, test whether its allowed local characters include a prescribed sign. For a fixed prescription of each of the at most three individual determinants, include the block tensors, each tested exterior algebra, its degree-one inclusion, and its pinned top exterior vector in a fixed-signature tensor system. Each exterior algebra on dimension $a=O(\log L)$ has dimension $2^a$, and the multiplication and inclusion force the action on all grades. Choose the sign of the top vector at the target to enforce the required physical sign. The ordinary tensor-system compiler yields a single ordinary TI instance. Disjoin the constantly many prescriptions with the given product. Thus for any local comparison there are positive and negative tests, both reducible to ordinary TI and of polynomial size. The same computation applies to comparisons within one endpoint. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

Use $E$ for the disjunction of the negative local self-comparisons for all source blocks, together with every ordinary test for isomorphism of two distinct source blocks in an odd-weight bucket. If $E$ holds, an automorphism correcting the sign is available on the whole source. In the first case it is a local map extended by identities. In the second case use inverse maps when exchanging the two blocks, so the internal characters cancel and the odd block permutation remains. Then $G$ suffices to give the signed verdict. If $E$ fails, all nonempty local relative characters are unique, including comparisons involving target blocks when $G$ holds, by conjugating stabilizers.

## Large even-weight buckets

Assume $G$ and failure of $E$. For one large even-weight bucket all blocks in the union of endpoints are ordinarily isomorphic and the total count is $2m$. Choose an abstract reference in this class and give it an ordered frame. Write $u_i\in\{1,-1\}$ for the unique relative character from that reference to block $i$, using its already selected frame. The unique relative character between blocks $i,j$ is $u_i u_j$. Every matching contributes the same product $\prod_i u_i$, because each block is used just once in the product and the permutation character is neutral.

If $p$ of the $u_i$ are negative, the number of unordered pairs with negative relative character is $p(2m-p)$, whose parity is $p$. Therefore compute the block product by parity of all negative pairs inside this combined bucket. No reference or matching has to be computed. For each pair, its two ordinary sign tests give the two Boolean values of this parity input, with exactly one true on the current branch.

## Odd-weight buckets

On the same branch, every source block in an odd-weight bucket has exactly one ordinarily compatible target block. Existence follows from $G$. Uniqueness follows from failure of $E$, because two compatible targets would belong to a class whose ordinary matching gives two compatible source blocks. For each source block, the disjunction over targets of each prescribed local sign test yields the corresponding sign bit value in positive Boolean form.

For each ordered pair $i<i'$ of source blocks within this bucket, the inversion bit can also be expressed in both values. Take a disjunction over target positions $j>j'$ for the inversion value, or over $j<j'$ for the other value, conjoining the ordinary tests for the two candidate edges on each alternative. The two raw formulas correctly give the inversion bit values because the matching is unique. The parity of these inversion bits is the permutation character. All of these formulas have polynomial size and can use logarithmic-depth balanced disjunctions.

## Small even-weight buckets

An even-weight bucket with $m=O(\log L)$ may have unrestricted ordinary types. Its possible signs can be computed by exact positive Boolean formulas, without superseding the global ordinary guard. Formulas for each desired sign use the following recursion on ordered lists of source and target positions of equal lengths. Length one is just the local signed edge test. For length $t>1$, split the source list into consecutive halves. Enumerate every subset of the target positions of size equal to the left source half, giving those positions in their inherited order to the left half and the complement to the right half. Both relative characters multiply because the permutation character is neutral in the bucket. To test either desired product, take the disjunction over the subsets and the two allowed pairs of child signs, requiring the corresponding two child tests. A recognisable format-count mismatch gives a fixed negative pair. This recursion also works for odd weight if the child signs are corrected by the fixed cross-inversion parity of the two target subsets.

The formula size satisfies an upper recurrence $s(t)\le 2^{t+O(1)}(1+s(\lceil t/2\rceil))$, giving $2^{O(t)}$. The balanced disjunctions have depth $O(t)$ in total, since the numbers of alternatives at a level use at most a constant plus the current subproblem size in their logarithms. This size and depth bound is polynomial and logarithmic, respectively, when $m=O(\log L)$. The formula allows every possible matching and gives both sign conditions exactly. On $G$ and failure of $E$, every perfect matching gives the same product of local signs, by the reference calculation within each ordinary class as above, so exactly one sign condition holds.

## Combine positive Boolean formulas in one ordinary TI instance

For the elementary character signs, inversion bits, and small-bucket products, obtain two formulas stating the available positive and negative values. For two subproducts with pairs $(P_0,P_1)$ and $(Q_0,Q_1)$, the combined pair is
$$
((P_0\land Q_0)\lor(P_1\land Q_1),~
 (P_0\land Q_1)\lor(P_1\land Q_0)).
$$
Encode positive as zero. A balanced tree has logarithmic depth and, even after unrolling, polynomial size. Choose the final parity needed to cancel the measured frame sign $\eta$, naming its formula $P_\eta$. The answer is
$$
G\land(E\lor P_\eta).
$$
The only guard needed for parity correctness is $G$ and failure of $E$. The output expression never requires negating an ordinary comparison.

Ordinary TI comparisons can be combined into a single instance for these formulas. For conjunction, embed the two comparisons in tagged absolutely indecomposable carriers and direct-sum them. For disjunction of $P\simeq Q$ and $R\simeq S$, first construct tagged direct sums for ordered tuples and then build the two unordered multisets of tuples
$$
\{(P,R),(Q,S)\},\qquad \{(P,S),(Q,R)\}.
$$
Wrap each tuple in an absolutely indecomposable carrier of the same format and take the indicated direct sums. A matching of the two summands can use either bijection. One asks $R\simeq S$ and the other $P\simeq Q$. Before applying the carrier, compact ordinary inputs to support and deal directly with unequal support dimensions or zero endpoints by fixed yes or no comparison pairs. At every gate, choose distinct internal format tags where positions must be fixed, and common formats at the disjunction summands where the two bijections must both be allowed. The prior scalar-centroid carrier uses a fixed two-dimensional marker label space and long marker side lengths linear in the largest original side. Consequently the largest side length grows by at most a constant times the largest child side at each binary gate, including both carrier applications for disjunction. Logarithmic depth bounds the dense output length by a polynomial. The ordinary conjunction theorem then absorbs this compiled comparison into the unrestricted signed input.

This covers arbitrary multiplicities in large homogeneous even buckets, heterogeneous even buckets of logarithmic multiplicity, and arbitrary odd-weight buckets for the indicated character problem. It leaves unrestricted large heterogeneous even buckets and large individual tested blocks unresolved. No unrestricted signed degree collapse is claimed.
