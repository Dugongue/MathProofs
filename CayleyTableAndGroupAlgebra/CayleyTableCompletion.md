# Sharp sample bounds for completing labelled Cayley tables

Huh's Open Problem 2 asks whether a flatness-regularized empirical minimizer exactly completes Cayley tables from $O(n\log n)$ uniformly sampled entries. Its displayed loss observes scalar coordinates of the binary structure tensor. Under that observation model the answer is negative, even for a learner told the abstract group in advance. There is a different bound when one observation returns the whole multiplication-table cell, including its output label. [Huh, Sections 3–4](https://arxiv.org/html/2605.29885v1#S4)

**Theorem.** Let the unknown object be a group operation on a known set of $n$ labels, and require exact recovery of the labelled operation. In the worst case, uniformly sampled cell observations have sample complexity $\Theta(n\log n)$. Uniformly sampled binary structure-tensor entries have sample complexity $\Theta(n^2\log n)$. The upper bounds recover every input with probability tending to one. For the lower bounds, the success probability tends to zero on some input at a sufficiently small constant times the stated rate, even when the learner knows the abstract group and only the labelling is unknown. Both bounds apply to independent samples with replacement and to a uniformly random fixed-size subset without replacement. No runtime guarantee is asserted.

The structure tensor of an operation $*$ on labels $Q$ has entries $\delta(x,y,z)=\mathbf1_{\{x*y=z\}}$. A cell observation gives $(x,y,x*y)$ for uniformly sampled $(x,y)\in Q^2$. A scalar observation gives $(x,y,z,\delta(x,y,z))$ for uniformly sampled $(x,y,z)\in Q^3$. A cell is therefore equivalent to one observed output label, or a fibre of $n$ scalar entries.

## Near tables come from permutations moving few labels

We give the correction argument used in the upper bound. Suppose $G,H$ are groups of equal finite order, and $f\colon G\to H$ is a bijection satisfying $f(xy)=f(x)f(y)$ on at least $1-\epsilon$ of the ordered pairs, for $\epsilon\le1/8$. For every $x\in G$, let $b_x(y)=f(xy)f(y)^{-1}$. For independent uniform $y,z$, the two multiplication tests on $(xy,z)$ and $(y,z)$ both pass except with probability at most $2\epsilon$. When they pass, $b_x(yz)=b_x(y)$. Since $y,yz$ are independent uniform elements, the probability that two independent values of $b_x$ agree is at least $1-2\epsilon$. The sum of squares of the atom probabilities is at most the largest atom probability. Thus a unique value $g(x)$ occurs with probability at least $1-2\epsilon$.

For each fixed $x,w$ and every $y$ there is an identity
$$
 b_{xw}(y)=b_x(wy)b_w(y).
$$
For uniform $y$, the three values equal their respective majority values simultaneously with probability at least $1-6\epsilon>0$. It follows that $g(xw)=g(x)g(w)$. For an $x$ with $f(x)\ne g(x)$, at most $2\epsilon$ of the $y$ can satisfy $b_x(y)=f(x)$. Averaging the original test failure probability over the rows $x$ bounds the fraction of such $x$ by $\epsilon/(1-2\epsilon)\le2\epsilon$. As $f$ is bijective, the image of $g$ has more than half the elements of $H$. The image is a subgroup, so $g$ is onto and, by equal order, an isomorphism. This is a direct form of the majority correction used in homomorphism testing. [Ben-Or–Coppersmith–Luby–Rubinfeld, homomorphism testing](https://doi.org/10.1002/rsa.20182)

Apply this to the identity map on the labels of two group tables. If the tables differ at $D\le n^2/8$ cells, an isomorphism moves at most $2D/n$ labels. Thus the second table is obtained by transport of the first through a permutation with small support.

## Upper bounds

Given the observations, return a group operation consistent with them when one exists, using any fixed choice rule. The ground truth is consistent. We bound the probability there is a second consistent table.

For every alternative with $0<D\le n^2/8$, choose one of the permutations furnished above with minimum support, say $\ell$. The alternative differs at $D\ge\ell n/2$ cells and $\ell\ge1$. There are at most $n^\ell$ permutations of support $\ell$, since there are at most $\binom n\ell\ell!$ ways to choose and act on the support. Each permutation determines at most one alternative. Each differing cell gives exactly two differing scalar coordinates, since its old and new output labels are distinct. With $m$ independent observations the probability of missing an alternative is therefore at most $\exp(-m\ell/(2n))$ in the cell model and $\exp(-m\ell/n^2)$ in the scalar model. For $m=C n\log n$ or $C n^2\log n$, respectively, the sum of these probabilities over near alternatives is bounded by a convergent geometric tail tending to zero for a large enough universal $C$.

For far alternatives, Pyber's bound on the number of isomorphism types of order $n$ gives at most $n!\,n^{O((\log n)^2)}=\exp(O(n\log n))$ labelled tables. A far alternative differs from the truth on more than $1/8$ of cells and more than $1/(4n)$ of scalar coordinates. At the stated sample sizes the same union bound tends to zero for large enough $C$. The proof is uniform over the ground truth. [Pyber, Enumerating finite groups of given order](https://annals.math.princeton.edu/1993/137-1/p06)

## Lower bounds

For $n>8$, fix any abstract group of order $n$ and give it to the learner. Choose the table uniformly among the distinct relabelled tables for that group. For each possible ground truth, partition all but at most one label into disjoint pairs $P_1,\ldots,P_{\lfloor n/2\rfloor}$. For each $i$ form the alternative table obtained by swapping the two labels in $P_i$ simultaneously in inputs and outputs. Each alternative differs from the ground truth, and the alternatives are pairwise distinct. A contrary equality would make a transposition or a product of two disjoint transpositions an automorphism of the ground truth. Each such permutation fixes at least $n-4>n/2$ elements. The fixed points of an automorphism form a subgroup, and any proper subgroup has at most half the group's elements, so the automorphism would be the identity.

Let $E_i$ denote the set of differing observed coordinates in either sampling model. In the scalar model a differing triple must touch $P_i$ and be a positive triple in the old or the new structure tensor. In a group table, fixing one coordinate of a positive triple leaves $n$ possibilities, and fixing any two leaves exactly one. Consequently $|E_i|\le 2\cdot 3\cdot 2n=12n$. A triple in $E_i\cap E_j$ touches the two disjoint pairs and is positive in one of the two tables defining $E_i$. Choosing distinct positions for the two contacts, the labels at those positions and the table shows $|E_i\cap E_j|\le6\cdot4\cdot2=48$.

In the cell model, a changed cell $(x,y)$ must have one of $x,y,x*y$ in the swapped pair. If all three labels were fixed, transport would leave the output unchanged. Thus $|E_i|\le6n$. A cell changed by two swaps has an old positive triple touching both swapped pairs, so $|E_i\cap E_j|\le24$ by the same position count.

Write $N=n^3$ for scalar coordinates or $N=n^2$ for cells. Let $X$ be the number of these alternatives missed by all $m$ samples. For $m\le c(N/n)\log n$ and sufficiently small universal $c>0$, the expectation
$$
 \mathbb E X=\sum_i (1-|E_i|/N)^m
 \ \ge\ \lfloor n/2\rfloor\,\exp(-24mn/N)
$$
tends to infinity. We used $\log(1-x)\ge-2x$ for sufficiently small $x$ and the common bound $12n$. For $i\ne j$, divide the probability of missing both sets by the product of their single-set miss probabilities. This ratio equals
$$
 \left(
 \frac{1-(|E_i|+|E_j|-|E_i\cap E_j|)/N}
 {(1-|E_i|/N)(1-|E_j|/N)}
 \right)^m
 \ \le\ (1+192/N)^m
 =1+o(1),
$$
uniformly in the truth and in the pair. Therefore $\operatorname{Var}(X)\le\mathbb EX+o((\mathbb EX)^2)$. Chebyshev's inequality shows there are a diverging number of consistent alternatives with probability tending to one.

Conditional on the sampled positions and observations, the prior on the distinct relabelled tables is uniform over the consistent ones. The optimal conditional probability of choosing the exact truth is the reciprocal of their number. This number is at least $X+1$ on every joint outcome, so average success tends to zero. In particular some promised input has success tending to zero for any given estimator. This proves the claimed worst-case lower bounds for every group order under consideration.

For sampling without replacement, the missed-set probabilities for a given alternative are at most those with replacement, so the upper proofs still apply. For the lower bounds, $m=o(N)$ in both models. In $2m$ draws with replacement the expected number of repetitions is at most $\binom{2m}{2}/N=o(m)$, so with probability tending to one there are at least $m$ distinct positions. The first $m$ distinct positions give a uniform sample without replacement, conditional on this event, which depends only on the repetition pattern. A successful estimator with $m$ observations without replacement would then succeed with $2m$ observations with replacement. Choosing the lower-bound constant half as large rules that out.

## Scope

Under the scalar sampling in the displayed empirical tensor loss, the impossibility applies to any learner based on those observations, including a flatness-regularized empirical minimizer. The paired full-cell model has the $O(n\log n)$ information-theoretic upper bound, but the proof uses consistency among valid group tables. It does not establish the guarantee for Huh's particular optimizer in that observation model. Huh's empirical antecedent treats predicting the discrete product for given input labels, making the distinction between a scalar entry and a full labelled cell relevant. A targeted search located the original question and empirical antecedent, with no matching pair of sharp bounds. Informal proof. [Huh, ICLR 2025, Sections 4 and 7](https://openreview.net/forum?id=Tz8Li6G2xU)
