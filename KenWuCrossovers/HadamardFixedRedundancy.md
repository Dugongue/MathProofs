# Exact Sylvester boosting gaps at every fixed support redundancy

For \(k\ge1\) and \(1\le t\le 2^k\), define the Sylvester boosting gap with \(t\) selected columns by

\[
\gamma(k,t)=\min_{\substack{S\subseteq\mathbb F_2^k\\|S|=t}}\min_{\substack{w_a\ge0\\\sum_{a\in S}w_a=1}}
\max_{0\ne r\in\mathbb F_2^k}
\left|\sum_{a\in S}w_a(-1)^{r\cdot a}\right|.
\]

This is the gap for the unsigned row-deletion matrix with its negative adjoined in the game formulation of Nie, Warmuth, Vishwanathan and Zhang. The full matrix has game value zero by the uniform distribution. [Original conjecture and normalization](https://proceedings.mlr.press/v30/Nie13.html), [Ken Wu's counterexample](https://kenwu-lab.wooqianghao.workers.dev/papers/colt-hadamard-boosting-gap/).

**Theorem.** If \(t\le k\), then \(\gamma(k,t)=1\). If \(t=k+s+1\le2^k\), its exact value is computable by finitely many rational linear programs of dimensions and number bounded by a function of \(s\) alone. The arithmetic outside those programs is polynomial in the bit length of \(k\) for fixed \(s\). An optimal support and rational weights have succinct descriptions by label multiplicities and label weights. For each fixed \(s\ge1\) and each parity \(\epsilon\), there is a computable rational \(c_{s,\epsilon}\) with

\[
\gamma(k,t)=1-\frac{2}{t/2+c_{s,\epsilon}}
\qquad(t\equiv\epsilon\pmod2,\ t \text{ sufficiently large}).
\]

The first three full-span regimes have the exact formulas

\[
\gamma(k,k+1)=1-\frac2{k+1},\qquad
\gamma(k,k+2)=1-\frac2{\lceil(k+2)/2\rceil},\qquad
\gamma(k,k+3)=1-\frac2{\lfloor(k+3)/2\rfloor}
\]

whenever their support sizes are admissible. In particular \(\gamma(4,6)=1/3\), completing the exact Sylvester side of Ken Wu's order-sixteen gap comparison. The algorithm also yields an exact rational optimizer at every valid fixed redundancy.

## From the game to a weighted binary code

If \(S\) is contained in a proper affine subspace, some nonconstant character of the ambient group is constant on \(S\), so the gap on \(S\) equals 1. No \(t\le k\) support spans affinely. For valid \(t\ge k+1\), there are affinely spanning supports, and uniform weights on any of them give a gap strictly below 1. It therefore suffices to consider the affinely spanning supports.

For such an ordered support, let \(C\le\mathbb F_2^t\) be the length-\(t\) binary code of restrictions of affine functions. Its dimension is \(k+1\), it contains the all-ones word, and its dual \(D\) has dimension \(s\) and minimum distance at least 4 if nonzero. Indeed all words in \(D\) have even weight, and a dual word supported on two positions would force the corresponding support points to coincide. Conversely any such dual \(D\) gives an affinely spanning support with the prescribed parameters. Choose a row basis of \(D^\perp\) starting with the all-ones row and take the \(t\) columns of the other \(k\) rows as points. Their distinctness follows from the exclusion of weight-two words in \(D\), and full affine rank follows from independence of the row basis.

Fix a support and a weight distribution \(w\). For each nonconstant affine word, its complement is another such word. The absolute character maximum is therefore

\[
1-2\min_{c\in C\setminus\{0,\mathbf1\}}\sum_{j\,:,c_j=1}w_j.
\]

The minimum on the right is positive for the uniform distribution. Maximizing it over \(w\) is equivalent, by rescaling, to taking the reciprocal of the minimum \(L\) of the sum of nonnegative coordinate costs \(x_j\) such that each nonempty proper codeword support has cost at least 1. In one direction divide optimal costs by their sum to get a probability distribution. In the other direction divide a distribution by its positive minimum word mass. Minimizing the gap over supports is equivalent to minimizing \(L\). The objective captures the weight of each codeword support under an optimized probability distribution.

## The fixed-size label programs

Take an \(s\times t\) generator matrix of \(D\) with columns \(h_j\in\mathbb F_2^s\). Its column multiset, with multiplicities \(n_h\), must satisfy three tests:

1. Its occurring labels span \(\mathbb F_2^s\).
2. The sum of its labels with multiplicity is zero.
3. For each \(a\ne0\) in \(\mathbb F_2^s\), the total number of columns with \(a\cdot h=1\) is at least 4.

These are exactly the rank, all-ones, and distance requirements above. The codeword supports are zero-sum subsets of the columns. A minimal nonempty zero-sum subset is a singleton with zero label, a pair of one repeated nonzero label, or one occurrence of each label in a distinct minimal dependent set of nonzero labels. The first two possibilities follow by taking out the indicated zero-sum subset whenever present. In the remaining case all labels are distinct and nonzero, and linear dependence over \(\mathbb F_2\) is equivalent to the vanishing sum of some nonempty subset. The full column set cannot itself be minimal since \(C\) has dimension \(k+1\ge2\) and hence has a proper nonzero word. Every nonempty proper zero-sum subset contains one of these minimal subsets. Nonnegativity then reduces the optimization to their constraints.

By averaging over permutations within each label, take a common cost \(x_h\) per label. The cost is

\[
L(n)=\min\sum_h n_hx_h,
\]

with \(x_0\ge1\) if \(n_0\ge1\), \(x_h\ge1/2\) if \(h\ne0\) and \(n_h\ge2\), and \(\sum_{h\in T}x_h\ge1\) for each minimal dependent set \(T\) of distinct occurring nonzero labels. Impose \(0\le x_h\le1\) without changing the minimum, by clipping any larger cost to 1. All constraints thus depend only on the class of each label's count.

Enumerate the six count classes \(0,1,2,3,\text{even}\ge4,\text{odd}\ge5\) for each label. The three tests on \(D\) depend only on this assignment. For the third, a single large count among the tested labels suffices, and otherwise the relevant counts are all specified. Give every large class its smallest representative count. If the difference from total \(t\) is nonnegative and even, distribute it among the large classes in steps of two. If there are none, require the difference to be zero. These are all realizable count assignments for the pattern.

For a fixed pattern the feasible cost polytope is independent of the distribution of that remaining mass. For every feasible cost vector, allocating the entire remainder to a cheapest large label is optimal. Therefore it suffices to enumerate one choice of receiving label and solve one constant-size linear program for each choice. This proves the exact algorithm and the optimal-support reconstruction. It uses only rational arithmetic and checks on at most \(2^s\) labels. The eventual affine formula follows too: for each fixed parity and sufficiently large \(t\), the same finitely many patterns and choices are feasible, and the vertices of their cost polytopes are independent of \(t\). The optimal \(L\) is the minimum of finitely many affine functions of \(t\). For \(s\ge1\), every large label costs at least \(1/2\), so \(L\ge t/2-O_s(1)\). For the matching upper bound, take four copies of each basis label, one zero label if \(t\) is odd, and put all remaining counts in one basis label. This passes all three tests for large \(t\), and its costs \(1/2\) on nonzero labels and 1 on zero labels are feasible. Hence \(L\le t/2+1/2\), and its eventual slope is \(1/2\). The intercept and a sufficient threshold are computable from the finitely many lines.

## Formulas and the order-sixteen instance

For \(s=0\), all labels are zero and \(L=t\). For \(s=1\), let \(m\) be the multiplicity of its unique nonzero label. The three tests give even \(m\ge4\). Therefore \(L=t-m/2\), minimized by the largest even \(m\le t\), giving \(L=\lceil t/2\rceil\).

For \(s=2\), call the three nonzero labels \(a,b,a+b\). Their multiplicities have the same parity. If even, every occurring nonzero label costs at least \(1/2\), and the minimum is at least \(t/2\). If odd, all three occur. Every nonsingleton costs at least \(1/2\) and the three costs sum to at least 1. With at most one singleton this gives at least \((t-n_0-1)/2+n_0\). If there are two singletons and one nonsingleton of multiplicity \(m\), the nonsingleton and the two singleton costs give at least \(1+(m-1)/2\), yielding the same bound. Three singleton labels violate the minimum-distance test. Hence the minimum is at least \(\lfloor t/2\rfloor\) for either parity, since odd nonzero multiplicities have odd total and then \(n_0\) has the opposite parity to \(t\).

For even \(t\ge6\), multiplicities \((2,2,t-4)\) and zero copies of the zero label attain \(L=t/2\). For odd \(t\ge7\), multiplicities \((1,3,t-4)\) attain \(L=(t-1)/2\) using costs \((0,1/2,1/2)\). Both pass all three tests. These bounds cover all admissible \(s=2\) cases. The reported \(t=6,k=4\) is instead \(s=1\); its value follows exactly from the even one-label formula without certifying any of the 8,008 individual Sylvester linear programs.

## Relation to previous work

Ken Wu's exact work identifies a larger gap for a different Hadamard matrix and provides the Sylvester support attaining at most \(1/3\). This argument supplies the matching exact lower bound for Sylvester and an arbitrary-fixed-redundancy theorem. The coding crossover follows the explicit equivalence perspective of the [MathProofs binary and nonprime-field code program](https://github.com/Dugongue/MathProofs/tree/main/NonprimeCodeToLattice), using an exact weighted invariant on a binary code. It also uses Fourier observations as in the [finite-phase response program](https://github.com/Dugongue/MathProofs/tree/main/SimultaneousPartiallyObservedLaws). The binary duality and linear-programming identities are standard. Priority for the patterned optimization and asymptotic exact formula remains provisional.
