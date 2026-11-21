# Shared tree cores for worst-case approximation of many tensors

Let $A_1,\ldots,A_K$ be dense rational tensors on one tree of $m\ge3$ nodes, with positive rational scales $s_i$, and let target bond caps be $r_e$. All comparisons use common nonroot cores and independent root cores. Let $E_\star$ be the infimum over such shared representations of
$$
\max_i \|A_i-X_i\|_F^2/s_i^2.
$$
Fix $0<\varepsilon\le1$. There is a deterministic algorithm, polynomial in the written data size and $1/\varepsilon$, with worst-case error at most $(1+\varepsilon)\alpha E_\star$ and a single shared representation with caps at most
$$
r_e \min\!\left(K,\,1+\left\lceil\frac{\log K}{\log(1+\varepsilon)}\right\rceil\right)
$$
for every edge, where $\alpha=m-1-\sum_{\mathrm{pairs}}1/[2(r+3)]$ is the rational paired-cut factor for the original caps. It also handles $E_\star=0$. The method gives polynomial-size rational cores and an error certificate for every channel. [Paired-cut approximation](paired-cuts.md)

## Proof

Put $B_i=A_i/s_i$. Input scaling is equivalent to scaling the root core of each channel. For a nonempty subset $J$ of the still uncovered channels, stack the $B_i$, $i\in J$, into one tensor with an added channel index at the root. A tree tensor for the stack yields a common collection of nonroot cores and one root slice for each channel. Conversely every common representation at these caps stacks to a feasible tree tensor. Thus the minimum squared Frobenius error for the stack is the infimum of the sum of squared errors on $J$. In particular it is at most $|J|E_\star$, since an arbitrarily close common minimax comparator is feasible for every such sum. The paired-cut routine returns a rational common representation with actual mean loss $c_J\le\alpha E_\star$.

Mark every $i\in J$ whose actual squared error is at most $(1+\varepsilon)c_J$, and save the common tree cores and the marked channels' root slices. If $c_J=0$, every channel is marked. Otherwise the sum of losses shows that fewer than $|J|/(1+\varepsilon)$ channels remain uncovered. At least one channel is marked at every trial. Hence after at most $\min(K,1+\lceil\log K/\log(1+\varepsilon)\rceil)$ trials every channel has a certified approximation at the desired error. The algorithm never estimates $E_\star$.

Combine the saved shared representations by direct sum along every bond. At a nonroot vertex permit nonzero blocks only when the incoming labels carry the same trial index as the outgoing label, filling that block with the corresponding old core. At the root, for a channel assigned to a particular trial use its old root slice on the block where all incident labels carry that trial index, scaled by $s_i$, and put zero elsewhere. The resulting single family of nonroot cores represents exactly the individually certified approximants. Each bond width is the sum of at most the stated number of original widths. The block data has a polynomial-size sparse encoding, with only the saved blocks stored. If dense cores are required, the algorithm may form the dense stack of the obtained approximants, within the dense input size up to polynomial factors, and apply exact rational tree descent. Its cut ranks cannot exceed the direct-sum widths, and sharing follows again by splitting the root channel index. [Exact tree rank reconstruction](https://github.com/Dugongue/MathProofs/blob/main/ExactTreeNetworkDescent/PROOFS.md)

The common rank inflation is logarithmic in the number of channels for fixed $\varepsilon$. This is a bicriteria result for simultaneous worst-case error. The reference optimum uses the original caps, and each output channel's squared error is measured separately.

## A near-optimal variant for fixed rank parameters

Use the deterministic relative-error solver for a tree with tolerance $\varepsilon/3$ at each stack, and mark channels within $1+\varepsilon/3$ times the current mean. The stack changes only the physical dimension of the root and leaves the number of vertices and all incident cap products unchanged. The guarantee is at most $(1+\varepsilon/3)^2 E_\star \le (1+\varepsilon)E_\star$ for $0<\varepsilon\le1$. The caps increase by at most $\min(K,1+\lceil\log K/\log(1+\varepsilon/3)\rceil)$, and the running time remains fixed-parameter tractable in the order, cap products and $1/\varepsilon$, with polynomial dependence on the full written panel size. [Deterministic relative-error solver](relative-error.md)

## Verification

Paper proof. A Lean companion checks the scalar covering bound used to count the unmarked channels.
