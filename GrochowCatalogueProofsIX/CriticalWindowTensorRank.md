# GP-0219 — Tensor rank in the finite-field critical window

Fix an integer $s$. Let $a\leq b$, $N=ab$, and let $T$ be uniform in $\mathbb F_q^{a\times b\times(N+s)}$. As $N\to\infty$, its ordinary rank equals the rank of its $N\times(N+s)$ flattening with probability $1-o(1)$, uniformly over the field and the aspect ratio $a\leq b$. The same event admits a deterministic polynomial-time algorithm recovering a minimum-length decomposition. Thus the laws of these ranks have total variation distance $o(1)$ in this window.

## Deterministic spanning certificate

Let $U$ be the flattening image inside $V\otimes W$, with $\dim V=a$, $\dim W=b$. Let $S=U^\perp$ be the $j$-dimensional space of annihilating bilinear forms. For a basis $(v_1,\ldots,v_a)$ of $V$, set $E_i=\{B(v_i,-):B\in S\}\subset W^*$. Write $E_{1+i}=\{B(v_1+v_i,-):B\in S\}$. Assume each row evaluation $S\to E_i$ is injective and $E_1\cap E_i=0$ for $i>1$.

Consider the span $D$ of the rank-one subspaces $v_i\otimes E_i^\perp$ and $(v_1+v_i)\otimes E_{1+i}^\perp$ for $i>1$. These subspaces are contained in $U$. If $H\in D^\perp$, then row $H(v_i,-)$ is evaluation of a unique $B_i\in S$. Evaluation at $v_1+v_i$ agrees with some $B\in S$, giving
$$
(B_1-B)(v_1,-)+(B_i-B)(v_i,-)=0.
$$
By the trivial intersection the summands both vanish, and injectivity gives $B_1=B_i$. So $H=B_1$ and $D^\perp=S$. This proves $D=U$. For $a=1$ the single row evaluation is itself an identification, and the same conclusion applies.

Compute bases of the indicated annihilators, and use elimination to select from their rank-one tensors a basis of $U$. Expressing the flattening in that basis gives a tensor decomposition of length $\dim U$. Every ordinary tensor decomposition has length at least the rank of this flattening, proving optimality.

## Uniform probability estimate

Write $P_d=\prod_{i=1}^{d}(1-q^{-i})$, with $P_0=1$. The usual independent-column count gives the following probability for flattening corank $j=N-\dim U$, for $j\geq\max(0,-s)$:
$$
q^{-j(j+s)}\frac{P_NP_{N+s}}{P_jP_{j+s}P_{N-j}}.
$$
Each nonempty product is bounded below by the fixed positive product $\prod_{i\geq1}(1-2^{-i})$. Thus for fixed $s$ the corank tail beyond $J$ is uniformly bounded by a constant times $\sum_{j>J}2^{-j(j+s)}$, which tends to zero as $J\to\infty$.

Conditional on $j$, $S$ is a uniform $j$-space. Sample its ordered basis by drawing $j$ independent uniform forms and conditioning on linear independence of the draws. For fixed $j$, the conditioning event has probability $1-o(1)$ uniformly as $N\to\infty$. Before conditioning, for each $i>1$ the output columns of evaluations on $v_1$ and on $v_i$ form a uniform $b\times 2j$ matrix. Its probability of failing full column rank is at most $\sum_{t=0}^{2j-1}q^{t-b}$. A full-rank matrix is exactly the required injectivity and trivial-intersection condition for its two evaluation images. A union bound over $i$ gives $o(1)$ for each fixed $j$, uniformly because $a\leq b$ and $b\to\infty$. The case $a=1$ is automatic. First restricting to bounded corank and then letting the corank bound increase proves the result.

This answers the fixed-offset critical window and leaves other offset scalings outside its statement. The companion critical-window stabilizer analysis is [Critical Rectangular Stabilizers](https://github.com/Dugongue/MathProofs/blob/3454ca222e13e2f12bf232b920771763bf8a7d1a/GrochowCatalogueProofsVIII/CriticalRectangularStabilizers.md). The finite-field slice-space formulation is developed by [Byrne and Cotardo](https://doi.org/10.1016/j.laa.2023.11.019). Their structured slice-space constructions and the [analysis by Randriambololona of spans of sampled rank-one matrices](https://arxiv.org/abs/1501.05978) concern different sampling models from the uniform flattening image here.
