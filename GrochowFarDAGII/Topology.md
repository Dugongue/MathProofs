# Quartic path-law error for stationary Markov compression

A finite Markov chain observed through a partition can have memory even when its one-step label transitions are fitted exactly. If the forward and reversed block transition probabilities are both close to their block averages, and the conditional filters contract a projective distance, the entire label trajectory has a quantitative Kullback–Leibler bound. The bound is quartic in the relative defect for reversible chains. A four-state reversible chain attains that order. Retaining a window of labels gives a further geometric error reduction, with an explicit cost in the size of the description.

This gives a certificate for a fixed observable and a specified family of high-level models in the State Space Compression framework of Wolpert, Grochow, Libby, and DeDeo. The loss is the divergence of observable path laws, and the model size can be chosen by the length of its retained label window. [Wolpert et al.](https://arxiv.org/abs/1409.7403).

## Model and certificate

Let $P$ be a transition matrix on a finite state space with strictly positive stationary law $\pi$. Partition the space into nonempty blocks $B_i$, write $\lambda_i=\pi(B_i)$, and let $\pi_i$ be the stationary law conditioned on $B_i$. Take the initial microstate from $\pi$ and let $Y_t$ be its block label. Put
$$
 q_{ij}(x)=\sum_{y\in B_j}P(x,y),\qquad A_{ij}=\sum_{x\in B_i}\pi_i(x)q_{ij}(x).
$$
The first-order model uses transition matrix $A$ and initial law $\lambda$. Write $K_{ij}$ for the rectangular matrix of transitions from $B_i$ to $B_j$. If $A_{ij}=0$, the entire matrix $K_{ij}$ vanishes. Call all other blocks admissible, and require every entry of every admissible $K_{ij}$ to be strictly positive.

Let $P^*(y,x)=\pi(x)P(x,y)/\pi(y)$ be the reversed matrix. Define $q^*_{ji}$ and $A^*_{ji}$ with $P^*$ in place of $P$. On admissible pairs, $A^*_{ji}=\lambda_i A_{ij}/\lambda_j>0$. Suppose that for every such pair and every $x\in B_i,y\in B_j$,
$$
 \left|q_{ij}(x)/A_{ij}-1\right|\le\varepsilon_f,qquad
 \left|q^*_{ji}(y)/A^*_{ji}-1\right|\le\varepsilon_b
$$
for $0\le\varepsilon_f,\varepsilon_b<1$. Set
$$
 \Theta=\max_{i,j,x,x',y,y'}
   \frac{K_{ij}(x,y)K_{ij}(x',y')}{K_{ij}(x,y')K_{ij}(x',y)},\quad
 \kappa=\frac{\sqrt\Theta-1}{\sqrt\Theta+1},\quad
 L_b=\log\frac{1+\varepsilon_b}{1-\varepsilon_b},
$$
where the maximum uses each admissible block's own row and column sets. These quantities are directly computable. For rational data, a rational bound $\kappa\le \bar\kappa<1$ can be certified by checking every cross ratio against $((1+\bar\kappa)/(1-\bar\kappa))^2$.

**Theorem.** Write $\mathcal P_T$ for the law of $Y_0,\ldots,Y_T$, and $\mathcal Q_T^{(1)}$ for the first-order model's law. With natural logarithms,
$$
 D(\mathcal P_T\|\mathcal Q_T^{(1)})
 \le 4\varepsilon_f^2
 \sum_{t=0}^{T-1}
    \tanh^2\!\left(\frac{L_b(1-\kappa^t)}{4(1-\kappa)}\right).
$$
In particular this is at most
$(T-1)_+\varepsilon_f^2\varepsilon_b^2/[(1-\varepsilon_b)^2(1-\kappa)^2]$.
For $m\ge2$, let $\mathcal Q_T^{(m)}$ start from the true initial $m$-label marginal, using the whole true marginal if $T+1<m$. Take its transition rows to be the true stationary conditional laws given the previous $m$ labels. Then
$$
 D(\mathcal P_T\|\mathcal Q_T^{(m)})
 \le (T-m)_+\frac{4\varepsilon_f^2}{1-\varepsilon_f}
 \tanh^2\!\left(\frac{\kappa^{m-1} L_b}{4(1-\kappa)}\right).
$$
The model needs at most $b^m$ suffix states for $b$ labels. Dividing the bounds by $T$ and passing to the limit bounds the excess predictive entropy rate of these models. In the reversible case one may use $\varepsilon_f=\varepsilon_b=\varepsilon$.

## Proof

For positive vectors put $d_H(u,v)=\max_x\log(u_x/v_x)-\min_x\log(u_x/v_x)$. Scaling either vector leaves this quantity unchanged, and it satisfies the triangle inequality by subadditivity of oscillation. For positive probability vectors the total variation distance, with convention $\operatorname{TV}(u,v)=\frac12\sum_x|u_x-v_x|$, is at most $\tanh(d_H(u,v)/4)$. To see the constant, write $r=u/v$ and let $a,b$ be its minimum and maximum. If $a=b$, the vectors agree. Otherwise $a\le1\le b$, and applying the upper chord of $(r-1)_+$ on $[a,b]$ and using $\mathbb E_v r=1$ gives
$$
 \operatorname{TV}(u,v)\le \frac{(b-1)(1-a)}{b-a}.
$$
For a fixed ratio $R=b/a$, this expression is bounded by $(\sqrt R-1)/(\sqrt R+1)$, because $Ra+a^{-1}\ge2\sqrt R$. The sharp conversion is a finite instance of the result of Cohen and Fausti. [Cohen and Fausti](https://arxiv.org/abs/2309.02413).

For a positive block $K$, multiplication $u\mapsto uK$ contracts $d_H$ by at most the coefficient computed from its cross ratios. For completeness, use $u_\alpha(x)=v_x\exp(\alpha r_x)$ with $r_x=\log(u_x/v_x)$, $0\le\alpha\le1$. The derivative of $\log(u_\alpha K)_y$ is the expectation of $r_x$ with weights proportional to $u_\alpha(x)K_{xy}$. For another column $y'$ the two weight laws have likelihood-ratio spread at most $\Theta$, since normalizations and $u_\alpha$ cancel from the cross ratios. Their total variation is at most $\kappa$ by the previous inequality. Thus their expectations of $r$ differ by at most $\kappa\operatorname{osc}(r)$. Integrate over $\alpha$ and take the largest difference across output columns. Normalizing the block product to a probability law does not change its projective distance. This is the finite positive-matrix Birkhoff contraction used in filtering. [Birkhoff](https://www.ams.org/tran/1957-085-01/S0002-9947-1957-0087058-6/S0002-9947-1957-0087058-6.pdf), [Le Gland and Oudjane](https://doi.org/10.1214/aoap/1075828050).

Let $F_{ij}(\mu)=\mu K_{ij}/(\mu K_{ij}\mathbf 1)$ be the filter update from one observed label to the next. Its stationary reference satisfies
$$
 F_{ij}(\pi_i)(y)=\pi_j(y)q^*_{ji}(y)/A^*_{ji}.
$$
This follows from the identity $\pi(x)P(x,y)=\pi(y)P^*(y,x)$ after summing over $B_i$. Hence its distance from $\pi_j$ is at most $L_b$. Along any positive-probability history ending at time $t$ in block $i$, let $\mu_t$ be the conditional hidden law. It starts at $\mu_0=\pi_{Y_0}$. The filter contraction and the reference error give
$$
 d_H(\mu_t,\pi_i)\le L_b(1-\kappa^t)/(1-\kappa).
$$
In particular the bound is uniform over histories, even when a particular history has very small probability.

If two possible hidden laws on $B_i$ have total variation $v$, their predictions of label $j$ differ by at most $2\varepsilon_f A_{ij}v$. This follows by integrating $q_{ij}$ against their difference, using the oscillation bound $2\varepsilon_f A_{ij}$. Against the stationary reference the predicted row is $A_i$. For two categorical laws $p,q$ on their common support, $D(p\|q)\le\sum_j(p_j-q_j)^2/q_j$ by $\log x\le x-1$. Taking $q=A_i$ and summing the resulting bound along the path by the divergence chain rule proves the first inequality. Its simpler bound follows from $\tanh u\le u$ and $L_b\le2\varepsilon_b/(1-\varepsilon_b)$. The first predicted transition is fitted exactly under stationary initialization.

For the $m$-label model, at time $t\ge m-1$ compare the full filter with the filter conditioned only on the suffix $Y_{t-m+1},\ldots,Y_t$. The latter initializes at the stationary conditional law of its first block. Their initial distance is at most $L_b/(1-\kappa)$, and they then follow the same $m-1$ filter updates, so their final distance is at most $\kappa^{m-1}L_b/(1-\kappa)$. The suffix prediction puts at least $(1-\varepsilon_f)A_{ij}$ on each admissible next label. The same categorical divergence calculation with this denominator gives the second inequality. The first $m$ labels and the next transition agree exactly, leaving at most $(T-m)_+$ summands.

The path divergence from the fitted order-$m$ model is the sum of the reductions in conditional log loss from using the full past instead of the retained window. By stationarity, the expected prediction loss of the fitted model is $H(Y_m\mid Y_0,\ldots,Y_{m-1})$ on each later step. The full-past prediction losses decrease to the entropy rate $h(Y)$, since conditional entropy decreases with more conditioning and is bounded below. The normalized path divergence therefore tends to $H(Y_m\mid Y_0,\ldots,Y_{m-1})-h(Y)$. For a prescribed window this fitted model minimizes the path divergence, since replacing a fitted transition incurs the conditional categorical divergence from that row to the replacement. For example, replacing $A$ by another first-order kernel $A'$ with the same initialization adds $T\sum_i\lambda_i D(A_i\|A'_i)$ to the stationary path divergence. Pinsker's inequality also gives a total variation bound of $\sqrt{D/2}$ for the complete trajectory and for every statistic of that trajectory. Under equal prior odds, the minimum probability of error in telling the two path laws apart is half the sum of their pointwise minima, or $(1-\operatorname{TV})/2$. Thus the path bound directly limits statistical distinguishability. [Degenne and Luccioli, binary testing source](https://github.com/RemyDegenne/testing-lower-bounds/blob/6c303c98977be5a81e5a659823d83038d48a9a04/TestingLowerBounds/Testing/Binary.lean).

## Arbitrary starting laws

The quartic first-order formula uses stationary initialization. For a different microstate prior initialize the first-order model with its true label marginal. The first forecast can contribute as much as order $\varepsilon_f^2$ to KL and contributes at most $\varepsilon_f^2$ under the assumptions. After one admissible block, even for a prior with zeros, the filter is positive and its distance to the stationary reference is at most $\log\Theta+L_b$. Indeed the cross ratio bound also bounds the ratio between two column ratios of $uK$ and $vK$ for arbitrary nonzero nonnegative inputs. Expand numerator and denominator as sums of pairs of entries and compare them term by term. At time $t\ge1$, one can thus use
$$
 \kappa^{t-1}(\log\Theta+L_b)+L_b(1-\kappa^{t-1})/(1-\kappa)
$$
in place of the stationary projective radius. This gives a decaying initialization term in the path bound.

## Sharp reversible example

Take four microstates $(i,u)$ with $i\in\{0,1\}$ and $u\in\{-1,1\}$, observed only through $i$. For $0<\varepsilon<1/2$, use the symmetric stochastic matrix
$$
 P((i,u),(j,v))=\tfrac14[1+\varepsilon(-1)^{i+j}(u+v)].
$$
The stationary law is uniform, $A_{ij}=1/2$, and both relative defects equal $\varepsilon$. All allowed entries are positive and $\Theta=(1-4\varepsilon^2)^{-1}$, so $\kappa=O(\varepsilon^2)$ as $\varepsilon\to0$. Conditional on the last two labels $i,j$, the next label $k$ has probability $[1+\varepsilon^2(-1)^{i+k}]/2$. This follows by averaging the forward block probabilities against the preceding reference update, whose hidden sign has conditional mean $\varepsilon(-1)^{i+j}$.

For $T=2$, the true path divergence from the fitted independent fair labels is
$$
 b(\varepsilon^2),\qquad
 b(x)=\tfrac12[(1+x)\log(1+x)+(1-x)\log(1-x)].
$$
For every $T\ge2$ it is at least $(T-1)b(\varepsilon^2)$, since conditioning on the entire past can only reduce expected log loss from conditioning on the last two labels. Here $b(x)=x^2/2+O(x^4)$. Thus the stationary first-order KL rate has order $\varepsilon^4$ in this family. The total variation on a three-label path is exactly $\varepsilon^2/2$.

The two defects can also vary independently. Replace $\varepsilon(u+v)$ by $\alpha u+\beta v$ with $\alpha,\beta\ge0$ and $\alpha+\beta<1$. The law remains uniform stationary, with forward defect $\alpha$, reversed defect $\beta$, and cross-ratio maximum $[1-(\alpha-\beta)^2]/[1-(\alpha+\beta)^2]$. The two-label forecast bias becomes $\alpha\beta$, and the path divergence is at least $(T-1)b(\alpha\beta)$. This gives the analogous sharp product of squared defects when the contraction is bounded away from one. If $\beta=0$, the labels are independent and fair in stationarity. A start concentrated on one hidden sign moves the first label-transition probabilities by $\alpha/2$ from fairness.

## Source crossing and verification

The source crossing combines the conditional-divergence viewpoint from formalized statistical testing with classical projective filter contraction. The archived testing source develops conditional KL through joint laws and makes the chain-rule accumulation the appropriate error notion. The proof here applies this to the label trajectory rather than measuring only one-step transition error. The new quantitative step isolates the product of the forward and reversed deviations and propagates it through label history. The positive-block cross ratio gives a direct check of the filtering hypothesis. [Degenne and Luccioli, conditional KL source](https://github.com/RemyDegenne/testing-lower-bounds/blob/6c303c98977be5a81e5a659823d83038d48a9a04/TestingLowerBounds/Divergences/KullbackLeibler/CondKL.lean).

Geiger, Petrov, Kubin, and Koeppl already use KL rate between the projected process and a reduced Markov model, and later work treats higher-order approximation. Hilbert-metric filter stability and the total variation conversion supply the ingredients for the estimate. The contribution here is the forward–reverse quartic certificate for the full path, its explicit memory tradeoff, and the reversible example showing the order of loss. Priority for the combined statement remains unverified. [Geiger et al.](https://arxiv.org/abs/1304.6603), [Geiger and Wu](https://arxiv.org/abs/1608.04637).

The companion control evaluates all $2{,}048$ label paths of length eleven for each of three noise values and checks both fitted model orders. Path probabilities are computed with rational arithmetic, with floating-point logarithms for the divergence comparisons. The argument above is a mathematical proof. It has no Lean formalization. [Topology.py](Topology.py).
