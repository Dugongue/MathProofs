# Tensor isomorphism in positive stationary sources

Equivalence under one invertible linear recoding of the alphabet is Tensor Isomorphism-complete over \(\mathbb Q\), even for strictly positive stationary finite-state sources with the same rapidly mixing hidden kernel. Every pair of observations in the constructed sources is independent and uniform. Their histograms have the iid multinomial law at every window length, and every memoryless channel with at most three outputs yields an iid process. The ordered distribution of three consecutive symbols retains the entire tensor-isomorphism instance.

## Problem and theorem

Let \(E=\mathbb Q^d\) be spanned by the alphabet basis vectors \(e_a\). A weighted word representation consists of a row \(\lambda\), a column \(\gamma\), and matrices \(A_a\). Extend \(x\mapsto A_x=\sum_a x_a A_a\) linearly. Its ordered word form is
\[
 F_k(x_1,\ldots,x_k)=\lambda A_{x_1}\cdots A_{x_k}\gamma .
\]
Two representations are equivalent under an alphabet recoding if there is \(M\in\mathrm{GL}(E)\) with \(F_k(x_1,\ldots,x_k)=F'_k(Mx_1,\ldots,Mx_k)\) for every \(k\ge 0\). The recoding acts on rational linear observables. The input stochastic kernels themselves have nonnegative probabilities.

For the stationary source subclass, \(\lambda=\pi\) is a stationary probability row, \(\gamma=\mathbf1\) is the all-ones state column, and the labeled transition matrix \((A_a)_{ij}\) is the probability of emitting \(a\) and moving from state \(i\) to state \(j\). The unlabeled kernel \(K=\sum_a A_a\) is row stochastic and \(\pi K=\pi\).

**Theorem.** Alphabet recoding of weighted word representations is TI-complete under deterministic polynomial-time many-one reductions over \(\mathbb Q\). Hardness holds for stationary sources with \(1+d+d^2\) hidden states and rational labeled matrices \(A_a\) with every entry at least \(1/(6d^3)\). Their reachable and observable dimension is at most \(1+2d\). At fixed alphabet dimension, all instances in the reduction share both \(K\) and \(\pi\). The kernel contracts total variation by a factor at most \(1/2\) per step. For any chosen rational \(0<\eta<1\), these instances can also have every next-symbol conditional probability in \([(1-\eta)/d,(1+\eta)/d]\). All one- and two-time marginals are uniform, the histogram law is iid at every length, and every fixed memoryless channel with at most three outputs produces iid observations. The equivalence remains TI-complete if recodings of stationary sources are required to fix \(u=\sum_a e_a\).

This is an exact decision result with rational matrices given explicitly. It applies even when words are strictly positive and two sources have identical data after every ternary memoryless channel.

## A hidden source with one alternating block

Let \(b\in E^*\) be the uniform covector \(b(e_a)=1/d\) and let \(C=\{\ell\in E^*:\ell(u)=0\}\), the space of zero-sum covectors. Take an alternating trilinear form \(D\in\bigwedge^3 C\). Its coefficients vanish if any argument is \(u\). For a positive rational \(\epsilon\), define
\[
 q(a,c,e)=d^{-3}+\epsilon D(e_a,e_c,e_e).
\]
Choose \(\epsilon=\eta/(d^3 B)\) with \(B=1+\sum_{a,c,e}|D(e_a,e_c,e_e)|\). Then \(q\) is a positive joint probability table with all proper marginals uniform, and all its entries lie in \([(1-\eta)d^{-3},(1+\eta)d^{-3}]\).

First consider a stationary sequence of independent three-symbol blocks with law \(q\), viewed from a uniformly random phase. An explicit edge-emitting source for it has states \(\star\), \((a)\), and \((a,c)\). Its nonzero original labeled transitions \(P_e\) are
\[
  \star \xrightarrow[\ 1/d\ ]{a}(a),\qquad
  (a)\xrightarrow[\ 1/d\ ]{c}(a,c),\qquad
  (a,c)\xrightarrow[\ d^2q(a,c,e)\ ]{e}\star.
\]
The unlabeled transition from \((a,c)\) to \(\star\) has probability 1. The two earlier phases transition with probability \(1/d\) per possible next state. Hence \(P=\sum_e P_e\) is independent of \(D\). Its stationary law gives weights \(1/3\), \(1/(3d)\), and \(1/(3d^2)\) per state in the three respective phases. Directly applying \(P\) cycles the phase and gives the stated uniform law within each phase. In the stationary process any complete block emits law \(q\). Taking a proper fragment of an end block gives an iid uniform fragment because all proper marginals of \(q\) are uniform. Thus the original ordered \(k\)-word form \(G_k\) is the average, over the three phases, of the ordered tensor products of \(b\) at fragment positions and \(b^{\otimes3}+\epsilon D\) at complete blocks. In particular,
\[
      G_1=b,\qquad G_2=b^{\otimes2},\qquad G_3=b^{\otimes3}+\tfrac{\epsilon}{3}D .
\]

Fix \(0<\rho<1\) rational, and use labeled matrices
\[
                A_e=(1-\rho)P_e+\rho\,b(e_e)\mathbf1\pi .
\]
Every entry is strictly positive. The hidden kernel is \(K=(1-\rho)P+\rho\mathbf1\pi\), still independent of \(D\), and \(\pi\) is stationary. For two hidden probability rows \(s,t\), \((s-t)K=(1-\rho)(s-t)P\), so total variation contracts by at least the reset probability each step. Set \(\rho=1/2\).

In the stationary source each step independently either uses \(P_e\) or emits a uniform symbol and refreshes the hidden state from \(\pi\). Algebraically, expand the product defining \(F_k\) by the subset of reset positions. Each reset inserts \(\mathbf1\pi\). It therefore separates the remaining positions into consecutive original runs, multiplying their \(G_j\) forms and contributing one factor \(b\) for each reset symbol. The coefficient of a reset pattern with \(r\) resets is \(\rho^r(1-\rho)^{k-r}\). All \(F_k\) are therefore determined equivariantly by \(b\) and \(\epsilon D\). At length three, every pattern with a reset has original runs of length at most two, so
\[
                  F_3=b^{\otimes3}+\frac{\epsilon(1-\rho)^3}{3}D
                     =b^{\otimes3}+\tfrac{\epsilon}{24}D.
\]
The reset leaves any pair of observations uniform and independent, whether in the same original run or different runs. This follows by first fixing the reset pattern, then the phase within each original run, and using the uniform proper marginals of its blocks. The next-symbol bound holds even given a hidden state. Its original emission probabilities are uniform in the first two phases and \(d^2 q(a,c,e)\) in the third phase. Averaging over a hidden-state posterior and over the reset preserves the bound.

The \(d^2\) third-phase states contribute at most \(d\) dimensions to a linear realization. Among row vectors supported on those states, take the kernel of the map to their \(d\) aggregate emission coordinates. Every vector in that kernel has row sum zero since the emission probabilities sum to one. It annihilates each \(P_e\), since a third-phase transition always goes to \(\star\), and it annihilates the reset term by its zero row sum. Quotienting the row state space by this kernel leaves at most \(1+2d\) dimensions, with unchanged word forms.

## What unordered and coarsened observations see

Evaluating \(F_k(x,\ldots,x)\) gives the multivariate probability generating polynomial for the histogram of the \(k\)-symbol window. Since \(D(x,x,x)=0\), the block and reset formulas give exactly \(b(x)^k\) for every \(k\). Thus every such histogram has the same multinomial law as independent uniform symbols.

For a memoryless observation channel with outputs \(y\), let \(x_y\in E_{\mathbb R}\) have coordinates \((x_y)_a=\Pr(y\mid a)\). We have \(\sum_y x_y=u\). If the channel has at most three outputs, the span of their images in \(E_{\mathbb R}/\mathbb R u\) has dimension at most two. The form \(D\) descends to that quotient and vanishes on every triple of channel vectors. Every complete-block factor becomes a product of \(b(x_y)\), and the reset expansion gives
\[
                 \Pr(y_1,\ldots,y_k)=\prod_{i=1}^{k} b(x_{y_i}).
\]
For nonzero \(D\), the bound of three is sharp. There are three distinct letters \(a,c,e\) with \(D(e_a,e_c,e_e)\ne0\). Partition the alphabet into those three singleton letters and a fourth class containing the rest. The rest is nonempty because a nonzero alternating 3-form on the contrast quotient requires \(d\ge4\). Under this deterministic four-output channel, the ordered probability of the three designated singleton symbols differs from the product of their uniform-source marginal probabilities.

## Isomorphism hardness

Grochow and Qiao’s Theorem 1.10, with its alternating output option for action 4, reduces ordinary TI over \(\mathbb Q\) to isomorphism of alternating trilinear forms under one invertible map in all slots. If the resulting form is on a space of dimension \(n\), identify its covector space with \(C\) for \(d=n+1\). Use the stochastic construction above for both forms. [Grochow and Qiao, *On the Complexity of Isomorphism Problems for Tensors, Groups, and Polynomials IV*, Theorem 1.10](https://arxiv.org/html/2306.16317#S1.SS4)

Any recoding of the sources fixes \(b\) by the length-one identity. The centered length-three identity then gives an isomorphism of their scaled alternating forms on \(E\). Each input form lies in \(C^{\otimes3}\). Its first contraction image, obtained by plugging arbitrary arguments into the other two slots, is an intrinsic covector subspace \(C_D\subseteq C\). Alternation makes all three such images equal. The form lies in \(C_D^{\otimes3}\), as seen by choosing a basis extending a basis of this image. An ambient recoding maps the support subspaces isomorphically and maps the restricted tensors by the same map in all slots. Extend that support isomorphism arbitrarily to an isomorphism between the full contrast spaces. Thus ambient recoding cannot identify different alternating-form isomorphism classes on the fixed \(n\)-dimensional space. Conversely a contrast isomorphism extends over \(E^*=\mathbb Q b\oplus C\) by fixing \(b\). The dual invertible letter map fixes \(u\). Every word form agrees under this recoding, by the block and reset identities.

The use of input-dependent positive scales causes no change to this reduction if one uses a shared scale on each pair. Explicitly use the same \(B\) in both instances by summing the absolute coefficients of both forms and adding 1. All formulas use rational operations on polynomial-size tensors and output \(d\) matrices of side \(1+d+d^2\), with polynomial bit length. This proves hardness with the stated statistical promises.

## Reduction to ordinary TI

For completeness, arbitrary weighted word representations reduce to TI after an exact linear-algebra computation. Restrict the state space to the span of the columns \(A_w\gamma\) and quotient by its subspace annihilated by every \(\lambda A_v\). Both subspaces are invariant under all letter transitions. Generate the two spans by extending bases until stable, which takes a polynomial number of matrix and Gaussian-elimination operations. A basis can be represented by words of length at most the original state dimension; over \(\mathbb Q\), the word products and the Gaussian eliminations have polynomial bit complexity. This is the reachable and observable realization of the word series. [Carlyle and Paz, *Realizations by Stochastic Finite Automata*](https://doi.org/10.1016/S0022-0000(71)80005-3)

On minimal realizations there is a recoding \(M\) exactly when there is an invertible state map \(X\) with
\[
 X\gamma=\gamma',\qquad \lambda' X=\lambda,\qquad
 XA_x=A'_{Mx}X\quad(x\in E).
\]
Indeed, under a proposed recoding, the map \(A_w\gamma\mapsto A'_{Mw}\gamma'\) respects linear relations. Pair a relation with every observable row on the primed side, use equality of word forms and invertibility of \(M\), then use observability. Reachability on both sides and the reverse argument give an invertible map. The equations imply word-form agreement by multiplication. Distinct minimal dimensions can be rejected, and two zero series can be accepted directly.

Build a 3-tensor on \((V\oplus\mathbb Q a)\otimes(V^*\oplus\mathbb Q c)\otimes(E^*\oplus\mathbb Q t)\), where \(V\) is the minimal state space. Use the transition tensor \(A\) in \(V\otimes V^*\otimes E^*\), put \(\gamma\otimes c\otimes t\) and \(a\otimes\lambda\otimes t\) in their indicated blocks, and put \(a\otimes c\otimes t\) as a unit marker. Require block preservation, with inverse-transpose links between \(V,V^*\) and between the two one-dimensional blocks of \(a,c\). If \(a\) scales by \(s\), then \(c\) scales by \(s^{-1}\). The unit marker fixes the scale of \(t\). The endpoint equations are then exact after rescaling the state map by \(s^{-1}\); this rescaling leaves transition conjugacy unchanged. The action on \(E^*\) is the inverse transpose of \(M\). Hence linked-partition isomorphisms exist exactly for recodable series. For the promised stationary sources, length one forces preservation of the common uniform covector \(b\). To impose \(Mu=u\) as well, partition \(E^*=C\oplus\mathbb Q b\), and fix the scale of \(\mathbb Q b\) by adding the unit marker \(a\otimes c\otimes b\) in its own block. Preserving \(C\) and \(b\) imposes exactly those two conditions. Grochow and Qiao’s Theorems 5.3 and 5.1 convert the linked-partition instance to ordinary TI. The number of blocks is constant, so the resulting tensor side lengths are linear in the minimal state and alphabet dimensions. [Linked partition and partitioned TI reductions](https://arxiv.org/html/2306.16317#S5)

For comparison, fixed-alphabet word equality with a prescribed \(M\) requires only Gaussian elimination. In the direct sum of the two representations, test whether its difference row vanishes on the reachable span. If there are \(N\) states in that direct sum then words of length at most \(N-1\) span it. An invertible recoding supplied as a certificate can therefore be verified without enumerating all these words.

## Evidence and scope

The project’s AutomataCoefficientBridge20260906 studies synchronized word products and the information loss caused by merging word order. RationalSeriesHankel_20260908 supplies the adjacent finite-realization and Hankel viewpoint. The proof above independently establishes the needed word-representation and reset identities. Relative to spectral learning from short observation statistics, the construction makes every two-observation table rank one while preserving the full ordered third-order orbit problem. It concerns exact recoding of explicit rational sources. Approximate learning, latent-parameter recovery under spectral separation, and recoding constrained to an alphabet permutation are distinct problems. [Hsu, Kakade, and Zhang, *A Spectral Algorithm for Learning Hidden Markov Models*](https://arxiv.org/abs/0811.4413) · [Kakade et al., *Learning Hidden Markov Models Using Conditional Samples*](https://arxiv.org/abs/2302.14753)

The proof is mathematical prose without a Lean kernel receipt. Optimization.py verifies 1,365 exact word and reset identities through length 5, 126 histogram masses, 160 pair marginal entries, all 81 deterministic ternary channels, and signed-recoding and four-output controls on a four-letter construction. The literature check located the cited realization and alternating tensor-isomorphism theorems. Priority for their combination with these statistical promises remains open.

