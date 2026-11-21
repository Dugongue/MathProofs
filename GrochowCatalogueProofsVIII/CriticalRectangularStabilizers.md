# Stabilizers in the sharply rectangular critical window

## GP-0163

Fix a finite field $k=\mathbb F_q$ and an integer $s$. Let a uniform tensor have format $a\times b\times(ab+s)$, with $ab\to\infty$ and $b/a\to\infty$. Its full product-general-linear stabilizer is described, with probability $1-o(1)$, by the random defect of its largest flattening. The description includes the unipotent factors and their conjugation actions. It also gives linear-algebraic isomorphism witnesses against arbitrary targets on the accepted source class. This addresses the critically unbalanced regime with an additional separation of the two smaller sides. [Average-case tensor-isomorphism context](https://arxiv.org/abs/1708.04501)

### A stabilizer description

Write $V,W$ for the first two spaces, $Z^*$ for the dual of the third, and $F:Z^*\to V\otimes W$ for the tensor. Put $N=ab$, $U=\operatorname{im}F$, $K=\ker F$, and $k_0=N-\dim U$. Write $S=U^\perp\subset V^*\otimes W^*$. An explicit acceptance test is that
$$
\Phi:V\otimes S\longrightarrow W^*,\qquad v\otimes z\longmapsto z(v,-)
$$
is injective. Set $L=\operatorname{im}\Phi$ and choose a complement $L_0$ in $W^*$. Regard the first two local maps as $A$ on $V$ and $B_*$ on $W^*$, where $B_* = B^{-\mathsf T}$ is the contragredient of the second tensor leg.

For a pair preserving $U$, let $C$ be its induced action on $S$ under the dual action. Then $B_*\Phi(v,z)=\Phi(Av,Cz)$. Conversely, if this identity holds, evaluating it on arbitrary $v,z$ shows that the dual pair indeed sends each $z$ to $Cz$. Thus the pair stabilizer $H$ consists exactly of the choices
$$
A\in\mathrm{GL}(V),\quad C\in\mathrm{GL}(S),\qquad
B_*=\begin{pmatrix}A\otimes C & X\\ 0&E\end{pmatrix}
$$
in $W^*=L\oplus L_0$, where $L$ is identified with $V\otimes S$, $E\in\mathrm{GL}(L_0)$, and $X:L_0\to L$ is arbitrary. This is the split semidirect product of the additive group $\operatorname{Hom}(L_0,L)$ by $\mathrm{GL}(V)\times\mathrm{GL}(S)\times\mathrm{GL}(L_0)$. The action on a shear is $X\mapsto (A\otimes C)XE^{-1}$.

Next split $Z^*=U\oplus K$ so that $F$ is projection onto $U$ followed by inclusion. If $h\in H$ acts on $U$ as $h_U$, the dual third-leg map $D$ must satisfy $FD=h_U F$. Its full choices are
$$
D=\begin{pmatrix}h_U&0\\ Y&E_K\end{pmatrix},\qquad
Y\in\operatorname{Hom}(U,K),\quad E_K\in\mathrm{GL}(K).
$$
Thus the full stabilizer is $\operatorname{Hom}(U,K)\rtimes(H\times\mathrm{GL}(K))$, with action $Y\mapsto E_KYh_U^{-1}$. In particular its order is
$$
q^{(N-k_0)(s+k_0)+ak_0(b-ak_0)}
|\mathrm{GL}_a(q)|\,|\mathrm{GL}_{k_0}(q)|\,
|\mathrm{GL}_{b-ak_0}(q)|\,|\mathrm{GL}_{s+k_0}(q)|.
$$
All zero-dimensional conventions use the trivial group. No scalar subgroup has been divided out.

For two accepted tensors with the same defect, choose arbitrary isomorphisms on their $V$ and $S$, use $\Phi$ to extend their tensor product to the two $W^*$, and then lift the induced map on the images to the third leg by splittings and a kernel isomorphism. This constructs a transporter. Defect and injectivity are invariant under transport, so a source passing the test can be compared in polynomial time against every target, including a target failing it.

### The limiting law

For $d\ge0$, put $P_d=\prod_{j=1}^d(1-q^{-j})$ and $P_\infty=\prod_{j\ge1}(1-q^{-j})$. Counting rank-$(N-k_0)$ rectangular matrices by first choosing an image and then a surjection gives
$$
\Pr(k_0=j)=q^{-j(j+s)}
\frac{P_NP_{N+s}}{P_jP_{j+s}P_{N-j}},
\qquad \max(0,-s)\le j\le N.
$$
These populations are bounded by a constant times $q^{-j(j+s)}$, since every finite product $P_i$ lies between $P_\infty>0$ and one. Their limit is $P_\infty q^{-j(j+s)}/(P_jP_{j+s})$ at each fixed $j$. The summable bound makes this a limiting probability distribution.

Conditional on defect $j$, $S$ is a uniform $j$-subspace. Sample it as the span of $j$ independent uniform vectors of $V^*\otimes W^*$, conditioned on their linear independence. Before conditioning, the matrix for $\Phi$ is a uniform $b\times aj$ array. Full column rank of this array implies independence of the $j$ tensors. The conditional acceptance probability for $aj\le b$ is therefore
$$
\frac{\prod_{i=0}^{aj-1}(1-q^{i-b})}
     {\prod_{i=0}^{j-1}(1-q^{i-N})}.
$$
For each fixed $j$ this tends to one when $b/a\to\infty$. The summable tail bound for $j$ proves that the entire probability of rejection is $o(1)$. The displayed probability law and the stabilizer description consequently cover all but an $o(1)$ fraction of the random tensors in this regime.
