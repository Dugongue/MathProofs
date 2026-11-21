# NP-hard orbit-distance approximation with simple marginal spectra

## GP-0303

The promised-gap Frobenius distance between two tensor orbits under the product of three full orthogonal groups is NP-hard. The same result holds for product unitary groups. This holds for integer tensors with polynomially bounded entries, connected coordinate support and simple marginal spectra. Rescaling both tensors to Frobenius norm at most one gives inverse-polynomial gaps in the squared distance promise and in each covariance spectrum.

### Data and anchors

Let $X$ be a simple graph with $n$ vertices and $m\ge1$ edges. Use a common index set of size $k=3(n+1)$ partitioned into disjoint lists $(a_i),(b_i),(c_i)$, each indexed by $0,\dots,n$. In the cubic tensor format define
$$
D=\sum_{j=1}^k j e_j\otimes e_j\otimes e_j .
$$
Take tensors $T=LD+P$ and $S=LD+Q$. The data $P,Q$ have the following support, in which every coordinate triple has three distinct indices:

- At $(a_0,b_0,c_0)$ and, for each $i\ge1$, at $(a_i,b_0,c_i),(a_0,b_i,c_i),(a_i,b_i,c_0)$, put the same positive integer $M$ in both $P,Q$.
- At $(a_i,b_j,c_0)$ for each edge $ij$ with $i<j$, put $1$ in $P$ and $-1$ in $Q$.

Choose $M=1000(n+m+1)^2$, $B=(3n+m+2)(M+1)$ and $L=10^6k^6B^3$. Then $\|P\|_F,\|Q\|_F\le B$ and $\|D\|_F\le k^2$. These parameters are integers of polynomial magnitude. The support hypergraph is connected for both tensors. Each diagonal anchor connects the three appearances of one global index. The baseline links the three zero-index positions, and the two tuples containing $c_i$ connect $a_i,b_i,c_i$ to that baseline.

For any graph sign assignment $(s_i)$, use diagonal orthogonal actions with signs $1$ at $a_0,b_0,c_0$ on their respective axes and $s_i$ at $a_i,b_i,c_i$ on those axes. At each global index at most one axis was specified, so complete the signs to have product $1$ across the three axes at every index. This fixes $D$, satisfies all weight-$M$ entries, and costs $4$ in squared distance on each uncut edge. Thus for either acting group, the optimal distance $\Delta$ satisfies
$$
\Delta\le 2\sqrt{m-\operatorname{MaxCut}(X)} .
$$

### Finding the almost diagonal transporters

Let $U_1,U_2,U_3$ be optimal orthogonal or unitary transporters, existing by compactness. Put $U=U_1\otimes U_2\otimes U_3$. In each mode $i$, let $\Gamma_i$ be the Gram matrix of its flattened tensor. The cross terms between $D$ and either data tensor vanish in each $\Gamma_i$, since the two contracted indices of a nonzero $D$ entry are equal and those of every data entry are distinct. Hence with $\Lambda=\operatorname{diag}(j^2)_{j=1}^k$,
$$
\Gamma_i(T)=L^2\Lambda+\Gamma_i(P),\qquad
\Gamma_i(S)=L^2\Lambda+\Gamma_i(Q).
$$
Covariance gives $\Gamma_i(UT)=U_i\Gamma_i(T)U_i^*$. The Gram difference is at most $(\|T\|_F+\|S\|_F)\Delta$ in Frobenius norm, by expanding the difference between $AA^*$ and $BB^*$ for the two flattenings. The Gram matrices of $P,Q$ have Frobenius norms at most $B^2$. Therefore, since $\Delta\le2B$ and $L\ge B$,
$$
\|U_i\Lambda-\Lambda U_i\|_F
 \le (4LB\|D\|_F+6B^2)/L^2
 \le 10k^2 B/L .
$$
Every distinct pair of diagonal entries of $\Lambda$ differs by at least $1$, so this bounds the Frobenius mass of the off-diagonal part of $U_i$. Let $H_i$ be the diagonal matrix of unit phases of the diagonal entries of $U_i$, taking arbitrary phase $1$ at zero, and signs in the real case. For a row of a unitary matrix, $(1-|u_{jj}|)^2\le1-|u_{jj}|^2$, its off-diagonal squared norm. Hence
$$
\|U_i-H_i\|_F\le 20k^2 B/L=:\eta .
$$

Let $\Pi$ be coordinate projection onto triples with pairwise distinct indices, and write $H=H_1\otimes H_2\otimes H_3$. Expanding $UD$ by writing each $U_i=H_i+(U_i-H_i)$, all terms with zero or one difference vanish under $\Pi$: at least two coordinates have stayed equal. Thus $\|\Pi UD\|_F\le4\eta^2\|D\|_F$ using $\eta\le1$ and the three terms with two differences and one with three. A telescoping of the tensor product of the three isometries gives $\|(U-H)P\|_F\le3\eta B$. Since $\Pi D=0$ and $HP,Q$ are already on the projected support,
$$
 e:=\|HP-Q\|_F\le \Delta+\xi,\qquad
 \xi=3\eta B+4L\eta^2k^2<1/(100B).
$$

### Rounding unit phases to a cut

Write $u_i,v_i,w_i$ for the diagonal phases on $a_i,b_i,c_i$ in the first, second and third axes, respectively. Set $c=u_0v_0w_0$, $x_i=u_i/u_0$, $y_i=v_i/v_0$, $z_i=w_i/w_0$. Each weight-$M$ entry differs from its target by at most $e$. Consequently $|c-1|\le h=e/M$ and
$$
 |x_i z_i-1|,\ |y_i z_i-1|,\ |x_i y_i-1|\le 2h .
$$
This implies $|x_i-y_i|\le4h$, and then $|x_i^2-1|\le6h$. Since at least one of $|x_i-1|,|x_i+1|$ is at least $1$, there is a sign $s_i$ with $|x_i-s_i|\le6h$, and $|y_i-s_i|\le10h$. On each edge the corresponding phase $c x_i y_j$ differs from $s_i s_j$ by at most $17h$. Restricting the distance to the edge coordinates and rounding therefore gives
$$
2\sqrt{m-\operatorname{MaxCut}(X)}
 \le e+17h\sqrt m
 \le \Delta+\xi+17h\sqrt m .
$$
Here $e\le2\sqrt m+1$, so the chosen $M,B$ give $\xi+17h\sqrt m\le1/[8(\sqrt m+1)]$. Squaring both bounds on the distance proves
$$
 4(m-\operatorname{MaxCut}(X))-1< \Delta^2
 \le 4(m-\operatorname{MaxCut}(X)).
$$
Thus a threshold promise with yes side $\Delta^2\le4(m-K)$ and no side $\Delta^2>4(m-K)+3$ distinguishes whether the input graph has a cut of size at least $K$. [Garey–Johnson–Stockmeyer, Simple Max Cut](https://doi.org/10.1016/0304-3975(76)90059-1) The same proof includes the real case by viewing real signs as unit phases.

Weyl's eigenvalue estimate gives marginal eigenvalue gaps at least $L^2-2B^2$, using consecutive diagonal differences at least $1$ and perturbation operator norms at most $B^2$. In particular every marginal eigenspace has multiplicity one. Dividing both tensors by $Lk^2+B$ gives norm at most one, inverse-polynomial marginal gaps, and an inverse-polynomial squared-distance promise gap. This yields the numerical hardness despite the exact orbit recovery methods for simple marginal spectra. [Numerical orbit context](https://arxiv.org/html/2603.27128v1) · [Prior exact transport under small spectral blocks](https://github.com/Dugongue/MathProofs/tree/d7366c4348bc03f0e93cb8674db191de32ba58bf/OrthogonalMultiplicityTwo)
