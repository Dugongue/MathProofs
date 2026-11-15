# Algebraic and spectral unbiasedness for any number of measurements

Informal proof. Designolle and Farkas introduced algebraic and spectral \(k\)-fold unbiased measurements and left their relation open beyond the cases in their Theorem 3. They also left the maximal-eigenspace parent criterion unresolved outside their conditional-moment regimes. We prove the equivalence in every finite dimension and show that the parent reaches the selected-sum bound for every such tuple. The existence of genuinely higher-order nonbinary tuples is a separate question. The universal asymptotic hierarchy value in their Conjecture 10 concerns all measurement tuples. [Designolle–Farkas, Sections III–VI and Appendix E](https://arxiv.org/html/2609.20728v1)

## 1. Setup and the scalar polynomials

Take \(k\ge2\) projective measurements, each with \(n\ge2\) outcomes of common rank \(r>0\), on a complex space of dimension \(nr\). The algebraic definition for general POVMs forces these properties by Designolle–Farkas, Theorem 3(1). For any fixed selection of outcomes, let \(P_i=V_iV_i^*\), where \(V_i\) is an isometry from \(\mathbb C^r\) onto the selected range of setting \(i\). For a subset \(S\) of settings and commuting variables \(y_i\), write
\[
 X_S(y)=\sum_{i\in S} y_iP_i,\qquad
 B_S(y)=(y_jV_i^*V_j)_{i,j\in S}.
\]
These are products in reverse orders of the same two rectangular matrices. Their nonzero spectra, with algebraic multiplicities, coincide. Equivalently, \(\det(I-X_S/t)=\det(I-B_S/t)\) by Sylvester's determinant identity. This includes the case \(|S|>n\), in which \(B_S\) has excess zeros.

Define the monic polynomial
\[
 p_S(t,y)=\sum_{J\subseteq S}(-1)^{|J|}
       \frac{(n)_{|J|}}{n^{|J|}}\ y_J t^{|S|-|J|},
 \qquad y_J=\prod_{j\in J}y_j,
\]
where \((n)_m=n(n-1)\cdots(n-m+1)\), with \((n)_0=1\) and \((n)_m=0\) for \(m>n\). If \(y_i=1\) for all \(i\), this is \(p_s(t)=t^{s-n}\mu_{s,n}(t)\) for \(s=|S|\). The expression is polynomial even for \(s<n\), by the zero factor in \(\mu_{s,n}\).

For \(i\in S\), this family satisfies
\[
 p_S=(t-y_i)p_{S\setminus\{i\}}
 -\sum_{\substack{J\subseteq S,\ i\in J\\ |J|\ge2}}
  y_J\frac{(|J|-1)!}{n^{|J|-1}}\ p_{S\setminus J}. \tag{1}
\]
For a proof, expand by a subset of used labels, permute those labels and assign a weight \(-n^{1-\ell}\) to each cycle of length \(\ell\). All unused labels contribute \(t\). The contribution from the cycle containing \(i\) gives (1), including the fixed point of weight \(-1\). On a particular subset of \(\ell\) used labels the total cycle weight is \(n^{-\ell}\sum_{\pi\in\mathfrak S_\ell}(-n)^{\#\operatorname{cycles}(\pi)}=(-1)^\ell(n)_\ell/n^\ell\). The cycle-insertion recurrence for the sum multiplies by \(-n+\ell-1\) upon adjoining the \(\ell\)-th label. This recovers exactly the displayed polynomial.

For \(i\in J\), \(|J|\ge2\), let
\[
 Z_{i,J}=\sum_{(j_2,\ldots,j_{|J|})}
 V_i^*V_{j_2}V_{j_2}^*V_{j_3}\cdots V_{j_{|J|}}^*V_i.
\]
The sum runs over all orders of \(J\setminus\{i\}\). This is the sum of products on oriented simple cycles through all of \(J\) based at \(i\), using unweighted overlap blocks. It is Hermitian because path reversal takes each term to its adjoint. The algebraic relation on \(J\) is
\[
 D_{i,J}=0,\qquad
 D_{i,J}=Z_{i,J}-\frac{(|J|-1)!}{n^{|J|-1}}I_r. \tag{2}
\]
This is exactly Definition 1 after compressing to the selected range of \(P_i\). For independent uniform outcomes, even conditional on the outcome at \(i\), \(\mathbb E D_{i,J}=0\). Each of the other selected projectors appears once in each term and averages to \(I/n\). If the original tuple is algebraic \(k\)-UM, its subtuples obey (2) by the authors' heredity proof, which also follows by summing over one omitted outcome at a time.

## 2. A Schur complement with one unknown cycle term

Suppose every proper subset of \(S\) obeys (2) for its given selected outcomes. We prove
\[
 \det(tI-B_S(y))=\det\bigl(p_S(t,y)I_r-y_S D_{i,S}\bigr)
 \quad\text{for any } i\in S,\quad |S|\ge2. \tag{3}
\]
At the same time we prove, when \(S\) itself obeys (2), that
\[
 [(tI-B_S(y))^{-1}]_{ii}=\frac{p_{S\setminus\{i\}}(t,y)}{p_S(t,y)}I_r. \tag{4}
\]
For one setting both the determinant and diagonal inverse are immediate. Proceed by induction on \(|S|\), and work with rational functions in \(t,y\), where the inverses exist since the pencils are monic.

For \(u\ne v\) in a subset \(R\), block inversion gives
\[
 [(tI-B_R)^{-1}]_{uv}
  =[(tI-B_R)^{-1}]_{uu}
       \sum_{w\in R\setminus\{u\}} B_{uw}
                [(tI-B_{R\setminus\{u\}})^{-1}]_{wv}.
\]
Recursively apply this identity, stopping when the current initial vertex equals \(v\). This enumerates simple paths, deleting each visited vertex. It is the block Schur-complement form of the standard matrix path-sum expansion. [Giscard–Thwaite–Jaksch](https://arxiv.org/abs/1112.1588)

Use the root \(i\) Schur complement in \(tI-B_S\), expanding the inverse on \(S\setminus\{i\}\) in this way. Each term is a simple closed path from \(i\) to \(i\) with nonempty intermediate list \(j_2,\ldots,j_s\), supporting \(J=\{i,j_2,\ldots,j_s\}\). The scalar diagonal-resolvent factors from (4) on proper subsets telescope to \(p_{S\setminus J}/p_{S\setminus\{i\}}\). Each destination label appears exactly once on the closed path, so the product of its block weights is \(y_J\) times its unweighted overlap product. The block Schur complement is consequently
\[
 (t-y_i)I_r-\sum_{\substack{J\subseteq S,\ i\in J\\ |J|\ge 2}}
  \frac{p_{S\setminus J}}{p_{S\setminus\{i\}}}\ y_J Z_{i,J}
 = \frac{p_S I_r-y_S D_{i,S}}{p_{S\setminus\{i\}}}.
\]
Here all proper cycles give their scalars and (1) sums the scalar terms. The complementary principal block has determinant \(p_{S\setminus\{i\}}^r\) by induction. Taking the determinant proves (3), and when the top cycle relation holds, inverting the Schur complement proves (4). This argument uses ordered block multiplication throughout and allows any common rank.

In particular an algebraic \(k\)-UM has characteristic polynomial \(p_S^r\) on the weighted selected Gram matrix of every subtuple. The determinant identity between \(B_S\) and \(X_S\) gives the desired unweighted spectral condition.

## 3. Recover the cycle identities from spectral information

Now suppose only that the full \(k\)-tuple is spectral. We prove (2) for each subtuple by induction on its size \(\ell\). One setting needs no condition. For subset \(S\), set
\[
 F_m(S,y)=\mathbb E\,\frac{1}{r}\operatorname{Tr}(X_S(y)^m),\qquad
 Q_m(S,y)=-m[t^{-m}]\log\bigl(p_S(t,y)/t^{|S|}\bigr),\quad
 E_m=F_m-Q_m.
\]
All coefficient operations are formal at \(t=\infty\), and \(F_m,Q_m\) are homogeneous of degree \(m\) in \(y\). This log series has the usual trace interpretation for a determinant:
\(\log\det(I-X/t)=-\sum_{m\ge1}\operatorname{Tr}(X^m)t^{-m}/m\).
Setting some \(y_i=0\) restricts both sides to the smaller subset. The spectral hypothesis on the full tuple gives \(E_m([k],\mathbf1)=0\) for each positive \(m\).

Assume all subsets of size below \(\ell\) are algebraic. For \(J\) of size \(\ell\), fix any root \(i\). Using (3) and expanding at infinity gives
\[
 \frac{1}{r}\log\frac{\det(tI-B_J(y))}{t^{r\ell}}
 -\log\frac{p_J(t,y)}{t^\ell}
 =-\sum_{h\ge1}\frac{y_J^h\,\operatorname{Tr}(D_{i,J}^h)}{rh\,p_J(t,y)^h}.
\]
In the averaged series the \(h=1\) term vanishes by the mean-zero identity for \(D_{i,J}\). As \(p_J\) is monic of degree \(\ell\), this yields
\[
 E_m(J,y)=0 \quad(m<2\ell),\qquad
 E_{2\ell}(J,y)=\frac{\ell}{r}y_J^2\ \mathbb E\operatorname{Tr}(D_{i,J}^2). \tag{5}
\]
The coefficient of \(y_J^2\) is nonnegative because \(D_{i,J}\) is Hermitian.

We need to control coefficients with larger support without assuming any extra subtuple identities. A coefficient with exponent exactly one at \(y_i\) is obtained by differentiating in \(y_i\) and evaluating at zero. For \(m\ge2\) the cyclic trace rule and completeness give
\[
 \left.\partial_{y_i} F_m(S,y)\right|_{y_i=0}
  =\frac{m}{n} F_{m-1}(S\setminus\{i\},y).
\]
The same rule holds for \(Q_m\). Put \(Z=p_{S\setminus\{i\}}/t^{|S|-1}\). The exact coefficients defining \(p_S\), with \((n)_{j+1}=(n-j)(n)_j\), give
\[
 \left.\partial_{y_i}(p_S/t^{|S|})\right|_{y_i=0}
       =-\frac{Z}{t}-\frac{1}{n}\partial_t Z.
\]
Taking the logarithmic derivative in \(y_i\) gives \(-1/t-(1/n)\partial_t\log Z\), which proves the claim coefficientwise at orders \(m\ge2\). At order \(m=1\) both derivatives are one, since \(\operatorname{Tr}P_i=r\).

Thus for \(m\le2\ell\) a monomial of support size greater than \(\ell\) has at least one exponent equal to one, so its coefficient in \(E_m\) reduces to a coefficient in \(E_{m-1}\). Inducting on \(m\), all differences vanish below order \(2\ell\), since on support at most \(\ell-1\) the algebraic-to-weighted-spectral implication applies and on support exactly \(\ell\) we have (5). At order \(2\ell\) the same deletion shows all larger-support differences are zero. The only remaining contributions therefore come from (5), and the full spectral assumption gives
\[
 0=E_{2\ell}([k],\mathbf1)=\frac{\ell}{r}
           \sum_{\substack{J\subseteq[k]\\ |J|=\ell}}\mathbb E\operatorname{Tr}(D_{i(J),J}^2).
\]
Choose the root \(i(J)\) for each subset freely. Every term is nonnegative. For any chosen \(J\) and \(i\in J\) this forces \(\operatorname{Tr}(D_{i,J}^2)=0\) for every outcome selection, since each has positive probability. A Hermitian matrix with this property is zero. This proves the induction at \(\ell\) and the unrestricted algebraic–spectral equivalence. It also proves heredity of the spectral condition.

## 4. The maximal-eigenspace parent at arbitrary order

Take an algebraic, and hence spectral, \(k\)-UM and specialize \(y_i=1\). Let \(V\) denote the row of all \(V_i\) for the chosen outcomes. Put \(X=VV^*\), \(B=V^*V\), and let \(\lambda=\lambda_{k,n}>0\) be the largest root of \(\mu_{k,n}\). It is simple in \(\mu_{k,n}\), and hence in \(p_k\), by the root argument of Designolle–Farkas, Appendix D. The projection \(\Pi\) onto the \(\lambda\)-eigenspace of \(X\) has rank \(r\).

For any real \(t>k\) the identity
\[
 (tI-X)^{-1}=\frac1t I+\frac1t V(tI-B)^{-1}V^*
\]
follows by multiplication. Using (4) and the off-diagonal path recursion of Section 2 on the full set, each term in \(V(tI-B)^{-1}V^*\) is a scalar coefficient, depending only on \(t\) and the path length, times a product \(P_{i_1}\cdots P_{i_s}\) of distinct selected projectors. Indeed a path with \(s\) distinct vertices has successive factors \(p_{k-1}/p_k,\ldots,p_{k-s}/p_{k-s+1}\), telescoping to \(p_{k-s}/p_k\). This holds for the one-vertex paths as well. Multiplying the overlap blocks by \(V_{i_1}\) and \(V_{i_s}^*\) gives the asserted projector product exactly. Conditional on one fixed choice \(P_i=P\), averaging each term gives a scalar times \(I\) if the path omits \(i\), or a scalar times \(P\) if it includes \(i\). Hence the conditional resolvent, and by its rational identity the conditional residue at \(t=\lambda\), belong to the span of \(I,P\). The residue is exactly the conditional average of \(\Pi\), since the resolvent of a Hermitian matrix has its eigenprojections as residues.

The diagonal block \(i\) of \((tI-B)^{-1}\) is \(p_{k-1}(t)/p_k(t)\) times \(I_r\). The generating series \(\sum_{s\ge0}p_s(t)z^s/s!=e^{tz}(1-z/n)^n\) gives \(p_k'(t)=k p_{k-1}(t)\). The diagonal residue at \(\lambda\) is thus \(I_r/k\). If \(E_\lambda\) is the projection for \(B\), then \(\Pi=\lambda^{-1} V E_\lambda V^*\), so \(V_i^*\Pi V_i=\lambda (E_\lambda)_{ii}=(\lambda/k)I_r\). The conditional average has trace \(r\). Combining its compression on \(P\), its trace and its membership in the span of \(I,P\) gives
\[
 \mathbb E[\Pi\mid P_i=P]
    =\frac{\lambda}{k}P+
      \frac{1-\lambda/k}{n-1}(I-P). \tag{6}
\]
This is precisely the conditional projector criterion from Designolle–Farkas, Theorem 8.

For clarity, define the parent entries \(G_{\vec a}=n^{1-k}\Pi_{\vec a}\). For each setting and outcome the marginal is (6), so summing those marginals gives \(I\). They dominate \((\lambda/k)P_i\), since \(\lambda\le k\) by \(X\preceq kI\) for an actual tuple. This gives generalized visibility at least \(\lambda/k\). For any parent at visibility \(\eta\), the sum of marginal traces against the selected projectors is at least \(k\eta\,nr\), but is also \(\sum_{\vec a}\operatorname{Tr}(X_{\vec a}G_{\vec a})\le \lambda\,nr\). Therefore equality is optimal. The exact generalized incompatibility robustness of every algebraic or spectral \(k\)-UM is \(\lambda_{k,n}/k\), with this explicit parent.

This result establishes fixed-tuple optimality for every algebraic or spectral tuple. Conjecture 10 adds a lower bound over arbitrary measurement tuples. No claim of independent publication priority or Lean verification is made.


## 5. Moment-only characterization and other noise models

The converse used the full spectral data only through the \(k-1\) equalities \(F_{2\ell}([k],\mathbf 1)=Q_{2\ell}([k],\mathbf1)\) for \(2\le\ell\le k\). Those averaged even moments alone therefore characterize the algebraic and spectral tuples under the projectivity and equal-rank hypotheses. If the identities first fail at a subtuple of size \(\ell\), all smaller averaged even moments take their target values, and (5) shows that the averaged \(2\ell\)-th moment strictly exceeds its target.

The marginal in (6) is also exactly \(\nu P+(1-\nu)I/n\) at
\[
 \nu=\frac{\lambda/k-1/n}{1-1/n}.
\]
For equal outcome ranks this is both the uniform-noise and the depolarizing-noise marginal. Its optimality for those two noise models follows from the same trace upper bound, since any such parent would have summed projected trace \(k\,nr\,[\nu+(1-\nu)/n]\). Thus the same parent establishes their exact common visibility. This extends the consequence of Designolle–Farkas, equation (17), to all algebraic or spectral tuples.
