# A sharp catalyst dimension–order tradeoff for sparse Peirce tensors

Let the order of a Laurent degeneration be the least sum of its three forward entry pole caps. For concise tensors this equals the least leading order of a polynomial-matrix presentation: clear the mode poles and truncate each resulting integral matrix above the leading order, or move the leading scalar power into one Laurent matrix. An algebra catalyst is the multiplication tensor of a nonzero finite-dimensional associative unital algebra over the same field. The three tensor modes are regrouped in each tensor product.

**Theorem.** There are explicit sparse \(0/1\) Peirce multiplication tensors \(U_m,V_m\) of format \(N_m\times N_m\times N_m\), with \(N_m=\Theta(m)\), over every field. For any integer \(s\ge1\), let \(P_m(s)\) be the least order after adjoining any algebra catalyst of dimension at most \(N_m^{s-1}\). There is an absolute \(C_0\) such that
\[
 \frac{s}{6}\bigl(2^{m/s}-1\bigr)
 \ \le\ P_m(s)\ \le\
 C_0s\bigl(2^{m/s}-1\bigr).
 \tag{1}
\]
The upper bound has an explicit monomial presentation after a constant factor permutation. It uses a catalyst of dimension \(N_m^{\min(s,m)-1}\). The lower bound allows arbitrary changes of basis across the regrouped modes and arbitrary associative algebra catalysts.

In particular the unamplified order is \(\Theta(2^m)\), and the unrestricted optimal catalytic order is \(\Theta(m)\). A polynomial-dimensional catalyst still incurs order \(2^{\Omega(m)}\). Catalysts of dimension \(2^{O(m)}\) attain polynomial order, and dimension \(2^{\Omega(m)}\) is necessary for any fixed polynomial bound. Linear order is attained with catalyst dimension \(2^{O(m\log m)}\), and dimension \(2^{\Omega(m\log m)}\) is necessary for linear order.

A separate universal bound in Section 5 shows that a catalytic order of \(P\) can be replaced by unamplified order at most \(2^P-1\) in the general common-type Peirce class, including heterogeneous products. Thus the exponential dependence on catalytic order is sharp up to a constant in the exponent for the family above. [Exact profile costs for thin Peirce types](OptimalCatalystSeed.md)

## 1. A sparse family with triangularly related contacts

Use oriented three-edge circles \(C_1,\ldots,C_m\), each with a separate vertex set. For \(j<m\), attach one fixed-size Möbius-and-annulus block with core \(C_{j+1}\) and outer three-edge circle \(D_j\). Orient \(D_j\) so that its homology class in the block is \(2[C_{j+1}]\). The standard block is the triangulated strip \([0,3]\times[-1,1]\) with the ends identified by reversal, together with the annulus between its six-edge boundary and a three-edge circle. It retracts to the core and gives the stated doubling. [Triangulated doubling block](SparseSeed.md) [Filakovský, Franek, Wagner and Zhechev, Lemma 7](https://doi.org/10.1007/s41468-018-0021-5)

Attach a fixed triangulated pair of pants along two of its boundary circles to \(C_j,D_j\). All three boundaries are three-edge circles. For instance, in each of three distinct triangular faces of a tetrahedral boundary place a new internal triangle, triangulate the intervening annulus, then remove the internal open triangles. Cap the third boundary with a cone on its three-edge circle. Separately cap \(C_m\) by another cone. All pieces have fixed size. Their seam circles are disjoint within each piece and have no filled seam triangle, so identifying the designated circles simplicially gives a finite simplicial complex with \(\Theta(m)\) simplices.

Barycentrically subdivide, and mark one small triangular flag \(\sigma_j\) in each cap, using the flag (cone apex, spoke, incident cone triangle). Its closure is interior to the cap. Use the rank order on each flag to orient it. Removing the open marked flag in a cap replaces that cone disk by an annulus. Choose the signs of the gluing maps on the two pair-of-pants seams and the orientation of the marked flag relative to that surface so that, in the punctured piece,
\[
 [\partial\sigma_j]=-[C_j]+[D_j]\quad(j<m),
 \qquad
 [\partial\sigma_m]=-[C_m].
 \tag{2}
\]
To see these choices explicitly, an oriented pair of pants has zero sum of the three boundary classes, and each gluing of a triangular boundary circle can preserve or reverse its orientation independently. The two spoke flags in a cone face have opposite signs relative to the disk orientation because their increasing-rank boundaries induce the same direction on the common apex-to-face edge. The terminal punctured cap is an annulus and gives the last displayed relation with the corresponding sign.

Order the vertices of the subdivided complex by original simplex dimension and then by fixed labels. The strict corners consist of all strict face inclusions and the missing successor corners of this total order. The latter have zero strict products. Every included triangular flag \((x,y,z)\) has product \(p_{xy}p_{yz}=p_{xz}\). The diagonal idempotents act at endpoints. Retain every unmarked flag and let any subset of the marked flags remain. These are admissible tables of one type in the profile theorem. In fact every flag product is from rank zero to rank two, so every triple product of strict corners vanishes. A removed flag always leaves the alternate flag through the other incident edge in the same original triangle, with the same output corner. Our marks are in different caps, so no such alternate is removed. Thus the based square of the radical is the same in all profiles. Its degree-two corners together with the degree-one remaining strict corners give the common radical grading. The added successors make the reachability order a chain. There are \(\Theta(m)\) supported corners including the diagonals, and the multiplication tensor has \(\Theta(m)\) nonzero entries. Let \(U_m\) retain all marks and \(V_m\) delete them all.

For an integer cochain \(w\) on the supported corners with zero defects at the unmarked flags, let \(c_j\) be its defect at \(\sigma_j\), computed as \(w(x,z)-w(x,y)-w(y,z)\) whether or not that product is present in the given table. Let \(z_j=w(C_j)\) be the signed circulation on the subdivided \(C_j\). Defect is the negative evaluation on the oriented triangle boundary. Thus (2) and the doubling block give
\[
 c_j=z_j-2z_{j+1}\quad (j<m),\qquad c_m=z_m. \tag{3}
\]
This uses only cocycle identities on the unmarked faces, so it applies to every profile-path step between \(U_m\) and \(V_m\).

## 2. Local sections with uniformly bounded weights

Conversely any integer vector \((z_1,\ldots,z_m)\) is realized by a cochain with the defects in (3) and with
\[
 \max_{x\to y}|w(x,y)|\le L\max_j |z_j| \tag{4}
\]
for some absolute \(L\). To construct it, prescribe a reference integral boundary cochain of period one on each oriented subdivided seam circle. On a doubling block, its input is a generator of its free integral first homology. A fixed integral cocycle of input period one has output period two. On each punctured pair-of-pants piece, the two seam classes freely generate the integral first homology, so choose fixed integer cocycles with seam periods \((1,0)\), \((0,1)\). The terminal punctured cap similarly has a unit-period cocycle. These exist integrally by evaluating the given homology character on edges closed through a spanning tree. Normalize each fixed cocycle on every seam to its prescribed period times the reference boundary cochain. Cochains on a circle with the same period differ by an integral vertex coboundary. The seams in each piece are disjoint, so these boundary corrections extend simultaneously to an integer vertex gauge on the piece. Now scale the doubling block by \(z_{j+1}\), combine the two fixed cocycles in the adjacent punctured piece with multipliers \(z_j,2z_{j+1}\), and scale the terminal cap by \(z_m\). These cochains agree on all seams. Each fixed piece uses one or two bounded cochains, with coefficients bounded by \(2\max_j|z_j|\). Added successor corners get weight zero. This proves (4).

Use the three-layer cycle mean \(\rho\) of the profile theorem. It satisfies
\[
 \frac{\max_j|z_j|}{3}\le \rho(w),\qquad
 \rho(w)\le 3L\max_j|z_j|\ \text{for the section in (4)}. \tag{5}
\]
For the lower bound traverse a subdivided \(C_j\) in the direction of positive circulation. Its six steps alternate forward and backward, because the original vertices have rank zero and the edge barycenters have rank one. A forward \(B\)-to-\(A\) step, an identity \(A\)-to-\(C\) step and a backward \(C\)-to-\(B\) step realize each pair in the layered graph. This yields reward \(|z_j|\) in three triples of steps. The upper bound is immediate from (4), since each triple of steps has at most three times the largest absolute weight as reward.

## 3. Every catalyst of the given dimension pays the lower bound

We use the active-grid extraction in Sections 2–3 of the exact profile-cost proof. Given a catalyst \(B\) and a witness of total cap \(P\), first pass to \(\overline k[[t]]\) with the same caps and remove the component-internal radical of the catalyst. Write \(E\) for the resulting catalyst over \(\overline k\), so \(\dim_{\overline k}E\le\dim_kB\). The normalized transporter permutes the active chain axis positions, all of the original thin type, in each connected component and maps the inactive spectator tuple \(q\) to its image \(p(q)\). On every active grid the corner support is the Cartesian product of its active supports, and the nonzero corners have dimension \(b^2\) for that grid's common matrix size \(b\). The integer cochains \(w_{q,i}\) extracted on the \(i\)-th active fiber obey
\[
 \sum_i\rho(w_{q,i})\le P. \tag{6}
\]
The inequality follows from the three unchanged caps and additivity of the layered cycle mean on the grid. The cochain for state \((q,i)\) is feasible for the comparison to the target profile at its successor \((p(q),P_{\mathrm{axis}}(i))\), where \(P_{\mathrm{axis}}\) denotes the transporter permutation of axis positions. At every nonexterior axis position the source and target profiles at the same state coincide. [Active-grid cochain and profile-path extraction](OptimalCatalystSeed.md)

Choose one orbit of \(p\), with \(h\) spectator tuples. Each grid along the orbit has the same number \(u\) of active axes, since the transporter matches them bijectively. A grid supports exactly \(N_m^u\) ordered corner pairs, because \(N_m\) counts all supported pairs of the base type, including the diagonals. Their corner spaces are distinct summands of the full Peirce decomposition of the endpoint algebra. Each has dimension at least one. Therefore
\[
 N_m^u\le \dim_{\overline k}\bigl(A(U_m)_{\overline k}\otimes E\bigr)
 \le N_m\dim_k B,
 \qquad
 u\le 1+\left\lfloor\log_{N_m}\dim_kB\right\rfloor. \tag{7}
\]
Here \(A(U_m)\) denotes the algebra whose multiplication tensor is \(U_m\).

The state permutation on the \(hu\) positions cuts into profile paths when cut at exterior occurrences. There is exactly one exterior position per grid, so there are \(h\) paths. Every state cycle meets an exterior position by the definition of active. Thus each path starts at \(U_m\), ends at \(V_m\), and consists of monotone profile moves. All unmarked products persist throughout a path. At each step let \(a\) be the greatest index already removed before it, with \(a=0\) if none, and let \(d\) be the greatest index removed after it. Call \(\ell=d-a\) the advance. Every \(\ell\) is nonnegative and the advances on each path sum to \(m\).

For a step with \(\ell>0\), the marked products with indices greater than \(d\) remain present with defect zero. Equation (3) then gives \(z_i=0\) for \(i>d\). The \(d\)-th marked product is removed at this step, so \(z_d=c_d\ge1\). All marked products with \(a<i<d\) were present before the step, so their defects are nonnegative, irrespective of which are removed. Repeatedly applying \(z_i=c_i+2z_{i+1}\) gives \(z_{a+1}\ge 2^{\ell-1}\). From (5) the step cost of its extracted cochain is at least \(2^{\ell-1}/3\), hence at least \((2^\ell-1)/6\). This last bound also holds for a zero advance since \(\rho\ge0\).

Apply convexity of \(x\mapsto 2^x-1\) to all \(hu\) steps, whose total advance is \(hm\), and sum (6). It follows that
\[
 hP\ \ge\ \frac{hu}{6}\bigl(2^{m/u}-1\bigr).
\]
The function \(x\mapsto x(2^{m/x}-1)\) decreases for \(x>0\), as it equals \(\int_0^{m\log 2}\exp(t/x)\,dt\). Under the dimension bound \(\dim B\le N_m^{s-1}\), (7) gives \(u\le s\). Dividing by \(h\) proves the claimed lower bound. This uses the total length across all profile segments in a spectator orbit, so it also covers transporters that permute multiple direct-product components of a catalyst.

## 4. Balanced batches attain the tradeoff

Put \(v=\min(s,m)\) and partition the marks in order into \(v\) consecutive batches, with lengths differing by at most one. Successively delete each batch, using the intervening prefix-deletion profiles as the catalyst factors. For the batch with indices \(a+1,\ldots,d\), use the integer period vector
\[
 z_i=2^{d-i+1}-1\quad(a<i\le d),\qquad z_i=0\quad\text{otherwise}.
\]
By (3) all defects of the batch are one. All defects of marked products with index greater than \(d\) are zero. The only potentially negative defect is at index \(a\) when \(a>0\), whose product is already absent. Unmarked defects are zero by construction. Thus (4) and (5) give a feasible cochain of cost at most \(3L(2^{d-a}-1)\) for that step.

The product of the \(v-1\) intermediate algebras has dimension \(N_m^{v-1}\). Arrange the source and target factors so that each of the \(v\) steps is performed in one coordinate simultaneously, as in the exact profile-cost construction. The additive cycle mean and integral difference constraints give a monomial witness of total cap equal to the ceiling of the sum of these costs, with a constant factor permutation on one side. If \(s\le m\), then \(v=s\) and each batch has length at most \(\lceil m/s\rceil\), giving an upper bound by an absolute constant times \(s(2^{m/s}-1)\). If \(s>m\), then \(v=m\) and the summed bound is \(O(m)\), while \(s(2^{m/s}-1)\ge m\log 2\). This proves (1).

For the dimension consequences, polynomial catalyst dimension has bounded \(s\). To reach order \(m^{O(1)}\), the lower bound forces \(m/s=O(\log m)\), and taking \(s\) of order \(m/\log m\) suffices by the upper bound. Since \(\log N_m=\Theta(\log m)\), the exponential-scale threshold for polynomial order is as stated. For order \(O(m)\), writing \(x=m/s\) gives a lower bound proportional to \(m(2^x-1)/x\), so \(s=\Omega(m)\) is necessary. The construction at \(s=m\) attains it.

## 5. A universal exponential bound in catalytic order

For any comparison of common-type thin Peirce profiles as in the exact profile-cost theorem, including its heterogeneous products, suppose an algebra catalyst achieves total cap at most the nonnegative integer \(P\). Then the unamplified comparison admits total cap at most \(2^P-1\).

Indeed the exact catalytic threshold supplies a type-preserving matching and profile paths with optimal cochains whose total cycle means are at most \(P\). Fix one such path with step cochains \(w_1,\ldots,w_\ell\). For any supported triangle and any cochain \(w\) with defect \(\delta=w(x,z)-w(x,y)-w(y,z)\), the length-three layered closed walk
\[
 B_x\to A_y\to C_z\to B_x
\]
has reward \(-\delta\). Thus a negative defect always has magnitude at most \(\rho(w)\), even when the corresponding product is absent. Write \(R_j=\lfloor\rho(w_j)\rfloor\) and combine the path cochains with coefficients
\[
 M_j=\prod_{i>j}(1+R_i).
\]
If a product is deleted at step \(j\), all earlier defects are zero, its step-\(j\) defect is at least one, and a later step-\(i\) defect is at least \(-R_i\) by integrality. Its combined defect is at least \(M_j-\sum_{i>j}M_iR_i=1\), by telescoping the products. A product retained at the end has zero defect in every step. Hence the combined integral cochain suffices for the direct comparison of the path endpoints.

The cycle mean is subadditive and positively homogeneous. Concatenate the finite step lists for all paths, so their total mean remains at most \(P\). Replacing individual suffix coefficients \(M_j\) in a path by the upper bounds given by the global suffix products \(\widetilde M_j\) only increases the bound on the sum of resulting means, since the means are nonnegative. Put \(R=\sum_j R_j\) over that concatenation. Then
\[
 \sum_j\widetilde M_j R_j=\prod_j(1+R_j)-1\le 2^R-1.
\]
The remaining fractional contribution is at most \(2^R(P-R)\), because \(\widetilde M_j\le2^R\). The sum of these bounds is at most \(2^P-1\), using \(1+(P-R)\le2^{P-R}\) for the nonnegative integer \(P-R\). The product cap construction applied to the combined cochains gives the stated integer total cap. If the paths are all stationary, it gives cap zero.

The family of this note has catalytic order \(\Theta(m)\) and direct order \(\Theta(2^m)\). A fixed catalytic order therefore bounds direct order throughout this thin profile class, while growing catalytic order can yield an exponential improvement.

These are written proofs. The exact earlier profile theorem is the input that accounts for arbitrary algebra catalysts and arbitrary mixing in their three tensor modes. The new construction uses only fixed-size topological pieces and integer cochains.
