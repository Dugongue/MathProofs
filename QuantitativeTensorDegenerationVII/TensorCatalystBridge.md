# Exact pole-cap cancellation for nonassociative tensor catalysts

For a bilinear tensor \(\beta:X\times Y\to Z\), conciseness means that both input annihilators are zero and the outputs span \(Z\). Use the three paired adjoint algebras
\[
\begin{aligned}
 L_\beta&=\{(P,Q):\beta(Px,y)=Q\beta(x,y)\},\\
 M_\beta&=\{(P,Q):\beta(Px,y)=\beta(x,Qy)\},\\
 R_\beta&=\{(P,Q):\beta(x,Py)=Q\beta(x,y)\}.
\end{aligned}
\]
In \(L_\beta\) both operators compose in the written order. In \(M_\beta\) they compose in reverse order on \(X\) and in the written order on \(Y\). In \(R_\beta\) both compose in reverse order. Thus the three operations on a multiplication tensor recover left multiplication, balanced right–left multiplication, and right multiplication, respectively. An adjoint algebra is scalar if it consists of the common scalar pairs.

**Theorem.**
1. For any equal-dimensional associative unital \(k\)-algebras \(S,T\) with \(Z(S)=Z(T)=k\), every concise \(\beta\) with three scalar paired adjoint algebras preserves the exact three forward pole caps for the comparison of their multiplication tensors on tensoring both sides with \(\beta\). The catalyst may be rectangular and the proof requires no invertible slices.
2. For connected thin acyclic \(0/1\) Peirce pairs with common support and a common based radical grading, the same exact cancellation holds for every concise \(\beta\) whose three paired adjoint algebras become semisimple over \(\overline{k}\). This includes the compatible Peirce products used in the earlier profile and catalyst dimension results.
3. In every square format \(d\times d\times d\), \(d\ge3\), a nonempty Zariski open set of tensors has three scalar paired adjoint algebras. There are explicit examples over every field with invertible slices in all three modes. Their tensors are outside the orbits of associative unital multiplication tensors.

The bounds apply to arbitrary Laurent witnesses, with separate caps on the forward entries and no restriction on inverse poles. In particular either comparison has the same least polynomial presentation order under the corresponding hypotheses. [Prior results for associative algebra catalysts](OptimalCatalystSeed.md)

## 1. Paired adjoints and their integral actions

Let \(\mu_S\) be multiplication in a unital associative algebra \(S\). For every concise \(\beta\),
\[
 L_{\mu_S\otimes\beta}=S\otimes L_\beta,\qquad
 M_{\mu_S\otimes\beta}=S\otimes M_\beta,\qquad
 R_{\mu_S\otimes\beta}=S\otimes R_\beta. \tag{1}
\]
We use the natural actions of the factors on the three modes. For the left identity, write the two operators as matrices indexed by a basis of \(S\). Testing the adjoint equation on second inputs \(1\otimes y\) gives one catalyst adjoint pair at each matrix entry. Expand these pairs in a basis \((P_j,Q_j)\) of \(L_\beta\). The other second inputs impose
\[
 \sum_j (D_j(a)b-D_j(ab))\otimes Q_j\beta(x,y)=0,
\]
where \(D_j\) acts on the \(S\)-factor. The \(Q_j\) are linearly independent because the projection to \(Q\) in \(L_\beta\) is injective by input conciseness. Since the outputs span, each \(D_j(a)b=D_j(ab)\), so \(D_j\) is left multiplication. The right identity follows with the input roles reversed. For \(M\), write the second operator on \(1\otimes y\) as a sum of \(c_j\otimes Q_jy\) over a basis \(c_j\) of \(S\). Testing on \(1\otimes x,1\otimes y\) gives the corresponding pairs \((P_j,Q_j)\) in \(M_\beta\). Then testing the adjoint equation with one of the \(S\)-inputs equal to \(1\), and using input conciseness, gives the first operator on \(a\otimes x\) as \(\sum_j ac_j\otimes P_jx\) and the second on \(b\otimes y\) as \(\sum_j c_jb\otimes Q_jy\). These descriptions prove (1), including the indicated algebra products.

The two adjacent paired adjoint actions on any mode commute. For example, on \(X\), move the middle action to \(Y\) inside the bilinear evaluation and move the left action to \(Z\). Either order produces the same result, and conciseness in \(X\) gives commutation. The same argument applies on \(Y\), and output spanning gives commutation on \(Z\). Thus \(X\) has left \(L\) and right \(M\) actions, \(Y\) has left \(M\) and right \(R\) actions, and \(Z\) has left \(L\) and right \(R\) actions. The law is equivariant over the left and right actions and balanced over the middle action. [Paired adjoints and their algebra structures](https://www.math.colostate.edu/~jwilson/papers/Central.pdf)

Let an integral tensor arc over \(R=k[[t]]\), with fraction field \(K=k((t))\), have generic presentation
\[
 \nu(x,y)=F_Z(\mu_S\otimes\beta)(F_Xx,F_Yy)
 \quad\text{and special law}\quad \mu_T\otimes\beta.
\]
All three \(F\)'s are generically invertible and the forward entry caps are \(p_X,p_Y,p_Z\). The two input maps go from the generic target spaces to the source spaces, and the output goes in the opposite direction. Conjugations by these maps in their appropriate directions transport the paired adjoint actions. Each integral paired adjoint algebra is a kernel of linear equations. Its generic and special dimensions agree by (1), so the kernel gives a free direct summand and specializes to the full special adjoint algebra. In detail, a maximal-rank minor in the special system gives a unit pivot block. After eliminating it the residual block is zero by the generic rank, and the resulting free kernel commutes with both base changes. The same argument applies to the kernel defining any simultaneous commutant whenever its two endpoint dimensions agree.

We will use the following matrix lifting fact. If a finite free \(R\)-algebra has special algebra \(M_d(k)\) and generic algebra \(M_d(K)\), it has a system of matrix units lifting those of the special algebra. Lift orthogonal diagonal idempotents successively in complementary corners by the iteration \(v\mapsto v-(2v-1)^{-1}(v^2-v)\). It is defined in the \(t\)-adically complete algebra and doubles the order of the error. Their Peirce corners are free rank one. Lift \(E_{i1},E_{1i}\) in the respective corners, then adjust the second lift by a unit so its product with the first is the first diagonal identity. The opposite product is an idempotent reducing to the identity in the other rank-one corner, and hence is that identity. The resulting products yield all matrix units. If this matrix algebra acts on a free module, its matrix units identify that module integrally with the tensor product of the image of \(E_{11}\) and the standard multiplicity space \(R^d\).

## 2. Scalar paired adjoints and arbitrary scalar-center algebras

Suppose \(\beta\) has three scalar paired adjoints, and put \(d_X=\dim X\), \(d_Y=\dim Y\), \(d_Z=\dim Z\) for its catalyst modes. By (1), the simultaneous commutant of the two adjacent adjoints on each full mode is \(M_{d_i}(k)\) at the special endpoint and \(M_{d_i}(K)\) at the generic endpoint. Indeed the mode is the regular \(T\)- or \(S\)-bimodule times the catalyst space, so the commutant is the matrix algebra on that space over the corresponding center, which is scalar. The integral commutant specializes by the kernel argument. Lift its standard matrix units. In integral frames reducing to the written decompositions, each target mode is identified with \(R^{\dim T}\otimes R^{d_i}\), with the integral commutant acting on the second factor.

Each \(F_i\) conjugates the intrinsic commutants. In the chosen frames its induced automorphism of the full matrix algebra is inner by Skolem–Noether. Removing that conjugation leaves a map commuting with each matrix unit, so
\[
 F_i=G_i\otimes H_i
\]
for invertible \(K\)-matrices \(G_i,H_i\). This holds in each of the three prescribed directions. Let \(v\) denote the least valuation of the entries of a tensor or matrix. A Kronecker product has valuation the sum of the two valuations, so \(v(G_i)+v(H_i)\ge-p_i\).

The resulting law is \(\tau\otimes\gamma\), where \(\tau=G\cdot\mu_S\) and \(\gamma=H\cdot\beta\) use the three mode actions. It is integral with nonzero special tensor \(\mu_T\otimes\beta\). Therefore \(v(\tau)+v(\gamma)=0\). Furthermore \(v(\gamma)\ge\sum_i v(H_i)\) by the multilinear coefficient formula. Choose integers \(b_i\ge v(H_i)\) with sum \(v(\gamma)\). Acting on \(\mu_S\) by \(t^{b_i}G_i\) keeps each cap and gives \(t^{v(\gamma)}\tau\), integral with nonzero reduction. Its reduction is a nonzero scalar multiple of \(\mu_T\): tensor it with the nonzero reduction of \(t^{-v(\gamma)}\gamma\) and compare the simple-tensor factorization of \(\mu_T\otimes\beta\). A constant scalar adjustment corrects that multiple. This proves same-field cancellation. The argument also works for distinct nonzero source and target catalyst factors after the integral factorization, provided their modal multiplicities match. The converse tensors an unamplified witness with identities.

## 3. Explicit nonassociative examples

In dimension \(d\ge3\), take the commutative unital bilinear law \(C\) with basis \(1,x_1,\ldots,x_{d-1}\), indices cyclic on the \(x_i\)'s, and products \(x_i^2=x_{i+1}\), \(x_ix_j=0\) for \(i\ne j\). For any unital bilinear law, evaluation at the unit identifies its three paired adjoints with its left, middle, and right nuclei. The nucleus condition in the indicated slot is vanishing of all associators \((ab)c-a(bc)\) with that slot fixed. For \(z=\alpha 1+\sum_i b_ix_i\), the associator \((z,x_i,x_{i+1})\) equals \(b_i x_{i+2}\). Thus the left nucleus is scalar, and the right is scalar by commutativity. For the middle nucleus use \((x_i,z,x_{i+1})\). It equals \(b_ix_{i+2}\) when \(d-1\ge3\), and \(b_ix_i-b_{i+1}x_{i+1}\) when \(d-1=2\). These tests force every \(b_i=0\) over every field. The law is nonassociative, and its tensor cannot be isotopic to the multiplication tensor of a \(d\)-dimensional associative unital algebra, for such a tensor has paired adjoint dimension \(d\) by (1).

The input slices at \(1\) are identities. The output functional taking value one on each \(x_i\) and value \(d\) on \(1\) gives a pairing with identity lower diagonal block and Schur complement \(d-(d-1)=1\), hence an invertible third slice. Finally conciseness and dimension one for each paired adjoint kernel are Zariski open rank conditions. The explicit tensors show that this intersection is nonempty, so it is dense in each square tensor space over an algebraic closure.

## 4. Semisimple paired adjoints reduce to rectangular matrix multiplication

Extend coefficients to \(F=\overline{k}\), preserving all forward pole bounds. Suppose the three catalyst adjoints split as products of matrix algebras, with simple block labels \(l,m,r\), respectively, and corresponding matrix sizes \(a_l,b_m,c_r\). By the commuting actions of Section 1, the catalyst modules split into blocks \(X_{lm},Y_{mr},Z_{lr}\). Each is a module for the two indicated full matrix algebras with opposite actions on the two sides. Thus, for example,
\[
 X_{lm}=M_{a_l,b_m}(F)\otimes U_{lm},
\]
where \(U_{lm}\) is the multiplicity space, and likewise use \(V_{mr}\) and \(W_{lr}\) on the other modes. This decomposition follows by the standard matrix units, first taking the common \((11,11)\) corner and then using rectangular row and column operations. The triple law for a consistent set of labels is the product of rectangular matrix multiplication and a residual tensor
\(\beta_{lmr}:U_{lm}\times V_{mr}\to W_{lr}\). To see this, balancing over the middle block forces the contraction of the middle matrix indices, and equivariance over the outer blocks forces the output matrix indices. Its remaining scalar-basis coefficients are arbitrary residual data. Cross terms with inconsistent labels vanish by the central idempotents and the same balanced identities.

Use this argument with the two associative outer laws \(S,T\) of a connected thin Peirce pair. Their centers are scalar because commuting with the vertex idempotents forces a diagonal vector and each supported strict corner equates its endpoint coefficients. Thus, in (1), the center of an endpoint adjoint algebra has one copy of \(F\) for each catalyst block label. The kernels defining these centers specialize exactly by the equality of dimensions. Lift their orthogonal central idempotents integrally, so that the normalized tensor law splits into the corresponding triple blocks, and the witness matches the source and special labels through the intrinsic algebras. In a matched adjoint block the matrix size agrees: its dimension is the common outer dimension times the square of that size. Every matched mode edge also has the same dimension, because its two commuting idempotent projections are integral. Consequently its residual multiplicities agree.

Choose a special triple with nonzero residual tensor. The generic matched triple is nonzero, since its integral tensor specializes to the chosen triple. Restrict the three maps to the matched mode-edge spaces. This restriction preserves the scaled lattice inclusions defining the three caps. For example on a source edge the two adjoints act as \(S\otimes M_a(F)\) on the left and \(S\otimes M_b(F)\) on the right, on the bimodule \(S\otimes M_{a,b}(F)\otimes U\). Its simultaneous commutant is \(M_{\dim U}(F)\): the rectangular matrix bimodule has only scalar bimodule endomorphisms, and the regular \(S\) bimodule has commutant \(Z(S)=F\). The special edge has the same commutant size for \(T\), so again the integral commutant is free and split with lifted matrix units. Apply the mode-factorization and scalar transfer of Section 2 to the residual multiplicity spaces. It applies even if the residual laws of the matched blocks are different or fail conciseness, since after the factorization it uses only a nonzero reduction. The result is a witness with precisely the original caps from
\[
 \mu_S\otimes \mathrm{MM}_{a,b,c}\quad\text{to}\quad \mu_T\otimes \mathrm{MM}_{a,b,c},
\]
where \(\mathrm{MM}_{a,b,c}\) is the bilinear law \(M_{a,b}(F)\times M_{b,c}(F)\to M_{a,c}(F)\) of ordinary matrix multiplication.

## 5. Rectangular matrix multiplication cancels on thin Peirce pairs

Here \(S,T\) are thin acyclic \(0/1\) Peirce algebras with common support and a common based radical grading. Denote the three adjoints of the rectangular-matrix comparison by \(L,M,R'\). Their endpoint laws are \(S\otimes M_a(F),S\otimes M_b(F),S\otimes M_c(F)\), respectively, and likewise with \(T\). The support of each adjoint algebra is that of the thin pair, with a regular matrix bimodule replacing each supported line.

We recall the relevant integral graded facts. For each adjoint algebra the intersection of its integral lattice with the generic Jacobson radical is saturated and nilpotent. Its special image has the dimension of the whole special radical, by the common endpoint ranks, so equals it. Powers specialize exactly by the unit-minor argument for the product image, using their matching generic and special dimensions. The radical-induced filtration on each tensor mode is the image under either adjacent adjoint radical power. The two images agree because they have the same generic subspace and are both saturated, by the same rank argument. At the endpoints these mode filtrations are the thin radical powers tensored with the indicated rectangular matrix spaces. The filtered tensor law induces graded products: by left and right equivariance its product on \(J_L^iX\) and \(YJ_{R'}^j\) lands in \(J_L^iZJ_{R'}^j=J_L^{i+j}Z\), where the two adjacent filtrations agree on the modes. Each mode map preserves the corresponding filtration generically, and retains its forward pole cap on the induced graded maps in integral frames.

The adjoint quotient algebras split as products of matrix algebras over \(F[[t]]\) by diagonal idempotent and matrix unit lifting. This follows by the same rank and lifting argument as in Section 1, with off-block corners zero by rank. Any supported mode corner in its unique Peirce grade has an integral matrix-bimodule basis obtained from its \((11,11)\) corner as before. In any mode the two adjacent permutations of its endpoint labels agree. Indeed they preserve the bipartite support of the common corner graph. The diagonal is its unique perfect matching, since any matching \(x\mapsto y\) with supported pairs must move each vertex forward or keep it fixed. In a total order extending the acyclic support, the sum of the vertex ranks is invariant under a permutation, so every forward move has to be equality. Thus two adjacent label permutations match their diagonals, and all three agree. Use this common matching for target labels below.

On each diagonal adjoint block the generic transporter is conjugation by a matrix \(S^L_x,S^M_x,S^{R'}_x\) respectively. On a corresponding adjoint corner it is the action of the endpoint conjugating matrices times one scalar \(\eta^L_{xy},\eta^M_{xy},\eta^{R'}_{xy}\), since the regular matrix bimodule has scalar commutant. On a mode corner each forward map must likewise be a scalar times the indicated two matrices from the adjacent transports. Write these three maps in order as
\[
\begin{split}
 X&\longmapsto \theta^X_{xy}(S^L_x)^{-1}XS^M_y,\\
 Y&\longmapsto \theta^Y_{xy}(S^M_x)^{-1}YS^{R'}_y,\\
 Z&\longmapsto \theta^Z_{xy}S^L_xZ(S^{R'}_y)^{-1}.
\end{split} \tag{2}
\]
This follows by removing the two conjugations, leaving a scalar endomorphism of the rectangular matrix bimodule. At a diagonal mode triple compose (2) with the rectangular multiplication. The matrices cancel, and its scalar is \(\theta^X_{xx}\theta^Y_{xx}\theta^Z_{xx}\). The integral law there reduces to ordinary rectangular multiplication, so that scalar has valuation zero.

Here are explicit cap inequalities. Write \(k_{xy}=v(\theta^X_{xy})\), \(l_{xy}=v(\theta^Y_{xy})\), \(m_{xy}=v(\theta^Z_{xy})\), and \(s^I_x=v(S^I_x)\) for the three adjoint labels \(I\). The three relaxed forward valuations are
\[
 \widetilde k_{xy}=k_{xy}-s^L_x+s^M_y,\quad
 \widetilde l_{xy}=l_{xy}-s^M_x+s^{R'}_y,\quad
 \widetilde m_{xy}=m_{xy}+s^L_x-s^{R'}_y.
\]
Each is at least the respective actual valuation in (2), because \(v(S^{-1})\le-v(S)\) and the matrix \(X\mapsto AXB\) has least entry valuation \(v(A)+v(B)\), also for rectangular \(X\). Set
\[
 \alpha_x=\widetilde k_{xx},\quad \beta_x=\widetilde l_{xx},\quad
 w_{xy}=v(\eta^{R'}_{xy})+s^{R'}_x-s^{R'}_y,
 \qquad w_{xx}=0.
\]
The diagonal valuation sum above gives \(\widetilde m_{xx}=-\alpha_x-\beta_x\).

An adjoint corner acting from a diagonal mode corner into the corresponding strict mode corner has a unit coefficient in the integral matrix frames. The special action is standard rectangular multiplication by the adjoint matrix, so the scalar coefficient is a unit. Use the right \(R'\) action on \(Y_{xx},Z_{xx}\) along \((x,y)\). Intertwining by (2) gives
\[
 l_{xy}=l_{xx}-v(\eta^{R'}_{xy}),\qquad
 m_{xy}=m_{xx}+v(\eta^{R'}_{xy}).
\]
The left \(M\) action on \(Y_{yy}\) and the right \(M\) action on \(X_{xx}\) likewise give \(l_{xy}=l_{yy}-v(\eta^M_{xy})\) and \(k_{xy}=k_{xx}-v(\eta^M_{xy})\). Combining yields
\[
 \widetilde k_{xy}=\alpha_x+\beta_x-\beta_y-w_{xy},\qquad
 \widetilde l_{xy}=\beta_x-w_{xy},\qquad
 \widetilde m_{xy}=w_{xy}-\alpha_x-\beta_x.
\]
These are at least \(-p_X,-p_Y,-p_Z\), respectively, including on the diagonal. Also \(w\) has the necessary defects at all generic nonzero thin products: in the \(R'\) adjoint algebra the product scalar has valuation \(v(\eta^{R'}_{xz})-v(\eta^{R'}_{xy})-v(\eta^{R'}_{yz})\), and the vertex corrections cancel. It is zero for retained products and positive for deleted products. A generic zero product cannot specialize to a nonzero product in the corresponding free graded corners.

Now take the monomial thin transporter using the common label matching and exponents \(w_{xy}\), and the two diagonal units of weights \(\alpha,\beta\). Its three mode exponents are exactly the displayed relaxed valuations, so it keeps each original cap. The values of the surviving structure constants are \(1\), and the desired deleted coefficients have positive valuation. This gives a witness over \(k((t))\) because the exponents and the matching are defined over the original field. Thus rectangular matrix multiplication cancels, and Section 4 gives the claimed cancellation for every semisimple paired-adjoint catalyst. The argument requires only the indicated thin pair properties, so it applies to the earlier thin profile products and to the dimension–order examples. [Prior integer cap construction](PowerSeed.md)

Finally multiplication tensors are concise by unitality, and all catalysts in the theorem are concise. Clearing forward caps and truncating the resulting power-series matrices to the leading order produces a polynomial presentation of that order. Conversely a polynomial presentation with concise leading tensor is generically invertible in every mode, and dividing one matrix by the leading power gives a Laurent witness. This gives equality of the least orders in the theorem. The results are written proofs.

## 6. Associative catalysts tensored with a scalar-adjoint tensor

Let \(A_+,A_-\) be the algebras of a connected thin Peirce comparison above. Suppose the catalyst is \(\mu_B\otimes\beta\) for any nonzero associative unital \(B\) and a concise \(\beta\) with scalar paired adjoints. A witness with this catalyst gives a witness over \(\overline{k}((t))\) with an associative algebra catalyst \(B'\) of dimension at most \(\dim_k B\), preserving each cap. In particular the previous optimal profile and dimension–order lower bounds apply in this larger class with effective dimension \(\dim_k B\).

To prove it, extend to \(F=\overline k\) and write \(B_0=B\otimes_k F\). The centroid of a concise bimap \(\nu\) consists of triples whose actions agree in the identity
\[
 \nu(P_Xx,y)=\nu(x,P_Yy)=P_Z\nu(x,y).
\]
The centroid for \(\mu_{A_\pm\otimes B_0}\otimes\beta\) is \(Z(B_0)\), acting by central multiplication in the algebra factor in every mode. In fact (1) for the scalar-adjoint \(\beta\) gives left and right regular actions on this factor, and equality of left and right multiplication forces the same central element. The center of \(A_\pm\) is scalar, so the center of the algebra factor is \(Z(B_0)\). This centroid is intrinsic under the three-mode maps by conjugation in the respective directions. Its integral kernel specializes exactly because its endpoint dimensions agree.

This construction repeats whenever both endpoints use the same associative algebra \(B_i\). Let \(J_i\) be the nilradical of \(Z(B_i)\). Its dimension survives extension to \(F((t))\) because over \(F\) each center factor is local with residue \(F\). In the integral centroid take the saturation of the generic nilradical, namely its intersection with the integral centroid lattice. Its special image is nilpotent with dimension \(\dim_F J_i\), so is the whole special centroid nilradical. On each integral mode take the image of its action. The generic and special dimensions of this mode subspace agree: they are \(\dim_F A_\pm\cdot\dim_F(J_i B_i)\) times the corresponding catalyst mode dimension of \(\beta\). The image is therefore a free direct summand by unit-minor elimination. The tensor descends to all three mode quotients by the centroid identity. The generic conjugation transports the subspaces and the mode maps descend with their original caps. Both quotient endpoints use the same associative catalyst \(B_{i+1}=B_i/J_i B_i\), with \(\beta\) unchanged.

If \(J_i\ne0\), the proper nilpotent ideal \(J_i B_i\) is nonzero and dimension decreases. After finitely many steps the remaining \(B'\) has reduced, split center over \(F\). In the integral centroid lift its primitive central idempotents. They split the modes into free matched blocks and the tensor law has no cross terms by the centroid identity. Each source block is the multiplication tensor of \(A_+\) tensored with some central factor of \(B'\), then tensored with \(\beta\), and similarly on the target. The matched algebra factors have equal dimensions by the ranks of their mode summands, and each has center \(F\). Apply Section 2 separately to each matched block to cancel \(\beta\), then assemble the modes as block-diagonal maps under the recovered matching. The separate forward caps bound the entries of the assembled maps. This is a witness for \(\mu_{A_+\otimes B'}\) to \(\mu_{A_-\otimes B'}\), with the same common \(B'\) on the two sides. The profile and dimension lower bounds hold over every field and can therefore be applied to it. [Earlier dimension–order bounds](https://github.com/Dugongue/MathProofs/blob/main/QuantitativeTensorDegenerationVI/CatalystTradeoff.md)

There is also a harmless padding extension of the theorem. For a nonzero catalyst \(\beta\), choose complements to its two input annihilators and restrict the output to its image span, obtaining a concise core. In a padded witness, restrict the target inputs to their cores and project each acting input map to its source core. On output, restrict the acting map to the source output core and project to the target output core. These are constant restrictions and projections and preserve the caps. The resulting compressed mode maps are generically invertible by the full flattening ranks of the concise special tensor. Conversely extend a core witness by identity maps on the unused complements. Thus the same conclusions hold when only the concise core meets the paired-adjoint hypothesis.
