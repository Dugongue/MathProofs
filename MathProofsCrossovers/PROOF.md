# Crossovers in tensor isomorphism and binary designs

These are informal proofs. They use the public MathProofs library at commit eb79798397b010605e561d6e87b12f709cd34dca. The first three sections address published questions in the settings stated below. The complex case in Section 1 was already solved by Lysikov and Walter, and is included with credit. The finite-field clause, Gaussian smoothed analysis and minimum-rank classification are candidate new answers. The fourth section settles the direct affine-block version of a published extension question. Publication priority remains provisional.

## 1. Unitary tensor isomorphism reduces to ordinary tensor isomorphism

**Statement.** For complex tensors with Gaussian-rational coefficients, unitary 3-tensor isomorphism reduces to ordinary complex 3-tensor isomorphism in deterministic polynomial time. For every fixed finite field \(E=\mathbb F_{q^2}\) with its nontrivial involution over \(K=\mathbb F_q\), the analogous decision problem reduces to ordinary 3-tensor isomorphism over either \(K\) or \(E\), in deterministic polynomial time. Both reductions cover arbitrary dimensions and all inputs, including zero and nonconcise tensors. This gives the finite-field clause of [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.10](https://arxiv.org/pdf/2306.03135#page=10). The complex clause is prior work of Lysikov and Walter, Theorem V.31, using a construction of Bürgisser et al. The short polar argument below is an alternate proof of the orbit-equality step in that construction. [Lysikov and Walter, Theorem V.31](https://arxiv.org/html/2411.04639v2#Thmtheorem31)

### Complex coefficients

For \(T\) in \(V_1\otimes V_2\otimes V_3\), take the mixed tensor tuple \((T,T^\dagger)\), where \(T^\dagger\) is the conjugate coefficient array regarded as a tensor in \(V_1^*\otimes V_2^*\otimes V_3^*\). A product of unitary changes of basis carries this tuple to the tuple for its image.

Conversely let \(g_i\in\operatorname{GL}(V_i)\) carry the mixed tuple for \(T\) to that for \(S\). On the first component we have \((\bigotimes_i g_i)T=S\). Conjugating the coefficient equation on the dual component gives \((\bigotimes_i(g_i^*)^{-1})T=S\). Write \(g_i=u_i p_i\) in right polar form with \(u_i\) unitary and \(p_i\) positive definite Hermitian. Since \((g_i^*)^{-1}=u_i p_i^{-1}\), putting \(P=\bigotimes_i p_i\) gives \(PT=P^{-1}T\). Hence \(P^2T=T\). Positivity of \(P\) forces \(PT=T\), by decomposing into its eigenspaces. Therefore \(S=(\bigotimes_i u_i)T\).

Use the basis-explicit mixed linear structure compiler to turn the two labelled tensors into one ordinary 3-tensor. The arities and signature are fixed, the auxiliary dimensions are polynomial, and conjugation of the input coefficients is exact. The argument also applies in an arithmetic model that allows complex conjugation on input. The same tuple has a closed complex orbit by Kempf–Ness, since the infinitesimal Hermitian contributions of the primal and conjugate-dual copies to the squared norm cancel. Thus this encoding also reduces local unitary orbit equality to complex tensor orbit-closure intersection, with exact reflection. [MathProofs linear-structure compiler](https://github.com/Dugongue/MathProofs/blob/main/LinearStructureUniversality/PROOF.md) · [Lysikov and Walter on tensor orbit closures](https://arxiv.org/abs/2411.04639)

### Finite coefficients

Write \(W_i=V_i^*\), with the standard Hermitian form \(h_i\) in the dual basis. View \(T\) as an \(E\)-trilinear scalar form on \(W_1,W_2,W_3\). An isomorphism on these argument spaces under inverse transpose has exactly the original unitary equivalence meaning, because inverse transpose preserves the unitary group.

Over \(K\), keep the three spaces obtained by restriction of scalars. Mark on each the endomorphism \(J_i\) given by multiplication by a fixed generator of \(E/K\), and the bilinear form \(\operatorname{Tr}_{E/K}(h_i)\). Mark also the trilinear form \(\operatorname{Tr}_{E/K}(T)\). The endomorphisms force the maps to be \(E\)-linear. Preservation of the trace forms then recovers preservation of the \(E\)-valued forms. In detail, vary the first argument by a factor \(\lambda\in E\) in the trace identity. Linearity or conjugate linearity in that argument gives \(\operatorname{Tr}_{E/K}(\lambda z)=0\) for every \(\lambda\), after replacing \(\lambda\) by its conjugate if necessary. The trace pairing for a finite separable extension is nondegenerate, so \(z=0\). This works also in characteristic two. The converse follows by taking traces.

Compile the resulting fixed signature over \(K\). To produce ordinary TI over \(E\), apply the MathProofs same-characteristic reduction to the resulting \(K\)-instance, which keeps the \(K\)-rational condition by explicitly tagging the field structure. All steps have polynomial binary runtime for fixed fields. [MathProofs same-characteristic reduction](https://github.com/Dugongue/MathProofs/blob/main/FixedCharacteristicTensorIsomorphism/Proof.md)

In fact for these finite fields the reverse containment holds as well. In a two-dimensional Hermitian space the isotropic line generated by \((1,c)\), with \(c\bar c=-1\), has an isotropic partner with nonzero pairing. The norm map is surjective and the trace map is surjective, so one can choose a partner of pairing 1 and make it isotropic by adding a suitable multiple of the first vector. This gives a hyperbolic plane also in characteristic two. Take \(n\) such planes. On the first isotropic half every \(\operatorname{GL}_n(E)\) map extends to a unitary map by the inverse conjugate transpose on the second half. Pad each tensor mode into the first half. Every transporter of padded tensors restricts to an isomorphism of their intrinsic mode supports, because those supports are images of the mode flattenings. Extend each restricted support isomorphism to the original mode dimensions by arbitrary complementary bases. Thus the padding reflects and preserves isomorphism even for nonconcise inputs. This combines the support argument used in the MathProofs symplectic construction with the field and form tags above. [MathProofs symplectic reduction](https://github.com/Dugongue/MathProofs/blob/main/TIEqTISp.lean)

## 2. Small-noise smoothed analysis for orthogonal and unitary tensor isomorphism

**Statement.** Let \(A\) be any real or complex \(n\times n\times n\) tensor, \(n\ge2\). Perturb each real coordinate by an independent \(N(0,\sigma^2)\) variable, with an independent imaginary perturbation of the same variance in the complex case. Denote the perturbed tensor by \(X\), put \(0<\eta<1\), and set
\[
R=\left(\|A\|_F+\sigma\sqrt{4n^3/\eta}\right)^2.
\]
With probability at least \(1-\eta\), all three marginal Gram matrices of \(X\) have spectrum in \([0,R]\) and all their distinct-index eigenvalue gaps exceed
\[
\delta=\frac{\eta\sigma^4}{100 n^2(R+\sigma^2)}.
\]
This is a uniform inverse-polynomial gap for polynomially bounded \(\|A\|_F\), inverse-polynomial perturbations and inverse-polynomial failure probabilities. It supplies a small-Gaussian-noise answer to [Chizewer, Everett, Mithal and Qiao, Open Problem 2](https://arxiv.org/html/2603.27128v1#S1.SS5), including their spectral hypothesis for exact isomorphism and gap-dependent orbit approximation. The proof reuses the marginal-Gram interface of MathProofs Problem 18 and applies spectral averaging to the row component outside the span of the other rows. [MathProofs Problem 18](https://github.com/Dugongue/MathProofs/tree/main/Problem18)

### A conditional density bound

Let \(W\) be one \(n\times n^2\) flattening of \(X\), so the marginal is \(H=WW^*\). Condition on all rows except row \(i\), and on the inner products of row \(i\) with those rows. This fixes the projection of row \(i\) onto their span. Its orthogonal component remains an independent isotropic Gaussian with variance \(\sigma^2\) per real coordinate and an arbitrary mean. Its dimension is at least \(n^2-(n-1)\), over the real or complex base field.

The diagonal \(H_{ii}\) is the squared row norm. Within its orthogonal component keep two real orthonormal coordinates and condition on the rest. These two coordinates have a joint density at most \(1/(2\pi\sigma^2)\), uniformly in their means. The area on which their squared radius belongs to an interval of length \(\ell\) is at most \(\pi\ell\). Therefore \(H_{ii}\) has conditional density bounded by \(K=1/(2\sigma^2)\). Averaging gives the same bound conditional on every entry of \(H\) except \(H_{ii}\), since all those entries are determined by the first conditioning. Another averaging gives the same bound when conditioning only on the entries of a principal minor other than its corresponding diagonal.

### Counting close eigenvalue pairs

For a Hermitian matrix \(H\), let \(N_I(H)=\operatorname{tr}1_I(H)\) for an interval \(I\). Rank-one spectral averaging gives
\[
\int_{\mathbb R}\langle e_i,1_I(H_0+t e_i e_i^*)e_i\rangle\,dt\le |I|.
\]
Indeed, for spectral parameter \(z\) in the upper half-plane the scalar resolvent is \(1/(t+\alpha(z))\), by Schur complementation, with \(\operatorname{Im}\alpha(z)<0\). Its imaginary part integrates to \(\pi\) in \(t\). Integrate over a slightly enlarged interval in the real part of \(z\) and let \(\operatorname{Im}z\) and the enlargement go to zero using Fatou's lemma and the spectral theorem. Thus a conditional diagonal density at most \(K\) gives conditional expected diagonal spectral mass at most \(K|I|\).

Write \(H^{(i)}\) for the minor obtained by deleting \(i\). Interlacing implies \(N_I(H)-1\le N_I(H^{(i)})\) whenever \(N_I(H)\ge1\). Multiply by the \(i\)-th diagonal spectral mass and sum. Condition first on all entries except \(H_{ii}\). Then apply the same single-diagonal spectral averaging estimate within the minor and sum over its diagonals. This gives
\[
\mathbb E[N_I(H)(N_I(H)-1)]
\le n(n-1)K^2|I|^2.
\]
No independence between the conditional diagonals is required. This is a Minami estimate in the present setting. [Aizenman et al., spectral averaging and Minami estimates](https://doi.org/10.1142/S0219199717500286)

The Frobenius norm squared of the perturbation has expectation at most \(2\sigma^2n^3\). Markov's inequality gives \(\|X\|_F^2\le R\) except with probability at most \(\eta/2\). On this event all marginal eigenvalues lie in \([0,R]\). Cover the pairs of points at distance at most \(\delta\) in this interval by the overlapping intervals \([j\delta,(j+2)\delta]\), \(0\le j\le\lfloor R/\delta\rfloor\). In each interval a pair occurs with probability at most \(2n(n-1)K^2\delta^2\). Sum over intervals and over three marginals. This contributes at most \(3n^2(R+\delta)\delta/(2\sigma^4)\). Since \(\delta\le\sigma^2\), the choice of \(\delta\) makes this less than \(\eta/2\), proving the claim.

### Algorithmic consequence

The exact simple-spectrum algorithm in Section 2.1 of Chizewer et al. applies to rationally encoded samples, with the orthogonal version using signs in place of phases. A second tensor \(B\) may be chosen adversarially after seeing \(X\), since the good event uses only \(X\). If \(B\)'s marginal spectra differ, return NO. If they agree and are simple, use the ordered eigenbases and solve the residual torus or sign equivalence. For rational encodings one can round the Gaussian perturbation to dyadic coordinates. If the resulting tensor differs from \(X\) by at most \(e\) in Frobenius norm, each Gram changes in operator norm by at most \(e(2\sqrt R+e)\). A dyadic precision making this smaller than \(\delta/4\) preserves a gap of at least \(\delta/2\) by Weyl's inequality. The rounding requires only polynomially many bits in the logarithms of the stated parameters. The exact query is isomorphism of the encoded, perturbed tensor.

For approximate complex isomorphism, apply their Theorem 2.8 to the gap \(\delta/2\), using its norm and accuracy hypotheses. For real inputs, one can also obtain the orthogonal analogue directly. If the distance is at most \(\varepsilon\), then under an orthogonal transporter each Gram differs from its counterpart by at most \(M\varepsilon\) in operator norm, where \(M=\|X\|_F+\|B\|_F\). If \(M\varepsilon<\delta/8\), Weyl's inequality aligns the ordered eigenvalues. Expanding each eigenvector in the counterpart eigenbasis bounds its error, after choosing a sign, by \(O(M\varepsilon/\delta)\). Thus the two tensor cores, after the appropriate signs, differ in each entry by at most \(\rho=O((1+\sqrt n M^2/\delta)\varepsilon)\), with the absolute constant taken large enough. Reject if any pair of core moduli differs by more than \(\rho\). For entries where both moduli exceed \(\rho\), impose the linear equation over \(\mathbb F_2\) that the product of the three signs matches the sign ratio. Reject if these equations are inconsistent. Otherwise use any solution. Small entries left unconstrained differ by at most \(3\rho\), and every constrained entry differs by at most \(\rho\). The resulting distance is at most \(3n^{3/2}\rho\). With rational computation, increasing the absolute constants and using certified eigenbasis approximations with core error at most \(\varepsilon\) implements these tests with the same asymptotic guarantee. The gap makes the required precision polynomial in the input and log precision parameters. This gives a polynomial separation factor on the stated good event. [Chizewer et al., exact and approximation algorithms](https://arxiv.org/html/2603.27128v1#S2)


## 3. Classification of minimum-rank translation designs of bent functions

**Statement.** Let \(m\ge 2\) be even. All translation designs of \(m\)-variable Boolean bent functions with binary incidence rank \(m+2\) are obtained from the following finite algebraic data. Take an \(m\)-dimensional commutative associative \(\mathbb F_2\)-algebra \(U\), possibly without a unit, with \(x^2=0\) for every \(x\), and a nondegenerate alternating bilinear form \(B\) satisfying \(B(xy,z)=B(x,yz)\). Define \(x\circ y=x+y+xy\). Choose a function \(c\) such that \(c(0)=0\) and
\[
c(x\circ y)=c(x)+c(y)+B(x,y).
\]
Every such choice exists. Relabel the underlying vector space of the translation design by a group isomorphism from \(\mathbb F_2^m\) to \((U,\circ)\), and use \(c\) or \(c+1\) as its defining function. Two resulting designs are isomorphic exactly when their ordinary-coordinate functions on \(U\) are EA-equivalent and their block sizes are equal. This is an exhaustive construction with an exact duplicate criterion. It answers [Hyun, Kwon, Wang and Wu, Open Problem 3](https://arxiv.org/html/2605.24355v1#S4.SS2). It combines the recoverable affine code used in the MathProofs bordered-rank proof with the regular-subgroup method used to analyze bent-design automorphisms. [Bordered-rank characterization](https://github.com/Dugongue/MathProofs/blob/main/PlateauedAdditionDesigns_BorderedRankCharacterization.lean) · [Bent-design automorphism groups](https://github.com/Dugongue/MathProofs/blob/main/CubicBentSupportCodeDesignAutomorphismGroups.lean)

### Recover affine coordinates from derivatives

Write \(f_b(v)=f(v+b)\) for the blocks of the translation design and let \(D\) be their binary linear span. The constant word 1 is in \(D\). Indeed apply the coordinate derivatives for the variables of a monomial of maximal degree in the algebraic normal form of \(f\). This gives the constant 1 and is a sum of translates. Let \(C\) be the span of 1 and the differences \(f_b+f\). Then \(f\notin C\). Otherwise an odd sum of translates of \(f\) would be constant. The corresponding sum \(L\) of translation operators squares to the identity in characteristic two, since the translations commute and each squares to the identity. Applying \(L\) again would make \(f\) constant, contrary to bentness. Thus \(\dim D=1+\dim C\).

Every nonzero-direction derivative of \(f\) is balanced, by the autocorrelation identity for bent functions. Also \(f_b+f_{b'}\) is a translated derivative when \(b\ne b'\). The \(2^m\) words \(f_b+f\) are therefore distinct modulo constants. In particular \(\dim D\ge m+2\), and rank \(m+2\) means that they exhaust \(C/\langle1\rangle\). Every nonconstant word in \(C\) is balanced. Choose \(m\) coordinate functions forming a basis modulo 1, normalized to vanish at the original origin. Their joint evaluation \(\pi\) gives a bijection to \(U=\mathbb F_2^m\), since all its nontrivial character sums vanish, and Fourier inversion gives a uniform fiber count of one. In these coordinates \(C\) is exactly the affine linear code.

Translations preserve \(C\), since they carry differences of block words to differences of block words. Consequently they act by affine permutations in the new coordinates. They form a regular elementary abelian group. Write its element carrying 0 to \(x\) as \(h_x(y)=x+A_x y\). By commutativity, \((A_x-I)y=(A_y-I)x\), so \(xy=(A_x-I)y\) is symmetric and bilinear. Since \(h_xh_y=h_{x+y+xy}\), comparing the linear parts gives \(A_{x+y+xy}=A_xA_y\), which is associativity of the multiplication. Squaring \(h_x\) gives \(x^2=0\). This is the classical correspondence between abelian regular affine groups and radical algebras. [Caranti, Dalla Volta and Sala](https://arxiv.org/abs/math/0510166)

### Recover the form and reconstruct every design

Set \(Q=f\circ\pi^{-1}\), using ordinary function composition here, and \(c(x)=Q(x)+Q(0)\). Write \(Q(h_x(y))+Q(y)=c(x)+\ell_x(y)\) with \(\ell_x\) linear. Evaluating at \(y\) and swapping \(x,y\) shows \(\ell_x(y)=\ell_y(x)\), because \(h_x(y)=h_y(x)\). Thus \(B(x,y)=\ell_x(y)\) is bilinear. The involution \(h_x\) gives \(B(x,x)=0\), and balanced derivatives give \(B(x,\cdot)\ne0\) for \(x\ne0\). The rule for \(c(x\circ y)\) follows by evaluation. Associativity of \(\circ\) in that rule gives the cocycle identity for \(B\). Expanding by ordinary bilinearity reduces this identity to \(B(xy,z)=B(x,yz)\).

Conversely the algebra data make \((U,\circ)\) an elementary abelian group of order \(2^m\). The identity for \(B\) makes
\[
(a,x)(b,y)=(a+b+B(x,y),\,x\circ y)
\]
an associative group law on \(\mathbb F_2\times U\). Symmetry and alternation make the group elementary abelian, so the projection onto \((U,\circ)\) splits as a homomorphism. For an explicit split, lift a group basis and extend by its binary combinations. The first coordinate of the section is the required \(c\). The formula for \(c\) gives balanced derivatives on \((U,\circ)\) because every \(B(x,\cdot)\) with \(x\ne0\) is nonzero and \(y\) ranges uniformly over the ordinary vector space. After identifying \((U,\circ)\) with \(\mathbb F_2^m\), this implies that the defining function is bent. Its derivatives span exactly the affine code modulo constants by nondegeneracy of \(B\). The earlier dimension calculation then gives rank \(m+2\). Thus enumerating multiplication tables satisfying the displayed identities, forms \(B\) and sections generates every minimum-rank design using finite tests on the stated data.

### Identify duplicates

In recovered coordinates the blocks are \(Q(y)+B(x,y)+c(x)\), as \(x\) ranges over \(U\), so there is one block with each linear mask and every block has the same weight. The substitution \(y\mapsto h_x(y)\) gives \(W_Q(B(x,\cdot))=(-1)^{c(x)}W_Q(0)\), where \(W_Q\) is the binary Walsh transform. Thus \(Q\) is bent in the ordinary coordinates as well. Each linear mask admits exactly one constant term with the given block weight, because the Walsh coefficients are nonzero. It follows that an EA change of \(Q\) preserves the design up to affine relabeling when the block weight is retained. Conversely a design isomorphism preserves the code spanned by pairwise block differences together with 1. That code is the affine linear code, and its coordinate permutations are affine because the pullbacks of its coordinate functions are affine and the permutation is bijective. The base block is carried to a block with an affine mask, giving EA equivalence. This proves the criterion without requiring an isomorphism to preserve the original translation action.

The preprint of Wu, Wang and Hyun already constructs nonquadratic families with classical symplectic translation designs using special commutative algebras. The classification here derives the algebra and its invariant form from every minimum-rank example, and allows arbitrary such algebras. [Wu, Wang and Hyun](https://arxiv.org/abs/2609.13968)

## 4. A negative answer for the direct plateaued extension of Theorem 6

**Statement.** For every \(r\ge1\) there is a balanced \(r\)-plateaued Boolean function with no nonzero linear structures for which its support \(D_f\) admits no nontrivial 2-design whose blocks are restrictions to \(D_f\) of affine hyperplanes. This holds even if the construction may discard labels, choose either sign for each label, and repeat blocks. It rules out a universal extension of the point set and affine blocks of Theorem 6 in [Hyun, Kwon, Wang and Wu, Open Problem 5](https://arxiv.org/html/2605.24355v1#S6.SS2). The wording of that problem also permits looking for more loosely analogous constructions using different point sets or block types. The argument here addresses the direct extension. The Walsh-support and rank perspective comes from the MathProofs plateaued design work, but the Fourier obstruction below uses the exact 2-design equations.

Let \(f\) be balanced with no nonzero linear structures, on \(V=\mathbb F_2^m\). Put \(D=\{v:f(v)=1\}\), so \(|D|=2^{m-1}\). Every nonzero \(d\in V\) is a difference of distinct points of \(D\). Otherwise \(D\) and \(D+d\) would be disjoint and, by size, complements. This would make \(f(v+d)+f(v)=1\) identically.

Suppose a nonempty multiset of blocks of common size strictly between 0 and \(|D|\) is a 2-design, with each block given on \(D\) by \(b\cdot v+s=1\). For each \(b\) let \(M(b)\) count blocks carrying that frequency, with both offsets counted. Frequencies for \(b=0\) are forbidden by the block-size condition. For distinct points \(v,w\), the signed row inner product in the incidence matrix is \(N-4R+4\lambda\), where \(N\) is the number of blocks and \(R\) is the number through one point. On the other hand that inner product is
\[
\sum_{b\in V} M(b)(-1)^{b\cdot(v+w)}.
\]
It is therefore the same at every nonzero \(v+w\in V\). Fourier inversion forces \(M(b)\) to be constant for all nonzero \(b\), hence positive since the design has a block.

For nonzero \(b\), the magnitude of the signed sum \(\big|\sum_{v\in D}(-1)^{b\cdot v}\big|\) equals \(|W_f(b)|/2\). An affine block in that direction has size \(|D|/2\) when \(W_f(b)=0\), and either \(|D|/2+|W_f(b)|/4\) or \(|D|/2-|W_f(b)|/4\) otherwise. An \(r\)-plateaued balanced \(f\) with \(1<|\operatorname{supp}W_f|<2^m-1\) has both kinds of nonzero direction. The forced use of all nonzero directions contradicts the common block size.

For explicit examples take
\[
g(x)=x_1x_3+x_2x_4+x_1x_2x_5+x_5
\quad\text{on }\mathbb F_2^5.
\]
Summing over \(x_3,x_4,x_5\) gives Walsh magnitude \(8\) precisely on \(b_5=1+b_3b_4\), and zero elsewhere. This support excludes zero and affinely spans \(\mathbb F_2^5\). To see the latter, any affine equation on the support would, on substitution, give an identically zero multilinear polynomial in \(b_1,b_2,b_3,b_4\), which forces all coefficients to vanish. A constant derivative in a nonzero direction would put the Walsh support in an affine hyperplane, by translating the Walsh sum. Thus \(g\) is balanced and has no such derivative. The sum of \(r\) copies on disjoint variables has Walsh transform given by a product, hence has the same two properties and is \(r\)-plateaued. Its support size \(2^{4r}\) satisfies the required strict inequalities.
