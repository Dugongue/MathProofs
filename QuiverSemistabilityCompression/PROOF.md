# P019 — Exact binary-input compression for generic quiver semistability

Informal proof document. Universal binary-input polynomial time is NOT proved.

0. Exact question and status
Input: a finite acyclic quiver Q with its arrow list, alpha in N^vertices, sigma in Z^vertices; every alpha and sigma entry is encoded in binary. Work over C. The action on polynomial functions is contragredient: (g.f)(V)=f(g^{-1}.V); semi-invariant weights use this convention. Does there exist a sigma-semistable representation of dimension alpha? Convention: sigma(alpha)=0 and sigma(dim W)<=0 for every subrepresentation W.

Iwamasa–Oki–Soma, ICALP 2025 Section 1.7, explicitly lists generic semistability as open. Vergne–Walter 2023 Section 4 identifies the encoding issue precisely: their Section 3 glued-hive linear program is already sufficient for arbitrary acyclic Q with expanded/unary dimensions and binary weights. It is not polynomial in binary alpha. No later universal closure was found in the bounded current search. This distinction prevents attributing an old unary theorem to our work.

We prove two exact sufficient algorithmic results: an adaptive all-input algorithm whose numeric dimension dependence uses the smaller of two primitive reciprocal cores, and a complete elementary polynomial-bit algorithm for every two-vertex acyclic quiver. These are deductions from classical results (the rank-two classification is classical); novelty is unverified and no open-problem closure is claimed.

1. Classical ingredients, used with exact scope
(1) King: existence of a sigma-semistable representation of dimension alpha is equivalent to existence of a nonzero semi-invariant of some positive multiple of sigma. The acyclic quiver saturation theorem removes the multiple.
(2) Derksen–Weyman/Schofield spanning: the semi-invariants on Rep(Q,alpha) are spanned by determinantal functions c^W, of weight -<.,beta> for beta=dim W. When alpha is sincere, the Euler map beta -> -<.,beta> is injective, since the acyclic Euler matrix is unimodular, and a nonzero weight space forces that unique beta to be nonnegative.
(3) Reciprocity: if <a,b>=0, then
 h(a,b):=dim SI(Q,a)_{-<.,b>} = dim SI(Q,b)_{<a,.>}.
The determinant of the Hom-to-arrow Hom map gives the two semi-invariants; the equality of dimensions is the classical reciprocity theorem. We use positivity, not an unproved equality of individual witnesses.
(4) Saturation holds for the weight semigroup at every fixed dimension vector: if SI(Q,a)_{k tau} is nonzero for an integer k>0, then SI(Q,a)_tau is nonzero.
(5) Vergne–Walter Theorem 1 / Corollary 2 gives an explicitly constructible combinatorial hive LP for multiplicity positivity. Its number of scalar variables and inequalities is polynomial in the actual expanded dimensions and |Q|; its coefficients are 0,1,-1. Binary weights affect right-hand sides only. Tardos yields strongly polynomial arithmetic complexity, with ordinary bit complexity polynomial in expanded dimension and the bit lengths of the right-hand sides.

2. Reciprocal primitive-core theorem
For all acyclic Q, there is a deterministic exact algorithm for the root decision taking time polynomial in L+kappa, where L is the ordinary binary input length, and kappa is computed as follows. Remove vertices of zero alpha and their incident arrows; discard their irrelevant weights. If alpha is identically zero or the remaining sigma is zero, return YES. If sigma(alpha) differs from zero, return NO. Now alpha is sincere.

Let E be the Euler matrix, <u,v>=sum_x u_x v_x - sum_{a:x->y} u_x v_y. Solve E beta = -sigma. This uses backwards topological substitution:
 beta_x = sum_{a:x->y} beta_y - sigma_x.
If beta has a negative entry, return NO by ingredient (2). Otherwise beta is nonzero and <alpha,beta>=-sigma(alpha)=0.

Write a=alpha/gcd(alpha_x), b=beta/gcd(beta_x), with gcd taken over nonzero entries. Then
 kappa=min(sum_x a_x, sum_x b_x).
The answer is exactly whether h(a,b)>0.

Proof of the two primitive divisions. For every k>0,
 h(a,kb)>0 iff h(a,b)>0
by fixed-dimension weight saturation on a. Also
 h(ka,b)>0 iff dim SI(Q,b)_{k<a,.>}>0 iff dim SI(Q,b)_{<a,.>}>0 iff h(a,b)>0,
by reciprocity, fixed-dimension saturation on b, and reciprocity back. These are independent equivalences, so dividing both gcds is valid. This is not justified by incorrectly taking a direct summand of an arbitrary semistable representation.

If sum a<=sum b, construct the hive LP for dimension a and weight -<.,b>. Otherwise use dimension b and reciprocal weight <a,.>. Zero coordinates of the chosen dimension are removed before construction, without changing the representation space or character. Ingredient (5) decides positivity exactly.

Bit-size proof. In a topological ordering E is unitriangular. Its inverse entries count directed paths with signs fixed by the inverse expansion, so their bit sizes are O(|vertices| log(1+|arrows|)). Thus every beta entry has polynomial input bit length, even if its numeric value is exponential. Gcd and integer Euler transformations take polynomial bit time. The selected LP has polynomially many variables and inequalities in |Q|+kappa; right-hand-side bit length is polynomial in L. This proves the stated total running-time bound. In particular it is a polynomial-bit algorithm on every family with kappa bounded by a polynomial in L, without ever expanding the other possibly enormous dimension vector.

This does not prove kappa polynomial for all inputs. For the three-arrow Kronecker quiver take alpha=(N,N+1), beta=(2N-1,N), sigma=(N+1,-N). Both alpha and beta are primitive, <alpha,beta>=0, and their norms are Theta(N) while input length is O(log N). Section 3 below solves this particular rank-two family by a different exact argument. It cannot certify that larger wild-quiver cores are small.

3. Full binary decision for every two-vertex acyclic quiver
After zero-support handling, write the quiver as m parallel arrows 1->2, alpha=(a,b) with a,b>0. If sigma=0 return YES. Otherwise balance forces sigma to be a real nonzero multiple of (b,-a). If that multiple is negative, return NO: a nonzero sink simple is a destabilizing subrepresentation. For a positive multiple put g=gcd(a,b), A=a/g, B=b/g. Then the answer is exactly
 A^2+B^2-m A B <= 1.
The operations are integer gcd, products, subtraction and comparison on polynomial-bit integers. The number m is given by the arrow list; no representation matrices of size a or b are constructed.

3a. Necessity, without invoking a classification of roots.
A semistable representation has a Jordan–Holder filtration in its zero-slope semistable category. Every stable factor has dimension (u,v) with bu-av=0; hence (u,v)=t(A,B), t a positive integer. A stable factor has scalar endomorphisms over C: a nonzero noninvertible endomorphism would yield proper kernel/image of zero slope; stability excludes that, and over an algebraically closed field every endomorphism has an eigenvalue. For the hereditary quiver Hom/Ext complex,
 dim End(M)-dim Ext^1(M,M)=q(dim M), q(u,v)=u^2+v^2-muv.
Consequently t^2 q(A,B)=1-dim Ext^1(M,M)<=1, so the integer q(A,B)<=1.

3b. Sufficiency by a direct incidence dimension count.
Assume q(A,B)<=1. We show a generic m-tuple of B-by-A matrices is stable for weight (B,-A). For possible subspaces U subset C^A, W subset C^B of dimensions u,w with B u-A w>0, consider the closed incidence variety where every arrow sends U into W. Its base is Gr(u,A) x Gr(w,B). For fixed U,W the constraints on an arrow are u(B-w) independent linear equations; the arrows are independent. Hence its dimension is the ambient representation-space dimension minus
 D=m u(B-w)-u(A-u)-w(B-w).
Set delta=B u-A w, z=B-w, q=q(A,B). Then direct expansion gives
 A B D=delta(Au+Bz)-q u z.
For a destabilizing pair, delta>=1, u>=1 and z>=1. Since q<=1, u<=A and z<=B,
 A B D >= Au+Bz-uz >= u^2+z^2-uz >0.
Thus each destabilizing incidence image has strictly smaller dimension. Projection from the product with the projective Grassmannian base is proper, so the image is closed and proper. There are finitely many integer pairs (u,w). Their union is proper in the irreducible affine representation space, and its complement is nonempty Zariski open. Every point there is semistable; because gcd(A,B)=1, no proper nonzero subrepresentation can have zero slope, so it is stable.
A direct sum of g copies is semistable of dimension (a,b). To see direct-sum preservation directly, for a subrepresentation X of M directsum N intersect with M and project to N; their dimensions add and both weights are nonpositive.

The dimension count establishes mathematical existence only. The actual decision algorithm evaluates q, and never enumerates the potentially exponentially many subspace dimensions. This distinction is essential to the binary running-time claim. The criterion is classical; this elementary derivation is included for a self-contained exact branch, not a novelty assertion.

4. Where the universal source question remains
The two algorithms compose: first use elementary rank-two decisions where applicable, otherwise use the smaller reciprocal primitive-core hive LP. For arbitrary larger acyclic quivers, the proven worst-case bound is still polynomial in a possibly exponential kappa. No compressed-hive theorem, polynomial-time generic-matrix nc-rank oracle, or polynomial-length reflection descent has been proved here. The root claim in Section 0 therefore remains OPEN.

The shared TI/SL work provides exact matrix identities, explicit symbol-level reductions and runtime-composition discipline. It does not turn a binary dimension into a polynomial number of scalar matrix entries. Our source tree has no verified theorem that bridges that quantitative gap; declarations carrying quiver or semistability names cannot be substituted for it.

Primary references
Iwamasa–Oki–Soma: Algorithmic Aspects of Semistability of Quiver Representations, ICALP 2025, Section 1.7 and Theorem 1.1. https://drops.dagstuhl.de/storage/00lipics/lipics-vol334-icalp2025/html/LIPIcs.ICALP.2025.99/LIPIcs.ICALP.2025.99.html
Vergne–Walter: Moment cone membership for quivers in strongly polynomial time (2023), Theorem 1, Corollary 2, and especially Section 4. https://arxiv.org/html/2303.14821
Derksen–Weyman: Semi-invariants of quivers and saturation for Littlewood–Richardson coefficients, JAMS 13 (2000), spanning, reciprocity, saturation. https://www.math.utah.edu/~ptrapa/math-library/knutson/derksen-weyman-quiver-JAMS.pdf
Derksen–Weyman: The Combinatorics of Quiver Representations, Ann. Inst. Fourier 61 (2011), Sections 2–3. https://sites.lsa.umich.edu/hderksen/wp-content/uploads/sites/614/2018/05/A.I.a.36.pdf
