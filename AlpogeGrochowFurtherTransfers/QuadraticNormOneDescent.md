# Quadratic norm-one descent for linked cubic tensor isomorphism

The previous quadratic norm transfer applies when all nonzero Smith invariants of the cubic incidence matrix equal one. Here the incidence matrix may have arbitrary Smith invariants. The exact obstruction to gluing local unitary tensor transporters over a fixed centroid identification is a direct sum of explicit binary obstructions. Each is attached to one incidence invariant and one centroid field. The criterion gives a Hasse principle for every incidence matrix with Smith invariants indivisible by eight. A concrete nonsplit example gives arbitrarily many independent failures once that divisibility condition is dropped.

The connection to the Lean Riemann release is **GlobalTheory.QNorm.hasseNormSt**, the quadratic Hasse norm theorem, in **Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HasseNormTheoremQuadraticExtension.lean**. Its archive member has SHA-256 **8827a27b05bb7d6cf8537685d426f48868814764c7aabfc74b5d2b63e4b32895**. We use it first to assemble local norms into global preimages and again to prove that every surviving cohomology class is realized by a genuine norm-one tensor coefficient. The result is an algebraic and arithmetic transfer with no analytic zero-distribution hypothesis. [Release announcement](https://alpo.ge/remark.pdf) · [Release import of the quadratic Hasse norm theorem](https://raw.githubusercontent.com/CocoSgt/riemann-hypothesis-lean/main/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean)

## 1. Statement

Let $B$ be a number field and $C/B$ a quadratic étale algebra, with conjugation $x\mapsto\bar x$. Write $T=\operatorname{Res}^{1}_{C/B}\mathbf G_m$ for the norm-one torus. For example, $T(B)=\{x\in C^\times:x\bar x=1\}$. Let $\epsilon$ be the quadratic character of $C/B$, with $\epsilon=1$ in the split case. For $e\geq 1$, let $\chi_{2^e}$ be the cyclotomic character on the $2^e$-th roots of unity. Define $\Gamma_e$ as the image of $\chi_{2^e}\epsilon$ in $(\mathbf Z/2^e)^\times$ and $\Gamma_{e,v}$ as the image of the corresponding local Galois group at the place $v$ of $B$. These images are independent of the choices of local embeddings since the target group is abelian.

**Theorem 1.** For a positive integer $d$, let
$$
\mathcal K_d(B,C)=\ker\left(T(B)/T(B)^d\longrightarrow
                      \prod_v T(B_v)/T(B_v)^d\right).
$$
If $e=v_2(d)$ is less than three, this group vanishes. Otherwise it is a group of order two exactly when $\Gamma_e$ is noncyclic and $\Gamma_{e,v}$ is proper in $\Gamma_e$ at every place $v$. It vanishes in every other case. For testing the properness condition when $\Gamma_e$ is noncyclic, it suffices to inspect finite places over $2$ or ramified in $C/B$.

When the group has order two, one can compute its bit using an actual geometric $2^e$-root and two elements of $\Gamma_e$. Write $\Gamma_e=\langle-1,b\rangle$ with $b=1+2^q$ for some $2\le q<e$. In additive coordinates on $T[2^e]$, the resulting cocycle may be normalized to take value zero at $-1$. Its value at $b$ is then either $0$ or $2^{e-1}$, independently of the normalization. These values are the two obstruction classes.

**Theorem 2.** Consider a connected system of Hermitian forms and cubic trace tensors as in Section 4, with arbitrary repetitions of modes. Let $d_1,\ldots,d_r$ be the positive Smith invariants of its incidence matrix. For each specified centroid identification, global transport is equivalent to the existence of local transport at every completion inducing that identification together with the vanishing of the explicitly computable classes
$$
\mathcal K_{d_j}(B,C)
\qquad
(1\le j\le r,\ B\text{ a target centroid field},\ C=B\otimes_F K).
$$
Each indicated class is determined by a Smith-transformed tensor coefficient and its specified norm. Every tuple of surviving bits can be realized by choosing tensor coefficients while keeping the Hermitian forms fixed and identical on the two systems. Without a specified global centroid identification, exact transport reduces to perfect matching of centroid fields, with independently tested edges. Under the intrinsic generation criterion in Section 6 the local identifications necessarily come from a unique global one, so vanishing of the indicated bits is sufficient for unmarked descent.

## 2. Cohomology and the finite action

We use continuous cohomology over the absolute Galois group. Over a separable closure of $B$, the algebra $C$ has two factors and a norm-one element is $(u,u^{-1})$. The factors are swapped by the automorphisms with $\epsilon=-1$. Consequently $T[d]$ is the additive module $\mathbf Z/d$ with Galois action by $\theta_d=\chi_d\epsilon$. This also follows immediately in the split case. Both norm and multiplication by $d$ are surjective on geometric points.

Hilbert's Theorem 90 applied on the two factors by restriction of scalars identifies $H^1(B,T)$ with $B^\times/N(C^\times)$, and identifies the local groups with the corresponding local norm quotients. The released quadratic norm theorem gives the injection
$$
H^1(B,T)\longrightarrow\prod_v H^1(B_v,T).
$$
For a quadratic field extension it is the local-to-global theorem for $x^2-\delta y^2$ when $C=B(\sqrt{\delta})$. For a split algebra the global norm is already surjective. Thus the Kummer sequence for multiplication by $d$ identifies $\mathcal K_d(B,C)$ with
$$
\ker\left(H^1(B,T[d])\longrightarrow\prod_v H^1(B_v,T[d])\right).      \tag{1}
$$
Indeed a class in this latter kernel has globally trivial image in $H^1(B,T)$ by the injection. Exactness then supplies an element of $T(B)/T(B)^d$ with that class. Local Kummer maps are injective, giving local divisibility of this element. This proves surjectivity as well as injectivity of the correspondence.

Let $A_d=\mathbf Z/d$ with this action and let $\Gamma=\operatorname{im}\theta_d$. For the finite-group calculation below, it is useful to describe (1) directly. Choose a continuous cocycle $f$ representing a class in (1). The map $\sigma\mapsto(f(\sigma),\theta_d(\sigma))$ to the finite semidirect product $A_d\rtimes\Gamma$ is a homomorphism, so $f$ and the action factor through a finite Galois quotient $J$. For every $g\in J$, Chebotarev gives an unramified Frobenius conjugate to $g$. Local triviality shows that $f(g)\in(g-1)A_d$. The property is invariant under conjugation because a restriction to one cyclic group is principal if and only if its conjugate restriction is principal. Equivalently, it says that the affine map $x\mapsto gx+f(g)$ has a fixed point, and conjugacy preserves this condition.

If $g$ acts trivially on $A_d$, this inclusion gives $f(g)=0$. Hence $f$ factors through the image $\Gamma$ and its restriction to every cyclic subgroup of $\Gamma$ is a coboundary. Restricting the inflated cocycle to a local Galois group is principal exactly when its restriction to the image $\Gamma_v$ is principal, since the action and the cocycle are both inflated. Also a cocycle on $\Gamma$ inflates to a global coboundary only if it was already principal, by surjectivity onto $\Gamma$. We have therefore obtained the exact finite description of (1) as the cyclically trivial classes on $\Gamma$ whose restriction to each actual decomposition image is trivial. This is the usual local cohomology reduction, with the local images retained to distinguish all-place solvability from solvability outside a finite set. [Dvornicich and Zannier, local–global divisibility](https://www.numdam.org/item/?id=BSMF_2001__129_3_317_0/)

We can do this calculation on each prime power $p^a\parallel d$ separately. The module splits canonically into its primary submodules and localization commutes with the resulting finite products. On the level of torus elements, the natural map $T(B)/T(B)^d\to\prod_{p^a\parallel d}T(B)/T(B)^{p^a}$ is an isomorphism by Bézout and the Chinese remainder theorem for abelian groups. The same is true locally. In particular it suffices to apply the preceding argument separately to the image of each primary action, even if the full image of $\theta_d$ is large and noncyclic.

## 3. Exact finite calculation

If $d$ is an odd prime power, $(\mathbf Z/d)^\times$ is cyclic. The units for $d=2$ and $d=4$ are cyclic as well. When the whole image $\Gamma$ is cyclic, cyclic triviality makes a class principal on all of $\Gamma$, proving vanishing.

For $d=2^e$ with $e\geq 3$, the unit group is $\langle-1\rangle\times(1+4\mathbf Z/2^e)$. The second factor is cyclic. One elementary verification is that $v_2(5^{2^j}-1)=2+j$ for $j\geq0$, by induction on $j$ after factoring $5^{2^{j+1}}-1$. Thus $5$ generates the full subgroup of units congruent to one modulo four. A subgroup that omits $-1$ injects into this cyclic factor, so it is cyclic. Every noncyclic subgroup consequently contains $-1$ and decomposes as the direct product of it with a nontrivial subgroup of the second factor. Such a subgroup is $\langle b\rangle$, $b=1+2^q$, for some $2\le q<e$. To see this, the unique subgroup of its size consists of the units congruent to one modulo $2^q$. The element $1+2^q$ generates it by the same valuation induction.

Take $A_d=\mathbf Z/2^e$. Cyclic triviality at $-1$ gives $f(-1)\in2A_d$, so subtract a principal cocycle and normalize $f(-1)=0$. Commutation gives
$$
-f(b)=f((-1)b)=f(b(-1))=f(b),
$$
hence $f(b)$ is zero or $2^{e-1}$. Changing the normalization adds a principal cocycle by an element killed by $2$. Since $b$ is odd, that change contributes zero at $b$. The exceptional choice is realized by the cocycle
$$
f_*((-1)^i b^j)=j\,2^{e-1}\pmod{2^e}.
$$
The formula is well-defined since $b$ has even order. It is a cocycle because the image is killed by two and all odd units fix it. To check cyclic triviality, consider any element $(-1)^i b^j$. When $j$ is even the value is zero. When $j$ is odd and $i=0$, the valuation of $b^j-1$ is $q$, since $(b^j-1)/(b-1)$ is odd. When $j$ is odd and $i=1$, the valuation of $-b^j-1$ is one since $b^j\equiv 1\pmod4$. In both cases the image of multiplication by $(-1)^i b^j-1$ contains $2^{e-1}$. So $f_*$ is principal on each cyclic subgroup. It is nonprincipal on $\Gamma$ by the normalization argument.

Finally, any proper subgroup $D<\Gamma$ which omits $-1$ is cyclic. If $D$ contains $-1$, its projection to $\langle b\rangle$ is proper, so all projected powers $b^j$ have even $j$ and $f_*|_D=0$. Thus the exceptional class survives precisely when every $\Gamma_v$ is proper. The character defining the module splits over the compositum $C B(\zeta_{2^e})$ when $C$ is a field, with just $B(\zeta_{2^e})$ needed in the split case. At finite places outside $2$ and the relative ramification of $C/B$, that compositum is unramified and the local images are cyclic. The real and complex images are also cyclic. This proves the finite place test and all parts of Theorem 1.

An exact cocycle representative can be computed when a locally divisible scalar $z\in T(B)$ is given. Choose a geometric $2^e$-th root $w$ in $T$ and a primitive $2^e$-th root of unity. The values of $f(\sigma)=\sigma(w)/w$ are powers of that primitive root in the first geometric coordinate, with the twisted action already accounted for. Local divisibility implies that these values factor through $\Gamma_e$ by the argument of Section 2. Take lifts of $-1,b$ and subtract a principal cocycle to set the first value to zero. The second value is the bit in Theorem 1. All choices of $w$ change $f$ by a principal cocycle. Thus the bit can be computed in finite algebraic extensions, with no global transporter oracle.

## 4. Descent from linked cubic records

Let $F$ be a number field and $K/F$ quadratic étale. Let $A,A'$ be finite étale $F$-algebras and put $L=A\otimes_F K$ and $L'=A'\otimes_F K$. The nontrivial automorphism of $K/F$ induces conjugation on these algebras. The modes are indexed by $1,\ldots,s$. On each $K$-module $L$ use a nonsingular Hermitian form $h_i(x,y)=\operatorname{Tr}_{L/K}(b_i x\bar y)$ with $b_i\in A^\times$. Each tensor record $\ell$ has three ordered mode occurrences $(i_{\ell,1},i_{\ell,2},i_{\ell,3})$ and value
$$
T_\ell(x_1,x_2,x_3)=\operatorname{Tr}_{L/K}(t_\ell x_1 x_2 x_3)
\qquad(t_\ell\in L^\times).
$$
The target has the analogous forms and tensor weights $b'_i,t'_\ell$. Mode labels and record labels are retained, with the same linear map on all occurrences of a mode. Require every mode to occur and the mode-record incidence graph to be connected. The integer matrix $M$ has entry $M_{\ell i}$ equal to the number of occurrences of $i$ in record $\ell$.

For a cubic record, the centroid consists of triples of equal scalar multiplications from $L$. In fact, moving an endomorphism from the first to the second slot and varying the third slot yields $(C_1x)y=x(C_2y)$, by the perfect étale trace pairing and invertibility of $t_\ell$. Taking $x=1$ and $y=1$ recovers a common scalar. Comparing against the third slot gives the same scalar there. This uses the three tensor arguments independently, including for repeated mode labels. A tensor transporter therefore conjugates the scalar actions to each other via a $K$-algebra isomorphism. At two records sharing a mode the induced isomorphisms agree, since the scalar operator on that mode determines its scalar. Connectedness gives a single identification $\sigma:L\longrightarrow L'$. Every transporter has form $g_i(x)=u_i\sigma(x)$ with $u_i=g_i(1)\in(L')^\times$.

The adjoint of multiplication by $a$ for $h_i$ is multiplication by $\bar a$. The unitary condition makes $\sigma$ preserve this involution, hence makes it arise from an $F$-algebra isomorphism $A\longrightarrow A'$. Conversely any such isomorphism extends by the identity on $K$. These arguments work over the ground field and all its completions. The perfect trace is also the algebraic input of the release's **traceGram_det_ne_zero**, in **CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean**, archive SHA-256 **5da8355bcf4a434b8db6a3035e2a70249c52c71ce6acc831be1cd80504e3a112**.

Fix $\sigma$ and project to one target field factor $B$ with $C=B\otimes_F K$. Put $a_i=\sigma(b_i)/b'_i\in B^\times$ and $z_\ell=\sigma(t_\ell)/t'_\ell\in C^\times$ on this component. Perfect trace and the transporter equations give precisely
$$
N(u_i)=a_i,\qquad \prod_i u_i^{M_{\ell i}}=z_\ell.                  \tag{2}
$$
For example, composing the target trace tensor by the $g_i$ changes its coefficient by the product of $u_i$ in that row. Composing the target Hermitian form changes its coefficient by $u_i\bar u_i$. The inverse implication follows by substitution in the traces.

Take integer unimodular $P,Q$ with $PMQ=\operatorname{diag}(d_1,\ldots,d_r,0)$. Set $u_i=\prod_j w_j^{Q_{ij}}$, $\widetilde a_j=\prod_i a_i^{(Q^{-1})_{ji}}$ and $\widetilde z_\ell=\prod_k z_k^{P_{\ell k}}$. These are invertible transformations on the multiplicative coordinate groups, so (2) is exactly the independent system
$$
N(w_j)=\widetilde a_j\quad(1\le j\le s),\qquad
w_j^{d_j}=\widetilde z_j\quad(1\le j\le r),\qquad
\widetilde z_\ell=1\quad(\ell>r).                                  \tag{3}
$$

If (3) is locally soluble everywhere, the row identities hold globally by injectivity into a completion. Every $\widetilde a_j$ is a local norm everywhere, hence has a global norm preimage $w_{0,j}$ by **hasseNormSt**. For each constrained index $j$, local solvability gives $N(\widetilde z_j)=\widetilde a_j^{d_j}$ globally. Consequently
$$
\eta_j=\widetilde z_j/w_{0,j}^{d_j}\in T(B).
$$
Dividing a local witness by the base change of $w_{0,j}$ proves $\eta_j\in T(B_v)^{d_j}$ at every place. Its coset is independent of the chosen global preimage, since any two norm preimages differ by an element of $T(B)$. Equation (3) is now globally soluble precisely when all the classes of $\eta_j$ in Theorem 1 vanish. On the free coordinates take the norm preimages, and on the constrained coordinates take $w_j=w_{0,j}\beta_j$ for explicit norm-one roots $\beta_j^{d_j}=\eta_j$. Returning through $Q$ gives the genuine transporter. This proves the fixed-identification criterion in Theorem 2.

When a transporter for an identification exists, all its choices in one field factor form a torsor for
$$
T(B)^{\,s-r}\ \times\ \prod_{j=1}^r T(B)[d_j].
$$
Here $T(B)[d_j]$ denotes the points killed by the $d_j$-th power map, and the same formula gives the scalar part of the stabilizer on that factor. The direct products across field factors give the full set of choices for the fixed identification.

There is no dependency among the indicated bits after the Smith transformation. For any prescribed tuple, choose a representative of each indicated class in $T(B)$ by (1), keeping all $a_i=1$. Set $\widetilde z_j$ equal to those representatives, using $1$ for zero classes and zero rows. Undo the unimodular row change. All weights remain units and have norm one. We obtain two trace systems on the same algebra with identical forms and everywhere local transport inducing the identity, with exactly the selected tuple as obstruction.

## 5. Exact tests and centroid matching

The formulas also give a decision procedure for any particular candidate identification, without first knowing local solubility. Check the zero rows in (3), the norm compatibility $N(\widetilde z_j)=\widetilde a_j^{d_j}$ for every constrained index, and the norm membership of all $\widetilde a_j$. Norm membership is equivalent to its tests at the real places and the finite places dividing the relative discriminant or the numerator or denominator ideals of the norm requests. At unramified finite places away from this support, the request is an integral unit and the norm of units is surjective. For a split algebra all requests are norms. The released norm theorem assembles the check into global preimages. Once these checks pass the remaining test is divisibility of the explicit $\eta_j$. It can be decided by factoring $X^{d_j}-\eta_j$ over $C$ and retaining roots with norm one. For split $C$, use its two field factors and the product norm. A successful root test together with norm-form solutions reconstructs the mode maps by (3).

One can also test the all-place premise by finite computation. For each explicit $\eta_j\in T(B)$, the geometric $d_j$-th roots in $T$ form a finite Galois set. Over its splitting field it can be computed by adjoining the roots, with the appropriate swap of coordinates when a Galois element conjugates $C$. At ramified finite places and infinite places, test for a fixed point of the local decomposition group on this set. At all other places, test whether every element of the finite Galois group fixes some geometric root. Indeed the local decomposition image is then generated by a Frobenius element, and every conjugacy class occurs at an unramified place by Chebotarev. This gives a finite criterion without enumerating infinitely many prime places. These procedures are exact arithmetic statements. The degree of the root polynomials can grow with the Smith invariants, so this gives no general polynomial bit bound.

For arbitrary global identifications, form the bipartite graph of field factors of $A,A'$. For every candidate $F$-field isomorphism, run the independent tests above on its target factor and retain the isomorphism as an edge label if successful. Every global unitary transporter supplies a perfect matching, since the induced centroid isomorphism permutes primitive factors. Conversely choose an isomorphism on each edge of a perfect matching and assemble the computed scale factors on disjoint field factors. Trace is the sum of factor traces, so the blockwise witness gives a transporter of all original arrays.

The same argument can start from raw promised trace arrays. Compute the centroid of each cubic tensor by linear equations in the three endomorphism slots. Project to each mode and propagate identifications along the connected incidence graph. Recover the involution from Hermitian adjoint. The centroid acts freely of rank one on each mode, so it suffices to choose one nonzero vector per simple component and sum these vectors to obtain a module frame. In those coordinates, read $b_i$ and $t_\ell$ by the perfect trace pairing against the form and tensor with all other arguments equal to the corresponding frame vectors. Checking the recovered identities with the original arrays verifies the presentation. The perfect matching and arithmetic tests then apply. This recovery works over the split quadratic base by componentwise operations.

## 6. An intrinsic criterion for the unmarked Hasse principle

For the raw models above, the following invariants constrain every centroid isomorphism. For each row take
$$
q_\ell=\frac{N(t_\ell)}{\prod_i b_i^{M_{\ell i}}}\in A^\times.
$$
For each basis element $\lambda$ of the integral kernel of $M^{\mathsf T}$, take the two $A$-coordinates of $\prod_\ell t_\ell^{\lambda_\ell}$ relative to one chosen $F$-basis of $K$. Such a basis of relations suffices since the remaining invariants are products of powers. The formula for $q_\ell$ is invariant under changing each module frame since the form and each tensor occurrence contribute equal powers of its norm. For a relation, the tensor-frame scale factors cancel because $\lambda^{\mathsf T}M=0$. For any unitary transporter these invariants therefore map to the corresponding target entries, by taking norms and row dependencies in (2).

If these entries generate $A$ as an $F$-algebra and the corresponding entries generate $A'$, local transport at every completion determines one global centroid isomorphism $\sigma$. In detail, the two evaluation maps from a polynomial algebra over $F$ sending the variables to the ordered invariants are surjective. Their kernels agree because any relation can be tested after extending to one completion with a local transporter, and extension of scalars on a finite-dimensional vector space is injective on elements. The two quotients identify uniquely with the required invariants, and at any other place local maps equal the base change of this identification by generation. Now Theorem 2 applies. In particular, for this unmarked family with every Smith invariant indivisible by eight, everywhere local unitary isomorphism implies global unitary isomorphism.

## 7. Explicit nonsplit examples and arbitrarily many bits

Let $B=\mathbf Q(\sqrt7)$ and $C=B(\sqrt{17})$. It is a quadratic field extension. Put $v=(5+\sqrt{17})/4$. Then $N(v)=1/2$. Fix $e\geq3$ and define
$$
\eta_e=2^{2^{e-1}}v^{2^e}\in T(B).
$$
Its norm is one because the norm of the rational coefficient is its square. A geometric $2^e$-root in the first coordinate is $w=\sqrt2\,v$.

The intersection of $C$ and $\mathbf Q(\zeta_{2^e})$ is $\mathbf Q$. The three quadratic subfields of the biquadratic $C$ have radicands $7,17,119$. The only quadratic subfields of the $2^e$-cyclotomic field have radicands $-1,2,-2$, by the structure of its Galois group and the visible roots in $\mathbf Q(\zeta_8)$. A nontrivial intersection with the biquadratic field would contain one of its quadratic subfields. It follows that the cyclotomic action over $B$ is surjective even on the subgroup fixing $C$, hence the twisted image is the full unit group $\Gamma_e$.

At places over $2$, the algebra $C$ splits because $17$ is a square in $\mathbf Q_2$. Also $B$ contains $i$ locally because $-7$ is a square in $\mathbf Q_2$. These square assertions follow from the unit criterion for squares modulo eight. Thus the cyclotomic image there fixes $i$ and is proper. At places over $17$, the cyclotomic part is unramified and its Frobenius is a power of $17$, so lies in the subgroup congruent to one modulo $16$. Multiplication by $\epsilon$ yields only units congruent to $\pm1$ modulo eight, a proper subgroup. At other finite places the compositum is unramified relative to $B$, hence the local image is cyclic. Every infinite local image is cyclic. This proves that the exceptional class survives for every $e\geq3$ over this same nonsplit quadratic extension.

To verify that $\eta_e$ represents it, write $s(\sigma)\in\{1,-1\}$ for the ordinary Galois sign on $\sqrt2$. In the first geometric coordinate, when $\epsilon(\sigma)=1$ we have $\sigma(w)/w=s(\sigma)$. When $\epsilon(\sigma)=-1$ the twisted action inverts the conjugate of $w$ and the ratio is $s(\sigma)/(2v\bar v)=s(\sigma)$. The sign on $\sqrt2=\zeta_8+\zeta_8^{-1}$ depends only on the cyclotomic unit modulo sign, and thus equally on the twisted unit. It is positive on $-1$ and negative on $5$. The cocycle is exactly the nonprincipal class of Section 3, with $q=2$. It is principal at every actual local image, so $\eta_e$ is locally a $2^e$-th power in the norm-one torus. It is globally no $2^e$-th power even in $C^\times$. If such a root existed, its ratio to $v$ would lie in $C\cap\mathbf Q(\zeta_{2^e})=\mathbf Q$ because all roots of $X^{2^e}-2^{2^{e-1}}$ are $\sqrt2$ times roots of unity in the cyclotomic field. Its rational $2$-valuation would have to be $1/2$. The split $e=3$ specialization is the familiar Grunwald–Wang example over $\mathbf Q(\sqrt7)$. The norm-one element above makes the obstruction occur in a nonsplit quadratic unitary problem. [Conrad, Appendix A and the split example](https://virtualmath1.stanford.edu/~conrad/papers/locchar.pdf)

We now realize the obstruction by cubic arrays with repeated modes and scalar Hermitian spaces. Set $F=B$, $K=C$, $A=A'=B$. Give all modes the same one-dimensional Hermitian form $x\bar y$. Use mode $0$ and modes $1,\ldots,e$, with rows
$$
3\mathbf e_0,\quad 2\mathbf e_1+\mathbf e_2,\quad
     2\mathbf e_2+\mathbf e_3,\quad\ldots,\quad
     2\mathbf e_{e-1}+\mathbf e_e,\quad 2\mathbf e_e+\mathbf e_0.
$$
All tensor weights are one except the source weight in the last row, set to $\eta_e$. The rows are realizable as ordered triples, and the incidence graph is connected. The equations force $u_0^3=1$, $u_{i+1}=u_i^{-2}$ and $u_e^2 u_0=\eta_e$ with every $u_i$ norm one. Since raising to $2^e$ is a bijection on elements killed by $3$, a global solution is equivalent to $\eta_e$ being a global $2^e$-th power in the norm-one group, with the parity of $e$ absorbed by inversion. Locally set $u_0=1$ and use the local roots just proved. The centroid here has only the identity as an $F$-identification, so this is an unmarked example of local but globally nonisomorphic cubic systems. The Smith cokernel is cyclic of order $3\cdot2^e$. To see this, successive chain relations express every $\mathbf e_i$ in terms of $\mathbf e_1$, the last relation expresses $\mathbf e_0$ in terms of it, and the remaining relation is multiplication by $3\cdot2^e$.

More generally take $m$ parallel chains through the same mode $0$ with the same terminal rows, one per chain. After eliminating the internal generators, there is a common generator for the first chain, subject to multiplication by $3\cdot2^e$. The differences between each remaining chain's generator and the first are independently killed by $2^e$. Thus the Smith cokernel is $\mathbf Z/(3\cdot2^e)\oplus(\mathbf Z/2^e)^{m-1}$. Assign terminal weights independently from $\{1,\eta_e\}$ in the $m$ chains. Every assignment yields local transport. Comparing any two distinct assignments gives a ratio $\eta_e$ or $\eta_e^{-1}$ at some terminal row, which obstructs global transport on that chain even after choosing $u_0$. This realizes $2^m$ distinct global orbits with the same local orbit throughout one connected family.

The results above are written mathematical proofs. The claims concern quadratic étale cubic trace systems with connected incidence and unit weights.
