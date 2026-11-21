# Geometry, arithmetic, and descent additions

The inherited constructions are [arithmetic descent and norm compilation](../baseline/DescentAndNorms.md), [diagonal closed orbits](../baseline/earlier/GeometryAndDescent.md), and the [determinantal families](../baseline/earlier/PriorDeterminantalFamilies.md).

Here a signed tensor transporter is a special-linear transporter in every mode. For a bilinear-map tensor \(A:U\times V\to W\), I use the convention \(B(fx,gy)=hA(x,y)\). Passing to the covariant convention dualizes the first two factors and preserves each determinant-one condition. All entries are paper deductions. The earlier atlas supplies the relative-norm compiler, the diagonal closed-orbit calculation and the determinant-pencils construction explicitly invoked below.

<a id="entry-159"></a>

### 159. Every finite algebra norm gives a signed tensor comparison

For a finite-dimensional nonzero commutative unital \(K\)-algebra \(E\) and \(c\in K^\times\), one can construct an ordinary-equivalent pair of \(n\times n\times n\) tensors whose signed equivalence over every extension \(L/K\) holds exactly when \(c\) is a norm of a unit of \(E\otimes_KL\). Only the given multiplication table and \(c,c^{-1}\) are needed. Indeed, for the multiplication tensor \(M_E\), every autotopism has the form \((L_u\sigma,L_v\sigma,L_{uv}\sigma)\), where \(L_u\) denotes multiplication by the unit \(u\) and \(\sigma\) is an algebra automorphism. Set \(u=f(1)\), \(v=g(1)\); the restrictions \(h=L_vf=L_ug\) and the invertibility of \(f,g,h\) force both to be units, and division by \(uv\) makes \(h\) a unital multiplicative map. This proof holds after arbitrary scalar extension. Its determinant tuple is \((a d,b d,ab d)\), with \(a=N(u),b=N(v),d=\det\sigma\). The required correction \((c,1,c)\) forces \(d=1\) by taking the third coordinate divided by the product of the first two. Conversely \((L_u,I,L_u)\) supplies that correction. Define the target by transporting \(M_E\) with diagonal maps of determinants \((c^{-1},1,c^{-1})\). The construction is polynomial in the explicit input size over finite fields and over \(\mathbb Q\).

<a id="entry-160"></a>

### 160. Exact orientation classification of étale multiplication isotopes

For finite étale \(E/K\), write \(N=N_{E/K}(E^\times)\) and \(D=\det(\operatorname{Aut}_K E)\). Two displayed isotopes of \(M_E\), supplied with a rational ordinary transporter, are signed-isomorphic precisely when their required correction \((a,b,h)\) has \(d=ab/h\in D\), \(a/d\in N\), and \(b/d\in N\). This follows from the full determinant formula in [Entry 159](#entry-159). Over a finite field of odd order \(q\), \(N=\mathbb F_q^\times\), and \(D\) contains \(-1\) exactly when either a constituent field has even degree or at least two isomorphic odd-degree constituents occur. A cyclic generator on a degree-\(e\) constituent permutes the \(e\) geometric factors by an \(e\)-cycle, and an exchange of two constituents of degree \(e\) exchanges \(e\) pairs. These generate all automorphisms. In characteristic two \(D=\{1\}\). Thus the number of rational signed orbits inside the ordinary orbit is exactly \((q-1)/|D|\), from the index of the determinant image in \((\mathbb F_q^\times)^3\). This also yields explicit correction witnesses by finite-field norm representatives.

<a id="entry-161"></a>

### 161. Norm twists of nonreduced algebras reduce to weighted residue norms

Let \(E=\prod_i E_i\) be a product of finite local commutative \(K\)-algebras with residue fields \(F_i\), and put \(\ell_i=(\dim_K E_i)/[F_i:K]\). Then the signed comparisons from [Entry 159](#entry-159) test membership in \(\prod_i N_{F_i/K}(F_i^\times)^{\ell_i}\). Filter \(E_i\) by powers of its maximal ideal. Multiplication by \(u_i\) on each successive quotient acts by its residue \(\bar u_i\) on a vector space over \(F_i\). Taking determinants on the filtration gives \(N_{E_i/K}(u_i)=N_{F_i/K}(\bar u_i)^{\ell_i}\). Every nonzero residue lifts to a unit. This proof also applies to the corresponding Artin factors after any base extension.

<a id="entry-162"></a>

### 162. Geometric signed equivalence can require purely inseparable scalar extension

Let \(K\) have characteristic \(p>0\), choose \(c\in K^\times\setminus K^{\times p}\), and take \(E=K[\epsilon]/(\epsilon^p)\). The [Entry 159](#entry-159) tensors have an ordinary \(K\)-transporter and a signed transporter over \(L/K\) if and only if \(c\in L^{\times p}\). The norm is the \(p\)-th power of the constant coefficient by the evident nilpotent filtration. Hence the pair is geometrically signed-equivalent and is signed-equivalent over \(K(\sqrt[p]{c})\) of degree \(p\), and it has no signed transporter over any separable algebraic extension of \(K\). This construction concerns actual tensor instances, including in characteristic two.

<a id="entry-163"></a>

### 163. Hasse principle for cyclic norm twists

Take \(E/K\) cyclic over a number field or global function field. The actual signed tensor pairs in [Entry 159](#entry-159) are signed-equivalent over \(K\) if and only if they are signed-equivalent over all \(K_v\). This is the cyclic Hasse norm theorem, applied to the identical norm condition after base change to every completion, where the extension algebra can be a product. In the number-field case finite primes outside those ramified in \(E\) or dividing the fractional ideal of \(c\) pass automatically by [Entry 166](#entry-166). [Hasse norm theorem and general obstruction in Frei–Loughran–Newton, introduction and Theorem 6.1](https://arxiv.org/pdf/1508.02518)

<a id="entry-164"></a>

### 164. Hasse failure for closed signed tensor orbits in format \(4\times4\times4\)

Take \(E=\mathbb Q(\sqrt{13},\sqrt{17})\). The explicit choice \(c=25\) produces a signed NO over \(\mathbb Q\) and a signed YES over every completion, on the single ordinary orbit in [Entry 159](#entry-159). At \(13\), \(17\) has a square root by Hensel since \(17\equiv4\bmod13\); at \(17\), \(13\) is a square modulo \(17\) because \(8^2\equiv13\). At other finite places the extension is unramified, since its two quadratic subfields have discriminants \(13,17\), and at infinity it is real split. Every decomposition group is cyclic. The kernel in Tate's norm-obstruction theorem is therefore all of \(H^3(C_2^2,\mathbb Z)\cong C_2\), which also proves existence. Browning and Newton specify \(25\) as a representative of its nontrivial class. The tensors lie in the same closed geometric signed orbit because \(E\) is geometrically split and the diagonal three-tensor has closed special-linear orbit as proved in the earlier *Geometry and Descent* chapter. [Entry 159](#entry-159) turns this into a counterexample using the special-linear tensor action itself. [Frei–Loughran–Newton, Theorem 6.1 and Lemma 6.5](https://arxiv.org/pdf/1508.02518), [Browning–Newton, introduction](https://arxiv.org/abs/1411.7775)

<a id="entry-165"></a>

### 165. A finite decomposition-group criterion for abelian norm twists

For a finite abelian number-field extension \(E/K\) with group \(G\), all [Entry 159](#entry-159) twists satisfy the Hasse principle precisely when the images of \(\bigwedge^2 D_v\) generate \(\bigwedge^2 G\), where \(D_v\) ranges over its decomposition groups. The Tate description identifies the obstruction with the dual of the quotient by that image. Unramified and archimedean decomposition groups are cyclic and contribute zero. For biquadratic \(E/K\) it therefore suffices, and is necessary for the whole family, that one decomposition group be all of \(C_2^2\). For example \(\mathbb Q(\sqrt5,\sqrt{13})/\mathbb Q\) gives a positive biquadratic family: at \(5\) the ramified quadratic and the unramified quadratic are distinct, since \(13\equiv3\bmod5\) is a nonsquare. [Frei–Loughran–Newton, Theorem 6.1 and Lemma 6.5](https://arxiv.org/pdf/1508.02518)

<a id="entry-166"></a>

### 166. Direct local norm criterion for tame fields

Let \(E/K\) be a finite tame field extension of complete discretely valued local fields with finite residue field, ramification degree \(e\) and residue degree \(f\). A [Entry 159](#entry-159) twist is a local signed YES precisely when \(v_K(c)=ft\) for some integer \(t\) and the residue of \(c/N(\pi_E)^t\) is an \(e\)-th power in the residue field of \(K\). Here \(\pi_E\) is any uniformizer. The valuation formula for the norm gives the first test. The residue of the norm of a unit is the finite-field residue norm raised to \(e\), by computing the determinant on the \(e\) graded pieces modulo a base uniformizer. Residue norms are surjective. A principal unit is already a norm from \(E\) if \(E/K\) is tame: first take its \(e\)-th root among base principal units by Hensel, then realize that root as a norm from the unramified degree-\(f\) subextension. In the unramified case the norm on principal units is onto by lifting successive graded pieces using surjectivity of the finite-field trace and passing to the complete limit. An unramified extension thus gives exactly the valuation test, even if the residue characteristic divides \(f\).

<a id="entry-167"></a>

### 167. Exact real obstruction for étale multiplication tensors

For a finite étale real algebra \(E=\mathbb R^r\times\mathbb C^s\), [Entry 159](#entry-159) has a signed transporter if and only if either \(r>0\) or \(c>0\). The norm is the product of the real coordinates and squared absolute values of complex coordinates. In particular, over an ordered number-field place the same exact local obstruction applies when all archimedean constituents are complex. This distinguishes the real obstruction from finite-place valuation and ramification restrictions.

<a id="entry-168"></a>

### 168. Weak approximation and the Hasse principle are different signed transporter properties

Let \(E/K\) be biquadratic over a number field. The identity-component transporter for the signed multiplication norm twist has weak approximation over \(K\), whenever nonempty over \(K\), if and only if every decomposition group of \(E/K\) is cyclic. Indeed the determinant-one equation in each of the two unit parameters is a torsor under the norm-one torus \(T\), and the component containing an identity-automorphism solution is a translate of \(T^2\). Its \(K\)-point identifies it with that product. The cited weak approximation criterion for \(T\) is equivalent for \(T^2\). For the [Entry 164](#entry-164) choice of field this component has weak approximation on each soluble twist, although some everywhere locally soluble twists fail globally. For the [Entry 165](#entry-165) biquadratic example every everywhere locally soluble twist passes globally, while the connected component through a rational solution fails weak approximation. [Frei–Loughran–Newton, Lemma 6.7](https://arxiv.org/pdf/1508.02518)

<a id="entry-169"></a>

### 169. A local-global family for products of two norms

For finite separable extensions \(E_1,E_2/K\) of a global field with linearly disjoint Galois closures, \(c\in N_{E_1/K}(E_1^\times)N_{E_2/K}(E_2^\times)\) if and only if it is in the analogous product for every completion of \(K\). This is Pollio–Rapinchuk's multinorm theorem, with no requirement that \(E_i/K\) themselves be Galois. On the supported explicit presentations of the earlier norm-product compiler it gives the same local-global rule for the resulting ordinary three-tensor comparisons. Tensors constructed by that compiler use identical structure constants after completion, so the same list of multiplication identities applies. [Pollio and Rapinchuk, main theorem](https://arxiv.org/abs/1203.0359)

<a id="entry-170"></a>

### 170. Uniform ordinary tensor reduction for Galois number-field norms of arbitrary degree

Suppose \(K\) and \(E/K\) are explicitly presented number fields and \(E=K[\alpha]\) is given by a monic minimal polynomial \(f\) that splits in \(E\). There is a deterministic polynomial bit-time reduction of \(N_{E/K}(u)=c\) to ordinary tensor isomorphism over \(K\). Factor \(f\) over \(E\) by Lenstra's algorithm and use each root to give the embedding of \(E\) into the single supplied-size algebra \(S=E\). In explicit number-field representations the coefficient and root descriptions are polynomial in the input bit length by the factorization theorem. The earlier relative-norm compiler uses these embeddings, so its polynomial bound here has no fixed degree restriction and no factorial splitting-algebra dependence. For tower presentations the claim uses explicit multiplication tables/inclusion maps and a polynomial-size absolute primitive presentation of \(E\). [Lenstra, *Factoring polynomials over algebraic number fields*](https://ir.cwi.nl/pub/2541)

<a id="entry-171"></a>

### 171. Odd prime-degree dihedral norms without a supplied normal closure

Let \(K\) be a number field and \(f\) an irreducible degree-\(p\) polynomial for odd prime \(p\), with normal closure of group \(D_{2p}\) in its natural degree-\(p\) action. Norm membership from \(E=K[X]/(f)\) reduces to ordinary tensor isomorphism in deterministic polynomial bit time on the explicit simple number-field presentations in [Entry 170](#entry-170). Factor \(f\) over \(E\); besides the displayed root its orbits under the root stabilizer are pairs, so any other irreducible factor is quadratic. Adjoining one root from any such factor gives a field of degree \(2p\) over \(K\), hence the normal closure. Factor \(f\) once there and use its roots in the earlier relative-norm compiler. Each step works in an explicit polynomial-degree number field. To convert the one relative quadratic presentation to an absolute simple presentation, choose a primitive element by trying polynomially many small integer coefficients in a linear combination of the two generators, since each pair of distinct embeddings excludes at most one coefficient, then use the powers basis and solve linear systems. This conversion keeps polynomial bit lengths. [Lenstra](https://ir.cwi.nl/pub/2541)

<a id="entry-172"></a>

### 172. Determinant correction for ordered matrix tuples through reduced norms

Let \(K\) be a perfect field, and let \(A\) be the commutant algebra of an ordered endomorphism tuple on \(V\). A joint conjugator, when given, can be corrected to determinant one exactly when its inverse determinant belongs to the following subgroup. Write \(A/\operatorname{rad}A=\prod_i M_{r_i}(D_i)\), with \(D_i\) central division over \(K_i\), of index \(d_i\); let \(m_i\) be the multiplicity of the simple module for factor \(i\) among the composition factors of \(V\) as \(A\)-module. The subgroup is
\[
\prod_i N_{K_i/K}\big(\operatorname{Nrd}(M_{r_i}(D_i)^\times)\big)^{m_i d_i}.
\]
The radical acts trivially on the graded factors of a composition series and units of the quotient lift, so a determinant is the product of the determinants on its simple constituents. Over a splitting field the simple \(D_i^{r_i}\) module is \(d_i\) copies of the defining \(r_i d_i\)-dimensional representation. This identifies its determinant over \(K_i\) with the stated reduced norm to power \(d_i\). Restriction to \(K\) takes the field norm. This is a different mechanism from the commutative algebra norm of [Entry 159](#entry-159) and works with arbitrary nonsplit simple factors.

<a id="entry-173"></a>

### 173. Local-global determinant correction for rational commutants with rational centers

Take an ordered matrix tuple over \(\mathbb Q\) with a given rational joint conjugator to its target and with every simple factor of its commutant having center \(\mathbb Q\). A determinant-one joint conjugator exists over \(\mathbb Q\) exactly when one exists over every completion. To see this, write \(w_i=m_i d_i\) as in [Entry 172](#entry-172), omitting zero weights. The image of a rational reduced norm is \(\mathbb Q^\times\) or \(\mathbb Q_{>0}\), according to whether the real factor is split or quaternionic. At finite places all reduced norms are onto. The same formula [Entry 172](#entry-172) commutes with extension, using the original reduced norms and powers even when a simple factor becomes a matrix algebra over a smaller division algebra. Consequently the finite tests require all rational prime valuations of the correction \(c\) to be divisible by \(g=\gcd_i w_i\). They suffice for its positive part by Bézout and a rational \(g\)-th root. The real test allows a negative correction precisely when some real-unrestricted factor has odd \(w_i\); in this case the sign is supplied by that factor. [Hasse–Schilling–Maass theorem in the general central simple setting, Goldstein–Schacher](https://arxiv.org/abs/1707.02498), [local reduced norm and the quaternion formulation, Voight, Lemma 13.4.9 and Main Theorem 14.7.4](https://jvoight.github.io/quat-book.pdf)

<a id="entry-174"></a>

### 174. A local-global theorem for simply connected stabilizers

For arbitrary tensors over a number field, assume they are geometrically signed-equivalent and that the geometric source stabilizer for the signed action is connected, semisimple and simply connected. The pair has a signed transporter over the number field if it has one over every completion. The transporter is a torsor under that source stabilizer over the base, which is a form of a semisimple simply connected group. The Kneser–Harder–Chernousov Hasse principle trivializes its class in \(H^1\) from all its local trivializations. The hypothesis on the signed stabilizer is essential to this argument; the connected norm-one torus in [Entry 164](#entry-164) illustrates the separate arithmetic of tori. [Chernousov, final type \(E_8\) case](https://www.mathnet.ru/php/archive.phtml?jrnid=dan&option_lang=eng&paperid=7092&wshow=paper)

<a id="entry-175"></a>

### 175. Laurent-series descent for reductive tensor stabilizers

If two geometrically equivalent tensors over any field \(K\) have reductive source stabilizer for the tested action, equivalence over \(K((t))\) implies equivalence over \(K\), for either action. The source stabilizer and its transporter torsor extend by the constant base change to \(K[[t]]\). Equicharacteristic Grothendieck–Serre injectivity for the regular local ring \(K[[t]]\) shows that the torsor over the ring is trivial if its generic fiber is, and reduction modulo \(t\) gives the desired transporter. The result also applies over the fraction field of any regular local \(K\)-algebra equipped with residue field \(K\), by the same argument. [Fedorov–Panin, infinite fields](https://arxiv.org/abs/1211.2678), [Panin, finite fields](https://arxiv.org/abs/1707.01767)

<a id="entry-176"></a>

### 176. Split solvable stabilizers give descent over arbitrary fields

Suppose two tensors are geometrically equivalent for either action and their source stabilizer is smooth with a filtration by normal \(K\)-subgroups whose successive quotients are \(\mathbb G_a\) or \(\mathbb G_m\). Then they are equivalent already over \(K\). The transporter has a separable point by smoothness, so is a Galois torsor. Additive and multiplicative Hilbert 90 kill the first cohomology of each factor. Inductively, the image of the torsor class in the last quotient is trivial; exactness makes it come from the preceding subgroup, whose cohomology has already been killed.

<a id="entry-177"></a>

### 177. Density of reductions with a prescribed tensor transporter

Let \(A,B\) be geometrically equivalent tensors over a number field \(K\) for either action, let \(\Omega\) be the finite set of geometric connected components of their transporter, and let \(\Pi\) be the finite image of the absolute Galois group of \(K\) on \(\Omega\). Outside finitely many primes there is a transporter over the residue field precisely when its Frobenius fixes some element of \(\Omega\). Hence the good prime ideals have density \(|\{\pi\in\Pi:\Omega^\pi\ne\varnothing\}|/|\Pi|\). Indeed the transporter is smooth in characteristic zero and is a torsor under the source stabilizer. Spread out its smooth stabilizer and torsor, and the finite étale component scheme with its identifications, after removing finitely many primes. A Frobenius-fixed component over the residue field is a torsor under the connected identity subgroup and has a point by Lang. Chebotarev gives the density. If \(\Pi\) acts transitively on more than one component the density is strictly between zero and one: the identity fixes all of them, whereas the average number of fixed points is one. [Lang, 1956](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf), [Chebotarev density in finite Galois extensions](https://websites.math.leidenuniv.nl/algebra/chebotarev.pdf)

<a id="entry-178"></a>

### 178. Characteristic-zero geometric equivalence detected by infinitely many reductions

Two tensors over a number field are geometrically equivalent for either action exactly when their reductions have residue-field transporters for infinitely many prime ideals. The positive implication follows from [Entry 177](#entry-177), since the identity in its finite Galois permutation image fixes a component. For the converse encode the transporter by the matrix equations and invertibility, using additional scalar variables for inverse determinants in the ordinary case. If this system has no solution over the algebraic closure of \(K\), the Nullstellensatz gives an ideal combination equal to one. Clear all denominators in the finitely many coefficients. The same contradiction then excludes transporters modulo every prime outside a finite set. Thus reduction at infinitely many primes detects geometric equivalence even though it cannot establish a rational transporter, as [Entry 164](#entry-164) shows.

<a id="entry-179"></a>

### 179. Purely transcendental extensions reflect tensor equivalence over every field

For either action, tensors over any field \(K\) are equivalent over \(K(t_1,\ldots,t_m)\) if and only if they are equivalent over \(K\). A displayed rational-function transporter is defined on some nonempty principal open of affine \(m\)-space, obtained by excluding the denominators. Over an infinite \(K\), that open has a \(K\)-point by the elementary polynomial identity lemma. For \(K=\mathbb F_q\), the same open has an \(\mathbb F_{q^k}\)-point for every sufficiently large \(k\), by the polynomial zero bound. The earlier Frobenius-component theorem gives a finite union of divisibility progressions for the degrees at which the transporter has a point. Such a union contains every sufficiently large \(k\) only if one of its periods is one, as seen by taking primes larger than all periods. This proves the missing finite-field specialization and applies also to arbitrary purely transcendental extensions by taking the finitely many variables appearing in the witness.

<a id="entry-180"></a>

### 180. All odd residue characteristics can miss an obstruction at two

The actual signed tensors in [Entry 159](#entry-159) for \(K=\mathbb Q\), \(E=\mathbb Q[\epsilon]/(\epsilon^8)\) and \(c=16\) are signed-equivalent over \(\mathbb R\) and every \(\mathbb Q_p\) with \(p\) odd. They are signed-inequivalent over \(\mathbb Q_2\) and \(\mathbb Q\). The relevant norm image is the eighth powers by [Entry 161](#entry-161). For an odd prime \(p\), write \(p-1=2^a b\) with \(b\) odd. When \(a\le2\), the fourth power \(2^4\) is an eighth power in \(\mathbb F_p^\times\) since the fourth and eighth power maps have the same image. When \(a\ge3\), \(p\equiv1\bmod8\), so \(2\) is a quadratic residue by the supplementary reciprocity law and \(2^4\) is again an eighth power. Hensel lifts the nonzero solution to \(\mathbb Q_p\). At two the valuation of \(16\) is four, which excludes eighth powers.

<a id="entry-181"></a>

### 181. Exact single-period connected descent over arbitrary finite fields

Suppose a tensor pair over \(\mathbb F_q\) has an ordinary base transporter and geometrically connected reduced ordinary stabilizer. Use the earlier split-quotient character matrix of its determinant map and write its nonzero Smith exponents as \(s_i\), with corresponding transformed corrections \(b_i\in\mathbb F_q^\times\). Require correction one on all zero Smith rows. For each prime \(\ell\mid\prod_i\operatorname{ord}(b_i)\), set
\[
M_\ell=\max_{i: \,\ell\mid\operatorname{ord}(b_i)}
       \big(v_\ell(s_i)+v_\ell(\operatorname{ord}(b_i))\big).
\]
All successful extension degrees are precisely the multiples of \(\operatorname{ord}_{M}(q)\), where \(M=\prod_\ell\ell^{M_\ell}\) and \(\operatorname{ord}_1(q)=1\). Indeed the Smith test requires \(v_\ell(q^k-1)\ge M_\ell\) exactly, so is equivalent to \(q^k\equiv1\bmod M\). The minimum divides \(\operatorname{lcm}_i s_i\), since \(q\equiv1\bmod\ell\) for every relevant prime, and raising \(q\) to \(\ell^a\) increases \(v_\ell(q-1)\) by at least \(a\) by binomial expansion. Thus each single-prime order divides \(\ell^{\max_i v_\ell(s_i)}\). This extends the earlier explicit ternary spectrum to arbitrary finite fields, with a period bound independent of the splitting degree of the original torus.

<a id="entry-182"></a>

### 182. Transporter counts recover Frobenius cycle multiplicities

For a nonempty geometric transporter \(X\) of two finite-field tensors for either action, put \(J=H^\circ_{\mathrm{red}}\) for the connected reduced source stabilizer over the perfect base. If the geometric components of \(X_{\mathrm{red}}\) have \(a_d\) cycles of Frobenius length \(d\), then
\[
\frac{|X(\mathbb F_{q^k})|}{|J(\mathbb F_{q^k})|}
   =\sum_{d\mid k}d a_d .
\]
Every rational point lies in a Frobenius-fixed component, which contains a rational point by Lang. Acting on that point by \(J(\mathbb F_{q^k})\) identifies the entire rational point set of its component with the group. Möbius inversion recovers each \(a_d\) from the normalized counts at degrees dividing \(d\). This gives the complete component cycle type, stronger information than the previous nonemptiness spectrum alone. [Lang](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf)

<a id="entry-183"></a>

### 183. Exact number of rational forms of a geometric tensor orbit

Fix a rational tensor \(A\) over \(\mathbb F_q\), and take its geometric orbit for either action. Let \(\Gamma\) be the geometric component group of its reduced stabilizer and \(\sigma\) the Frobenius automorphism of \(\Gamma\). Rational orbits inside the geometric orbit correspond to \(\sigma\)-twisted conjugacy classes in \(\Gamma\). For a rational \(gA\), record the component of \(g^{-1}\operatorname{Frob}(g)\). Lang's theorem in the ambient group gives every such class, and Lang in the stabilizer identity component, with Frobenius twisted by an inner automorphism, removes the choice of lift within the component. More explicitly, if two cocycle values project to the same element, write their difference in the connected group and apply Lang to \(x\mapsto a\operatorname{Frob}(x)a^{-1}\), which is the Frobenius of a descended form of that group. The number of classes equals the number of ordinary conjugacy classes of \(\Gamma\) preserved by \(\sigma\). For twisted conjugation by \(x\), a fixed \(a\) solves \(a^{-1}xa=\sigma(x)\); it exists exactly for \(x\) in a \(\sigma\)-stable ordinary class, and then there are \(|C_\Gamma(x)|\) solutions. Burnside averages these contributions, one per stable class. [Lang](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf)

<a id="entry-184"></a>

### 184. Coprime field extension reflects rational forms without an ordinary transporter

In [Entry 183](#entry-183), assume two rational tensors of the same geometric orbit become equivalent over \(\mathbb F_{q^k}\). They were already equivalent over \(\mathbb F_q\) if \(\gcd(k,|\Gamma|)=1\), even if the order of the Frobenius action shares primes with \(k\). This applies with the component group of the actual signed stabilizer and needs no rational ordinary transporter. Write \(m=\operatorname{ord}\sigma\) and realize twisted conjugacy as \(\Gamma\)-conjugacy in the coset \(\Gamma\sigma\) of \(\Gamma\rtimes C_m\). Extension sends \(a\sigma\) to \((a\sigma)^k\), by the ordered cocycle product. After \(\Gamma\)-conjugating representatives \(X,Y\), assume \(X^k=Y^k=Z\). In \(C=C_{\Gamma\rtimes C_m}(Z)\), the projection is onto since \(X\) projects to \(\sigma\). Let \(B=C\cap\Gamma\). Modulo the central subgroup \(\langle Z\rangle\), the image of \(B\) is normal and the quotient is cyclic of order \(\gcd(k,m)\), because \(Z\) projects to \(\sigma^k\). The images of \(X,Y\) have order dividing \(k\) and generate complements to the image of \(B\), since they project onto the quotient and \(|B|\) is coprime to \(k\). Schur–Zassenhaus conjugates the complements by an element of the image of \(B\), and their specific generators match because the projected generators match. Lifting, \(bXb^{-1}=YZ^j\) with \(b\in B\). The projection and \(k\)-th powers give \(Z^j\in B\) and \((Z^j)^k=1\), hence \(Z^j=1\). The argument even needs only \(\gcd(k,|C_\Gamma(Z)|)=1\).

<a id="entry-185"></a>

### 185. Abelian components give a Bézout descent criterion

In [Entry 183](#entry-183) suppose \(\Gamma\) is abelian, written additively. Rational forms have classes in \(\Gamma/(\sigma-1)\Gamma\). The exact extension test for two classes separated by \(u\) is
\[
(1+\sigma+\cdots+\sigma^{k-1})u\in(\sigma^k-1)\Gamma .
\]
On the base coinvariants this implies \(k[u]=0\). Thus any list of successful extension degrees whose greatest common divisor is coprime to the exponent of the base coinvariants is sufficient for base equivalence. This includes two successful coprime degrees and applies regardless of \(\gcd(k,|\Gamma|)\) for the individual degrees. If \(\sigma=1\), the successful degrees are exactly multiples of the order of the difference class.

<a id="entry-186"></a>

### 186. Ordered tuple conjugacy has universal scalar-extension descent

Let \(X_1,\ldots,X_t\) and \(Y_1,\ldots,Y_t\) be endomorphism tuples on equal finite-dimensional spaces over \(K\). If they are simultaneously conjugate over any field extension, they are simultaneously conjugate over \(K\). This applies to tensors interpreted as labelled slice tuples with an invertible named anchor, with the residual row and column maps identified by that anchor. A finite-dimensional \(K\)-algebra acts on the direct sum of the two spaces by the block matrices \(X_i\oplus Y_i\). The question is whether its two summands are isomorphic modules. For a finite extension, restricting an extended isomorphism gives an isomorphism between equal positive numbers of copies of the two modules, so Krull–Schmidt gives cancellation. For an arbitrary extension, the determinant of the generic element of the linear intertwiner space is nonzero if an invertible intertwiner exists anywhere. For infinite \(K\) it is nonzero at a base point. For finite \(K\) it is nonzero at a point of some finite extension by the polynomial zero bound, bringing the problem back to the finite-extension case. This gives the precise distinction from [Entry 172](#entry-172), where a determinant restriction can defeat descent.

<a id="entry-187"></a>

### 187. Single-exponential extension bound for geometric signed equivalence

Put \(v=\sum_i n_i^2\) for the total number of transporter matrix entries, and \(D=\max(3,n_1,n_2,n_3)\). A geometrically signed-equivalent pair over \(\mathbb F_q\) has a signed transporter over some \(\mathbb F_{q^k}\) with \(k\le D^v\). The solution scheme is defined in affine \(v\)-space by cubics or lower-degree tensor equations and by the three determinant-one equations, all of degree at most \(D\). The sum of degrees of the irreducible components of the underlying algebraic set is at most \(D^v\) by affine Bézout's component bound. One can obtain the bound by successively intersecting with generic linear combinations of the defining equations, retaining a component once it is contained in the target. At each round, active components that are cut properly drop dimension and their total child degree is at most \(D\) times their degree. Each surviving component is either part of the target or is cut again, so the weighted degree bound by remaining codimension yields \(D^v\). Frobenius permutes the connected components, no more numerous than the irreducible components, and some cycle length is at most this bound. Lang provides a point on that component over the extension of its cycle length. This complements the earlier superpolynomial minimum-degree examples. [Heintz, affine degree and Bézout inequalities](https://doi.org/10.1016/0304-3975(83)90002-6)

<a id="entry-188"></a>

### 188. Unmarked affine hypersurface isomorphism on an explicit determinant family

Start from the earlier squarefree homogeneous polynomial \(P_A(X)\) encoding signed tensor equivalence, with zero translation radical and degree \(d\), and the absolutely irreducible suspension \(Q_A=P_A(X)+y\xi^{d-1}\). Then abstract isomorphism over \(K\) of the affine schemes \(Q_A=0\) is equivalent to signed equivalence of the underlying tensors, with no marked point in the input. The translation radical of \(Q_A\) is zero: the coefficient of \(y\) first forces the \(\xi\)-direction to vanish, the coefficient involving \(\xi^{d-1}\) forces the \(y\)-direction to vanish, then \(P_A\) gives zero in \(X\). Its affine origin is the unique geometric point of multiplicity \(d\). For a point \(a\), the hypersurface multiplicity is the order of \(Q_A(X+a)\), whose top homogeneous part is \(Q_A(X)\). Multiplicity \(d\) therefore means \(Q_A(X+a)=Q_A(X)\). Homogeneity gives \(Q_A(X+\lambda a)=Q_A(X)\) for all \(\lambda\ne0\) over the infinite algebraic closure, contradicting zero translation radical unless \(a=0\). Every abstract isomorphism preserves the forced vertex and induces a graded isomorphism of its maximal-ideal associated graded rings. Those rings are the original homogeneous hypersurface coordinate rings. A graded isomorphism is induced by a linear map on the degree-one generators and maps the single degree-\(d\) relation to its scalar multiple. The earlier suspension proof then recovers signed tensor equivalence. The reverse tensor extraction and polynomial-size affine-linear determinant presentation are the previous ones. In particular this is an equivalence on the specific presented family, including over \(\mathbb F_3\).

<a id="entry-189"></a>

### 189. Canonically polarized normal projective determinant hypersurfaces

The projective family can be chosen geometrically normal and with \(\omega_Y\simeq\mathcal O_Y(1)\). In the earlier \(P_A\) construction, raise the eight distinct marker degrees by a common polynomially bounded amount until its total degree \(d\) is at least \(M+3\), where \(M\) is the number of coordinates of \(P_A\). The recovery proof uses distinct marker degrees greater than the core degree and is unchanged under this choice. Adjoin \(d-M-3\) unused coordinates to \(Q_A=P_A(X)+y\xi^{d-1}\), for \(d-1\) total homogeneous coordinates. Its projective singular locus still spans the hyperplane \(\xi=0\), since the old axes, \(y\) axis, and new unused-coordinate axes are singular. The restriction to this hyperplane has translation radical exactly the span of \(y\) and the unused coordinates, so the same quotient recovers \(P_A\). The hypersurface is integral. Its geometric singular locus is contained in \(\xi=0\) and projects in the affine coordinate blocks onto the singular locus of \(P_A=0\). As \(P_A\) is squarefree over the algebraic closure, the latter locus has codimension at least two in the affine \(X\)-space. Including \(\xi=0\) gives ambient codimension at least three and singular codimension at least two in the hypersurface. The hypersurface is Cohen–Macaulay and therefore normal by Serre's criterion. Adjunction gives \(\omega_Y=\mathcal O_Y(d-(d-1))=\mathcal O_Y(1)\). Any abstract isomorphism preserves this intrinsic polarization and hence extends linearly by the complete system of canonical sections. The affine-linear determinant representation and inverse extraction remain polynomial size and work in every characteristic.

<a id="entry-190"></a>

### 190. Birational equivalence loses the comparison on the entire family

The projective hypersurfaces in [Entry 189](#entry-189) of any fixed format are all \(K\)-rational, since the chart \(\xi=1\) solves uniquely for \(y\) and is an affine space in the remaining coordinates. Thus they are birational over \(K\) regardless of whether they are isomorphic over \(K\). The family includes pairs without a geometric isomorphism, for example the constructions for the zero tensor and a nonzero tensor of the same format. It also includes pairs geometrically isomorphic but arithmetically distinct, by applying [Entry 164](#entry-164). Consequently neither birational equivalence nor the existence of a dense affine-space open recovers the signed tensor comparison, even on normal canonically polarized projective hypersurfaces.

<a id="entry-191"></a>

### 191. Succinct Artin algebras with one top-layer relation give an exact model

Let \(Q_A\) be as in [Entry 188](#entry-188) in \(N\) variables, let \(\mathfrak m=(x_1,\ldots,x_N)\), and consider the local algebra \(R_A=K[x]/(\mathfrak m^{d+1},Q_A)\). Present it succinctly by \(N,d\) and the affine-linear determinant pencil for its one additional relation, with the cutoff ideal implicit. Any \(K\)-algebra isomorphism preserves the unique maximal ideal and hence its associated graded ring, which is the displayed graded algebra. Its degree-one map must carry the unique line of relations in degree \(d\) to the target's line. A linear change of coordinates doing this gives an algebra isomorphism, so these tests are equivalent, and [Entry 188](#entry-188) recovers signed tensor equivalence. Both reductions use polynomial-size data in this succinct presentation, including inverse coefficient extraction. This concerns one relation at the top of a higher nilpotency filtration, a different model from the previous explicit cubic-zero radical tables. No expansion of the full multiplication table is involved.

<a id="entry-192"></a>

### 192. Finite point sets suffice after a provably small extension

Let \(P_A,P_B\) be the earlier reduced forms of the same format and total degree \(d\). Over a finite test field \(L\) with \(|L|>d^2+1\), an invertible linear map sends the projective \(L\)-point sets onto each other if and only if it maps the geometric hypersurfaces onto each other. Here the projective-point assertion may equally be tested by vanishing on the affine cones. To prove the nontrivial direction, each irreducible factor other than \(s\) has shape \(V^eU+R\), linear in \(U\), with \(R\) independent of \(U\), and \(e+1\le d\). This is true for every marker and the core. Given the pullback of \(P_B\) under the linear map, substitute \(U=-R/V^e\) and clear denominators by \(V^{ed}\). The resulting polynomial of degree at most \(d(e+1)\le d^2\) vanishes on all test-field choices with \(V\ne0\). Multiplying by \(V\) makes it vanish everywhere, so it is the zero polynomial by the multivariate degree bound. The given irreducible factor divides the pullback in the localization at \(V\), hence also before localization, as it is coprime to \(V\). The factor \(s\) is handled by direct evaluation on its hyperplane. Squarefreeness and matching degrees finish the proof. The same argument with the single factor \(Q_A\) works for the absolutely irreducible suspension. Thus over any fixed ground field \(\mathbb F_q\) the geometric condition for a ground-field transformation is recovered by a point test over one extension of degree \(O(\log d)\). This does not require listing that potentially very large projective point set.

<a id="entry-193"></a>

### 193. Rational finite-group invariants separate rational tensor orbits

In a tensor coordinate space of dimension \(N\) over \(\mathbb F_q\), the indicator function of any rational special-linear orbit is represented by a polynomial of degree at most \(N(q-1)\). It is the sum over that orbit of the point indicators \(\prod_j(1-(x_j-a_j)^{q-1})\), with disjoint supports on rational points. To obtain an actual polynomial fixed by the finite group \(G=\prod_i\mathrm{SL}_{n_i}(\mathbb F_q)\), multiply the pullbacks of this polynomial by all \(g\in G\). This ordinary product is unchanged as a formal polynomial under the finite group and still evaluates to the orbit indicator on every rational point. Its degree is at most \(|G|N(q-1)\), giving an unconditional separation bound even when the characteristic divides \(|G|\). Algebraic group invariants can fail to separate the same points by [Entry 196](#entry-196).

<a id="entry-194"></a>

### 194. Low-degree rational-group invariants are already algebraic invariants

A tensor polynomial of total degree \(<q\), over \(\mathbb F_q\), which is formally invariant under \(\prod_i\mathrm{SL}_{n_i}(\mathbb F_q)\) is invariant under the algebraic group after scalar extension. For any one elementary transvection with parameter \(T\), the difference of the pulled-back and original polynomial has degree at most the given total degree in \(T\), since a transvection changes the tensor coordinates linearly in \(T\). It vanishes identically as an \(x\)-polynomial at all \(T\in\mathbb F_q\), so it is zero in \(\mathbb F_q[x,T]\). Elementary transvections generate each special-linear factor over the algebraic closure. In particular a formal finite-group invariant separating two rational forms of a single geometric orbit must have degree at least \(q\). The assertion is about formal invariance, with evaluation invariance of polynomial functions a separate condition.

<a id="entry-195"></a>

### 195. A side-dimension divisibility law for every algebraic invariant

For the usual covariant tensor representation, any nonzero positive-degree homogeneous polynomial invariant under the algebraic special-linear product has degree divisible by every side dimension. For each factor, write the exponent sum in its \(j\)-th slice of a monomial as \(a_j\). The diagonal determinant-one torus scales that monomial by its weight, and formal monomial independence forces invariance of each weight contributing to the polynomial. Zero weight means \(a_1=\cdots=a_{n_i}\) for factor \(i\), since the character lattice of that diagonal torus identifies tuples only modulo the all-one vector. Summing the \(a_j\) gives the degree, which is consequently divisible by \(n_i\). The lattice proof keeps factors of the characteristic in this divisibility assertion. After using dual input conventions the weights in a whole factor are negated and the same conclusion holds.

<a id="entry-196"></a>

### 196. Arbitrarily many closed rational tensor orbits share every algebraic invariant

In odd characteristic, the split diagonal \(n\times n\times n\) three-tensor has signed geometric stabilizer with component group \(A_n\) and trivial Frobenius action on it. Multiplication identifies this with \(M_{\mathbb F_q^n}\). In the determinant formula of [Entry 159](#entry-159), three coordinates one force \(\det\sigma=1\), hence even permutations, and the residual two unit groups are independent product-one tori, geometrically connected. Every even permutation is itself represented over the finite field. The diagonal geometric signed orbit is closed by the earlier calculation. Thus [Entry 183](#entry-183) says exactly as many rational signed orbits lie in it as there are conjugacy classes of \(A_n\). This tends to infinity, since the even permutations formed from \(j\) disjoint three-cycles have different ordinary cycle types as \(j=0,\ldots,\lfloor n/3\rfloor\) varies. The count is the number of conjugacy classes of \(S_n\) in characteristic two, where all permutation determinants are one. All polynomial invariants of the algebraic group have equal values on these rational orbits because they are in the same geometric orbit.

<a id="entry-197"></a>

### 197. A complete finite-field invariant for regular \(2\times2\times2\) tensors

Let \(K\) be a finite field of odd order. A \(2\times2\times2\) bilinear-map tensor whose binary determinant polynomial in one input has nonzero discriminant is determined up to signed equivalence by that discriminant in \(K^\times\), without quotienting by squares. To see this, choose a nonsingular slice, possible since a nonzero quadratic has at most two projective zeros and \(|\mathbb P^1(K)|\ge4\), and normalize that slice to the identity. The other normalized slice generates a quadratic étale algebra \(E\), because the two orbit roots are distinct. The resulting pencil is the regular multiplication representation of \(E\), after compatible vector-space basis choices. Its ordinary class is thus determined by the squareclass of the discriminant, which determines \(E\). Under an ordinary transporter \((f,g,h)\) the binary determinant transforms by the scalar \(\det h/\det g\) and the inverse label map \(f^{-1}\); the discriminant transforms by \((\det h/(\det f\det g))^2\). Equality of discriminants gives the sign condition of [Entry 160](#entry-160) since the two quadratic étale automorphisms have determinants \(1,-1\), and the remaining norm conditions are automatic over a finite field. The converse follows from determinant-one invariance.

<a id="entry-198"></a>

### 198. Local-global signed equivalence for all regular rational \(2\times2\times2\) tensors

Over any number field, two regular \(2\times2\times2\) tensors in the [Entry 197](#entry-197) sense are signed-equivalent if they are signed-equivalent over every completion. Local equivalence gives equality of their global binary determinant discriminants. The same regular-pencil normalization gives one rational ordinary transporter, since their quadratic étale algebras are identical up to isomorphism. The exact correction criterion [Entry 160](#entry-160) reduces the comparison to two independent norms from the common quadratic algebra. That criterion remains valid after every completion, including where the algebra splits, and the cyclic Hasse norm theorem gives each global norm. Thus this positive theorem covers the whole regular \(2\times2\times2\) stratum over number fields, not only norm-twist comparisons chosen in advance.

<a id="entry-199"></a>

### 199. Exact arithmetic splitting of a regular \(2\times2\times2\) discriminant fiber

Over any field of characteristic different from two, choose one rational tensor in a given nonzero discriminant fiber of the regular stratum in [Entry 197](#entry-197), and let \(E\) be its quadratic étale algebra. The rational signed orbits within that fiber are in bijection with the pairs in \((K^\times/N_{E/K}(E^\times))^2\). All tensors of the given discriminant are in one ordinary orbit by the same pencil normalization, which holds since any such field has at least four projective points. Let \((a,b,h)\) be determinant data for an ordinary transporter from the chosen tensor, and \(d=ab/h\). Exact discriminant equality means \(d=\pm1\). Composing with an appropriate source automorphism of determinant sign \(d\) normalizes the third-to-product ratio to one. Remaining source autotopisms of ratio one have determinant tuples \((u,v,uv)\) with \(u,v\in N_{E/K}(E^\times)\) by [Entry 159](#entry-159). Hence after normalization the two independent norm classes are exactly the orbit invariants. All pairs occur by twisting the chosen tensor with determinant tuples \((a,b,ab)\). Over \(\mathbb R\) this gives four real signed orbits in the nonsplit quadratic case and one in the split case, with the same nonzero discriminant value in each fiber.

<a id="entry-200"></a>

### 200. Exact proportions of local-global failures in explicit signed tensor families

Apply [Entry 159](#entry-159) over \(\mathbb Q\) to any fixed number field \(E\), using rational targets \(c=a/b\ne0\) in reduced form with height \(\max(|a|,|b|)\le B\). Count comparison instances by their written parameters \(c\). Among the instances with signed transporters at every completion, the limiting proportion of rational signed NO instances is \(1-1/i(E/\mathbb Q)\), where \(i\) is the knot number, namely the index of the global norm group in the everywhere local norm group. The sets being counted coincide exactly with the norm sets in Browning–Newton's theorem by [Entry 159](#entry-159). For \(E=\mathbb Q(\sqrt{13},\sqrt{17})\), exactly half of the locally soluble instances are counterexamples at each height cutoff, since multiplication by the locally normed nonglobal value \(-1\) preserves height and exchanges the two norm classes, and the number of such counterexamples is asymptotic to \(C B^2/(\log B)^{3/2}\) for a constant \(C>0\). This is a count of rationally parameterized pairs in one fixed tensor format with closed geometric signed orbits. [Browning and Newton, Theorems 1.2 and 1.4](https://arxiv.org/abs/1411.7775)
