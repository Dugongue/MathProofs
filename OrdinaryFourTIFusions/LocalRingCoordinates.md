# Exact formal coordinates and determinant profiles for ordinary four-tensors over finite local rings

This is an informal extension of the [almost-all ordinary four-tensor theorem](https://github.com/Dugongue/MathProofs/blob/main/FourTIAlmostAll/RESULTS.md). The previous [search and Galois-ring lifting proof](https://github.com/Dugongue/MathProofs/blob/main/FourTIAlmostAll/SearchAndLifting.md) gives a transporter above a successful residue comparison. Here we construct one exact coordinate system for the entire residue fiber, and use it to classify lifts and count all transporters with any four prescribed determinants.

## The theorem

Let \(R\) be an explicitly presented finite commutative local ring with maximal ideal \(\mathfrak m\) and fixed residue field \(k=\mathbb F_q\). The ring presentation consists of cyclic additive coordinates and their multiplication structure constants. The radical dimension, characteristic exponent, and nilpotence index may vary with the input. Let \(A,D\) be dense balanced ordered four-tensors of side \(n\ge2\) over \(R\). Fix a positive constant \(M\).

There is a recognizable invariant source set with uniform density at least \(1-O_{q,M}(n^{-M})\), for every such \(R\). For each recognized source and every target, one can decide ordinary isomorphism, find a witness, and return the exact number of witnesses in deterministic polynomial bit time. With any prescribed determinants \(\delta_1,\ldots,\delta_4\in R\), the same three claims hold for witnesses with exactly that determinant quadruple.

More precisely, fix any recognized residue tensor \(A_0\) and choose any lift \(T_0\). One can give an affine coordinate slice through \(T_0\) that contains exactly one representative of every ordinary isomorphism class in the fiber over \(A_0\). The slice has \(n^4-4n^2+3\) coordinates in \(\mathfrak m\). Hence there are exactly \(|\mathfrak m|^{n^4-4n^2+3}\) classes in this fiber. The transporter of each point to its slice representative is unique after normalization of three entries and can be computed by Newton doubling.

The algorithm and its probability bound also apply to finite ring products with residue field \(k\) in every local factor. With \(s\) local factors the rejection bound is \(s\) times the local bound. In particular, one can choose the polynomial running-time exponent to obtain arbitrarily high inverse-polynomial coverage for any fixed polynomial upper bound on \(s\) in \(n\). The local factors need not be supplied.

## 1. Recognition and the two residue stabilizer properties

Let \(G_R=\operatorname{GL}_n(R)^4\), acting by the tensor product of the four mode maps. Its central subgroup

\[
Z_R=\{(u_1I,u_2I,u_3I,u_4I):u_i\in R^\times,\ \prod_i u_i=1\}
\]

fixes every tensor. Use the residue search theorem together with its certificate that \(\operatorname{Stab}_{G_k}(A_0)=Z_k\). Additionally compute the kernel of

\[
L_{A_0}(X_1,X_2,X_3,X_4)=\sum_i(1\otimes\cdots\otimes X_i\otimes\cdots\otimes1)A_0 .
\]

Require that it contain only scalar tuples \((x_iI)_i\) with \(\sum_ix_i=0\). The latter property is certified by testing kernel dimension three. Both conditions are invariant under the residue action. The residue algorithms and their arbitrary inverse-polynomial rejection bounds are established in [Search and lifting](https://github.com/Dugongue/MathProofs/blob/main/FourTIAlmostAll/SearchAndLifting.md) and [Sharper coverage](https://github.com/Dugongue/MathProofs/blob/main/FourTIAlmostAll/SharperCoverage.md).

For the two scalar conditions, the elementary failure bound is worth recalling. If a factor \(g_i\) is nonscalar, choose \(v\) with \(g_iv\) outside its span. Restrict the operator \(\bigotimes_i g_i-I\) to \(v\otimes(k^n)^{\otimes3}\) and project the \(i\)-th output factor modulo \(kv\). This produces an injection because the remaining factors are invertible. Its rank is at least \(n^3\). For a nonscalar infinitesimal factor \(X_i\), the same argument projects away every term except the one with \(X_iv\), again giving rank at least \(n^3\). There are at most \(q^{4n^2}\) tuples in either calculation. A scalar tuple with the wrong product or sum fixes or annihilates only the zero tensor. This gives failure probability at most \(2q^{4n^2-n^3}+q^{-n^4}\) for both conditions together. The residue of a uniform tensor over \(R\) is uniform and all recognition conditions depend only on the residue.

## 2. An explicit coordinate slice and its inverse

Write \(N=n^4\), \(r=4n^2-3\), and \(d=N-r\). In the infinitesimal domain set \((X_i)_{11}=0\) for \(i=1,2,3\). This gives an \(r\)-dimensional subspace complementary to the scalar kernel, since any tuple can be cleared in those three positions by adding a unique scalar kernel tuple. Restricting \(L_{A_0}\) to that subspace gives an injective map to \(k^N\). Pick \(r\) pivot output positions of an invertible minor. The coordinate subspace on the remaining \(d\) positions is a complement to the image. Make the choices in a fixed coordinate order.

For \(x\in\mathfrak m^r\) let \(X_i\) be its matrices in these input coordinates and write \(g(x)_i=I+X_i\). For \(w\in\mathfrak m^d\), embed \(w\) on the nonpivot output positions as above. Define the polynomial map

\[
F(x,w)=g(x)\cdot(T_0+w).
\]

Every matrix \(g(x)_i\) is invertible. The reductions of all Jacobians of \(F\) on this domain are the same block map \(J_0:(X,w)\mapsto L_{A_0}(X)+w\), which is invertible over \(k\) by the pivot choice. Therefore each such Jacobian over \(R\) is invertible.

Here is a direct inverse algorithm on any \(T\equiv T_0\pmod{\mathfrak m}\). Start with \(z=(x,w)=0\). While \(F(z)\ne T\), solve

\[
DF(z)\,\eta=T-F(z),\qquad z\leftarrow z+\eta .
\]

If the residual belongs entrywise to \(\mathfrak m^j\), so does \(\eta\), since the inverse Jacobian is \(R\)-linear. The polynomial remainder has at least two factors from \(\eta\), so the new residual is in \(\mathfrak m^{2j}\). This proves termination in at most \(\lceil\log_2 L\rceil\) steps when \(\mathfrak m^L=0\). It also proves uniqueness. If \(z,z'\) have the same image and agree modulo \(\mathfrak m^j\), the first-order difference and the inverse Jacobian force their difference into \(\mathfrak m^{2j}\). They agree modulo \(\mathfrak m\) by construction, and nilpotence yields equality. This proves the exact bijection

\[
\mathfrak m^r\times\mathfrak m^d\longrightarrow T_0+\mathfrak m^N.
\]

The Jacobian can be formed by differentiating the explicit multilinear expression and solved by unit-pivot elimination. Its size is polynomial in the dense tensor length. The same coordinate map commutes with local reduction of coefficients whenever the chosen anchor lift is reduced along with the inputs. For a compatible family of anchor lifts it therefore also gives compatible normal coordinates at every finite precision.

## 3. The slice classifies unmarked ordinary isomorphism

Let \(S=T_0+w\) and \(S'=T_0+w'\). A transporter between them reduces to a scalar tuple of product one, because both have residue \(A_0\). Lift the scalar tuple to \(Z_R\) by lifting its first three units arbitrarily and using the inverse of their product for the fourth. Dividing the transporter by this tuple makes all its modes congruent to the identity. The \((1,1)\) entries in the first three modes are now units in \(1+\mathfrak m\). Divide by a second element of \(Z_R\), taking exactly these three entries as its first three units. The resulting transporter has the form \(g(x)\) in the coordinate map of Section 2. Since \(F(x,w)=F(0,w')\), injectivity gives \(x=0,w=w'\). This proves the slice assertion and proves that the exact stabilizer of every point in the fiber is \(Z_R\). Indeed the stabilizer of its slice representative is \(Z_R\), and conjugating by the normalizing map cannot change a central subgroup.

On an arbitrary comparison, first run the residue search algorithm. For a positive output \(\bar h\), take any matrix lifts of its modes, which are invertible over \(R\), and denote the tuple by \(h\). Compare \(A\) to \(h^{-1}D\) using the same anchor lift \(T_0\) of their common residue. If their slice coordinates differ then no transporter exists. If they agree and their recovered coordinate tuples are \((x,w)\) and \((x',w)\), respectively, the tuple \(h g(x')g(x)^{-1}\) transports \(A\) to \(D\). This procedure uses each tensor's slice invariant in a common residue fiber. A transporter computed with a different initial residue witness differs by an element of \(Z_R\), by the already established stabilizer assertion.

## 4. Exact determinant profiles and orbit splitting

Suppose \(g\) is any computed transporter and put \(H=R^\times\). Every transporter is uniquely \((u_i g_i)_i\) with \(u_i\in H\) and \(\prod_i u_i=1\), so the unrestricted count is \(|H|^3\). Scale each requested unit determinant by setting \(v_i=\delta_i/\det(g_i)\). A nonunit request fails. For unit requests the condition is exactly

\[
 v_i\in H^n\quad(1\le i\le4),\qquad \prod_i v_i=1 .
\]

In fact, take arbitrary roots \(u_i^n=v_i\). Their product is in \(H[n]=\{u:u^n=1\}\), so multiply the last root by the inverse of that product. This gives a transporter with the requested determinants. All such transporters then form a coset of the kernel on \(Z_R\), which has size \(|H[n]|^3\). Thus the number of distinct attainable profiles is \(|H^n|^3\). More structurally, \(\operatorname{SL}_n(R)^4\) is the kernel of the surjective four-determinant map on \(G_R\). Its orbits in any recognized \(G_R\)-orbit correspond to the cosets of the determinant image of \(Z_R\) in \(H^4\). Consequently each ordinary orbit splits into exactly

\[
\frac{|H|^4}{|H^n|^3}=|H|\,|H[n]|^3
\]

special-linear orbits.

Here is a polynomial-time computation of \(H^n\) membership, a root when one exists, and \(|H[n]|\). Write \(|R|=p^B\). Choose generators of the elementary additive groups \(\mathfrak m^j/\mathfrak m^{j+1}\) as bases over \(\mathbb F_p\). For each basis element lift to \(a\in\mathfrak m^j\) and use the principal unit \(u=1+a\). Order the generators by layer. Every principal unit has a word in them computed by reading its quotient coordinates and removing their unit product layer by layer. The equality \((1+a)(1+b)\equiv1+a+b\pmod{\mathfrak m^{j+1}}\) for \(a,b\in\mathfrak m^j\) proves this collection rule. The \(p\)-th power of each generator lies in the next layer, because each quotient has exponent \(p\). Encode the collected relations \(u^p=\prod_{v\text{ later}}v^{e_v}\) as integer rows. Their matrix is triangular with diagonal \(p\) and presents the actual principal-unit group. Indeed it surjects to the group, and its determinant gives the exact product of the layer cardinalities, equal to the actual order.

Adjoin a lift of a generator of the fixed residue group \(k^\times\). Raise the lift to an exponent congruent to one modulo \(q-1\) and zero modulo \(p^B\). The resulting lift has order \(q-1\), since its \((q-1)\)-st power was raised to a multiple of the principal-unit group order. It splits the residue map and gives one more independent cyclic relation. The case \(q=2\) has trivial residue group. Discrete logs in \(k^\times\) use a fixed lookup table. Now integer Smith normal form expresses the entire unit group as a product of explicitly computable cyclic groups. The power tests and equations are linear congruences in those coordinates, and the kernel cardinality is the product of the gcds of \(n\) with the cyclic orders. Group representatives are recovered by powering the supplied units. No enumeration of the ring or of its unit group occurs.

To compute the filtration from the ring presentation, take \(R/pR\). Its nilradical is the kernel of a sufficiently high Frobenius power, an \(\mathbb F_p\)-linear map there. For example, its \(B\)-fold iterate kills every nilpotent. Each strictly decreasing step in the powers of the radical reduces the additive order by a factor at least \(p\) until zero, by Nakayama's lemma. Taking the inverse image gives \(\mathfrak m\), since \(pR\) is nilpotent. Generate each successive ideal additively using products of coordinate generators. Additive subgroup and quotient computations use integer Smith or Hermite normal form. The number of generators needed over all principal-unit layers is at most \(B\), the nilpotence index is at most \(B+1\), and all exponent and coefficient bit lengths are polynomial in the presentation. This also bounds all output counting bit lengths.

## 5. Finite products and relation to prior work

For a finite commutative ring whose residue fields are all isomorphic to the same fixed \(k\), compute the radical \(J\) by the same Frobenius kernel on \(R/pR\). The semisimple quotient is \(k^s\). Obtain the subalgebra \(\mathbb F_p^s\) as the kernel of \(u\mapsto u^p-u\). An \(\mathbb F_p\)-basis of this subalgebra separates its coordinates. Starting with the identity, split each currently obtained idempotent by each basis element \(a\) using the coordinate masks \(1-(a-t)^{p-1}\), for \(t\in\mathbb F_p\). Keep only nonzero parts. This produces the primitive idempotents in polynomial time, because there are at most \(s\) nonzero parts and \(p\) is fixed. Lift the idempotents to \(R\) by the Newton correction for \(z^2-z\). The derivative \(2z-1\) is a unit whenever \(z\) is idempotent modulo \(J\), since its square is congruent to one. Each step squares the error ideal. The lift is unique since the difference of two lifts is killed by their sum minus one, a unit. This also makes the lifted idempotents pairwise orthogonal with sum one. They present the actual finite product with explicit coordinate maps. Transport, witnesses, determinant conditions, and counts all decompose exactly. For uniform first inputs the residue components are independent, and the required rejection bound follows already by a union bound. [Lenstra and Silverberg on idempotent lifting and principal units](https://arxiv.org/abs/1509.02612)

The explicit slice proof is a Jacobian computation in the spirit of formal étaleness, and the unit filtration is standard finite-ring algebra. The new application here is the exact classification and determinant enumeration of the almost-all four-tensor residue fibers, with uniform deterministic bit complexity for arbitrary explicit local rings of fixed residue and no restriction on the radical embedding dimension. The [commutative-ring TI program of Grochow, Qiao, Stange and Sun](https://arxiv.org/abs/2611.00735) studies general complexity and reductions over rings. The [MathProofs deformation-family construction](https://github.com/Dugongue/MathProofs/blob/main/IntrinsicIsomorphismCrossovers/deformation.md) gives worst-case hardness in specially chosen fibers with larger residue stabilizers. In the present result the scalar residue and infinitesimal conditions are where the exact transverse coordinates arise. The present proof concerns the stated recognized family and carries no claim of publication priority. [The Stacks Project, formally étale maps](https://stacks.math.columbia.edu/tag/00UP)
