# Succinct class-two group isomorphism and free tensor isomorphism over prime-power rings

**Theorem.** Fix a prime $p$, or supply $p$ as part of the input. Isomorphism of arbitrary finite $p$-groups of nilpotency class at most two in centered power-commutator coordinates is deterministically polynomial-time many-one equivalent to ordinary free three-tensor isomorphism over $\mathbb Z/p^E\mathbb Z$, where the modulus $p^E$ is supplied in binary and $E$ may vary.

The group coordinates give cyclic bases of $C=Z(G)$ and $A=G/C$, the commutators of chosen lifts of the quotient generators, and their central powers to their cyclic orders in $A$. All cyclic orders are written in binary. Both directions produce one target instance. If $n=\log_p|G|$, the forward reduction uses maximum tensor side $O((n+1)^2)$ and takes $E$ to be the maximum cyclic exponent in $A,C$, or one for the trivial group. A source tensor of format $(a,b,c)$ over $\mathbb Z/p^E\mathbb Z$ gives a group of order $p^{O((E+1)(a+b+c+1))}$ in the succinct model.

## 1. Intrinsic commutator and power data

Write $A,C$ additively and use the commutator convention $[x,y]=xyx^{-1}y^{-1}$. Commutation gives an alternating bilinear map $b:A\times A\to C$. Let $A_j=A[p^j]$, $C_j=C/p^j C$, and put
$$
q_j:A_j\to C_j,\qquad q_j(v)=\widetilde v^{\,p^j}\bmod p^j C.
$$
The power belongs to $C$ and changing the lift adds an element of $p^j C$. Also $q_j(kv)=kq_j(v)$ for integers $k$, by choosing the lift $\widetilde v^k$. The class-two power identity gives
$$
q_j(v+w)-q_j(v)-q_j(w)=-\binom{p^j}{2}b(v,w)\pmod{p^j C}.
$$
This is zero for odd $p$ because $p^j$ kills $b(v,w)$. For $p=2$ it is $2^{j-1}b(v,w)$ modulo $2^j C$, of order dividing two.

A pair of isomorphisms $g:A\to A'$, $h:C\to C'$ lifts to a group isomorphism exactly when it preserves $b$ and the listed $q_j$ under the induced actions. It is enough to list the values $j$ occurring as cyclic exponents in $A$. Indeed let $a_i$ be a cyclic generator of order $p^{s_i}$, with lift $x_i$ and recorded central power $c_i=x_i^{p^{s_i}}$. Choose any lift $y_i$ of $g(a_i)$. Preservation of $q_{s_i}$ says that $h(c_i)-y_i^{p^{s_i}}$ belongs to $p^{s_i}C'$. Multiplying $y_i$ by a central element corrects the power exactly and leaves all commutators unchanged. The central cyclic orders, centrality, quotient generator powers and pairwise commutators give a presentation of $G$. Collection gives at most $|A||C|$ distinct ordered normal words and the presentation surjects onto $G$ of order $|A||C|$. Thus the corrected lifts and $h$ induce a homomorphism. Since it induces isomorphisms on the center and its quotient, it is bijective. The converse is immediate from functoriality.

A cyclic generator of the $a_i$ summand of $A_j$ is $p^{\max(s_i-j,0)}a_i$. Its $q_j$ value is $p^{\max(j-s_i,0)}c_i$ modulo $p^j C$. Thus all necessary coordinates are explicitly computable. The input can be promised valid or validated in polynomial time. Check the cyclic orders, coefficient ranges, alternatingness, annihilation by the two relevant cyclic orders on each commutator, and that $b$ has zero radical, using Smith operations over the prime-power ring. An ordered bilinear cocycle on $A$ realizes the commutators. It is well-defined by the annihilation test. To realize the powers, add the ordinary coordinate carry cocycle. In a cyclic coordinate of order $m$, its value is the required central power multiplied by $\lfloor(x+y)/m\rfloor$ for representatives $0\le x,y<m$. Both cocycle identities follow, respectively, from bilinearity and from adding three representatives in either order. The resulting group on $A\times C$ has the given relations and the radical test makes its center exactly $C$.

For Cayley-table inputs, compute the center and central quotient directly. In either abelian group, successively adjoin generators outside the subgroup generated so far, enumerating that subgroup to recover the relative order and power relation of the next generator. The resulting triangular integer presentation has the correct order by collection. Smith normal form and its basis changes give cyclic coordinates and actual representatives. Table operations give all the desired powers and commutators in polynomial time in the table size.

## 2. Linear representation of the binary power data

For $p=2$ use the intrinsic binary quotient
$$
U_j=A_j/(A_{j-1}+2A_{j+1}),\qquad A_0=0.
$$
The polarization of $q_j$ vanishes when one argument belongs to $A_{j-1}$. When that argument is $2z$ in $2A_{j+1}$, the polarization is $2^j b(z,w)=0$ for $w\in A_j$. Hence polarization factors through $U_j$ in both arguments. Each cyclic summand contributes dimension one to $U_j$ exactly when its order is $2^j$. Lower-order summands are killed by $A_{j-1}$ and higher-order ones by $2A_{j+1}$. Denote this dimension by $d_j$.

For a binary vector space $U$, let $D(U)=U\otimes_{\mathbb F_2}U$ and let $\Gamma(U)\subseteq D(U)$ be the fixed space of swapping the factors. In a basis $e_i$ of $U$, a basis of $\Gamma(U)$ is
$$
e_i\otimes e_i,\qquad e_i\otimes e_k+e_k\otimes e_i\quad (i<k).
$$
There is a natural linear map $\delta:\Gamma(U)\to U$ sending the first listed vectors to $e_i$ and the second to zero. Indeed $\delta(v\otimes v)=v$, using binary coefficients. The pure squares $\gamma(v)=v\otimes v$ span $\Gamma(U)$ since their defects give the listed off-diagonal basis. Thus the displayed property characterizes $\delta$ and makes it natural.

Set
$$
P_j=A_j\times_{U_j}\Gamma(U_j)
    =\{(x,z):x\in A_j,\ z\in\Gamma(U_j),\ \bar x=\delta(z)\}.
$$
There is a unique homomorphism $Q_j:P_j\to C_j$ with $Q_j(x,\gamma(\bar x))=q_j(x)$. In the cyclic coordinates, the pairs $(u_i,\gamma(\bar u_i))$ for cyclic generators $u_i$ of $A_j$, together with a basis of $0\times\ker\delta$, give an explicit direct sum decomposition of $P_j$. Each pair has the same order as $u_i$. Assign it the value $q_j(u_i)$, which satisfies that order bound. Assign to each off-diagonal basis element of $\ker\delta$ the polar value of the corresponding two exact-order cyclic generators. Each such value has order at most two. The defect identity
$$
\gamma(v+w)-\gamma(v)-\gamma(w)=v\otimes w+w\otimes v
$$
then gives the required formula by expanding in cyclic coordinates and using the additive power defect from Section 1. The elements $(x,\gamma(\bar x))$ span $P_j$, because they contain the cyclic lifts and their defects generate $0\times\ker\delta$. This proves uniqueness.

Record $b$, the maps $A_j\hookrightarrow A$, $C\to C_j$, $A_j\to U_j$, $\Gamma(U_j)\hookrightarrow D(U_j)$, $\delta$, the two projections out of $P_j$, and $Q_j$. Also record the bimap $U_j\times U_j\to D(U_j)$ of pure tensors. All sorts are abelian groups of exponent at most $2^E$, hence modules over that prime-power ring. Isomorphisms of the records force the induced maps on $A_j,C_j,U_j$ by the indicated inclusions and quotient maps. They force the action on $D(U_j)$ because pure tensors span. The inclusion forces the restriction to $\Gamma(U_j)$ and the two projections jointly force the map on $P_j$. Therefore $Q_j$ is preserved precisely when $q_j$ is preserved. Conversely compatible actions on $A,C$ extend by all these induced maps. This gives an exact diagram test for the original group isomorphism.

For odd $p$, simply record $b$ and the linear maps $A_j\hookrightarrow A$, $C\to C_j$, and $q_j:A_j\to C_j$. In both cases there are only $O(n+1)$ roles and maps, and the total ranks with multiplicity of occurrences are $O((n+1)^2)$. For the binary case there are $O(n)$ cyclic generators per level outside tensor-square terms, and $\sum_j d_j^2\le n^2$ for the latter. Cyclic bases for all auxiliary modules are given by the constructions.

## 3. Replace cyclic modules by free roles

Over $R=\mathbb Z/p^E\mathbb Z$, replace a role $M=\bigoplus_i R/(p^{a_i})$ by two free roles $F_M,F'_M$ of rank the number of its cyclic summands and a fixed linear map
$$
S_M:F_M\to F'_M,\qquad S_M=\operatorname{diag}(p^{E-a_i}).
$$
This factors as the usual quotient $\pi_M:F_M\to M$ and the injection $\iota_M:M\hookrightarrow F'_M$ identifying $M$ with $\operatorname{im}S_M$. Compare the corresponding cyclic types first. Invertible free maps $X,Y$ with $Y S_M=S_{M'}X$ induce the same map on the quotient and its embedded image.

Conversely lift an isomorphism of modules by taking representatives $x_{ij}$ of its entries modulo $p^{a_i}$, with orders in increasing order. The column order relation forces $p^{a_i-a_j}\mid x_{ij}$ whenever $a_i>a_j$. Thus $y_{ij}=p^{a_j-a_i}x_{ij}$ is an integer using division only in divisible entries. These satisfy $Y S_M=S_{M'}X$. The reductions of $X,Y$ modulo $p$ are block upper and block lower triangular respectively, with identical diagonal blocks. Those blocks are invertible since $X$ induces the isomorphism on $M/pM$. Thus both lifts are invertible.

Replace each bimap $\beta:M_1\times M_2\to M_3$ by the free bimap
$$
(x,y)\longmapsto \iota_{M_3}\beta(\pi_{M_1}x,\pi_{M_2}y).
$$
Replace unary maps in the same way, then bilinearize them using one scalar role whose action is fixed to identity. Surjectivity of the quotient maps and injectivity of the inclusions prove equivalence of the linked tests. The same lifts work on all occurrences of each role. This preserves the previous rank bound.

## 4. One unmarked free tensor

Consider a diagram of free roles $V_0=R,V_1,\ldots,V_r$, whose scalar role action is the identity, with marked bimaps $\phi_t:V_i\times V_j\to V_k$. Build a three-level triangular associative $R$-algebra $\mathcal A$ with vertices represented by orthogonal diagonal idempotents. The corner from $u$ to $v$ is $e_u\mathcal A e_v$. Common first and last vertices $O,P$ have corner $W=\bigoplus_i W_i$ between them, where $W_i$ copies $V_i$. Write $\ell$ for the generator of $W_0$.

For each $t$, insert a private middle vertex $M_t$ with arrows $O\to M_t$ of space $Ra_t\oplus V_i$ and $M_t\to P$ of space $Rb_t\oplus V_j$. Their product in $W$ is given by
$$
a_tb_t=\ell,\qquad xb_t=x\in W_i,\qquad a_ty=y\in W_j,\qquad xy=\phi_t(x,y)\in W_k.
$$
Append two scalar outgoing arrows from $M_t$ to distinct private last vertices. Multiplication by them gives the two projections of the incoming data arrow to its summands, in distinct first-to-last corners. Append two scalar incoming arrows to $M_t$ from distinct private first vertices. Multiplication on the left gives the same projections for the outgoing data arrow. To distinguish each $W_i$ add a private middle vertex with incoming space $V_i$, outgoing space $R$, and product the scalar action with image $W_i$. Every unlisted off-diagonal product is zero.

Assign each vertex a distinct length $N_v$ between one and the number of vertices. Its diagonal corner is $R[z_v]/(z_v^{N_v})$. Positive powers of $z_v$ annihilate each incident off-diagonal corner and the local unit acts by identity. This defines a unital associative algebra. A product of two arrows lands at the final level, and a third off-diagonal factor gives zero in either association. Constants act compatibly by bilinearity. The ideal $J$ generated by $p$, the positive diagonal powers and the off-diagonal corners is nilpotent and the quotient is the product of one $\mathbb F_p$ for each vertex. Thus $J$ is the Jacobson radical.

An algebra isomorphism permutes vertex residues modulo $J$. If $u_v$ are the image idempotents and $e'_{\sigma(v)}$ the corresponding standard idempotents in the target, the element $z=\sum_v u_v e'_{\sigma(v)}$ is one modulo $J$ and satisfies $u_vz=ze'_{\sigma(v)}$. Conjugating by its inverse aligns the idempotents. The distinct diagonal ranks $N_v$ then force all vertices to be fixed. The projection products identify the two summands of each data arrow as kernels of multiplication by the respective marker lines. The probes recover $W_i$ as their product images. Let $c_i$ be the resulting action on $W_i$, with $c_0$ multiplication by a unit $\lambda$. The units $\alpha_t,\beta_t$ on $Ra_t,Rb_t$ satisfy $\alpha_t\beta_t=\lambda$. The maps on their data summands must be $\beta_t^{-1}c_i,\alpha_t^{-1}c_j$ by the anchor products. Thus the product equations on $(x,y)$ give
$$
c_k\phi_t(x,y)=\lambda^{-1}\phi_t'(c_ix,c_jy).
$$
Writing $g_i=\lambda^{-1}c_i$ gives the desired compatible maps with $g_0=1$. Conversely diagram maps lift by setting all anchor and marker scales to one, acting by $g_i$ on each role copy, and fixing diagonal corners.

The multiplication table is a single free three-tensor with dual input modes. An isotopy $f(x)g(y)=h(xy)$ of two such unital associative algebras satisfies $h(x)=f(x)v=ug(x)$ where $u=f(1)$ and $v=g(1)$. Surjectivity and injectivity give invertibility of left multiplication by $u$ and right multiplication by $v$, making both elements units. For example if $ut=1$, injectivity of left multiplication by $u$ applied to $tu$ and $1$ gives $tu=1$. Then $\varphi(x)=u^{-1}f(x)=g(x)v^{-1}$ is a unital algebra isomorphism by the isotopy equation. Conversely an algebra isomorphism is an isotopy. This proves exactness over the local ring, including residue characteristic two.

The algebra has $O(n+1)$ vertices and total diagonal rank $O((n+1)^2)$. All other ranks are $O((n+1)^2)$ by the diagram size bounds. The dense table is written in polynomial time with coefficients of $O(E\log p)$ bits. Given an output transporter, the displayed normalizations give $g,h$ on the center and quotient, and then central corrections recover an actual group isomorphism.

## 5. Reverse reduction

First compare the two input formats. If their ordered dimensions differ, return a fixed negative group-isomorphism instance at the same prime. This check is required before using the same free ranks on both sides in the lifting argument.

For a free bimap $\mu:X\times Y\to W$ over $R=\mathbb Z/p^E\mathbb Z$, let
$$
L_X=X\oplus X^*\oplus H_X,\qquad L_Y=Y\oplus Y^*\oplus H_Y,\qquad L=L_X\oplus L_Y.
$$
The free pads $H_X,H_Y$ have even ranks $d_X,d_Y$. Take $d_X>c_0$ and $d_Y>d_X+c_0$, with both $O(c_0+1)$ for $c_0=2(\operatorname{rank}X+\operatorname{rank}Y)$. Let $J_X,J_Y$ be standard symplectic forms pairing each role with its dual and with an independent symplectic form on its pad, extended by zero on the other half. Define $\Theta:L\times L\to W\oplus R^2$ with components $\mu(x,y')-\mu(x',y), J_X,J_Y$. Its radical is zero because the two marker forms have complementary radicals.

A scalar slice of $\Theta$ is $D+\alpha J_X+\beta J_Y$ where data slices $D$ vanish on the pads. The minimum number of module generators of its matrix image lies in $[s,s+c_0]$, with $s=d_X[\alpha\ne0]+d_Y[\beta\ne0]$. The pad blocks have independent images, and every nonzero ideal of $R$ needs one generator. The remaining block has $c_0$ columns. The four possible intervals are disjoint. Thus every transporter preserves data covectors and each marker coordinate line modulo the data. Each marker changes by a unit scale and a data slice.

Let $K$ be the common radical of the data slices. Then $K=K_X\oplus K_Y$ with $K_X=\ker\mu(-,Y)\oplus X^*\oplus H_X$ and $K_Y=\ker\mu(X,-)\oplus Y^*\oplus H_Y$. Recover these as $K\cap\operatorname{rad}J_Y$ and $K\cap\operatorname{rad}J_X$. These intersections are unaffected by marker scales and added data because data annihilate $K$. The $J_Y$-orthogonal to $K_Y$ projects in $L/K$ to the $X$-quotient by the left kernel: it contains $L_X$, and the presence of $Y^*$ in $K_Y$ forces the $Y$ coordinate to vanish. The analogous formula recovers the $Y$-quotient. These constructions again ignore added data since data annihilate $K$. Therefore the induced quotient actions preserve the descended bimap, with output action dual to the data covector action.

Any isomorphism $R^d/N\to R^d/N'$ lifts to an invertible free map between free modules of the same rank. Choose lifts of the standard generators to get an initial linear map. Modulo $p$ it induces the isomorphism of the quotients by the images of $N,N'$. Alter its restriction on the image of $N$ to any isomorphism onto the image of $N'$ by a linear correction, with image in the latter, and extend the correction to the ambient residue space. Lift each column correction into $N'$. This leaves the lift on the quotients fixed and makes the free map invertible modulo $p$, hence invertible over $R$. Lift the two quotient actions by this procedure. Then the original bimap equations hold since the two kernels annihilate the bimap. Conversely any original transporter gives a $\Theta$ transporter by the inverse dual actions and identities on the pads and two scalar outputs. All dimensions are linear in the input format sum.

Write $L=R^d$, $W\oplus R^2=R^m$ and take $C=(\mathbb Z/p^{E+1}\mathbb Z)^m$ with $pC$ identified with $R^m$ by multiplying lifts by $p$. On $R^d\times C$ use the central group law with biadditive cocycle
$$
f(x,y)=p\sum_{i<k}x_i y_k\Theta(e_i,e_k).
$$
It is independent of representatives because of the factor $p$ and the target modulus. Its commutator is $f(x,y)-f(y,x)=p\Theta(x,y)$, so the center is exactly $C$. The chosen basis lifts $(e_i,0)$ have zero central powers at order $p^E$. Every lift $(x,0)$ has that power equal to $\binom{p^E}{2}f(x,x)\in p^E C$. This follows from divisibility of the binomial for odd $p$ and from its divisibility by $2^{E-1}$ with $f(x,x)\in2C$ at $p=2$.

A group isomorphism induces a $\Theta$ isometry on the central quotient and $pC$. Conversely an isometry lifts its output map to $C$ by lifting entries, which keeps it invertible modulo $p$. The prescribed image of each quotient basis lift can be corrected by a central element to have zero required power. The resulting maps give a group isomorphism by Section 1. The centered presentation uses polynomially many explicit entries. This proves the reverse reduction and the asserted order bound.

## 6. Scope and comparison

This is an informal proof of a complexity equivalence in the stated succinct models. The quadratic dimension enlargement in the forward direction gives no new Cayley-table running-time bound. Grochow–Qiao–Stange–Sun, Theorem 5.1, use Baer's correspondence at odd primes and give better linear dimensions there. Sun treats general class-two 2-groups by restricting a tensor search and using an orbit computation to restore power digits. Here the full powers enter a single ordinary free tensor comparison. The Frattini-class-two quadratic-form encoding is classical, and the proof here handles mixed cyclic orders and unbounded commutator exponent. [TI V](https://arxiv.org/html/2611.00735v1#S5) · [Sun, general class two](https://arxiv.org/html/2611.05920v1) · [Grochow–Ivanyos–Qiao–Sun, Frattini class two](https://arxiv.org/html/2610.00874v1)

Representing quadratic maps by linear maps on a universal module is established. The contribution here is the equal-order localization of the power defects and the compatible single-instance encoding. Zhang–Wang–Zhuang §4 gives a marked triangular ring for one bimap and obtains algorithms polynomial in a table-sized parameter. Section 4 above encodes arbitrarily many linked roles, removes all corner marks by local tags, and does not use that algorithmic hypothesis. The proof reuses the prior MathProofs triangular algebra for linked tensor roles and radical-free alternating marker. The closest sources checked do not state the exact uniform equivalence. Publication priority is unverified. [Gaudier–Hartl](https://arxiv.org/abs/0809.0194) · [Zhang–Wang–Zhuang §4](https://arxiv.org/html/2611.18084v1#S4) · [Grochow–Qiao, linear-length reductions](https://arxiv.org/html/2306.16317v2)
