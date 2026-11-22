# Polynomial Calculus degree for algebras with thin basic corners

**Theorem.** Consider the literal three-tensor isomorphism system of a geometrically negative pair. Suppose one tensor, after compression to its supports, is geometrically an associative unital multiplication tensor. Over the algebraic closure write
$$
A/\operatorname{rad}A=\prod_i M_{u_i}(k)
$$
in that multiplication model, and take lifts of matrix units $e_{i,ab}$ in $A$. Suppose the basic corners $e_{i,11}A e_{j,11}$ have dimension at most one for all $i,j$. Let $d$ be the largest active side of the pair. Then ordinary PC has degree $O((d+1)^2)$ in characteristic zero and in characteristic $p>d$, and $O((d+1)^4)$ in every characteristic. No field equations are used and the target is arbitrary. Thus these bounds hold with ordinary rank or border rank in place of $d$ when both ranks are bounded. The class contains all the thin basic algebras, arbitrary matrix algebras over them, and algebras in which different vertices of a thin basic algebra have different matrix sizes. [Basic thin case and literal comparison](ThinAlgebras.md)

Work geometrically and descend as in the companion proof. Its support compression and unital isotope calculation give an algebra isomorphism system, with polynomial-coordinate maps $\phi,\psi$ in the original witnesses, whose identities have constant-degree derivations. A failure of that preliminary calculation is refutable in degree $O(d+1)$. Hereafter $A,B$ are the two unital associative multiplication models of equal dimension $d$. Write $J_A,J_B$ for their radicals. All bases for algebras and subspaces below are fixed scalars. Fixed projections are implemented by constant linear combinations of identities, as in the basic thin proof.

## 1. Supply radical transport

In characteristic zero or $p>d$, the radical of the bilinear form
$$
(a,b)\longmapsto \operatorname{Tr}(L_{ab}:A\to A)
$$
is $J_A$, and likewise for $B$. On the radical filtration, the multiplication representation decomposes into simple modules over the split quotient; the trace pairing is a sum of ordinary matrix trace pairings with multiplicities of the respective simple modules. Each multiplicity is positive, since its block appears in the quotient of the regular module itself, and at most $d$. Hence each coefficient is nonzero, and the ordinary full-matrix trace pairing is nondegenerate. Trace is unchanged by conjugacy, and multiplicativity gives $L_{\phi(ab)}=\phi L_{ab}\psi$ in constant degree. The corresponding linear kernel equations transport $J_A,J_B$ in both directions in constant degree.

In characteristic $0<p\le d$, take a power $q=p^h$ with $d\le q<pd$, taking $q=d$ if $d$ is already such a power. We show that the coordinatewise $q$-powers of the algebra-map witnesses transport the radicals between the Frobenius twists of the two algebras. For each fixed $a\in J_A$ and fixed $b,c\in B$, the element $\psi(b\phi(a)c)=\psi(b)a\psi(c)$ lies in the fixed $J_A$ after bounded-degree projection. Its $d$-th power is identically zero by $J_A^d=0$, and the transported identity $(b\phi(a)c)^d=0$ has a degree-$O(d)$ derivation by multiplication and the algebra equations. In $B/J_B$, choose $b,c$ to lift constant matrix units that sandwich a specified entry $\ell(\phi(a))$ of one simple block into its $(1,1)$ position, killing all other entries and blocks. Projecting the $d$-th power identity gives $\ell(\phi(a))^d=0$. Multiplying gives its $q$-th power zero in degree $O(q)$. Repeat for basis vectors $a$ of $J_A$, then reverse the argument for $J_B$.

Raise each algebra-map or inverse equation to its $q$-th power by PC multiplication. In characteristic $p$ these are the same equations with $q$-powered coefficients and $q$-powered witness coordinates. The preceding projections supply the missing radical transport equations in the same coordinates. Frobenius is a field automorphism on the algebraic closure, so twisting preserves geometric nonisomorphism and the thin-corner condition. A proof of degree $D$ in the twisted algebra-map variables with the radical transport equations therefore gives degree $O(q(D+1))$ in the original tensor variables. We now treat exact radical transport and then apply this substitution.

## 2. Align the central blocks

Under radical transport, each radical grade $J^a/J^{a+1}$ is transported in both directions with constant degree. The induction derives projection lines for the next power from products of two fixed basis vectors, as in the basic thin proof. Transport centers of the quotient using their fixed commutator equations and $\phi\psi=1$. In the primitive center idempotent bases the maps give an orthogonal Boolean permutation matrix, with both row and column sums one. This uses transport of products and the unit, and the two coefficient matrices are transposes by pulling back and pushing forward the relations for a product of two idempotents. Quotient center dimensions differing give a rectangular determinant contradiction in degree $O(d)$. Choose one permutation branch, and relabel the target accordingly.

Choose lifts of matrix units of the target quotient as well, using the semisimple subalgebra lifting theorem over the algebraic closure. Put $e_i=\sum_a e_{i,aa}$, and let $f_i$ be the corresponding lifted target central-block idempotent. Thus $\phi(e_i)-f_i\in J_B$ on the branch. The left and right actions of these idempotents on every radical grade are transported, since the discrepancy sends that grade one step down. If any dimension of a matched grade corner differs, the induced rectangular forward and inverse matrices on its image refute the branch by a determinant in degree $O(d)$, as in the basic thin proof. If they all agree, the degree-zero grade gives the equality of matching matrix sizes $u_i$, and summing all grades gives equality of the dimensions of the full central corners. Matrix units identify $e_i A e_j$, as a bimodule, with matrices of shape $u_i\times u_j$ whose entries lie in $e_{i,11}Ae_{j,11}$, by multiplying on the left and right by the units. The same holds for $B$. Therefore their basic corner dimensions match and are zero or one. In particular $f_iJ_B f_i=0$.

With $p_i=\phi(e_i)$ put $U=\sum_i p_i f_i$, $V=\sum_i f_i p_i$. As in the basic thin proof, $VU=1$, since $f_i(p_i-f_i)f_i=0$; the idempotent $1-UV$ vanishes by the successive squaring projection through the radical powers, in constant PC degree. Adjust $\phi$ by conjugating by $U^{-1}=V$. It now sends $e_i$ to $f_i$. Write $\phi,\psi$ for the resulting maps. Their coordinate polynomials and certificates still have bounded degree.

## 3. Use rank-one projectors without choosing local bases

Fix a basis of each nonzero basic corner and use lifted matrix units to identify every nonzero full $(i,j)$ corner with the scalar rectangular matrices $M_{u_i\times u_j}$. In a diagonal block choose the given matrix units. Under these identifications multiplication of two composable nonzero corners, when the output corner is nonzero, is ordinary rectangular matrix multiplication times the scalar product coefficient in the two basic corners. When the output is zero the product is zero. This follows by multiplying the intermediate matrix units and summing over their common index.

Write $p_i=\phi(e_{i,11})$ in the actual $i$-th target diagonal matrix algebra. We derive uniformly bounded-degree identities that $p_i$ is idempotent, has trace one, and has zero $2\times2$ minors. The first follows immediately. To prove the others let $P_{ab}=\phi(e_{i,ab})$ and write $p=P_{11}$. The identity
$$
p E_{bc}p=\gamma_{bc}p
$$
holds with $\gamma_{bc}$ the $(1,1)$ coefficient of $\psi(E_{bc})$, by applying $\phi$ to the corresponding elementary corner projection in the source. Reading entries gives $p_{ab}p_{cd}=\gamma_{bc}p_{ad}$. Setting $d=a$, summing over $a$, and using $p^2=p$ gives $p_{cb}=\tau\gamma_{bc}$ where $\tau=\operatorname{Tr}p$. Substituting this in $\sum_a P_{a1}pP_{1a}=I$ gives a polynomial inverse of $\tau$ by taking a single diagonal entry. Consequently $\tau(p_{ab}p_{cd}-p_{ad}p_{cb})=0$ implies the corresponding $2$-minor vanishes. These minor identities give $p^2=\tau p$ entrywise. Using idempotence and the same matrix-unit sum gives $\tau=1$. All products used here involve a bounded number of bounded-degree polynomials. In particular, for every supported endomorphism $Z=p_i Z p_i$ we have $Z=\operatorname{Tr}(Z)p_i$, by the same rank-one entry identity summed against $Z$.

On a nonzero corner $(i,j)$ let $W_{ij}$ be the image under $\phi$ of the chosen basic generator, viewed as a rectangular matrix with $W_{ij}=p_i W_{ij}p_j$. Construct its inverse between the two projected lines. Let $\gamma(X)$ be the $(1,1)$ coefficient of $\psi(X)$ on this rectangular corner. It is a functional with polynomial coefficients. Under the rectangular trace pairing write $\gamma(X)=\operatorname{Tr}(L X)$ for a polynomial $u_j\times u_i$ matrix $L$. Set $V_{ji}=p_j L p_i$. Then
$$
V_{ji}W_{ij}=p_j,\qquad W_{ij}V_{ji}=p_i .
$$
In fact both products are supported on their corresponding rank-one projectors, and both have trace $\gamma(W_{ij})=1$ by cyclicity of rectangular traces. These are again degree-bounded polynomial identities. A square-zero or zero-product mismatch on matched basic corners is refuted using these inverse equations, because the product of two such isomorphisms of projected lines is invertible between the outer lines. This works also when the outer corner is present and only one of the structure constants vanishes. When the outer corner is absent both constants are zero.

In each connected component of the graph of nonzero basic corners, ignoring directions, choose a spanning tree and a root. Let $G_i$ be the product of the available $W,V$ maps along the tree path from the root to vertex $i$, and $H_i$ its reverse product. Thus $G_i$ is a rectangular map from the root block to block $i$, $H_iG_i=p_{\rm root}$, and $G_iH_i=p_i$. These identities follow by successive adjacent cancellations, at degree $O(d)$ since a tree path has length at most $d$. The rank-one calculation now gives
$$
H_i W_{ij}G_j=\lambda_{ij}p_{\rm root},
\qquad
H_j V_{ji}G_i=\mu_{ij}p_{\rm root}
$$
where the scalar coefficients are taken by trace and are polynomial of degree $O(d)$ in the algebra-map witnesses. The projectors and inverse identities imply $\lambda_{ij}\mu_{ij}=1$. On diagonal corners the value is one. When the two composable basic products have nonzero structure constants, the multiplication identity on the matrices reduces to the usual scalar equation
$$
c_{ijk}\lambda_{ik}=c'_{ijk}\lambda_{ij}\lambda_{jk}.
$$
All these equations have derivations of degree $O(d)$ after expanding products along the chosen paths. No coordinate on a projected line had to be inverted.

## 4. Discharge the branch

Any solution of the resulting Laurent-binomial system identifies the basic multiplication tables by scalar changes, and using the matching matrix units it gives an isomorphism of the whole algebras. On a negative input the Laurent system is therefore inconsistent in each branch. The Steinitz proof in the companion theorem refutes it in degree $O(d)$ in its abstract scalar variables. Substituting the polynomial path weights multiplies the degree by $O(d)$. The resulting branch proof has degree $O(d^2)$, and the Boolean permutation selector removes the branch at additive $O(d)$ cost. This proves $O(d^2)$ in the exact-radical system. The Frobenius step gives the stated $O(d^4)$ in the remaining characteristics, since $q\le d^2$.

This is a written proof. The use of projected rank-one modules keeps the proof inside ordinary PC even when the transported matrix units do not admit a fixed choice of a generator on each line. The theorem is a further sufficient case of the polynomial-in-rank clause of Question 7.1.
