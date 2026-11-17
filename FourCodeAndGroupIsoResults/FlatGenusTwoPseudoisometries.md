# Automorphisms and central quotients of a flat genus-two group

Let $K=\mathbb F_{p^e}$, $q=p^e$, and let $H=H^{\flat}_1(K)$ be Schrock's flat genus-two group, with $p$ odd as in Chapter 4 of his thesis. We determine the pseudo-isometry group of its commutator bimap and prove that its central quotients are isomorphic exactly when their kernels lie in the same orbit under $\operatorname{Aut}(H)$. The first result disproves Conjecture 4.4.4.3, and the second proves Conjecture 4.4.4.1 as stated. Both arguments are informal. [Schrock, §4.4.4, printed p. 107](https://math.colorado.edu/~tysc3584/Tyler_Schrock-PhD_Thesis.pdf#page=118)

## 1. The commutator bimap

Write $V=K\oplus K^2$ and $P=K^2$. In coordinates $(s,u)=(e_1,(f_0,f_1))$ the two components of Schrock's flat commutator formula give
$$
 b((s,u),(t,v))=sv-tu.
$$
It is surjective and its radical is zero. In particular the center and derived subgroup of $H$ coincide with $P$, and the abelianization identifies with $V$. Use the Baer coordinates $(x,z)\in V\oplus P$ with product $(x,z)(y,w)=(x+y,z+w+b(x,y)/2)$. The change from the original upper triangular coordinates subtracts half the diagonal value of the old bilinear multiplication cocycle from the center coordinate, and acts identically on the center. [Schrock, §§4.2.1 and 4.3](https://math.colorado.edu/~tysc3584/Tyler_Schrock-PhD_Thesis.pdf#page=94)

## 2. Exact pseudo-isometry group

A pseudo-isometry is a pair of invertible $\mathbb F_p$-linear maps $(g,h)$ on $V,P$ with $b(gx,gy)=h(b(x,y))$. All are uniquely of the form
$$
 g(s,u)=(a\,s^\sigma,M u^\sigma+c\,s^\sigma),\qquad
 h(z)=a M z^\sigma,
$$
where $a\in K^\times$, $M\in\operatorname{GL}_2(K)$, $c\in K^2$, and $\sigma\in\operatorname{Gal}(K/\mathbb F_p)$ is applied coordinatewise.

For $s\ne0$, evaluation by $(s,u)$ has image $P$. For $s=0$ and $u\ne0$, its image is $Ku$, of $\mathbb F_p$-dimension $e$. Thus $g$ preserves $0\oplus K^2$. Write $g(s,u)=(A(s),B(u)+C(s))$ with $A,B$ invertible and $C$ linear over $\mathbb F_p$. The pseudo-isometry equation on $(s,0),(0,v)$ gives $h(sv)=A(s)B(v)$. Set $a=A(1)$, nonzero. Then $h=aB$, and with $\sigma(s)=A(s)/a$ we have $B(sv)=\sigma(s)B(v)$. Evaluating on a nonzero $v$ shows $\sigma(st)=\sigma(s)\sigma(t)$. Additivity, bijectivity and $\sigma(1)=1$ give a field automorphism, so $B(u)=M u^\sigma$ for some $M\in\operatorname{GL}_2(K)$. The pair $(s,0),(1,0)$ gives $A(s)C(1)=aC(s)$, hence $C(s)=C(1)s^\sigma$. Conversely the displayed pair preserves the bimap because its two shear terms cancel. The $\sigma=1$ part of the group consists of invertible $K$-linear block matrices preserving the plane $0\oplus K^2$, with the action on $P$ fixed by $g$. Frobenius acts on their coefficients. The order is
$$
 q^2(q-1)|\operatorname{GL}_2(q)|e.
$$
Its $p$-adic valuation is $3e+v_p(e)$. The valuation of Schrock's proposed group's order, $|\operatorname{Sp}_2(q)|\,|\operatorname{GL}_2(p)|e$, is $e+1+v_p(e)$, since $\operatorname{Sp}_2(q)=\operatorname{SL}_2(q)$ has order $q(q^2-1)$. These valuations differ for every $e\ge1$.

Every such pair acts on $H$ by $(x,z)\mapsto(gx,hz)$ in Baer coordinates. An automorphism inducing identity on $V$ and $P$ has form $(x,z)\mapsto(x,z+\mu(x))$ for $\mu\in\operatorname{Hom}_{\mathbb F_p}(V,P)$, by comparing products. Thus this Hom group, of order $p^{6e^2}$, is the kernel and the displayed action splits the projection to the pseudo-isometry group. In particular the induced action on $P$ is exactly $\Gamma\operatorname{L}_2(K)$.

## 3. The dual forms of a central quotient

For an arbitrary central subgroup $N\le P$, put $S=N^\perp\subset K^2$ using the perfect $\mathbb F_p$-pairing $(w,z)\mapsto\operatorname{Tr}_{K/\mathbb F_p}(w^\mathsf T z)$. The derived group of $H/N$ is $P/N$, and its abelianization is still $V$, including when the center has grown. The commutator bimap on these two characteristic quotients gives the family of alternating scalar forms
$$
 \omega_{(a,b)}((s,u),(t,v))
 =\operatorname{Tr}\left(s(av_1+bv_2)-t(au_1+bu_2)\right),\quad (a,b)\in S.
$$
An isomorphism of $H/N$ and $H/N'$ supplies a linear bijection $g:V\to V$ and a linear bijection $\theta:S\to S'=N'^\perp$ such that
$$
 \omega_w(x,y)=\omega_{\theta(w)}(gx,gy)\quad(w\in S).
$$
The radical of any nonzero $\omega_{(a,b)}$ is $\{(0,u):au_1+bu_2=0\}$. This follows by first varying $v$ and then varying $t$, using the nondegenerate trace pairing. Two nonzero forms have the same radical precisely when their weights are $K$-collinear. In particular $\theta$ takes any $K$-independent pair of weights to a $K$-independent pair.

## 4. Recover a semilinear transporter

Suppose first that $S$ spans $K^2$ over $K$. Choose two $K$-independent weights in $S$. Change coordinates separately on each side so that the chosen pair and its matched pair in $S'$ are both the two standard coordinate vectors. A change of weight coordinates by any element of $\operatorname{GL}_2(K)$ is realized by the inverse-transpose change on the $u,v$ coordinates in the scalar forms. These changes preserve the existence of the desired semilinear transporter.

The radicals of the marked forms are the two distinct coordinate lines of $0\oplus K^2$. The map $g$ preserves both. On $V/(0\oplus K^2)$ it has some $\mathbb F_p$-linear action $A$, and on the two coordinate lines it has invertible $\mathbb F_p$-linear actions $B_1,B_2$. Evaluating the two marked form equalities on $(s,0)$ and a vector on the relevant coordinate line gives $\operatorname{Tr}(A(s)B_i(u))=\operatorname{Tr}(su)$. Therefore $B_1=B_2=B=(A^*)^{-1}$, with $A^*$ the trace adjoint. The shear from $K$ to $K^2$ has no effect on either equality.

Let $m_a$ denote multiplication by $a$ on $K$. For any $(a,b)\in S$ with match $(a',b')=\theta(a,b)$, the same evaluations give
$$
 m_{a'}=B m_aB^{-1},\qquad m_{b'}=B m_bB^{-1}.
$$
Consequently conjugation by $B$ identifies the two subfields of scalar multiplication operators generated over $\mathbb F_p$ by all these coordinates. Each such algebra is a finite integral domain and hence a field. The fields have equal order, so they are the same subfield of $K$ in scalar coordinates. The induced field automorphism extends to $\sigma\in\operatorname{Gal}(K/\mathbb F_p)$, since every automorphism of a subfield is a power of the prime-field Frobenius. Thus $\theta(a,b)=(a^\sigma,b^\sigma)$ in the normalized coordinate systems. Undoing the basis changes gives a semilinear transporter $S\to S'$.

If the $K$-span of $S$ has dimension one, the radical test forces the same for $S'$. Match one nonzero weight and normalize both to $(1,0)$. Write all weights as $(a,0)$ and $(a',0)$, and quotient $V$ by the common radical. On the resulting $K^2$ with coordinates $(s,u_1)$, the form at weight $1$ is nondegenerate by the trace pairing. The endomorphism $T_a$ defined by $\omega_{(a,0)}(x,y)=\omega_{(1,0)}(T_ax,y)$ is scalar multiplication by $a$ on both coordinates. The induced isomorphism conjugates $T_a$ to $T_{a'}$. The same generated-subfield argument gives a common Frobenius automorphism on all weights. If $S=0$, then also $S'=0$, and their kernels equal $P$.

In all cases the semilinear transporter of the dual spaces yields a semilinear transporter $N\to N'$ on $P$. Explicitly, for a map $w\mapsto Lw^\sigma$ from $S$ to $S'$, send $z\mapsto L^{-\mathsf T}z^\sigma$. The trace pairing is preserved because trace is Frobenius-invariant. Section 2 lifts this map on $P$ to an automorphism of $H$, proving the forward implication of Conjecture 4.4.4.1. Any automorphism taking $N$ to $N'$ induces an isomorphism of the quotients, proving the reverse implication.

## 5. A polynomial-time test from raw Cayley tables

There is a deterministic polynomial-time isomorphism test on pairs of promised central quotients in this family. The tables need not supply a covering group, a kernel, or coordinates over $K$. The same algorithm handles two groups with initially unspecified primes and extension degrees. An isomorphic pair has the same prime and abelianization size, which fixes $e$ by $|V|=p^{3e}$.

First compute the derived and abelianization tables by generating the subgroup of all commutators and passing to cosets. Compute $\mathbb F_p$-bases of these elementary abelian groups by extending a basis whenever a scanned element is outside its current span. The resulting coordinates give the dual space of scalar forms from commutator evaluation on basis elements. There are $|G'|$ forms, so they can all be enumerated at polynomial cost in the table size. If the two form spaces have different dimensions, reject. Dimension zero gives elementary abelian groups, whose orders decide isomorphism.

If all nonzero forms have the same radical, pick one nonzero form on the source and try every nonzero target form as its match. Reject if only one of the inputs has this common-radical property. Divide each form by the marked form on the common radical quotient, using the operators $T_a$ of Section 4. This produces an operator space on that quotient. Its generated $\mathbb F_p$-algebra is a field of order at most $q$. The two operator spaces match if some $\mathbb F_p$-isomorphism between their generated fields takes one operator space onto the other.

Otherwise pick two source forms with distinct radicals and try every ordered target pair with distinct radicals. In each input write the radicals as $R_1,R_2$, set $U=R_1\oplus R_2$, and set $X=V/U$. Call the marked forms $\omega_1,\omega_2$. The form $\omega_1$ gives a perfect pairing between $X$ and $R_2$, and $\omega_2$ gives a perfect pairing between $X$ and $R_1$. Indeed in the normalized cover coordinates these are the two trace pairings. Every form vanishes on $U\times U$, so these cross pairings and the analogous pairings from every $\omega$ descend to $X$ regardless of the chosen representatives. Define two endomorphisms $T^1_\omega,T^2_\omega$ of $X$ by
$$
 \omega(x,y)=\omega_1(T^1_\omega x,y)\quad(y\in R_2),\qquad
 \omega(x,z)=\omega_2(T^2_\omega x,z)\quad(z\in R_1).
$$
They are obtained by solving linear equations over $\mathbb F_p$. In the normalized coordinates they are multiplication by the two coordinates of the weight of $\omega$. Generate the field algebra from all operators in the two coordinates. Test whether an $\mathbb F_p$-isomorphism of the two resulting fields takes the space of ordered operator pairs onto the corresponding target space, acting with the same field isomorphism in both coordinates.

These field calculations take polynomial time. Multiplicative closure of a linear basis inside the operator matrix algebra needs at most the square of the matrix dimension many independent additions. Each generated field has at most $q$ elements. Compare the field dimensions, then enumerate the elements of the source field to find a generator over $\mathbb F_p$ by testing the spans of powers. Try each root of its minimal polynomial in the comparison field as its image. Every root defines an isomorphism because the two field dimensions agree. For each isomorphism, compare the image spaces by linear algebra. There are at most $|G'|^2$ marked-pair trials and $q\le |G|$.

An isomorphism of the groups supplies a successful trial and conjugates the relative operators as in Section 4. Conversely a successful field comparison extends to a Frobenius map on $K$ in the normalized coordinate systems. It maps the resulting weight spaces onto each other. Undoing normalization gives the semilinear transporter that lifts to a group isomorphism. This is a separate raw-table algorithm for the promised family.

## 6. Central quotients of larger flat blocks

For every $m\ge1$, the central-quotient lifting theorem also holds for $H^{\flat}_m(K)$, and the raw Cayley-table algorithm extends to pairs of promised central quotients of these larger blocks. The flat commutator formula uses $V=E\oplus U=K^m\oplus K^{m+1}$, with coordinates $e_1,\ldots,e_m$ and $f_0,\ldots,f_m$. If $J_1,J_2:U\to K^m$ extract the first and last $m$ coordinates, its two components are
$$
 b_i((e,f),(e',f'))=e^{\mathsf T}J_i f'-(e')^{\mathsf T}J_i f.
$$
Each nonzero scalar slice has $\mathbb F_p$-radical dimension $[K\colon\mathbb F_p]$. Indeed its $K$-radical is $0\oplus\ker(aJ_1+bJ_2)$, and the $m$ equations $af_{i-1}+bf_i=0$ are independent for $(a,b)\ne(0,0)$. Independent weights have radicals with zero intersection, by solving the two equations at each $i$. This gives the same radical test for collinearity as in Section 3.

Every $K$-linear coordinate change on the output lifts to a pseudo-isometry of the original bimap. One construction uses a two-dimensional $K$-space $L$, regards $E$ as $\operatorname{Sym}^{m-1}(L)$, regards $U$ as $\operatorname{Sym}^m(L)^*$, and takes the output to be $L^*$. For $r\in L$, the output of $((e,f),(e',f'))$ evaluated at $r$ is $f'(re)-f(re')$. The monomial bases give exactly the two coordinate slices above. Applying the changes of basis induced by $D\in\operatorname{GL}(L)$ on $E$ and $U$ changes the output by the inverse dual of $D$. Coordinatewise Frobenius lifts as well, because the bimap has prime-field coefficients. All pairs lift to group automorphisms using the Baer product. We may therefore normalize a matched independent pair of weights to $(1,0),(0,1)$ on both sides.

For the two normalized scalar forms $\omega_1,\omega_2$, let $\alpha_i:V\to V^*$ be the map $v\mapsto\omega_i(v,-)$ over $\mathbb F_p$. Recover the suffix flag on the $f$-coordinates by starting at $R_0=\ker\alpha_1=K f_m$ and setting $R_{j+1}=\alpha_1^{-1}(\alpha_2(R_j))$. Here $K f_i$ means the line spanned by the $i$-th coordinate vector. The formula gives $R_j=K f_{m-j}\oplus\cdots\oplus K f_m$ for $0\le j\le m$. This follows because $\alpha_2$ takes the current suffix to the matching suffix of the dual $e$-coordinates, and $\alpha_1$ takes its preimage back to the suffix starting one position earlier. Swapping the two forms gives the prefix flag. The two flags recover $U$ and each coordinate line $K f_i$ by intersection.

A prime-field isomorphism of the normalized form pairs preserves both flags. Write $B_i$ for its action on $K f_i$ and $A$ for its action on $V/U$. For $1\le i\le m$, the $\omega_1$ pairing with $K f_{i-1}$ depends exactly on the $i$-th coordinate of $V/U$. Preservation of that pairing forces the $i$-th component of $A$ to depend only on that coordinate and to equal $(B_{i-1}^*)^{-1}$ there. To see the dependence, pair a vector with zero $i$-th component against every vector of $K f_{i-1}$, then apply the nondegenerate trace pairing and surjectivity of $B_{i-1}$. The $\omega_2$ pairing with $K f_i$ gives $(B_i^*)^{-1}$ for the same component. Thus every $B_i$ is a common map $B$ and every diagonal coordinate of $A$ is $(B^*)^{-1}$. Evaluating any additional form $\omega_{(a,b)}$ on $(e_i,f_{i-1})$ and $(e_i,f_i)$ separately now gives the same two scalar conjugation equations as in Section 4. The resulting common Frobenius map transports the weight space. For a collinear space, divide by a normalized marked nondegenerate form on the quotient by its radical. The resulting endomorphisms on $K^{2m}$ are again scalar multiplications. This proves the kernel orbit classification, including the zero weight space.

To implement the raw-table test, recover $e=[K\colon\mathbb F_p]$ from the dimension of the radical of any nonzero scalar form and $m$ from $\dim_{\mathbb F_p}V=(2m+1)e$. With no nonzero scalar forms, test the orders of the elementary abelian groups directly. For a trial matched pair of independent weights, compute the two flags by prime-field linear algebra. On $X=V/U$, pair with $K f_0$ and $K f_m$ using $\omega_1$ and $\omega_2$, respectively. Their kernels on $X$ remove all but the first and last coordinates, respectively. Every form has the same vanishing on these kernels. The maps dividing each form's pairing by the corresponding marked pairing are thus endomorphisms of the two $e$-dimensional quotients of $X$. They give the actions of $a$ and $b$ as before. For the two representations of the generated scalar fields to use one common coordinate, one can transport operators from the last quotient to the first using the chain of trace pairing identifications. Concretely, for each $i$ the $\omega_1$ pairing with $K f_{i-1}$ and the $\omega_2$ pairing with $K f_i$ identify the duals of these two lines through their common $i$-th quotient of $X$. Compose these $m$ identifications. In the normalized cover coordinates the resulting identification of the endpoint quotients is the identity of $K$. Thus the two operators for every weight are now matrices on one space, and the field comparison algorithm of Section 5 applies. A successful field comparison again extends to a Frobenius map of $K$ and yields a lift.

Computing flags, quotient pairings and the identifications adds only a polynomial number of linear-algebra operations. The counts of candidate marked pairs and field sizes remain bounded by the original group orders. This treats the isomorphism-testing task for larger flat blocks raised in the thesis. It gives a separate algorithm from the one outlined in the thesis. [Schrock, §§4.3 and 4.5](https://math.colorado.edu/~tysc3584/Tyler_Schrock-PhD_Thesis.pdf#page=119)

## 7. Prior work and scope

Brooksbank, Maglione and Wilson's Proposition 5.3 gives the surjection of the pseudo-isometry group of an indecomposable flat pencil onto $\Gamma\operatorname{L}_2(K)$. The computation above identifies its entire kernel and multiplication action in the smallest flat block. The quotient argument uses its scalar-form radicals and applies to arbitrary central subgroups, including those that enlarge the quotient center. Targeted searches for Schrock's two conjectures and for flat genus-two quotient lifting found the original thesis and the genus-two pseudo-isometry algorithms. Publication priority is unestablished. [Brooksbank, Maglione and Wilson, *A fast isomorphism test for groups of genus 2*, Proposition 5.3](https://joshmaglione.com/papers/Genus2.pdf#page=23) · [Schrock, §4.4.4](https://math.colorado.edu/~tysc3584/Tyler_Schrock-PhD_Thesis.pdf#page=118)
