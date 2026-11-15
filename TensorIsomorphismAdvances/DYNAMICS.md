# Tensor isomorphism within single quadratic Hamiltonian shears

**Theorem.** Over every field, ordered three-tensor isomorphism is equivalent under polynomial-time many-one reductions to ordinary polynomial conjugacy on an explicit family of quadratic symplectic shears
$$
       F_T(q,p)=(q,p+\nabla H_T(q)).
$$
The polynomials $H_T$ are homogeneous cubics with squarefree monomials. The phase space dimension grows linearly in the sum of the input mode dimensions. Every iterate has degree at most two. In characteristic $p>0$, the maps have exact order $p$, in particular order two even over $\mathbb F_2$. Their linear part at the origin is the identity. Every positive instance has a linear symplectic conjugator, even when the decision problem allows arbitrary nonlinear polynomial conjugators. In characteristic zero each output is the time-one map of a Hamiltonian shear that is linear in time.

All equalities are formal polynomial identities, including over finite fields. The reductions use polynomially many field operations and equality tests, and have the usual polynomial bit bounds for explicitly presented finite fields or rational inputs. This is an informal proof.

## Preprocessing and notation

View $T:X\times Y\longrightarrow Z$ as a bilinear map. Pass to the concise core by quotienting each input by its common kernel and restricting the output to the span of values. These operations are computable by linear algebra. At equal original input formats, a core equivalence lifts to the original format by extending the three maps along the unused complements. If the core formats differ the answer is negative. Test zero cases directly. Fixed positive and negative output pairs of nonzero cores are available. For a negative pair take the two concise $2\times2\times2$ pencils with slices $I,\operatorname{diag}(1,0)$ and $I,E_{12}$, whose determinant polynomials have different numbers of distinct projective zeros. Thus every tensor used in the construction below can be assumed nonzero and concise.

Write $G(b,c)=\sum_i b_i c_i$ for a standard hyperbolic quadratic polynomial on an auxiliary even-dimensional space, using separate blocks $b,c$. Its bilinear polarization is $G(d+d')-G(d)-G(d')$ and is nondegenerate in every characteristic. For a homogeneous quadratic map $Q$, write $\beta_Q$ for the corresponding bilinear polarization.

## 1. A quadratic map whose polarization remembers the tensor

Set $U=X\oplus Y\oplus X^*\oplus D$, with $D$ auxiliary hyperbolic of dimension $2r>\dim X+\dim Y$. Set $W=Z\oplus k$ and
$$
        Q_T(x,y,a,d)=(T(x,y),a(x)+G(d)).
$$
Its polarization $\beta_T$ has zero common radical and spans $W$. The first statement follows from the marker form, whose radical is $Y$, and concision in $Y$. The second follows from the payload on $X,Y$ and the marker on $D$. A tensor transporter extends to an equivalence of the quadratic maps themselves, acting on $X^*$ by the inverse transpose of the action on $X$, and as the identity on $D$ and on the scalar marker output.

Conversely, suppose the polarizations are equivalent through invertible maps on $U,W$. In the slice space $\{\ell\beta_T : \ell\in W^*\}$, the subspace of payload slices is exactly the slices of rank at most $(\dim U)/2$. Payload rank is at most $\dim X+\dim Y<(\dim U)/2$. A nonzero marker coefficient gives rank at least $2\dim X+2r>(\dim U)/2$ by restriction to $X\oplus X^*\oplus D$. The common radical of the payload slices is $K=X^*\oplus D$, by concision in $X,Y$. The radical of every slice with nonzero marker coefficient projects onto the same subspace $Y\subset U/K$. Indeed testing against the $X^*$ and $D$ blocks forces the $X,D$ components of a radical vector to vanish. Testing against $X$ then determines its $X^*$ component uniquely from its $Y$ component, and the remaining equations hold. Thus the equivalence preserves $Y\subset U/K$. Polarizing on a vector from $X$ and a vector from $Y$ now recovers precisely $C T(x,y)=T'(A x,B y)$, with invertible maps $A,B$ induced by the filtration $Y\subset U/K$ and $C$ induced by the payload output quotient. This is the rank-marker mechanism of Grochow–Qiao, Theorem 2.1, with a quadratic refinement that the forward maps preserve. [Grochow–Qiao IV](https://arxiv.org/html/2306.16317v2#S2)

## 2. A cubic whose polarization remembers the quadratic map

Put $V=U\oplus W^*\oplus U^*\oplus D'\oplus kg$, where $D'$ is auxiliary hyperbolic of dimension strictly larger than $\dim U+\dim W+2$. Denote its quadratic form by $G'$, and let the $g$-coordinate be $s$. Define
$$
         H_{0,T}(u,z,a,d,s)=z(Q_T(u))+s(a(u)+G'(d)).
$$
Here and below the homogeneous cubics have squarefree monomials in the displayed separate blocks. Write $t_0$ for the third polarization of $H_{0,T}$, given by the alternating sum of values over subsets of the three arguments. It is symmetric trilinear in every characteristic, and for the displayed squarefree cubics it is alternating in characteristic two. Its restriction to the hyperplane $E$ with $s=0$ is the trilinear form with two $U$ arguments and one $W^*$ argument given by $z(\beta_T(u,u'))$, extended symmetrically and zero on other pure-block triples. Contraction with $g$ restricted to $E$ is the bilinear form pairing $U,U^*$ and carrying the hyperbolic form on $D'$.

The hyperplane $E$ is intrinsic to $t_0$. For a vector in $E$, its contraction has rank at most $\dim U+\dim W+2<(\dim V)/2$. The first contribution is supported on $U\oplus W^*$, and the $g$-row and column can raise rank by at most two. For a vector with nonzero $g$-coefficient the contraction restricted to $U\oplus U^*\oplus D'$ has rank $2\dim U+\dim D'>(\dim V)/2$: the hyperbolic pairing is nondegenerate after adding a term on $U$ alone. Thus the rank threshold is the same for all templates having the same ambient dimension. The radical of $t_0|_{E^3}$ is $K'=U^*\oplus D'$ because $\beta_T$ has common radical zero and spans $W$. For any vector $v$ outside $E$, the radical of $t_0(v,-,-)|_{E^2}$ projects onto $W^*\subset E/K'$. To see this, test a radical vector against $U^*,D'$ to force its $U,D'$ components to vanish. Testing against $U$ determines its $U^*$ component uniquely from its $W^*$ component. The $W^*$ equations then hold. Thus this projected subspace is independent of $v$. The trilinear restriction has zero terms with two entries in $W^*$, so it gives a well-defined pairing on two copies of the quotient $(E/K')/W^*$ and one copy of $W^*$. This recovers $\beta_T$ up to the two simultaneous basis changes. All of the recovery works for proportional trilinear forms as well. A forward equivalence of $Q_T$ extends to exact polynomial equivalence of $H_{0,T}$ by the inverse-transpose actions on $W^*,U^*$ and identity on the new marker blocks. This uses the rank-marker idea of Grochow–Qiao, Theorem 6.1, with a direct calculation of the radicals. [Grochow–Qiao IV](https://arxiv.org/html/2306.16317v2#S6.SS1)

## 3. A linear-size extension with scalar centroid

On $B=V\oplus V^*\oplus kh$, define the cubic
$$
      H_T(v,b,\tau)=H_{0,T}(v)+\tau b(v).
$$
Let $t$ be its third polarization. On $M=V\oplus V^*$ it is $t_0$ extended by zero. Its contraction with $h$ on $M$ is the nondegenerate symmetric hyperbolic pairing $\omega((v,b),(v',b'))=b(v')+b'(v)$. All terms with two $h$ arguments vanish. The hyperplane $M$ is intrinsic: contractions by elements of $M$ have rank at most $\dim V+2$. If $a\ne0$, the restriction of the contraction by $u+a h$ to $M$ has block matrix
$$
            \begin{pmatrix}C&aI\\aI&0\end{pmatrix},
$$
which is invertible, of rank $2\dim V>\dim V+2$. The radical of $t$ itself is zero, since every nonzero $u\in M$ pairs nontrivially with $h$ and some vector of $M$. Also $t_0$ has zero radical: a radical vector first lies in $E$ by the rank test, then lies in $K'$ by the restriction, and contracting with $g$ shows it is zero. Consequently $M/\operatorname{rad}(t|_{M^3})$ recovers $V,t_0$. A similitude of $t$ therefore recovers a tensor transporter by the first two sections.

The centroid of a symmetric trilinear form consists of endomorphisms $A$ satisfying
$$
        t(Au,v,w)=t(u,Av,w)=t(u,v,Aw)
$$
for every $u,v,w$. The centroid of $t$ is exactly the scalars. To prove this, first write $Au=Pu+\lambda(u)h$ on $M$. Compare $t(Ab,b',v)=t(b,Ab',v)$ with $b,b'\in V^*,v\in V$. This gives $\lambda(b)b'(v)=\lambda(b')b(v)$. As $\dim V\ge3$, take two independent covectors to deduce $\lambda|_{V^*}=0$. Then compare $t(Av,v',b)=t(v,Av',b)$ with $v,v'\in V,b\in V^*$. This gives $\lambda(v)b(v')=\lambda(v')b(v)$, so $\lambda|_V=0$. Next write $Ah=u_0+ch$. The identity $t(Ah,h,u)=t(h,h,Au)=0$ forces $\omega(u_0,u)=0$ on $M$, hence $u_0=0$. Finally $t(Au,h,u')=t(u,Ah,u')$ gives $\omega(Pu,u')=c\omega(u,u')$, so $P=cI$. This proves the centroid claim with no characteristic restrictions.

Forward polynomial equivalence of $H_{0,T}$ extends to $H_T$ by the inverse-transpose action on $V^*$ and identity on $kh$.

## 4. Shear dynamics and reflection through arbitrary conjugators

Set $R_T(q)=dH_T(q)\in B^*$ in the displayed bases, and $F_T(q,p)=(q,p+R_T(q))$. On the phase space $B\oplus B^*$ the kick preserves the canonical symplectic form because the Hessian of $H_T$ is symmetric. It has inverse $F_T^{-1}(q,p)=(q,p-R_T(q))$, and its $m$-th integer iterate adds $mR_T(q)$ to $p$. Its gradient is nonzero by the term $\tau b(v)$ on disjoint blocks. Thus its order in characteristic $p>0$ is exactly $p$. In characteristic zero the same formula in a scalar parameter gives the Hamiltonian flow, with the sign of the Hamiltonian chosen to match the convention for the canonical form. A linear map $A:B\to B'$ satisfying $H_T=H_{T'}\circ A$ lifts by $A\oplus A^{-T}$ to a linear symplectic conjugator.

For reflection, let $\Phi$ be an arbitrary polynomial conjugacy. Its value $b$ at the origin is a fixed point of $F_{T'}$, where the derivative of $F_{T'}$ must be the identity by the chain rule and invertibility of $D\Phi(0)$. Hence $R_{T'}(b_q)=0$ and $dR_{T'}(b_q)=0$. Expanding the homogeneous quadratic map gives $R_{T'}(q+b_q)=R_{T'}(q)$. Translation by $b$ therefore commutes with $F_{T'}$. Compose $\Phi$ with the inverse translation so that it fixes the origin.

Since the linear parts of the two shears are the identity, the homogeneous quadratic terms of $\Phi$ cancel in the conjugacy equation. The derivative $L=D\Phi(0)$ satisfies
$$
           L(0,R_T(q))=(0,R_{T'}(\operatorname{pr}_{B'}L(q,p)))
$$
for all $(q,p)$, as a polynomial identity. The values of $R_T$ span $B^*$, because its polar values span $B^*$. Indeed the polar is dual to $t$, and any annihilator of its values would be in the radical of $t$. Polar values are linear combinations of values of $R_T$, including over the smallest field. Therefore $L$ sends $0\oplus B^*$ onto $0\oplus B'^*$. Its induced quotient and vertical maps $A:B\to B'$ and $C:B^*\to B'^*$ are invertible and satisfy $C R_T(q)=R_{T'}(Aq)$.

Polarizing the gradient gives the third polarization of the squarefree cubic, so the last identity implies
$$
      t'(Au,Av,Aw)=t(u,v,Jw),\qquad J=(A^*C)^*.
$$
The left side is symmetric. By permuting its entries we deduce that $J$ lies in the centroid of $t$. By Section 3 it is a nonzero scalar. Thus $A$ is an exact similitude of the displayed polar forms, and the intrinsic rank and radical recoveries of Sections 1–3 return a tensor transporter over the original field. This uses only arbitrary polynomial conjugacy, with no assumption about the conjugator preserving the symplectic form.

The dimensions of $U,W,V,B$ are all linear in $\dim X+\dim Y+\dim Z$ when the auxiliary even dimensions are chosen minimally. All formulas are explicit of degree at most three. Conversely the displayed template can be given with its mode dimensions, and reading the coefficients of the original payload from the gradient gives a polynomial reverse reduction. Testing the template itself and extracting its mode dimensions is also polynomial, by reading or trying the candidate dimensions and evaluating the formula. The target consists of these coordinate templates.

These maps all commute within any one phase space. The same reflection proof works for formal conjugacy germs at the origin, and for conjugating $C^2$ germs over the reals at fixed points, since only derivatives through order two enter the argument. In positive characteristic the order is minimal among nontrivial finite-order maps tangent to the identity at a fixed point. Indeed for such a map with first nonlinear homogeneous term $P$ the corresponding term of its $m$-th iterate is $mP$, so its order is divisible by $p$. The linear dimension bound is asymptotically optimal for an objectwise orbit-preserving reduction over a fixed finite field: cubical side-$n$ input has at least $q^{n^3-3n^2}$ orbits, and cubic shears in $D$ phase coordinates have at most $q^{O(D^3)}$ possible coefficient arrays.

## 5. Fixed-degree form equivalence in small characteristic

There is also a direct membership theorem for homogeneous form equivalence. Fix a positive degree $d$. For a degree-$d$ homogeneous polynomial $f$ in the symmetric algebra of $L$, give the linked tensor system of multiplication maps
$$
          L\otimes \operatorname{Sym}^{i-1}L\ \longrightarrow\
          \operatorname{Sym}^{i}L \qquad (2\le i\le d)
$$
and the specified vector $f\in\operatorname{Sym}^{d}L$. A system isomorphism with first map $A:L\to L'$ has forced maps $\operatorname{Sym}^{i}(A)$ on each other space, by induction and surjectivity of multiplication. Thus it preserves the vector precisely when it implements ordinary equivalence of $f$. The system has fixed signature for fixed $d$, its monomial bases and maps are explicit, and its dimensions are polynomial in the original number of variables. Futorny–Grochow–Sergeichuk Theorem 1.1 compiles it to one 3TI pair. This proves membership over every field, including in characteristics two and three. It bypasses the invertibility of $d!$ required by the direct polarization route. Grochow–Qiao I already gives cubic-form hardness and records the characteristic restriction on its membership proof in the footnote to Corollary B. [Systems of tensors](https://arxiv.org/html/1810.09219v2) · [Grochow–Qiao I](https://arxiv.org/html/1907.00309)

The cubics $H_T$ above give a linear-variable hardness construction that also works when forms are compared only up to a scalar. They are geometrically irreducible. Viewed over the polynomial ring in $v,\tau$, the polynomial $H_{0,T}(v)+\tau\sum_i b_i v_i$ is primitive and linear in the $b_i$. Indeed the greatest common divisor of the nonconstant coefficients is $\tau$, which does not divide $H_{0,T}$. Gauss's lemma then applies over every field extension. For each $d>3$, multiply $H_T$ by $z^{d-3}$ in a fresh variable. A linear equivalence of the resulting polynomials must match their unique irreducible cubic factors up to scalar. Those cubic factors have full essential-variable dimension in their original variables, since their polarized form has zero radical. Cancelling the unused variable recovers a cubic similitude, and the rank recovery proves ordinary TI of the payloads. The forward direction extends by fixing $z$. Thus fixed-degree form equivalence is TI-complete for all $d\ge3$ over every field. The hardness argument owes the degree-raising step to Grochow–Qiao's Appendix A. [Appendix A](https://arxiv.org/html/1907.00309#A1)

## Context and scope

The original dynamics construction used three Jordan lengths and had exact order eight in characteristic two. The present shears have identity derivative, linear time dependence, and the smallest possible nontrivial order in characteristic two. The rank tags are closely related to the cited Grochow–Qiao linear-length gadgets. The additional step is the scalar-centroid extension that turns a general first-jet left–right gradient equivalence into a trilinear similitude. The earlier MathProofs dynamics proof supplies the fixed-point and jet strategy. Federated DAG probes on symplectic forms, polarization, rank, centroid, covariants, symmetric powers, radicals and conjugacy each queried 103 registered catalogs with a successful lookup. The proof is self-contained apart from the explicitly cited tensor-system compiler in the form-equivalence corollary. Publication priority for the stated arbitrary-conjugacy theorem remains unestablished. [Prior dynamics proof](https://github.com/Dugongue/MathProofs/blob/main/FurtherIsomorphismTransfers/DIFFERENTIAL.md) · [Centers of multilinear forms](https://arxiv.org/abs/2110.07915) · [Hamiltonian flows with straight-line orbits](https://arxiv.org/abs/1304.3377)

Exact finite controls replayed 120 contraction-rank tests for the two cubic marker hyperplanes over each of F₂, F₃ and F₅. These are controls for the calculations, while the proof applies to all inputs and fields.
