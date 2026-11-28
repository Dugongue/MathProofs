# Exact \(\mathrm{SL}_2\) charts at dense \(\mathrm{SU}_2\) representations

Kapovich–Millson Corollary 1.4 realises every finite-type affine \(\mathbb Q\)-scheme germ in an \(\mathrm{SL}_2\)-representation scheme of a closed 3-manifold group, at a representation with dense image in \(\mathrm{SU}_2\). The realisation is only up to a regular étale covering with deck group \(\mathbb Z_2^{k+r}\). Remark 1.5 records that the authors could not replace that covering by an isomorphism. [Kapovich–Millson, Corollary 1.4 and Remark 1.5](https://www.math.ucdavis.edu/~kapovich/EPR/char.pdf)

[ExactChart.md](ExactChart.md) removed the covering in two settings:
- at a Zariski-dense base whose image contains unipotents (Theorem 1);
- in the compact case, but only when the lift torsor splits (Theorem 2).

The statements below remove it in the compact case for arbitrary input, with an explicit inverse. There are four ingredients:
- a rigid icosahedral frame;
- projective points encoded by Cayley vectors of free generators;
- projective lines encoded by order-three elements, whose unit normals are recovered by residual intersection instead of normalisation;
- von Staudt gadgets for addition and multiplication, in which every auxiliary is given by Cramer's rule.

**Notation.**
- Quaternions are written \(X=x_0+x\) with \(x\) pure, inside \(M_2(\mathbb C)\) via \(i\mapsto\operatorname{diag}(i,-i)\), \(j\mapsto\begin{pmatrix}0&1\\-1&0\end{pmatrix}\), \(k\mapsto\begin{pmatrix}0&i\\i&0\end{pmatrix}\).
- The determinant is the norm \(x_0^2+q(x)\), where \(q\) is the sum of squares.
- On \(\mathrm{SL}_2\), \(X^{-1}=\bar X\) and \(\langle X,Z\rangle:=\operatorname{Re}(X\bar Z)=x_0z_0+x\cdot z=\tfrac12\operatorname{tr}(XZ^{-1})\).
- All statements concern the functor on commutative \(\mathbb C\)-algebras \(R\), nonreduced ones included.

## The theorem

**Theorem.** Let \(X\) be a finite-type affine scheme over \(\mathbb Q\) and \(x\in X(\mathbb Q)\). There are:
- an open neighbourhood \(X'\subset X_{\mathbb C}\) of \(x\);
- a closed hyperbolic three-manifold \(M\);
- an integer \(k\ge0\);
- a representation \(\rho_0\colon\pi_1(M)\to\mathrm{SU}_2\) with dense image;
- a conjugation-invariant Zariski-open subscheme \(\mathcal R^\circ\subset\operatorname{Hom}(\pi_1(M),\mathrm{SL}_2)\) containing \(\rho_0\), with a conjugation-equivariant isomorphism
\[
\mathcal R^\circ\ \simeq\ X'\times\mathrm{SL}_{2,\mathbb C}^{\,k}\times\mathrm{PGL}_{2,\mathbb C},
\qquad \rho_0\mapsto(x,h_0,1),
\]
where \(h_0\in\mathrm{SU}_2^{\,k}\) is the fixed base value of the free generators (§5); left translation by \(h_0^{-1}\) normalises it to \(1\).

Conjugation acts trivially on \(X'\) and on the \(\mathrm{SL}_2^k\) coordinates, which are measured in the moving frame. It acts by left multiplication on \(\mathrm{PGL}_2\). The quotient chart on the character scheme is \(X'\times\mathrm{SL}_2^k\). Both directions of the isomorphism are given by explicit formulas below. The manifold \(M\) is nonorientable, as in ExactChart Theorem 1.

## 1. A rigid icosahedral frame

Let \(2I=\langle a,b,c\mid a^2=b^3=c^5=abc\rangle\) be the binary icosahedral group, with standard representation
\[
a=\tfrac12(\varphi^{-1}i+\varphi j+k),\qquad b=\tfrac12(1+i+j+k),\qquad c=-b^{-1}a^{-1},
\]
where \(\varphi=(1+\sqrt5)/2\). Its image is the group of 120 unit icosians, and \(\operatorname{tr}\rho_{\rm fr}(c)=\varphi\).

**Frame lemma.** The locus \(\mathcal C=\{\rho:\operatorname{tr}\rho(c)=\varphi\}\subset\operatorname{Hom}(2I,\mathrm{SL}_2)\) is open and closed. The map \(O\mapsto\Phi_O\circ\rho_{\rm fr}\) is an isomorphism \(\mathrm{SO}_3\simeq\mathrm{PGL}_2\to\mathcal C\). Here \(\Phi_O\) is the algebra automorphism of \(M_2(R)\) that fixes \(1\) and acts by \(O\) on the pure part. The inverse is linear in \(\rho\):
\[
O(\rho)_{nm}=-\tfrac1{120}\textstyle\sum_{g}\operatorname{tr}(e_m\rho_{\rm fr}(g)^{-1})\operatorname{tr}(e_n\rho(g)),\qquad e=(i,j,k).
\]

*Proof.*
- A homomorphism \(2I\to\mathrm{GL}_2(R)\) is a unital algebra map \(f\colon\mathbb C[2I]\to M_2(R)\).
- The central idempotents of \(\mathbb C[2I]\) cut \(R^2\) into projective pieces of locally constant rank. The only irreducibles of dimension at most two are the trivial one, \(V\) and \(V'\). So \(\operatorname{tr}\rho(c)\) is locally one of \(2,\varphi,1-\varphi\), and \(\mathcal C\) is open and closed.
- On \(\mathcal C\) the idempotent \(f(e_V)\) has trace \(2\), so it equals \(1\). Hence \(f\) factors through a unital map \(M_2(\mathbb C)\to M_2(R)\), which is an automorphism, and \(\operatorname{Aut}(M_2(R))=\mathrm{PGL}_2(R)\).
- The formula is Fourier inversion with the Schur relations. No localisation and no square root occur. \(\square\)

**Normalised coordinates.** For further generators \(h\), set
\[
N_\rho(h)=\tfrac1{60}\textstyle\sum_g\operatorname{tr}(\rho(h)\rho(g))\,\rho_{\rm fr}(g)^{-1}.
\]
This is conjugation-invariant, multiplicative, and equal to \(\rho_{\rm fr}\) on \(2I\). Hence, for finitely presented \(\Gamma\supset 2I\),
\[
\operatorname{Hom}(\Gamma,\mathrm{SL}_2)|_{\mathcal C}\simeq\mathrm{PGL}_2\times\mathcal S,
\]
where \(\mathcal S\) is the slice with the frame fixed at \(\rho_{\rm fr}\). Every open condition below is a function of traces, hence invariant.

## 2. Points: Cayley vectors in a tangent plane

**Fixed traces.** For any word \(Y\), "\(Y^3=-1\) and \(\operatorname{tr}Y+2\in R^\times\)" is equivalent to \(\operatorname{tr}Y=1\).
- Cayley–Hamilton gives \(Y^3=(t^2-1)Y-t\), and taking traces gives \((t-1)^2(t+2)=0\).
- With \(\varepsilon=t-1\) this yields \(\varepsilon(2Y-1)=0\), and \(\det(2Y-1)=3-2\varepsilon\) is a unit.

Likewise "\(P^3=1\) and \(\operatorname{tr}P-2\in R^\times\)" is equivalent to \(\operatorname{tr}P=-1\). The element \(-1=a^2\) lies in \(2I\), so these are group relators.

**Cayley chart.** The map \(X\mapsto v=x/(1+x_0)\) is an isomorphism \(\{X\in\mathrm{SL}_2:1+x_0\in R^\times\}\to\{v\in\mathbb A^3:1+q(v)\in R^\times\}\), with inverse
\[
X=\frac{(1-q(v))+2v}{1+q(v)} .
\]
This is stereographic projection from \(-1\); real \(v\) give \(\mathrm{SU}_2\). If \(\operatorname{tr}P=-1\), so \(P=-\tfrac12+p\), then
\[
\langle X,P\rangle=\tfrac12 \iff -\tfrac12(1-q(v))+2\,v\cdot p=\tfrac12(1+q(v))\iff v\cdot p=\tfrac12 .
\]
The terms in \(q(v)\) cancel identically, so nothing depending on \(P\) is ever inverted.

**The plane.** Let \(P_1=\tfrac12(-1+i+j+k)\in2I\) and \(n_1=\tfrac12(i+j+k)\), so \(q(n_1)=\rho^2=\tfrac34\). Set
\[
\Pi=\{v:v\cdot n_1=\tfrac12\},
\]
the plane tangent to the sphere \(q(v)=\tfrac13\) at \(T_1=\tfrac23n_1\). Write \(v=T_1+s\,e_1+t\,e_2\) with \(e_1=(1,-1,0)\) and \(e_2=\tfrac16(1,1,-2)\).

A **point generator** \(X\) carries:
- the relator \((XP_1^{-1})^3=-1\);
- the opens \(1+x_0\in R^\times\) and \(\operatorname{tr}(XP_1^{-1})+2\in R^\times\).

These say exactly that \(v_X\in\Pi\). So point generators form an open subscheme of \(\mathbb A^2_{(s,t)}\).

## 3. Lines: order-three elements by residual intersection

A **line generator** \(P\) carries the relator \(P^3=1\) and the open \(\operatorname{tr}P-2\in R^\times\). So \(P=-\tfrac12+p\) with \(q(p)=\tfrac34\). Decompose \(p=a\,n_1+\alpha e_1+\beta e_2\) and put
\[
\gamma=\frac{1-a}{2}=\frac{2-\operatorname{tr}(PP_1^{-1})}{3}.
\]

**Line lemma.** On \(\{\gamma\in R^\times\}\), the map \(P\mapsto(A,B)=(p\cdot e_1/\gamma,\ p\cdot e_2/\gamma)\) is an isomorphism onto \(\{D:=4\rho^2+A^2/|e_1|^2+B^2/|e_2|^2\in R^\times\}\). Its inverse is
\[
\kappa=4\rho^2/D,\qquad a=1-2\kappa,\qquad \alpha=\kappa A/|e_1|^2,\qquad \beta=\kappa B/|e_2|^2 .
\]

*Proof.*
- One computes \(q(p)=\rho^2(1-2\kappa)^2+\kappa^2(D-4\rho^2)=\rho^2\).
- Conversely, \(\alpha^2|e_1|^2+\beta^2|e_2|^2=\rho^2(1-a^2)=4\rho^2\gamma(1-\gamma)\), and this returns \(\kappa=\gamma\).
- The tangent planes containing a line of \(\Pi\) are \(\Pi\) itself (\(\kappa=0\), \(P=P_1\)) and exactly one more, the residual one, given by the rational formula. \(\square\)

**Incidence.** Impose the relator \((XP^{-1})^3=-1\) with the open \(\operatorname{tr}(XP^{-1})+2\in R^\times\). By §2 this says \(v_X\cdot p=\tfrac12\). Since \(v_X\cdot p=a/2+s\,p\cdot e_1+t\,p\cdot e_2\), the condition is \(\gamma(As+Bt-1)=0\), that is,
\[
As+Bt=1 .
\]
So point and line generators realise exactly the affine incidence geometry of \(\Pi\). The only excluded objects are points at infinity and lines through \(T_1=(0,0)\).

Exact checks:
- reduced rational points: [checks/su2/w4_line_lemma_check.cpp](checks/su2/w4_line_lemma_check.cpp), 5823 tests, 0 failures;
- first-order deformations over \(\mathbb Q[\varepsilon]/\varepsilon^2\): [checks/su2/w3_dual_incidence_check.cpp](checks/su2/w3_dual_incidence_check.cpp), where incident pairs satisfy the relators exactly and \(\varepsilon\)-perturbed pairs fail at order \(\varepsilon\).

**Join and meet.** Let \(\Delta=s_1t_2-s_2t_1\). If \(\Delta\in R^\times\), the line generators incident with two point generators form exactly one \(R\)-point:
\[
A=\frac{t_2-t_1}{\Delta},\qquad B=\frac{s_1-s_2}{\Delta}.
\]
Similarly, let \(\Delta'=A_1B_2-A_2B_1\). If \(\Delta'\in R^\times\), the incident point of two lines is
\[
s=\frac{B_2-B_1}{\Delta'},\qquad t=\frac{A_1-A_2}{\Delta'}.
\]
In both cases a linear system with unit determinant has a unique solution over every \(R\). The condition \(\Delta\neq0\) says the join misses \(T_1\); \(\Delta'\neq0\) says the meet is finite.

**Why involutions cannot do this.**
- With trace-zero elements (the involutions of \(\mathrm{PO}_3\)), the planes pass through the origin.
- A line then lies in a unique such plane, and its unit normal must be normalised.
- That normalisation is the Kummer torsor of ExactChart's square-class test, and it is the source of the \(\mathbb Z_2^r\) in Kapovich–Millson Corollary 1.4.
- A nonzero trace provides the second, known tangent plane.

## 4. Arithmetic gadgets

**Constants.** All constants below are fixed elements of \(\Pi\) or of its dual, pinned by \(2I\). The constant lines are the lines \(L_P\) of the 18 order-three icosians \(P\neq P_1^{\pm1}\). The constant points are of two kinds:
- the icosians whose Cayley vector lies in \(\Pi\);
- meets of two constant lines, which are pinned by Cramer's rule.

Every further constant is a join or meet of earlier ones, with a nonzero constant determinant.

A configuration found by exact search over \(\mathbb Q(\sqrt5)\) is listed below ([checks/su2/w4_constant_frame_search_q5.cpp](checks/su2/w4_constant_frame_search_q5.cpp)). Coordinates are \((s,t)\); a line \(\lambda s+\mu t+1=0\) is written \([\lambda,\mu]\).

| object | value | provenance |
|---|---|---|
| \(L\) | \([0,\tfrac12]\), i.e. \(t=-2\) | Hurwitz icosian \(\tfrac12(-1-i-j+k)\) |
| \(M\) | \([\tfrac32,-\tfrac14]\) | Hurwitz icosian |
| \(N\) | \([-\tfrac32,-\tfrac14]\) | Hurwitz icosian |
| \(E\) | \((-1,-2)\) | on \(L\), \(M\) and three more constant lines |
| \(O\) | \((1,-2)\) | on \(L\), \(N\) and three more constant lines |
| \(U\) | \((0,-2)\) | on three constant lines (and the Cayley point of \(k\)) |
| \(A\) | \((\tfrac18(1+\sqrt5),\ \tfrac14(1-3\sqrt5))\) | meet of three constant lines |
| \(K\) | \(\operatorname{join}(E,A)=[\tfrac34-\tfrac9{20}\sqrt5,\ \tfrac18+\tfrac9{40}\sqrt5]\) | Cramer |
| \(U_1\) | \(\operatorname{meet}(\operatorname{join}(O,A),M)\) | Cramer |
| \(U_3\) | \(\operatorname{meet}(\operatorname{join}(U,A),M)\) | Cramer |

Here \(L\), \(M\) and \(K\) pass through \(E\); \(O,U\in L\); \(A\in K\); and \(N\ni O\).

**Encoding.** A value \(\xi\) is a point generator \(X\) incident with \(L\). Its coordinate is the projective coordinate on \(L\) with \(O\mapsto0\), \(U\mapsto1\), \(E\mapsto\infty\). Since \(L\) is \(t=-2\), this is the Möbius function \(\xi=(1-s)/(1+s)\) of the regular coordinate \(s\). It is regular and invertible on \(\{s+1\in R^\times\}\), with inverse \(s=(1-\xi)/(1+\xi)\), regular on \(\{\xi+1\in R^\times\}\). (The value \(\xi=-1\) is the point of \(L\) at infinity, which is not representable.)

**Addition gadget** (\(z=\xi+\eta\)). Each auxiliary is pinned by two incidences:
- \(\ell_Y=\operatorname{join}(Y,U_1)\);
- \(B=\operatorname{meet}(\ell_Y,K)\);
- \(\ell_X=\operatorname{join}(A,X)\);
- \(U_2=\operatorname{meet}(\ell_X,M)\);
- \(\ell_B=\operatorname{join}(B,U_2)\);
- \(Z=\operatorname{meet}(\ell_B,L)\).

**Multiplication gadget** (\(z=\xi\eta\)):
- \(\ell_1=\operatorname{join}(X,U_3)\);
- \(C=\operatorname{meet}(\ell_1,\operatorname{join}(O,A))\);
- \(\ell_2=\operatorname{join}(A,Y)\);
- \(U_4=\operatorname{meet}(\ell_2,M)\);
- \(\ell_3=\operatorname{join}(C,U_4)\);
- \(Z=\operatorname{meet}(\ell_3,L)\).

**Why these compute \(\xi+\eta\) and \(\xi\eta\).**
- Send \(E\) to infinity by a projectivity. Then \(L,M,K\) become the parallel lines \(t=1,c,a_2\), and \(O=(0,1)\), \(U=(1,1)\), \(A=(a_1,a_2)\).
- In these coordinates the constructions are von Staudt's. With \(r=(a_2-1)/(c-1)\) one finds
\[
B=(\eta(1-r)+a_1,\ a_2),\qquad U_2=(\xi+(a_1-\xi)/r,\ c),
\]
\[
C=(\lambda a_1,\ 1+\lambda(a_2-1)),\qquad \lambda=\xi/(1-r+r\xi),
\]
and the output points have abscissa \(\xi+\eta\) and \(\xi\eta\) respectively.
- Join and meet commute with projectivities, and the coordinate on \(L\) is projective.

The identities were checked exactly:
- in normal form: [checks/su2/w2_vonstaudt_gadgets_check.cpp](checks/su2/w2_vonstaudt_gadgets_check.cpp), 4000 tests, 0 failures;
- for the configuration above over \(\mathbb Q(\sqrt5)\): the search program, 0 failures.

**Base nondegeneracy.** At \(\xi=\eta=0\) every input equals \(O\). The search program checks, for the configuration above, that every join and meet occurring in both gadgets has the following properties at the base:
- it is nondegenerate;
- every line misses \(T_1\);
- every point is finite.

At the base:
- the addition gadget has \(B=A\), \(U_2=U_1\), \(\ell_Y=\ell_X=\ell_B=\operatorname{join}(O,A)\) and \(Z=O\);
- the multiplication gadget has \(C=O\), \(U_4=U_1\) and \(Z=O\).

Each determinant is therefore a nonzero constant at the base, so all Cramer opens hold on a Zariski neighbourhood. All base coordinates lie in \(\mathbb Q(\sqrt5)\subset\mathbb R\). So every generator lies in \(\mathrm{SU}_2\) at the base.

**Zero test.** Making an output \(Z\) incident with \(N\) as well as \(L\) forces \(Z=O\) (Cramer), that is, \(z=0\), scheme-theoretically.

## 5. Assembly

The assembly follows ExactChart Theorem 1 verbatim.
1. Translate \(x\) to the origin and clear denominators, so every defining polynomial \(f_j\in\mathbb Z[\xi_1,\dots,\xi_n]\) has zero constant term.
2. Write each \(f_j\) as a circuit of the two gadgets on the input generators \(X_m\) (incident with \(L\)). Integer multiples come from repeated addition. Negation \(\eta=-\xi\) comes from an addition gadget whose output is tested to be zero.
3. Every wire is \(0\) at the base, which is the base configuration of §4. Hence every open condition holds on a Zariski neighbourhood \(X'\) of \(x\).
4. Test each final output to be zero.

Let \(\Gamma_0\) consist of:
- the frame \(2I\);
- one point or line generator for every wire and auxiliary, with the relators of §§2–3;
- the incidences of the gadgets;
- the incidences pinning the constants;
- the zero tests.

On \(\mathcal C\) and the listed opens, \(\mathcal S\cong X'\), because every auxiliary is a regular function of the inputs (Cramer and the line lemma). Hence
\[
\mathcal R^\circ(\Gamma_0)\simeq X'\times\mathrm{PGL}_2 .
\]

**Explicit inverse.**
- A point \(\xi\in X'\) determines every wire and auxiliary value by the formulas above.
- A point \((s,t)\) is sent to \(X=\mathrm{Cayley}(T_1+s e_1+t e_2)\).
- A line \((A,B)\) is sent to \(P=-\tfrac12+p(A,B)\) by the line lemma.
- The tuple is then transported by \(\Phi_O\).

**Density.** The base image contains \(2I\). To be independent of the base values, add one free generator \(h\in\mathrm{SU}_2\setminus2I\); this adds one factor \(\mathrm{SL}_2\). A closed subgroup of \(\mathrm{SU}_2\) properly containing \(2I\) is infinite, so its identity component is a torus or \(\mathrm{SU}_2\). A torus is excluded because a perfect group maps trivially to \(N(T)/T=\mathbb Z/2\). Hence the image is dense.

## 6. The closed hyperbolic source

Apply Kapovich–Millson Lemma 4.4 to \(\Gamma_0\) with \(H=\mathrm{SL}_{2,\mathbb C}\), exactly as in ExactChart Theorem 1:
- Start from the Panov–Petrunin orbifold.
- Remove the cone neighbourhoods and pair the \(\mathbb{RP}^2\) boundaries.
- Kill the designated order-two elements. In \(\mathrm{SL}_2\), \(\rho(\lambda)^2=1\) forces \(\rho(\lambda)\in\{1\}\sqcup\{-1\}\), a clopen splitting via the idempotent \((\operatorname{tr}+2)/4\). This gives the factor \(\mathrm{SL}_2^k\).

The perfect-kernel hyperbolic replacement identifies the representation schemes on an open-and-closed subscheme and preserves image subgroups. It keeps the orientability type, so \(M\) is nonorientable. [Kapovich–Millson, Lemma 4.4](https://www.math.ucdavis.edu/~kapovich/EPR/char.pdf) · [Derived hyperbolic transfer, Theorem 1 and §3](DerivedHyperbolicTransfer.md) · [Panov–Petrunin, Telescopic actions](https://doi.org/10.1007/s00039-012-0196-5)

## 7. Comparison with Kapovich–Millson Remark 1.5

Kapovich–Millson obtain a regular étale cover \(\tilde{\mathcal R}_0\to X'\times\mathrm{PSL}_2^{k+1}\) with deck group \(\mathbb Z_2^{k+r}\). Its two parts are:
- \(\mathbb Z_2^k\): signs of the free-factor generators, from passing from \(\mathrm{PSL}_2\) to \(\mathrm{SL}_2\);
- \(\mathbb Z_2^r\): signs of the order-four lifts of the \(r\) Coxeter involutions, i.e. the Kummer torsor of the axis norms \(q(v)\).

Factor by factor, the chart here reads as follows.
- \(X'\) appears exactly, with its nonreduced structure.
- \(\mathrm{SL}_2^k\) replaces \(\mathrm{PSL}_2^k\). These are genuine free factors, since \(\operatorname{Hom}(F_k,\mathrm{SL}_2)=\mathrm{SL}_2^k\), so the \(\mathbb Z_2^k\) disappears; it was an artefact of working in \(\mathrm{PO}_3\).
- \(\mathrm{PGL}_2\) is the frame: a single orbit, rigid because \(2I\) is finite.

The \(\mathbb Z_2^r\) disappears because no involution is used:
- points are Cayley vectors, which need no normalisation;
- lines are order-three elements, which have a canonical lift class (trace \(-1\) rather than \(1\)), and whose oriented normals are residual intersections.

The covering in Remark 1.5 therefore reflects the involution encoding, not the geometry of \(\mathrm{SU}_2\)-representations.

**Remark (Mnëv).** Instead of the gadgets, one may feed the scheme-theoretic Mnëv theorem into §3: Kapovich–Millson 1998 / Lafforgue give \(BR_0(\mathcal A,\mathbb P^2)\simeq X\) with a real base realisation. The line lemma and incidence identity then reproduce \(BR_0\) exactly. A constant frame for that route has to be chosen so that the base realisation avoids the line at infinity of \(\Pi\) and the point \(T_1\). The gadget route above is self-contained and avoids this citation. [Kapovich–Millson, §5 Step 1](https://www.math.ucdavis.edu/~kapovich/EPR/char.pdf) · Lafforgue, *Chirurgie des grassmanniennes*, CRM Monograph Series 19 (2003)

## 8. Routes that do not work

These were checked and explain why naive compact gadgets fail.
- **Unipotent anchors.** A generator confined to a unipotent subgroup is the identity at a compact base, where the \(U\)- and \(L\)-branches cross.
- **\(\sigma\)-stability.** With \(\sigma(g)=(g^*)^{-1}\), relators with \(\mathrm{SU}_2\) constants are \(\sigma\)-stable. So no word can vary inside a Borel subgroup, a unipotent group or a noncompact torus.
- **Euler/KAK recovery.** The decomposition \(D(t_1)R\,D(t_2)\) gives \(t_1^2\), never \(t_1\).
- **Gibbs products.** The relation \((1+xi)(1+yj)=1+xi+yj+xyk\) is exact in \(\mathrm{PO}_3\), but its \(\mathrm{SL}_2\) lift needs \(\sqrt{1+x^2y^2}\).
- **Torus encodings.** Iterated two-sheeted gadgets compute only flip-semi-invariant functions. A pole argument excludes one-relator torus gadgets for \(\xi+\eta\) and \(\xi\eta\).
- **Parity.** A relator set invariant under \(w\mapsto-w\) (for instance only trace-zero conditions) reproduces a \(\mu_2\)-torsor.

The construction above avoids all of these. Its relators have odd exponent sums and nonzero trace values, and every auxiliary is obtained by division or by residual intersection.

## Status

**Theorem: proved informally, confidence 0.9.** The components:
- frame lemma, Cayley chart, line lemma, incidence, join/meet: proved, 0.95, with the line lemma and incidence also checked in exact arithmetic over reduced and dual-number points;
- gadgets: proved, 0.9; the identities were checked exactly in normal form, and for the explicit \(\mathbb Q(\sqrt5)\) constant configuration including base nondegeneracy;
- the frame constants of §4 come from exact computer search. The provenance of \(A\) as a meet of constant lines and the representability of every derived constant were machine-checked, not hand-checked.

Weakest links:
- Panov–Petrunin for a presentation with torsion, and the transfer, used unchanged from ExactChart Theorem 1;
- the encoding coordinate \(\xi\) is a Möbius function of \(s\), so the input chart is \(X'\) through that fixed Möbius change of coordinates on each factor, which is harmless.

Not done: an orientable \(M\).
