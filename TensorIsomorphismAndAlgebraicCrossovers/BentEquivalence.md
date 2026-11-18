# Tensor-isomorphism completeness of cubic bent equivalence

**Theorem.** Linear equivalence, affine equivalence, and extended-affine equivalence of Boolean bent functions of degree at most three, represented by their algebraic normal forms, are each polynomial-time many-one equivalent to ordinary three-tensor isomorphism over $\mathbb F_2$. Equivalence of the graphs under ambient affine bijections has the same complexity. Hardness holds on the fixed Maiorana–McFarland family with identity permutation, namely functions $x^{\mathsf T}y+p(y)$ with $p$ a squarefree homogeneous cubic. The reduction from an alternating three-form on $n$ variables to this family uses $2n$ input bits.

Here linear and affine equivalence act by precomposition on the inputs. Extended-affine equivalence also allows addition of an affine function of the inputs. Graph equivalence is the usual CCZ equivalence. The input format provides the number of variables explicitly, and bounded-degree algebraic normal forms may be given in their full monomial basis.

## 1. Alternating forms as cubic bent functions

Let $K=\mathbb F_2$. For an alternating trilinear form $\theta$ on $K^n$, let
$$
p_\theta(y)=\sum_{i<j<k}\theta(e_i,e_j,e_k)y_i y_j y_k,\qquad
f_\theta(x,y)=x^{\mathsf T}y+p_\theta(y).
$$
For every pair of labels $a,b\in K^n$, its Walsh transform is $2^n(-1)^{p_\theta(a)+b^{\mathsf T}a}$. Summing over $x$ forces $y=a$, and evaluating the remaining term gives this formula. In particular $f_\theta$ is bent for every $\theta$.

For a function $f$ on a binary vector space write $\Delta_u f(z)=f(z+u)+f(z)$. On degree-at-most-three functions the third difference
$$
\beta_f(u,v,w)=\Delta_u\Delta_v\Delta_w f(0)
$$
is independent of the base point, alternates, and is trilinear. These identities hold on the squarefree basis monomials: a cubic monomial produces the six products using all three directions, and a lower-degree monomial produces zero. The increasing triples of $\beta_f$ recover precisely the cubic coefficients. Translation and addition of an affine function therefore preserve $\beta_f$, and a linear input change acts on all three arguments simultaneously. For $f_\theta$, its third difference is the pullback of $\theta$ by $(x,y)\mapsto y$.

If $f_\theta$ and $f_\eta$ are extended-affine equivalent, their alternating forms on $K^{2n}$ are isomorphic. For an alternating form $\beta$, the radical consists of $u$ with $\beta(u,v,w)=0$ for all $v,w$. Such a form factors through the radical quotient, and its isomorphism type on a fixed-dimensional space is determined by that quotient form. Indeed a linear isomorphism between quotient forms lifts after choosing complements and identifying the radicals. For the pulled-back forms the quotients are exactly $K^n/\operatorname{rad}(\theta)$ and $K^n/\operatorname{rad}(\eta)$ with their respective forms. Consequently $\theta$ and $\eta$ are isomorphic on $K^n$.

Conversely, suppose $S\in\mathrm{GL}_n(K)$ satisfies $\theta(u,v,w)=\eta(Su,Sv,Sw)$. The Boolean polynomial $r(y)=p_\theta(y)+p_\eta(Sy)$ has degree at most two and constant term zero. Every such Boolean polynomial is $y^{\mathsf T}B y$ for a matrix $B$: a diagonal entry contributes $y_i^2=y_i$ and one entry in each off-diagonal pair contributes the required squarefree quadratic. Then the invertible linear map
$$
(x,y)\longmapsto \bigl(S^{-\mathsf T}(x+B^{\mathsf T}y),Sy\bigr)
$$
sends $f_\eta$ to $f_\theta$ by precomposition. This proves the coincidence of the three equivalence relations on the constructed family, including forms with nonzero radical.

Alternating trilinear form equivalence is TI-complete over $K$ by the reduction of Grochow, Qiao and Tang. It is important that the input to the construction above is an alternating form, for which the squarefree cubic supplies a right inverse to polarization even in characteristic two. [Grochow–Qiao–Tang, Theorem 2 and Section 4](https://doi.org/10.4230/LIPIcs.STACS.2021.38)

## 2. A tensor-system upper bound for raw Boolean inputs

Fix $d$. For $0\le j\le d$, let $V_j$ be the $K$-space of Boolean functions in $m$ variables represented by algebraic normal forms of degree at most $j$. It has the squarefree monomial basis. Record the inclusions $V_j\hookrightarrow V_{j+1}$, the constant vector $1$ in $V_1$, and the bilinear products
$$
\mu_j\colon V_1\times V_j\longrightarrow V_{j+1}\qquad (1\le j<d)
$$
of Boolean functions. The table entries are ordinary binary coefficients obtained by taking unions of monomial supports. All spaces and maps have polynomial size for fixed $d$.

Any isomorphism of this system acts on $V_1$ by an invertible linear map fixing $1$. Its images of the coordinate functions are the coordinate functions of a unique affine bijection $T$ of $K^m$, since the induced map on $V_1/\langle1\rangle$ is invertible. Inductively each squarefree monomial in $V_{j+1}$ is in the included $V_j$ or is a product with one generator from $V_1$. Hence the action on all $V_j$ is precomposition by $T$. Conversely, any affine bijection acts on all spaces and preserves the recorded tables. Recording evaluation at $0$ as a fixed covector on $V_1$ restricts $T$ to linear maps.

For linear or affine equivalence of the functions, mark the vector $f$ in $V_d$. For extended-affine equivalence, record the quotient $V_d/V_1$, its quotient map, and the vector $f+V_1$ there. A transporter of the marked system exists exactly when the corresponding function equivalence holds. These are fixed-signature systems of order at most three, and the Futorny–Grochow–Sergeichuk construction compiles them into one ordinary three-tensor comparison. A vector or covector mark can also be written as a map to or from a distinguished one-dimensional space with its unit multiplication, which forces its change of basis to be the identity. Thus the upper bound works from raw bounded-degree ANFs. It neither requires a bentness algorithm nor an input coordinate decomposition. [Futorny–Grochow–Sergeichuk, Wildness for tensors](https://arxiv.org/abs/1810.09219) · [Grochow–Qiao, Theorem 7.3](https://arxiv.org/abs/1907.00309)

## 3. Graph equivalence on scalar bent inputs

Any ambient affine map from one graph to the other has first coordinate block $x\mapsto Ax+b f(x)+c$ on the first graph, with $b\in K^m$. This map of $K^m$ must be bijective. If $b\ne0$ and $A$ is invertible, compare $x$ and $x+A^{-1}b$. Injectivity requires $\Delta_{A^{-1}b}f(x)=0$ for every $x$. If $A$ has rank $m-1$, bijectivity requires $b\notin\operatorname{im}(A)$, and comparing the two points in each fiber of $A$ requires a constant derivative $1$ along its kernel. Rank below $m-1$ cannot give surjectivity because $\operatorname{im}(A)+\langle b\rangle$ is proper.

A bent function has balanced derivatives in nonzero directions. One way to see this is Fourier inversion of the squared Walsh transform, the Fourier transform of the sign autocorrelation $u\mapsto\sum_x(-1)^{f(x)+f(x+u)}$. The squared transform is constant, so the autocorrelation vanishes at nonzero $u$. It follows that $b=0$. Now $A$ is invertible, and the remaining row of the ambient affine bijection gives $f$ plus an affine function. Every extended-affine equivalence also yields an ambient affine map of the graphs. This recovers in the scalar bent case the published CCZ-to-EA coincidence.

## 4. Consequences for addition designs and exact transporters

For $n\ge1$, take the code $C_\theta=RM(1,2n)+\langle f_\theta\rangle$ on $K^{2n}$. The weights $0,2^{2n-1},2^{2n}$ recover precisely the first-order Reed–Muller subcode because all words $f_\theta+\ell$ with affine $\ell$ have weight $2^{2n-1}\pm2^{n-1}$. A permutation preserving the Reed–Muller subcode is affine on the coordinate points: each coordinate function must pull back to an affine function, and bijectivity gives invertibility. Thus permutation equivalence of these codes agrees exactly with extended-affine equivalence of the bent functions.

The minimum-weight words are $f_\theta(x,y)+a^{\mathsf T}x+b^{\mathsf T}y+p_\theta(a)+a^{\mathsf T}b$, where $a,b$ are arbitrary. Their differences with the word for $a=b=0$ give affine functions spanning every linear part. The sum of the words with labels $(a,0),(0,b),(a,b),(0,0)$ is the constant $1$ when $a^{\mathsf T}b=1$. Thus the blocks of the minimum-weight support design span $C_\theta$, and every code equivalence carries the minimum-weight blocks to each other. It follows that equivalence of these succinctly presented codes and isomorphism of their addition designs are also binary TI-complete. The finite point set and block family have exponential cardinality in the ANF dimension. The claim is for the specified succinct representation.

For tensors with zero alternating radical, one can also count the exact witnesses. The $x$-space is then the radical of $\beta_{f_\theta}$. Every affine transporter has linear part $(x,y)\mapsto(Ax+By,Sy)$, where comparison of the mixed quadratic terms forces $A=S^{-\mathsf T}$. Its action on the cubic form requires $S$ to transport $\theta$ to $\eta$. For linear transport, the equation for $B$ is onto the space of zero-constant degree-at-most-two functions on $K^n$, with kernel of dimension $n(n-1)/2$, as seen by varying its diagonal and off-diagonal pairs. Hence the number of linear witnesses is $2^{n(n-1)/2}$ times the number of form transporters. For exact affine transport the $y$-translation must be zero, by the coefficient of $x$; each $x$-translation is possible, giving a further factor $2^n$. For extended-affine transport both translations are arbitrary, and the equation for $B$ sees only the quadratic squarefree coefficients, with kernel dimension $n(n+1)/2$. The added affine function is then uniquely determined. The witness factor for extended-affine equivalence is $2^{n(n+1)/2+2n}$.

## 5. Fixed-output vectorial bent functions

The extended-affine theorem also holds for $s$-output vectorial bent functions for every fixed positive $s$. Here a map to $K=\mathbb F_{2^s}$ is vectorial bent when every nonzero binary linear functional of its output is bent. The action allows arbitrary binary affine input maps, arbitrary invertible binary linear output maps, and addition of a binary affine map to the output. The input is given by $s$ binary ANFs of degree at most three.

Let $\theta$ now be a nonzero $K$-alternating three-form with zero radical. Use the same squarefree cubic $p_\theta$, with coefficients in $K$, and define
$$
F_\theta(x,y)=\sum_{i=1}^n x_i y_i+p_\theta(y),\qquad x,y\in K^n .
$$
For every nonzero binary linear map $\ell\colon K\to\mathbb F_2$, the pairing $(a,b)\mapsto\ell(ab)$ is nondegenerate. Summing the Walsh transform of $\ell F_\theta$ along $x$ selects a unique $y$, yielding constant magnitude $2^{sn}$. The component ANFs have degree at most three because field multiplication is binary bilinear. Their joint third derivative, viewed in $K$, is the pullback of $\theta$, and its radical as a binary form is the $x$-space.

An extended-affine equivalence induces binary linear isomorphisms $P$ on the $y$-quotient and $L$ on the output such that
$$
\theta(u,v,w)=L\eta(Pu,Pv,Pw).
$$
For $a\in K$ write $m_a$ for multiplication by $a$ and set $B=P m_aP^{-1}$ and $M=L^{-1}m_aL$. The displayed equality implies $\eta(Bu,v,w)=M\eta(u,v,w)$. Pick a nonzero value $z=\eta(u,v,w)$. Replacing $v$ by $cv$ gives $M(cz)=cM(z)$ for every $c\in K$. Thus $M$ is multiplication by a scalar $\sigma(a)$. The zero radical of $\eta$ then gives $B=m_{\sigma(a)}$. Conjugation in the two endomorphism rings shows that $\sigma$ is a field automorphism. Hence $P(y)=S y^\sigma$ for an invertible $K$-matrix $S$, and $L(z)=\lambda\,z^{\sigma^{-1}}$ for some $\lambda\in K^\times$. This forces
$$
\theta^\sigma=\lambda^\sigma\,\eta(S\,\cdot,S\,\cdot,S\,\cdot).
\tag{1}
$$

Conversely, given (1), define $P,L$ by these formulas. As a formal polynomial over $K$, $p_\theta(y)+L(p_\eta(P y))$ is homogeneous cubic. The $\sigma^{-1}$ in $L$ cancels the $\sigma$ in $P$ on coordinates. Its squarefree cubic coefficients vanish by (1). The remaining monomials have the form $y_i^2y_j$, including $y_i^3$. Thus it is $v(y)^{\mathsf T}y$, with each component of $v$ a $K$-linear combination of the $y_i^2$. This is a binary linear map. Taking
$$
(x,y)\longmapsto
\bigl(\sigma(\lambda^{-1})S^{-\mathsf T}(x+v(y))^\sigma,\ S y^\sigma\bigr)
$$
as input change and $L$ as output change gives exact transport between $F_\eta$ and $F_\theta$.

To obtain many-one hardness, start with ordinary $K$-TI and add a separately typed one-dimensional endomorphism $\alpha\,I$, with $\alpha$ a fixed field generator over $\mathbb F_2$, to each input tensor system. Isomorphism of the systems forces equality of their scalar labels. Apply the fixed-signature FGS compiler, then the Grochow–Qiao alternating-matrix-space reduction, then the Grochow–Qiao–Tang alternating-three-form construction. These constructions commute with field automorphisms up to isomorphism. Their gadget arrays use identities, zero, and signs, and any essential-space compression can use row reduction, whose pivot choices commute with scalar automorphisms. In the last construction the form has three coordinate parts $U,V,W$. Its support types are $UUV$ and $UWW$, together with permutations (the data and the array $G_1$, respectively). Simultaneous multiplication by $a$ on $U$ and by $a^{-1}$ on $V$, fixing $W$, scales the form by $a$ for any $a\ne0$. Thus the scalar in (1) leaves the ordinary orbit of the compiled form unchanged. [Futorny–Grochow–Sergeichuk](https://arxiv.org/abs/1810.09219) · [Grochow–Qiao, Proposition 7.3](https://arxiv.org/pdf/1907.00309) · [Grochow–Qiao–Tang, Section 4](https://doi.org/10.4230/LIPIcs.STACS.2021.38)

Pass to the radical quotient before forming $F_\theta$. This preserves all comparisons at fixed ambient dimension, including (1), by lifting quotient maps across arbitrary complements and radicals. Original formats and quotient dimensions can be compared on the pair before output. For a fixed NO pair use $\sum_{i=1}^3 x_i y_i$ and $\sum_{i=1}^3 x_i y_i+y_1y_2y_3$, whose third differences are respectively zero and nonzero. The marker constructions have nonzero forms and polynomial dimension. Each compiled comparison can therefore yield (1) only when the marked systems for the source and target are isomorphic after applying $\sigma$ to the first. The scalar labels then satisfy $\sigma(\alpha)=\alpha$, which forces $\sigma$ to be the identity. Reflection of ordinary $K$-TI follows, and any ordinary $K$-TI witness gives an equivalence of the resulting vectorial bent maps.

Finally the tensor-system upper bound uses, in place of the single vector mark in $V_3/V_1$, the map from the output dual to $V_3/V_1$ sending a covector to the corresponding component function modulo $V_1$. The general-linear action on that output dual accounts for invertible output changes. This proves the upper bound over $\mathbb F_2$. Combining with the project's same-characteristic field conversion gives binary TI-completeness for every fixed output dimension $s$. The vectorial conclusion is about extended-affine equivalence. [MathProofs, Fixed Characteristic Tensor Isomorphism](../FixedCharacteristicTensorIsomorphism/Proof.md)

## Attribution and scope

The Maiorana–McFarland construction, the association of a cubic Boolean function with its third derivative, and the bent-function relation to codes and addition designs are established ingredients. The additional result is the exact hardness lift through this fixed family, paired with the tensor-system upper bound on ANF inputs. Polynomial-time equivalence of explicit, fully listed designs with binary TI does not follow from the succinct representation. This is an informal proof and publication priority remains unestablished. [Langevin–Solé, Kernels and Defaults](https://langevin.univ-tln.fr/recherche/conference/kad.pdf) · [Polujan, Boolean and Vectorial Functions, Theorem 3.25](https://opendata.uni-halle.de/bitstream/1981185920/38199/1/Polujan_Alexandr_Dissertation_2021.pdf) · [MathProofs, Cubic Bent Support Code and Design Automorphism Groups](../CubicBentSupportCodeDesignAutomorphismGroups.lean)
