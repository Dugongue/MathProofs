# When word-trace constraints become undecidable

Prescribing numerical traces of group words in \(\mathrm{SL}_2(\mathbb Z)\) is decidable. Allowing comparisons of the traces of two words makes the problem \(\Sigma^0_1\)-complete on a single closed orientable hyperbolic three-manifold, with a fixed list of comparisons and one numerical input trace. The same construction realizes Manin's bilinear systems as exact integral trace sections.

## 1. The transition from prescribed traces to comparisons

Write \(\mathbb N=\{0,1,\ldots\}\), and take an effective enumeration \(W_e\) of the computably enumerable subsets of \(\mathbb N\). For a finitely presented group \(\Gamma\), let \(R_\Gamma\) denote its natural affine \(\mathrm{SL}_2\)-representation scheme over \(\mathbb Z\) and let \(X_\Gamma=\operatorname{Spec}\bigl(\mathcal O(R_\Gamma)^{\mathrm{SL}_2}\bigr)\) be the affine invariant quotient. For a word \(w\), let \(\tau_w\) denote its matrix trace, an integral regular function on both schemes.

**Theorem 1.** The following two statements hold.

1. Given a finite group presentation, words \(w_i\), and integers \(t_i\), it is decidable whether there is a representation to \(\mathrm{SL}_2(\mathbb Z)\) with all \(\tau_{w_i}=t_i\).
2. There exist one closed orientable hyperbolic three-manifold \(M\), a fixed set of marks in \(\pi_1M\), and fixed trace equations consisting of prescribed numerical traces and comparisons \(\tau_u=\tau_v\). There is one further mark word \(w\) such that, on input \(n\in\mathbb N\), deciding existence of an integral representation satisfying the fixed equations and \(\tau_w=n+2\) is \(\Sigma^0_1\)-complete. Every word in the equations has length at most two in the fixed marks. The fixed numerical traces take only the values \(2\) and \(3\). Every witness has Zariski-dense image.

For (1), the proof in §4 computes the conjugacy possibilities for a prescribed trace by free-product normal form, then applies the algorithm for equations with rational constraints in a virtually free group.

For (2), fix \(e\) indexing a complete computably enumerable set. By the DPRM theorem take a polynomial with integral coefficients whose zero set in integer witnesses defines \(W_e\). If the chosen polynomial uses natural witnesses, substitute four integer squares for each. Use a fixed circuit for that polynomial with zero final value. [Jones, *Universal Diophantine equation*](https://doi.org/10.2307/2273588)

The frame \(A,B\) with \(\tau_A=\tau_B=2,\ \tau_{AB}=3\) can be normalized to \(U(1),L(1)\) by the integral matrix-unit argument in §2. For an upper-wire mark \(X\), prescribe \(\tau_X=\tau_{XA}=2\). In the frame these imply that the lower-left entry vanishes, the sum of the diagonal entries is \(2\), and their product is \(1\). Over \(\mathbb Z\) the diagonal entries therefore both equal \(1\). Thus \(X=U(x)\), and \(\tau_{XB}=2+x\). Similarly the prescriptions \(\tau_Y=\tau_{YB}=2\) put a lower-wire mark in \(L(y)\), with \(\tau_{YA}=2+y\).

Represent every circuit wire by an upper mark. Use \(A\) for the constant \(1\) and pin a zero wire by trace \(2\) after multiplication by \(B\). Any other integer constant can be assembled by addition and negation from \(1\). Negation is \(\tau_{X^{-1}B}=\tau_{ZB}\), and multiplication is \(\tau_{X D}=\tau_{ZB}\) where the lower copy \(D\) of the second input \(Y\) is enforced by \(\tau_{DA}=\tau_{YB}\). Indeed \(\tau_{U(x)L(y)}=2+xy\).

For addition introduce one common auxiliary mark \(H_0\), with \(\tau_{H_0}=3\) and \(\tau_{H_0A^{-1}}=2\). Thus its lower-left entry is \(1\). These equations admit \(H_0=AB\). For an addition gate \(x+y=z\), introduce a companion mark \(C\) and impose \(\tau_C=\tau_{YB}\) and \(\tau_{CA}=\tau_{YH_0}\). Since \(Y=U(y)\), the right sides are \(2+y\) and \(3+y\), respectively. Thus \(C\) has trace \(2+y\) and lower-left entry \(1\). Conversely \(C=U(y)B\) works. The addition equation \(\tau_{XC}=\tau_{ZB}\) now says exactly \(2+x+y=2+z\). Pin the output to zero by comparing it with the zero wire, and take \(w=VB\) for the input wire \(V\). These are precisely the allowed comparisons and each has the claimed length.

Take a closed orientable hyperbolic \(M\) with a free quotient of rank the number of marks, with marks obtained by a section of the quotient as in §2. Every tuple of marked matrices extends to a representation, and the equations concern only those matrices. Therefore fibre existence is equivalent to \(n\in W_e\). Enumeration of integral generator tuples gives the matching \(\Sigma^0_1\) upper bound. The normalized frame has Zariski-dense image in characteristic zero. \(\square\)

## 2. A fixed pair of trace functions with points at every completion

**Theorem 2.** There exist one closed orientable hyperbolic three-manifold \(M\) and a fixed pair \(P,F\) of integral regular functions on \(X_{\pi_1M}\) with the following properties.

1. For all \(e,n\in\mathbb N\), the fibre \(P=e,\ F=n+1\) has an integral point if and only if \(n\in W_e\). Equivalently, it has a witness in \(\mathrm{SL}_2(\mathbb Z)\) representations of \(\pi_1M\). Every integral witness has a representative with Zariski-dense image in \(\mathrm{SL}_{2,\mathbb Q}\).
2. Every such fibre has a point already on the representation scheme over \(\mathbb R\), over \(\mathbb Z_p\) for every prime \(p\), and over \(\mathbb Z/m\mathbb Z\) for every positive integer \(m\).
3. There are fixed marks in \(\pi_1M\) such that \(P\) is affine linear and \(F\) is cubic in traces of words of length at most three in these marks. Equivalently, \(F\) is an integral linear combination of traces of words of length at most eight, with an integral constant.
4. A suitable \(M\) can be found among the finite covers of any given closed orientable hyperbolic three-manifold.

In particular, for a single fixed index of a complete computably enumerable set, varying only the positive integer \(F\)-value gives a \(\Sigma^0_1\)-complete integral-point problem. A fixed slice is also \(\Sigma^0_1\)-complete on integral representations.

### The arithmetic relation

By the Davis–Putnam–Robinson–Matiyasevich theorem applied to \(\{(e,n):n\in W_e\}\), take one polynomial \(H(e,n,\mathbf z)\) with integer coefficients such that, for \(e,n\in\mathbb N\), the relation holds exactly when \(H=0\) has a solution in \(\mathbf z\in\mathbb Z^h\). If the original witnesses are natural numbers, replace each by a sum of four integer squares. [Jones, *Universal Diophantine equation*](https://doi.org/10.2307/2273588)

Let \(Q(t)=(t^2-13)(t^2-17)(t^2-221)\). Its factors have no integer roots. For odd \(p\) not dividing \(221\), either one of \(13,17\) is a square modulo \(p\) or their product is a square, and its nonzero square root lifts to \(\mathbb Z_p\). For \(p=13\) use \(17\equiv4\bmod 13\); for \(p=17\) use \(13\equiv8^2\bmod 17\). For \(p=2\) use \(17\equiv1\bmod 8\), the square-unit criterion in \(\mathbb Z_2\). The polynomial also has real roots. Use the system

\[
\sigma(\sigma-1)=0,\qquad \sigma H(e,n,\mathbf z)=0,\qquad
(1-\sigma)Q(t)=0.
\]

Over \(\mathbb Z\) the equations force \(\sigma=1\) and \(H=0\). Over each required local ring choose \(\sigma=0\) and a root of \(Q\). Fix a finite arithmetic circuit for these equations, with additions, negations, multiplications, integer constants, and output equations.

### The integral frame and exact trace gates

Take two matrix marks \(A,B\) with trace equations \(\tau_A=\tau_B=2\) and \(\tau_{AB}=3\). Over every commutative ring these frame equations uniquely specify an algebra automorphism of \(M_2\) that takes \(E_{12},E_{21}\) to \(a=A-I\) and \(b=B-I\), respectively. Indeed Cayley–Hamilton gives \(a^2=b^2=0\) and \(\operatorname{tr}(a)=\operatorname{tr}(b)=0\). The third trace equation gives \(\operatorname{tr}(ab)=1\). Polarizing the trace-zero Cayley–Hamilton identity gives \(ab+ba=I\), so \(ab,ba,a,b\) obey the matrix-unit multiplication rules. The four matrices form a basis since their trace Gram matrix is a permutation matrix with determinant a unit, and the ordinary trace pairing on \(M_2\) is unimodular. Conversely, an automorphism of \(M_2\) supplies these two marks. The automorphism scheme is \(\mathrm{PGL}_2\).

In this frame \(A=U(1)\), \(B=L(1)\), where \(U(x)=I+xE_{12}\) and \(L(y)=I+yE_{21}\). If \(C\) is any matrix mark, the four normalized entries are the polynomial trace expressions

\[
C_{11}=\operatorname{tr}(abC),\quad
C_{22}=\operatorname{tr}(baC),\quad
C_{21}=\operatorname{tr}(aC),\quad
C_{12}=\operatorname{tr}(bC).
\]

Here, for example, \(\operatorname{tr}(abC)=\tau_{ABC}-\tau_{AC}-\tau_{BC}+\tau_C\). Thus affine-linear expressions in traces of words of length at most three pin an upper wire \(C\) to \(U(x)\), by requiring \(C_{11}=C_{22}=1\) and \(C_{21}=0\). In the resulting scheme \(x=\tau_{CB}-2\). Similarly a lower wire \(D=L(y)\) is pinned by requiring \(D_{11}=D_{22}=1\), \(D_{12}=0\), and its value is \(y=\tau_{DA}-2\). These descriptions are valid over nonreduced rings.

Use one upper-wire mark per circuit variable and one extra lower-wire mark at each multiplication gate, constrained to have the value of the second input. Addition, negation, constants and zero-output tests are affine-linear relations in the upper-wire values. For a multiplication gate with upper first input \(C=U(x)\), lower second input \(D=L(y)\), and upper output \(E=U(z)\), the residual is

\[
\tau_{CD}-\tau_{EB}=xy-z.
\]

Taking all residuals to vanish is exact for the scheme of gate solutions. The residuals for the frame, wires and gates are a fixed finite list \(r_j\) of affine-linear trace expressions.

### The two fixed functions and the closed hyperbolic source

Let \(V\) be the upper wire for the input \(n\), and let \(J\) be the upper wire for the index \(e\). Add four unconstrained matrix marks \(D_1,\ldots,D_4\). Define

\[
T=1+\sum_{i=1}^4(\tau_{D_i^2}+2),\qquad
P=\tau_{JB}-2.
\]

Adjoin the residual \((\tau_{VB}-2)-(T-1)\) to the fixed list, and set

\[
E=\sum_j r_j^2,\qquad F=T(1-E).
\]

By Cayley–Hamilton, \(T=1+\sum_i\tau_{D_i}^2\), where in the latter expression each ordinary integer trace is squared. In particular \(T\ge1\) on integral points. If \(F=n+1>0\) then \(1-E>0\) and the nonnegative integer \(E\) is zero. All circuit constraints therefore hold, and the residual for \(V\) pins the actual input wire to \(n\). The index wire equals \(P=e\). Conversely, if there is a circuit solution, the four-square theorem writes \(n\) as a sum of four squares \(d_i^2\). Each trace \(d_i\) is realized by the determinant-one matrix with first row \((d_i,-1)\) and second row \((1,0)\). Thus every integral circuit solution gives the prescribed fibre. The same construction chooses integral \(D_i\) in each local problem, while taking \(\sigma=0\) and choosing a root of \(Q\) in the local ring. Reduction modulo prime powers and the Chinese remainder theorem give the remaining fibres over finite rings.

Write \(r\) for the finite number of marks just used. Choose \(M\) with an epimorphism \(\pi_1M\to F_r\), and fix a section by lifting the free basis. For example, apply a degree-one hyperbolic replacement to the connected sum of \(r\) copies of \(S^2\times S^1\); the degree-one map induces a fundamental-group epimorphism. A map of degree one between closed oriented manifolds is surjective on fundamental groups because it lifts to the cover corresponding to the image, which either has degree zero on top homology or forces the degree to be divisible by the finite index. Equally, for any given closed orientable hyperbolic source, Liu and Sun's virtual \(1\)-domination theorem provides such a map from a finite cover. The free basis images under the section are the fixed marks. Over each ring, any representation of \(\pi_1M\) restricts to a tuple of matrices on the section, and every tuple occurs by pullback along the quotient. Consequently the arithmetic characterization on tuples is also the characterization on representations of \(M\), with no extra representation condition in the input. The frame contains the two elementary unipotents; their powers are Zariski dense in the two one-parameter root subgroups in characteristic zero, and the latter generate \(\mathrm{SL}_2\). [Kawauchi, Corollary 4.3](https://ir.library.osaka-u.ac.jp/repo/ouka/all/8213/ojm26_04_02.pdf) · [Liu and Sun, *Virtual \(1\)-domination of 3-manifolds*](https://arxiv.org/abs/1610.03937)

The coefficient and length bounds follow from the formula for \(F\). Products of two traces expand using \(\tau_u\tau_v=\tau_{uv}+\tau_{uv^{-1}}\). A term of \(F\) uses at most one trace of length at most two from \(T\) and two traces of length at most three from the residuals. Its linear expansion has length at most eight.

### Integral invariant-quotient points

An integral quotient point gives integer values of all trace functions. Therefore the same positivity argument still forces the frame and gate equations in the quotient. To recover a representation over \(\mathbb Z\), first base change this point to \(\mathbb Q\). The formation of invariants commutes with the flat base change \(\mathbb Z\to\mathbb Q\), since invariant functions are the kernel of the difference between the action coaction and the trivial coaction. Over \(\mathbb Q\), reductivity in characteristic zero makes the invariant functor exact. For the invariant ideal generated by the three frame equations, its invariant part is generated by the same three equations over the invariant ring, by applying a Reynolds projection to their coefficients. Thus the frame locus in the rational quotient is the quotient of the rational frame locus in the representation scheme. [Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, §1](https://doi.org/10.1007/978-3-642-57916-5)

Over \(\mathbb Q\) the representation scheme with the three frame equations is the product of the normalized representation scheme with \(\mathrm{PGL}_2\), by the matrix-unit construction. Conjugation is through left multiplication on the latter factor. Hence its invariant quotient is exactly the normalized representation scheme, whose rational point is obtained from our original integral quotient point. For every generator of \(\pi_1M\), the four normalized entries of its matrix are the four trace expressions displayed above. All values are integers because the original point takes integer values on every trace. The recovered rational representation therefore has matrices in \(\mathrm{SL}_2(\mathbb Z)\). Its quotient point and the original agree on every invariant after embedding \(\mathbb Z\) in \(\mathbb Q\), and hence on every invariant over \(\mathbb Z\). Conversely, an integral representation has an integral quotient image.

This proves the theorem and both directions of the integral characterization. A direct enumeration of integral generator matrices verifies the \(\Sigma^0_1\) upper bound for representations; the equivalence gives it for quotient points. Hardness follows by choosing \(e\) to index a complete computably enumerable set. \(\square\)

## 3. Scheme-level realization of Manin's bilinear systems

**Theorem 3.** Fix a pair of nonnegative integers \(a,b\). There exist a closed orientable hyperbolic three-manifold \(N\), a distinguished group quotient \(\pi_1N\to F_{a+b+2}\), and a finite fixed list of short word traces, with the following property. For every finite collection of integral affine-bilinear relations in \(a\) left coordinates and \(b\) right coordinates, defining an affine scheme \(Y/\mathbb Z\), a trace-linear section of the representations factoring through the distinguished quotient is isomorphic to \(Y\times\mathrm{PGL}_2\). The isomorphism holds over \(\mathbb Z\), including nonreduced rings and all characteristics, and the affine invariant quotient of this section is \(Y\). Only the coefficients and right-hand sides of affine-linear probe equations vary with the input.

**Proof.** Use the same hyperbolic source construction for rank \(a+b+2\). The representations factoring through its distinguished quotient form a closed subscheme isomorphic to the representation scheme of the free group. Choose \(A,B\) and the frame equations as above. Take one upper matrix \(C_i=U(x_i)\) per left coordinate and one lower matrix \(D_j=L(y_j)\) per right coordinate. Besides the frame and normalization probes, need only the traces

\[
\tau_{C_iB}-2=x_i,\qquad
\tau_{D_jA}-2=y_j,\qquad
\tau_{C_iD_j}-2=x_i y_j.
\]

Every affine-bilinear equation is an affine-linear relation in these traces. Over an arbitrary commutative ring, the inverse construction places the coordinates in the displayed matrices and applies the frame automorphism. This gives the conjugation-equivariant product isomorphism. The group action on the frame factor factors through \(\mathrm{PGL}_2\), and the map \(\mathrm{SL}_2\to\mathrm{PGL}_2\) is faithfully flat, so \(\mathrm{SL}_2\)-invariants on this product are precisely the functions from \(Y\). This applies componentwise to projections of each of Manin's fixed vector-valued bilinear maps. No assumptions on the reducedness or arithmetic of the solution scheme are used. [Manin, §7, *Rational homotopy type and computability*](https://arxiv.org/html/2007.10632#S7) \(\square\)

## 4. Decision algorithm for prescribed numerical traces

In \(\mathrm{PSL}_2(\mathbb Z)=C_2*C_3\) use the generators represented by \(S=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)\) and \(R=\left(\begin{smallmatrix}0&-1\\1&1\end{smallmatrix}\right)\). The two mixed syllable pairs \(SR,SR^{-1}\) are respectively represented by \(U(1),L(1)\) up to sign. It follows from cyclically reduced free-product normal form that, apart from the identity and the conjugates of the factors, all elements in \(\mathrm{SL}_2(\mathbb Z)\) are conjugate to a positive word in \(U(1),L(1)\) or its negative. The short factor cases give the finitely many representatives for traces \(0,1,-1\). A word using only one type of letter has trace \(2\) before the sign, and \(U(1)\) and \(L(-1)\) are conjugate by \(S\). Thus the trace-\(2\) elements are exactly the conjugates of the cyclic group \(\langle U(1)\rangle\). The trace-\((-2)\) elements are their negatives. For a positive word with \(u\) upper letters and \(v\) lower letters, \(u,v\ge1\), expand each letter as identity plus its off-diagonal matrix unit. Every mixed pair contributes \(1\) to the trace and no term contributes negatively. Hence its trace is at least \(2+uv\ge u+v+1\). Given \(|t|>2\), it suffices to enumerate positive words of length at most \(|t|-1\), apply the prescribed sign, and filter by trace. This produces a finite list containing a representative from every conjugacy class, with possible repetitions. This is the block-length cutoff from Fine's published algorithm, with the elementary matrix-unit argument above giving the bound. [Fine, Theorem 2 and Lemma 3](https://doi.org/10.4153/CMB-1994-030-1)

Consequently each prescribed numerical trace can be written as a finite disjunction of equations with new conjugating variables, and for traces \(\pm2\) a variable in the rational subset \(\langle U(1)\rangle\). The group presentation gives further equations. The target is virtually free, so Dahmani–Guirardel's algorithm for equations with rational constraints gives a decision procedure. [Dahmani and Guirardel, *Foliations for solving equations in groups*](https://arxiv.org/abs/0901.1830) \(\square\)

The proof uses the unipotent frame underlying exact algebraic representation charts and the bilinear multiplication used in the Manin reduction. Its arithmetic source is the classical DPRM theorem. Fine's algorithm addresses fixed numerical trace classes. Ciobanu and Garreta study the corresponding question with abelianization predicates instead of matrix traces. Targeted searches on the modular group, word traces, equal-trace constraints, and Diophantine representations yielded no earlier statement of the bound in Theorem 1(2). [Fine, *Trace classes and quadratic forms in the modular group*](https://doi.org/10.4153/CMB-1994-030-1) · [Ciobanu and Garreta, *Group equations with abelian predicates*](https://arxiv.org/abs/2204.13946)

Priority remains unverified. The proofs are informal.
