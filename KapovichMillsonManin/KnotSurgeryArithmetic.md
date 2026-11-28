# Diophantine universality in a hyperbolic rational homology sphere

## 1. One surgery realizes every marked affine scheme in a fixed number of variables

**Theorem 1.** For every \(r\ge 0\) and every bound \(b\), there are a hyperbolic knot \(K\subset S^3\), an integer surgery \(M\) on \(K\) that is closed hyperbolic, and fixed words in \(\pi_1(M)\) with the following property. The first homology of \(M\) is cyclic of order greater than \(b\). In the natural \(\mathrm{SL}_2\) representation scheme of \(M\) over \(\mathbb Z\), a fixed set of equations in word traces defines a conjugation-invariant closed subscheme isomorphic to
\[
\mathrm{PGL}_{2,\mathbb Z}\times\mathbb A^r_{\mathbb Z}.
\]
The \(r\) coordinates of the second factor are differences of two word traces. Every closed subscheme \(X\subseteq\mathbb A^r_{\mathbb Z}\) is therefore realized by imposing its equations on these same trace coordinates, with the full scheme structure. At every characteristic-zero point of the fixed subscheme the representation is Zariski dense. The same construction works directly in the exterior of \(K\).

The equations specifying the closed subscheme are part of the result. The unconstrained character and representation schemes of knots obey the obstructions in the companion work on knot universality. This construction uses interior word traces as additional data.

### The trefoil calculation

For the positive trefoil use the Wirtinger presentation \(\langle a,b\mid aba=bab\rangle\). The meridian is \(a\) and the preferred longitude is \(a^{-6}(ab)^3\). Indeed the torus framing gives the central Seifert fibre \((ab)^3\), of linking number \(2\cdot 3\) with the knot, and multiplying by \(a^{-6}\) changes to the zero-linking longitude. For the connected sum of \(\ell\) positive trefoils the presentation has a common meridian \(a\) and a copy \(b_j\) for each summand, with the indicated braid relations. Its longitude is the product of the longitudes of its summands, with the meridians identified. [Clay–Lidman–Watson, §3](https://msp.org/agt/2013/13-4/agt-v13-n4-p18-p.pdf)

In the following formulas \(I\) denotes the identity matrix. Over every commutative ring define
\[
 A=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
 B_x=\begin{pmatrix}1-x&x^2\\-1&1+x\end{pmatrix},\qquad
 U(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}.
\]
The matrices \(A,B_0\) satisfy the braid relation by direct multiplication. Since \(B_x=U(x)B_0U(-x)\) and \(U(x)\) commutes with \(A\), so do \(A,B_x\). The Cayley–Hamilton identity gives \((AB_x)^3=-I\) since \(\operatorname{tr}(AB_x)=1\) and \(\det(AB_x)=1\). Thus the longitude of an active summand, on which \(b_j\) is sent to some \(B_x\), is sent to \(-A^{-6}\). For an inactive summand, set \(b_j=a\) in the representation. Its longitude goes to \(I\).

Let \(B\) be the image of the first active \(b_j\). The frame equations are
\[
 \operatorname{tr} A=\operatorname{tr} B=2,\qquad \operatorname{tr}(AB)=1.
\]
Here and below the same symbols for words and matrices are used during evaluation. The equations are exact over every commutative ring. Put \(e=A-I\) and \(f=I-B\). Cayley–Hamilton yields \(e^2=f^2=0\) and \(\operatorname{tr}(ef)=1\). Polarized Cayley–Hamilton for traceless \(2\times 2\) matrices gives \(ef+fe=I\). Consequently \(e,f,ef,fe\) are matrix units. They define an automorphism from the standard matrix algebra to the matrix algebra in the moving frame. The unital homomorphism determined by these units is an isomorphism since it is an isomorphism over every residue field, where the matrix algebra is simple. The automorphism scheme of the matrix algebra is \(\mathrm{PGL}_2\). This argument includes characteristic two and works functorially, without choosing any square root or dividing by an integer.

In this frame each further active matrix \(C\) satisfies \(\operatorname{tr}C=2\), \(\operatorname{tr}(AC)=1\) precisely when \(C=B_x\) for a unique \(x\). In fact the second equation gives \(C_{21}=-1\), and the determinant gives \(C_{12}=(C_{11}-1)^2\). For these matrices the two trace functions recover the parameter explicitly:
\[
 P_x=(AB_xA)(AB_0A)^{-1}
     =\begin{pmatrix}1+x^2&x\\x&1\end{pmatrix},
 \qquad x=\operatorname{tr}(AP_x)-\operatorname{tr}(P_x).
\]
Assign the first active summand as the frame, the next \(r\) as the \(r\) coordinates, and every extra active summand the frame value \(B_0\). The equality of two word matrices can itself be written as four trace equations. In the frame the four matrices \(I,A,B,AB\) form a basis of the full matrix algebra, because their differences give \(e,f,ef\) with unit coefficients. If \(D\) is the difference of the matrices for two words, \(D=0\) is equivalent to \(\operatorname{tr}(DW)=0\) for all \(W\) in this basis by the perfect matrix trace pairing.

### Hyperbolic knot and hyperbolic filling

Choose an even positive integer \(\ell\ge r+1\) with \(6\ell>b\). Take the connected sum \(J\) of \(\ell+2\) positive trefoils. Silver–Whitten supply a hyperbolic knot \(K\) with a knot-group epimorphism onto \(\pi_1(S^3\setminus J)\) carrying a meridian and preferred longitude to those chosen for \(J\). On \(J\), either activate the first \(\ell\) summands and leave the last two inactive, or activate all \(\ell+2\). For \(k=\ell\) or \(k=\ell+2\) the resulting longitude is \((-I)^kA^{-6k}=A^{-6k}\). All the indicated representations therefore kill the slope \(\mu^{6k}\lambda\) on \(K\). [Silver–Whitten, *Hyperbolic covering knots*, Theorem 2.2](https://msp.org/agt/2005/5-4/agt-v5-n4-p08-s.pdf)

The two candidate slopes have distance \(12\) on the boundary torus. The Lackenby–Meyerhoff bound \(8\) on the distance between exceptional slopes guarantees that at least one filling is hyperbolic. Fix that choice of \(k\) and \(M=K(6k)\). Its first homology is \(\mathbb Z/(6k)\), since the longitude is zero in the abelianization of a knot group. The knot group epimorphism induces a surjection from \(\pi_1(M)\) to the quotient of the group of \(J\) by \(a^{6k}\lambda_J\). Both groups are finitely presented. A surjection between finitely presented groups has finitely normally generated kernel: write a presentation of the quotient on the images of the chosen finite generators of the source, and lift its finite relation list. Thus finitely many fixed word-matrix equations specify exactly the representations pulled back from the quotient, over any coefficient ring. Translate them to trace equations using the frame. Impose the frame equations, the \(r\) variable equations, and the specified matrix equalities for extra or inactive summands. The normalized matrices constructed above already kill the surgery relation for every ring and every choice of the \(r\) parameters. This gives the product and its inverse on points over every ring. [Lackenby–Meyerhoff, *The maximal number of exceptional Dehn surgeries*](https://arxiv.org/abs/0808.1176)

For the knot exterior use the same epimorphism to the group of \(J\) itself and the same marked matrices. In characteristic zero the positive powers of \(A\) and \(B_0\) in the normalized image are Zariski dense in the upper and lower unipotent subgroups respectively. These subgroups generate \(\mathrm{SL}_2\), which proves density after any base change to an algebraically closed characteristic-zero field. \(\square\)

## 2. One fixed invariant with everywhere-soluble local fibres

**Theorem 2.** There is a single closed hyperbolic rational homology sphere \(M\) as in Theorem 1 with the following property. For every computably enumerable set \(S\subseteq\mathbb N\), there is one integral regular conjugation-invariant function \(F_S\) on its natural \(\mathrm{SL}_2\) representation scheme, given by a polynomial in a fixed finite list of word traces, with the following properties for all \(n\ge 0\).

1. The equation \(F_S(\rho)=n+1\) has a solution in \(\mathrm{SL}_2(\mathbb Z)\) representations if and only if \(n\in S\). Every such solution is Zariski dense over \(\mathbb C\).
2. The same fibre has a representation over \(\mathbb Q\), \(\mathbb R\) and \(\mathbb Z_p\) for every prime \(p\), even when \(n\notin S\). It also has a point over the profinite completion \(\widehat{\mathbb Z}\), and over \(\mathbb Z/m\mathbb Z\) for every \(m\ge 1\).

The theorem also holds with the exterior of the knot \(K\) in place of \(M\). For a complete c.e. set \(S\) this gives a \(\Sigma^0_1\)-complete problem on fibres of one fixed trace polynomial on one fixed hyperbolic rational homology sphere. No nonconstant datum besides the single positive integer on the right varies.

**Proof.** Fix a computable enumeration \((S_e)\) of the c.e. sets and apply the Davis–Putnam–Robinson–Matiyasevich theorem to the c.e. relation \(n\in S_e\). This gives one polynomial \(P_*(e,n,y)\in\mathbb Z[e,n,y]\) with \(n\in S_e\) equivalent to \(P_*(e,n,y)=0\) for some integer tuple \(y\). If the original witnesses range over natural numbers, replace them with sums of four squares. For a given \(S=S_e\), set \(P(n,y)=P_*(e,n,y)\). The scalar multiplication gates underlying this encoding are the integer instance of the bilinear systems in Manin's Conjecture 7.2. [Matiyasevich, *Diophantine representation of enumerable predicates*](https://m.mathnet.ru/php/archive.phtml?jrnid=im&option_lang=eng&paperid=1910&wshow=paper) · [Manin, §7](https://arxiv.org/html/2007.10632#S7)

Use Theorem 1 once with enough parameters for four variables \(s_1,\ldots,s_4\), the tuple \(y\), and one coordinate \(u\). The tuple length comes from \(P_*\) and is independent of \(S\). Regard all these parameters as regular trace functions on the entire representation scheme, by the word formulas of Theorem 1. Set
\[
\begin{split}
 T&=1+s_1^2+\cdots+s_4^2,\\
 Q(u)&=(2u-1)(u^2-13)(u^2-17)(u^2-221),\\
 E&=\sum_j R_j^2+\bigl(P(T-1,y)Q(u)\bigr)^2,\qquad
 F=T(1-E).
\end{split}
\]
Here the \(R_j\) are the integer trace-polynomial residuals for the fixed closed subscheme in Theorem 1. They are a fixed finite list. At an integral representation, \(T\) is a positive integer and \(E\) a nonnegative integer. Thus \(F=n+1>0\) implies \(E=0\), \(T=n+1\), and \(P(n,y)Q(u)=0\). None of \(13,17,221\) is an integer square and \(2u-1\) has no integer root, so \(Q(u)\ne0\) over \(\mathbb Z\). It follows that \(P(n,y)=0\). The frame and density then follow from Theorem 1. Conversely, if \(P(n,y)=0\) over the integers, choose a four-square representation of \(n\) and any integer \(u\). The product construction of Theorem 1 gives an integral representation in this fibre.

For solubility over the other rings, retain the same integer four-square tuple, set \(y=0\), and take a root of \(Q\). The rational root \(1/2\) works over the reals as well. For an odd prime outside \(\{13,17\}\), among \(13,17,13\cdot17\) at least one is a nonzero square modulo \(p\), and the square root lifts by Hensel's lemma. At \(13\) use \(17\equiv4\pmod{13}\). At \(17\) use \(13\equiv 8^2\pmod{17}\). At \(2\), the unit \(17\) is a square in \(\mathbb Z_2\) since \(17\equiv1\pmod 8\). Choosing these roots prime by prime also gives a root in \(\prod_p\mathbb Z_p\). Theorem 1 gives the corresponding representation over each of these rings and reduction gives the solutions modulo every \(m\). [Leth and collaborators on intersective polynomials](https://home.olemiss.edu/~leth/papers/intersective_polynomials_II_2.pdf)

For the stated completeness, the positive integral fibre problem is c.e. by enumeration of integer matrices for the generators and evaluation of the fixed relations and \(F\). The reduction is \(n\mapsto n+1\). \(\square\)

The two guaranteed kinds of witnesses can be compared over the finite adeles. A fibre has an integral representation exactly when some rational representation and some representation over \(\widehat{\mathbb Z}\) agree as representations over \(\mathbb A_f\). Indeed \(\mathbb Q\cap\widehat{\mathbb Z}=\mathbb Z\) inside \(\mathbb A_f\), so agreement makes every generator matrix integral. The converse takes both images of the same integral point. For a complete c.e. set \(S\), this compatibility problem is complete c.e. even though both witness spaces have points in every fibre.

**Verification.** These are informal proofs using the cited theorems. The square-root obstruction in the compact version of Kapovich–Millson concerns a different problem. Here the characteristic-zero representations in the marked slice contain nontrivial unipotents.
