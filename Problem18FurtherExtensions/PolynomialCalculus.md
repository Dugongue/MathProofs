# Polynomial-calculus certificates on the Problem 1.8 source set

This informal theorem combines the verified [Problem 1.8 recognizer](https://github.com/Dugongue/MathProofs/tree/main/Problem18) with the [algebraic proof-complexity framework of Galesi, Grochow, Pitassi and She](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2023.4).

## Statement

Let \(k=\mathbb F_q\). Work either with standard bilinear orthogonal tensor isomorphism over \(K=k\), or with standard Hermitian unitary tensor isomorphism over \(K=\mathbb F_{q^2}\) relative to \(k\). Let \(*\) denote transpose or conjugate transpose. Put the dimensions in order \((a,c,b)\) with \(2\le a\le b\le c\), and suppose that the source tensor \(A\) passes the large-median two-algebra test of Problem 1.8. The target \(B\) is arbitrary. The source test has density at least \(1-O((1+\log b)/\sqrt b)\), with absolute constants, by the Problem 1.8 large-median bound.

Take the tensor-action equations in the entries of \(P,Q,R\) and both quadratic isometry equations \(U^*U=UU^*=I\) for each of \(U=P,Q,R\). In the unitary case use a fixed \(k\)-basis of \(K\), two base variables per entry, and both coefficient equations for every \(K\)-valued equation. If \(A,B\) are nonisomorphic, polynomial calculus over \(k\) refutes this system in degree at most 16, except at the odd orthogonal nonsquare-normalization branch specified below. Those certificates are constructible in polynomial bit time in the dense input and field presentation. On the exceptional branch, adding the field equations \(x^q-x=0\) for the original variables gives a refutation of degree at most \(\max(16,q)\), constructible in time polynomial in the input length and \(q\).

For every odd \(q\ge17\) there are examples in arbitrarily large equal even dimensions for which degree \(q\) is necessary and sufficient in this encoding. Without field equations the system in those examples has a solution over the algebraic closure. The lower bound concerns this exact encoding of field membership.

## Recovering the two small-mode factors inside polynomial calculus

Write \(F,D\) for the flattenings along the mode of dimension \(c\), \(S=FF^*\), \(S'=DD^*\), and \(W=P\otimes R\). The action equations are \(D=QFW^{\mathsf T}\). The two isometry equations imply \(W^{\mathsf T}\bar W=\bar W W^{\mathsf T}=I\), where the bar is the involution applied entrywise. Substitution gives

\[
 S'=QSQ^*,\qquad S'Q=QS,\qquad D^*Q=\bar W F^*.
\]

These identities use only multiplications of degree at most 7. For example, subtract \((QFW^{\mathsf T})(QFW^{\mathsf T})^*\) from \(DD^*\) by replacing one factor at a time through the action equations. Each monomial multiplier can be applied by successive variable multiplications. The intertwining identities \(S'^t Q=Q S^t\) follow by induction using constant left and right matrix multipliers and the degree-one identity \(S'Q=QS\). The exponent \(t\) does not increase polynomial-calculus degree. Thus for \(0\le t<c\),

\[
 D^* S'^t D=\bar W F^*S^tF W^{\mathsf T}.
\]

Transpose, take the partial trace over the mode of dimension \(a\), and use \(P^*P=I\). If \(R_t(A)\) and \(R_t(B)\) denote the ordered partial-trace matrices, this gives \(R_t(B)=R R_t(A)R^*\). Right multiplication by \(R\) and the quadratic equations now give the linear equations \(R_t(B)R=R R_t(A)\). In the unitary case applying conjugation to a displayed identity amounts to a constant linear recombination of its two component equations. A multiplication of degree \(j\) over \(K\) is simulated over \(k\) by expansion in the fixed basis into multiplications of degree at most \(j\).

If this linear system has only the zero solution, Gaussian elimination derives every entry of \(R\) equal to zero, contradicting \(R^*R=I\). Otherwise its solution space is a line through an invertible matrix \(X\). The kernel of a nonzero intertwiner is invariant under the source generators, which generate the full matrix algebra by the recognizer. The quotient of two invertible intertwiners commutes with that algebra and is scalar. Because the generators are self-adjoint, \(X^*X=d_b I\) for a nonzero involution-fixed \(d_b\). The relation \(R=r X\) is obtained by linear elimination, with \(r\) a scaled entry of \(R\). Substitution into the orthogonality equation yields \(r\bar r=d_b^{-1}\).

Undo \(X\) in the target's \(b\)-mode to obtain known slices \(Y_k\). Let \(M_k\) be the source slices and \(Z_{k\ell}=M_k M_\ell^*\). The tensor equations give \(Y_k=rP M_k Q^{\mathsf T}\). Multiplying two such relations and substituting \(r\bar r=d_b^{-1}\) and \(Q^{\mathsf T}\bar Q=I\) yields \(d_bY_kY_\ell^*=PZ_{k\ell}P^*\). Right multiplication by \(P\) gives the linear intertwiner system for \(P\). Again the zero case refutes the equations. Otherwise \(P=pP_0\) where \(P_0\) is independently computed and invertible. The involution sends each pair-Gram to the pair with indices reversed, so \(P_0^*P_0=d_a I\), and the proof derives \(p\bar p=d_a^{-1}\). In this stage substituted tensor equations have degree at most 3 and products have degree at most 6. Normalization scalars are linear forms in the original variables.

## Arithmetic failure and the last extension test

For unitary groups the scalar norm maps onto \(k^\times\). For bilinear orthogonal groups in characteristic two squaring is a bijection. In odd orthogonal characteristic, either required scalar square may be a nonsquare in \(k\). This is the exceptional branch. If \(x\) is the original coordinate chosen for that normalization, rescaling gives \(x^2-h=0\) with \(h\) a nonsquare. Multiply and combine this equation successively to obtain \(x^q-h^{(q-1)/2}x=0\) in degree \(q\). Subtract the field axiom, obtaining \(2x=0\), and use \(x^2-h=0\) again to refute. This takes \(O(q)\) proof lines. If the branch occurs and a bounded-degree certificate is available from any other failure test, that certificate may still be used.

Suppose the scalar equations are solvable. Let \(H\) be the flattening of \((P_0,I,X)A\), \(s=(d_ad_b)^{-1}\), and \(M=prQ\). Then polynomial calculus derives

\[
 D=MH,\qquad M^*M=MM^*=sI,\qquad H=s^{-1}M^*D,\qquad D^*D=sH^*H.
\]

Here \(M\) is an abbreviation for polynomials of degree 3. The similarity equations follow by multiplying the scalar and \(Q\) equations. The reciprocal and Gram equations follow by replacing the factors in the products in turn. A Gram mismatch now derives a nonzero constant directly. A kernel mismatch gives a nonzero constant by applying either the forward or reciprocal identity to a constant kernel witness. In the odd orthogonal and Hermitian settings, these tests suffice. After choosing \(p,r\) solving the scalar equations they define an isometry between the column spans of \(prH\) and \(D\), and Witt extension gives \(Q\).

In characteristic two with transpose, let \(e\) be the all-ones column in the large mode and \(\lambda_0=\sqrt{s}\). Both diagonal equations for \(M\) give entrywise identities

\[
 (Me-\lambda_0e)^{[2]}=0,\qquad
 (M^{\mathsf T}e-\lambda_0e)^{[2]}=0.
\]

Here \([2]\) means coordinatewise square. If \(Hu+t e=0\) while \(Du+t\lambda_0e\ne0\), then the forward action identity expresses any nonzero coordinate of the latter vector as a nonzero constant multiple of an entry of \(Me-\lambda_0e\). Squaring gives a nonzero constant. The reverse mismatch, with \(Du+t\lambda_0 e=0\), follows by the reciprocal action identity and the second square-zero identity. Algebraically the squaring step multiplies \(z-\gamma=0\) by \(z+\gamma\) and uses \(z^2=0\), with \(\gamma\) a known nonzero constant. The degree is at most 6. Equality of the marked cross pairings already follows from the equal Grams because \(v^{\mathsf T}v=(v^{\mathsf T}e)^2\) and squaring is injective on \(k\).

If all tests pass, the marked span map sends \(\lambda_0H\) to \(D\) and fixes \(e\). In odd ambient dimension the dot product splits as the line \(ke\) and its alternating nondegenerate complement. Apply symplectic Witt extension on the complement after subtracting the \(e\) component. In even ambient dimension the alternating nondegenerate form \(I+ee^{\mathsf T}\) makes the marked map a symplectic isometry. Its extension fixes \(e\) and preserves the functional \(v\mapsto v^{\mathsf T}e\), which is pairing with \(e\) for the alternating form. It therefore preserves the dot product. This gives the required last factor in either dimension. Thus every NO instance on the announced source set hits one of the certificate-producing failures.

All intermediate polynomial substitutions above can be implemented using linear combination and multiplication by one variable. A product difference uses \(UV-U'V'=(U-U')V+U'(V-V')\). After expansion, the products in the proof have degree at most 16. Since the number of variables is polynomial in the input length and this degree is fixed, the total work for those derivations is polynomial. The field-equation branch adds only the explicitly described univariate chain.

## Matching example for the field-equation degree

Fix odd \(q\) and choose a nonsquare \(\delta\in k\). Take a recognized balanced source of sufficiently large even dimension, which exists by the density theorem. There are similitudes \(P_1,Q_1\) with multipliers \(\delta,\delta^{-1}\), since scaling the standard dot product in even dimension leaves its discriminant class unchanged and nonsingular symmetric forms over a finite odd field are classified by dimension and discriminant. Set \(B=(P_1,Q_1,I)A\).

The marginal operator of the large mode transforms by conjugation by \(Q_1\), since the multipliers cancel. In the transposed flattening Gram used for \(R_t\), the conjugation in the \(a\)-mode is by \(P_1\) and the additional scalar factor is \(\delta^{-1}\). The partial trace cancels that factor with the multiplier of \(P_1\). Hence \(R_t(B)=R_t(A)\) for all \(t\), and any isometric transporter has scalar last factor. Its square is 1. The pair-Grams of \(B\) are \(P_1Z_{k\ell}(A)P_1^{-1}\), so after undoing the last factor the small-mode transporter must be a scalar multiple of \(P_1\). No such multiple is orthogonal over \(k\). Over the algebraic closure choose \(\gamma^2=\delta^{-1}\). The triple \((\gamma P_1,\gamma^{-1}Q_1,I)\) is orthogonal and has the same action on \(A\) as \((P_1,Q_1,I)\).

Every polynomial-calculus refutation must therefore include a field axiom, each of which has degree \(q\). For \(q\ge17\) the constructive upper bound and this lower bound coincide. This gives an exact arithmetic-versus-geometric degree gap for the stated classical tensor equations.

## Relation to earlier work

Galesi, Grochow, Pitassi and She study proofs for ordinary general-linear tensor isomorphism, including worst-case degree lower bounds and constructive upper bounds in bounded tensor rank. The theorem here uses two-sided isometry equations and the high-density source test, whose passing tensors can have unbounded rank. The degree-\(q\) lower bound describes how a field-membership axiom enters this particular polynomial encoding. It is separate from lower bounds for unconstrained general-linear tensor isomorphism. [Galesi–Grochow–Pitassi–She](https://arxiv.org/abs/2305.19320)
