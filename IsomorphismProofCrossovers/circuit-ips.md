# PC+INV with circuit annotations and the Ideal Proof System

**Theorem.** Fix any field $F$. When the matrices specifying each inversion inference are included as algebraic circuits and charged to the certificate size, PC+INV and the algebraic Ideal Proof System (IPS) admit polynomial-size translations in both directions. Every IPS certificate can be translated to a PC+INV proof with one inversion inference and proof-line degree at most the maximum axiom degree. The translations concern representation size, with equality of polynomials interpreted as formal polynomial identity. [IPS definition and Hilbert-like certificates](https://arxiv.org/abs/1404.3820) · [PC+INV rule](https://arxiv.org/html/2305.19320#S2.SS3).

The input equations $f_1,\ldots,f_m$ and certificate data are encoded by finite arithmetic circuits over $F$. For a PC+INV certificate we charge the input, the proof-line circuits, the rule annotations, and all matrix entries, including the explicit list of references to earlier lines for the premises of each inversion. Sparse proof-line representations can instead be used as input to the forward translation by converting their monomials to circuits. In the reverse translation the only lines are input lines and constants, so they can retain their original representation. The measure is algebraic circuit size, including the matrix dimensions and the annotation length. Over a represented field the translations copy field constants and introduce only $0,1,-1$, so they do not require computing new constants of unbounded encoded length.

## From annotated PC+INV to IPS

An IPS refutation is a circuit $H(x,y)$ with
$$
H(x,0)=0,\qquad H(x,f(x))=1.
$$
Maintain, for each PC+INV line $p(x)$, a circuit $H_p(x,y)$ with the same properties except that the second evaluation is $p(x)$. An input axiom $f_i$ uses $H_{f_i}=y_i$. Linear combinations and multiplication by a variable act on these circuits by the corresponding arithmetic gates.

For an inversion instance, put $C=AB$ and $D=BA$, where $A,B$ are square polynomial matrices of side $r$. Over the formal polynomial ring the following identity holds:
$$
D-I=B(C-I)A\,\operatorname{adj}(D)-(D-I)(\det C-1).
$$
To check it, use $B(C-I)A=D^2-D$, $D\,\operatorname{adj}(D)=\det(D)I$, and $\det D=\det C$. No invertibility or division is required for any of these identities.

Expand $\det C-1$ as a linear combination of the entries of $C-I$ with polynomial cofactors as coefficients. Namely, telescope determinants over the $r+1$ hybrids of $C$ and $I$ whose first $j$ rows come from $C$ and whose remaining rows are those of $I$, for $0\le j\le r$. The difference of two successive determinants is the expansion along the changed row, using the entries of the row of $C-I$ and cofactors of the hybrid. Thus each conclusion entry of $D-I$ is a linear combination of the premise entries of $C-I$, with coefficients computed using ordinary matrix products, determinants and minors of $r\times r$ matrices. Division-free polynomial-size determinant circuits work over every field. [Berkowitz, On computing the determinant in small parallel time using a small number of processors](https://doi.org/10.1016/0020-0190(84)90018-8).

For the selected conclusion entry, use those coefficient circuits in $x$ and replace each premise entry with its maintained circuit $H_p(x,y)$. This gives the required evaluations. Reuse all earlier circuits by DAG sharing, rather than recursively copying them into each new line. Each inference adds a number of gates polynomial in its annotation length and earlier gate references. The final line supplies an IPS refutation.

## From IPS to one annotated inversion

A standard Hilbert-like conversion supplies polynomial-size circuits for $g_i$ with $\sum_i f_i g_i=1$. For completeness, start from $H(x,y)$ and telescope $H(x,y)-H(x,0)$ by replacing $y$ variables with zero one at a time. In term $i$, divide the difference formally by $y_i$ using a circuit construction with no division gates. For each gate $p$, keep the value $p$, its specialization $p_0$ at $y_i=0$, and the difference quotient $Q_p$, initialized by $Q_{y_i}=1$ and by zero for all other input gates. At a sum gate add the child quotients. At a product gate $p=ab$, set $Q_p=Q_a b+a_0 Q_b$. This satisfies $p-p_0=y_iQ_p$. Including the other zero substitutions from the chosen telescope gives $H(x,y)-H(x,0)=\sum_i y_i Q_i(x,y)$, using a circuit of size polynomial in $m$ and the size of $H$. Substitute $y=f(x)$ in each $Q_i$ to get $g_i(x)$.

Apply the matrices from the companion proof:
$$
 A=\begin{pmatrix}1&0\\-g&I_m\end{pmatrix},
 \qquad B=\begin{pmatrix}1&f\\g&I_m+gf\end{pmatrix}.
$$
Their annotations have polynomial circuit size. The inversion premises are original axiom lines and the zero line, and the selected consequence is $-1$. This completes the two translations, with the claimed degree bound in this direction.

## Degree and verification

The proof-line degree can be constant while the circuit annotations encode large-degree polynomials. For comparison, if a variant explicitly caps all matrix-entry degrees by $D_0$ and the inversion matrices have side at most $r$, the first proof gives an ordinary PC simulation of each inversion of degree at most $(2r+2)D_0$. Indeed the adjugate and cofactor identities above have products of total degree at most that bound. Expand their multipliers as monomials and use the ordinary variable multiplication rule on the already derived premises. Across a full proof, the bound is the maximum of this value and the original proof-line degree. This additional assertion is a degree bound, with no circuit-to-sparse size guarantee.

Formal polynomial identity is part of the checking condition for circuit-encoded annotations. The result therefore identifies algebraic size with IPS in this representation. It does not give a deterministic polynomial-time identity-testing procedure, a polynomial bound for the annotated certificate size of arbitrary unsatisfiable systems, or an algorithm for tensor isomorphism.

Status: informal proof. The circuit-annotation convention is explicit and distinct from the proof-line degree in the original PC+INV conjecture.
