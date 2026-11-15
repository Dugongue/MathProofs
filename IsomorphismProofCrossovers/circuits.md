# The published inversion rule collapses Polynomial Calculus degree

**Theorem.** Let $F$ be any field and $f_1,\ldots,f_m\in F[x_1,\ldots,x_N]$ any finite system with no common zero over $\overline F$. In the PC+INV system defined by Galesi, Grochow, Pitassi and She, the system has a refutation of degree at most $\max_i\deg f_i$, with exactly one application of the inversion rule. The inversion instance uses matrices of side $m+1$. The only displayed proof lines are the input equations, the zero polynomial, the constant $-1$ and its rescaling to $1$.

In particular, over every field, every geometrically nonisomorphic pair of 3-tensors has a PC+INV refutation of degree at most 3 for the cubic action and quadratic inverse equations. This disproves Conjecture 1.7 of Galesi, Grochow, Pitassi and She as stated. For tensors over a fixed finite field of order $q$, adjoining the field equations gives the same assertion for nonisomorphism over the base field, with degree at most $\max(3,q)$. [CCC 2023 paper, Conjecture 1.7 and Sections 2.1 and 2.3](https://arxiv.org/html/2305.19320#S2.SS3).

## The exact inference

In Section 2.3, an inversion instance substitutes arbitrary polynomials for the entries of square matrices $A,B$. The rule allows a **single** entry of $BA-I$ as the next proof line if every entry of $AB-I$ already appears as a proof line. Degree is the maximum degree of a polynomial used as a proof line, as specified in Section 2.1. The substitution polynomials are the parameters of the inference. The rule does not ask for their separate derivation or give a syntactic degree bound for them.

## Proof

Write $f=(f_1,\ldots,f_m)$ as a row. By the weak Nullstellensatz, there is a column $g=(g_1,\ldots,g_m)^{\mathsf T}$ of polynomials with
$$
fg=1.
$$
The Nullstellensatz gives this identity over $\overline F$ and it descends to $F$. Indeed, fix the finite monomial supports of the coefficients $g_i$ in a certificate over $\overline F$. Comparing coefficients of $fg=1$ is then a finite linear system with entries in $F$. Gaussian elimination gives a solution over $F$ whenever it has one over $\overline F$.

Use the square polynomial matrices
$$
 A=\begin{pmatrix}1&0\\-g&I_m\end{pmatrix},
 \qquad
 B=\begin{pmatrix}1&f\\g&I_m+gf\end{pmatrix}.
$$
Both have side $m+1$. Multiplication gives the polynomial identity
$$
 AB-I_{m+1}=\begin{pmatrix}0&f\\0&0\end{pmatrix}.
$$
For example, its bottom-right block is $-gf+(I_m+gf)-I_m=0$. Thus the premises are exactly copies of the original $f_i$ and copies of the zero polynomial. List the input equations and derive a zero line by linear combination. Repeated premises can refer to the same line.

The top-left entry of $BA-I_{m+1}$ is
$$
 1-fg-1=-1.
$$
Take just this entry by one application of INV and rescale it to $1$. This proves the claimed degree bound. Neither a high-degree entry of $A$ or $B$, nor any other entry of $BA-I$, is a line of the refutation. The construction also works in characteristic two, where $-1=1$.

For tensor isomorphism, the three action matrices and their three inverse matrices satisfy the stated equations exactly when there is an isomorphism over the solution field. Hence geometric nonisomorphism supplies the no-common-zero hypothesis, and the largest axiom degree is at most 3. Over $\mathbb F_q$, the auxiliary equations $x_j^q-x_j=0$ require every variable value in the algebraic closure to lie in $\mathbb F_q$, so base-field nonisomorphism suffices for the field-equation variant.

## Consequences and proof representation

The inference is a block-matrix encoding of a Nullstellensatz certificate. Its premise product $AB$ cancels all entries involving $g$, whereas the selected entry of the reverse product recovers the certificate. It uses neither a border-rank condition nor a structural promise on the input equations.

The displayed line list has size linear in the sum of the sparse sizes of the input equations, plus a constant number of terms. The actual rule application also needs the substitutions $A$ and $B$, which contain the Nullstellensatz coefficients. Their degree and encoded size can be large. The theorem provides neither a polynomial-time construction nor a polynomial bound for full annotated certificates. It concerns the published proof-line degree. A degree measure charging every entry of the instantiating matrices would require a separate analysis.

Status: informal proof. The source rule and conjecture were checked against the published paper and the arXiv text. A targeted literature search located the original paper and the same rule in Adrian She's thesis. Priority for this argument remains unestablished.
