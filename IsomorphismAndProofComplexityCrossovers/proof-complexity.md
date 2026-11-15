# Sparse Polynomial Calculus simulation of inversion over finite-field equations

## Theorem

Let $F$ be a field containing $\mathbb F_q$ and let $f_1,\dots,f_m\in F[y_1,\dots,y_N]$ be an equation system. Include the field axioms $y_i^q-y_i=0$. Let $A_0=\max(1,\max_j\deg f_j)$. Choose positive integers $w_i$ in binary and set $\Phi(y_i)=x_i^{w_i}$. Consider a sparse Polynomial Calculus with Inversion refutation of the pulled-back equations
$$
\Phi(f_j)=0,\qquad x_i^{w_iq}-x_i^{w_i}=0.
$$
At an inversion inference, matrices $A,B$ of side $r$ are supplied in sparse form, each entry of $AB-I_r$ references an earlier line, and a selected entry of $BA-I_r$ is the new line. Let $S$ be the total written size, including the original input, all proof lines, matrix annotations, exponent bits, matrix dimensions and premise references. Put
$$
R=F[x_1,\dots,x_N]/(x_i^{w_iq}-x_i^{w_i}:1\le i\le N).
$$
Assume that for each inversion inference every $(k+1)$-minor of $AB-I_r$ vanishes in $R$, with a common $k\ge 0$. If $r\le k$ this condition is vacuous.

Then the base equations $f_j=0$ and $y_i^q-y_i=0$ have an ordinary PC refutation with size at most
$$
  (2+N+q+A_0+S)^{C(k+1)}
$$
for an absolute $C$. The bound counts sparse monomial occurrences and also bounds the number of arithmetic operations in an explicit construction with a supplied bound $k$. The construction uses arithmetic on exponent encodings in addition to field operations. For fixed $q,k$ and a fixed finite coefficient field, it runs in deterministic polynomial binary time when the base input has polynomially bounded degree. The bound has no dependence on the values of the weights beyond their encoding lengths. It also applies to a proof of any pulled-back consequence, producing a base derivation of that consequence's separately reduced representative.

For $w_i=1$, the hypothesis is that $\operatorname{rank}(AB-I_r)(z)\le k$ for every $z\in\mathbb F_q^N$, with rank taken over $F$. This need only hold on the finite cube. More generally, if every annotation is in the image of $\Phi$, the same condition on the corresponding base annotations suffices for arbitrary weights. For annotations over $R$ formed using arbitrary $x$-polynomials it is the stated condition on minors in $R$ that is used.

## Normal forms and transport of ordinary lines

In
$$
K=F[y_1,\dots,y_N]/(y_i^q-y_i:1\le i\le N)
$$
the coefficient representatives have individual degrees below $q$. A positive exponent $a$ reduces to $1+(a-1)\bmod(q-1)$, and exponent zero stays zero. The reduced monomials form a basis by successive division by the monic relations. A reduced polynomial vanishing at every point of $\mathbb F_q^N$ is zero, by induction on $N$ using the univariate root bound. Thus $K$ is the algebra of $F$-valued functions on the cube.

The monic relations in $R$ likewise give a unique representative with the $i$-th exponent below $w_iq$. Write such an exponent as $\rho_i+w_i b_i$, with $0\le \rho_i<w_i$ and $0\le b_i<q$. This identifies $R$ as a free $K$-module with basis $x^\rho$. As a computational representation, each input monomial contributes at most one representative, since while its exponent is at least $w_iq$, the relation subtracts $w_i(q-1)$. The result is equivalently obtained by taking the residue $\rho_i$ and reducing $b_i$ by the $K$ rule. Coefficients with the same residue and same base monomial are combined. Thus a sparse line $P$ yields at most as many total base monomial occurrences as in $P$, distributed among the coefficients $P_\rho(y)$ in
$$
 [P]=\sum_\rho x^\rho\Phi(P_\rho)\in R.
$$

We maintain ordinary PC derivations of the reduced $P_\rho$ for each original line. Field axioms of the pulled-back system have zero representative. Another input axiom contributes only its zero-residue coefficient, which is the normalized $f_j$. To derive that representative, subtract monomial multiples of $y_i^q-y_i$, applying one lowering operation at a time starting from $f_j$. This costs polynomially in $A_0,N,q$ and its sparse input length. Ordinary PC implements each monomial multiple by repeated multiplication by variables. A proof line of large formal degree later in the proof is processed through its representatives, so only the base-input degree enters this initialization cost.

Linear combinations act coefficientwise. Multiplication by $x_i$ changes the residue by one modulo $w_i$, with a multiplication by $y_i$ precisely on a carry. At each multiplication by $y_i$, a reduced input coefficient has exponent at most $q-1$ in $y_i$, hence the product has exponent at most $q$. For each term reaching $q$, subtract the corresponding monomial multiple of the field axiom once. This derives the normalized product at polynomial cost in $q,N$ and the input support, with no support expansion. A monomial multiplier $x^\sigma\Phi(y^\beta)$ in normal form sends the input residue $\rho$ to $\rho+\sigma$ modulo $w$, and multiplies its base coefficient by $y^{\beta+\delta}$, where each $\delta_i$ is the carry bit. The base multiplication uses at most $Nq$ variable multiplications with the same normalization. Only residues actually present in a line or in a product are enumerated.

## Transport of inversion lines

For the given step put $E=AB-I_r$ and $J=BA-I_r$, and perform the following calculations in $R$. Over any commutative ring the universal identity
$$
B\operatorname{adj}(AB)A=\det(AB)I_r
$$
holds, since it holds over the rational function field of generic integer-coefficient matrices and is an identity of integer polynomials. The matrix $E$ commutes with $\operatorname{adj}(I_r+E)$. This can also be verified generically and specialized. It follows that
$$
B E\operatorname{adj}(I_r+E)A=\det(I_r+E)J.
$$

Write $\det(I_r+tE)=\sum_{j\ge 0}c_jt^j$ and $\operatorname{adj}(I_r+tE)=\sum_{j\ge 0}M_jt^j$. Expansion along the selected identity entries expresses $c_j$ as a sum of principal $j$-minors and each entry of $M_j$ as a signed sum of $j$-minors. By Laplace expansion, the hypothesis on $(k+1)$-minors implies every larger minor vanishes in $R$ as well. Thus $c_j=M_j=0$ for $j>k$. The coefficient of $t^{k+1}$ in
$$
(I_r+tE)\operatorname{adj}(I_r+tE)=\det(I_r+tE)I_r
$$
gives $E M_k=0$. For $k=0$, $E=0$ and the same universal identity gives $J=0$. For $k\ge 1$, substitute $t=1$ in the truncated expansions to obtain
$$
J=B E\left(\sum_{j=0}^{k-1}M_j\right)A-J\left(\sum_{j=1}^{k}c_j\right).
$$

For each selected entry of $J$, the first term exposes one premise entry in $E$. Expand the determinant terms in the second sum and select one entry of $E$ in each product. After these selections the right-hand side is a sum of premise entries times products of polynomial entries of $A,B,E,J$, with $O(k+1)$ factors per product. The $E,J$ multiplier entries are computed directly from $A,B$, so this calculation uses no as-yet underived conclusion as a proof premise. The number of summands is $r^{O(k+1)}$. Indeed a cofactor coefficient of order $j$ chooses at most $j$ surviving nonidentity rows and columns, and then chooses a permutation of these $j$ positions.

Expand each multiplier in reduced sparse form using monomial multiplication in $R$. Since a monomial reduces to one monomial, expanding a product of $O(k+1)$ sparse factors costs $(S+2)^{O(k+1)}$. Now apply the monomial multiplier rule from the preceding section to each exposed premise coefficient. It derives each product's contribution in the correct output residue over $K$. Regrouping and linear combination derives the coefficients of the selected $J$-entry. The combination size is polynomial in the expanded term count, which preserves the asserted bound. This process can compare the computed coefficients with the input conclusion's representatives by sparse equality, giving a direct check of the simulation. It can also test the rank promise by expanding and normalizing all $(k+1)$-minors. Both costs fall within the same bound. When the original last line is $1$, its zero-residue coefficient is $1$, yielding the ordinary PC refutation.

## Consequence for concise tensor and succinct group isomorphism

Fix $q$. On the explicit concise tensor families in each fixed characteristic, and the special-group families in their succinct structure-constant representation over each fixed prime field, the base PC sparse-size lower bound is $2^{c n}$ for some $c>0$ and the base input degree is bounded. Here $n$ denotes the tensor side or log-order, respectively. Charge the base input and the pullback weights to the proof description. Their sizes ensure $N$ and $A_0$ are bounded by a polynomial in $S+2$ on these families. The theorem gives
$$
 (S+2)^{O(k+1)}\ge 2^{c n},
 \qquad
 \log(S+2)=\Omega\!\left(\frac{n}{k+1}\right).
$$
In particular, polynomial-size certificates on these families require $k=\Omega(n/\log n)$. This also holds after pure-power pullbacks with binary-encoded weights. For the original finite-field presentation the parameter is the maximum numerical rank over the whole finite cube. For example, $E=(x^q-x)I_r+x\,e_{11}$ has full formal rank but numerical rank at most one. [Concise tensor families](https://github.com/Dugongue/MathProofs/blob/main/InversionProofComplexity/concise-separation.md) · [Succinct special-group families](https://github.com/Dugongue/MathProofs/blob/main/InversionProofComplexity/special-group-separation.md)

## Degree refinement

Give $x_i$ rational weight $1/w_i$. Let $L$ be the maximum such degree of the reduced representatives of the original proof lines. Let $D$ be the maximum sum of the two reduced matrix-entry degree bounds over the inversion annotations, using zero as the degree of a zero or constant matrix. The constructed ordinary PC degree is at most
$$
  \max\{q,A_0,L+1,(k+1)D\}.
$$
Indeed the $y$-degree of an output coefficient monomial with residue $\rho$ is the rational weight of its unreduced $x$-monomial minus $\sum_i\rho_i/w_i$. Reduction by a field relation always lowers degree. During normalization of a variable multiplication, every line uses degree at most the degree of the just-multiplied coefficient and $q$. For an inversion, before reducing, each product in the displayed identity has at most $k$ factors from $E$ and either one each from $A,B$ or one from $J$. Its rational weight is at most $(k+1)D$. Process each monomial multiplier by variable multiplication in the base ring, reducing at each step. Each intermediate normalized product and each correction term has degree at most the weight of its full unreduced product or $q$. The degree bound follows across every rule. On the stated lower-bound families, $L=o(n)$ and $D=O(1)$ therefore force $k=\Omega(n)$.

## Polynomial-size inversion refutations after large pure-power pullbacks

A derived line $f=0$ can be multiplied by a monomial $g$ in one rank-one inversion and one scalar rescaling. Set
$$
 A=\begin{pmatrix}1&0\\-g&1\end{pmatrix},\qquad
 B=\begin{pmatrix}1&f\\g&1+gf\end{pmatrix}.
$$
The displayed premise matrix is $AB-I=\begin{psmallmatrix}0&f\\0&0\end{psmallmatrix}$ and the chosen reverse entry is $-gf$. The annotations remain sparse since multiplication by a monomial preserves support. This is the coefficient multiplication instance of the earlier block identity. [MathProofs block identity](https://github.com/Dugongue/MathProofs/blob/main/IsomorphismProofCrossovers/circuits.md)

Substitute the pure powers into the earlier polynomial-size charged refutations. Linear combinations and the original inversion steps transfer by polynomial substitution, which preserves the support of each polynomial. Each ordinary multiplication by $y_i$ becomes multiplication by $x_i^{w_i}$. The displayed two-by-two inference implements it using support at most that of the old line plus constants and exponent encodings. For weights of polynomial binary description length, the prior concise tensor and succinct group families therefore still have polynomial-size charged refutations. There is one inversion of side $O(n)$ from the previous construction, and the additional inversions have side two and defect rank at most one. The exponential size lower bounds for constant defect rank apply to these same pulled-back instances. The original rank principle supplies the large-side inversion and the sparse coefficient simulation supplies the quantitative bound for the restricted system. [Concise tensor certificate](https://github.com/Dugongue/MathProofs/blob/main/InversionProofComplexity/concise-separation.md) · [Succinct group certificate](https://github.com/Dugongue/MathProofs/blob/main/InversionProofComplexity/special-group-separation.md)


## Primary comparison and evidence

Galesi, Grochow, Pitassi and She introduce the inversion inference, prove a matrix-side-dependent ordinary PC degree upper bound, and prove linear ordinary-PC degree lower bounds for the rank principle. The earlier MathProofs note reduces the dependence to formal defect rank times annotation degree and gives a polynomial sparse simulation under simultaneous constant caps. The parallel exact pullback proof permits degree descent along a filtered free basis and sparse descent for pure powers. The argument here carries out the inversion elimination directly in the finite function algebra and then performs coefficient descent on only the occupied monomials, which removes annotation degree, allows pointwise rank, and avoids materializing the full pullback basis. The primary-source search did not establish priority. This is an informal proof. [Galesi–Grochow–Pitassi–She, §§2.3, 3.2–3.3](https://arxiv.org/html/2305.19320#S2.SS3) · [Earlier rank-sensitive simulation](https://github.com/Dugongue/MathProofs/blob/main/InversionProofComplexity/rank-sensitive.md) · [Earlier exact pullback](https://github.com/Dugongue/MathProofs/blob/main/InversionProofComplexity/bounded-rule.md) · [Riis, Lemma 14.1](https://arxiv.org/html/2611.07280v1)

The shared DAG lookup found the Mathlib adjugate identity in the Axiom CFSG and recent Mathlib source catalogs, and found the corresponding monic-division and multivariate evaluation sources. Those entries are source evidence. An independent finite control computed the truncated adjugate identity on 18 exact matrices over the weighted binomial quotient rings in characteristics two, three and five. It also checked 2,160 residue carry identities using random 256-bit exponents, with weights up to $2^{52}+1$.
