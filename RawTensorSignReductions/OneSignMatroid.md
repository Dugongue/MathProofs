# An exact Pfaffian sign test from dependencies among factors

This is an informal sufficient reduction of one-sign tensor isomorphism to one ordinary tensor isomorphism instance over \(\mathbb F_3\). The matrix and label dimensions, factor count, and factor multiplicities are unbounded. The factor lines need not span the label dual. The input consists of raw tensor arrays. The hypotheses below specify the promised family.

## The statement

Write the source and target tensors as square matrix pencils \(M_T,M_S\) with contraction arguments in \(W_T,W_S\). The desired sign is that of the left matrix action \(P\) in the ordinary transporter equation \(M_S(Cz)=P M_T(z)Q^{\mathsf T}\). For each pencil, require the space of matrices \(B\) for which every \(M_X(z)B\) is alternating to be one-dimensional, with an invertible generator. Choose a generator by row reduction and multiply the slices on the right by it. Denote the resulting alternating pencil by \(\widehat M_X\).

Suppose the source Pfaffian is nonzero and splits over \(\mathbb F_3\):
\[
p_T(z)=\operatorname{Pf}(\widehat M_T(z))=c_T\prod_{i\in I_T}\ell_{T,i}(z)^{e_i},
\]
with distinct projective linear factors and \(\ell_{T,i}\) normalized by its first nonzero coefficient. For a fixed integer \(k\ge 1\), take the bank of all minimally dependent sets of the factor lines of size at most \(k\). We can also include the full circuits of any intrinsic connected matroid components of nullity one, without a size bound. A circuit type consists of its multiset of factor multiplicities. For each circuit type sum the incidence vectors of all its circuits and keep only the even-size circuit types. If the vector \((e_i\bmod2)_{i\in I_T}\) lies in the binary span of these incidence sums, the tested sign is a computable constant on the entire ordinary transporter set, whenever that set is nonempty. An enlarged sufficient span that also mixes odd circuits is given below.

The reduction returns the original ordinary TI pair if this constant equals the prescribed sign and returns a fixed ordinary TI NO instance otherwise. It runs in deterministic polynomial time at fixed \(k\). No factorization, transporter, ordering correspondence, or target promise is required as input. If the endpoints are ordinarily isomorphic, the target inherits the source conditions.

## Recovering the factor lines

The one-dimensional right-multiplier spaces are kernels of linear equations. Under an ordinary transporter with left and right actions \(P,Q\), the condition that \(P M_T(z)Q^{\mathsf T}B\) be alternating is equivalent to the condition that \(M_T(z)Q^{\mathsf T}BP^{-\mathsf T}\) be alternating. Thus these spaces and the invertible-generator condition are transported. Right rebasings preserve the left action. After the rebasings the right-multiplier space at each endpoint is exactly the line of scalar matrices. Any ordinary transporter of the rebased pencils has \(P^{-1}Q\) scalar: multiply its equation on the left by \(P^{-1}\) and on the right by \(P^{-\mathsf T}\), obtaining an alternating pencil of the form \(\widehat M_T(z)(P^{-1}Q)^{\mathsf T}\). Small scalar rescaling of \(C\) converts it to a congruence transporter with the same \(P\). Conversely any congruence transporter supplies an ordinary transporter. Pfaffian covariance gives
\[
p_S(Cz)=\det(P)p_T(z)
\]
for every congruence transporter. Therefore the set of signs for the raw TI comparison is the set computed on the rebased congruence comparison. [Earlier one-dimensional alternating recovery](https://github.com/Dugongue/MathProofs/blob/main/TensorSignPacking/Pfaffian.md)

The factor lines and multiplicities can be recovered from Pfaffian evaluations by a simple deterministic procedure under the split promise. Let \(d\) be the Pfaffian degree and \(r=\dim W_T\). Work in an explicit extension \(K/\mathbb F_3\) whose cardinality exceeds both \(d\) and \(r(1+d)^2\), and is polynomial in the input length. Find the extension by enumerating irreducible polynomials of the required logarithmic degree. A nonzero linear form has at most \(r-1\) roots on the moment curve \(s\mapsto (1,s,\ldots,s^{r-1})\), so some point \(a\) on that curve has \(p_T(a)\neq 0\). For \(b\) on the same curve, recover \(p_T(b+ta)\) by univariate interpolation in \(t\). Choose \(b\) maximizing the number of distinct roots in \(K\). Because the normalized linear forms \(\ell_i/\ell_i(a)\) are distinct, some \(b\) separates every pair of roots, by the same univariate root bound applied to the pairwise differences. The selected \(b\) therefore separates all roots. Enumerating the elements of \(K\) and successively dividing the univariate polynomial gives each root \(t_i=-\ell_i(b)/\ell_i(a)\) and its multiplicity \(e_i\).

For each coordinate vector \(e_j\), scan \(v\in K\) and test whether
\[
p_T\bigl(b+u e_j+(t_i+uv)a\bigr)=0
\]
for every \(u\in K\). The left side has degree at most \(d<|K|\) in \(u\). It vanishes as a polynomial exactly when some linear factor vanishes identically on this line. At \(u=0\), only \(\ell_i\) vanishes, giving the unique passing slope \(v=-\ell_i(e_j)/\ell_i(a)\). Normalizing the slope vector recovers \(\ell_i\) over the base field. Compute \(c_T\) from \(p_T(a)\) and the factors. The target is processed by the same procedure. On an arbitrary target some of the recovery checks can fail, in which case output NO. If the original ordinary pair is a YES pair, the target is proved split by Pfaffian covariance, so its recovery always succeeds and is exact. The final unchanged ordinary comparison prevents false positives when the target lies outside the promise.

All evaluations use alternating elimination, and the polynomial bounds allow either input mode dimension to grow without restrictions. In the degree-zero case the Pfaffian is constant and its ratio directly gives the sign, with the empty factor bank.

## The circuit calculation

A transporter induces a bijection \(\sigma:I_T\to I_S\) and scalars \(\lambda_i\in\mathbb F_3^\times=\{1,-1\}\) such that
\[
\ell_{S,\sigma(i)}(Cz)=\lambda_i\ell_{T,i}(z),\qquad
\det(P)=\frac{c_S}{c_T}\prod_i\lambda_i^{e_i}.
\]
This uses equality of formal polynomials, and the factors are matched with their multiplicities. The order of factors is immaterial. The normalized coefficient \(c_X\) is essential. If the factor representative \(\ell_{X,i}\) changes by \(\eta_i\in\mathbb F_3^\times\), then \(c_X\) changes by \(\prod_i\eta_i^{-e_i}\) and the corresponding products of relation weights change by the same parity product. Their combination in the determinant formula is unchanged. The argument also allows the two right-multiplier generators to be normalized by unrelated pivot rules. The rebasing changes only the untested right action, and the label rescaling turns the rebased transporter into genuine congruence without changing \(P\).

For every circuit \(D\) choose a nonzero relation \(\sum_{i\in D}b_{D,i}\ell_i=0\), with all coefficients nonzero. The relation space of the restricted vector list is a line. If \(D'=\sigma(D)\), there is \(\alpha_D\in\{1,-1\}\) with
\[
b_{D',\sigma(i)}\lambda_i=\alpha_D b_{D,i}.
\]
For even \(D\), taking products gives
\[
\prod_{i\in D}\lambda_i
=\frac{\prod_{i\in D} b_{D',\sigma(i)}}{\prod_{i\in D} b_{D,i}} .
\]
Inversion of signs has no effect, and the products do not depend on the chosen scaling of either relation.

Multiply this formula over all circuits of a given intrinsic type. The left side has its vector of exponents equal to the sum of their incidence vectors modulo two. The numerator on the right is the product computed over the entire same type at the target, because the same actual \(\sigma\) is a bijection on those circuits. Multiply over the type columns selected by any binary span solution for the requested multiplicity vector. The result is precisely the ratio giving the one sign. The computation needs no factor matching because every selected circuit type is taken in its entirety.

Rank tests recognize circuits of size at most \(k\). To find matroid components, choose a basis from the factor list, compute the fundamental circuit for each nonbasis element, and merge elements sharing such a circuit. Each nonbasis element uses only the basis elements in its resulting component. The spans of different components therefore form a direct sum, proving no circuit can cross components. Conversely every merged set is intrinsically connected through the fundamental circuits that caused the merges. A component of nullity one has a single full circuit because any unused coordinate in the kernel line would be in no circuit, hence a distinct component. To list these circuits simply test nullity and full support. Include each bank circuit once even if it qualifies in both ways. All spans, normalizing products, and coefficients are computed in polynomial time.

## Adding paired relation records

Extend each relation coefficient vector to the coordinate space of all factors by zeros. A pair of distinct bank circuits \(D,E\) with \(h_{D,E}=\sum_i b_{D,i}b_{E,i}\ne 0\) is detected covariantly. Under transport its value is multiplied by \(\alpha_D\alpha_E\), because \(\lambda_i^2=1\) for all \(i\).

For the enlarged span use binary coordinates indexed by factors and by bank circuits. The circuit record for \(D\) contributes the incidence vector of \(D\) on the factor coordinates plus \((|D|\bmod2)\) at its circuit coordinate. Its endpoint weight is \(\prod_i b_{D,i}\), taking the product only over the support. The paired record for \(\{D,E\}\) contributes 1 at both circuit coordinates and zero on factors. Its endpoint weight is \(h_{D,E}\). Group circuit records by the factor multiplicity multiset and group paired records by the unordered pair of circuit types. Compute an incidence sum and a weight product for each type. The transport law shows that each target/source weight ratio evaluates the corresponding product of the current \(\lambda_i\) and \(\alpha_D\). Thus if the vector with factor coordinates \(e_i\bmod 2\) and circuit coordinates zero is in the span of those sums, the same computation recovers the requested sign. This uses at most quadratically many pair records in the computed circuit-bank length. Even circuits are the preceding special case.

## A raw family with unbounded test and label dimensions

Fix \(m\ge 1\) and put \(s=4m\). For each of \(m\) disjoint label triples \(x_j,y_j,z_j\), take the four factors \(x_j,y_j,z_j,x_j+y_j+z_j\). These four factor lines form one four-element circuit. Across the \(m\) label triples the spans form a direct sum. Form the diagonal \(s\times s\) pencil \(A\) from the \(s\) factors and set
\[
M(x,y,z,w)=
\begin{pmatrix}
0&A\\
-A^{\mathsf T}&B(w)
\end{pmatrix},
\]
where the \(w\) coordinates parametrize all alternating \(s\times s\) matrices independently. The Pfaffian is \(\pm\det A\). Every perfect matching term must cover the first \(s\) indices by pairing each with a second-block index. This forces the determinant expansion with a uniform prefactor and leaves no \(B\)-entry.

To check the multiplier condition, write a potential multiplier in blocks \(\begin{pmatrix}P&Q\\R&S\end{pmatrix}\). The pure \(B\) directions show \(BR=0\) and \(BS\) alternating for every alternating \(B\). Taking the elementary matrices \(E_{ij}-E_{ji}\) gives \(R=0\). Their products with \(S\) have only rows \(i,j\), so alternation forces those rows of \(S\) to have no entries outside \(i,j\), forces \(S_{ij}=S_{ji}=0\) from their diagonal entries, and forces \(S_{ii}=S_{jj}\) from their transposed entries. Hence \(S=aI\). The pure \(A\) directions now give \(A^{\mathsf T}P=aA^{\mathsf T}\) and \(A^{\mathsf T}Q\) alternating. Nonzero factors give \(P=aI\), and distinct factor lines force \(Q_{ij}=0\) for \(i\ne j\) from \(\ell_i Q_{ij}=-\ell_j Q_{ji}\). The diagonal entries of \(Q\) vanish too, giving precisely scalar multipliers.

The unique four-circuit type covers all factors exactly once, so the sign test applies. The tested dimension is \(8m\) and the label dimension is \(3m+\binom{4m}{2}\). The factor normals span only \(3m\) dimensions. Arbitrary base changes in all modes preserve the promise. The constant sign on a self-comparison must be \(+1\) because the identity is available. Rebasing only the tested matrix mode by a determinant-\(-1\) map therefore gives ordinary isomorphic but one-sign nonisomorphic examples. This verifies that the family genuinely tests the determinant.

## Scope and research inputs

The study on spectrum-preserving changes asks which downstream features actually change when the observable spectral data are fixed. The exact counterpart here is to retain all ordinary transporter equations while tracking the residual factor scalars under every permitted permutation. The proof sums only genuine incidence records and cancels their relation-line scales, inspired by the archive's use of exact transition verification. The study supplies no algebraic premise. [Pinned spectrum-control study](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a18d98-2e26-7f67-9f50-c6a86e739e72.pdf) · [Pinned exact-verifier study](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a1b00f-3a81-791c-98fd-c5daefe85ff8.pdf)

The earlier Pfaffian test evaluates the whole label table and works when its size is polynomial. The earlier hyperplane-bank argument uses a spanning bank and multiple ordinary TI decisions. The present calibration uses relation signs without a spanning hypothesis, at arbitrary split factor count, and outputs a single ordinary instance on its stated family. The unrestricted many-one question remains open. [Published endpoint question](https://arxiv.org/html/2306.03135v2#S1.SS5)