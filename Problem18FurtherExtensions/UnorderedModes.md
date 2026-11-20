# Recovering hidden mode permutations in finite-field tensor isomorphism

Let \(d\ge 3\), \(n\ge 2\), and \(V=(K^n)^{\otimes d}\) with dense inputs. Use either the standard bilinear form over \(K=\mathbb F_q\), including in characteristic two, or the standard Hermitian form over \(K=\mathbb F_{q^2}\) with the \(q\)-power involution. Write \(G\) for the corresponding group of isometries of \(K^n\). Allow independent local isometries and an arbitrary permutation of the physical modes, so that the acting group is \(G^d\rtimes S_d\). Count group elements as tuples of a mode permutation and local isometries.

**Theorem.** There is an invariant, deterministically polynomial-time recognizable set \(\mathcal C\subseteq V\) such that for every \(A\in\mathcal C\) and every \(B\in V\), orbit equality and the exact number of transporters can be computed in deterministic polynomial bit time. If a transporter exists, a verified one can be produced in expected polynomial bit time with zero error. The polynomial exponents are absolute, even with variable field, dimension and order. A uniform source has rejection probability \(o(1)\) as the number of entries \(n^d\) grows, uniformly in the shape and the field. For \(n\) large the rejection probability is \(O((1+\log n)/\sqrt n)\), and for \(d\) large it is \(O(e^{-c d})\), with an absolute \(c>0\). For \(d\ge512\), the proportion of tensors whose stabilizer can move any physical mode is at most \(3e^{-d/50}\), uniformly in \(n\) and the field.

The proof uses the ordered higher-order extension of the Lean-verified Problem 1.8 result, and introduces a graph on the physical modes that is computable from the tensor entries. Its edges are quadratic-matrix invariants of two-mode Gram marginals. Correlations between those marginals are controlled by the ranks of operators acting nontrivially on at most two modes. [Problem 1.8](https://github.com/Dugongue/MathProofs/tree/main/Problem18)

## 1. Ordered recovery and the new mode graph

Use the ordered higher-order recovery theorem with a balanced partition into three nonempty groups, with group sizes differing by at most one. Let \(a\le b\le c\) be the grouped dimensions and \(h=c/n\). The ordered recognizer tests two generating matrix algebras, then tests whether the largest grouped flattening has corank less than \(h\). With \(Q=|K|\), its rejection probability is at most

\[
 C(1+\log b)/\sqrt b+\min\{1,4Q^{-h(ab-c+h)}\}.
\]

This is \(O((1+\log n)/\sqrt n)\) for \(n\) large, uniformly in \(d\). Indeed \(b\ge n\) and \(c\le ab\). If \(h\ge n\) the last exponent is at least \(n^2\). If \(h=1\), the balanced groups each have size one and the exponent is \(n^2-n+1\). Once the source passes the ordered test, the ordered theorem gives decision, exact counts and expected polynomial-time witness production for every target using the same partition. It applies to the physical local groups. Its proof recovers projective local matrices from the grouped transporters, including when the grouped flattening has small positive corank, and solves their remaining scalar norm equations. [Ordered higher-order proof](OrderedFoundation.md)

For a pair \(S=\{i,j\}\) of modes, form the \(n^2\)-by-\(n^2\) matrix

\[
 M_S(x)=\operatorname{Tr}_{[d]\setminus S}(xx^*)
\]

using the usual partial trace, where \(x\) is the \(N\)-entry tensor written as a column, \(N=n^d\), and star is the chosen transpose or adjoint. Equivalently \(M_S(x)\) is a flattening times its adjoint. Let \(e_2(M_S)\) be the second elementary characteristic coefficient of \(M_S\), the sum of all its \(2\)-by-\(2\) principal minors. In the Hermitian case this coefficient lies in \(\mathbb F_q\), since transpose preserves it and conjugation of the entries transposes the matrix.

Fix once for the input field a subset \(D\subseteq\mathbb F_q\) of size \(\lfloor q/2\rfloor\) with membership computable in polynomial bit time. For example, compute a basis of \(\mathbb F_q\) over its prime field and use the first \(\lfloor q/2\rfloor\) coefficient strings in base-\(p\) integer order. In the unitary case the basis is obtained as the kernel of the prime-field linear operator \(z\mapsto z^q-z\) on \(K\). Form a simple graph \(\Gamma(x)\) with vertex set \([d]\) by placing edge \(ij\) exactly when \(e_2(M_{\{i,j\}}(x))\in D\). Local isometries conjugate \(M_S\) by the product of the isometries on its two modes. This follows directly from the flattening: the isometries on its column side disappear from the Gram product. Mode permutations permute the marginals and can swap the two physical factors within an individual marginal. Consequently a tensor transporter always induces the corresponding graph isomorphism.

## 2. A rank bound for operators supported on few modes

Call an operator supported on \(S\subseteq[d]\) if it is an arbitrary operator on the tensor factors in \(S\), tensored with identities elsewhere. Over any field, if a nonzero operator \(A\) is a sum of operators supported on at most \(k\) modes, with \(k\le d\), then

\[
\operatorname{rank}(A)\ \ge\ n^{d-k}/2^k.
\]

To prove this, write \(\operatorname{End}(K^n)=KI\oplus L_i\) in mode \(i\), using any vector-space complement of the scalar matrices. The full operator space decomposes into a direct sum indexed by exact supports, obtained by putting \(L_i\) on the support and scalars elsewhere. Choose a nonzero component on a maximum-size support \(S\), with size \(s\le k\). For each \(i\in S\), commute successively with an operator acting only on mode \(i\). After those commutators every other component vanishes, since its support misses at least one of the modes in \(S\). There is a choice of the one-mode operators for which the \(S\)-component survives. In each mode, sending \(X\in L_i\) to the list of commutators \(([B,X])_B\) over a matrix-space basis is injective, because a matrix commuting with all matrix units is scalar. The tensor product of these injective maps is injective, so some coordinate of its output on that component is nonzero. The surviving commutator is supported on \(S\) and has rank at least \(n^{d-s}\). Each commutator increases rank by at most a factor of two. This proves the bound, including \(s=0\) when the operator is a nonzero scalar.

## 3. Joint distribution of the Gram marginals

Let \(P\) be the \(\mathbb F_q\)-linear map sending an \(N\)-by-\(N\) self-adjoint matrix to its tuple of two-mode partial traces, and let \(W=\operatorname{im}P\). The ambient field for each matrix is \(K\). Self-adjoint means symmetric in the bilinear setting, and includes symmetric matrices in characteristic two. Let \(U_W\) be uniform on \(W\). For uniform \(x\in V\),

\[
d_{\mathrm{TV}}\bigl(P(xx^*),U_W\bigr)
\ \le\ \tfrac12 q^{\binom d2 n^4/2-n^{d-2}/8}.
\tag{1}
\]

For the Fourier proof choose a nontrivial additive character \(\psi\) of \(\mathbb F_q\). Every character of \(W\) has the form \(\psi\circ\ell\) for an \(\mathbb F_q\)-linear functional \(\ell\), since this representation is injective and the number of these functionals is \(|W|\). A nonzero \(\ell\) extends to a linear functional on the ambient tuple of smaller matrices. Also \(xx^*\), as \(x\) varies, span the self-adjoint matrices over \(\mathbb F_q\). The coordinate vectors give diagonal matrix units. Evaluating \(xx^*\) at \(e_u+\lambda e_v\) and subtracting its diagonal part gives the off-diagonal coordinates, using \(\lambda\in K\). Thus the polynomial \(x\mapsto\ell(P(xx^*))\) is nonzero as a function when \(\ell\ne0\).

In odd bilinear characteristic and in the Hermitian case in all characteristics, the trace pairing on self-adjoint matrices over the fixed field is nondegenerate. The diagonal coordinates have the ordinary field pairing. The off-diagonal coordinates have twice the ordinary pairing in the symmetric case, and the nondegenerate field trace pairing with an involution in the Hermitian case. Represent the extended functional on the smaller matrices by self-adjoint matrices \(A_S\) via this pairing. Then \(\ell(P(xx^*))=x^*Ax\), where \(A=\sum_S A_S\otimes I_{[d]\setminus S}\). The rank-one spanning result implies \(A\ne 0\). Diagonalizing an odd-characteristic symmetric form gives character average of magnitude \(q^{-r/2}\), where \(r=\operatorname{rank} A\), by the elementary quadratic Gauss sum. Diagonalizing the Hermitian form gives magnitude \(q^{-r}\) over \(K\). In each nonzero Hermitian coordinate the unnormalized character sum is \(-q\), since each nonzero norm value has \(q+1\) preimages and zero has one.

For the bilinear case in characteristic two use the coefficients on the independent entries of the smaller symmetric matrices directly. The quadratic polynomial \(F(x)=\ell(P(xx^*))\) has polar form whose matrix \(A\) is a sum of alternating matrices supported on two modes. This holds because each off-diagonal marginal coordinate sums products of pairs of tensor entries with matching complementary coordinates, while each diagonal marginal coordinate is a sum of squares. When \(A\ne0\), square the magnitude of the character average and use the change of variables \((x,y)\mapsto(x,x+y)\). Orthogonality in the \(x\) variable gives zero outside the kernel of \(A\) in the other variable, yielding the bound \(q^{-r/2}\). If \(A=0\), the polynomial consists of square terms, and some square coefficient is nonzero by the spanning result. The character average is then zero by bijectivity of squaring on \(\mathbb F_q\).

In all three cases each nontrivial Fourier coefficient is at most \(q^{-n^{d-2}/8}\) by Section 2. The uniform law on \(W\) has zero nontrivial Fourier coefficients. Parseval and Cauchy–Schwarz bound total variation by one half times the square root of the sum of squared nontrivial Fourier coefficients. The dimension of \(W\) over \(\mathbb F_q\) is at most \(\binom d2 n^4\), proving (1). For \(d\ge512\), \(n^{d-6}\ge 2^{d-6}\ge 8\binom d2\), the last inequality persisting by induction on \(d\). Hence the bound in (1) is at most \(\tfrac12\,2^{-n^{d-2}/16}\le \tfrac12 e^{-d/50}\) uniformly in \(n\ge2,q\ge2\).

## 4. Asymmetry of the mode graph

First sample uniformly from \(W\). For the marginal on \(S=\{i,j\}\), select its off-diagonal coordinates between row labels \((u,v)\) and \((u',v')\) satisfying \(u\ne u'\) and \(v\ne v'\), treating an off-diagonal entry and its adjoint as one coordinate. These selected coordinates over all pairs vary freely and independently after conditioning on all remaining coordinates. To see this, give the ambient matrix one off-diagonal entry and its adjoint on a pair of full words that differ at exactly \(i,j\), with the desired values on those two modes. Its image has the one requested entry and adjoint in the marginal on \(S\), and zero in every other marginal. The selected coordinate subspace is therefore contained in \(W\). Uniform sampling on any fiber of the complementary coordinates gives a uniform, independent choice of these coordinates.

For a single marginal, use

\[
e_2(M)=\sum_{\alpha<\beta}
 \bigl(M_{\alpha\alpha}M_{\beta\beta}-M_{\alpha\beta}M_{\beta\alpha}\bigr).
\]

There are at least two selected off-diagonal coordinates because \(n\ge 2\). Condition on all but two of them in odd bilinear characteristic, or on all but one in the other cases. The remaining term in the statistic is, up to a translation and a sign, a sum of two independent uniform squares in the odd bilinear case, one uniform norm in the Hermitian case, and one uniform square in the characteristic-two bilinear case. For the sum of two squares, each nonzero value has \(q-1\) preimages if \(-1\) is a square, by rewriting the form as a product of two independent coordinates. It has \(q+1\) preimages otherwise, by viewing the form as a quadratic field norm. In both cases zero has at least one preimage. The Hermitian norm has \(q+1\) preimages for each nonzero value and one at zero. The characteristic-two square is uniform. Consequently each bucket has probability at least \(\delta=1/10\), for every translation and sign. For \(q\ge4\), either bucket contains at least \(\lfloor q/2\rfloor-1\ge q/5\) nonzero values, each having probability at least \((q-1)/q^2\). For \(q=2,3\) every value in the applicable square or norm law has mass at least \(1/9\). Thus after conditioning on the complementary coordinates, all edge indicators are independent and have individual biases within \([\delta,1-\delta]\).

A permutation moving \(k\ge2\) vertices moves at least

\[
k(d-k)+\binom{k}{2}-\lfloor k/2\rfloor
 \ \ge\ k(d/2-1)
\]

unordered pairs. The first count comprises pairs with one moved vertex and pairs among moved vertices, with the only fixed pairs in the second category coming from transpositions. In a cycle of length \(j\ge2\) of its action on pairs, the probability that all edge bits match is at most \((1-\delta)^{j-1}\). This follows by conditioning on the first bit and using independence. Disjoint cycles use disjoint pairs, so a permutation with that support size preserves the graph with probability at most \((1-\delta)^{k(d/2-1)/2}\). There are at most \(d^k\) permutations of support size \(k\). For \(d\ge512\), the ratio \(d(1-\delta)^{(d/2-1)/2}\) is at most \(e^{-d/100}\), using \(\log d+1/20\le 3d/200\). The sum over \(k\ge2\) is therefore at most \(e^{-d/50}/(1-e^{-d/100})\le 2e^{-d/50}\), uniformly over the conditioned values. Inequality (1) gives a bound of \(3e^{-d/50}\) for \(\Gamma(x)\) under the true tensor distribution. A tensor automorphism that moves physical modes gives a nonidentity automorphism of \(\Gamma(x)\), proving the stabilizer assertion.

## 5. Exact algorithm and complexity

First require the source to pass the ordered recognizer for at least one balanced three-part partition. This property is invariant under local isometries and all mode permutations. There are at most \(3^d\) trial partitions, polynomial in the dense input size since \(n\ge2\). Save one passing partition and use it for all ordered comparisons. If \(d\le n\) or \(d<512\), try all \(d!\) mode permutations. For \(d\le n\) one has \(d!\le n^d\). For \(d<512\) the factor \(d!\) is absolute. After reordering the target for a candidate permutation, the ordered algorithm decides its contribution to the transporter count. Sum the exact counts over permutations. Each group element contributes to exactly one summand.

For the remaining values of \(d\), additionally require \(\Gamma(A)\) to be asymmetric. Use deterministic quasipolynomial-time graph isomorphism to test this by individualizing and comparing each pair of distinct vertices. Implement individualization in ordinary GI by adjoining a clique of \(d+2\) new vertices and connecting its first vertex to the marked old vertex by a single edge. The clique is identifiable as the vertices of degree greater than \(d\), and the marked vertex is the unique old neighbor of the clique. Thus the two individualized graphs are isomorphic exactly when an automorphism sends one marked vertex to the other. Then compare \(\Gamma(A)\) and \(\Gamma(B)\). If they are isomorphic, the mode match is unique since \(\Gamma(A)\) is asymmetric. It is recovered by comparing each individualized source graph to the corresponding individualized target candidates. Run the ordered tensor algorithm only for the recovered mode match. The graph comparison constrains the mode permutation, and the ordered call performs the exact tensor comparison for every target. [Babai’s quasipolynomial graph isomorphism algorithm](https://arxiv.org/abs/1512.03547)

Quasipolynomial time on a graph of size polynomial in \(d\) is at most \(e^{O(d)}\), which is polynomial in \(n^d\). All marginals, characteristic coefficients, field operations, source recognizers and ordered calls cost polynomial bit time in the explicit input. The count has at most \(O(d\log d+dn^2\log Q)\) bits because the acting group is a subgroup of \(\operatorname{GL}_n(K)^d\rtimes S_d\). Witness reconstruction uses one accepted ordered call, then applies its selected permutation. For \(b\) above the ordered theorem's absolute cutoff, the precise rejection bound supplied by this proof is

\[
C(1+\log b)/\sqrt b+\min\{1,4Q^{-h(ab-c+h)}\}
+\mathbf 1_{\{d>n,\ d\ge512\}}\,3e^{-d/50}.
\]

The ordered terms here are for any single fixed balanced partition, since accepting any passing partition can only improve coverage. The last term is at most \(3e^{-n/50}\). For growing \(d\), the inequalities \(b\ge 2^{\lfloor d/3\rfloor}\) and \(h\ge 2^{\lceil d/3\rceil-1}\) give exponentially small rejection in \(d\), uniformly in \(n\). Finally \(n^d\) tends to infinity only if \(\max\{n,d\}\) does, so the two uniform bounds give the stated \(o(1)\) rejection as \(n^d\) grows.

## Scope and relationship to existing work

The unordered action includes an unknown permutation on top of the local classical groups. The theorem gives an absolute polynomial bound on a recognized set of raw dense inputs over both finite-field families, as well as a joint probability bound for Gram marginals and an explicit graph whose isomorphisms recover the hidden mode permutation with high probability. It addresses classical local groups, balanced tensor format, and a uniform distribution on the first tensor. Existing related work includes worst-case reductions for classical-group actions and average-case results for fixed-order tensor isomorphism. The new argument is informal and publication priority remains unverified. [Chen, Grochow, Qiao, Tang and Zhang](https://arxiv.org/abs/2306.03135) · [Li, Li, Qiao, Tao and Wang](https://arxiv.org/abs/2604.00591) · [Chizewer et al.](https://arxiv.org/abs/2603.27128)
