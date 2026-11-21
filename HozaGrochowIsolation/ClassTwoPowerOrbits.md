# Smaller power orbits for class-two group isomorphism

Suppose \(G,H\) are class-two \(p\)-groups of order \(N\), given by Cayley tables, with a pair of Sun group restrictions. The restriction fixes selected \(z_1,\ldots,z_\zeta\) in the center and selected \(g_1,\ldots,g_\gamma\) in the group. Write \(Z(G)=\langle z_1\rangle\oplus\cdots\oplus\langle z_\zeta\rangle\oplus Y\), and \(A=G/Z(G)=\bigoplus_{i=1}^{\gamma}\langle\bar g_i\rangle\oplus K\), where \(K=FZ(G)/Z(G)\) for the marked subgroup \(F\). The target has the corresponding data, with \(X\) its central complement and \(E\) its marked subgroup. The restrictions include labels that factor through \(F/(F\cap Z(G))\) and \(E/(E\cap Z(H))\).

The input to our algorithm is the read-only output of Sun's extended-vector matching step in a branch that passed the necessary fixed-power tests. In particular we are given matched extended vectors \(a,b\) and the normalized doubled-tuple generators from Lemma 5.24. This is the same algebraic input to the power-recovery stage in Sun's algorithm. Let \(a_i^*,b_i^*\), \(1\le i\le\eta\), be the corresponding quotient-basis lifts in \(F,E\). The extended vectors can also have auxiliary entries. Their quotient orders \(d_i\) match, and \(q_k=\operatorname{ord}(z_k)\) agrees with the corresponding target order. Set
\[
 \mathcal I=\{(i,k):1\le i\le\eta,\ 1\le k\le\zeta,\ q_k\le d_i\},
 \qquad r=|\mathcal I|.
\]
Let \(L\) be the bit length of the explicit input, including the generator matrices and the subgroup and label data. All labels for finite sets are ordered by their input encoding.

## Theorem

1. There is an implicit affine action on \(\mathbb F_p^r\) whose source and target are computable from the branch data. The branch admits a restriction isomorphism exactly when the two states lie in the same orbit. The action has one generator per normalized doubled-tuple generator. Its coordinates come only from cyclic-basis powers. When \(r=0\), the matched vectors and fixed-power tests alone suffice to produce an isomorphism.
2. One can deterministically decide the branch and output the full table of a restriction isomorphism using \(O(\log L+r\log p)\) work bits and \((Lp^r)^{O(1)}\) time. This replaces a search over up to \(p^{\phi\zeta}\) states, where \(\phi\) is the extended-vector length. The machine constructs transitions from the group tables and tuple matrices and never constructs the state graph.
3. Using the equality \(\mathsf{NL}=\mathsf{UL}\) of Hoza's preprint, the same space and time bounds hold for an unambiguous transducer that outputs the lexicographically first shortest positive generator word from the source to the target, followed by an actual restriction isomorphism. The order is that of the supplied generator list. The shortest word is for this quotient action, and each adjustment to a basis lift after the word has been selected is handled by a deterministic table scan.

The first two statements are unconditional. All work-space bounds exclude the read-only branch data and the write-only output. No space bound for the earlier tensor and tuple computations is needed. The time bound is polynomial in the implicit orbit bound \(p^r\) and the supplied data size. Selecting a shortest word is a route selection within one normalized branch, with the supplied basis and generator labels fixed. [Sun, *Faster Isomorphism for Groups of Class 2*, Lemma 4.4 and §§5.4–5.5](https://arxiv.org/html/2611.05920v1) · [Hoza, *NL = UL*, Theorems 1.1 and 1.3](https://eccc.weizmann.ac.il/report/2026/323/).

## Pair actions from the normalized matrices

We use representatives in the source group. Let \(v\) be an admissible extended vector matching \(a\), and \(v_i^*\) its cyclic-basis lifts. It comes with an automorphism \(U_v\) of \(A\) fixing the \(\bar g_i\) and sending \(\overline{a_i^*}\) to \(\overline{v_i^*}\). It also comes with \(H_v\) on \(Z(G)\) fixing all \(z_k\) and carrying the \(Y\)-projections of the first \(\psi\) entries of \(a\) to those of \(v\). These are genuine abelian automorphisms because the displayed elements are ordered cyclic bases with the same orders. They preserve commutators in the sense
\[
 [U_v x,U_v y]=H_v[x,y]\qquad(x,y\in A).
\]
This follows from matching on the basis consisting of the fixed quotient generators and the cyclic-basis lifts, then bilinearity. For any auxiliary entry \(a_j\), matching also gives \(\bar v_j=U_v\bar a_j\). Indeed, the difference brackets to zero against every vector of the transported basis. The commutator map on \(G/Z(G)\) has trivial common radical.

Write \(v\cdot P\) for applying the ordered products of a normalized block-diagonal generator to \(v\), as in Sun's Lemma 5.25. Put \(U_P=U_{a\cdot P}\) and \(H_P=H_{a\cdot P}\). Then
\[
 U_{v\cdot P}=U_v\circ U_P,\qquad H_{v\cdot P}=H_v\circ H_P.
\]
For \(U\), use the equality on all auxiliary quotient coordinates in the ordered products. For \(H\), Claim 5.22 gives that the central output coordinates of the block-diagonal matrix involve only central inputs. The \(Y\)-projections of the distinguished central entries following the first \(\psi\) entries are zero. The remaining projections transform linearly under \(H_v\), proving the formula. The elementary central adjustments in Sun's algorithm have the identity pair. Only their effect on powers is relevant below. [Sun, Claim 5.22 and Lemma 5.25](https://arxiv.org/html/2611.05920v1#S5.SS5).

## Coordinates needed for powers

For each cyclic lift \(v_i^*\), write \(\alpha_{ik}(v)\) for the exponent of \(z_k\) in the central element \((v_i^*)^{d_i}\), represented in \([0,q_k)\). Its residue \(\ell_{ik}\) modulo \(\lambda_k=q_k/p\) is constant under matching. Thus \(\alpha_{ik}(v)=\ell_{ik}+\lambda_k\theta_{ik}(v)\), with \(\theta_{ik}(v)\) a single digit in \(\mathbb F_p\). Retain only \(\theta_{ik}\) for \((i,k)\in\mathcal I\). The target coordinates come from \(b_i^*\) in the corresponding center decomposition.

Fix \(P\). Write the action of \(U_P\) on \(K\) in the cyclic basis, taking representative coefficients \(u_{ji}\in[0,d_j)\) for the image of basis element \(i\). Thus \(d_j\mid d_i u_{ji}\). The quotient identity above shows that \((v\cdot P)_i^*\) is \(\prod_j (v_j^*)^{u_{ji}}\) times a central element. If \((i,k)\) is retained, raising to \(d_i\) kills the \(z_k\)-component of that central factor, since \(q_k\mid d_i\). Write \(\beta_{ljk}\) for the \(z_k\)-coefficient of \([v_l^*,v_j^*]\). By matching it is independent of \(v\). The ordered-product power identity in a class-two group gives, modulo \(q_k\),
\[
 \alpha_{ik}(v\cdot P)\equiv
 \sum_j C_{ij}\alpha_{jk}(v)
 +\binom{d_i}{2}\sum_{j<l}u_{ji}u_{li}\beta_{ljk},
 \qquad C_{ij}=\frac{d_i u_{ji}}{d_j}.
\]
This uses \(d_j\mid d_i u_{ji}\) to express individual powers in terms of \((v_j^*)^{d_j}\). Take the digit at \(\lambda_k\) by integer division and then reduce modulo \(p\). The resulting affine update is
\[
 \theta'_{ik}
 =\sum_{j:q_k\le d_j} C_{ij}\theta_{jk}
 +\left\lfloor
   \frac{\sum_j C_{ij}\ell_{jk}+\binom{d_i}{2}\sum_{j<l}u_{ji}u_{li}\beta_{ljk}}
        {\lambda_k}
  \right\rfloor \pmod p.
\]
The omitted digits have coefficient zero modulo \(p\), since \(d_j<q_k\le d_i\) implies \(p\mid d_i/d_j\). This derivation uses only quotient-basis lifts, including for computing the new basis digits. In particular it does not need the power digits of any auxiliary entry or of the central entries of the extended vectors.

Each displayed affine map is a permutation of the full ambient space. To see this let \(D=\operatorname{diag}(d_1,\ldots,d_\eta)\). The integer matrix \(C=D u^{\mathsf T}D^{-1}\) has determinant prime to \(p\), because \(u\bmod p\) is the automorphism induced by \(U_P\) on \(K/pK\) in its given basis. For each \(k\) list first the basis rows with \(d_i<q_k\). Then \(C\bmod p\) has a zero block from the discarded columns into the retained rows, so the retained square block is invertible. This proves invertibility separately in every \(k\)-column. It is important that this argument holds on every formal digit vector, including ones that are not realized by the source group.

## Exactness of the smaller orbit and construction of a witness

Sun's Theorem 5.1 and Lemma 5.26 imply that an isomorphism puts the target full power state in the original orbit. A normalized generator induces the affine map just proved. An elementary central adjustment induces the identity on the retained digits. Hence an isomorphism puts the target retained state in the smaller orbit.

Conversely, suppose a positive word sends the source retained state to the target. Applying the same ordered products to \(a\) gives a mathematical witness vector \(v\) by Lemma 5.25. It agrees with \(b\) on the retained powers, since the lower digits were fixed. The only possibly different \(z_k\)-powers of cyclic-basis lifts occur at \(d_i<q_k\). For each such pair the element
\[
  z_k^{\,q_k/(p d_i)}
\]
lies in \(F\cap Z(G)\) and its \(d_i\)-th power is \(z_k^{\,q_k/p}\). This is exactly Sun's elementary central adjustment for a noncentral row. Multiplying a lift by it increments the selected top digit, while preserving the quotient image, the label, every commutator, and every other power coordinate. Thus all the missing cyclic-basis powers are independently correctable. The central entries of the extended vector need no comparison of their own top digits. The center map fixes the full \(z_k\) and matches the projected \(Y,X\) bases, which is all the center basis required in Lemma 4.4. That lemma yields a restriction isomorphism once the quotient-basis powers and commutators agree, with the already checked fixed-generator powers. [Sun, Lemma 4.4 and proof of Lemma 5.25](https://arxiv.org/html/2611.05920v1).

The same conclusion holds for a signed word. Each letter acts by a permutation on the digit space, on \(A\) and on \(Z(G)\). In the finite direct product of these three permutation groups, its inverse is a positive power of that letter. Therefore the signed word gives the retained state and basis maps of some actual admissible vector. This is an existence argument. The algorithm evaluates signed permutations directly, so the potentially long replacement word is irrelevant to its running time.

To construct the actual isomorphism, it is enough to compute \(U_v,H_v\) as needed. Compute the inverse map from \(H\) to \(G\). Send the target \(z_k'\) and \(g_i'\) to their prescribed counterparts. Send each projected \(X\)-basis element of \(b\) to the image under \(H_v\) of the corresponding projected \(Y\)-basis element of \(a\). This defines the center map \(\sigma:Z(H)\to Z(G)\). For each target quotient lift \(b_i^*\), find the least \(x\in F\) such that
\[
 \bar x=U_v(\overline{a_i^*}),\qquad x^{d_i}=\sigma\bigl((b_i^*)^{d_i}\bigr).
\]
Existence was proved by the elementary adjustments. Any two choices differ by a central element of \(F\), so changing the choice does not affect a commutator or the quotient label. The ordered normal-form map from the target group now gives the desired table of a restriction isomorphism. The maps with these fixed center and quotient actions have cardinality \(\prod_i |(F\cap Z(G))[d_i]|\), since for each lift the choices are one coset of the \(d_i\)-torsion subgroup. Each factor can be counted by a table scan. This count is conditional on the fixed pair \(U_v,H_v\), without requiring enumeration of other pairs.

## Space and unambiguity

The branch data supply cyclic generators on both center and quotient. Cyclic-basis coordinates can be extracted by scanning mixed-radix products and comparing group elements or quotient cosets. An enumeration of a full normal form, including marked generators and the center, has exactly \(N\) candidates. A central projection can also be computed by enumerating the products of \(z_k\) and checking membership in \(Y\), given by the supplied subgroup data. Orders, powers, cosets and commutators require only a constant number of current Cayley-table elements and counters. All these use \(O(\log L)\) bits and polynomial time in \(L\), including the construction of any requested coordinate of \(U_P,H_P\). In computing a generator's ordered products, stream each exponent modulo \(N\) before exponentiation. Thus the algorithm does not need extra workspace proportional to the exponent's bit length in the matrix. The carry computation in the affine transition sums a polynomial number of terms of magnitude at most \(N^{O(1)}\). Storing one current digit vector costs \(O(r\log p)\) bits. The graph can therefore be simulated by read-only access to virtual edge bits in \(S=O(\log L+r\log p)\) space and polynomial time in \(Lp^r\) per query.

For unconditional search, use Reingold's deterministic log-space undirected path algorithm on the virtual graph made by ignoring the directions of the permutation edges. The graph has \(p^r\) states and its adjacency test scans the supplied generators. Each such path step gives a signed letter by scanning for either an edge or its reverse and using the first match. Since the actions are permutations, undirected reachability equals membership in the original positive orbit. The path procedure is a deterministic log-space transducer, so it can be replayed for any requested letter. In dimension zero the source and target are the unique state, so take the empty word without reading the generator list. [Reingold, *Undirected Connectivity in Log-Space*](https://omereingold.wordpress.com/wp-content/uploads/2014/10/sl.pdf).

For the shortest positive word, let \(Q=p^r\). The existence of an exact-length \(j\)-letter walk between two states is a directed reachability query on at most \(Q\) layers for \(0\le j<Q\). A shortest walk never repeats a state. The virtual graph for a length query may use an intermediate vertex \((t,x,P)\) between the state vertices \((t,x)\) and \((t+1,P(x))\). Distinct generator labels then remain distinct on a simple layered graph, as required by Hoza's weight-isolation theorem. The vertex count is polynomial in \(LQ\). Theorem 1.1 and closure of \(\mathsf{NL}\) under complement give unique signed answers to each query. Specifically, guess yes or no and invoke the corresponding unambiguous recognizer, then continue only on its accepting branch. Sequential queries therefore have exactly one surviving computation when the transducer returns a result. To find the word, scan lengths for the smallest feasible one. At each step scan the ordered alphabet and select the first letter from whose successor the remaining exact-length query is positive. This canonically gives the lexicographically least word among shortest positive routes. A negative instance has a unique computation reporting failure.

Every lookup of a selected route letter can be repeated with the same unique signed answers. To evaluate \(U_v\) or \(H_v\) on one argument, replay letters in reverse order of the selected word, since a new letter composes on the right in the pair formulas. The inverse of any single generator's permutation on \(A\) or \(Z(G)\) can be computed by scanning at most \(N\) candidates. Only the current group or quotient element and replay counters are needed. In an output-table loop, use these point queries for the normal-form generators and for the least-lift tests. This gives the claimed work bits and time. The same reasoning includes the recomputation cost of a polynomial number of route lookups for each output element. The graph of permutations gives unconditional low-space search, while the preprint supplies the exact shortest positive selector in the same space. [Hoza, Theorems 1.1 and 1.3](https://eccc.weizmann.ac.il/report/2026/323/) · [Reinhardt–Allender, *Making Nondeterminism Unambiguous*](https://doi.org/10.1137/S0097539798339041).

## Scope and provenance

This refines the power-recovery step already used to produce isomorphisms in the earlier class-two witness-and-count algorithm. The improvement is algebraic as well as computational. All auxiliary power rows, all central rows, and each individually correctable \(z_k\)-coordinate are unnecessary for this witness search. The affine permutation quotient and the reconstruction via the paired center and quotient actions give the smaller state bound even for \(p=2\) and arbitrary exponent. The earlier breadth-first method stored an admissible vector at each state. Here the only orbit data needed are one digit vector and access to a route. The argument concerns the matching branch and its supplied tuple generators, and does not settle unrestricted group isomorphism, group epimorphism, or canonical labeling. The argument is a written proof. Exact controls compared 1,800 mixed-order digit predictions at \(p=2,3,5\) with group multiplication, tested 12 induced affine permutations on their entire state spaces, and exercised nonzero dyadic commutator carries. Broader search-to-decision and counting-to-decision reductions in the earlier exponent-\(p\) setting use tensor isomorphism. [Sun, §§4–5](https://arxiv.org/html/2611.05920v1) · [Grochow–Qiao, *On p-Group Isomorphism*](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2021.16).
