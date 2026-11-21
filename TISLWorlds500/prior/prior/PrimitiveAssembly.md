# Removing the matching bottleneck in square-zero orientation

Work over \(F=\mathbb F_3\) with explicit coefficient tables. The earlier square-zero lemma reduces exactly to testing \(\det(g)\det(h)=1\) for a transporter of a symmetric bilinear map \(\beta:X\times X\to Z\), where \(\beta\) has zero common radical and spans \(Z\). The map \((g,h)\) is a transporter when \(h\beta(x,y)=\beta'(gx,gy)\). This section proves a single ordinary TI compiler on any collection of primitive factors with ordinary local sign tests. There is no bound on how often an ordinary factor type can occur. [Reference square-zero carrier](earlier/SquareZeroClosure.md)

## 1. Compute the intrinsic summands

The centroid consists of pairs \((P,Q)\) with
\[
\beta(Px,y)=\beta(x,Py)=Q\beta(x,y).
\]
It is a commutative algebra in the product of the two endomorphism rings. Closure under multiplication follows by moving each operator across the bilinear map. For commutativity evaluate \(\beta(Px,P'y)\) in the two possible orders to see that \(Q,Q'\) commute on the spanned output. The zero common radical then forces the same on \(X\). A transporter acts on this algebra by conjugation on both roles. Each primitive idempotent gives a summand on both roles, with cross products zero because \(\beta(e x,f y)=ef\beta(x,y)\). Conversely a collection of independent summand transporters for a bijection of primitive factors assembles to a full transporter.

The centroid is a linear kernel. Over \(F\) its cube-fixed subalgebra is a product of one copy of \(F\) per primitive local factor. Indeed each local residue field has exactly \(F\) as its cube-fixed field, and an element differing from its fixed residue scalar by a nonzero nilpotent cannot be cube-fixed. Refine the unit by the idempotent indicators \(1-(x-a)^2\) for the three \(a\in F\) and for a basis of the cube-fixed algebra. On each current idempotent slot use the corresponding unit of that slot. The fixed basis separates all factors, so this gives all primitive idempotents by linear algebra and multiplication. There are only polynomially many slots at any stage. Use displayed based summands throughout. [Wilson, bilinear map decomposition](https://arxiv.org/abs/1005.0548)

## 2. Combine arbitrary repeated types in one ordinary query

**Theorem.** Suppose the local transporter sign tests
\[
\exists(g_i,h_i):\beta_i\longrightarrow\beta'_j,\qquad
\det g_i\,\det h_i=s
\]
have uniform deterministic polynomial-time ordinary-TI compilers for \(s=\pm1\) on the allowed primitive local factors. Include the same tests between source factors. Then the signed comparison of the full square-zero spaces has a deterministic polynomial-time many-one reduction to ordinary TI, with no bound on the multiplicities or the number of factors. A factor known to admit an odd self-transporter needs no signed solver, since it already corrects orientation on the whole pair.

Fix a desired sign in the original frames. Compute a known sign calibration \(\kappa\) by replacing the two full coordinate orders with interleaved blocks \(X_i\oplus Z_i\). A permutation of such blocks of dimensions \(d_i=\dim X_i+\dim Z_i\) contributes the permutation sign of the subsequence of odd-dimensional blocks. Adjacent swaps have determinant \((-1)^{d_i d_j}\), which proves this formula regardless of the sizes of the even blocks. The remaining determinant is the product of the local signs. Check that the original formats are compatible and include an **ordinary guard** \(G\) on the full pair. The guard is one comparison by the typed-system compiler, or by the multiplication tensors of the local algebras. It guarantees an ordinary matching of the blocks.

Test **flexibility** on the source by the positive disjunction of two finite lists of ordinary TI tests:

- some primitive factor has an odd self-transporter (a local sign test)
- two distinct odd-dimensional factors are ordinarily isomorphic (an ordinary local comparison)

In the first case use the odd automorphism on that factor and the identity elsewhere. In the second case swap the two odd factors using one isomorphism and its inverse, whose local determinants cancel. In either case there is an odd source automorphism, so the ordinary guard implies the full signed answer is YES. Conversely if both tests fail, all local signs are rigid, odd source factors have pairwise distinct ordinary types, and every source automorphism is even. A block permutation can exchange only equal ordinary types and hence only even-sized blocks, while all the block-preserving signs are one.

We need a second ordinary query that is correct when \(G\) holds and flexibility fails. It can have arbitrary behavior on flexible or ordinary-NO instances. In this rigid case use the following two tests.

**Odd block permutation.** Form the square matrix indexed by the odd source and odd target blocks whose entry is the bit of the ordinary isomorphism test for that pair. Under the two promises it is a permutation matrix. In each row any entry has a complementary ordinary query given by the disjunction of its competitors in that row, which is complementary on this domain. The earlier query-dependent determinant compiler tests whether the permutation sign is \(+1\) or \(-1\), as a single ordinary query for either specification. If there are no odd blocks, use the constant sign \(+1\).

**Local sign sum.** For each source and target pair and each \(s\in\{\pm1\}\), create a binary variable \(z_{ij,s}\) enabled by its local sign test. Impose
\[
 \sum_{j,s} z_{ij,s}=1\quad(\text{each }i),\qquad
 \sum_{i,s} z_{ij,s}=1\quad(\text{each }j)
\]
in \(\mathbb F_2\), together with a specified value for \(\sum_{i,j}z_{ij,-}\). These equations compile by the ordinary linear switch theorem. To prove correctness, pick a conceptual reference block for each ordinary type. Rigid local signs on the edges of that type are \(s_{ij}=a_i b_j\), where \(a_i,b_j\) are the signs of transports to and from the reference. Every matching has sign product \(\prod_i a_i\prod_j b_j\). Every solution of the odd-incidence equations has the same product because each endpoint occurs with odd multiplicity. An actual matching exists under the ordinary guard and yields one solution. This calculation avoids computing the equivalence classes or a matching while constructing the query.

For each of the two requested permutation signs, combine its determinant query with the incidence query for the required complementary value after raw-frame calibration. Disjoin these two tests. Finally take the disjunction with the flexibility test and conjoin \(G\). All lists have polynomial length, and all their Boolean combinations are balanced positive combinations into one ordinary TI instance. This proves the theorem without any complement assumption or adaptive selection of local witnesses. [Linear switches and positive combining](earlier/baseline/baseline/LinearSwitchCompiler.md) · [Query-dependent determinants](earlier/baseline/expansion/LinearAlgebraAndCounting.md)

The same reasoning works for a fixed binary determinant character on a fixed-arity direct sum. Use the parity of the sum of the dimensions of the weighted roles in place of \(d_i\bmod 2\). It applies separately to each character, with conjunction to recover a prescribed fixed-dimensional sign profile.

## 3. An unconditional class with large relative ranks

There is an explicit local test useful in the preceding theorem. On a primitive factor let \(E\) be the canonical coefficient field of its local centroid. It is the stable image of cubing. The stable image is reduced, meets the nilpotent radical in zero, and maps onto the finite residue field because cubing is bijective there. All operators in this field make \(\beta\) \(E\)-bilinear. The centroid and its field are computed at both inputs in polynomial time. Finite fields of the same degree can be aligned using a primitive factor of their tensor product, via the cube-fixed idempotent calculation. Algebraic isomorphisms of the centroid preserve the coefficient field. Thus all local transporters are semilinear for one common Frobenius automorphism \(\sigma\) on the two roles. [Earlier coefficient-field construction](earlier/DescentClosure.md)

If \(r=\dim_E X\) is odd, multiplication on \(X\) by a field element of norm \(-1\) and on \(Z\) by its square is a genuine odd automorphism. The norm is onto and the square action on \(Z\) is even. In this case a single ordinary comparison already suffices.

Suppose now that \(r\) is even. Let \(K\) denote the relation space in the exact sequence of explicitly presented \(E\)-spaces
\[
 0\longrightarrow K\longrightarrow\operatorname{Sym}^2_E X
          \xrightarrow{\ \beta\ } Z\longrightarrow0.
\]
Let \(g=A\sigma\) and \(h=B\sigma\) in calibrated \(E\)-frames and write \(C\sigma\) for the forced map on \(K\). The \(E\)-linear determinants satisfy
\[
 \det A\,\det B=(\det A)^{r+2}(\det C)^{-1}
\]
in compatible exact-sequence frames. This follows from \(\det(\operatorname{Sym}^2 A)=(\det A)^{r+1}\). Different chosen frames contribute a known factor via the two endpoint basis changes. Taking norms kills the even power \(r+2\). The remaining \(F\)-sign is the norm of \(\det C\) times the determinant of \(\sigma\) raised to \(r+\dim_E Z\), and the known frame calibration. If \([E:F]\) is odd, the determinant of every Frobenius power is one, by its action as a cycle in a normal basis. If the degree is even, its sign is the action on the trace-zero line of the intrinsic quadratic subfield.

When \(\dim_E K=O(\log L)\) for coefficient length \(L\), the full \(E\)-exterior algebra of \(K\) has polynomial dimension over \(F\). Include \(E\), its actions, the original bimap, the symmetric square and kernel inclusion, and the exterior chains as an ordinary typed system. On the highest exterior line the semilinear map is \(z\mapsto c\sigma(z)\). Link its Frobenius twists and multiply to obtain a norm line. This operation uses \([E:F]\) line copies and multiplication constraints, and exports the scalar norm on the embedded \(F\)-line. Use the quadratic trace-zero line if needed. Tie the desired product sign to the fixed unit in a marked scalar line. Every actual local witness of that sign lifts. Every extended witness respects the same induced \(C\sigma\) and its forced signs, so it reflects. The construction has one ordinary TI output by polynomial packing into a constant-size typed tensor signature. [Tensor system theorem and prior packing](earlier/baseline/baseline/LinearSwitchCompiler.md)

Consequently a single ordinary TI query decides the entire square-zero comparison whenever **each primitive factor either has odd relative input dimension or has logarithmic relative symmetric relation dimension**. There is no width bound on the two original roles, on the residue-field degree, on the nilpotent radical of the centroid, or on factor multiplicities. For example the free \(E\)-symmetric product map on arbitrarily large even relative dimension has \(K=0\), and arbitrary stacks of such factors, with repeated types, are covered. Such a free product map is indecomposable over \(E\): a nonzero vector from each of two different proposed summands has nonzero symmetric product. For a single \(E\)-free product its centroid is exactly \(E\), since a centroid endomorphism is determined by its action on products and satisfies \((Px)y=x(Py)\), which forces scalar action on two independent vectors. The same conclusion over \(F\) follows first by commutation with the contained \(E\)-centroid action. This class gives a genuine ordinary reduction without supplying local sign oracles.
