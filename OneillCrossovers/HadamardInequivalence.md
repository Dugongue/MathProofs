# Two inequivalent Hadamard matrices of order 4792

**Theorem.** The order-4792 Hadamard matrices from cases 268 and 523 of O’Neill, Kirkby and Astra’s search are inequivalent under signed row and column permutations, even if transposition is allowed. Neither is equivalent to a Kronecker product of two Hadamard matrices of smaller orders greater than one. Their two-frame tensors give nonisomorphic tensors under real orthogonal and complex unitary isomorphism, with identical three flattening Gram matrices.

The constructions are the authors’ work. Section 5 of their manuscript leaves their equivalence untested. The separation below uses a finite exact check and a proof that the resulting invariant survives all the equivalence operations. [Order-4792 manuscript](https://charlesponeill.com/maths-releases/hadamard-4792/hadamard-4792.pdf)

## Two intrinsic borders

A **closed row quadruple** is a set of four distinct rows whose entrywise product is constant. Permutations preserve this condition. Changing the sign of a row changes the product by a constant, and changing the sign of a column contributes four signs at that column. The corresponding column condition is also invariant.

The checker below establishes that each matrix has exactly one closed row quadruple and one closed column quadruple. In both cases these are the displayed four border rows and four border columns. Any signed equivalence must therefore preserve the two borders, or interchange their roles if it includes a transpose.

Partition the bulk rows by their sign pattern on the border columns, taken modulo an overall sign. Partition the bulk columns by their sign pattern on the border rows in the same way. The displayed bordered Goethals–Seidel construction has four classes of size 1197 on each axis. Their patterns are the four rows or columns of the order-four sign matrix \(S\). Distinct rows or columns of \(S\) are orthogonal, so none are equal up to sign. Within each particular class the restrictions are literally equal before taking signs.

Any signed equivalence must carry those partitions to the corresponding partitions. Its row signs are constant within a row class. Indeed two rows of the source class agree at every border column, and their two image rows agree at the corresponding border column, where the column sign affects them both equally. The column signs are constant within each column class by the same argument. Consequently each of the 16 bulk blocks is transferred to a corresponding block by row and column permutations and one overall sign, allowing a transpose if the equivalence does so.

## The separating invariant

For the bulk rectangle \(C\) from any row class and column class, compare the inner products of distinct rows of \(C\). Row and column permutations and an overall sign preserve the multiset of these inner products. A transposition exchanges the row and column versions of the invariant.

Each bulk block, up to its overall sign and reversible index permutations, has the form \(C_{g,h}=s(h-g)\) for one of the four sign strings \(s\) on the group \(G=\mathbb Z_7\times\mathbb Z_{19}\times\mathbb F_3^2\). Row and column correlations of this block run over exactly the same values of

\[
P_s(t)=\sum_{g\in G}s(g)s(g+t),\qquad 0\ne t\in G.
\]

In particular the **largest** inner product of distinct rows occurring in any bulk block is also the largest such inner product for columns.

| Case | Closed row quadruples | Closed column quadruples | Largest bulk inner product |
| --- | ---: | ---: | ---: |
| 268 | 1 | 1 | 157 |
| 523 | 1 | 1 | 125 |

The two different maxima prove inequivalence with or without transposition.

If a Hadamard matrix factors as \(A\otimes B\) with both factors of order greater than one, any two distinct row indices \(i,i'\) of \(A\) and two distinct row indices \(j,j'\) of \(B\) yield a closed row quadruple. It is the set \(\{(i,j),(i',j),(i,j'),(i',j')\}\). Each factor of any entry of their product occurs twice, so that product is identically one. For factor orders \(u,v>1\) with \(uv=4792\), this gives at least \(\binom u2\binom v2>1\) different closed row quadruples. The verified unique quadruple excludes such factorizations, including equivalence to a Sylvester doubling of an order-2396 matrix.

## Exact verification

Take the two local JSON certificates linked below and run the checker. It requires only Python 3’s standard library. Its mathematical input is the explicit bordered array formula of Theorem 3 in the manuscript. The checker independently verifies the required autocorrelation identity for both certificates and checks the SHA-256 digest of each reconstructed sign matrix. [Case 268 certificate](https://github.com/charlieoneill11/maths-releases/blob/main/hadamard-4792/code/certificate.json), [Case 523 certificate](https://github.com/charlieoneill11/maths-releases/blob/main/hadamard-4792/code/certificate-case523.json)

    python check_hadamards.py certificate.json certificate-case523.json

For each axis encode a row as a binary sign string and add its first bit to every bit. This chooses a representative modulo overall sign. A closed quadruple is equivalent to a collision between the XORs of two disjoint row pairs. The checker enumerates all \(\binom{4792}{2}=11{,}479{,}236\) pairs. It first compares the XORs in the 64 coordinates \(7+1879i\bmod 4792\) for \(0\le i<64\). Every full collision must survive this coordinate restriction, so comparing the full strings only within repeated buckets is exact. In both axes of both matrices the only full collisions are the three pairings of indices \(0,1,2,3\). The numbers of repeated projected keys are \((45,21)\) for the rows and columns of case 268 and \((9,6)\) for case 523.

For the inner products let \(D=\{g:s(g)=-1\}\) and let \(\lambda(t)\) count ordered pairs \((u,v)\in D^2\) with \(v-u=t\). Then \(P_s(t)=1197-4|D|+4\lambda(t)\). The checker enumerates the differences as integers. It also verifies that the four autocorrelations sum to \(-4\) at each nonzero shift, as required by the published construction.

## Transfer to definite tensor isomorphism

For an order-\(n\) real sign Hadamard matrix \(H\) with rows \(h_i\), let \(e_i,f_i\) be the standard bases of two orthogonal \(n\)-dimensional blocks in each of the first two modes. Let \(g_j\) be the standard basis of the third mode. Set

\[
T_H=\sum_{i=1}^n e_i\otimes e_i\otimes h_i+
     \sum_{j=1}^n f_j\otimes f_j\otimes g_j
\quad\in\quad\mathbb R^{2n}\otimes\mathbb R^{2n}\otimes\mathbb R^n.
\]

For \(n>1\), the first and second flattening Gram matrices each equal \(\operatorname{diag}(nI_n,I_n)\). The third equals \((n+1)I_n\). These assertions follow by contracting the displayed summands and using \(H^\mathsf{T}H=nI_n\). A real orthogonal or complex unitary isomorphism must preserve the two distinct eigenspaces in both of the first two modes.

In either diagonal block the slice space along the third mode is the full space of diagonal matrices. On the \(e\)-block this follows because the \(h_i\) form a basis. On the \(f\)-block the \(g_j\) form the standard basis. If \(A,B\) send such a slice space to itself by \(M\mapsto AMB^\mathsf T\), then \(AE_{ii}B^\mathsf T\) is a rank-one diagonal matrix for each \(i\). Its two factors are scalar multiples of the same standard vector. Thus \(A,B\) are monomial with the same permutation on that block. The \(f\)-block now forces the third actor to be monomial in the standard basis. The \(e\)-block forces it to carry the Hadamard row bases to each other up to a monomial change. Conversely a signed row and column equivalence produces an isomorphism of the tensors.

In the real orthogonal case the nonzero monomial entries have signs. In the complex unitary case there can be phases \(r_i,c_j\), but every product \(r_i c_j\) must be a sign because all entries of \(H\) and the target Hadamard are signs. Then each \(r_i/r_1\) and \(r_1 c_j\) is a sign, giving a signed equivalence in this case as well. Therefore the two verified Hadamards give inequivalent tensors under both groups in format \(9584\times9584\times4792\), despite all three flattening Gram matrices agreeing.
