# Multilinear monomial substitutions that lift sparsity to ROABP width

Hu and van Melkebeek ask in Section 5 whether sparsity can be lifted to read-once oblivious algebraic branching program (ROABP) width by a more efficient gadget using multilinear codeword monomials. The construction below answers this affirmatively. It uses \(O(n)\) output variables and increases degree by a factor \(O(n)\), independent of the original degree. The source paper achieves exact lifting with \(2n\) variables and a degree factor \(O(n(n+d))\) for degree \(d\). [Hu and van Melkebeek, Lifting Polynomial Complexity Measures Using Error-Correcting Codes, Sections 2 and 5](https://eccc.weizmann.ac.il/report/2026/125/download/)

## Theorem

For each positive integer \(n\), a deterministic algorithm running in time polynomial in \(n\) constructs an \(N\times n\) binary matrix \(A\) with \(N=O(n)\). Write \(\Phi\) for the substitution
\[
\Phi(x_i)=\prod_{j=1}^N y_j^{A_{ji}}.
\]
Over every field \(F\), every nonzero \(f\in F[x_1,\ldots,x_n]\), and every order \(\pi\) of the \(y\)-variables, one has
\[
\operatorname{width}_{\pi}(\Phi(f))=\operatorname{sparsity}(f).
\]
The output polynomial has the same sparsity as \(f\) and degree at most \(N\deg f\). Here width means the minimum width among ROABPs of the specified order computing the formal polynomial, and sparsity is the number of nonzero monomials. Each substitution monomial \(\Phi(x_i)\) is multilinear. The map depends only on \(n\).

## A binary matrix with a spanning cut in every order

A binary linear code is intersecting if every pair of nonzero codewords has overlapping supports. Let \(B\) be a generator matrix in the column-vector convention for a binary intersecting code of dimension \(n\). For any two proper linear hyperplanes of \(\mathbb F_2^n\) with nonzero normals \(u,v\), a row \(r\) of \(B\) has \(r\cdot u=r\cdot v=1\), including when \(u=v\). Thus some row is outside their union. This is an application of the classical intersecting-code property. [Cohen and Lempel, Linear intersecting codes](https://www.sciencedirect.com/science/article/pii/0012365X85901906)

Form \(A\) by giving each row of \(B\) two occurrences, with distinct output variables for the two occurrences. There are at least two row occurrences outside the union of any two proper hyperplanes. The same property holds after appending arbitrary rows to \(A\).

Order the rows of \(A\) according to \(\pi\). The full row set spans \(\mathbb F_2^n\), so it has a first full-rank prefix. The rows before its last row lie in a proper hyperplane. If the rows after that last row failed to span, they would lie in a second proper hyperplane, and all rows except that one occurrence would belong to the union of the two hyperplanes. Hence both the first full-rank prefix and its complementary suffix have column rank \(n\).

Each of these two row submatrices has an \(n\times n\) minor with determinant \(1\) modulo \(2\). Its determinant as an integer is odd and nonzero. Hence both submatrices have column rank \(n\) over \(\mathbb Q\), and each associated map on integer exponents is injective. The construction works for coefficient fields of arbitrary characteristic because monomial exponents and their differences are integers.

## An explicit intersecting code of linear length

Set \(b=\lceil\log_2(2n)\rceil\), \(q=2^b\) and \(k=\lceil n/b\rceil\). Construct \(\mathbb F_q\) and fix an \(\mathbb F_2\)-basis of it. One may find an irreducible binary polynomial of degree \(b\) by enumerating all monic candidates and testing trial divisibility by the monic polynomials of degrees \(1\) through \(\lfloor b/2\rfloor\). This takes polynomial time in \(n\) since \(q<4n\).

Pad input vectors with zero bits and pack them as the \(k\) coefficients of a polynomial \(p\) of degree less than \(k\) over \(\mathbb F_q\). Evaluate \(p\) at \(2k-1\) distinct field elements, which exist because \(2k-1<q\). A nonzero input gives a nonzero \(p\). For any two nonzero inputs, the union of the zero positions of their evaluated polynomials has size at most \(2k-2\). Thus some output location has nonzero symbols in both words.

Encode each field symbol with a binary linear inner map constructed as follows. Start with all ordered pairs \((u,v)\) of nonzero vectors of \(\mathbb F_2^b\), allowing \(u=v\). For distinct \(u,v\), exactly a quarter of the rows \(r\) of \(\mathbb F_2^b\) satisfy \(r\cdot u=r\cdot v=1\), since the two linear functionals are independent. For equal vectors the fraction is one half. Hence some row covers at least a quarter of the currently uncovered pairs. Choose such a row deterministically by exhaustive scanning and remove the pairs it covers. After \(O(b)\) rows the number of uncovered pairs is less than one, since it starts below \(2^{2b}\) and decreases by a factor at most \(3/4\) in each iteration. Each scan uses at most \(q\) rows and \(q^2\) pairs.

Concatenating the outer and inner maps gives a binary linear map. Given two nonzero inputs, choose a common nonzero outer position and then a common nonzero inner position there. The map is injective by applying the property to equal inputs. Its binary length is \(O(kb)=O(n+b)=O(n)\). Apply it to the \(n\) input basis vectors to obtain the columns of \(B\). Duplicating the rows yields the required \(A\), still in deterministic polynomial time.

For a simpler quadratic-length construction, take the rows \(e_i\) and \(e_i+e_j\) for \(i<j\) before doubling. If two nonzero normals have a coordinate with both entries \(1\), the corresponding \(e_i\) evaluates to \(1\) against both. Otherwise their nonempty supports are disjoint, so choosing one coordinate from each gives an \(e_i+e_j\) that evaluates to \(1\) against both.

## Exact width

Let \(S\subseteq\mathbb N^n\) be the exponent support of \(f\) and \(c_a\) the coefficient at \(a\in S\). The exponents of the substituted monomial are \(Aa\). They are all distinct because \(A\) has full column rank over \(\mathbb Q\). At the cut proved above, the rows \(U\) of the prefix and the rows \(V\) of the suffix give injective maps \(a\mapsto A_Ua\) and \(a\mapsto A_Va\). In the coefficient matrix for this cut, the entries \(c_a\) consequently occupy distinct rows and distinct columns. Restricting to these rows and columns and permuting them yields a diagonal matrix with nonzero diagonal \(c_a\), so the rank is \(|S|\) over \(F\).

A width-\(w\) ROABP in the given order would express the polynomial as a sum of at most \(w\) products of a prefix polynomial and a suffix polynomial, one summand per vertex at the cut. Each product contributes a matrix of rank at most one. Thus the width is at least \(|S|\). The \(|S|\) scalar monomial paths give an upper bound of \(|S|\) in any order. That proves the exact identity.

A homogeneous substitution of the same degree bound is also available. Append the \(0/1\) complement of each row of \(A\) as a distinct new output variable. Every column of the new matrix has weight exactly \(N\), so \(\Phi\) takes a homogeneous degree-\(d\) polynomial to a homogeneous degree-\(Nd\) polynomial. The spanning-cut proof survives the additional rows.

## Exact transfer for irreducible factors

There is a linear-length multilinear version that also preserves each irreducible factor after removing a common output monomial. Append \(n\) fresh coordinate rows to register \(x_i\) as a distinct variable \(z_i\), so the new substitution has
\[
\Psi(x_i)=z_i\prod_{j=1}^{N}y_j^{A_{ji}}.
\]
It has the same exact width property since the doubled rows of \(A\) remain present.

Let \(g\) be a nonconstant irreducible polynomial in \(F[x]\). In the Laurent polynomial ring \(F[z,y_1^{\pm1},\ldots,y_N^{\pm1}]\), the polynomial \(g(z)\) is prime because its quotient ring is a Laurent polynomial ring over the domain \(F[z]/(g)\). The automorphism \(z_i\mapsto z_i\prod_j y_j^{A_{ji}}\) fixing the \(y_j\) shows that \(\Psi(g)\) is prime in that ring. Remove the largest common \(y\)-monomial \(y^\alpha\) from \(\Psi(g)\), getting \(h=y^{-\alpha}\Psi(g)\) in \(F[z,y]\). If \(h\) factored there, one factor would be a Laurent unit. Any such factor belonging to \(F[z,y]\) is a nonzero constant times a nonnegative \(y\)-monomial. No \(y_j\) divides \(h\), so this factor would be constant. Hence \(h\) is irreducible. If \(g\mid f\), then \(h\mid\Psi(f)\) in the polynomial ring because \(\Psi(f)=y^\alpha h\Psi(f/g)\).

Removing a common monomial translates the row and column indices of every supported coefficient-matrix entry by fixed exponent vectors and leaves ranks unchanged. Equivalently, both injective exponent projections at the spanning cut remain injective after translation, and the monomial-path upper bound remains the same. It follows that the irreducible factor \(h\) has exact ROABP width \(\operatorname{sparsity}(g)\) in every order, while the full polynomial \(\Psi(f)\) has exact width \(\operatorname{sparsity}(f)\).

## Optimal asymptotic order for degree-independent monomial substitutions

Consider any fixed monomial substitution on \(n\) inputs, with exponent matrix \(M\in\mathbb N^{m\times n}\). A cut is deficient if one of its projected matrices has rational rank \(r<n\). For
\[
f_D=\prod_{i=1}^{n}(1+x_i+\cdots+x_i^D),
\]
a deficient projection gives at most \(O_M((D+1)^r)\) distinct row or column indices. Indeed, choose \(r\) independent coordinate rows for that projection. Their values determine all others, and each is an integer between \(0\) and \(D\) times its row sum. This bounds the rank of the cut coefficient matrix by \(O_M((D+1)^{n-1})\), including when additional monomial collisions cancel terms. If all cuts of an order are deficient, the coefficient-matrix width characterization bounds the width in that order by \(O_M((D+1)^{n-1})\). The original sparsity is \((D+1)^n\). [Hu and van Melkebeek, Lemma 6](https://eccc.weizmann.ac.il/report/2026/125/download/)

If \(m<2n\), every cut is deficient in every order because at least one half has fewer than \(n\) rows. If any matrix column is supported on at most \(n\) rows, order the rows with zero in that column first. Cuts before the first row using the column have a deficient prefix, and cuts after that row have fewer than \(n\) suffix rows. These two scenarios each violate any uniform positive-factor lift of sparsity as \(D\) grows. Thus a degree-independent monomial gadget giving such a lift in every order requires \(m\ge 2n\), and each image \(\Phi(x_i)\) must involve at least \(n+1\) distinct variables. The linear variable count and linear worst-case degree factor in the theorem have optimal asymptotic order for this class.

## Attribution and scope

The preceding work introduced the exponent-code viewpoint and proved the original exact lifting theorem. The step above replaces the need for both halves of a fixed middle cut to decode with a spanning prefix and suffix whose cut may depend on the order. The binary intersecting-code property guarantees such a cut after doubling the rows. The two components of the concatenated construction, the coefficient-matrix characterization, and intersecting codes are established tools. The conclusion proved here is the multilinear-gadget question in Section 5 and the stated extensions. [Hu and van Melkebeek, APPROX/RANDOM 2026](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX/RANDOM.2026.64) [Cohen and Lempel, Linear intersecting codes](https://www.sciencedirect.com/science/article/pii/0012365X85901906)
