# A single ambient sign on commuting triangular operators

Write \(H\) for the existence of a deterministic polynomial-time many-one reduction from dense determinant-one three-tensor isomorphism over \(\mathbb F_3\) to ordinary three-tensor isomorphism. The reverse reduction is available by unused-line padding. Everything below uses displayed bases over \(\mathbb F_3\) and polynomial size in dense coefficients. [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

## Exact missing lemma

Let \(X,Z\) be framed spaces of even and odd dimensions, respectively. Let \(\beta,\beta':X\times X\to Z\) be symmetric bilinear maps with spanned output and zero common radical. Set \(V=\mathbb F_3\oplus X\oplus Z\), and for either bimap use the explicitly given subspace
\[
 {\cal N}_\beta=\{N_\beta(x,z):x\in X,\ z\in Z\}\subseteq\operatorname{End}(V),\qquad
 N_\beta(x,z)=
 \begin{pmatrix}
 0&0&0\\
 x&0&0\\
 z&\beta(x,-)&0
 \end{pmatrix}.
\]
Suppose the two subspaces are conjugate by an invertible operator on \(V\).

**Missing lemma.** There is one deterministic polynomial-time map, on this ordinary-conjugate promise, which outputs an ordinary \(\mathbb F_3\) tensor-isomorphism pair that is YES exactly when some conjugator \(g\) of the displayed operator spaces has \(\det g=1\).

This is a single ambient sign in a class of commuting operator spaces, with all triple products zero. No change of ground field, factorization, unknown group representation, or recovery of a particular generator correspondence is part of the input. The lemma is also equivalent to orientation removal for the compact elementary abelian subgroups \(1+{\cal N}_\beta\) of the same ambient general linear group. Their groups are given by polynomially many explicit matrices, and their representation on \(V\) is part of the problem. The claim concerns ordinary-conjugate pairs with the displayed algebraic form. A supplied conjugator would be additional input.

## Why this would settle the original problem

Set \(A_\beta=\mathbb F_3 1\oplus X\oplus Z\), with \(xy=\beta(x,y)\) for \(x,y\in X\) and all radical products involving \(Z\) zero. It is an associative commutative local algebra. Its radical \(J=X\oplus Z\) satisfies \(J^2=Z\), \(J^3=0\) and \(\operatorname{Ann}_J(J)=Z\). In the displayed frames, left multiplication by \(x+z\) is \(N_\beta(x,z)\). Left multiplication faithfully identifies \(A_\beta\) with \(\mathbb F_3 I+{\cal N}_\beta\).

**Exact comparison.** If \(g{\cal N}_\beta g^{-1}={\cal N}_{\beta'}\), conjugation by \(g\) induces a unique unital algebra isomorphism \(\phi:A_\beta\to A_{\beta'}\). Conversely \(\phi\) itself conjugates the left regular multiplications. More precisely every conjugator is of the form
\[
 g(a)=\phi(a)u,\qquad u=g(1)\in A_{\beta'}^\times .
\]
Indeed conjugating the left multiplication by \(a\) and evaluating at \(1\) gives the formula. Since \(g,\phi\) are invertible, multiplication by \(u\) is invertible and \(u\) is a unit. For any unit \(u=s+j\), with \(s\in\mathbb F_3^\times\) and \(j\in J\), its regular multiplication has determinant \(s^{\dim A}\) since multiplication by \(j\) is nilpotent. Here \(\dim A=1+\dim X+\dim Z\) is even, so that determinant is one. Therefore the sets of attainable signs of algebra isomorphisms and ambient conjugators are identical.

**Compact subgroups.** The set \(1+{\cal N}_\beta\) is a group since \({\cal N}_\beta\) is an associative nilpotent algebra. In characteristic three every element cubes to the identity, and they commute. The maps
\[
  \exp N=I+N+\tfrac12 N^2,\qquad
  \log(I+N)=N-\tfrac12 N^2
\]
are inverse and are equivariant under conjugation. They identify addition in \({\cal N}_\beta\) with multiplication in \(1+{\cal N}_\beta\) because all triple products vanish. The exponentials of a displayed basis are compact generators and the logarithms of those generators recover the subspace by ordinary linear span. Conjugation of the spaces is equivalent to conjugation of the compact matrix groups in both sign conventions.

**Ordinary guard.** On all well-formed pairs in this class, ordinary conjugacy reduces to ordinary TI by the multiplication tensors of \(A_\beta,A_{\beta'}\). A multiplication isotopy is equivalent to a unital algebra isomorphism by normalization at the two units. Hence if the promise lemma were available, apply its map on the pair, conjoin with the ordinary guard, and use the ordinary TI conjunction compiler. Off the promise the guard is false, so correctness of the promise map there is unnecessary. A reduction algorithm for the promise is taken to be polynomially clocked on all inputs. This yields the total oriented comparison for these algebras. [Earlier ordinary conjunction](baseline/baseline/LinearSwitchCompiler.md)

**Recovering all three determinants.** The earlier weighted cube-zero compiler takes an arbitrary ternary tensor pair, and for each nonzero character of its three sign coordinates gives a pair \(A_\beta,A_{\beta'}\) in exactly the class above. Its possible total algebra determinants are exactly the attainable values of that character on tensor transporters. The hypotheses on \(X,Z,\beta\) and both dimension parities are part of that construction. It is uniform and deterministic. If the original carrier has a nonempty transporter, its determinant patterns form a coset \(dS\) of a subgroup of \(D=\{\pm1\}^3\). The identity is in \(dS\) exactly when each character admits value \(+1\) somewhere on \(dS\). In fact, if \(d\notin S\), choose a character trivial on \(S\) and equal to \(-1\) on \(d\). If the transporter is empty, every character test fails. Thus seven weighted comparisons, followed by ordinary conjunction, prove \(H\) from the missing lemma. [Earlier weighted exact compiler](baseline/baseline/earlier/CubeZeroAndExtensions.md)

**Converse.** Given \(H\), signed conjugacy in this class reduces to signed TI by the multiplication tensors of \(A_\beta,A_{\beta'}\). In the normalized isotopy formula the three maps are obtained from an algebra isomorphism by multiplication by units. Those unit determinants are all one in even dimension, so a signed multiplication isotopy exists exactly when the algebra isomorphism can have determinant one. Now apply \(H\). Consequently the displayed promise lemma is equivalent to \(H\). Ordinary comparison of these operator spaces also has the ordinary TI degree without assuming \(H\), using the zero-character version of the earlier compiler in the other direction.

## A sharp failure of small corresponding tuples

The exact lemma cannot be replaced by testing whether **each small corresponding tuple of group elements** admits an even simultaneous conjugator. There are pairs in the displayed class with a fixed explicit odd ordinary conjugator \(r\), for which the minimum tuple length that can expose the orientation failure is exactly \(\dim X\).

Take \(n=\dim X\equiv2\bmod4\), \(Z=\operatorname{Sym}^2 X\), and \(\beta(x,y)=xy\) the usual symmetric product. The resulting ring is the free commutative local algebra on \(X\) truncated at degree three. The symmetric product has spanned output and zero common radical. Its radical-square dimension is \(n(n+1)/2\), which is odd. An automorphism of the algebra induces \(P\in\operatorname{GL}(X)\) on \(J/J^2\) and \(\operatorname{Sym}^2 P\) on \(J^2\). The unipotent shears contribute determinant one. Triangularizing \(P\) over an algebraic closure shows that \(\det(\operatorname{Sym}^2 P)=(\det P)^{n+1}\). The total determinant is \((\det P)^{n+2}=1\). The exact comparison above makes every operator-space normalizer even. If \(r\) negates the scalar line and fixes \(X,Z\), then \(r{\cal N}_\beta r^{-1}={\cal N}_{-\beta}\). This gives an ordinary YES and a signed NO with a known reference conjugator.

Let \(1\le k<n\), and take any \(N_i=N_\beta(x_i,z_i)\) for \(i=1,\ldots,k\). Put \(U=\operatorname{span}(x_1,\ldots,x_k)\), \(a=\dim U\), and \(W=\sum_i\operatorname{im}N_i\). The subspace \(U X\subseteq\operatorname{Sym}^2 X\) spanned by products with one factor in \(U\) is contained in \(W\cap Z\). Modulo \(U X\), the only generators of \(W\) are the \(k\) vectors \(x_i+z_i\). A combination of these lies in \(Z\) only if its \(x_i\) components cancel, leaving at most \(k-a\) additional dimensions. Therefore
\[
 \dim Z/(W\cap Z)\ \ge\ \tfrac12(n-a)(n-a+1)-(k-a)>0.
\]
For the strict inequality use \(k-a\le n-a-1\). Choose a line \(\ell\subset Z\) outside \(W\) and a complementary hyperplane containing \(W\). Negating \(\ell\) and fixing the hyperplane is an odd map \(s\) commuting with every \(N_i\): each \(N_i\) has image in the hyperplane and kills \(\ell\). The even map \(rs\) therefore sends all \(N_i\) to \(rN_i r^{-1}\). The same proof works for their exponentials, or for arbitrary chosen group elements by taking logarithms.

For \(k=n\), choose \(x_i\) to be a basis and all \(z_i=0\). The resulting \(N_i\), together with the identity, generate the entire regular algebra, since their products span \(Z\). A map centralizing this tuple is regular multiplication by a unit, and all such maps are even. The corresponding tuple in \({\cal N}_{-\beta}\) admits no even conjugator. Again this holds at group level because the logarithms are polynomials in the given group elements.

Thus even agreement on **every** corresponding tuple of size at most \(n-1\) does not imply even conjugacy of the full spaces, even with a reference ordinary map and with strictly triangular commuting generators. The bound is sharp on this explicit family. It is an obstruction to that local-to-global implication. A general reduction can use coefficients and can impose other coupled conditions.

## What linear switches can assemble

Once individual ordinary tests for the seven character conditions are available, ordinary TI positive closure finishes the problem. The arbitrary-rank linear switch theorem additionally aggregates sign tests that are already available by ordinary TI. Neither step decides whether a particular sign is available on a single ordinary-conjugate pair of the spaces above. The free family exhibits the failure of supplying that bit by local tuples. The exact missing lemma asks only for the bit on the stated normal form and is enough for the global conclusion.

The main equivalence and sharp tuple theorem are written proofs. Separate Lean checks are for the truncated exponential/logarithm identities only.
