# Generic idempotent monodromy of perfect evolution algebras

Informal result concerning Conjecture 2 of Kaygorodov, Martín González and Viruel, *Evolution algebras: A survey of results and a list of open problems*, §2.3. The main conjecture says that the \(2^n-1\) nonzero idempotents of the generic \(n\)-dimensional evolution algebra over \(\mathbb Q\) have Galois group \(S_{2^n-1}\). The paper also proposes the resulting random-permutation fixed-point law for random perfect algebras over finite fields as \(q\to\infty\). The main Galois statement holds, and the proposed distribution holds uniformly as the odd prime powers tend to infinity. At powers of two, the law is exactly the fixed-vector law of \(\mathrm{GL}_n(2)\) at every \(q\). In dimensions \(n\ge3\) this gives a counterexample to the unrestricted finite-field consequence. The direct proof below also gives the geometric monodromy over every characteristic. [Original Conjecture 2](https://arxiv.org/html/2610.22248v1#S2.SS3)

## 1. The finite cover

Write \(M\) for the multiplication matrix of squares in a natural basis. Perfectness is equivalent to invertibility. An idempotent \(x\) satisfies \(x=M x^{[2]}\). Thus writing \(A=M^{-1}\) gives
\[
x_i^2=(Ax)_i,\qquad 1\le i\le n.
\]
Inversion is a bijection on \(\mathrm{GL}_n(\mathbb F_q)\) and a birational change of generic parameters over \(\mathbb Q\). Here random perfect algebras are sampled by uniform invertible structure matrix in a fixed natural basis, the random-matrix convention of the source.

The universal algebra of these equations is free of rank \(2^n\) over the parameter ring, with squarefree monomial basis. Each equation is monic in its leading monomial \(x_i^2\) for a degree order. The leading monomials are pairwise coprime, so the equations form a monic Gröbner basis. Explicitly their \(S\)-polynomial for \(i,j\) has terms \(x_i^2(Ax)_j-x_j^2(Ax)_i\), which reduce to zero after replacing the squares by the linear forms. This argument is valid over the integral coefficient ring. The zero point has invertible Jacobian \(-A\). It is a section in the étale locus of the finite cover of \(\mathrm{GL}_n\), hence open there and closed in the full cover. Removing zero leaves a finite flat cover of degree \(D=2^n-1\). At \(A=I\) every solution is a Boolean vector and has invertible Jacobian, so the open parameter space \(U\) of étale fibers is nonempty over every field. This open is the complement of the trace-pairing discriminant of the finite free algebra. The equations, sections, covers and \(U\) therefore have a common finite-type definition over \(\mathbb Z\).

## 2. The geometric permutation action is two-transitive

Take algebraically closed \(k\) and \(n\ge2\). Any two distinct nonzero roots \(x,y\) at \(A\in\mathrm{GL}_n(k)\) are linearly independent over \(k\). Otherwise \(y=cx\) with \(c\ne0\), and \(c^2x^{[2]}=c x^{[2]}\) forces \(c=1\). In addition \(x^{[2]},y^{[2]}\) are independent, being their images under \(A\).

In \(\mathbb A^{2n}\), take the nonempty open locus where both pairs are independent. Over it the incidence conditions \(Ax=x^{[2]}\) and \(Ay=y^{[2]}\) on all matrices \(A\) have affine fibers of dimension \(n(n-2)\). This is an affine bundle locally: choose a nonzero two-row minor of \([x\ y]\) and solve for the corresponding two coefficients in every row of \(A\). The determinant-open part in each fiber is nonempty because an invertible linear map can extend any isomorphism between two-dimensional subspaces. The total space is irreducible. Restricting to the open \(A\in U\) preserves irreducibility and remains nonempty by \(A=I\), \(x=e_1,y=e_2\). This restriction is the ordered-distinct-pair cover associated to the nonzero idempotent cover. Connectedness of the ordered-distinct-pair cover gives two-transitivity of the geometric monodromy. [Finite étale covers and their permutation actions, Stacks Project](https://stacks.math.columbia.edu/tag/03SF)

## 3. A single transposition in odd characteristic

Work over an algebraically closed \(k\) with \(2\ne0\). Fix the first \(n-1\) equations \(x_i^2=x_i\), and take the last equation
\[
x_n^2=x_n+\sum_{j<n}b_jx_j.
\]
Its matrix \(A\) is triangular with diagonal one. The first \(n-1\) coordinates are indexed by a subset \(I\subseteq\{1,\ldots,n-1\}\). In that branch the last quadratic has discriminant \(1+4\sum_{j\in I}b_j\). At \(b_1=-1/4\), choose \(b_2,\ldots,b_{n-1}\) outside the finitely many hyperplanes on which another subset with an index greater than one has zero discriminant. This is possible over the infinite algebraically closed field. The empty subset has discriminant one. Thus the only zero discriminant is at \(I=\{1\}\).

Now put \(b_1=-1/4+t\) and base-change along \(\operatorname{Spec}k((t))\to U\). At \(I=\{1\}\) the discriminant is \(4t\) and the two roots are exchanged by the nontrivial automorphism of \(k((t))(\sqrt t)/k((t))\). For every other subset the discriminant is a unit with a nonzero square root at \(t=0\). It has a square root in \(k[[t]]\) by Hensel's lemma, so these roots are all fixed by this automorphism. All discriminants are nonzero over \(k((t))\), proving that this parameter lies in \(U\). The Galois action on the pulled-back finite étale cover factors through the geometric monodromy group over \(k\). It furnishes a single transposition there.

A two-transitive group conjugates that transposition to every transposition, and those generate \(S_D\). This proves the full geometric group over algebraically closed fields of characteristic zero and of every odd characteristic. The arithmetic group over \(\mathbb Q(A_{ij})\) contains the geometric group, so is also \(S_D\). Dimension one has one nonzero point and the trivial permutation group.

## 4. Uniform law over odd finite fields

For \(1\le m\le D\), take the cover \(X_m\to U\) of ordered \(m\)-tuples of distinct nonzero roots. The group \(S_D\) acts transitively on every such set. Thus \(X_m\) is geometrically irreducible over every odd finite field and has dimension \(n^2\), the base dimension. These are fibers of fixed finite-type schemes over \(\mathbb Z[1/2]\). Uniform Lang–Weil therefore gives
\[
|X_m(\mathbb F_q)|=q^{n^2}+O_n(q^{n^2-1/2}),\qquad
|U(\mathbb F_q)|=q^{n^2}+O_n(q^{n^2-1/2}).
\]
This use of uniformity may be taken directly from the finite-type-family formulation. [Poonen, *Rational Points on Varieties*, Theorem 7.7.1](https://math.mit.edu/~poonen/papers/Qpoints.pdf)

If \(Z\) is the number of nonzero \(\mathbb F_q\)-rational idempotents, the identity \(\mathbb E (Z)_m=|X_m(\mathbb F_q)|/|U(\mathbb F_q)|\) holds under a uniform parameter in \(U\). Here \((Z)_m=Z(Z-1)\cdots (Z-m+1)\). The complement of \(U\) in \(\mathrm{GL}_n\) has \(O_n(q^{n^2-1})\) points since its discriminant is a nonzero polynomial of bounded degree, nonzero at \(I\). Since \(Z\le D\) for all parameters, the same factorial moments \(1+O_n(q^{-1/2})\) hold for uniform \(A\in\mathrm{GL}_n(\mathbb F_q)\). A uniform random permutation of \(D\) letters has factorial moments exactly one through order \(D\), by counting its fixed ordered \(m\)-tuples. For random variables on \(\{0,\ldots,D\}\), these moments and the zeroth moment determine the distribution by an invertible triangular linear system. Hence the probability of every individual idempotent count equals the random-permutation probability up to \(O_n(q^{-1/2})\), uniformly over odd prime powers. In particular the zero-count probability tends to \(\sum_{j=0}^{D}(-1)^j/j!\).

## 5. Exact characteristic-two law

In characteristic two the equations \(x^{[2]}=Ax\) are additive, with constant invertible Jacobian \(-A\) in the \(x\)-coordinates. The solution group over an algebraic closure is an \(n\)-dimensional vector space over \(\mathbb F_2\), because the étale fiber has exactly \(2^n\) elements. Any \(\mathbb F_2\)-linearly independent tuple of solutions is linearly independent over the ambient field as well. Indeed a shortest nontrivial ambient-linear dependence has one coefficient normalized to one. Squaring it and using \(x^{[2]}=Ax\) and \(A^{-1}\) gives a second dependence with the coefficients squared. Subtracting gives a dependence with fewer terms unless every coefficient equals its own square, contrary to \(\mathbb F_2\)-independence.

A full ordered \(\mathbb F_2\)-basis of the geometric solution space is thus an invertible matrix \(B\) of columns, satisfying \(B^{[2]}=AB\). The frame cover of \(\mathrm{GL}_n\) is itself the irreducible \(\mathrm{GL}_n\) with \(A=B^{[2]}B^{-1}\). It is a finite étale cover as the space of ordered bases in a finite étale \(\mathbb F_2\)-vector-space cover. Each geometric fiber of the frame cover is a torsor for \(\mathrm{GL}_n(2)\), and connectedness gives exactly this geometric monodromy. The arithmetic monodromy over any \(\mathbb F_q\) also equals \(\mathrm{GL}_n(2)\), since it preserves the \(\mathbb F_2\)-linear structure and contains the geometric group.

There is an exact finite-field count that avoids a limiting theorem. Write \(V_A=\{x\in\mathbb F_q^n:x^{[2]}=Ax\}\) and \(r(A)=\dim_{\mathbb F_2}V_A\). For \(m\le n\), its \(\mathbb F_2\)-independent ordered \(m\)-tuples are exactly the \(\mathbb F_q\)-independent ordered \(m\)-tuples of solutions. Each ordered independent tuple \(x_1,\ldots,x_m\) in \(\mathbb F_q^n\) has independent coordinatewise square tuple. The number of \(A\in\mathrm{GL}_n(\mathbb F_q)\) taking the given tuple to that square tuple is the order of its pointwise stabilizer. The group is transitive on independent tuples, so summing this stabilizer count over all tuples gives exactly \(|\mathrm{GL}_n(\mathbb F_q)|\). Thus
\[
\mathbb E_A\prod_{i=0}^{m-1}(2^{r(A)}-2^i)=1.
\]
For uniform \(G\in\mathrm{GL}_n(2)\), the same expectation equals one for \(r'=\dim_{\mathbb F_2}\operatorname{Fix}(G)\), by the same transitive counting of independent tuples over \(\mathbb F_2\). The functions \(\prod_{i<m}(2^r-2^i)\) vanish when \(r<m\) and are positive at \(r=m\). They give an invertible triangular moment system on \(\{0,\ldots,n\}\). Hence \(r(A)\) and \(r'\) have exactly the same distribution and \(Z=2^{r(A)}-1\) has the claimed law for every \(q\) of characteristic two.

For \(n\ge3\) this law cannot put any probability on exactly two nonzero idempotents. In \(S_D\) exactly two fixed points occurs with positive probability, by fixing two letters and cycling the remaining \(D-2\ge5\). The finite-field consequence written for all \(q\to\infty\) thus fails. Restricting to odd characteristic repairs it. For \(n=1,2\) the characteristic-two permutation and symmetric groups agree on the nonzero solution sets.

As a finite control, exact enumeration at \(n=3\) and \(q=2,4\) gives counts by \(r=0,1,2,3\) of \((48,98,21,1)\) and \((51840,105840,22680,1080)\), respectively. The second list is precisely the first multiplied by \(1080\). The calculation enumerates invertible matrices and obtains \(r\) by binary rank of the linearized idempotent equations.

## 6. Prior results and scope

Esterov's characteristic-zero theorem on generic sparse polynomial systems already gives the symmetric group as a general corollary after restricting to nonzero-coordinate solutions. Indeed the supports are \(\{2e_i,e_1,\ldots,e_n\}\), each spans the whole ambient affine space and its differences generate the full lattice, so the support tuple is reduced and irreducible. The leading coefficients can be normalized independently to one. A generic nonzero root has no zero coordinate: the incidence with \(x\ne0\) and one coordinate zero has dimension at most \(n^2-1\), because \(Ax=x^{[2]}\) imposes \(n\) independent row equations for any fixed nonzero \(x\). Thus generic torus roots are exactly the generic nonzero roots considered here. The direct incidence and degeneration arguments additionally work for every odd characteristic. The characteristic-two monodromy, exact law and discrepancy follow by the separate linearized-equation argument. [Esterov, *Galois theory for general systems of polynomial equations*](https://arxiv.org/abs/1801.08260)

The bounded searches found the survey formulation, the existing \(n=2\) case, Esterov's general theorem and related work on natural-basis permutation actions. They found no application giving the two-characteristic result recorded here. This is an informal proof with an explicit attribution for the characteristic-zero case.
