# Bilinear Diophantine Undecidability and Simultaneous Failure of Diophantine Approximation

The first theorem proves Fedor Manin's Conjecture 7.2 in its full integral formulation. It uses Koymans–Pagano's theorem for finitely generated commutative rings. The second theorem assumes Glazer's claimed Diophantine definition of the integers in the rationals. It gives one smooth projective counterexample to the rational case of Pasten's Conjecture 5.24 at every place at once.

## 1. Manin's bilinear conjecture

**Theorem.** Fix any nonzero bilinear map \(B\colon \mathbb Z^m\times\mathbb Z^n\to\mathbb Z^p\). There is no algorithm deciding whether an input system
\[
 \sum_{i,j=1}^r a_{ij}^{(q)}B(u_i,v_j)=c_q,\qquad 1\le q\le s,
\]
with integer scalar coefficients and integer vector right sides has a solution in integer vectors. The map \(B\) is fixed throughout the reduction. This is exactly [Conjecture 7.2 in Manin, *Rational homotopy type and computability*](https://arxiv.org/html/2007.10632#S7).

### Normalize a frame using bilinear equations alone

Quotient the two input lattices by their left and right radicals. Each radical is the kernel of a map into a free abelian group, so it is saturated and the quotient is free abelian. Write \(U,V\) for the quotients and \(\beta:U\times V\to W=\mathbb Z^p\) for the descended map. It has zero radicals on both sides. Any system written with \(\beta\) lifts to a system of precisely the same form with \(B\): every solution upstairs projects and every solution downstairs lifts by choosing integral representatives independently. Both quotient lattices have positive rank.

Fix bases \((e_i)\) and \((f_j)\) of \(U,V\). Introduce unknown frame vectors \((a_i),(b_j)\) and require
\[
 \beta(a_i,b_j)=\beta(e_i,f_j)\quad\text{for all }i,j.
\]
Write \(Ae_i=a_i\) and \(Df_j=b_j\). These equations imply \(\beta(Au,Dv)=\beta(u,v)\). The zero radicals imply that \(A,D\) are injective over \(\mathbb Q\), hence rationally invertible.

In fact both are unimodular. The injection
\[
 \Phi:U_{\mathbb Q}\to\operatorname{Hom}_{\mathbb Q}(V_{\mathbb Q},W_{\mathbb Q}),\qquad
 \Phi(u)(v)=\beta(u,v)
\]
has a rational linear left inverse \(L\). Fix a positive integer \(N\) such that \(NL\) sends integer matrices to integral vectors. The identity \(\Phi(A^{-k}u)=\Phi(u)\circ D^k\) holds for all \(k\ge1\), since \(\beta(A^k x,D^k v)=\beta(x,v)\). Thus \(N A^{-k}\) is integral for all \(k\). The positive integer \(N^{\operatorname{rk}U}/|\det A|^k\) would tend to zero if \(|\det A|>1\), so \(|\det A|=1\). Swapping the arguments proves \(|\det D|=1\).

Applying \(A^{-1}\) and \(D^{-1}\) to every left and right unknown preserves every equation, because the inverses together preserve \(\beta\). We can therefore require any fixed integral input vector within a pairing by using its fixed linear combination of frame vectors. Conversely, setting the frames to the chosen bases is always permitted. After expansion by bilinearity, every such constraint has the required coefficient-only form.

### Encode a commutative ring in the same equation language

Form the integral adjoint ring
\[
 \mathcal A=\{(L,R)\in\operatorname{End}_{\mathbb Z}(U)\times
                 \operatorname{End}_{\mathbb Z}(V)^{\mathrm{op}}:
                 \beta(Lu,v)=\beta(u,Rv)\text{ for all }u,v\}.
\]
The product is \((L,R)(L',R')=(LL',R'R)\), since the adjoint identities can be applied in succession. Both coordinate projections are injective by the zero-radical property. The defining equations are integral linear equations on matrix entries, so an additive basis of \(\mathcal A\) is computable by integer linear algebra. Its center \(C=Z(\mathcal A)\) is likewise computable by linear commutation equations against that basis. It is a commutative unital ring free of finite rank as an abelian group, hence a finitely generated \(\mathbb Z\)-algebra. The identity has infinite additive order because \(U\) has positive rank. Thus Hilbert's tenth problem over \(C\) is undecidable by [Koymans–Pagano, Theorem 1.1](https://arxiv.org/html/2412.01768v3#S1.SS2). The paper also credits Alpöge, Bhargava, Ho, and Shnidman with independently recovering this theorem.

For a ring variable \(X\), introduce left variables \(x_i^X\) and right variables \(y_j^X\) for the columns of \(L_X\) and \(R_X\). In the normalized frame the equations
\[
 \beta(x_i^X,f_j)=\beta(e_i,y_j^X)
\]
are exactly adjoint membership. For each fixed additive basis element \(E=(L_E,R_E)\) of \(\mathcal A\), also impose
\[
 \beta(x_i^X,R_E f_j)=\beta(L_E e_i,y_j^X)\quad\text{for all }i,j.
\]
The two sides are \(\beta(L_E L_Xe_i,f_j)\) and \(\beta(L_X L_Ee_i,f_j)\). The zero left radical and injective left projection show these constraints are equivalent to commutation with \(E\), hence with all of \(\mathcal A\) as \(E\) varies. Every fixed column here is an integral combination of the frame variables.

Represent a polynomial system over \(C\) by addition, multiplication and constant gates with final outputs constrained to zero. For each gate, the following constraints hold for every \(i,j\).

| Gate | Constraint |
| --- | --- |
| \(X+Y=Z\) | \(\beta(x_i^X+x_i^Y-x_i^Z,f_j)=0\) |
| \(XY=Z\) | \(\beta(x_i^Y,y_j^X)=\beta(x_i^Z,f_j)\) |
| \(X=K\), \(K\) fixed | \(\beta(x_i^X,f_j)=\beta(L_K e_i,f_j)\), with the right side a fixed output vector |

For the multiplication gate the left side equals \(\beta(L_X L_Y e_i,f_j)\) by adjoint membership. All gates enforce equality of the indicated left matrices, which is equality of adjoint pairs by injectivity. Each equation expands into the required sum of pairings. Pad either list with unused variables if the two lists differ in length.

A ring solution gives a bilinear solution by taking its columns and the standard frames. Conversely, normalize the frames of any bilinear solution and read its columns as center elements. The gate equalities then give a solution of the original ring system. This is an effective many-one reduction for every fixed nonzero \(B\), proving the theorem.

**Topological consequence.** For every fixed simply connected finite complex \(Y\) which is not a rational H-space, deciding whether a given map \(A\to Y\) extends to \(X\) is undecidable. This holds already for finite simplicial pairs \((X,A)\) of relative cohomological dimension \(d+1\), where \(d\) is the first Postnikov degree in which \(Y_d\) fails to be a rational H-space. Apply [Manin's Theorem 8.1](https://arxiv.org/html/2007.10632#S8) to the bilinear theorem above. For fixed simply connected finite targets which are rational H-spaces, Manin's Theorem A gives decidability. For input pairs of cohomological dimension less than 3, one may pad the pair with a disjoint sphere of dimension 3 and a marked point mapped constantly, which does not change the extension answer.

**Relation to prior work.** Manin uses frame normalization for scalar-valued maps in §7, equation (7.15). [Garreta, Miasnikov, and Ovchinnikov](https://arxiv.org/abs/1805.02573) use scalar-ring interpretations for bilinear maps. The argument above gives explicit equations in Manin's exact input format, with no named input vectors and with arbitrary nonzero output rank. A targeted search did not locate a prior proof of the full conjecture in this format. Publication priority is unverified.

## 2. One counterexample to Pasten's conjecture at every rational place

**Theorem conditional on Glazer's integrality result.** Assume \(\mathbb Z\) is Diophantine in \(\mathbb Q\). There are a smooth projective geometrically integral \(\mathbb Q\)-variety \(X\) with \(X(\mathbb Q)\) Zariski dense and a dominant morphism \(f:X\to\mathbb P^1\) such that, for every place \(v\) of \(\mathbb Q\), \(f(X(\mathbb Q))\) has exactly one accumulation point in \(\mathbb P^1(\mathbb Q_v)\), and it is transcendental over \(\mathbb Q\).

This refutes the rational-field case of [Pasten's Conjecture 5.24](https://arxiv.org/pdf/2012.14054#page=27) with the same \(X,f\) and \(U=X\) for all places. Pasten's Proposition 5.30 already proves that Diophantine definability of the integers refutes the conjecture place by place. The simultaneous smooth projective construction below is the additional conclusion. We take [Glazer's claimed definition](https://github.com/elliotglazer/diophantine-z-q) as a premise.

### One computable rational sequence with transcendental limits at all places

Set \(\alpha_\infty=\sum_{k\ge1}10^{-k!}\) and \(\alpha_p=\sum_{k\ge1}p^{k!}\) for each prime \(p\), the second sum taken in \(\mathbb Z_p\). The real sum is transcendental by Liouville's argument. Indeed, the \(n\)th truncation has denominator dividing \(10^{n!}\) and error at most \(2\cdot10^{-(n+1)!}\). If an integer polynomial of degree \(d\) vanished at the limit, its value at the truncation would be nonzero for all large \(n\), at least \(10^{-d n!}\) in absolute value by clearing denominators, and at most a constant times the error by the mean-value theorem. This is impossible for large \(n\).

For the \(p\)-adic sum the integer truncation \(a_{p,n}\) has ordinary size at most \(2p^{n!}\) and \(v_p(\alpha_p-a_{p,n})=(n+1)!\). If \(P\in\mathbb Z[T]\setminus\{0\}\) of degree \(d\) vanished at \(\alpha_p\), the distinct truncations would give \(P(a_{p,n})\ne0\) for all large \(n\). The identity \(P(t)-P(s)=(t-s)Q(t,s)\) with \(Q\) integral gives \(v_p(P(a_{p,n}))\ge(n+1)!\). The nonzero integer \(P(a_{p,n})\) would have ordinary absolute value at least \(p^{(n+1)!}\) and at most a constant times \(p^{d n!}\), a contradiction.

Enumerate primes \(p_1,p_2,\dots\). At stage \(n\) compute an open interval of positive length with rational endpoints inside \((\alpha_\infty-2^{-n},\alpha_\infty+2^{-n})\) using the explicit real tail bound. Compute the residue \(c_i=\alpha_{p_i}\bmod p_i^n\) for \(i\le n\) using the terms of exponent less than \(n\). Write \(M=\prod_{i\le n}p_i^n\). Choose a positive denominator \(D\equiv 1\bmod M\) large enough that the interval contains more than \(n\) points \(A/D\) with \(A\equiv D c_i\bmod p_i^n\) for all \(i\le n\). Such numerators are a single arithmetic progression of step \(M\) by the Chinese remainder theorem, so this is effective. Take one such rational \(s_n=A/D\) distinct from the earlier terms. It follows that \(s_n\to\alpha_v\) in each completion. Every infinite subset of \(S=\{s_n:n\ge1\}\) has exactly that one accumulation point in \(\mathbb P^1(\mathbb Q_v)\). Indeed, every neighborhood of the limit contains all but finitely many terms, and any different point has a neighborhood disjoint from a neighborhood of the limit.

### Realize infinitely many of these terms on a single smooth projective variety

The set of integer pairs \((A,D)\) emitted by the algorithm is computably enumerable. By the Matiyasevich–Robinson–Davis–Putnam theorem it is an existential polynomial relation on integer variables. In that relation replace each integer-variable restriction, including those for \(A,D\), by the assumed rational Diophantine definition of \(\mathbb Z\). Adjoin \(D t=A\), where \(t\) ranges over \(\mathbb Q\). Every represented pair has \(D>0\). The resulting finite system defines an affine variety (taking the reduction of its coordinate ring) whose rational projection to \(t\) has exact image \(S\).

Take the closure of the graph of this projection in \(\mathbb P^N\times\mathbb P^1\), for an affine embedding in \(\mathbb A^N\). The affine graph is an open subvariety of the closure. By [Poonen's image-preserving compactification theorem, Theorem 1.3](https://math.mit.edu/~poonen/papers/chatelet.pdf), there is a regular projective variety mapping to this closure with rational-point image exactly the affine graph's rational points. Composing with projection to \(\mathbb P^1\) has rational image exactly \(S\).

Inside that regular projective variety take the reduced Zariski closure of its rational points. At least one irreducible component \(Z\) has infinitely many rational image values. Rational points are dense in each component, since the open part of that component outside the other components is relatively open in the full closure and dense in the component. Resolve \(Z\) projectively by the characteristic-zero resolution theorem of Hironaka to get an integral smooth projective \(X\to Z\) that is an isomorphism over a dense open. The rational points in that open are dense in \(Z\), so their lifts are dense in \(X\). The composite \(f\) on \(X\) is dominant because the map on \(Z\) has infinite image in \(\mathbb P^1\). Since \(X(\mathbb Q)\) is dense, its image is infinite and it is contained in \(S\). Also \(X\) is geometrically integral. The geometric components of a smooth integral \(\mathbb Q\)-variety are disjoint and Galois acts transitively on them. A rational point lies on a unique such component, which must be fixed, so there is just one.

For each place \(v\), the support of an effective divisor defined over \(\mathbb Q\) on \(\mathbb P^1\) is a finite set of algebraic points in \(\mathbb P^1(\mathbb Q_v)\). None can be the unique accumulation point \(\alpha_v\). No sequence of image points outside the support can approach it. For if such a sequence existed, some support point would be a limit of a subsequence, and that subsequence would contain infinitely many distinct values since its terms are outside the support. This proves failure of Conjecture 5.24 at every place with the same witness.
