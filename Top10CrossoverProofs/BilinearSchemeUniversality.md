# Which fixed bilinear maps realize every affine scheme?

Let \(k\) be a perfect field and \(B:U\times V\to W\) a fixed nonzero bilinear map of finite-dimensional \(k\)-vector spaces. A raw system for \(B\) has variables \(u_a\in U,v_b\in V\) and equations

\[
\sum_{a,b}\lambda_{ab}B(u_a,v_b)=w,\qquad \lambda_{ab}\in k,\quad w\in W.
\]

Its solution scheme has the actual coordinate equations in any chosen bases. For instance, its points over any commutative \(k\)-algebra \(A\) are the raw solutions for \(B_A\). We retain the whole scheme, including nilpotents.

Pass to the quotient of \(B\) by its left and right radicals and restrict its codomain to the span of its values. Call this map \(B_0\). Let \(C\) be its largest ring of scalars, described below. Write \(C=\prod_{i=1}^s C_i\) for its decomposition into local Artinian algebras, with residue fields \(L_i=C_i/\mathfrak m_i\). Define \(G\) to be the group of pairs \((A,D)\) preserving the output of \(B_0\), so \(B_0(Au,Dv)=B_0(u,v)\).

**Theorem.** The group \(G\) is a nonempty smooth geometrically irreducible rational affine \(k\)-group. The following statements hold.

1. Every nonempty raw solution scheme is isomorphic to a product of the form
   \[
   \mathbb A_k^r\times\prod_{i=1}^s \operatorname{Res}_{L_i/k} X_i
   \]
   for finite-type affine \(L_i\)-schemes \(X_i\).
2. Conversely, for arbitrary finite-type affine \(L_i\)-schemes \(X_i\), a raw solution scheme is isomorphic to
   \[
   G\times \mathbb A_k^t\times\prod_{i=1}^s \operatorname{Res}_{L_i/k} X_i.
   \]
   The affine dimension \(t\) is given by the numbers of variables and the nilradicals of the scalar factors. The projection to the displayed product of Weil restrictions has a \(k\)-section. The product identifies its fibers over every \(k\)-algebra and preserves all local and global existence predicates.
3. A fixed \(B\) realizes every finite-type affine \(k\)-scheme up to this smooth product if and only if some \(L_i=k\). In the other case, even two reduced \(k\)-points cannot occur as a raw solution scheme up to multiplication by any nonempty geometrically connected smooth scheme. The possible numbers of geometric connected components of nonempty raw solution schemes are exactly
   \[
   \left\{\prod_i m_i^{[L_i:k]}:m_i\in\mathbb Z_{\ge1}\right\}.
   \]

## The scalar ring and the frame group

Work first with \(B_0\) and write it as \(B\). It has zero radicals and spans \(W\). The scalar ring is

\[
C=\{(P,Q,T): B(Pu,v)=B(u,Qv)=T B(u,v)\},
\]

with maps on \(U,V,W\), respectively, and componentwise operations. Its projection to each factor is injective, by zero radicals and spanning. It is commutative. For two scalar triples with left components \(P,P'\) and right components \(Q,Q'\), move \(P\) across the pairing, use the action of \(P'\) on the output, and move the \(Q\) term back to the left to obtain

\[
B(PP'u,v)=B(P'u,Qv)=T'B(u,Qv)=B(P'Pu,v).
\]

This proves \(PP'=P'P\), and injectivity gives commutativity of the triples. Closure under multiplication follows by applying the two scalar identities in succession. The scalar ring contains \(k\) by simultaneous scalar multiplication. All defining equations for \(C\) are \(k\)-linear, so \(C_A=C\otimes_k A\) is the scalar ring of \(B_A\) for every \(k\)-algebra \(A\), including nonreduced ones. Here tensoring the exact sequences of vector spaces remains exact.

Fix bases \(e_a,f_b\) for \(U,V\). The raw equations \(B(a_a,b_b)=B(e_a,f_b)\) define the frame scheme. If \(A_0,D_0\) are the endomorphisms taking \(e_a,f_b\) to these frame vectors, they preserve \(B_A\). After reduction modulo each maximal ideal of \(A\), the reduced \(B\) still has zero radicals. In a field, \(A_0 u=0\) would imply \(B(u,v)=0\) for all \(v\), hence \(u=0\). Apply the same argument to \(D_0\). Thus their determinants are units in \(A\). This identifies the whole frame scheme with \(G\), and normalization by \(A_0^{-1},D_0^{-1}\) is regular and natural in \(A\).

Let \(J=\{(P,Q):B(Pu,v)=B(u,Qv)\}\) be the adjoint algebra, with multiplication \((P,Q)(P',Q')=(PP',Q'Q)\). The two coordinates of a unit of \(J_A\) are invertible. Conversely an adjoint pair with invertible coordinates has its componentwise inverse in \(J_A\), by substituting inverse images in the adjoint identity. The maps \((A_0,D_0)\mapsto (A_0,D_0^{-1})\) and \((P,Q)\mapsto(P,Q^{-1})\) identify \(G\) and \(J^\times\). The latter is the principal open subset of the \(k\)-vector space \(J\) on which the two determinants have invertible product. It contains the identity, so it has all claimed geometric properties.

## Every raw scheme has a Weil-restriction decomposition

Because \(k\) is perfect, each \(L_i/k\) is separable and has a coefficient-field embedding \(L_i\hookrightarrow C_i\). To obtain it, choose a primitive element of \(L_i/k\) with separable minimal polynomial \(g\), lift it to \(C_i\), and apply Newton steps. The derivative is a unit and each step doubles the order of the error in the maximal ideal. That ideal is nilpotent, so finitely many steps give an exact root inducing the chosen primitive element. This also covers \(L_i=k\), where the existing scalar map suffices.

The central idempotents \(\epsilon_i\) give decompositions \(U=\bigoplus U_i\), \(V=\bigoplus V_i\), and \(W=\bigoplus W_i\). The scalar identities give \(B(U_i,V_j)=0\) for \(i\ne j\), and \(B_i:U_i\times V_i\to W_i\) is \(L_i\)-bilinear using its coefficient field. For any raw system, write each variable and right side in these components. In fixed \(L_i\)-bases, the \(i\)-th set of component equations defines an affine \(L_i\)-scheme \(X_i\). For every \(k\)-algebra \(A\), solutions of the original system correspond precisely to the independent solutions over \(L_i\otimes_k A\) of these systems. This is the functor of the product of Weil restrictions.

Returning to the original \(B\), a right side outside the span of its values gives the empty scheme. The radical coordinates of every input variable are free, after choosing linear splittings of the two radical quotients. They supply the affine factor in assertion 1.

## The compiler realizes every permitted product

Adjoin a frame and normalize all other unknowns by it. Describe a scalar element of \(C_A\) by its left and right columns \(p_a=P e_a\), \(q_b=Q f_b\) in normalized coordinates. First impose \(B(p_a,f_b)=B(e_a,q_b)\). Let \((\rho_{ab})\) range over a fixed basis of the kernel of the surjection \(U\otimes_k V\to W\), in these bases. Require

\[
\sum_{a,b}\rho_{ab} B(p_a,f_b)=0
\]

for each basis vector. These are raw equations when the frame is substituted for \(e_a,f_b\) and all columns are stored in frame coordinates. They ensure that \(B(p_a,f_b)\) gives a well-defined output endomorphism \(T\). The kernel and quotient are direct summands over \(k\), so the criterion works over each \(A\). Endomorphisms are determined by their columns and the output action is determined by the span of the values. Thus the scalar variables introduce exactly \(C_A\), with no additional variables ranging over output endomorphisms.

Addition uses column-wise linear equations checked against the opposite basis. To impose \(XY=Z\) use

\[
B(p_a^Y,q_b^X)=B(p_a^Z,f_b).
\]

The scalar identities turn its left side into \(B(P_XP_Y e_a,f_b)\); zero radicals prove equivalence to the product gate. To pin a fixed scalar \(\gamma\in C\), impose \(B(p_a,f_b)=B(P_\gamma e_a,f_b)\), using a fixed right side and the frame. Thus a finite polynomial circuit over \(C\) has a raw implementation. Every intermediate gate variable is uniquely determined, so these equations implement a scheme isomorphism rather than an existential projection with uncontrolled fibers.

For each \(i\) write \(X_i\subseteq\mathbb A_{L_i}^{n_i}\) by finitely many polynomials \(f_{ij}\). Encode each coordinate as a variable from \(C_i\otimes_k A\), enforcing \(\gamma=\epsilon_i\gamma\) by the product gate. Lift coefficients through the chosen embedding \(L_i\hookrightarrow C_i\). Pick a nonzero \(s_i\in C_i\) killed by \(\mathfrak m_i\), using the last nonzero power of that ideal, or \(s_i=1\) if \(C_i\) is a field. Its annihilator is exactly \(\mathfrak m_i\), since every element outside that ideal is a unit. Therefore

\[
s_i f_{ij}(\gamma)=0
\quad\Longleftrightarrow\quad
f_{ij}(\overline\gamma)=0\text{ in }L_i\otimes_k A .
\]

Indeed the kernel of multiplication by \(s_i\) is \(\mathfrak m_i\otimes_k A\), by the split exact sequence of \(k\)-vector spaces. The coefficient field splits the projection to \(L_i\otimes_k A\), and its kernel is a free affine choice for each coordinate. The nilpotent-lift affine factor has dimension \(\sum_i n_i\dim_k\mathfrak m_i\). All gates are uniquely solved from these coordinates. Restoration of the original input radicals adds the number of left variables times the left radical dimension and similarly for the right. Together with the frame this gives assertion 2 by the functorial identification over every \(A\). Choosing the standard frame, zero nilpotent lifts, and zero radical coordinates gives its section.

## The exact universality criterion

Over an algebraic closure, \(\operatorname{Res}_{L_i/k}X_i\) is the product over the \([L_i:k]\) embeddings of \(L_i\). Each conjugate has the same number \(m_i\) of geometric connected components. Products of geometrically connected finite-type schemes over an algebraically closed field are connected, so the number of geometric connected components of a nonempty raw solution scheme is \(\prod_i m_i^{[L_i:k]}\). Conversely take \(X_i\) to be the disjoint union of \(m_i\) reduced \(L_i\)-rational points. The compiler realizes the desired count because \(G\) and the affine factors are geometrically connected.

If no \(L_i=k\), all the exponents are at least two, and \(2\) is not a possible count. This proves the obstruction with any geometrically connected extra factor. If some \(L_i=k\), insert an arbitrary affine \(k\)-scheme \(X\) in that slot and a point in the other slots. The scheme realizes \(X\) up to \(G\) and affine space, including all nilpotent structure.

For example, multiplication on a strict finite separable field extension \(L/k\), considered as a fixed \(k\)-bilinear map, has scalar ring \(L\). Every nonempty raw solution scheme has a number of geometric connected components that is a \([L:k]\)-th power. In contrast, the scalar ring of a nonzero scalar-valued bilinear form is \(k\), because its scalar triples inject into the endomorphisms of the one-dimensional target, and its raw systems realize all affine \(k\)-schemes in the stated sense.

## Simultaneous arithmetic realization away from finitely many primes

Suppose \(B\) is given integrally on finite free \(\mathbb Z\)-modules and its rational base change is nonzero. Let \(L_i\) now be the scalar residue fields of \(B_{\mathbb Q}\). There is an integer \(N\ge1\), depending only on \(B\), such that the decomposition and converse realization hold over \(R=\mathbb Z[1/N]\), for every \(R\)-algebra, with \(L_i/k\) replaced by the finite étale \(R\)-algebra \(S_i=\mathcal O_{L_i}[1/N]\). In the forward direction, an arbitrary system also has the base constraint that the projections of its right-hand sides to the fixed complement of the output image vanish. This is a factor \(\operatorname{Spec}(R/I)\), where \(I\) is generated by those projected coordinates. The fixed frame factor in the converse is a principal open subset of affine space over \(R\) containing the identity section. It is relatively smooth and its geometric fibers are irreducible. If the rational scalar ring has \(\mathbb Q\) as a residue field, any affine scheme of finite presentation over \(R\) is realized, with the same smooth product, by raw equations for this single \(B_R\). The compiler works simultaneously for all geometric and arithmetic coefficient specializations over this base.

To prove this, fix the rational decomposition data first. Choose rational bases for the two source radicals and complements and for the output image and a complement. After inverting finitely many primes the basis changes and their inverses are integral over \(R\), and the input radicals and output image split. The rational injective contractions and surjective output tensor remain split after base change once their chosen rational left and right inverses are integral over \(R\). The same argument applies to all linear kernels used to define the adjoints, the scalar ring, and the relations among the output values. Explicitly, for each of this finite list of linear maps, choose rational bases splitting source and target into kernel, image and complements, clear the denominators of the changes of basis and their inverses, and invert the diagonal entries of its invertible block. This makes formation of each kernel and image commute with arbitrary \(R\)-algebra base change.

Extend the rational scalar idempotents, bases for the nilpotent ideals, and coefficient field embeddings over \(R\) by clearing their finitely many denominators. For each \(i\) use the image of a \(\mathbb Z\)-basis of \(\mathcal O_{L_i}\) together with a rational basis of \(\mathfrak m_i\). The combined bases are interconvertible with the preceding basis of the scalar ring after enlarging \(N\). Consequently the resulting scalar factor splits over \(R\), as a module, into \(S_i\) and the spread-out ideal \(M_i\) from \(\mathfrak m_i\). The rational ring identities, including the multiplication tables of \(S_i\), hold integrally over this localized torsion-free base. Invert the discriminants to make the \(S_i\) finite étale. Choose compatible \(L_i\)-bases for \(U_i,V_i,W_i\), and use the same denominator argument on the bases formed with \(\mathbb Z\)-bases of the number rings. This makes their spread-out modules free over \(S_i\). Finally spread out the \(s_i\) and split the rational matrix of multiplication by \(s_i\) as above, so its kernel is exactly \(M_i\) after every base change. Only finitely many fixed matrices are involved throughout. In particular \(N\) is independent of the input scheme and its coefficients.

The arguments above now apply using those split maps instead of exactness of tensor products over a field. Frame invertibility follows from the same residue-field test using split nondegeneracy. Coefficients in \(S_i\) are available by the fixed scalar embedding, and the affine lift factor remains free in every family. This proves the arithmetic assertion.

The project’s previous coefficient-only centroid classification identifies decision problems over number fields. The extra conclusions here are the universal scheme isomorphism over all \(k\)-algebras, the smooth frame factor, and the exact criterion for stable scheme universality. The maximal ring of scalars and its interpretation in a multisorted structure are due to earlier work. External priority for the scheme statement remains to be checked independently. [Garreta–Miasnikov–Ovchinnikov](https://arxiv.org/abs/1805.02573) · [Rank-two scheme universality](https://github.com/Dugongue/MathProofs/blob/main/RankTwoGeometricUniversality/PROOF.md).
