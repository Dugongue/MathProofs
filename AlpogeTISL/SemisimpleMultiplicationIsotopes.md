# Special-linear equivalence of semisimple multiplication isotopes

Fix a finite field $F$ of cardinality $q$. A raw bilinear tensor is a multiplication isotope if it is ordinarily isomorphic, by independent linear maps on the three modes, to the multiplication of a finite-dimensional unital associative algebra. There is a deterministic polynomial-time algorithm to recognize isotopes whose underlying algebra is semisimple and to decide coordinatewise special-linear equivalence of any two such isotopes. The algorithm computes the entire determinant-triple coset of ordinary transporters, or the empty set. In particular, on this locus one can return a fixed ordinary 3-TI YES or NO instance according to the computed outcome.

The proof uses the trace-restriction nondegeneracy lemma from Alpöge's release and extends the autotopism and norm calculation for quaternion and split matrix multiplication tensors in *Small-prime certificates for special-linear isomorphism of split matrix-algebra tensors*. The finite-field argument uses separability. It has no analytic RH or GRH premise. The proof is in prose. [Alpöge's release announcement](https://alpo.ge/remark.pdf)

## Recovering the underlying multiplication

Write the tensor as $T:U\times V\to W$. A transporter from $T$ to $T'$ is written $(P,Q,R)$ with $T'(Pu,Qv)=R T(u,v)$. In the covariant tensor convention the first two mode matrices are inverse transposes of $P,Q$. The determinant-one condition is identical in both conventions. The dimensions in a multiplication isotope are equal. The zero-dimensional case is immediate.

Compute the linear space
$$
 S_T=\{(X,Y)\in\operatorname{End}(U)\times\operatorname{End}(V):
      T(Xu,v)=T(u,Yv)\text{ for all }u,v\}.
$$
Its projections $B_U,B_V$ are unital endomorphism subalgebras, since $S_T$ is closed under $(X,Y)(X',Y')=(XX',Y'Y)$.

For multiplication in an associative unital algebra $A$, substitution of $1$ into the equations defining $S_T$ gives $X(x)=xa$, $Y(y)=ay$ for $a=X(1)=Y(1)$. Associativity gives the converse. Thus in hidden coordinates $T(Px,Qy)=R(xy)$, the projected algebras are $P\operatorname{Right}(A)P^{-1}$ and $Q\operatorname{Left}(A)Q^{-1}$. Evaluation on each mode is isomorphic to the left regular module of its projected algebra, using the opposite algebra for $B_U$.

For each projection $B$, run constructive module isomorphism between its left regular action on $B$ and its evaluation action on the corresponding mode. Use the action matrices of a basis of $B$ as generators. The image of $1_B$ under the resulting module isomorphism is cyclic for the evaluation action. On $V$, for example, it is $\beta=Q(b)$ with $Ab=A$, which gives a left inverse of $b$. A left inverse is a two-sided inverse in a finite-dimensional algebra, by first obtaining injectivity and then surjectivity of left multiplication by $b$. The other projection gives $\alpha=P(a)$ with $aA=A$, so $a$ is also a unit. The choices are independent. [Brooksbank and Luks, Testing isomorphism of modules](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

Put $L=T(\alpha,-):V\to W$, $J=T(-,\beta):U\to W$, and
$$
 x\star y=T(J^{-1}x,L^{-1}y).
$$
In the hidden coordinates, $J(Px)=R(xb)$ and $L(Qy)=R(ay)$. The slices are invertible. Substitution shows that $z\mapsto R(zab)$ is an algebra isomorphism $A\to(W,\star)$. In particular $(J,L,I)$ transports the raw tensor to the normalized multiplication.

For recognition, reject unequal dimensions, a failed projected-module comparison, or a singular required slice. Verify associativity and existence of an identity for the normalized table, using the basis and linear equations. With invertible slices, a table that passes these checks itself witnesses that the tensor is a multiplication isotope. Compute its Jacobson radical and require it to vanish. These steps give a deterministic polynomial-time recognition algorithm, including tensors outside the locus. [Rónyai, Computing the structure of finite algebras](https://www.sciencedirect.com/science/article/pii/S074771710880017X)

## The determinant image

Suppose $R(xy)=P(x)Q(y)$ for a multiplication self-transporter. With $a=P(1)$ and $b=Q(1)$, the equations $R(y)=aQ(y)$ and $R(x)=P(x)b$ imply that $a,b$ are units. Put $\phi(x)=a^{-1}R(x)b^{-1}$. Then $P(x)=a\phi(x)$, $Q(y)=\phi(y)b$, and substitution gives $\phi(xy)=\phi(x)\phi(y)$. Also $\phi(1)=1$. Conversely, any two units and algebra automorphism $\phi$ give a self-transporter $(L_a\phi,R_b\phi,L_aR_b\phi)$, where $L_a(x)=ax$ and $R_b(x)=xb$. The same calculation between two algebras shows that an ordinary transporter exists exactly when there is a unital algebra isomorphism.

Write $A=\prod_i M_{d_i}(E_i)$, where $E_i/F$ has degree $e_i$. Left multiplication applies a matrix to each column. Right multiplication applies it to each row. Their determinants on a block over $F$ are $N_{E_i/F}(\det_{E_i} a)^{d_i}$. Matrix determinant and finite-field norm are surjective, so the common image on the product is
$$
 C=(F^\times)^{\gcd(q-1,d_1,\dots,d_s)}.
$$

An automorphism permutes simple factors of the same type $(d_i,e_i)$. On a block it consists of entrywise Frobenius followed by inner conjugation, by Skolem–Noether after removing the induced center map. Inner conjugation has determinant one because the multiplication determinants cancel. Frobenius on $E_i$ cycles a normal basis, so its entrywise action on the matrix block has determinant $(-1)^{(e_i-1)d_i^2}$. Transposition of two copies of a type has determinant $(-1)^{e_i d_i^2}$ by exchange of two ordered bases of length $e_i d_i^2$. Hence the automorphism determinant image $D$ is generated by these signs. In odd characteristic it contains $-1$ precisely if some odd $d_i$ occurs with even $e_i$, or a type with both $d_i,e_i$ odd occurs at least twice. In characteristic two $D=\{1\}$.

Independence of the two units and the automorphism gives the exact determinant group
$$
 H=\{(u r,v r,u v r):u,v\in C,\ r\in D\}.
$$
Membership of $(a,b,c)$ is tested using $r=ab/c$ and checking $r\in D$ and $a/r,b/r\in C$. For $g=\gcd(q-1,d_1,\ldots,d_s)$, membership in $C$ is one exponentiation to the power $(q-1)/g$. Normalization conjugates each mode of the self-transporter group, preserving its determinant.

## Trace Gram and reference determinants

Two semisimple algebras are isomorphic exactly when their multisets of pairs $(d_i,e_i)$ agree. When these multisets agree, let $\phi:A\to A'$ be any algebra isomorphism and $r=\det_F\phi$ in the two given bases. The intrinsic symmetric bilinear form
$$
 B_A(x,y)=\sum_i\operatorname{Tr}_{E_i/F}
          \bigl(\operatorname{tr}_{M_{d_i}(E_i)}(x_i y_i)\bigr)
$$
is preserved by $\phi$. Its nonsingularity follows from the trace-restriction lemma in Alpöge's release, theorem traceGram_det_ne_zero in *CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean*. On each factor use the identity involution and the $E_i$-Gram matrix of $(x_i,y_i)\mapsto\operatorname{tr}(x_i y_i)$. Matrix units pair with their transposes, so this Gram matrix is nonsingular, and $E_i/F$ is separable. The lemma gives nonsingularity after restriction from each $E_i$ to $F$. Direct sum gives the displayed form and
$$
 r^2=\det B_A/\det B_{A'}.
$$
If $D=\{1,-1\}$ in odd characteristic, both roots occur as determinants of algebra isomorphisms by composing with a determinant-$-1$ automorphism. If the characteristic is two, the equation has a unique root and an isomorphism exists by the agreement of types. For these cases the trace form gives the exact determinant coset of algebra isomorphisms.

To compute the form and multiset, compute the center linearly and split its fixed algebra under $z\mapsto z^q$ to find the primitive central idempotents, since the fixed algebra is a product of copies of $F$. In each center component $E_i$, the dimension of the corresponding ideal over $E_i$ gives $d_i^2$. The reduced matrix trace is computable without a matrix presentation, including when $p=\operatorname{char}F$ divides $d_i$. Write $d_i=p^a m$, where $p\nmid m$. The characteristic polynomial of $E_i$-linear left multiplication by $x_i$ is the reduced matrix characteristic polynomial raised to $d_i$, by its repeated column action. Its coefficient at exponent $d_i^2-p^a$ is $(-m\,\operatorname{tr}(x_i))^{p^a}$. Apply inverse Frobenius and divide by $-m$ to recover the trace. Compute this on products of basis vectors and take field trace to obtain the Gram matrix.

In odd characteristic with $D=\{1\}$, resolve the sign left by the square equation by constructing one algebra isomorphism. Rónyai's reduction to finite-field polynomial factorization constructs explicit matrix presentations of the finite simple factors. Factoring over any explicitly represented extension of a fixed prime field is deterministic polynomial time. For a squarefree polynomial, the fixed algebra of base-field Frobenius in its quotient is a product of copies of the base field. For any two components, some element of a basis of this algebra distinguishes them. Multiply by members of a prime-field basis of the base field and take trace to the prime field. Nondegeneracy of the field trace pairing ensures one such function still distinguishes the components. Compute these functions by sums of Frobenius powers in the quotient and split by their at most $p$ values using gcds. Squarefree decomposition handles multiplicities over the perfect base field. Match centers of equal degree by deterministic $F$-isomorphisms and extend entrywise. Composing with the explicit matrix presentations produces $\phi$ and its determinant. [Rónyai, Computing the structure of finite algebras](https://www.sciencedirect.com/science/article/pii/S074771710880017X) · [Lenstra, Finding isomorphisms between finite fields, Theorem 9.3](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf)

## Assembling the test

Let $J,L$ and $J',L'$ be the source and target normalization maps. An algebra isomorphism $\phi$ gives the ordinary transporter
$$
 ((J')^{-1}\phi J,\ (L')^{-1}\phi L,\ \phi).
$$
Writing $\lambda_J=\det J/\det J'$ and $\lambda_L=\det L/\det L'$, the entire determinant coset of raw transporters is
$$
 (\lambda_J r,\lambda_L r,r)\,H
$$
for any determinant $r$ of a normalized algebra isomorphism. Equivalently it is
$$
 \{(\lambda_J u r,\lambda_L v r,u v r):
        u,v\in C,\ r\in\det_F\operatorname{Iso}_{\mathrm{alg}}(A,A')\}.
$$
If the type multisets differ, the transporter set is empty. With matching types, an SL transporter exists exactly when $(1,1,1)$ is in the displayed set. The only possible required value of $r$ is $(\lambda_J\lambda_L)^{-1}$. Check that this value occurs as the determinant of an algebra isomorphism and that $(\lambda_J r)^{-1}$ and $(\lambda_L r)^{-1}$ belong to $C$. The cases using the trace form need only one squared comparison for the algebra-isomorphism factor.

This covers arbitrary basis twists, nonsplit centers, repeated simple blocks and all characteristics on the semisimple isotope locus. The raw slice recovery works for every unital associative multiplication isotope. The algebra isomorphism and orientation calculation above uses semisimplicity. The unrestricted same-field reduction remains open.
