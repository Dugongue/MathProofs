# Genus-two epimorphisms from Frobenius complete intersections

Informal sufficient theorem addressing Grochow–Srivastava–Thakkar Question 3(3). Let K be a finite field of odd characteristic p. Put
$$
R=K[x_1,\ldots,x_r]/(x_1^{p^{e_1}},\ldots,x_r^{p^{e_r}}),\qquad e_i\ge1.
$$
The case r=0 gives R=K. Let S be any finite commutative local K-algebra with residue field exactly K. From an explicit structure-constant presentation of S and the compact list of the e_i, one can count unital K-algebra epimorphisms R onto S and construct one in polynomial bit time. There is no bound on r, the socle rank or embedding dimension of S, or its nilpotency length.

For the associated stem genus-two groups defined below this yields deterministic polynomial Cayley-table decision, construction and exact counting on a class with no bound on nonreduced centroid length. The full published genus-two question remains open. Its literal definition allows centroids beyond this source class. [Published question](https://arxiv.org/html/2609.07429v1#S7) · [Brooksbank–Maglione–Wilson, Definition 3.2](https://joshmaglione.com/papers/Genus2.pdf)

## 1. The ring map is a nested rank problem

Write J for the radical of S, H=J/J squared, and h for its K-dimension. For each e set
$$
N_e=\{s\in J:s^{p^e}=0\},\qquad U_e=(N_e+J^2)/J^2\subseteq H.
$$
The Frobenius power is additive in a commutative characteristic-p algebra and satisfies F^e(a s)=a^{p^e}F^e(s). Since K is a finite field its scalar Frobenius is an automorphism. Thus N_e is a K-subspace, although F^e itself need not be K-linear. Compute its kernel by prime-field linear algebra and then choose a K-basis. The subspaces N_e and U_e increase with e.

A unital K-algebra homomorphism R to S is determined by independent images s_i in N_{e_i}. Conversely any such tuple gives a homomorphism, by precisely the defining relations of R. It is onto exactly when the classes of the s_i span H. For sufficiency, every radical element can be written as a K-linear combination of those generators plus an element of J squared. Iterating this substitution inside products expresses it as a polynomial in the s_i modulo J to any specified power. The error vanishes by nilpotence. The field K is already in the image.

Sort e_i increasingly, put u_i=dim U_{e_i} and n_i=dim N_{e_i}. For a partial choice of head columns with rank a the preceding span lies in U_{e_i}. Exactly q^a next columns preserve rank, and q^{u_i} minus q^a increase it. A dynamic program on i and a therefore gives the exact number D of spanning head choices. Each column has q^{n_i-u_i} original lifts, independently. The ring epimorphism count is
$$
D q^{\sum_i(n_i-u_i)}.
$$
A positive completion count selects a basis direction or a vector in the existing span. Linear lifting then supplies the actual generator images. This is the homogeneous instance of the compact nested-column algorithm in the preceding [module proof](PriorModules.md).

The arithmetic and output bit lengths are polynomial in the written target dimensions, the field representation, and r. Very large e_i need no repeated powering beyond the nilpotence length. If p^{e_i} is at least dim_K S, every element of J satisfies that relation, since J to that power is zero. Compare exponents in binary and truncate the number of Frobenius iterations accordingly. Multiplication tables over K give polynomial-time prime-field and K-linear arithmetic in the explicit target model.

## 2. Recognizing the source rings from raw tables

The structural source promise is recognizable in polynomial ring-table time. Compute the residue field K, its unique coefficient-field copy, and J. In characteristic p the coefficient copy consists of the roots of a^q=a, where q=|K|. Each residue root lifts uniquely through nilpotent powers because the derivative is minus one. Commutativity implies that these roots form a field. Enumerating ring elements gives a deterministic table-time implementation.

Compute the increasing head flag U_e for R itself. Choose a basis of J/J squared adapted to that flag and lift each new basis vector from N_e. Let the corresponding e values be e_1,...,e_r. They yield a surjection from the displayed truncated polynomial algebra onto R. Test
$$
\dim_K R = p^{\sum_i e_i}.
$$
If this equality holds, the surjection is an isomorphism. If the right side exceeds the left, computation may stop immediately. No exponential expansion is necessary for this test.

Conversely in a truncated polynomial algebra of the displayed kind, its monomials form a basis and their p^e-th powers are either zero or distinct surviving monomials. Hence its Frobenius head kernel U_e is exactly the span of the variables whose defining exponent e_i is at most e. The flag recovers the correct lengths, and the dimension equality holds. The test therefore recognizes exactly this source class among the finite commutative local characteristic-p algebras.

For epimorphisms as F_p-algebras, the source and target residue fields must be isomorphic. Indeed source variables are nilpotent, so their images cannot generate additional residue-field elements. For equal residue fields of degree f over F_p, enumerate their f field isomorphisms. Each has the same tuple count because the defining power relations have prime-field coefficients. Multiply the count from Section 1 by f. Different field choices give disjoint homomorphisms.

## 3. The corresponding literal genus-two groups

For a finite commutative local F_p-algebra A put V=A^3, W=A^2 and
$$
b_A((x,y,z),(a,b,c))=(xb-ya,xc-za).
$$
Let G_A have underlying set V plus W and product given by addition plus one half of b_A. It has class two, exponent p, center equal to its derived group W, and centroid A. Its genus is exactly two under the residue-rank definition, since W is free of rank two over A. The flat-bimap centroid and quotient correspondence were proved in the earlier [local-ring genus note](PriorGenus.md). Here are the exact ingredients needed for counting.

A group epimorphism induces surjective prime-field maps L:A^3 to S^3 and M:A^2 to S^2 preserving b. Its kernel on the first space is the common radical of M b_A and is stable under multiplication by A. Thus multiplication descends to a unital map alpha from A to the centroid S. It makes both L and M alpha-semilinear. The two images M(1,0), M(0,1) span S^2 as an S-module, because M is onto. Their matrix is invertible over S. It follows that alpha(A)=S. Conversely a ring epimorphism supplies group maps coordinatewise.

For a fixed alpha, write L=P alpha cubed and M=Q alpha squared. Both P and Q are invertible and S-linear, and must be pseudo-isometries of b_S. Its wedge kernel is the free line generated by e_2 wedge e_3. Preserving that line is equivalent to preserving the plane U spanned by e_2,e_3. This follows by taking its wedge-annihilator in S^3, and holds over a local ring because every displayed basis vector is primitive. Hence all allowed P have block form
$$
P=\begin{pmatrix}a&0\\c&D\end{pmatrix},\qquad a\in S^\times,\quad c\in S^2,\quad D\in\operatorname{GL}_2(S).
$$
The induced Q is aD. Their number is
$$
|S^\times|\,|S|^2\,|\operatorname{GL}_2(S)|.
$$
For residue field of order q and radical J_S the last factor equals
$$
|J_S|^4(q^2-1)(q^2-q).
$$
Finally every bracket-preserving pair admits all prime-field linear central additions tau:A^3 to S^2. If a=dim_Fp A and s=dim_Fp S there are p^{6as} of them, and they give distinct group maps. Therefore the exact group count is
$$
\#\operatorname{Epi}(G_A,G_S)=\#\operatorname{Epi}_{\mathbb F_p\text{-alg}}(A,S)\,|S^\times|\,|S|^2\,|\operatorname{GL}_2(S)|\,p^{6as}.
$$
The scalar ring map alpha is recovered uniquely by centroid descent, so this product has no overlapping alpha branches.

## 4. Raw group input and costs

On promised Cayley tables compute the elementary central and derived spaces and the commutator bimap by the odd-characteristic class-two correspondence. Compute its centroid by linear equations. For a flat bimap first check the necessary dimension identities dim V=3 dim centroid and dim W=2 dim centroid, and that the centroid is local. Its ring elements can then be enumerated within polynomial time in the group-table size.

Enumerate triples in V. Test whether each is a free centroid basis, whether b(v_2,v_3)=0, and whether b(v_1,v_2),b(v_1,v_3) form a free basis of W. Rank tests over the prime field verify these conditions. The centroid identity supplies bilinearity, so they are equivalent to the displayed flat normal form. The search costs at most |V| cubed times polynomial overhead, and constructs the coordinates used above. The source-ring recognition of Section 2 then tests its Frobenius complete-intersection form.

Every ring order, field search, rank computation and basis search is polynomial in the original group table length. One may reject inputs outside the source class; the theorem only asserts the stated class. For nontrivial target and source the primes must agree. For ring residue fields of different sizes the answer within this flat family is zero, as shown above.

This extends the earlier target-bounded-generator/bounded-socle ring algorithm in a different direction. The target may have unbounded generator number and socle dimension. For example its radical may have square zero and arbitrary dimension, or it may have arbitrary further local relations. The source, however, has the explicitly recognized Frobenius complete-intersection form. No full solution of the published genus-two problem or publication priority is asserted.
