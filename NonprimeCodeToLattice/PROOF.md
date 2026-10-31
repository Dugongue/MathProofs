# Nonprime-Field Code Equivalence to Lattice Isomorphism

**Status:** AI-assisted informal proof; separate AI-worker review and exact finite checks where supplied. No Lean certificate; independent human review and publication-priority assessment remain pending.

Complete informal proof at polynomial alphabet-size cost — 31 October 2026

## Theorem And Exact Complexity
For every presented finite field F_q, monomial equivalence of arbitrary linear codes over F_q reduces to Euclidean lattice isomorphism. The construction and witness recovery cost poly(n,k,q), for length n and dimension k. The output lattice rank is at most

    (p^2+1) n(q-1)(3n+7) = O(n^2 q^3),

where p is the characteristic. There is no genericity, distance, hull, rate, nondegeneracy, or extension-degree restriction on the original codes. The algorithm handles zero columns and unequal ranks explicitly. A supplied lattice isometry yields an original monomial code isomorphism in time polynomial in the constructed instance size.

This is alphabet-polynomial, not uniform polynomial in log q. In particular, for every fixed finite field it is an ordinary polynomial-bit-time many-one reduction, and it is polynomial bit time when q is polynomially bounded in the other input parameters. It does not settle the separately stated poly(n,k,log q) uniformity question for exponentially large q.

## Source Target
Cheraghchi, Shagrithaya and Veliche, Reductions Between Code Equivalence Problems, arXiv:2502.07916 / IACR ePrint 2025/208, identifies nonprime-field code equivalence to lattice isomorphism as an open direction. Horlemann, Mazumder, Schaller and Weger, A Survey on Code Equivalence: The State-of-the-Art and Open Questions, arXiv:2607.12870v2, Section 6 explicitly asks whether there are reductions from LEP to LIP over nonprime fields. Section 4.4 distinguishes existing alphabet-polynomial prime-field reductions from the separate desired polylogarithmic field dependence.
https://arxiv.org/abs/2502.07916
https://eprint.iacr.org/2025/208
https://arxiv.org/html/2607.12870v2#S6

The result supplies the nonprime-field direction at the stated alphabet-polynomial cost. No literature-first claim is made before a wider priority review. The Construction A and shortest-vector arguments below are classical; the proposed contribution is the field-descent frame and its composition.

## 1. INPUT MODEL AND PREPROCESSING
The common field is supplied as F_p[T]/(h(T)), with h irreducible of degree s, q=p^s, and its coordinate representation is part of the input. All field arithmetic is effective. We do not construct a field from q alone or seek a multiplicatively primitive element.
Reduce both generators to full row rank. Different lengths or ranks give an immediate NO instance. In a full-row-rank generator, a zero column is an invariant under monomial equivalence: an invertible row map cannot turn a nonzero column into zero. If zero-column counts differ, return a fixed pair of nonisometric one-dimensional lattices Z and 2Z. Otherwise remove the same number of zero columns from both inputs and retain their locations for final recovery. If all columns are zero, the codes are equal and return Z,Z. Henceforth G,H are full-row-rank k by n matrices with k>=1 and all columns nonzero.
For s>1 let alpha be the class of T. Its degree over F_p is s, so alpha is neither 0 nor 1 and F_p[alpha]=F_q. When s=1 omit the fourth family below; the proof simplifies because every F_p-linear endomorphism of F_p is already multiplication by a scalar.

## 2. THE FOUR-FAMILY POINT CONFIGURATION
Write g_i for column i of G. Work in

    F_q^(k+n) = U direct-sum Y,
    U=F_q^k, Y=F_q^n,

and let e_i be the standard basis of Y. For each i form four nonzero vectors

    X_i=(g_i,0),
    Y_i=(0,e_i),
    Z_i=(g_i,e_i),
    W_i=(alpha*g_i,e_i).

Each symbol also denotes its one-dimensional F_q span when context requires it. Choose the polynomial F_p basis 1,T,...,T^(s-1), and let Gamma be the additive coordinate isomorphism from F_q^(k+n) to F_p^(s(k+n)).

Construct a generator E(G) over F_p as follows. For every a in F_q minus {0}, include the actual column Gamma(a X_i) once, Gamma(a Y_i) n+1 times, Gamma(a Z_i) n+2 times, and Gamma(a W_i) n+3 times. Repeat for every i. Thus

    L = n(q-1)(3n+7)

is its length when s>1. Its row rank is d=s(k+n): the X columns span U over F_p, because the original g_i span U over F_q and all their multiples are included; the Y columns span Y. When s=1 omit W, giving a smaller length bounded by the same displayed bound.

The construction enumerates only q-1 scalars for each of O(n) vectors. It never enumerates F_q^k or possible transporters.

## 3. EXACT MULTIPLICITIES FORCE THE FOUR ROLES
All vector sets in the Y,Z,W roles are mutually disjoint and disjoint from X. Within Y,Z,W, different indices have different nonzero Y-coordinate blocks. For a fixed index, equality of a Z vector with a W vector would imply a=b from its Y coordinate and then (alpha-1)a g_i=0, impossible. The other disjointness assertions follow similarly, using g_i!=0.
Only X sets may coincide, precisely when original columns span the same F_q line. Therefore every actual X-column value has multiplicity between 1 and n, whereas every actual Y,Z,W value has multiplicity exactly n+1,n+2,n+3 respectively.

Suppose E(G),E(H) are permutation equivalent. There is an invertible F_p-linear row map S taking their actual column multisets to each other. Invertibility preserves equality and inequality of columns, so it preserves exact multiplicities. Thus S preserves all four roles separately. The X role spans U and the Y role spans Y, hence

    S = diag(A,B)

for invertible F_p-linear maps A on U and B on Y. This conclusion does not assume F_q-linearity.

## 4. FINITE UNIONS IDENTIFY THE INDIVIDUAL BLOCKS
As F_p spaces the Y_i are independent s-dimensional subspaces whose direct sum is Y. The maximal F_p-linear subspaces contained in their union are exactly these Y_i. Indeed, a subspace containing nonzero vectors from two different direct summands also contains their sum, which is outside that union. Hence B permutes the individual Y_i. Write this permutation as pi, and write its restriction as

    B(a e_i)=B_i(a)e'_pi(i),

where B_i:F_q->F_q is an invertible F_p-linear map.

The Z_i also form a direct sum of s-dimensional F_p subspaces: their projection onto Y is the direct-sum system of coordinate blocks. Since S preserves the Z role, it permutes these blocks as well. Projection onto Y forces this permutation to be the SAME pi. Consequently, for every a in F_q,

    A(a g_i)=g'_pi(i) B_i(a).                 (1)

Exactly the same argument applies to W, whose blocks are independent by their Y projections. Its permutation must again be pi, so

    A(alpha*a*g_i)=alpha*g'_pi(i) B_i(a).    (2)

The finite-union assertion uses independence, not the false assertion that every subspace in an arbitrary finite union lies in one member. This distinction also makes the proof valid in characteristic two.

## 5. THE FOURTH ROLE FORCES THE ENTIRE FIELD ACTION
Apply (1) to alpha*a and compare with (2). Since g'_pi(i) is nonzero,

    B_i(alpha*a)=alpha*B_i(a).

Thus B_i commutes with multiplication by alpha. It is F_p-linear and F_q=F_p[alpha], so it commutes with multiplication by every element of F_q. Therefore

    B_i(a)=d_i a,   d_i=B_i(1)!=0.

Equation (1) now reads A(a g_i)=a d_i g'_pi(i). Since the g_i span U over F_q, additivity shows that A is globally F_q-linear: express any u as sum_i a_i g_i, apply the identity to t a_i, and obtain A(tu)=t A(u). It remains invertible because it was already an invertible additive map. Taking a=1 gives

    A g_i = d_i g'_pi(i).

This is precisely a monomial equivalence of the original codes, after taking inverse diagonal entries if using the convention A G D P=H. For s=1, B_i is already scalar multiplication and (1) gives the same conclusion without W.

## 6. COMPLETENESS OF FIELD DESCENT
Conversely suppose an F_q-linear A, a permutation pi and nonzero d_i satisfy A g_i=d_i g'_pi(i). Extend it to an F_p-linear map on U direct-sum Y by

    S|U=A,   S(a e_i)=a d_i e'_pi(i).

It sends each X,Y,Z,W field line onto the corresponding target line, including the W role because A is F_q-linear. All nonzero scalar multiples are present with the same role multiplicity, so it takes the actual column multiset E(G) to E(H). This gives a permutation equivalence of the prime-field codes.

We have proved for all input pairs

    LEP_Fq(G,H) iff PEP_Fp(E(G),E(H)).

The result is not based on naive scalar expansion of G; the added independent blocks and commuting-operator role prevent the extra F_p-linear equivalences that would otherwise invalidate descent.

## 7. SIGNED PERMUTATIONS DO NOT ADD EQUIVALENCES
Every actual column v in E(G) has the same multiplicity as -v, because all nonzero scalars are included. This is central symmetry of the actual column multiset, not only of its projectivization.

For any row map S, both the transformed source multiset and the target multiset have this property. A signed coordinate equivalence preserves the total column count at each pair {v,-v}. In odd characteristic each individual count is half that total, so the actual column multisets must agree. In characteristic two the signs are identical. Hence signed permutation equivalence is equivalent to ordinary permutation equivalence on these codes.

## 8. SUPPLYING THE DISTANCE HYPOTHESIS
Let R=p^2+1 and repeat every coordinate of the p-ary code E(G) exactly R times, obtaining J(G). Any nonzero codeword now has Hamming weight at least R. Central symmetry of columns persists. Repetition multiplies every actual column count by the same R. Thus signed equivalence of J(G),J(H) implies exact equality of source/target actual column multisets after a row map, and division of these integer counts by R recovers permutation equivalence of E(G),E(H). The converse follows by repeating a permutation. No min-distance computation or promise is needed on the original input.

## 9. AN EXPLICIT INTEGER LATTICE
For C=rowspace_Fp(J(G)), define

    Lambda(G)={ z in Z^N : z modulo p belongs to C },
    N=R L.

This is the standard Construction A lattice. A basis is explicit. Put a full-row-rank generator in systematic form [I_d | Q] by Gaussian elimination and a coordinate permutation. Lift Q entrywise to integers in 0,...,p-1 and take the rows of

    [ I_d   Q ]
    [  0   pI ].

Undo the coordinate permutation on these rows. Every integer vector with residue in C has this representation: use its first d coordinates as the top-row coefficients and divide the remaining residual coordinates by p. Conversely every displayed row combination has residue in C. The basis is triangular before undoing the permutation, with determinant p^(N-d).

## 10. EVERY LATTICE ISOMETRY IS A SIGNED COORDINATE PERMUTATION
If a nonzero vector of Lambda(G) lies in p Z^N, its squared length is at least p^2, with equality exactly for the vectors +/-p e_j. If its reduction modulo p is nonzero, that reduction is a nonzero codeword and has at least R nonzero coordinates. The integer vector therefore has squared length at least R=p^2+1.

Consequently the shortest nonzero vectors of Lambda(G) are EXACTLY +/-p e_j. Any orthogonal isomorphism between two output lattices permutes these vectors, so it is a signed coordinate permutation. Reducing modulo p yields signed equivalence of the J codes. Sections 7 and 8 recover PEP of the E codes; Sections 3 through 6 recover original F_q monomial equivalence.

Conversely an original monomial equivalence induces a permutation equivalence of E and J, hence an integer coordinate permutation between the Construction A lattices. This proves both YES and NO preservation.

## 11. WITNESS RECOVERY AND COST
Given an explicit ambient orthogonal isometry, read its signed permutation using the shortest-frame conclusion; this is a proof about its entries, not a shortest-vector search algorithm. Reduce it modulo p and solve the full-row-rank generator equation for the induced F_p row map S. The central-symmetry and repetition arguments ensure this same S maps the E-column multisets exactly. Read the Y-block permutation pi, the scalars d_i=B_i(1), and the F_q-linear matrix of A from its images on an F_q basis of U. Restore the previously removed zero columns by an arbitrary bijection. All recovery is ordinary exact linear algebra and sorting of explicit column lists.

There are O(nq) line elements before multiplicity tagging and O(n^2 q) columns afterwards. The p-ary row dimension is s(k+n). Repetition gives N=O(n^2 q p^2), and a dense lattice basis uses O(N^2 log p) bits. Every construction and recovery step costs polynomial time in n,k,q. It is not claimed polynomial in the binary length of an arbitrarily large q.

## 12. REUSE, AUDIT, AND NOVELTY
The construction uses the project's stabilizer/marker methodology: attach explicitly paid auxiliary structures that force transporters to respect a source decomposition, then extract the original transporter. The centralizer-of-a-field-generator argument, field restriction of scalars and Construction A are established mathematics. They are credited rather than assigned invented names.

Two independent workers audited the complete algebra and the lattice completion, including zero columns, exact role multiplicities, direct-sum reconstruction, the shared permutation, characteristic two, field-generator versus primitive-element distinctions, distance amplification, and source complexity conventions. Their full reports are in AUDIT.md and the separately reviewed construction described here.

Exact finite tests independently enumerate full prime-field row groups for a small descent instance and inspect all codewords of a small amplified code; they supplement the universal proof. No Lean certificate or absolute novelty claim is made. This result should be described as a complete informal field-extension reduction at alphabet-polynomial cost, while explicitly retaining the separate polylog(q) question.
