# One Bipartite Operator Is TOCI-Complete

An informal extension of the balanced quartic result, 4 November 2026.

Theorem. Over C, with rationally encoded coefficients as in Lysikov–Walter,
OCI for End(A tensor B) under GL(A) times GL(B), acting by conjugation with
g_A tensor g_B, is TOCI-complete. Only one operator is supplied. The
reduction from their complete two-copy balanced quartic problem takes
dim A = dim B = 3 dim V and is affine-linear in the source data.

Consequently every fixed, individually balanced tensor tuple sequence for
a product of general linear groups satisfies this dichotomy: if any
component contains at least two covariant/contravariant pairs in total,
it is TOCI-complete; otherwise OCI is in deterministic polynomial time.
Here individually balanced means that within each component, for each
named mode, the number of covariant occurrences equals the number of
contravariant occurrences. This does not claim the full dichotomy for
arbitrary unbalanced tuples in Lysikov–Walter Question I.12.

1. A closed-tag lemma over the complex numbers.

Let G act algebraically on affine spaces X and Y, let pi:X->Y be an
equivariant regular map, and let y have a closed G orbit. Put H=G_y.
For x in pi^(-1)(y), the intersection of the G-orbit closure of x with
that fiber is exactly the H-orbit closure of x. To prove it, a sequence
g_j x tending to any z in that intersection can be chosen in the complex
Euclidean topology: an algebraic group orbit is locally closed, and its
Euclidean and Zariski closures coincide. Then g_j y tends to y. The orbit
map G->G y has a local analytic section s near y with s(y)=1, by the local
submersion theorem for complex Lie groups and their closed subgroups.
Hence h_j=s(g_j y)^(-1) g_j fixes y and h_j x tends to z. The reverse
inclusion is immediate. If two G-orbit closures in X meet, their common
point maps into G y because that orbit is closed, and can be moved by G
back into the fiber. Thus OCI at the tagged points is exactly OCI in the
fiber for H. A closed affine invariant data subspace in the fiber may be
identified with its source representation when taking H-orbit closures.

2. First tags: split each of the two modes into three named colors.

The source is (R_1,R_2) in End(V tensor V)^2 under the same GL(V) in both
tensor factors, TOCI-complete by Lysikov–Walter Theorem V.12(2). Let n=dim V
and A=A_1 directsum A_2 directsum A_3, B=B_1 directsum B_2 directsum B_3,
with every summand a named copy of V. We use n>=1; a zero-dimensional
source parameter has one point and may be mapped to any fixed point.

Let P_A and P_B have eigenvalues -1,0,1 on the three colors in order.
Their traces vanish. In Z in End(A tensor B) the two unnormalized partial
traces are conjugation covariants for the respective two groups. Set

       Z_0 = P_A tensor I_B/(3n) + I_A tensor P_B/(3n).

Then Tr_B Z_0=P_A and Tr_A Z_0=P_B. Their joint tag orbit is closed: a
matrix with these fixed eigenvalues and multiplicities n is characterized
by P(P-I)(P+I)=0 and the fixed characteristic polynomial. These are closed
conditions and all solutions are similar. The fiber group is the product
of the six color GL groups, denoted G_0. It fixes Z_0.

3. Second tags: couple the colors across both modes.

View Z as a block matrix indexed by the nine pairs (a,b) of colors. Add
the following invertible operators in six distinct off-diagonal blocks.
For i=2,3, add the identity transfer from (1,1) to (i,i) and its inverse in
the reverse block. Add the factor-swap transfer from (1,2) to (2,1) and
its inverse in the reverse block. The factor swap sends v tensor w to
w tensor v, using the indicated identifications of the copies of V.
Call the sum of these markers M. Each such block changes both colors, so
both of its partial traces vanish. No block coincides with a diagonal
block or with a block of Z_0.

Under G_0 the map reading those six marked blocks is equivariant into
the direct sum of the corresponding Hom spaces. The orbit of the six
markers is CLOSED there. Here is a norm proof that also accounts for
non-diagonal degenerations of all six color groups. Give all V copies
the standard Hermitian norm and all operator blocks the Hilbert–Schmidt
norm. Each marker and its reverse transform to L,L^(-1) for some
invertible L of order n^2. The sum of their squared norms is at least
2 n^2, by summing s^2+s^(-2)>=2 over the singular values of L. The original
two markers are unitary, so attain this bound. Summing over the three
pairs proves that the tag tuple is of minimum norm in its complex
reductive G_0 orbit. The classical Kempf–Ness minimum-norm criterion now
implies that the orbit is closed. The inner product used is invariant
under the product of the six standard unitary groups, as required.

Write a_i and b_i for the three GL matrices in the A and B colors. A
stabilizer of the forward and reverse identity tags satisfies

               a_i tensor b_i = a_1 tensor b_1,  i=2,3.

Since nonzero decomposable tensors are equal only up to reciprocal scalar
factors, a_i=lambda_i a_1 and b_i=lambda_i^(-1) b_1. Preservation of the
swap tag says a_2 tensor b_1 = b_2 tensor a_1. Thus a_1 and b_1 are
proportional, and all six matrices are scalar multiples of a common
h in GL(V). Conversely taking all six matrices equal to any h preserves
all six tags. The remaining scalar equations do not matter below; they
are not dropped from a claimed faithful stabilizer presentation.

4. The data have zero partial traces and trivial scalar charge.

In the three-dimensional color coordinate spaces set

          C=diag(1,-1,0),   D_1=diag(1,-1,0),   D_2=diag(0,1,-1).

On the diagonal color block (a,b), put the operator

                 C_aa ( (D_1)_bb R_1 + (D_2)_bb R_2 ).

Put zero data in all off-diagonal blocks. Denote the resulting operator
by L(R_1,R_2). This map is injective since D_1,D_2 are linearly independent
and C is nonzero. Its two partial traces vanish because both D_i and C
have trace zero. The data do not alter the six off-diagonal markers.
Our output is the single operator Z_0+M+L(R_1,R_2).

In the stabilizer of the two rounds of tags, every color map is a scalar
multiple of h. On each diagonal block the scalars cancel in conjugation,
so its action on the entire data image is exactly conjugation by h tensor
h on both source operators. Every h occurs by the all-equal choice. Thus
the data image with tags fixed is a closed affine space whose stabilizer
orbits and orbit closures identify with those of the source.

Apply Section 1 first to the two partial traces, then inside their fiber
to the six extracted blocks. Both tag orbits are closed as proved above.
It follows that OCI of the single output operators preserves and reflects
OCI of the two input operators for every pair of complex points. This
argument also preserves and reflects ordinary orbit equality. The maps
have rational constants of O(log(n+1)) bits, dimension 3n per mode, and
O(n^4) dense output entries. The target is a fixed ordinary tensor tuple
sequence, hence in TOCI. This proves completeness.

5. The full individually balanced product-group classification.

If a summand contains two or more pairs in one named mode, embed the
one-group balanced quartic theorem into those two pairs. If it has two
pairs in distinct named modes, use the bipartite theorem just proved.
All extra paired slots are padded by identity operators, and other
summands by zero. This is an equivariant closed linear embedding for the
active groups; the extra groups act trivially on the image. An equivariant
linear left inverse is obtained by projection onto the summand and
normalized partial traces over the added identity slots. In particular
the embedding preserves and reflects orbit-closure intersection. It is
polynomial size for fixed tensor tuple type. This proves the hard side
for any component with at least two pairs.

If each summand has at most one pair in total, its only possible data
are scalars and endomorphism tuples on individual modes. Scalar entries
must match exactly. For a fixed mode, all GL invariants of an endomorphism
tuple are generated by traces of words in its matrices: in the tensor
contraction description every contraction graph is a union of directed
cycles. Consequently two tuples have intersecting closures exactly when
traces of all corresponding words agree. This is checked in polynomial
time: generate the span of all word pairs (A_w,B_w) in
Mat_n(F) directsum Mat_n(F), starting at (I,I), and multiply retained basis
words by each paired input matrix until the span stops growing. It has
dimension at most 2n^2 and contains all words by closure. Test the linear
functional (A,B)->tr(A)-tr(B) on its basis. The retained word lengths
are at most 2n^2, so ordinary rational or Gaussian-rational coefficient
bit lengths and all linear algebra are polynomial in the input length.
Independent modes and scalar equality give the promised full easy branch.

The proof covers individually balanced tuples, not arbitrary unbalanced
tuples whose center weights cancel only after multiplication. It gives
no reduction of pure covariant SL orbit closure or unrestricted SL-TI.
Over C, balance does imply that ordinary GL and SL orbits coincide for
these particular actions, because scalar matrices act trivially and any
matrix may be rescaled to determinant one. That observation does not
transfer to finite-field rational points or pure covariant tensors.

Credit. The underlying two-copy complete source, contraction description,
and complex OCI model are from Lysikov–Walter, arXiv:2411.04639v2,
Theorem V.12(2), Section IV-C, and Question I.12:
https://arxiv.org/html/2411.04639v2
The use of a minimum-norm vector to prove orbit closedness is classical
Kempf–Ness theory. The two-round color coupling and trace-zero single
operator assembly above are the candidate contributions. No Lean or
first-publication claim is made.
