# Objectwise one-sign reductions from intrinsic Pfaffian data

Let F be the field of three elements. Let T be an explicit raw tensor with tested mode U_T of even dimension n. Suppose a polynomial-time algorithm returns a linear subspace Q_T of alternating forms on U_T. Require that pullback by the tested mode map of every ordinary transporter from T to S sends Q_S bijectively to Q_T. Take r=dim Q_T. The algorithm below applies on input classes where this hypothesis holds and r=O(log L), with L the explicit input length.

In the raw coordinate frame set P_T(A)=Pf(A) for A in Q_T. For a transporter g from T to S let h:Q_T→Q_S be the map characterized by g_U^*(h A)=A. The Pfaffian identity gives

    P_S(h A) = det(g_U)^(-1) P_T(A).

This equality holds as a polynomial law, after substitution over every commutative F-algebra, because the Pfaffian congruence identity is an integral polynomial identity. We give two polynomial-size ways to mark enough values of the polynomial law that a negative transporter cannot preserve the marks. Either construction yields a deterministic objectwise reduction to one ordinary TI comparison. Neither requires a nonsingular form over F.

## Bounded-order Taylor expansions at rational forms

Fix s=O(log L), depending only on the raw dimensions, and suppose at least one Taylor expansion P_T(A+X) at a rational A in Q_T has a nonzero coefficient of total degree at most s. The coordinate variable X ranges over Q_T. Use the algebra of polynomials on Q_T truncated above total degree s,

    R_T = Sym(Q_T*) / (monomials of total degree > s).

This is a unital algebra of dimension binom(r+s,s)≤2^(r+s) over F. Attach its multiplication and its degree-one inclusion. Attach the dual pairing of Q_T and Q_T*, with scalars fixed. A map on Q_T consequently forces the action on R_T to be substitution by the inverse of that map. Every invertible map on Q_T induces such an action. The case s=0 uses just the marked scalar field.

Enumerate the 3^r rational forms A. Use the split coordinate algebra F^(Q_T), with actual multiplication and unit, and its linear map e_A↦A into Q_T. Its primitive idempotents are exactly the coordinate idempotents, so their permutation under a transporter must be the bijection h. Finally mark the linear map

    e_A ↦ P_T(A+X) mod (total degree > s)

from the split coordinate algebra to R_T. Use the actual trilinear evaluation of Q_T on U_T and U_T to ensure that h is the map forced by the tested mode, rather than an independent map.

The marked equality under a transporter is precisely the equality of the displayed Taylor expansions after substitution. The Pfaffian identity says it holds at every A if the tested determinant is +1. If the tested determinant is −1, each expansion is negated. Since at least one is nonzero and F has odd characteristic, the marks reject that transporter. Every positive transporter extends by its uniquely determined action on the algebra generators and idempotents. The nonvanishing condition can itself be checked in polynomial time. It is invariant along ordinary isomorphism because h is invertible and linear.

To compute each truncated expansion, evaluate a division-free Pfaffian algorithm on the alternating matrix A+X over the explicit truncated ring. Its dimension is polynomial, and addition and multiplication can both be performed naively on the coefficient lists in polynomial time. This uses the division-free Pfaffian circuit over arbitrary commutative rings of Mahajan, Subramanya and Vinay. It never divides by the characteristic or by a nilpotent. Thus all marked structure constants and linear maps are built deterministically in polynomial bit time. [Division-free Pfaffian algorithm](https://doi.org/10.1016/j.dam.2003.12.001)

## Full Pfaffians on constant-dimensional rational restrictions

Fix an absolute constant k≥1. Suppose that at least one ordered k-tuple of rational forms A_1,…,A_k has a nonzero polynomial

    P_T(t_1 A_1 + … + t_k A_k) ∈ F[t_1,…,t_k].

It suffices that some rational subspace of dimension at most k has a nonzero symbolic Pfaffian. There need be no rational form of full rank and the vanishing order at every rational point may be arbitrarily large. Enumerate the 3^(kr) ordered tuples. On their split coordinate algebra F^(Q_T^k), include the k linear maps picking out the k entries of each tuple. These force the idempotent permutation to be the coordinatewise action of h.

Mark the coefficient vector of the above polynomial at each idempotent. The color space is fixed pointwise, since the dummy variables t_j describe coefficients in an ordered tuple and do not transform under h. One way to fix the color space with a constant number of marks is to identify its ordered basis with powers of z in F[z]/(z^D), where D=binom(k+n/2,k), and include its multiplication, unit and distinguished z. The degree bound n/2 and chosen tuple order give the same coefficient axes for all raw inputs of the given format. Fixing z makes the action on the whole algebra the identity. For D=1 there is just the scalar unit. Compute all coefficients by running the division-free Pfaffian circuit in the k-variable polynomial algebra truncated above n/2. Each such table is polynomial in n for fixed k, and the tuple count is polynomial in L.

A positive transporter respects every color, and a negative transporter negates every color. As at least one color is nonzero, the resulting comparison accepts precisely the positive transporters, independently of whether the tensor stabilizer has a negative element. The checking and construction bounds are polynomial, and the fixed number of bounded-order tensor components is independent of L.

In both constructions include the original tensor as part of the diagram so every accepted map is an original transporter. All additional components are multiplication, unit or vector marks, mixed linear maps, or evaluations with at most three variable slots and fixed scalar output. The standard fixed-component mixed tensor compiler produces one ordinary TI pair. The construction acts on each input object independently. Shared data such as s, k and coefficient axes depend only on its raw format. If necessary, include an explicit format tag so different raw formats cannot match. [Ordinary tensor-system compiler](https://arxiv.org/html/2306.03135v2#S4)

## Raw examples with growing pencil dimension

Here is a realization of the hypotheses where the dimension of Q_T grows and every form over F is singular. The raw recovery below is the symmetrized quotient construction from the earlier symbolic-pencil note. Given a pencil Q of alternating forms on U, let K be its common kernel in Λ²U. Embed Λ²U in U⊗U by x∧y↦x⊗y−y⊗x. Define T as the bilinear quotient map

    U × U → (U⊗U)/K.

After independent rebasings of the two input spaces, recover the raw K by flattening. Let m map the second input mode into the first. Impose the linear equations that (I⊗m)K project to zero in the symmetric square of the first input. In hidden coordinates the identity solves them. Conversely, for each nonzero x there exists a y independent of x with all Q-pairings on (x,y) zero whenever dim Q≤dim U−2. Such x∧y lies in K, so x m(y)=y m(x) in the symmetric algebra. Since x and y are coprime linear forms, m(x) is a multiple of x. Applying this to every line forces m to be scalar. Thus the solutions form the line of the hidden identification. Every nonzero element of that line recovers the same subspace K in the first mode's exterior square and hence the same annihilator pencil Q. The linear equations and the extraction are covariant under all raw transporters. [Earlier quotient recovery](https://github.com/Dugongue/MathProofs/blob/main/OneSignTensorComparison/SymbolicPencils.md)

Set f(x,y)=xy(x+y)(x−y). A block with alternating form ℓ(x,y,z,...)J_2 has Pfaffian ℓ, where J_2 is the standard two-dimensional alternating form of Pfaffian one. Products of linear forms are therefore the Pfaffian polynomials of block-diagonal pencils with one such block per factor including multiplicity. The linear factors in both examples below span all their coordinate labels, so the displayed polynomial uses a pencil of exactly the asserted dimension.

For the Taylor construction choose label variables x_i,y_i for 1≤i≤h, one label z and the polynomial

    z^M ∏_(i=1)^h f(x_i,y_i),   M=3^h.

The tested dimension is 2M+8h and the pencil dimension is 2h+1, logarithmic in the raw length. Every rational form is singular, since f vanishes at every pair over F. At the point z=1, x_i=1, y_i=0, the first nonzero total Taylor degree is h. Indeed in each factor the unique degree-one term is y_i in the corresponding increment. The coefficient on the product of these h increments is one. An analogous family uses all block factors with doubled multiplicity. It has first nonzero total Taylor degree 2h at the same point.

For the fixed-dimensional restriction construction choose r labels x_1,…,x_r and the polynomial

    f(x_1,x_2)^M ∏_(i=3)^r x_i,   M=3^r.

The tested dimension is 8M+2(r−2), and r is logarithmic in its length. Every rational form is singular. Every Taylor expansion at a rational form vanishes through degree M−1 because f vanishes at that point and its M-th power has order at least M. Nonetheless the restriction to (x_1,x_2,x_3,…,x_r)=(s,t,s,…,s) is a nonzero binary polynomial. This example passes the second construction with k=2 even though logarithmic Taylor truncation cannot read a nonzero coefficient.

The same examples furnish both stabilizer behaviors. In the first family, reflecting x_1 replaces f(x_1,y_1) by its negative. This is realized by exchanging the two blocks indexed by x_1+y_1 and x_1−y_1, and using multiplier −1 similitudes on the three blocks whose coefficients change sign. The block exchange has determinant one because its blocks have even size. The three similitudes together have determinant −1 in the tested mode. The same construction works for the second family since M is odd. Such congruences induce quotient autotopisms by equal maps on the two input modes. If all linear block factors are instead repeated an even number of times, the Pfaffian is a nonzero square. An ordinary autotopism induces an invertible linear label substitution. It cannot negate a nonzero square polynomial over F, since −1 is nonsquare in the rational function field. Hence every stabilizer then has positive tested determinant. This gives rigid tensors whose single-mode reflections are ordinary-isomorphic but fail the positive-sign comparison.

These are informal reductions on stated intrinsic-pencil classes. The polynomial-time jet and restriction data are sufficient conditions. They do not provide a universal extraction of a covariant pencil or a general compiler for one-sign TI.
