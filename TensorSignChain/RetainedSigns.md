# Preserve two designated determinant signs through a tensor-system compiler

Work over F = F_3. Consider two explicit bounded-order mixed tensor systems of the same signature, and designate two of their linear roles a and b. Let d_a and d_b denote the determinant signs of the corresponding maps, using additive bits. There is a deterministic polynomial construction of one ordinary three-tensor pair whose first two physical sign bits realize exactly the set of pairs (d_a,d_b) of simultaneous system transporters. In particular it reduces the two designated determinant-one conditions to one ordinary two-sign instance. No ordinary decision queries are made during construction.

The earlier compiler preserves one designated sign using an explicit layered algebra. We reuse its algebra, modify its dimension tags, and attach a faithful module that reads the second sign. [Prior signed compiler](https://github.com/Dugongue/MathProofs/blob/main/TensorDeterminantIntervals/SignedCompiler.md)

## Keep the first sign in the algebra

Use Sections 1–4 of the earlier compiler with a as the designated role, padding every linear role to odd dimension by a fixed one-dimensional summand when necessary. The padded maps have the original determinants. Include an extra system map that is identically zero, with first role b and second and output roles the fixed scalar field. It imposes no condition on the original system. Its new data vertex M_t in the layered algebra R has a left arrow space

    A = e_O R e_(M_t) = F e_t ⊕ V_b,

where V_b denotes the padded role. This is a first-length arrow corner disjoint from J², where J is the radical of R. The earlier scalar anchors separate these two summands under all normalized algebra isomorphisms. A normalized isomorphism is one carrying each displayed vertex idempotent to its corresponding target idempotent. Freely adding the zero map does not affect the proof of the earlier compiler.

Recall its recovery equations. The common anchor L has multiplier λ. For the map indexed by t, the scalar anchors e_t,f_t have respective multipliers α_t,β_t with α_tβ_t=λ. The map on the common output copy of role b has matrix c_b=λ g_b, where g_b is the corresponding padded system map. Therefore the action on the two parts of A is the block matrix α_t(I⊕g_b). Its determinant has bit d_b because 1+dim V_b is even.

Modify only the local diagonal corner tags. At vertex v the earlier tag was F[τ_v]/(τ_v^(N_v)) with all N_v distinct and congruent to 1 modulo 4. Choose instead each N_v to be 0 or 1 modulo 4 so the dimension of the left projective R e_v is even. Explicitly, its dimension is N_v plus the sum of the incoming off-diagonal corner dimensions, and the two residues of N_v provide both parities. Choose distinct N_v in disjoint intervals of length four indexed by the fixed vertex order. The incoming dimensions depend only on the common signature and padded role sizes. Each genuine algebra transporter still fixes vertices after conjugation by a radical unit, since the diagonal dimensions are distinct. All local corner automorphisms still have determinant one. In fact a tag automorphism with linear coefficient ρ on τ_v has determinant ρ^(N_v(N_v−1)/2), and that exponent is even for both tag residues. All other determinant calculations in the one-sign compiler are independent of N_v. Thus every normalized algebra transporter φ still recovers a simultaneous system transporter and has determinant bit d_a. Conversely every system transporter extends. Conjugation by a radical unit has positive determinant and does not alter this set of signs.

## Read the second sign on a small explicit module

Construct an R-module L supported at vertices O and M_t. Write

    L_O = F ⊕ V_b,     L_(M_t) = F².

Every tagged vertex idempotent acts as its matching projection. Positive powers of the diagonal variables and every off-diagonal corner other than A act by zero. The arrow A sends L_(M_t) to L_O according to

    (c e_t+x)·(p,q) = (cp,xq).

This is an associative module action. The only nonzero arrows in this module act from the second supported vertex to the first and do not compose with themselves. Products of any two radical elements in R are in J², which has zero intersection with A, and the action sends each such product to zero. The vertex idempotent rules behave as the corresponding domain and codomain projections. Nilpotent diagonal tags act by zero. These checks cover all products generating the multiplication.

For a normalized algebra transporter φ, choose the identity on L_(M_t) and choose α_t(I⊕g_b) on L_O. The resulting map g_L between the two displayed modules satisfies

    g_L(r·x) = φ(r)·g_L(x).

For the only participating arrow this is the action formula and the block shape of φ on A. For all other terms it follows from support and from preservation of the named corners. Its determinant bit is d_b. For a nonnormalized φ, first normalize by conjugation by a radical unit. Undo conjugation on L by the action of that same unit, which is unipotent and has determinant one since its difference from one acts nilpotently. Thus the same determinant conclusion holds for every φ.

Use the faithful module M=R⊕L, where the first summand is regular on the left. The determinant of the reference φ-semilinear transporter φ⊕g_L has bit d_a+d_b. There is no other determinant bit from changing the choice of module transporter. To show that, decompose the regular summand into its indecomposable projectives R e_v, each of even dimension by construction. Their endomorphism rings are the opposite diagonal rings, whose residues are F. The module L is the direct sum of two more indecomposables, obtained by taking the p and q coordinates separately. Their total dimensions are 2 and 1+dim V_b, both even. Each has endomorphism ring F because its M_t-space is one-dimensional and multiplication by the arrow generates its entire O-space. Thus its endomorphisms are completely determined by the scalar on M_t.

For clarity, the positive determinant claim now follows from the standard module endomorphism decomposition. For a finite-dimensional module decomposed into indecomposable summands, its endomorphism algebra modulo its Jacobson radical is the product, over distinct isomorphism classes, of the full matrix algebras on multiplicities over the residue division rings of the summands. Here every residue is F. A unit in such a matrix algebra lifts by acting on the multiplicity coordinates of the isomorphic summands. Its determinant on M is its determinant on the multiplicity space raised to the dimension of that indecomposable, which is even. Any two lifts differ by 1 plus a radical element, acting unipotently. Hence every R-linear module automorphism has positive determinant. Every φ-semilinear comparison differs from the reference one by such an automorphism. [Finite-field module endomorphism and algebra algorithms](https://arxiv.org/abs/1708.03495)

Finally, multiplication by a unit of R on L has positive determinant. Modulo J, a unit gives one scalar at each vertex. The only two nonzero vertex spaces of L have even dimension, so the contribution of both scalar powers is positive. The remaining factor is 1 plus a radical element and acts unipotently. Therefore the determinant bit of a unit action on M is identical to that of its regular left action on R.

## Produce the ordinary tensor and the two exact sign readouts

Take the three-tensor written as the bilinear module action

    ρ: R × M → M.

Any transporter has maps s on labels, g on inputs and h on outputs satisfying ρ_S(s(r))g=hρ_T(r). Evaluating at r=1 gives ρ_S(u)=hg^(-1) with u=s(1). This forces u to be a unit because M includes the regular representation and ρ_S(u) is invertible. Therefore h=ρ_S(u)g. Define φ=L_(u^(-1))s on R, where the left multiplication is in the target algebra. The action equation becomes

    ρ_S(φ(r)) = gρ_T(r)g^(-1).

Faithfulness implies φ is a unital algebra isomorphism, and g is φ-semilinear. Conversely any recovered algebra transporter admits a φ-semilinear module transporter as above, and u=1 then yields a tensor transporter. The construction therefore preserves ordinary emptiness as well.

Write ℓ for the determinant bit of multiplication by u on the regular algebra. The three physical bits of the action tensor are

    s-bit = d_a+ℓ,
    g-bit = d_a+d_b,
    h-bit = d_a+d_b+ℓ.

In the customary triple tensor product convention some maps dualize, which leaves their bits unchanged over F. The first desired role bit is s-bit+g-bit+h-bit. The second is s-bit+h-bit. Apply the existing exact linear sign projection from the three physical bits to these two bits and a third zero bit. Every possible projected pair is exactly the pair of some actual simultaneous system transporter, in both directions. This gives the promised single two-sign instance. [Exact sign projections](https://github.com/Dugongue/MathProofs/blob/main/TensorSignProjections/SignProjections.md)

All dimensions are polynomial in the specified input lengths. The added gate has one new data vertex and the usual fixed number of auxiliaries. The adjusted local tag dimensions grow linearly in the number of vertices, and L has the dimension of the padded role plus three. Structure constants, the regular action and the appended action are explicit and polynomial to write. The earlier projection is also polynomial.

## Consequences for the determinant chain

Suppose a polynomially constructible ordinary tensor system contains the original tensor and forces positivity of a specified one of its physical signs. Require the precise extension and recovery property. Every original positive transporter extends and each diagram transporter restricts to such an original map. The recent raw Pfaffian, alternating flag, intrinsic operator and jet locks supply this property on their stated classes.

* With one further live physical sign, the earlier one-sign compiler gives a single one-sign output for the corresponding two-sign comparison. The retained mode can have arbitrary dimension. Its sign is read on the same original transporter that passed the ordinary lock.
* With two further live physical signs, the construction above gives a single two-sign output for the full three-sign comparison on that class. This extends the small diagonal-block and small format results to every class admitting any one of the ordinary locks, with no additional width bound on either retained mode.
* If an ordinary lock controls a product of a prescribed subset of role signs, designate the common direct-sum role for another product sign and include its canonical inclusions and projections. Its determinant is the product. The same applies to two live product characters by adding two such direct-sum roles. Every underlying system transporter extends uniquely on these new roles, and every augmented transporter induces the required sums.

An objectwise lock for one sign would also have stronger consequences if it were universal. Indeed an unrestricted objectwise reduction from two signs to one already implies an ordinary many-one reduction for one sign. Given a one-sign pair x,y, use the earlier objectwise independent-axis packing to make the three two-sign objects corresponding to ordered pairs (x,x), (x,y), (y,x). If x,y are one-sign equivalent, all three objects are two-sign equivalent. Otherwise they are pairwise two-sign inequivalent. Apply the hypothesized two-sign-to-one-sign object map. If the three outputs were all within one ordinary orbit, they could have at most two one-sign orbits, contradicting the negative case. Thus test ordinary equivalence of all three using two ordinary TI pairs and pack their conjunction. This is the three-object form of the earlier capacity argument for three signs to two. The argument does not apply to an arbitrary pair-dependent reduction with unrelated outputs for the occurrences of each input. [Independent axis packing and capacity argument](https://github.com/Dugongue/MathProofs/blob/main/TensorSignProjections/SignProjections.md)

These deductions are informal. The compiler preserves two live signs but does not supply a universal ordinary lock for the third. The resulting collapses are for the stated input families, not unrestricted collapses of the sign tiers.

## Upgrade to three designated signs

The same method preserves three live signs in one three-tensor. Designate roles a,b,c in the bounded-order system. Use the earlier algebra with a as in the preceding proof, and add two identically zero system maps, with respective first input roles b,c and with the fixed scalar second input and output. They produce distinct data vertices with left arrow copies of F⊕V_b and F⊕V_c. On either arrow the normalized algebra map is α(I⊕g_j) for j=b or c. Both padded role dimensions are odd.

Choose the diagonal corner tags so all left and right vertex projectives have even dimension. This is possible because the incoming and outgoing off-diagonal corner dimension sums have the same parity at every vertex of the earlier construction. Here is the count. The two data arrows at a data vertex have even dimensions. That vertex also has two private incoming and two private outgoing scalar arrows. Each private projection vertex has two incident odd-dimensional arrows or length-two corners in the one supported direction and none in the other. At a probe middle vertex the incoming and outgoing dimensions are both odd. Finally, at O and P the even-dimensional data arrows contribute zero modulo two, projection corners occur in pairs of odd dimensions, and the probe count has the same parity as the common corner W. Indeed with r nonscalar roles, the probe count is r+3 and W has r+1 odd-dimensional summands. The other direction is empty at O and P. That verifies equality of incoming and outgoing parities throughout. Set N_v≡0 modulo 4 for an even parity and N_v≡1 modulo 4 for an odd parity, again using distinct positive tags. Adding the tag makes both projective dimensions even. Its algebra automorphisms have positive determinant as before.

Every unit of R acts by positive determinant on the regular representation on either side. The determinant of a left unit on R is the product of its residue at each vertex raised to the dimension of the corresponding right ideal e_vR. For a right unit acting on R use the dimensions of the left ideals Re_v. All these dimensions are even. In either case the factor in 1+J is unipotent. The algebra isomorphism determinant remains d_a, by the sign calculation of the earlier compiler, unaffected by the tag modification or the two zero gates.

Use the left module L_b already constructed from the b-arrow. In the c-arrow O→M_t, use the mirrored right module L_c, with (L_c)_O=F² and (L_c)_(M_t)=F⊕V_c and right multiplication

    (p,q)·(x e_t+v) = (px,qv).

All other off-diagonal corners and all positive diagonal degrees act by zero. For right modules the arrow acts from O to M_t instead of from M_t to O. This gives an associative module by the same direct check using J². Its two direct summands have even dimension and endomorphism ring F. For a normalized algebra transporter, it has a semilinear comparison with determinant d_c, using the identity on its F² space and the corresponding α(I⊕g_c) on its other space. The left module similarly reads d_b. Both unit actions on the readout modules have positive determinant because each supported vertex space has even dimension.

Choose a positive integer t with 2t>dim R, using the same value for the common signature. Let M_b=R^(2t)⊕L_b be a left module and M_c=R^(2t)⊕L_c a right module. The reference semilinear maps have determinant bits d_b and d_c, because the 2t regular copies contribute zero. Every module automorphism has positive determinant, by the argument with even-dimensional indecomposable summands and their residue endomorphism rings. For right regular copies the relevant indecomposable projectives are e_vR, which now also have even dimensions. The left and right unit actions on all these modules have positive determinant by the preceding parity calculations.

Define the single tensor as the bilinear map

    (R⊕M_c) × (R⊕M_b) → R⊕M_b⊕M_c,
    ((r,x),(s,y)) ↦ (rs,r·y,x·s).

We verify the necessary intrinsic decomposition for its ordinary transporters. A vector (0,x) in the first mode gives a contraction of rank at most dim R, since the only possible output is x·s, with s in R. If r≠0, the contraction has rank at least 2t, by restricting its second input to the 2t separate regular copies inside M_b. Left multiplication by a nonzero r is nonzero on each regular copy. Hence the first-mode rank condition of at most dim R picks out exactly M_c. The second-mode rank condition similarly picks out M_b using right multiplication. These ranks are invariant under every ordinary transporter. The output subspaces M_b and M_c are recovered as the separate spans of products with the appropriate low-rank input subspace. For example multiplying the first unit in R by M_b gives all of M_b, and products with that second-mode subspace have no other components. Their sum and each summand are therefore preserved in the indicated order. Quotienting the inputs by M_c and M_b, and the output by their sum, recovers the multiplication tensor of R.

Write a_0,b_0,c_0 for the three induced quotient maps. The ordinary isotopy of associative unital multiplication gives units u=a_0(1), v=b_0(1) and a single unital algebra isomorphism φ with

    a_0(r)=uφ(r),     b_0(s)=φ(s)v,     c_0(z)=uφ(z)v.

For completeness, setting one argument to 1 proves c_0(r)=a_0(r)v=u b_0(r). Since these are invertible linear maps, multiplication by u and by v is invertible, making both units. Cancelling the factors in the original identity proves that u^(-1)a_0=b_0·v^(-1) is multiplicative and unital.

Let p_b and q_b be the input and output restrictions to M_b. The tensor equation on the second low-rank subspace gives q_b(r·y)=a_0(r)·p_b(y). The possible off-diagonal shears of a lift of r have no effect on that product. At r=1 the same identity gives q_b=u·p_b, where the unit acts on its output value, and hence p_b is φ-semilinear. In the other mode the restrictions satisfy q_c(x·s)=p_c(x)·b_0(s), so q_c=p_c·v and p_c is φ-semilinear for the right action. Both module inputs and outputs have the determinant of the corresponding semilinear map, because the units act by positive determinant. There is no determinant from shears between the intrinsic subspaces and their quotients.

The three physical determinant bits of the whole tensor are therefore

    first = d_a+d_c,     second = d_a+d_b,     output = d_a+d_b+d_c.

They determine the three designated bits exactly. For instance the sum of all three is d_a, and adding d_a to each of the first two recovers d_c and d_b respectively. Conversely every simultaneous system transporter extends to a normalized φ, and semilinear module comparisons extend it to this whole tensor by taking u=v=1 and zero shears. Thus the full attainable three-bit profile is preserved through the invertible linear readout. Apply the earlier exact sign projection to put the three bits directly in their designated physical coordinates. The input dimensions and all tables remain polynomial, since 2t can be the smallest positive even integer exceeding dim R. This proof preserves all three determinant constraints on the same original transporter. It applies also to three linear combinations of role signs by first adding the direct-sum roles linked by inclusions and projections.

This three-sign extension proves that ordinary tensor-system compilation itself need not lose any of the three signs over F. An ordinary orientation condition for any one of them can now be implemented as a bounded-order tensor-system mark and the other two survive in one ordinary two-sign instance. A universal ordinary orientation condition is still required to obtain an unrestricted strict downward step in the sign chain.
