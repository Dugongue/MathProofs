# Concrete orbit-family collapses: quadratic polynomial maps and equation spaces

Date: 2026-09-13. Deterministic many-one reductions on PAIRS, over every field. No web search or Lean. These results do not establish unrestricted TI=TI_SL.

## 1. The mutual-reduction theorem

Each of the following decision problems is polynomial-time equivalent to ordinary three-tensor isomorphism (TI):

1. LINEAR equivalence of subspaces of inhomogeneous polynomials of degree at most two: given R,S subset K[z_1,...,z_N]_(<=2), decide whether an invertible linear variable substitution sends R onto S.
2. AFFINE equivalence of those same quadratic polynomial subspaces.
3. Equivalence of quadratic polynomial maps F,G:K^N->K^m under invertible affine changes of input variables and invertible LINEAR changes of output coordinates.
4. The analogous quadratic-map problem with only invertible LINEAR input changes.
5. UNMARKED homogeneous quadratic polynomial-subspace equivalence under GL variable changes.
6. UNMARKED homogeneous quadratic-map equivalence under independent GL input and output changes.

For any fixed d>=2, replacing degree at most two by degree at most d gives the same polynomial-time equivalence. Coefficients refer throughout to FORMAL POLYNOMIALS, not to their value functions on finite fields. For example z^2-z is a nonzero formal polynomial even over F_2.

The theorem has two explicit directions. The upper direction uses the free presentation-window compiler. The hard direction constructs one PAIR of quadratic equation spaces from a TI pair; it is not asserted to be an objectwise canonical encoding of individual tensors. Both directions preserve the field and use no factorization, ideal-membership algorithm, or search for an isomorphism.

## 2. TI to quadratic equation-space equivalence

Let T,S have format a by b by c, with all dimensions positive. Use variables for six square matrices

    P,Pbar of size a; Q,Qbar of size b; R,Rbar of size c,

and one additional square matrix K of size ab. Let R(T,S) be the K-linear span of all scalar entries of the following equations:

    P Pbar-I=0, Pbar P-I=0;
    Q Qbar-I=0, Qbar Q-I=0;
    R Rbar-I=0, Rbar R-I=0;
    K-P tensor Q=0;
    (K tensor R)T-S=0.

Every equation has degree at most TWO. The Kronecker-product entries in the fourth line are products of one P entry and one Q entry. The fifth line is bilinear in K and R. The number of variables is

    N=2(a^2+b^2+c^2)+(ab)^2,

which is polynomial in the original explicit tensor input length. Write bases for the two polynomial spaces

    R(T,S), R(T,T).

If their dimensions differ, return a fixed NO instance, such as span{1} and span{z_1}, of the same ambient variable number on both sides. These spaces are inequivalent under either linear or affine substitution. Otherwise they have the same format and are the actual output pair.

### Completeness uses a linear substitution

Suppose S=(P0 tensor Q0 tensor R0)T. Substitute

    P=P0 P', Pbar=Pbar' P0^(-1),
    Q=Q0 Q', Qbar=Qbar' Q0^(-1),
    R=R0 R', Rbar=Rbar' R0^(-1),
    K=(P0 tensor Q0)K'.

This is an invertible LINEAR substitution in the displayed scalar variables. Matrix inverse equations become invertible linear combinations of the corresponding reference equations. The Kronecker equation becomes

    (P0 tensor Q0)(K'-P' tensor Q'),

and the final equation becomes

    (P0 tensor Q0 tensor R0)((K' tensor R')T-T).

Consequently the complete source relation span is carried EXACTLY onto the reference span. Applying the inverse transporter gives the reverse inclusion. An actual TI isomorphism therefore gives a linear, and hence also an affine, equivalence of the quadratic equation spaces.

### Soundness permits arbitrary affine substitutions

The reference space R(T,T) vanishes at the explicit identity point

    P=Pbar=I_a, Q=Qbar=I_b, R=Rbar=I_c, K=I_(ab).

Suppose an arbitrary invertible affine variable substitution carries R(T,S) onto R(T,T). Evaluate the substitution at this identity point. Every source equation then vanishes at the resulting K-valued point. The inverse equations make P,Q,R invertible; the Kronecker equations give K=P tensor Q; the final equation gives

    (P tensor Q tensor R)T=S.

Thus the original tensors are isomorphic over K itself. This works for EVERY affine equivalence of the output spaces, not only one arising from the displayed transporter substitution. No variable, matrix block, or distinguished identity point is marked in the output instance.

This proves the hard direction for both linear and affine quadratic-space equivalence. It also explains why merely lowering equations to degree two was sufficient here: the new variable K has an explicit linear transporter action, rather than being an unstructured arithmetic-circuit intermediate.

## 3. Quadratic equation-space equivalence to TI

Let F and G be matrices whose columns are bases of the two input polynomial subspaces, in the monomial basis of K[z]_(<=d). First compare their dimensions and their ambient variable dimensions; mismatches give a fixed NO output.

Let g be an invertible affine transformation of the variable space, represented by an affine matrix M of size N+1 together with its inverse Mbar. Both have fixed last row (0,...,0,1); their free coordinates satisfy M Mbar=Mbar M=I. For the linear version use ordinary N by N matrices and omit translations.

Let rho(g) act on polynomials by substitution f(z)->f(g^(-1)z), and introduce an invertible matrix H, with inverse Hbar, acting on the relation bases. The transporter equations are the scalar coefficient equations

    rho(g) F=G H,
    M Mbar=Mbar M=I,
    H Hbar=Hbar H=I.

The first equations have degree at most d in the affine inverse-matrix entries and degree one in H. The other equations are quadratic. Their K points are exactly affine variable equivalences of the input polynomial spaces, with the induced basis change recorded by H.

If (g0,H0) is an actual transporter, set g=g0 h and H=H0 J. Composition with g0 acts affine linearly on the free affine-matrix coordinates and on their inverse coordinates; the basis-matrix variables transform linearly. Since G H0=rho(g0)F, the polynomial coefficient equation becomes

    rho(g0)(rho(h)F-F J).

The coefficient matrix rho(g0) is invertible. The matrix-inverse equations also become invertible constant linear combinations of the reference equations. Thus their initial relation span is carried exactly onto its reference span by an affine linear coordinate change.

Apply TI_GI_FILTERED_TRANSFER_20260913.md: write the FREE polynomial spaces P_0,...,P_e in these transporter coordinates, where e=max(d,2), together with unit, inclusions, partial products, and the inclusion of the initial relation span into P_e. The proof there gives both directions by translation and reference identity evaluation. For fixed d these spaces and all their maps have polynomial dimension. The established tensor-system packing writes one ordinary-TI pair.

This is a constructive many-one upper reduction, not a Turing reduction or a request to solve polynomial equations. No true coordinate ring or Groebner basis is computed.

## 4. Polynomial maps give the same family

For a polynomial map F=(f_1,...,f_m), its coordinate span is R_F=span_K{f_1,...,f_m}. If the output coordinate polynomials are independent, an invertible input substitution carries R_F onto R_G exactly when there is an invertible linear change of the m output coordinates relating the maps.

The same equivalence holds with dependent output coordinates, provided the common output dimension m and the coordinate-span ranks agree. Any isomorphism between the two coordinate spans extends to an invertible transformation of the two m-dimensional coefficient spaces by choosing and matching bases of their kernels and complements. These bases are obtained by ordinary linear algebra. A rank mismatch is a NO case.

Thus arbitrary quadratic-map instances reduce to quadratic-space instances by taking coordinate spans. Conversely a basis of any quadratic space is an explicitly written quadratic map. These reductions work for both linear and affine input changes and preserve the stated output-linear restriction.

Combining Sections 2 and 3 proves all four mutual reductions in Section 1. Because the degree-d family contains the quadratic family, the same argument proves TI-completeness for each fixed d>=2.

## 5. A concrete degree-one / degree-two boundary

For degree-at-most-one maps with affine input and linear output changes, there is a complete elementary polynomial-time classification. Write F(x)=A x+b. With input and output dimensions fixed, its equivalence class is determined exactly by

    rank A, and whether b belongs to image A.

Affine input translation changes b by an element of image A. Independent invertible linear input and output maps put A into its standard rank form. The remaining output transformations act transitively on nonzero vectors in the quotient K^m/image A. These observations prove both necessity and sufficiency of the displayed data, over every field, and provide an algorithm using Gaussian elimination.

Thus degree-one affine-input/linear-output polynomial-map equivalence is in deterministic P, whereas degree two is TI-complete. This is an unconditional classification of two families and their reductions. It is not an unconditional proof that the families have different polynomial-time complexity; that further assertion would require TI not in P.

## 6. Complexity, packing dependency, and exact scope

All lower-reduction coefficients are original tensor coefficients, their negatives, 0 or 1. Writing monomial coefficient arrays and selecting bases of the relation spans has polynomial bit complexity over Q and represented finite fields. The upper reduction has fixed defining degree, so the free polynomial-window construction likewise has polynomial bit complexity. No field-element enumeration occurs.

The lower reduction outputs ordinary polynomial spaces or maps without marked matrices, a fixed point, or a preserved variable decomposition. It is pair dependent. The upper reduction ends with the existing explicit finite-tensor-system packing from the filtered-transfer notes; that established construction is the sole final encoding dependency.

Sections 2--4 concern inhomogeneous maps with linear output changes. Section 8 supplies a separate explicit proof for unmarked homogeneous quadratic maps. Maps with unrestricted affine output changes are not silently identified with either family. The theorem does not infer an unrestricted SL-TI reduction, a GI-versus-TI separation, or an algorithm for TI.

## 7. Exact executed checks

The script ti_gi_quadratic_map_checks_20260913.py and receipt TI_GI_QUADRATIC_MAP_CHECKS_20260913.json validate the lower reduction for eighteen dense transporter cases of tensor format (2,2,2), over F_2,F_3,F_5. Each instance has forty polynomial variables and forty-eight displayed equations. Exact sparse formal-polynomial substitution and modular row ranks verify all eighteen source/reference relation-span equalities. Identity evaluation annihilates all 864 tested reference equations and recovers the eighteen original P,Q,R matrices and their Kronecker products.

These are tests of formal polynomial coefficients, so no substitution of polynomial functions on a finite field hides a nonzero polynomial relation. The checks do not search over arbitrary affine equivalences and do not execute the upper reduction's final tensor packing.


## 8. An explicit unmarked homogenization: homogeneous quadratic families are TI-complete

The hard direction strengthens to HOMOGENEOUS quadratic spaces with no marked hyperplane, variable, or decomposition. The following elementary anchoring construction supplies the missing recovery proof.

### 8a. The displayed TI relation spaces contain no lower-degree polynomial

For nonzero T, each space R(T,S) in Section 2 satisfies

    R(T,S) intersect K[z]_(<=1) = 0.

To see this, separate the homogeneous quadratic supports of the equation families. The three inverse-matrix families involve their own matrix/inverse variables. Any linear combination of their quadratic parts that is identically zero also has zero constant part: substitute both matrices equal to the identity. The equations K-P tensor Q have pairwise distinct P-entry times Q-entry monomials, so no nonzero combination of their quadratic parts vanishes. The final equations use K-entry times R-entry monomials, disjoint from every other quadratic support.

Their quadratic coefficient map is injective. Choose a nonzero coefficient T_(j,l). The monomial K_(i,j) R_(k,l) in a linear combination of output equations has coefficient T_(j,l) times that combination's coefficient at output (i,k). Thus all its output coefficients vanish if its quadratic part is zero. These observations show that any cancellation of all degree-two terms is the zero polynomial, proving the claim.

The case T=0 is settled directly before this construction: S=0 gives YES and S!=0 gives NO. Fixed homogeneous-quadratic NO instances of identical format are span{x^2} and span{xy} in two variables; their generators have different linear-factor multiplicities over every field. A fixed YES pair uses two copies of either one.

### 8b. Anchor the homogenizing variable by an intrinsic dimension property

Let R subset K[x_1,...,x_N]_(<=2) have dimension r and R intersect K[x]_(<=1)=0. Homogenize it using a new variable z_0, obtaining

    Rtilde={z_0^2 f(x/z_0): f in R}

inside the homogeneous quadratic polynomials on span{z_0,x_1,...,x_N}. Choose D=r+2 additional variables y_1,...,y_D, and define the UNMARKED homogeneous quadratic space

    H(R)=Rtilde + span{z_0 y_1,...,z_0 y_D}.

This is a direct sum. Let L be the full linear-form space, and Y=span{y_1,...,y_D}. The line K z_0 is intrinsically the UNIQUE linear-factor line K ell satisfying

    dim(H(R) intersect ell L)>r+1.

Indeed, for ell=z_0 this intersection is exactly z_0 Y and has dimension D=r+2. The absence of lower-degree polynomials in R means that no nonzero Rtilde element is divisible by z_0.

If ell is not proportional to z_0, the intersection ell L intersect z_0 Y has dimension at most one: a quadratic divisible by both distinct linear forms is a scalar multiple of ell z_0. Projecting H(R) intersect ell L to H(R)/(z_0 Y), whose dimension is r, bounds its dimension by r+1. This proves uniqueness. The argument uses only unique factorization of formal polynomials and holds in every characteristic.

After this line is recovered, the whole auxiliary space is intrinsically recovered as

    Y={v in L: z_0 v belongs to H(R)}.

Scaling the chosen generator z_0 does not change this space. Again the claim Rtilde intersect z_0 L=0 proves the equality.

### 8c. Both directions, including arbitrary unmarked isomorphisms

An affine substitution carrying R onto S homogenizes to an invertible linear substitution fixing z_0. Extend it by any invertible map of Y onto the target auxiliary space. It carries H(R) onto H(S), proving completeness.

Conversely suppose ANY invertible linear variable substitution carries H(R) onto H(S). Their dimensions determine the same r in the paired construction. The intrinsic characterization above forces it to carry K z_0 onto the target K z_0 and Y onto the target Y. Quotient the linear-form space by Y. The induced invertible linear map carries the image Rtilde onto Stilde and preserves the z_0 line. On the affine chart z_0=1 it is therefore an invertible affine change of the original x variables. If z_0 scales by alpha, the homogeneous quadratic substitution introduces the same nonzero scalar alpha^2 on the relation space, which does not alter that subspace. Hence it carries R onto S.

Thus

    H(R) is GL-equivalent to H(S) iff R is affine-equivalent to S.

Applying this explicit construction to the two TI relation spaces, after checking their equal dimensions, proves TI-hardness of UNMARKED homogeneous quadratic-space equivalence. The number of added variables is only r+3. The upper reduction is Section 3 with linear input variables and homogeneous degree-two coefficient equations. Taking polynomial-space bases as map coordinates proves the same TI-completeness for unmarked homogeneous quadratic maps under GL input and GL output changes.

No factorization algorithm or intrinsic-line search is run by the reduction. The line characterization proves recovery from ANY isomorphism of the actual output spaces. Every output coefficient is explicitly computed by homogenization and the displayed D monomials.

## 9. Exact homogeneous-anchor checks

The same validation script checks that the degree-two parts of each nonzero-T relation space in the eighteen transporter cases have the SAME row rank as the full polynomial space. Thus no nonzero degree-at-most-one remainder occurs in those tests.

The additional receipt TI_GI_HOMOGENEOUS_ANCHOR_CHECKS_20260913.json exhausts all 4333 projective linear-factor lines over F_2,F_3,F_5 in a six-dimensional small anchoring example, after unrelated dense changes of ambient basis. In all three fields, precisely the expected homogenizing line has an intersection of dimension three with the quadratic space; every other line has intersection dimension at most one. The recovered auxiliary colon space is also checked. These bounded tests exercise the intrinsic, unmarked characterization; they are not a replacement for its universal dimension proof.
