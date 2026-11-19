# Large projective orbits on split matrix multiplication

Let K be any finite extension of the field with three elements, write Q for its cardinality, and let m ≥ 2 be even. Consider the balanced three-tensor T(X,Y)=XY on M_m(K). It is concise because evaluation at the identity in either input slot yields the identity map on the other input and all outputs are obtained this way.

**Theorem.** The centroid of T consists of common scalars. Its stabilizer over the field with three elements has trivial determinant image. Nevertheless each nonempty invariant set of projective covector lines in any one mode has cardinality at least ((Q^m−1)/(Q−1))² over K. In particular moving to a safe extension cannot produce the two polynomial-size projective lists for this family. The SL-TI comparison on pairs promised to lie in this ordinary isotopy class has an elementary Las Vegas polynomial-time algorithm over the base field.

## The stabilizer and its projective orbits

Each triple of invertible m-square matrices a,b,c gives an autotopism with mode maps

    X ↦ aXb⁻¹,    Y ↦ bYc⁻¹,    Z ↦ aZc⁻¹.

On each individual mode these give the full left-right matrix action. For covectors, identify the dual with matrices by the trace pairing. The induced contragredient again gives the full left-right action. Its projective orbits are the nonzero matrix rank strata, since elementary row and column operations put any matrix in rank normal form.

For a rank-r stratum the exact number of lines is

    [m choose r]_Q² · |GL_r(K)|/(Q−1).

Indeed choose the r-dimensional row and column spaces, and then the invertible r by r coefficient matrix in fixed bases for these spaces, modulo a common scalar. For r=1 the formula is exactly the asserted lower bound. For 1≤r<m use the symmetry of the Gaussian binomial coefficients and the consecutive ratio (Q^(m−r)−1)/(Q^(r+1)−1) to see that [m choose r]_Q is at least [m choose 1]_Q. Also |GL_r(K)| ≥ Q−1. For r=m the first two independent columns already give at least (Q^m−1)(Q^m−Q) invertible matrices, because each such pair extends to a basis. Since Q≥3 and m≥2, Q^m−Q ≥ (Q^m−1)/(Q−1). These inequalities prove the bound for every rank. Over the base field the list has size exponential in m, while the explicit input length for the ordinary tensor is polynomial in m.

The centroid condition reads A(X)Y=X B(Y)=C(XY). Substituting X=I, Y=I shows that these three maps are respectively left and right multiplication by a common central element and its identical action on the output. The center of the full matrix algebra is K, which gives the claim.

For the determinant image let F,G,H be any autotopism, satisfying F(X)G(Y)=H(XY). Write a=F(I), b=G(I). Then H(X)=F(X)b=aG(X). Invertibility of H,F,G implies that a,b are units. Substitution shows that α(X)=a⁻¹H(X)b⁻¹ is a unital algebra automorphism. Every automorphism of a full matrix algebra is conjugation. For the direct proof, the images of the standard matrix units obey the same matrix unit relations. Their diagonal idempotents are nonzero and sum to I, so each has rank one. Taking a nonzero vector in the first diagonal image and applying the column of image matrix units gives a basis in which all the images are the original matrix units. Thus F(X)=aα(X), G(X)=α(X)b and H(X)=aα(X)b, and these have determinant tuple

    ((det a)^m, (det b)^m, (det a det b)^m).

For even m all determinants are squares. Over the base field this tuple is always (1,1,1). In particular a reflection in a single mode produces a pair which is ordinary-isomorphic but not SL-isomorphic. Finite projective lists fail on a family where the determinant condition can change the answer.

## A raw-array algorithm via one minimal left ideal

Suppose a displayed tensor S is promised ordinary-isomorphic to T over the field with three elements. Write it as a bilinear map U×V→W. Select u₀ and v₀ for which L(u)=S(u₀,u) and R(v)=S(v,v₀) are both invertible, as checked by linear algebra. In hidden matrix coordinates either test succeeds exactly when the sampled matrix is invertible. A uniform draw succeeds with probability ∏_{j=1}^m (1−3^(−j)) ≥ 1/2, by the geometric series bound on the sum of the failure terms.

Define a product on W by x*y=S(R⁻¹x,L⁻¹y). It is a split associative unital matrix algebra given by explicit structure constants. In hidden coordinates the product is x(u₀v₀)⁻¹y, with u₀,v₀ now denoting their hidden matrices, so its identity is the displayed S(u₀,v₀). The transformations R,L identify the original tensor with multiplication in this new algebra A.

Sample a uniform a in A and compute the kernel dimensions of left multiplication L_a and L_a². Keep it if both dimensions are m. On M_m, left multiplication repeats the action of a separately on every matrix column. The test therefore asks for a one-dimensional kernel of a and for that kernel to have no length-two generalized zero vector. Such a matrix has a simple zero eigenvalue, as its kernel line splits off from its image and its restriction to that image is invertible. To count the event, choose the kernel line, a complementary hyperplane, and an invertible map on the latter. The probability over a finite field with Q elements is

    ((1−Q^(−m))/(Q−1)) · ∏_{j=1}^{m−1}(1−Q^(−j)),

which is at least 1/6 at Q=3.

Compute the minimal polynomial of a by linear dependence of its powers in A. It has the form t b(t) with b(0) nonzero. The element e=b(a)/b(0) is the rank-one projector onto the zero eigenspace in hidden matrix coordinates. The left ideal Ae has dimension m. Its left regular action gives an injective algebra map A→End(Ae), since a matrix acting by zero on every possible column is zero. Equal dimensions make it an isomorphism. Compute the map in any linear basis of Ae to obtain an explicit normalization to the standard multiplication tensor. This algorithm uses no promise about the positions of any prescribed projective lines.

Normalize both promised inputs and compose the resulting ordinary transporters to get a transporter between them. All transporters have the same determinant tuple because the source stabilizer image is trivial. Comparing the tuple with (1,1,1) decides SL-TI. All random searches are verified and have bounded expected trial counts. Thus the failure of the lists does not require searching through their members on this family.

These are informal deductions. The use of a minimal left ideal to split a known full matrix algebra is standard. The proof above gives a direct sampling bound and a complete exact orientation test for the stated promise. [Related explicit isomorphism work](https://arxiv.org/abs/1508.07755)


## Scalar pair adjoints with large projective orbits

A different family rules out a repair based solely on scalar pair adjoints. Let k≥2, let V=K^(3k) with a fixed volume form, and put E=Λ^k V. The coefficient trilinear form

    T(x,y,z) = vol(x∧y∧z),    x,y,z ∈ E,

has balanced mode size N=binom(3k,k). Identifying trilinear forms with dense tensors gives the ordinary three-mode problem, with dual basis-change maps. This distinction inverts the determinants, which does not affect their signs over the base field. The tensor is concise since each exterior basis vector has a pair of disjoint complementary k-subsets whose wedge tests its coefficient.

A pair adjoint is a pair of linear maps A,B satisfying T(Ax,y,z)=T(x,By,z) for every x,y,z. Perfect wedge pairing between degrees 2k and k says equivalently (Ax)∧y=x∧(By). If I'≠I are k-subsets and j belongs to I but not I', choose a k-subset J disjoint from I' and avoiding j. The coefficient at I'∪J in (A e_I)∧e_J is the (I',I) entry of A up to sign. In e_I∧(B e_J) it is zero because every nonzero term includes j. Thus A is diagonal, and by interchanging sides B is diagonal too. The diagonal entries for I,J must agree whenever they are disjoint. Any two k-subsets I,I' have a common disjoint k-subset since their union has size at most 2k, so all entries are one common scalar. By exchanging roles of the three coordinates this holds for every pair adjoint, over every extension. The centroid is scalar as well.

For any nonzero vector in any mode choose a nonzero exterior coefficient on k chosen coordinate vectors spanning a subspace A₀. Let B₀ be the complementary coordinate space of dimension 2k. Use the determinant-one shears that add independent vectors of B₀ to the chosen k vectors and fix B₀. Their exterior actions simultaneously preserve T because the action on volume has determinant one. In an orbit of a vector, its original coefficient on Λ^k A₀ is fixed and nonzero. Each coefficient of A₀-degree k−1 and B₀-degree 1 records the original such coefficient plus the top coefficient times one of the 2k² shear entries, up to sign. No lower A₀-degree term can contribute. Consequently the projective lines obtained for the Q^(2k²) shears are distinct. For dual vectors take dual exterior bases and the contragredient actions. The map g↦g^(−t) permutes all determinant-one matrices, which gives the same conclusion. Any nonempty invariant projective list has at least Q^(2k²) points. As N=binom(3k,k)=exp(Θ(k)), this is superpolynomial in the explicit base-field tensor size and only increases in extensions.

For k=3·2^s with s≥0, the entire stabilizer has trivial determinant image over the field with three elements. The following argument computes it using the projective automorphisms of a Grassmannian.

A nonzero x in E gives the wedge map y↦x∧y, whose rank equals the rank of its slice in T by perfect wedge pairing. Its minimum is binom(2k,k), and it attains that minimum exactly at the decomposable x. To see this, choose A₀,B₀ from a nonzero exterior coefficient as above. The restriction to Λ^k B₀ is injective because projection of its image to A₀-degree k is multiplication by the nonzero top coefficient. The rank for decomposable x is exactly the stated minimum after a change of basis. For the converse, apply a determinant-one shear to eliminate all A₀-degree k−1 coefficients. This is possible by the independent-entries calculation just given. If x is not decomposable, it still has some nonzero coefficient on I'∪J of B₀-degree r≥2, with I' in A₀ and J in B₀. Choose one unused basis index a in A₀ outside I', and a (k−1)-subset L of B₀ disjoint from J. Wedge x with the basis wedge indexed by {a}∪L. The result is nonzero because its coefficient at I'∪{a}∪J∪L is precisely the chosen nonzero term up to sign. It has zero A₀-degree k projection. The pure top-degree term of x vanishes when wedged with a vector having index a, and the next-degree terms were eliminated. Hence the new image vector lies outside the already found injective image of Λ^k B₀, proving the strict inequality.

An autotopism therefore preserves the decomposable locus in each mode, since it preserves slice ranks. This proof holds after scalar extension, including over an algebraic closure. By Chow's Grassmannian theorem, the linear preserver in mode i is a nonzero scalar times Λ^k(g_i) for some invertible g_i on V. The dual Grassmannian automorphism case occurs only in ambient dimension 2k, whereas our ambient dimension is 3k. Over a finite base field the g_i may be chosen rational over that field. The representation of PGL(V) on the Grassmannian is faithful, since a linear map fixing every k-subspace fixes every line by intersection and must be scalar. The projective class of g_i is therefore fixed by Frobenius. Normalize any nonzero entry of a representing matrix to 1 to get a Frobenius-fixed representative, and then compare one nonzero entry of the original exterior action to recover the scalar over the same field. [Chow, On the Geometry of Algebraic Homogeneous Spaces](https://doi.org/10.2307/1969351) · [Ghorpade and Kaipa, Automorphism groups of Grassmann codes](https://arxiv.org/abs/1204.5547)

The g_i are the same projectively. For two decomposable wedges, their product is zero precisely when the corresponding k-planes meet nontrivially. An autotopism preserves that relation because its third mode map is surjective. If a k-plane Y differed from g_i^(−1)g_j Y, one could choose a line in Y outside g_i^(−1)g_j Y and extend it to a k-plane X disjoint from g_i^(−1)g_j Y. Then X meets Y but its image under g_i is disjoint from the image of Y under g_j, a contradiction. Thus g_i^(−1)g_j fixes every k-plane and is scalar.

The determinant of Λ^k(g_i) is (det g_i)^binom(3k−1,k−1), as one sees on diagonal matrices and then on triangular matrices over the algebraic closure. The additional scalar in mode i contributes its N-th power. Both exponents are even for k=3·2^s. Indeed the binary digits of k are not a subset of the digits of 3k=9·2^s, and the digits of k−1 are not a subset of the digits of 3k−1. This parity rule follows by expanding (1+t)^a over the field with two elements as the product of (1+t^(2^j)) at the nonzero binary digits of a. Thus every stabilizer sign is positive at the base field. A reflection in one mode changes the ordinary-orbit pair into an SL-no instance while preserving all the structural properties just proved. This supplies a sign-sensitive obstruction even when every pair adjoint and the centroid are scalar.
