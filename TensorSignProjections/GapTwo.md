# A two-sign reduction from Koszul determinants on a small intrinsic quotient

**Informal theorem.** Over F_3, consider a dense three-tensor comparison with two tested modes of the same even dimension n and an arbitrary third mode. There is a deterministic, raw-input sufficient condition for reduction to **one** one-sign instance. The condition below admits unbounded dimensions in all three modes, including families where the projected determinant image of the pair adjoint units is zero. The construction uses rank, linear equations and determinants, and requires no decision oracle or supplied transporter.

## The raw computation

Use the pencil form M(z):X → Y, with n = dim X = dim Y even and label space Z. In these conventions each transporter acts by invertible (a,b,c) on (X,Y,Z) with

    M_S(cz) = b M_T(z) a^(-1).

The two tested signs are det(a), det(b). Switching a tensor mode to its dual has no effect on its sign over F_3.

Compute the fixed-label endomorphism algebra

    E_M = { (P,Q) in End(X) × End(Y) : Q M(z) = M(z) P for all z }

by linear equations. If dim E_M ≤ C log L for the fixed chosen constant C and written input length L, enumerate its square-zero elements. Set

    X_1 = span { image P : (P,Q) in E_M, (P,Q)^2 = 0 },
    Y_1 = span { image Q : (P,Q) in E_M, (P,Q)^2 = 0 }.

These subspaces transport under a,b because (P,Q) transports by conjugation. Every M(z) sends X_1 into Y_1. Require dim X_1 = dim Y_1. Let Z_0 be the common kernel of the two linear maps taking z to the restrictions X_1 → Y_1 and to the induced quotient maps X/X_1 → Y/Y_1. It is therefore intrinsic under c. Compute these maps using adapted bases and linear algebra, without selecting a basis as additional structure on the pair. Write Z_bar = Z/Z_0 and require dim Z_bar ≤ C log L. Do not require the same bound on the dimension of Z.

For every three-dimensional subspace D of Z_bar, choose an ordered basis and arbitrary lifts z_1,z_2,z_3 in Z. Let H be the coordinate space F_3^3, with basis e_1,e_2,e_3, and define

    K_D(M): H ⊗ X → Λ² H ⊗ Y,
    h ⊗ x ↦ sum_i (e_i ∧ h) ⊗ M(z_i)x.

This is a square 3n by 3n matrix. Compute its determinant in fixed ordered exterior bases and the original X,Y bases. Count the numbers h_plus(M), h_minus(M) of D with determinant +1 and -1, respectively. Zero determinants do not contribute. Require h_plus(M) ≠ h_minus(M).

## Exact invariance

Changing the lifts of z_i changes M(z_i) only by off-diagonal blocks in the common two-step flags. In bases adapted to X_1,Y_1, K_D(M) is block upper triangular after regrouping tensor-product basis elements, with square diagonal blocks because dim X_1 = dim Y_1. The determinant is unchanged by any such change of off-diagonal blocks. Basis conversion contributes the same constant before and after changing the lifts.

Changing the ordered basis of D replaces the triple of slices by its invertible linear recombination. If the matrix of this recombination on the list has the appropriate transpose H-action u, then the new Koszul map is (Λ²u ⊗ I_Y) K_D(M) (u^(-1) ⊗ I_X). Its determinant factor is det(u)^(2n−n) = 1 because n is even. This proves that the sign of the determinant is well defined for D without orientations of its label basis or any compatibility of lifted labels.

For a true transporter (a,b,c) from T to S, c induces a bijection of the three-dimensional quotient subspaces. Choose lifts on the target that are c-images of lifts on the source. Then

    K_{c(D)}(M_S) = (I ⊗ b) K_D(M_T) (I ⊗ a^(-1)),

so each determinant is multiplied by det(b)^3 det(a)^(-3) = det(a)det(b). In particular a positive product preserves the ordered histogram, while a negative product swaps it.

## The single-instance reduction

Run the sufficient-condition test on the source. On this source promise, any ordinarily isomorphic target has matching intrinsic dimensions and also satisfies its sufficient-condition test. A mismatch or failure on the target therefore gives a fixed negative one-sign instance. When both tests pass, if the ordered histograms differ, output a fixed negative instance because a two-sign witness must preserve them. If the histograms agree, return the original pair with only det(a) constrained. Every actual transporter for that pair has positive product because the histogram is asymmetric, and hence det(a)=1 implies det(b)=1 on that very same transporter. A two-sign witness automatically satisfies the remaining sign. This proves the many-one claim.

The work is polynomial in L, 3^(dim E_T), 3^(dim E_S), 3^(3 dim Z_bar,T), and 3^(3 dim Z_bar,S). To enumerate each set of three-dimensional subspaces once, enumerate independent ordered triples, take their row-reduced echelon representatives, and deduplicate. Each determinant is computed by Gaussian elimination. Thus the check and construction have deterministic polynomial cost for the fixed logarithmic bounds, with no restriction on the two tested dimensions or the unprojected label dimension.

## An explicit growing all-even example with no adjoint sign corrections

Let m ≥ 4 be even. On F_3^m, take a cyclic shift Zs and a diagonal matrix Ys whose entries are alternately 0 and 1 until the last entry, which is 2. Consecutive colors around the whole cycle differ, and the single 2 makes the string aperiodic. On X = Y = F_3^m ⊕ F_3^m, use as slices the duplicated diagonals

    diag(I,I), diag(Ys,Ys), diag(Zs,Zs),

and any positive odd number r ≤ m² of independent upper-right slices [0 D_j;0 0], for example distinct standard matrix units as D_j. The format is (2m,2m,3+r), which is all even. Taking r = m²−1 makes all three dimensions grow. The tensor is concise because the identity slice is present and the listed slices are independent.

Its algebra E_M has both components equal, since the identity is a slice. A matrix commuting with Ys and Zs is scalar: a matrix commuting with the cycle is circulant, and a nonzero coefficient at a displacement of a color-preserving shift is required by commuting with Ys. Aperiodicity permits only displacement zero. Consequently commuting with the duplicated diagonal slices forces all four m by m blocks to be scalar. Commuting also with any nonzero upper-right slice forces the lower-left scalar to vanish and the diagonal scalars to agree. Thus E_M is the two-dimensional algebra of matrices [a I b I;0 a I]. Its square-zero elements have a = 0. The computed X_1,Y_1 are both the first m-block, and Z_0 is exactly the span of the upper-right slices. Therefore dim Z_bar = 3.

The unique three-subspace D of Z_bar has positive Koszul determinant. Indeed the map is the direct sum, up to the same regrouping permutation in domain and codomain, of two copies of the Koszul map on (I,Ys,Zs). In the latter map, elimination using the identity slice identifies its kernel with the kernel of Ys Zs − Zs Ys. This commutator is a weighted permutation of the cyclic shift with a nonzero difference of successive colors in every position. Hence it is invertible and the duplicated determinant is a nonzero square. The ordered histogram is (1,0).

None of the paired adjoint units has a nonzero projected two-sign image. For the fixed-label pair, its units have determinant a^(2m) = 1. For either of the other pairs, one tested mode is fixed, so the histogram identity forces the sign of the other tested mode to be positive. In fact the projected image of the **full** stabilizer is zero for this particular example. All stabilizers conjugate the one-dimensional radical of E_M to itself, so each tested physical map is block upper triangular with diagonal blocks P,Q satisfying P = λQ with λ ∈ F_3*. Its determinant is λ^m det(Q)^2 = 1 because m is even. Reorienting both tested modes on the target by reflections yields an ordinarily isomorphic pair whose histogram agrees but whose two signs are both negative. The second stage of the reduction is therefore necessary on that raw pair.

The example demonstrates the sufficient condition with no bound on any raw mode and no preexisting adjoint sign correction. It does not assert that every previously known approach fails on this particular example.

## Scope and source

The exterior Koszul map and its determinant covariance are standard. The project already used its full determinant when the entire label space had a suitable odd dimension. The present argument passes to a raw invariant quotient obtained from two-step endomorphism flags, and combines the determinants through an unordered histogram, so it does not require choosing a distinguished three-dimensional subspace of either raw label space. The condition does not cover arbitrary tensors, since the quotient may be large or have a symmetric histogram. No unrestricted tier collapse or novelty priority is claimed.

For primary background on exterior flattenings, see Landsberg’s [lecture notes on tensors](https://people.tamu.edu/~jml/simonsclass.pdf). The determinant computation and reduction above are fully given here.

## Variant with an arbitrary-size endomorphism algebra

The same reduction works with no dimension bound on E_M if its paired radical flags have matching layer dimensions and the resulting label quotient is logarithmic. Embed E_M block diagonally in End(X ⊕ Y). Compute its Jacobson radical J by the finite-field algebra algorithm stated in [Ivanyos and Qiao, Theorem 18](https://arxiv.org/html/1708.03495#Thmtheorem18). Their deterministic bound is polynomial in the ambient matrix size, log(q), and the characteristic. Both field parameters are constant here.

Replace the two-step flags by X_i = J^i X and Y_i = J^i Y, with X_0 = X and Y_0 = Y. Here each action is via the corresponding projection of E_M. A basis of J suffices to compute each next term by spanning the images of the current term. Nilpotence and strict dimension descent until the flag becomes zero bound the number of steps by the ambient dimension. Conjugation of E_M transports J and both module flags. The relation Q M(z) = M(z) P makes every slice preserve the flags and induce a map X_i/X_(i+1) → Y_i/Y_(i+1). Require these dimensions to match at every grade, and take Z_0 to be the joint kernel of the label maps on every successive quotient.

In adapted bases each three-slice Koszul matrix is block triangular by grade, with square blocks on the diagonal. Hence its determinant is independent of the lifts just as in the two-step proof. The label basis change still acts with determinant factor det(u)^n, and a transporter still contributes det(b)^3 det(a)^(-3) on the original coordinates. The same asymmetric histogram test and one-sign output therefore work. Preprocessing is polynomial, with only the histogram enumeration costing a factor polynomial in 3^(3 dim Z_bar). The two-dimensional algebra in the example has J = F_3 N for N = [0 I;0 0], so the radical flags give precisely the same label quotient there.

The calculation also gives an ordinary-TI reduction if the source has an explicitly found projected stabilizer line generated by the two-negative bit vector. In that case, once the ordered histograms agree, the two possible bit vectors for a transporter are zero and the two-negative vector. Composing with a source stabilizer of the latter type always corrects both signs together. When the line comes only from an unproved stabilizer guess, this last conclusion does not apply.

Finite controls checked the determinant formula on the displayed two-step family for m = 4, 6, 8, 10, and 12. Arbitrary upper-right perturbations of the three chosen lifts, one reflection, and two reflections gave the predicted positive, negative, and positive signs respectively. These checks complement the proof, without placing a bound on m.
