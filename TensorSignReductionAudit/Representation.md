# Determinant representations: reuse audit and exact boundary

Status: informal research audit. This branch does not prove the unrestricted polynomial-time many-one reduction from two determinant signs to one. It also does not establish a new mathematical discovery: the strongest complete construction recovered here was already in the project’s September 8 determinant-gadget work.

## Exact balanced exterior lock

Let F be any field, let U = F^n with its coordinate volume epsilon, and choose nonnegative a, b, c with a + b + c = n and r = max(a,b,c) = ceil(n/3). Small n can be handled directly. Form the truncated exterior algebra

E = direct_sum_(j=0)^r exterior^j U,

with the usual wedge multiplication when degrees sum to at most r, and zero otherwise. Include its multiplication tensor, unit, and degree-one inclusion i:U -> E. Also include the trilinear form

v(x,y,z) = epsilon(x_a wedge y_b wedge z_c),

where x_a, y_b, z_c are the indicated homogeneous components. This is one ordinary order-three tensor; its scalar output is the coefficient field, not another freely rescaled one-dimensional tensor mode.

For an invertible linear map g on U, an algebra isomorphism h on E satisfying h i = i g is uniquely determined: E is generated as a unital algebra by U, so h on exterior^j U is exterior^j g for every j <= r. Such h always exists. It preserves v exactly when det(g)=1. Indeed every exterior top wedge occurring in v scales by det(g), and v is nonzero: choose disjoint basis subsets of sizes a,b,c covering all coordinates.

Thus the four auxiliary tensors (multiplication, unit, inclusion, volume) enforce the determinant constraint exactly, without basis flags or division by factorials. Together with the original input tensor they form a fixed-signature tensor system. No condition is being weakened to a determinant square or parity of a different independently chosen map.

Its auxiliary space dimension is

D = sum_(j=0)^ceil(n/3) binom(n,j)
  = 2^(H_2(1/3) n + O(log n)),

where H_2(1/3) is approximately 0.918296. Writing all the dense multiplication and volume tables costs O(D^3) field entries. The fixed-signature ordinary tensor-system compiler gives an ordinary TI instance of size polynomial in D and the original input size. The polynomial exponent in that compiler is not specified here, so the internal exponent 0.918296 must not be advertised as an end-to-end TI runtime exponent.

For a single signed input, this is an exact finite construction and is polynomial when n = O(log N). For a two-sign input, it converts the first sign into an ordinary tensor-system constraint while leaving the second sign on the original second space. The cited ordinary tensor-system compiler does not, merely by its statement, preserve that remaining physical determinant. Consequently this paragraph is NOT an unrestricted two-sign-to-one-sign reduction.

The same balanced exterior-volume idea is already present in the project’s earlier determinant-gadget construction, where multiplication and evaluation assemble it into an algebra. Recovering it in this pass is reuse, not novelty. Its characteristic-zero lower-bound claims from the older notes are not asserted here for finite F_3.

## Why the other candidate compressions did not supply a proof

1. A determinant arithmetic circuit evaluates a given matrix in polynomial time. Encoding the gates as additional vector spaces requires a demonstrated transformation law under every allowed unknown source transporter. A gate’s numeric evaluation is not such a transformation law. No valid polynomial ordinary-TI gate compiler was obtained.

2. Finite-field Moore determinants satisfy a useful exact covariance identity: for a matrix g over F_3, replacing the variables x by g x multiplies det(x_j^(3^i)) by det(g). But evaluating this polynomial through a short circuit does not give a small tensor-system realization of all its intermediate transformations. The project’s previous Moore-marker work already records this distinction. We have not bypassed it by using Frobenius gates.

3. Exterior powers can move the sign onto an odd-dimensional representation. For example, if n is even and k = 2^v_2(n), then binom(n,k) and binom(n-1,k-1) are odd, and det(exterior^k g)=det(g). This does not produce the required physical one-sign tensor instance. An unconstrained ordinary three-tensor with an odd tested mode admits a scalar sign correction in that mode, paired with another mode. Any compilation retaining the source’s genuine orientation constraint must prevent or account for that correction. Dropping the auxiliary linkage loses the constraint.

4. Clifford and spin constructions do not automatically yield polynomial dimension: the usual exterior/Fock modules have exponential size. No compact replacement with the necessary universal transporter extension and recovery was proved.

These are diagnoses of particular unsuccessful constructions, not impossibility statements for general pair-dependent reductions. No complexity separation follows.

## Sources and verification status

The federated source/notes lookup found the project’s existing balanced exterior, Moore-marker, and determinant-circuit analyses. The returned external source records were discovery evidence, not a fresh Lean audit. The current argument is informal and uses no new Lean certificate.

For the tensor-system compilation step, see Chen, Grochow, Qiao, Tang and Zhang, *On the complexity of isomorphism problems for tensors, groups, and polynomials III: actions by classical groups*, Theorem 4.1, rephrasing the construction of Futorny, Grochow and Sergeichuk. Its displayed bound depends exponentially on a polynomial in the number of tensor components; our count is constant. The theorem establishes ordinary isomorphism equivalence and does not state determinant preservation.

Primary reference: https://arxiv.org/html/2306.03135v2#S4
