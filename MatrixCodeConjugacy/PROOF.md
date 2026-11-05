# Arbitrary-Dimension Average-Case Matrix-Code Conjugacy
November 4, 2026. Full informal proof candidate; not Lean verified.
Target: Li–Li–Qiao–Tao–Wang, arXiv:2604.00591v2, Problem 1.6.
Primary source: https://arxiv.org/html/2604.00591v2

## STATUS AND CREDIT
This is an explicit sufficient algorithm and proof for the fixed-field asymptotic problem, rather than merely a necessary condition. It still requires independent mathematical review. It is not a novelty or publication-priority certificate. Our October 7 notes already proposed a different full decision algorithm; this proof reuses their elementary subspace count while avoiding their commutative-unit/field-network engine. The canonical trace-dual pair and the random-matrix inputs are due to the cited paper. The additional assembly is dimension duality + a polynomial enumeration cutoff + a dimension-parametric incidence argument.

## 1. EXACT THEOREM

There is an algorithm on n-by-n-by-m tensors over an explicitly represented finite field F_q, running in randomized time polynomial in n,m,log q, which returns YES with an explicit conjugating matrix, NO, or FAILURE. Every answer other than FAILURE is correct.

There is an absolute c>0 such that, for every fixed prime power q, there is n_0(q), independent of m, with the following property. For n>=n_0(q) and EVERY m>=0, at least c/q of the iid uniform first tensors have the property that comparison against EVERY second tensor is decided by the mathematical algorithm. Any randomized standard matrix-similarity subroutine can be run with bounded repetition, returning FAILURE on a subroutine timeout; its success probability can be made >=2/3 uniformly on each input. A successful YES can include the GL_m slice-change witness.

One may take c=e^(-23/9)/2048 after allowing a factor two for bounded standard subroutines. The statement is asymptotic for each fixed q, exactly as in the source. We do not claim a uniform explicit n_0(q) from asymptotic random-matrix estimates, or worst-case polynomial time on every source.

## 2. NOTATION AND THE ONLY PUBLISHED RANDOM-MATRIX INPUTS

Let W=M_n(F_q), N=n^2, and beta(X,Y)=Tr(XY). For C<=W let H(C)=C cap C^perp. beta is symmetric, nondegenerate, and invariant under simultaneous conjugation. Matrix units provide a dual-permuted basis, so these properties hold in every characteristic.

Call a nonzero matrix H spectral-good if beta(H,H)=0 and H has exactly one F_q-eigenvalue, which is nonzero and has algebraic multiplicity one. This condition is invariant under nonzero scalar multiplication. Put a=e^(-23/9).

We use two already proved results:
(G) Independent uniform H,X in W generate M_n(F_q) except with probability epsilon_n(q)=q^(-Omega(n)), for fixed q.
(S) For fixed q and sufficiently large n, the ambient density delta_n(q) of spectral-good matrices is at least a/(2q).

These are respectively Theorem 2.3 and Theorem 6.11 / Equation (56) of the source. Their proofs, including the nonzero-eigenvalue condition and all finite characteristics, remain upstream inputs. Our extension does not assume that a canonically chosen matrix is independent of the source code.

All other counting and algorithmic steps below are explicit. Standard exact finite-field arithmetic, Gaussian elimination, polynomial gcd, matrix characteristic polynomials, and one-matrix similarity are established computational-algebra routines, not conjectural oracles.

## 3. RANK REDUCTION AND DIMENSION DUALITY

Compute the spans C,D of the two m-tuples. Unequal dimensions imply NO. Once their dimensions agree, the tensor orbit problem is equivalent to conjugacy of C,D. This remains true with dependent slices: two linear maps F_q^m -> W with the same image differ by an invertible domain map, obtained by matching bases of their kernels and chosen complements.

Conjugation is a beta-isometry, and hence
  S C S^(-1)=D  iff  S C^perp S^(-1)=D^perp.
If their common dimension r exceeds N/2, replace both by their perpendiculars. Denote the resulting common dimension by d=min(r,N-r). This map is a bijection between Grassmannians, so it preserves uniformity of a random code conditional on its dimension.

If d=0, answer YES. This covers zero/full spans. When n=1, all spans are zero or F_q, so rank equality decides everything.

Assume below n>=2 and 1<=d<=N/2.

## 4. A POLYNOMIAL ALL-TARGET ROUTINE FOR SMALL CODES

First handle d=1 as in Section 5. For d>=2 use this routine whenever q^d<=n^2.

Enumerate the q^d elements of C. Search all ordered pairs (X,Y) for one with simultaneous commuting algebra
  {Z: ZX=XZ and ZY=YZ}=F_q I.
If there is no such pair, return FAILURE.

Fix the first such pair. Enumerate every ordered pair (U,V) in D^2. For each pair, solve the linear intertwiner equations
  S X=U S,   S Y=V S.
If the solution space has dimension one, choose a nonzero generator S. If S is invertible and S C S^(-1)=D, return YES with S. Otherwise continue. If no pair succeeds, return NO.

CORRECTNESS. If S_0 is an actual code conjugacy, its images U=S_0 X S_0^(-1), V=S_0 Y S_0^(-1) occur in the target enumeration. The entire intertwiner space for this pair is S_0 times the source commuting algebra, hence the one-dimensional space F_q S_0. Thus the routine finds an invertible generator and accepts. Conversely every acceptance is checked on the full code. No image pair is missed and no arbitrary nonsingularity oracle is used.

COST. Each pair list has at most q^(2d)<=n^4 elements. We search the source list once, then search the target list once; these are added costs, not an unbounded recursive product. Each test is polynomial-size linear algebra.

SOURCE FRACTION. For uniform d-dimensional C, a uniform ordered basis has its first two matrices distributed as two independent uniform matrices conditioned on linear independence. That conditioning event has probability
  (1-q^(-N))(1-q^(1-N))>=1/4.
By (G), C contains a full-algebra-generating pair, and hence a scalar-commutant pair, with probability at least 1-4 epsilon_n(q). Existence is a property of C, independent of which input basis is supplied. Thus this branch succeeds on at least half of the source codes for sufficiently large n, uniformly in every d on this branch.

## 5. DIMENSION ONE

For a line C=F_q H, require H to be spectral-good; otherwise return FAILURE. Normalize H by its unique nonzero F_q-eigenvalue, producing A whose unique F_q-eigenvalue is 1.

For a target line D=F_q K, if K fails the same condition, return NO. Normalize K to B. The lines are conjugate exactly when A,B are similar: an arbitrary line conjugacy may multiply a generator by a scalar, but the eigenvalue normalization removes exactly that freedom.

Ordinary one-matrix similarity, with a conjugating witness, is a polynomial-time computational-algebra problem. It can be done by constructive rational canonical forms, or by the established matrix-tuple conjugacy routine cited in source Theorem 2.5. No enumeration of F_q is required.

The fraction of spectral-good lines equals delta_n(q)/(1-q^(-N)), since every line has q-1 nonzero generators. Thus (S) gives at least a/(2q) successful source lines. This handles the endpoint where no pair can generate the full matrix algebra.

The spectral test itself needs no full factorization: compute gcd(c_H(t),t^q-t), with t^q computed modulo c_H by repeated squaring; require a degree-one gcd with nonzero root lambda and c_H'(lambda)!=0. All costs are polynomial in n,log q.

## 6. A UNIFORM NONDEGENERATE-SUBSPACE LEMMA

LEMMA. Let V be a nondegenerate symmetric bilinear space over F_q. In odd characteristic it may have either isometry type. In characteristic two assume it is nonalternating. For every 0<=k<=M=dim V, at least p_0=1/64 of its k-subspaces have nondegenerate restriction.

PROOF. Endpoints k=0,M are immediate. Choose an orthogonal decomposition V=E perp F with dim E=k; over odd fields diagonalization supplies it, and over even finite fields a nonalternating symmetric form has an orthogonal basis and is equivalent to I_M. Count one orbit of E under the full bilinear isometry group:
  number in this orbit = |O(V)| / (|O(E)| |O(F)|).

In odd characteristic, the standard finite orthogonal-group orders, divided by q^(s(s-1)/2), lie between 1 and 3 in every dimension s, including dimension zero. Consequently this orbit contains at least q^(k(M-k))/9 subspaces.

In characteristic two, for the symmetric BILINEAR form I_s, not a quadratic orthogonal form,
  |O(I_s)|=q^(s(s-1)/2) product_(i=1)^floor((s-1)/2) (1-q^(-2i)).
For odd s, fix the characteristic vector and use Sp_(s-1)(q). For even s, fix its isotropic characteristic vector; the quotient action is Sp_(s-2)(q) and its kernel has q^(s-1) elements. These give the displayed formula. Every normalized product lies in [2/3,1]. Choose E,F both nonalternating, so the orbit has at least (2/3)q^(k(M-k)) subspaces.

Finally
  [M choose k]_q <= q^(k(M-k)) / product_(i>=1)(1-q^(-i))
                  <= 4 q^(k(M-k)).
The last product exceeds 1/4: at q=2 its first three factors multiply to 21/64, and the remaining product is at least 1-sum_(i>=4)2^(-i)=7/8. Larger q only increase it.

The odd-characteristic probability is therefore at least 1/36, and the even-characteristic probability at least 1/6. The weaker 1/64 works uniformly. QED.

This lemma and its group-order argument were already present, with stronger constants, in our October 7 density notes. No transitivity on ALL isotropic lines in characteristic two is being assumed.

## 7. THE CANONICAL HULL PAIR FOR ARBITRARY d

For C on the remaining branch q^d>n^2, require dim H(C)=1 and a spectral-good hull generator. Otherwise return FAILURE.

Normalize that generator to A with unique F_q-eigenvalue 1. Write
  c_A(t)=(t-1)g_A(t),  g_A(1)!=0,
and define the rank-one spectral projector
  P=g_A(A)/g_A(1).
Then P^2=P, AP=P, beta(A,A)=0, beta(A,P)=beta(P,P)=1.

Define
  U=span(A,P)^perp,   M=N-2,   k=d-1,
  E=C cap P^perp.
The Gram matrix on span(A,P) is [[0,1],[1,1]], nonsingular in EVERY characteristic. Thus U is nondegenerate. C=span(A) direct-sum E, and E is a nondegenerate k-subspace of U exactly when H(C)=span(A).

Put tau=Tr(A) and
  R=I-(1-tau)A-tau P.
Direct pairing gives R in U. Also R!=0: otherwise, on ker P one would have I=(1-tau)A, giving an F_q eigenvalue on that nonzero complementary space, contrary to uniqueness and simplicity of the eigenvalue 1.

In characteristic two U is nonalternating. Indeed beta(X,X)=Tr(X)^2. If U were alternating then Tr would vanish on U, so I would lie in U^perp=span(A,P), equivalently R=0, a contradiction.

There is a unique Z in E satisfying
  beta(Z,Y)=Tr(Y) for all Y in E.
It is computed by a nonsingular Gram system. Because beta(R,Y)=Tr(Y) on U, Z is exactly the orthogonal projection of R onto E. Everything A,P,E,Z depends only on C and is conjugation-equivariant.

If the commuting algebra of (A,Z) is not the scalar line, return FAILURE. Otherwise construct the corresponding pair (B,Z_D) from the target code, rejecting necessary-condition failures. Solve the two linear intertwiner equations as in Section 4. If the solution space is not one-dimensional, or its generator is singular, return NO. Otherwise check the full span conjugacy and return YES or NO accordingly.

The same scalar-commutant proof from Section 4 establishes all-target correctness. This does not require finding all units in an arbitrary linear space. Every YES is checked on the complete input span.

## 8. UNIFORM DENSITY OF THE REQUIRED HULLS

Let G be the set of spectral-good lines in W. By (S),
  |G| >= a q^(N-1) / (2(q-1)).

Fix L in G, normalize its generator A, and use P,U from Section 7. The map
  E -> C=L direct-sum E
is a bijection from k-subspaces of U to d-subspaces C with L contained in C contained in L^perp. Moreover H(C)=L iff E is nondegenerate. Section 6 gives at least
  p_0 [N-2 choose d-1]_q
such codes for EACH good line. The exact Gaussian ratio is
  [N-2 choose d-1]_q / [N choose d]_q
  = ((q^d-1)(q^(N-d)-1))/((q^N-1)(q^(N-1)-1))
  >= q^(1-N)/4.
Different exact hull lines give disjoint code sets. Therefore, for every 1<=d<=N-1,
  Pr[uniform d-code has spectral-good one-dimensional hull]
  >= a p_0 / (8(q-1))
  >= a/(512q).

This proof does not require the hull line to be uniformly distributed after nondegeneracy conditioning. Its good-line-by-good-line bound avoids that issue entirely.

## 9. POINT-PROBABILITY CONTROL FOR THE TRACE-DUAL MATRIX

The key is that this calculation works for arbitrary k, not only k=n-1.

Sample L uniformly from G and a nonzero generator H uniformly from L. Equivalently H is a uniform spectral-good ambient matrix. Normalize H to A, obtain P,U,R as above, and sample a uniform k-subspace E of U before imposing nondegeneracy. Let ND be the event E is nondegenerate. Then Pr[ND]>=p_0 for every H.

After conditioning on ND, the resulting code C=L direct-sum E is UNIFORM among d-codes with spectral-good line hull. To see this, before conditioning every incidence (L,E) has the same probability: all U have the same dimension and Gaussian number of k-subspaces; every such code has exactly one hull line. This remains true even when Pr[ND|L] varies.

For x in U outside {0,R}, projection Z=x implies
  x in E contained in (R-x)^perp.
If beta(x,R-x)!=0 there are no such E. Otherwise the number of k-subspaces satisfying these incidences is
  [M-2 choose k-1]_q,
before nondegeneracy is imposed. This is an UPPER BOUND even when the incidences force degeneracy.

Hence the unconditioned point mass of {ND and Z=x}, for fixed H, is at most
  [M-2 choose k-1]_q / [M choose k]_q
  = ((q^k-1)(q^(M-k)-1))/((q^M-1)(q^(M-1)-1))
  <=4 q^(-M+1)=4q^3 q^(-N).

The exceptional projections obey, on ND,
  Z=0 iff E<=R^perp,   Z=R iff R in E.
Their combined unconditioned probability is at most
  ([M-1 choose k]_q + [M-1 choose k-1]_q)/[M choose k]_q
  = (q^(M-k)+q^k-2)/(q^M-1)
  <=2(q^(-k)+q^(k-M)).
After conditioning on ND, this is at most
  128(q^(-k)+q^(k-M)).

By (S), the law of H has density at most 2q/a relative to an independent uniform ambient matrix. The preceding point bound therefore shows that the JOINT law of (H,Z), away from the exceptional projections and after ND conditioning, is pointwise bounded by
  (8/(a p_0)) q^4 = (512/a) q^4
times the independent uniform law on W^2.

Applying (G) and noting that scaling H to A leaves its generated algebra unchanged gives the uniform bound
  Pr[ A,Z fail to generate M_n(F_q) | required good hull ]
  <= 128(q^(-k)+q^(k-M)) + (512/a)q^4 epsilon_n(q).      (*)

This is a density comparison, not a claim of independence.

## 10. WHY THE LARGE-DIMENSION BRANCH IS POLYNOMIALLY GOOD

We use it only when q^d>n^2 and d<=N/2. Thus
  q^(-k)=q^(1-d)<q/n^2,
  q^(k-M)<=q^(-N/2+1).
The right side of (*) tends to zero for each fixed q as n tends to infinity, UNIFORMLY over every d on this branch.

Choose n_0(q) so that (*) is at most 1/2, (S) holds, and 4 epsilon_n(q)<=1/2. This threshold has no dependence on d or the original m. A generating pair has scalar commuting algebra. Multiplying Section 8's hull density by the conditional success at least 1/2 gives
  at least a/(1024q)
successful first codes in this branch.

Together with Sections 4 and 5, every dimension has an all-target good-source fraction at least a/(1024q), before allowing bounded standard-subroutine failures.

## 11. RETURN TO IID TENSORS, INCLUDING ALL DEPENDENT-SLICE CASES

For iid uniform A_1,...,A_m, condition on ANY span rank r. Its span is a uniform r-dimensional subspace of W: GL(W) acts transitively on subspaces of a given dimension and preserves the iid tuple distribution. All conditioning ranks, including r=0,N, are covered by Section 3.

Consequently we may average the dimension-uniform good-source lower bound over r. There is no need to discard dependent tuples, or multiply by a full-rank event whose probability depends on m. Orthogonal complementation preserves the relevant conditional uniformity.

This proves the claimed c/q fraction uniformly over every m. If a successful conjugator S is found for complemented codes it is also a conjugator for the original codes. Recover the GL_m slice-change matrix by matching kernel/complement bases of the two coefficient maps, as in Section 3.

## 12. BINARY RUNTIME AND INDEPENDENT CHECKER

Represent F_q using the supplied prime-field coordinates/irreducible defining polynomial. A field operation has cost polynomial in log q. All vectors and matrix spaces have dimensions polynomial in n,m. Hulls, perps, Gram systems, centralizers and intertwiners use finite linear systems. Characteristic polynomials and gcd(c_A,t^q-t) cost polynomially many field operations; repeated squaring uses O(log q) modular products.

The small branch enumerates at most n^2 code elements and n^4 pairs per list. The large branch uses no code-element enumeration. Rank-one projectors and Gram complements are polynomial-size matrices; no field extension, determinant-oracle search, exponential dictionary, discrete logarithm or supplied search group is present. The standard one-matrix similarity routine has a known polynomial bound; bounded repetitions/timeouts give the requested randomized polynomial-time implementation.

An independent YES checker verifies det S!=0 and the ORIGINAL span equality. If a GL_m witness is emitted it checks every original slice equation and its invertibility as well. These checks do not replace the proof of correct NO answers, which is supplied by the exhaustive image-pair argument or scalar-commutant intertwiner argument.

## 13. SCOPE AUDIT AND WHAT THIS DOES NOT ASSERT

The theorem is an average-case all-target result for matrix-code CONJUGACY, not arbitrary left-right matrix-code equivalence, GL 3-TI, worst-case TI, cross-characteristic reductions, or VP versus VNP. No random target distribution is assumed. Orthogonal complements are taken for Tr(XY), not the coordinatewise Euclidean form. The characteristic-two form is a symmetric bilinear form, not a quadratic form.

The only asymptotic probability inputs are the precise established (G) and (S). The proof supplies every intermediate dimension and keeps a single polynomial runtime bound. Its new trace-dual assembly avoids relying on our prior unverified semisimple field-network transporter algorithm.

## REFERENCES AND REUSED MATERIAL

Primary: Li–Li–Qiao–Tao–Wang, https://arxiv.org/html/2604.00591v2, §§2,3.2,6.3; v2 revised November 3, 2026. Our proof uses their spectral/trace-dual construction and their two cited random-matrix theorems.

Prior MathProof drafts, read and credited as informal work:
- Prior MathProof note: `MATRIX-CODE-AVERAGE.md`.
- Prior MathProof note: `DENSITY.md`.
- Prior MathProof note: `DENSITY-PROOF.md`.

These supplied the dimension-uniform isometry-group count, exact-hull counting discipline and warnings about characteristic-two scalar lines. No unsupported claim of their Lean verification is made. Problem 1.8/25's verified execution/bit-accounting library and general trace/orthogonal-complement lemmas were searched as possible future formalization support; none is required as an assumed new mathematical theorem in this informal assembly.
