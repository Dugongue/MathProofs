# UNIVERSAL INTERTWINER TRACE CERTIFICATES AND MATRIX CONGRUENCE

Independent informal construction/audit, November 4, 2026.
This is an extension note. The earlier P019 proof remains frozen and unchanged.
No Lean verification; first-publication priority unestablished.

THEOREM U — UNIVERSAL FINITE-QUIVER ISOMORPHISM CERTIFICATES
Let M,N be arbitrary finite-dimensional representations of a fixed finite quiver, including quivers with cycles, over a field F. Assume they are not isomorphic over the algebraic closure K of F. Put d=max(dim M,dim N), where dimension is the sum over all vertices. If char F=0 or char F=p>d, the ordinary Polynomial Calculus isomorphism system
 E_a=T_h M_a-N_a T_t=0,
 F_v=T_v S_v-I_{N_v}=0,
 G_v=S_v T_v-I_{M_v}=0
has a refutation of degree at most 4 and polynomial expanded size in d, the arrow count, and the explicit matrix-entry input (dimensions are explicit/unary for this size measure). Here T_v and S_v are mutually opposite rectangular matrices of proof variables; for matching dimension vectors they are square. No field equations, Boolean equations, extra variables, division rule or PC+Inv is used.

The same result applies to tuples of matrices with simultaneous conjugacy: encode the tuple as loops at one vertex. It applies to matrix-pair strict equivalence: encode the pair as two parallel arrows. It does not permit arbitrary changes of the arrow basis or tensor third-mode mixing.

THEOREM C — CONGRUENCE CERTIFICATES
Let (A_i) and (B_i) be fixed labelled tuples of n-by-n matrices over F, with no simultaneous congruence over K. Assume char F=0, or char F=p>2n. The ordinary equations
 C_i=X A_i X^T-B_i=0,
 F0=XY-I_n=0, G0=YX-I_n=0
have PC refutations of degree at most 4 and polynomial expanded size. In particular this covers arbitrary single matrices, including singular and nonsymmetric matrices, in the stated characteristics. The congruence here is transpose congruence, not Hermitian congruence.

Over a nonalgebraically closed F, noncongruence only over F is not sufficient for a PC refutation: e.g. real forms of opposite signs may become congruent over C. These statements refer exactly to unsatisfiability over the algebraic closure, as ordinary algebraic PC requires. They settle the universal constant-degree, polynomial-size upper-bound direction of CCC 2023 Open Question 7.3 in characteristic zero (and the stated large-characteristic regimes), not optimal lower bounds or all small characteristics.

1. A trace on the endomorphism algebra separates nonisomorphic summands
Work first over K. Set W=M directsum N and B=End_Q(W), a finite-dimensional associative K-algebra. Let e,f in B be the projections onto M,N; e+f=1 and ef=fe=0.

Krull–Schmidt gives a list of pairwise nonisomorphic indecomposable representations U_i with
 M=isum U_i^{m_i}, N=isum U_i^{n_i}.
Since M,N are not isomorphic, m_i differs from n_i for some i. End(U_i) is local and its residue division algebra is K: any finite-dimensional division algebra over an algebraically closed field equals K, since every element has an eigenvalue and hence is scalar. Therefore
 B/rad B = product_i Mat_{m_i+n_i}(K).
In its i-th matrix factor the images of e,f have ranks m_i,n_i, respectively. One can see this by choosing the displayed Krull–Schmidt decomposition; another choice merely conjugates the idempotents in each factor and leaves their ranks unchanged.

Let tau:B->K be the i-th matrix trace after the quotient map. Then tau(ab)=tau(ba) for all a,b in B and
 c=tau(e-f)=m_i-n_i.
The integer satisfies 0<|m_i-n_i|<=d: an indecomposable has total vector-space dimension at least one, and each multiplicity is at most the corresponding total dimension. Thus c is nonzero in the stated characteristics. This is the only characteristic restriction in Theorem U.

Extend tau as a K-linear functional to the full space End_K(W). No multiplicativity of this extension is claimed or needed. Its commutator identity is used only for products of genuine Q-endomorphisms.

2. A degree-2 certificate when BOTH intertwining directions are supplied
Temporarily give the additional linear source equations
 H_a=S_h N_a-M_a S_t=0.
Let V_T and V_S be the vertex-graded spaces of arbitrary T and S matrices, and let L_T=Hom_Q(M,N), L_S=Hom_Q(N,M) be the kernels of the linear maps E,H. Choose constant linear projections pi_T:V_T->L_T and pi_S:V_S->L_S. The residual T-pi_T(T) is a constant linear combination of entries of E: its kernel contains ker E, so it factors through E and the factor map can be extended linearly from im E to its codomain. Similarly S-pi_S(S) is a constant linear combination of entries of H.

Embed T,S into the off-diagonal blocks of End_K(W), writing t=f t e and s=e s f, and write t0=pi_T(t), s0=pi_S(s). Then t0,s0 are Q-endomorphisms, so tau(s0 t0-t0 s0)=0. This is a polynomial identity in the proof variables: expand in fixed Hom-space bases and apply tau to each commutator of constant basis elements.

Put u=t-t0, v=s-s0. The following exact expansion avoids a product of two residual equations:
 st-ts-(s0 t0-t0 s0) = v t+s0 u-u s-t0 v.              (2.1)
Every term on the right contains ONE residual and one full/projected linear variable expression. Consequently tau(st-ts) is a sum of entries of E,H multiplied by linear polynomials. Meanwhile
 st=e+G, ts=f+F
under the obvious block embeddings of the vertex inverse-error matrices. Therefore
 c = tau(e-f) = tau(vt+s0u-us-t0v) - tau(G-F).         (2.2)
After expressing u through E and v through H, (2.2) is a Nullstellensatz certificate of degree at most 2. Its multipliers of E,H have degree at most 1; its multipliers of F,G are constant. Dividing by c gives 1. All products can be expanded and derived by ordinary PC multiplication by individual variables. Neither radical membership nor semantic substitution is used as a proof rule: the constant functional and projections simply provide coefficients of an explicit polynomial identity.

3. Remove the extra reverse equations, charging their actual degree
For each arrow a:t->h, direct expansion yields
 M_a S_t-S_h N_a
   = S_h E_a S_t - G_h M_a S_t + S_h N_a F_t.        (3.1)
Indeed S_h T_h=I+G_h and T_t S_t=I+F_t, so cancellation gives the left side exactly. The matrices M_a,N_a are constants. Each entry in (3.1) has an ordinary PC derivation of degree at most 3 from the original equations E,F,G. Thus each H entry can be derived in degree 3.

In (2.2), H is multiplied by only one linear variable expression. Its derivation therefore costs at most degree 4 after multiplication. E times linear variables costs degree 2, and the remaining inverse equations cost degree 2. This proves Theorem U with degree 4, without any extra inverse-witness assumptions.

4. Field descent, size, and effective construction
Only finitely many algebraic coefficients occur in the functional, projections and certificate, so they lie in a finite extension L/F inside K. Choose an F-linear map ell:L->F with ell(1)=1. It exists by extending 1 to an F-basis; it is NOT the field trace and does not require separability. Apply ell coefficientwise to the final identity 1=sum h_j f_j. Since every source f_j has coefficients in F, the resulting identity over F is still 1=sum ell(h_j) f_j. Degrees do not increase. Descent is applied to certificate coefficients, not to products of arbitrary proof lines, so no false multiplicativity of ell is required.

Unlike P019, this proof-size claim is polynomial in the actual total representation dimension d; it is not a polynomial-size claim for arbitrary binary-compressed quiver dimensions.

There are at most 2 sum_v dim(M_v)dim(N_v)<=2d^2 proof variables. A degree-4 expanded polynomial has at most binom(V+4,4) monomials, polynomial in d and the explicit representation input; the number of source equations is also polynomial in the arrow-list and matrix-entry input. Every certificate above has multiplier degree bounded by 4 minus the source degree, so its expanded encoding has polynomially many coefficients. It yields a polynomial-size PC proof by monomial multiplication of source equations and summation.

A uniform constructive algorithm need not compute Krull–Schmidt decompositions or radicals efficiently: introduce unknown coefficients for all allowable bounded-degree multipliers and solve the resulting polynomial-size linear coefficient system. The existence proof ensures a solution for every nonisomorphic pair in the stated fields. Over Q, this system has polynomial-size rational/integer coefficients inherited from the original input, so ordinary rational linear algebra also supplies polynomial bit-length certificates and polynomial bit time (with a large fixed exponent). Over unspecified coefficient fields the complexity claim is the usual algebraic one unless a field representation/arithmetic model is provided.

5. Strict equivalence of transpose pairs is equivalent to congruence
For any finite labelled tuple (A_i), consider the quiver with two vertices and arrows A_i and A_i^T for each i. A tuple isomorphism to (B_i,B_i^T) amounts to invertible R,S such that
 B_i=R A_i S, B_i^T=R A_i^T S for every i.             (5.1)
The forward implication from congruence is immediate with S=R^T.

Conversely transpose the second equality of (5.1) and compare with the first:
 R A_i S=S^T A_i R^T.
Set P=S R^{-T}. Multiplication by R^{-1} on the left and R^{-T} on the right gives
 A_i P=P^T A_i for every i.                           (5.2)
Because P is invertible and K is algebraically closed of characteristic different from 2, there is a polynomial h in K[t] such that H=h(P) satisfies H^2=P. Here is a characteristic-safe justification: modulo each (t-lambda)^r primary factor of the minimal polynomial of P, lambda is nonzero and has a square root in K; solve successive coefficients of h^2=t by lifting, dividing only by 2 times the nonzero constant square root. Chinese remaindering gives a single polynomial for all primary factors. No factorial denominators or matrix diagonalizability assumption is needed.

Polynomial functional calculus in (5.2) gives A_i H=H^T A_i. Define Z=R H^T. Then
 Z A_i Z^T=R H^T A_i H R^T=R A_i H^2 R^T
          =R A_i P R^T=R A_i S=B_i.
This works simultaneously for all i, with arbitrary singular/nonsymmetric A_i. Thus noncongruence over K implies nonisomorphism of the transpose-pair representations. The source representation has total dimension 2n, so p>2n suffices for Theorem U's trace argument; characteristic 2 is also excluded by the square-root step.

6. Direct degree-4 congruence derivation (sharper than black-box degree 6)
Use the bidirectional trace identity (2.2), not a generic degree-4 proof substitution. For a source equation C_i=X A_i X^T-B_i and G0=YX-I, derive the following TWO linear-looking target intertwiner polynomials directly:
 L_i=X A_i-B_i Y^T = C_i Y^T-X A_i G0^T,             (6.1)
 K_i=Y B_i-A_i X^T = G0 A_i X^T-Y C_i.              (6.2)
Both have PC derivations of degree at most 3 in the ORIGINAL source variables. Apply exactly the same identities to C_i^T, a scalar linear combination of the given C_i entries, to obtain the corresponding equations for A_i^T and B_i^T.

The forward quiver node maps are T_source=Y^T and T_target=X. The reverse maps are S_source=X^T and S_target=Y. The target node inverse equations are exactly F0,G0 or their transposes, not products requiring any new variables. The residual trace certificate (2.2) uses each target linear intertwiner equation only times a single linear expression in X,Y. Multiplying the degree-3 derivations (6.1)-(6.2) by that expression costs degree at most 4. Its inverse-equation terms still cost degree 2. This proves Theorem C.

Merely substituting into an arbitrary degree-4 target PC derivation gives a valid but looser degree-6 upper bound, because such a derivation may charge degree-3 target-equation multipliers. The explicit bilinear identity is why the stronger degree 4 is justified.

7. Scope and attribution
Krull–Schmidt, the endomorphism radical quotient, Artin–Wedderburn, cyclic block trace, linear projections, and polynomial square roots are classical. This note's candidate contribution is their explicit low-degree PC assembly, including the direct bidirectional congruence pullback. We have not verified publication priority. The existing MathProofs inverse-transport/kernel-trace notes supplied accounting discipline; no imported source-only theorem is asserted to be kernel checked.

The universal theorem does not settle matrix-space isometry with arbitrary slice mixing, tensor isomorphism, or arbitrary small characteristic. In small characteristic every multiplicity difference can vanish modulo p; the present trace certificate then has zero constant and must not be declared a refutation.

Primary statement: Galesi, Grochow, Pitassi, She, On the Algebraic Proof Complexity of Tensor Isomorphism, CCC 2023, Section 7.3, Open Question 7.3.
https://drops.dagstuhl.de/storage/00lipics/lipics-vol264-ccc2023/LIPIcs.CCC.2023.4/LIPIcs.CCC.2023.4.pdf
Classical congruence context: Horn–Sergeichuk, Canonical forms for complex matrix congruence and *congruence.
https://arxiv.org/abs/0709.2473
