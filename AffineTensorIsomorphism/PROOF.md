# Affine Tensor Isomorphism Is TI-Complete

**Status:** AI-assisted informal proof; separate AI-worker review and exact finite checks where supplied. No Lean certificate; independent human review and publication-priority assessment remain pending.

31 October 2026. Complete informal reduction proof; no new Lean/kernel audit.

Chosen published direction.
Chen, Grochow, Qiao, Tang and Zhang, On the complexity of isomorphism problems for tensors, groups, and polynomials III: actions by classical groups, Section 1.5, explicitly proposes studying TI_G for affine groups alongside special-linear, Borel and parabolic families. This is a documented research direction, not a numbered conjecture. We settle the standard homogeneous affine family in full, over every field. Existing TI_Par, TI_Levi and TI_SL-related project results are not reannounced as new.
https://arxiv.org/html/2306.03135v2#S1.SS5

The decisive reused result is the SAME paper's Theorem 4.1, rephrasing Futorny-Grochow-Sergeichuk 2019, Theorem 1.1. It compiles a constant-size tensor system, whose components have order at most three and may use dual spaces, into ordinary three-tensor isomorphism. The output dimensions and construction time are polynomial when the number of components is fixed. Section 4 explicitly defines dual factors using inverse-transpose actions, so the covectors below satisfy its actual hypotheses.
https://arxiv.org/html/2306.03135v2#S4

Frozen theorem.
Fix any field K. Put

    Aff(n,K) = { [[A,b],[0,1]] : A in GL_n(K), b in K^n } <= GL_(n+1)(K).

On arbitrary pairs of three-tensors in K^(n1+1) tensor K^(n2+1) tensor K^(n3+1), let AffTI ask orbit equality under the independent three Aff groups. No conciseness, genericity or nonzero-input promise is imposed. Then ordinary three-tensor isomorphism and AffTI are polynomial-time many-one equivalent over K. The corresponding reduction classes are equal: TI_Aff=TI.

This fixes the intended representation explicitly: the affine group is embedded in homogeneous coordinates, as required to regard it as a matrix subgroup in the source's TI_G framework. It is not a statement about an undefined nonlinear action directly on tensor entries.

Sufficient assembly.
## 1. Ordinary TI -> AffTI: append one zero coordinate to every mode.
## 2. AffTI -> tensor-system isomorphism: attach the three distinguished quotient covectors.
## 3. Apply the published constant-component tensor-system compiler to obtain ordinary TI.
All maps are described below; no unknown gadget or oracle is assumed.

Proof of the forward reduction.
Let U_i=K^ni and V_i=U_i direct-sum K e_i. Embed an input tensor T in U_1 tensor U_2 tensor U_3 into V_1 tensor V_2 tensor V_3, with every coordinate involving e_i set to zero. Denote the resulting tensor by T+.

If (A_1,A_2,A_3) is a GL transporter from T to S, choose affine matrices diag(A_i,1). They carry T+ to S+.

Conversely, every affine matrix [[A_i,b_i],[0,1]] preserves the subspace U_i=ker ell_i, where ell_i is the last-coordinate functional. Its restriction to U_i is exactly A_i, which is invertible. Since T+ is supported entirely inside the U_i factors, the affine tensor action on it is exactly the embedded action of A_1 tensor A_2 tensor A_3 on T. Therefore an affine transporter from T+ to S+ gives an ordinary GL transporter from T to S. Translation columns b_i cannot create an extra equivalence. This is valid even for zero tensors and nonconcise tensors; no support-recovery lemma or cancellation of concise cores is needed.

The forward map is a coordinate zero-padding map, adding only one coordinate per mode. It has polynomial output size and direct polynomial-time construction. If a zero-dimensional source mode is permitted, its tensor space is zero and this degenerate case is handled directly; the positive-dimensional model used in the source needs no exception.

Proof of the reverse reduction.
Given T,S in V_1 tensor V_2 tensor V_3, form the two tensor systems

    System(T)=(T, ell_1, ell_2, ell_3),
    System(S)=(S, ell_1, ell_2, ell_3),

where ell_i in V_i^* is the last-coordinate covector. The three support spaces are labeled V_i; the tensor types distinguish the components. A system transporter is a triple G_i in GL(V_i) satisfying the tensor equation together with

    G_i^(-transpose) ell_i = ell_i.

Multiplying by G_i^transpose makes this equivalent to G_i^transpose ell_i=ell_i, or in row notation ell_i G_i=ell_i. Thus the last row of G_i is (0,...,0,1). Such an invertible matrix has exactly the affine block form [[A_i,b_i],[0,1]], with A_i invertible. The covector condition fixes its value, not merely the line spanned by it: no unwanted scalar is left on the quotient.

Consequently T and S are Aff-equivalent if and only if their four-component tensor systems are GL-isomorphic. Every component has order one or three. The published tensor-system compiler therefore produces ordinary three-tensors C(T),C(S) whose GL-equivalence is exactly Aff-equivalence of T,S. The component count is four, so its exponential dependence on the component count is a fixed constant; its size/time dependence on the input dimensions is polynomial.

This completes both directions and the full frozen theorem. The upper reduction is a direct application of prior tensor-system universality; that machinery must be credited rather than presented as a newly invented compiler.

Stronger variable-size framed-quotient family.
For n>=0,k>=1 define

    Aff(n,k;K)={ [[A,B],[0,I_k]] : A in GL_n(K), B in Mat_(n,k)(K) }.

The same TI-completeness conclusion holds with k_i supplied as part of the mode dimensions. Its quotient action is fixed pointwise, so this is distinct from the full parabolic that permits an arbitrary GL_k quotient action.

Forward: append k_i zero coordinates in mode i. The matrices preserve the original n_i-dimensional hyperplane and restrict to arbitrary GL_ni, exactly as above.

Reverse: for each i introduce an auxiliary W_i=K^ki, a projection Q_i:V_i->W_i onto its last k_i coordinates, a regular nilpotent Jordan operator J_i on W_i, and a cyclic vector v_i=e_1 with (v_i,J_i v_i,...,J_i^(ki-1)v_i) a basis. Use the system containing T and the three copies each of Q_i,J_i,v_i. These have orders three, two, two and one, with ten components total independent of k_i.

An auxiliary transporter H_i preserving J_i by conjugation and fixing v_i fixes J_i^j v_i for every j, hence is the identity. The Q_i tensor equation is then Q_i G_i^(-1)=Q_i, equivalent to Q_i G_i=Q_i. Thus each G_i has the required [[A_i,B_i],[0,I_ki]] form. Conversely every such G_i, with H_i=I, preserves the auxiliary tensors. All components have order at most three and their count is ten, so the same compiler yields polynomial output dimensions/time even when k_i grows. All J_i,v_i,Q_i entries are zero or one. If some k_i=0, omit that mode's auxiliary frame and let its action be unrestricted GL; the same argument applies with fewer components.

Uniformity and field conventions.
The proof uses no square roots, algebraic closure, random choices, form nondegeneracy, determinant-root oracle, characteristic restriction or extension field. Zero padding and marker data are explicit. The reduction algorithm of Theorem 4.1 is the actual published construction reused here. For exact bit-complexity claims over Q or presented finite fields, one uses its coordinate-gadget implementation; no arithmetic with unknown transporters is part of the reduction algorithm. No assertion is made that the orbit-decision problem itself is polynomial time.

DAG/library reuse inspected.
- Meta/FGSPackaging20260902.lean packages constant-free source-coordinate block encodings as ordinary GL3TI projections, including polynomial bounds and zero-extension equivalence.
- Meta/FormTI.lean contains the same use of fixed tensors to encode group stabilizers, together with inverse-transpose identity couplings and the concrete partition-removal compiler.
- The canonical TIPar and TI_Levi results supply related stabilizer machinery, but the groups here fix the quotient pointwise rather than allowing its full general-linear action.
- JouxNarayanan54.lean already provides ordinary TI-to-special-linear padding; its GI corollary is prior project work and is not counted as a different closure here.

Novelty/source audit.
The primary source names affine groups as a future direction and simultaneously supplies the tensor-system compiler that makes its upper reduction immediate. Bounded searches for affine-group tensor-isomorphism classifications found no explicit subsequent statement of this equivalence. The result may be an unstated elementary corollary of published machinery; this search does not establish priority. It is appropriate to describe it as a complete informal answer for the standard homogeneous affine family in the documented direction, with novelty pending. It is not an answer to the Borel part of that direction or to the numbered open questions about TI_SL or orthogonal/unitary equality.

No new Lean file or kernel audit was produced. Exact finite tests in this directory check the stabilizer and padding identities; they do not replay the published tensor-system compiler.

Exact finite controls.
verify.py enumerated all 168 invertible three-by-three matrices over F_2 and all 11,232 over F_3. The inverse-transpose covector stabilizers were exactly the expected affine subgroups (24 and 432 elements). It also checked 200 random padding/transporter identities over those fields and exhaustively confirmed that the nilpotent-plus-cyclic-vector auxiliary frame has trivial stabilizer in both groups. Every check passed. These validate the local algebraic interfaces, not a new execution of the published tensor-system compiler.
