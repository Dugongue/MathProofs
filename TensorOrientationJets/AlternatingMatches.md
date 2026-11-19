# Signed comparison from alternating matches and their kernels

**Theorem.** Work over the field F of three elements. Write a tensor in bilinear form as T:U×V→W and test the determinant on U. Suppose dim U=dim V. Let L be the total explicit input length and fix a threshold b=O(log(2+L)). Define the alternating-match space

    E_T = {f:U→V such that T(x,f(x))=0 for all x∈U}.

Suppose dim E_T≤b and some invertible f∈E_T has the following two properties. The map

    κ_(T,f): Λ²U → W,       x∧y ↦ T(x,f(y))

has kernel of dimension at most b, and that kernel contains an alternating bivector of rank at least dim U−b. Then one-sign TI between T and another tensor with the same format reduces to a single ordinary TI comparison, with no extra target hypothesis. Failed target size or existence tests make the pair ordinary-negative because all the tested properties are invariant. The construction does not require a supplied transporter or prior knowledge of rigidity.

This extends the nonsingular form-list test. The bivectors may be singular and their images need not span U. A small quotient supplies any determinant not already fixed by the large symplectic part.

## Extract both spaces and the candidate marks

Choose a basis u_i of U. Evaluate T(u_i,f(u_i)) and the cross expression T(u_i,f(u_j))+T(u_j,f(u_i)) for i<j. Setting all these vectors to zero gives a homogeneous linear system in the entries of f. These constraints are equivalent to T(x,f(x))=0 for every x by bilinearity. Thus a raw tensor determines E_T by Gaussian elimination.

For each invertible f, T(x,f(y)) is alternating. Write the matrix of κ_(T,f) explicitly on basis wedges to find its kernel K_(T,f). For bivectors P∈K_(T,f) write P also for the corresponding alternating linear map U*→U defined by contraction. Compute its rank by Gaussian elimination. Enumerate all invertible f with dim K_(T,f)≤b and, for each such f, every P in the kernel of rank at least dim U−b. The total count is at most 3^(2b), and all tests and coordinate conversions per candidate take polynomial time. This is a raw extraction, with yes and no recognition of the stated size and rank conditions.

An ordinary transporter (a,c,d) satisfying S(ax,cy)=dT(x,y) maps these marks by

    f ↦ f' = c f a⁻¹,             P ↦ P' = (Λ²a)P.

Indeed S(ax,f'ax)=dT(x,f(x))=0 and κ_(S,f') (Λ²a)=dκ_(T,f). This gives bijections on the two spaces, on the invertible matches, and on their kernels. In particular the dimension and rank bounds are preserved. Tests on the raw arrays can establish the hypotheses without giving the arrays any extra input marks.

## Isolate the sign in a small quotient

Fix one valid source mark (f,P). For each target mark (f',P') of the same rank add to the actual tensor comparison the equations

    cf=f'a,               (Λ²a)P=P'.

The first equation is a linear-map marker. For the second, represent the bivector by its alternating bilinear map on U*, which is a mixed tensor of order two with a fixed scalar output. Use the same physical mode maps in the markers as in the original tensor.

Let I=im P, I'=im P'. Alternation gives ker P=I^⊥ in U*, since P(α)=0 exactly when α vanishes on the image. Consequently P induces a nonsingular alternating map I*→I. Invert it to get a nonsingular alternating form B on I. Do the same for P'. The bivector equality forces a(I)=I'. Its induced map a_I satisfies a_I^t B'a_I=B. In chosen frames of I and I' this gives

    det(a_I)=Pf(B)/Pf(B').

The Pfaffian congruence identity follows from the usual polynomial identity over the integers and therefore holds over F as well. The nonzero Pfaffian can be computed by symplectic elimination with basis tracking. Use adapted full frames M_T,M_S whose first vectors are the chosen bases of I and I'. Let c₀=det M_S/det M_T. In the raw full coordinate frames every marked transporter satisfies

    det(a)=c₀ · Pf(B)/Pf(B') · det(a_Q),

where a_Q acts on U/I→U'/I' in the corresponding quotient frames. This follows by the determinant of the block triangular matrix preserving the chosen subspaces. Require the last determinant to be [c₀ Pf(B)/Pf(B')]⁻¹. When the quotient has dimension zero its determinant is prescribed automatically as one, so discard a conflicting branch.

The quotient has dimension at most b. Include its actual quotient map and its exterior algebra, including the degree-one inclusion. Multiplication forces the induced top-line action to be the determinant. Mark its top generator with the prescribed multiplier between source and target. This costs at most 2^b algebra coordinates. A marked transporter meeting the sign condition extends to the auxiliary maps. A solution to the mixed system restricts to an actual tensor transporter and the displayed determinant calculation forces the desired sign. The ordinary tensor-system compiler applies to a constant number of bounded-order component maps. Use the polynomial disjunction construction to combine all branches into one ordinary comparison. [Ordinary tensor-system compiler](https://arxiv.org/html/2306.03135v2#S4) · [Disjunction and full-rank alternating forms](https://github.com/Dugongue/MathProofs/blob/main/OneSignTensorComparison/Disjunction.md)

Every positive transporter maps the chosen source mark to one target candidate and satisfies that branch. Every positive branch produces a positive transporter. Thus the relation is exact in both directions. To distinguish flexibility from rigidity on the promised class, compare T with its translate by a fixed reflection in U using the same reduction. A positive transporter to the reflected tensor exists exactly when T has a negative stabilizer sign. This procedure does not require a separate ordinary search-to-decision theorem.

## Examples with scalar pair adjoints

Let U=V, let K⊂Λ²U have dimension at most b, and let

    T(x,y) = [x∧y] in Λ²U/K.

Assume every nonzero element of K has rank at least six. Suppose K contains a bivector of corank at most b. Then E_T consists exactly of the scalar matrices. Indeed T(x,f(x))=0 implies that the rank-at-most-two bivector x∧f(x) vanishes. The resulting linewise property implies f is scalar, by testing basis vectors and their pairwise sums. Each nonzero f produces kernel K. Consequently the algorithm recognizes the indicated data from arbitrary rebasings of these raw arrays.

The two input pair-adjoint equation lifts to the exterior square before quotient, since the difference of the two decomposable bivectors has rank at most four. Comparing coefficients in e_i,e_j then gives a common scalar. A pair adjoint involving the output similarly forces the input map to preserve all lines by evaluating on (x,x), and the output is spanned by the wedge values. Thus all pair adjoints are scalar. These scalar adjoints give no basis for separating the bivectors in the kernel. The algorithm instead uses a linear space of matches between the two inputs.

For a concrete two-dimensional kernel take independent nonsingular bivectors P₁,P₂ on different even-dimensional direct summands U₁,U₂, each of dimension at least six and of different dimensions. Set K=F P₁+F P₂. The two bivector lines are distinguished by rank, and their images are the two support subspaces. Each bivector with both coefficients nonzero has full rank. The allowed first-mode maps preserve U₁,U₂ and act by symplectic similitudes on the two spaces. To see this, the full-rank condition separates the two singular projective lines, and their different ranks prevent exchange. The usual relation on (x,x) gives the same first and second input map up to scalar, so each such pair of similitudes really extends to the quotient output. Their determinant signs multiply and each individual sign is the corresponding similitude multiplier to the power dim U_i/2. Therefore this family is rigid when both summand dimensions are multiples of four and flexible when either dimension is two modulo four. It has scalar pair adjoints in both cases. The symplectic group on each support acts independently, so a projective orbit with nonzero projection to a growing support already has exponentially many points. Taking both dimensions to grow forces every nonempty invariant projective point list on the tested mode to be exponentially large.

A singular example uses a single bivector of rank dim U−r for 1≤r≤b and rank at least six. It has no nonsingular bivector in K. Its big support gives the Pfaffian contribution, and the algorithm reads the r-dimensional quotient directly. This separates the criterion from the nonsingular-only test.

These results are informal. The construction closes the exact one-sign comparison on the stated class and gives a raw recognizer for the mark hypotheses. Unrestricted one-sign TI still needs a method for tensors without these alternating matches or with no large-rank bivectors in their small match kernels.


## An objectwise construction using every mark once

The same raw criterion gives a kernel reduction. It applies the same polynomial object map to each input independently. Fix the logarithmic threshold as a function of the common format. Let J_T be the set of all enumerated marks, which is nonempty on the domain. For j∈J_T write I_j for the image of its bivector P_j and Q_j=U/I_j. The dimension of Q_j is at most b.

The nonsingular bivector on I_j gives a distinguished volume ω_j∈det I_j. In an I_j basis it is the Pfaffian of the bivector's alternating coefficient matrix times the wedge of that ordered basis. This description is independent of the chosen basis by Pfaffian congruence. It sends P_j to a vector without choosing a square root or dividing by a factorial. Use the canonical determinant isomorphism det I_j⊗det Q_j≅det U to choose η_j in det Q_j by requiring that ω_j⊗η_j maps to the raw standard volume of U. In adapted frames this is an explicit nonzero scalar times the wedge of the quotient basis. More precisely the scalar is the inverse of the bivector Pfaffian on I_j times the inverse determinant of the full adapted frame. Use det(0)=F for a zero-dimensional quotient.

If a transporter with tested map a carries j to j', it sends ω_j to ω'_(j') exactly. Functoriality of the determinant isomorphism now says that the induced quotient map sends η_j to det(a) η'_(j'). This is the source of the orientation constraint in the object map below.

Build a bounded-order mixed tensor system as follows.

* Keep the original tensor and include the split coordinate algebra D=F^(J_T), with its unit and actual multiplication. Its primitive idempotents e_j can only be permuted.
* Include the map D×U→V taking (e_j,x) to f_j(x). Include the map D×U*×U*→F giving the alternating coefficients of P_j at e_j. The target scalar is fixed and the dual mode is linked to U by its evaluation. These two maps force the induced permutation of D to be the exact mark correspondence.
* Include X=⊕_j Q_j with the diagonal D-action. The map D×U→X taking (e_j,x) to the actual quotient of x in Q_j forces the component maps on X. It uses the corresponding summand of X as output.
* Include the unital associative algebra Y=∏_j Λ*(Q_j) with the D-action by the corresponding factor idempotents. Mark the degree-one inclusion X→Y. Any allowed algebra map then restricts in each factor to the actual exterior-power action, because the unit and the degree-one generators determine the algebra map. Mark the single vector Σ_j η_j in Y.

All components are of order at most three with fixed scalars, or can be included in a constant tensor signature by the ordinary compiler. There are constantly many sorts and relations. The label permutation is forced by the maps carrying f_j and P_j, and every actual transporter induces a bijection on marks. Under this bijection the distinguished sum has one nonzero component in every factor of Y. Compatibility with the sum therefore forces det(a)=1. Conversely a positive transporter induces the actual maps on all auxiliary sorts and preserves the marked sum by the volume identity. Thus the output objects are ordinarily isomorphic exactly when their raw inputs are one-sign isomorphic.

The size is polynomial because the number of marks is at most 3^(2b), each exterior algebra has dimension at most 2^b, and the remaining maps are explicit coefficient tables of bounded order. Different original raw formats can be distinguished by including their format as a fixed structural tag. This proof uses only the promises on the source class and their invariance, with no oracle calls or enumeration of a stabilizer.
