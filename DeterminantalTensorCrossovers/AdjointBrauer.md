# Recognizing matrix multiplication tensors and their arithmetic forms

Let $k$ be a field. Use the ordered bilinear convention $T:X\times Y\to Z$ for ordinary three-tensor isomorphism. The format of rectangular matrix multiplication $M(a,b,c)$ is $(ab,bc,ac)$. All integers $a,b,c$ are positive.

**Theorem 1.** Given an explicit tensor of this format, one can test deterministically in polynomially many field operations whether it becomes isomorphic to $M(a,b,c)$ over an algebraic closure. This test works in every characteristic. For tensors that pass, the two-sorted adjoint algebra in (1) is central simple of degree $c$. Two passing tensors are isomorphic over any extension $L/k$ exactly when their adjoint algebras are isomorphic after tensoring with $L$. Each Brauer class of index dividing $\gcd(a,b,c)$ occurs, and two passing tensors over $k$ are isomorphic precisely when their classes agree.

In particular over every explicitly presented finite field the geometric test decides equivalence to the original matrix multiplication tensor in deterministic polynomial bit time, uniform in the characteristic. Over a number field the test and the Brauer criterion give exact extension behavior, including an all-place local–global principle. The result complements the randomized reductions between determinant equivalence, full matrix algebra isomorphism, and isomorphism of matrix multiplication tensors. [Murthy–Nair–Saha](https://doi.org/10.4230/LIPIcs.MFCS.2020.72)

## The linear reconstruction

For $x\in X$ write $T_x(y)=T(x,y)$. Compute
$$
D_T=\{(P,Q)\in \operatorname{End}(Z)\times\operatorname{End}(Y):
                  P T_x=T_x Q\quad \text{for every }x\in X\}.
\tag{1}
$$
This is a unital algebra under componentwise composition. A change of bases in the tensor conjugates both components and so identifies the algebras. The defining equations are linear in $P,Q$ and commute with field extension.

For standard $M(a,b,c)$, split $Y$ and $Z$ into $b$ and $a$ rows, respectively. The slice corresponding to the $ij$ matrix unit carries the $j$-th row of $Y$ identically to the $i$-th row of $Z$ and kills the others. The intertwiner equation for all $i,j$ forces both $P$ and $Q$ to be block diagonal and all their diagonal row actions to be the same endomorphism of $k^c$. Indeed, comparing input rows other than $j$ kills $Q_{j\ell}$ for $\ell\ne j$, and comparing output rows other than $i$ kills $P_{\ell i}$ for $\ell\ne i$. The remaining row equality identifies $P_{ii}=Q_{jj}$. Thus $D_T\simeq M_c(k)$ in this convention.

A finite-dimensional unital $k$-algebra $D$ is central simple if and only if
$$
D\otimes_k D^{\mathrm{op}}\longrightarrow \operatorname{End}_k(D),
\qquad u\otimes v\longmapsto [z\mapsto uzv]
\tag{2}
$$
is a linear isomorphism. If it is surjective, any two-sided ideal is invariant under every endomorphism, so the algebra is simple. A central element then acts by an endomorphism commuting with every endomorphism and must be scalar. Conversely for a central simple algebra extend to an algebraically closed field where it is a full matrix algebra. Both sides and the map commute with base extension. Left and right multiplication by matrix units yields matrix units for the endomorphism space there. This proves (2) and makes it a single rank test in every characteristic. [Stacks Project, central simple algebras](https://stacks.math.columbia.edu/tag/0748)

The algorithm tests that $x\mapsto T_x$ is injective, that $\dim_kD_T=c^2$, and that (2) has full rank for $D_T$. Structure constants in (2) are obtained by multiplying pairs in a basis from (1) and solving linear systems. The tests are necessary by base change to the standard tensor. If all pass, write $D_T=M_s(\Delta)$ with division algebra $\Delta$ of degree $\delta$ and $s\delta=c$. Its unique simple left module has $k$-dimension $c\delta$, and the endomorphism algebra of this module has $k$-dimension $\delta^2$. The $D_T$-module structures on $Y,Z$ are their actions by $Q,P$, respectively. Their multiplicities of the simple module are $b/\delta,a/\delta$, so $\delta\mid a,b,c$. Therefore
$$
\dim_k \operatorname{Hom}_{D_T}(Y,Z)=(a/\delta)(b/\delta)\delta^2=ab.
$$
The slices all belong to this Hom space, and injectivity of the slice map identifies $X$ with the whole space. The tensor is exactly evaluation of all $D_T$-linear maps $Y\to Z$. After splitting $D_T$, standard simple-module coordinates identify this evaluation with $M(a,b,c)$. This proves recognition.

If an algebra isomorphism $D_T\to D_{T'}$ is given, transport the actions of $D_{T'}$ along it. Semisimplicity and the dimensions give a $D_T$-linear isomorphism on each of $Y,Z$ with the corresponding space for $T'$. These maps induce the required isomorphism on $X$ via the full Hom spaces. Conversely every tensor isomorphism identifies the two adjoint algebras by (1). The proof works verbatim after any field extension. Since equal-degree central simple algebras are isomorphic precisely when their Brauer classes are equal, this gives the criterion. If the Brauer class has index $\delta\mid\gcd(a,b,c)$, choose the corresponding degree-$c$ matrix algebra over its division representative, take the indicated direct sums of the simple module, and use evaluation. After scalar extension this tensor becomes standard. Its adjoint algebra contains the chosen degree-$c$ algebra, and the dimensions agree by the calculation on the split standard tensor, so the chosen class occurs. [Stacks Project, Brauer groups](https://stacks.math.columbia.edu/tag/074J)

For finite fields all central simple algebras split. Field operations in a supplied polynomial-basis representation cost polynomial bit time in the encoding size. The algorithm only computes kernels, structure constants and ranks. It never needs to find an invertible matrix slice, factor a polynomial, or find a square root.

## Exact extension behavior over number fields

For passing tensors over a number field $k$, put $\alpha=[D_T]-[D_{T'}]$. Over a finite extension $L/k$, the tensors are isomorphic exactly when for each place $w$ over $v$,
$$
[L_w:k_v]\,\operatorname{inv}_v(\alpha)=0\quad\text{in }\mathbb Q/\mathbb Z .
\tag{3}
$$
The formula also applies to the real and complex places with their local invariant conventions. Indeed (3) expresses vanishing of the local Brauer invariants of $\alpha_L$, which is equivalent to vanishing of the global class by Albert–Brauer–Hasse–Noether. In particular all local isomorphisms over $k$ imply a global one. The minimum degree of an extension giving isomorphism is exactly $\operatorname{ind}(\alpha)$: a maximal subfield of the division representative splits it and has degree its index, while the index divides the degree of every finite splitting field. For number fields the index equals the period, the least common multiple of its local invariant denominators. It divides $\gcd(a,b,c)$. Every divisor occurs by choosing a Brauer class with opposite invariants of that denominator at two finite places and comparing the resulting form to the split tensor. This is a complete field-change result on these tensor formats and this geometric orbit. [Grochow–Qiao, Part I, field-change question](https://arxiv.org/abs/1907.00309) · [Albert–Brauer–Hasse–Noether and local invariants](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

## Direct sums, Brauer classes, and an unbounded genus at fixed format

**Theorem 2.** Consider ordinary tensors over $k$ which become finite direct sums of ordered rectangular matrix multiplication tensors over an algebraic closure. Assume their adjoint algebra (1) has split center, meaning a product of copies of $k$. Such tensors are classified by their multiset of ordered triples $(a_i,b_i,c_i)$ decorated by a Brauer class of index dividing $\gcd(a_i,b_i,c_i)$ for each triple. For any number field and any even $t\ge4$, in the fixed format $8\times8\times8$ there is an everywhere locally isomorphic family of $2^{t-2}-1$ pairwise inequivalent tensors with split adjoint center, each geometrically the sum of two copies of $M(2,2,2)$. Within the split-center class in this theorem, no format with a side below eight has local–global failure.

For a direct sum over an algebraic closure the off-diagonal components of both adjoint maps vanish. In fact choose a slice supported in one multiplication summand. Its images, as the slice varies within that summand, span its whole output. The intertwiner identity forces any block of $P$ from that output to another summand to vanish. Its collective kernel in its own input is zero, so any block of $Q$ into that input from another summand also vanishes. Repeating for all summands proves that the adjoint algebra is the product of the individual matrix adjoint algebras. The slice map still identifies $X$ with the full Hom between $Y,Z$ as modules over this product.

These conclusions about dimensions and the slice identification descend. The algebra $D_T$ with split center is a product of central simple factors: the primitive center idempotents split over $k$, and the corresponding factor becomes a full matrix algebra over the algebraic closure. Read $c_i$ as the degree of that factor and read $b_i,a_i$ from the dimensions $b_ic_i,a_ic_i$ of their $Y,Z$ modules. Any isomorphism permutes the factors, preserving the ordered triple and Brauer class. Conversely matching those data identifies the adjoint factors and modules, hence the evaluation tensors. Each multiset is realizable by the construction above applied one summand at a time. This proves the classification, over $k$ and over all its field extensions.

For the arithmetic family fix $t$ distinct finite places of the number field. For every unordered partition into two nonempty even subsets $S,S^c$, choose the two quaternion Brauer classes with invariant $1/2$ at the respective subset and zero at other places. Existence follows from the sum-zero condition in Albert–Brauer–Hasse–Noether. Form the two corresponding $M(2,2,2)$ twists and take their direct sum. At each chosen place the unordered local classes are exactly the split and the quaternion class. At all other places they are both split. Thus the tensor is locally independent of the partition. The global multiset of classes remembers the partition, so the tensors are pairwise inequivalent. There are $2^{t-1}$ even subsets, two of them empty or full, and passing to unordered complements yields $2^{t-2}-1$.

Finally, within a fixed ordered shape if the gcd is one, every class is split. If the gcd exceeds one, all three dimensions of a block are at least four. Two blocks of that shape require every side of the full tensor to be at least eight. With a side below eight, every shape that admits a nontrivial Brauer class occurs at most once. Local tensor isomorphisms then equate the local invariants for that shape at every place, so the global comparison follows from Albert–Brauer–Hasse–Noether. This proves the sharp format statement in the stated class.

## Recognition and classification of every geometric direct sum

The same algorithm recognizes arbitrary geometric direct sums of rectangular matrix multiplications, even when the summand formats are absent from the input and the adjoint center is nonsplit. For nonzero tensors require conciseness in the three modes: the slice map $X\to\operatorname{Hom}_k(Y,Z)$ is injective, the slices have zero common kernel in $Y$, and the sum of their images is $Z$. Test that the slice map identifies $X$ with $\operatorname{Hom}_{D_T}(Y,Z)$ by linear equations. Finally test that $D_T$ is separable over $k$ by solving for an element $\sum_i u_i\otimes v_i$ in $D_T\otimes_k D_T$ satisfying
$$
\sum_i u_i v_i=1,\qquad
\sum_i au_i\otimes v_i=\sum_i u_i\otimes v_i a\quad(a\in D_T).
\tag{4}
$$

These linear conditions are necessary for the standard direct sum. Its adjoint algebra is a product of full matrix algebras as shown above. On a matrix factor one can take $\sum_i E_{i1}\otimes E_{1i}$, and add these elements over the separate factors. Necessity descends because the equations (4) are linear. For sufficiency, extend scalars to an algebraic closure. For any submodule of any left $D_T$-module and any linear projection $p$ onto that submodule, (4) gives a $D_T$-linear projection $w\mapsto\sum_i u_i p(v_iw)$. Thus all submodules split and $D_T$ is a product of matrix algebras over the algebraic closure. Let one such factor have size $c_i$ and module multiplicities $b_i,a_i$ in $Y,Z$. Conciseness implies both multiplicities are positive: if a factor occurs in just one of the two modules then its input summand is in the common kernel or its output summand is absent from the sum of the images. Each factor acts nontrivially on at least one of the two modules by the faithful pair in (1). Evaluation of the full Hom space is now exactly the direct sum of the corresponding $M(a_i,b_i,c_i)$. This proves recognition by deterministic linear algebra over every field.

The full classification over $k$ replaces each split center entry in Theorem 2 by a finite separable field $L_i/k$. In detail, the center of the separable algebra $D_T$ is a finite étale $k$-algebra, hence a product of fields $L_i$. Its corresponding simple factors are central simple over their centers. Record for each $i$ the field $L_i$, the ordered triple of the block sizes computed over $L_i$, and a Brauer class over $L_i$ of index dividing $\gcd(a_i,b_i,c_i)$. Compare two such lists up to permutation and $k$-isomorphism of the matched fields transporting the Brauer classes. Necessity follows from (1), which preserves both module dimensions over the center field. For sufficiency align the algebras and then their modules by semisimplicity, as in Theorem 1. For construction use the evaluation tensor of Theorem 1 over each $L_i$, regard it as a bilinear map on the restricted $k$-spaces, and take the direct sum. After scalar extension to an algebraic closure the $[L_i:k]$ embeddings split that restricted tensor into independent copies of its geometric block. Scalar extension of any of these tensors is given by decomposing each $L_i\otimes_k L$ into fields and restricting the Brauer class to those fields. This recovers all comparisons after arbitrary extensions, including inseparable extensions. [Stacks Project, separable and semisimple algebras](https://stacks.math.columbia.edu/tag/074J)

## Deterministic comparison over arbitrary finite fields

For every explicitly presented finite field $k=\mathbb F_q$, the algorithm also decides isomorphism between any two passing direct sums in deterministic polynomial bit time in the tensor encodings and $\log q$. The factors of the center need not be given. Over finite fields the Brauer labels are all zero, so it suffices to recover the multiset of ordered triples and center field degrees. This can be done without factoring.

First compute the center $C$ by linear equations. Compute its decomposition into the strata on which $D_T$, $Y$, and $Z$ have specified ranks as $C$-modules. For each of these modules, use a $k$-basis as $C$-generators and compute the kernel of the resulting presentation as a $k$-linear map. A $k$-basis of this kernel generates it over $C$, giving a matrix presentation. Gaussian elimination on that matrix over the finite étale algebra $C$ computes the rank strata. For a nonzero proposed pivot $p$, find $pC$ and $\operatorname{ann}(p)$ by linear algebra. A nonunit pivot gives $C=pC\oplus\operatorname{ann}(p)$. The two identity idempotents are the components of $1$, and $p$ is invertible on the first stratum and zero on the second. Continue elimination on both. Each split increases the number of nonzero strata, which is bounded by $\dim_k C$. The operations on each branch are ordinary elimination with invertible pivots. After treating the three modules, the ranks on a stratum are $c^2,bc,ac$, so they determine its ordered triple.

For a stratum of $k$-dimension $s$, write $m_e$ for the number of center factors of degree $e$ over $k$, for $1\le e\le s$. Let $F:C\to C$ be the $q$-power map on this stratum. It is $k$-linear and is computable by repeated squaring. For each $d=1,\ldots,s$ calculate
$$
f(d)=\dim_k\ker(F^d-I)=\sum_{e=1}^s m_e\gcd(d,e).
$$
On a degree-$e$ field the fixed elements form the degree-$\gcd(d,e)$ field. The arithmetic identity $\gcd(d,e)=\sum_{j\mid d,\ j\mid e}\varphi(j)$ gives
$f(d)=\sum_{j\mid d}\varphi(j)\sum_{e: \,j\mid e} m_e$.
Recover the sums over multiples by inversion over divisors, then recover the $m_e$ in decreasing order. The dimensions, matrix powers, sums, and modular field operations are all polynomial in the input lengths. This computes the full invariant from the preceding section without choosing primitive idempotents of fields of the same type.

Finally, for the single-block form comparison over an arbitrary field, the exact equivalence $T\simeq T'\iff D_T\otimes D_{T'}^{\mathrm{op}}\text{ is split}$ yields a deterministic many-one reduction to full matrix algebra isomorphism. In the reverse direction, for a central simple algebra $A$ of degree $n$, compare its multiplication tensor with $M(n,n,n)$. The adjoint of all left multiplication maps identifies with right multiplication by $A^{\mathrm{op}}$, using the identity map among the slices, so this comparison is equivalent to splitting $A$. Both reductions are direct rank and structure-constant computations.

## Verification and relation to determinantal geometry

The direct calculation in (1) applies the module-isomorphism viewpoint of linear determinantal presentations to the matrix slice family of a tensor. The pencil is evaluated as a full module Hom space, so its endomorphism data suffice to reconstruct the entire tensor. The arithmetic example replaces the single line bundle in the plane-curve argument by two central simple blocks and uses exact local permutations of their labels. The classification and algorithms have written proofs. Lean 4.33.0 independently checked the rectangular block calculation, with axiom propext. [Lean source](RectangularAdjoint.lean) Priority for this explicit combined classification, algorithm and fixed-format genus remains provisional.
