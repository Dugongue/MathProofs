# Determinant characters from quadratic factors with repeated spectrum

Informal proof. Fix an odd finite field $F=\mathbb F_q$, a fixed extension $K/F$, and fixed constants $d,r$. Consider a pair of square matrix pencils $M_A,M_B$, each with label dimension $u$ and matrix side $v$. The label spaces and both matrix spaces may have arbitrary input bases. The transport convention is
$$
M_B(fx)=hM_A(x)g^{-1}.
$$
We test whether an actual base-field transporter has
$$
(\det f)^a(\det h/\det g)^b=\eta,
\qquad \eta\in F^\times .
$$
The exponents $a,b$ are taken modulo $q-1$. For a balanced tensor of unit side residue, $a=-1,b=1,\eta=1$ is equivalent to SL-TI by scalar correction. The same test applies to the corresponding weighted characters encoded by triangular multiplication algebras.

Suppose the source determinant pencil $P_A=\det M_A$ is nonzero. Its absolute factors have degree at most $d$ and are defined over $K$, with arbitrary multiplicities. Two distinct factors are quadratic, with symmetric matrices $S_1,S_2$, and $S_2$ is nonsingular. Write $L=S_2^{-1}S_1$. For an irreducible $p$ of the minimal polynomial of $L$, let $e=\deg p$, and let $r_{p,s}$ be the number of primary blocks of length $s$ over $K[t]/p^s$. Put
$$
w=\max \bigl(\{r_{p,s}: a e s\text{ is odd}\}\cup\{0\}\bigr).
$$
Assume one of these two further conditions.

1. The number of distinct geometric factors is at most $r$.
2. For some $p$, its largest block length $s$ occurs once, and $P_A$ restricts nontrivially to $p(L)^{s-1}V_p$, where $V_p$ is the $p$-primary space.

Then there is an exact one-instance reduction to ordinary TI over $F$, with construction time and size polynomial in the input and $2^w$. The width condition permits Jordan blocks and arbitrarily large repeated multiplicities. Blocks of even length or even residue degree incur no exterior-power cost. The first condition is used for the matrix-mode determinant ratio. The second makes that ratio accessible even with arbitrarily many factors.

## Extract and align the two quadratic forms

Use deterministic bounded-degree factor recovery from the preceding MathProofs quadratic-pencil proof. The relevant part is recovery over a fixed field of definition. It obtains all absolute factors and multiplicities from polynomial-size line restrictions, bounded-degree interpolation, and Hensel root lifting. It allows arbitrarily many distinct factors when their degrees and common definition field are bounded. Only the source is promised, because ordinary equivalence forces the target to have the same factor properties. Both the factor extraction and the subsequent branching have a polynomial work bound outside the promise. An unsuccessful extraction can reject.

Choose the two source factors and try the ordered pairs of target quadratic factors. Try their similarity multipliers $\lambda_1,\lambda_2\in K^\times$ in each branch. There are polynomially many branches since $K$ is fixed. Their two equations are $f_K^{\mathsf T} S'_{i} f_K=\lambda_i S_i$, where $f_K$ is the extension of the actual base-field label map. Use constructive isometry of symmetric matrix tuples over fixed characteristic to find a reference $f_0$ for these two equations, or reject the branch. The reference satisfies only the two form equations. The final instance always keeps the original tensor. [Ivanyos–Qiao, Theorem 7](https://arxiv.org/pdf/1708.03495)

An allowed label map now has the form $f_K=f_0 u_0$, where $u_0$ preserves $S_2$ and commutes with $L$. Conversely these two conditions make $f_0u_0$ satisfy the two quadratic equations. This follows by substituting $S_1=S_2L$. Thus the remaining determinant in the label mode can be computed using only this isometry centralizer.

## Determinants on the primary multiplicity spaces

Write $B(x,y)=x^{\mathsf T}S_2y$. The operator $L$ is self-adjoint for $B$. Its distinct primary spaces are orthogonal, by applying the relatively prime primary projectors. Each $V_p$ is therefore nondegenerate for $B$. Set $N=p(L)|_{V_p}$. For every length $s$ use
$$
W_{p,s}=
\frac{\ker N^s}{\ker N^{s-1}+N\ker N^{s+1}},
\qquad
B_s(\bar x,\bar y)=B(x,N^{s-1}y).
$$
The displayed denominator is contained in the radical of this form on $\ker N^s$ by self-adjointness. For the reverse containment, if $x$ pairs to zero with that kernel, then $N^{s-1}x$ belongs to $(\ker N^s)^\perp=\operatorname{im}N^s$. Write $N^{s-1}x=N^sz$. This gives $x-Nz\in\ker N^{s-1}$ and $N^{s+1}z=0$. Thus $B_s$ is nondegenerate on $W_{p,s}$.

The space $W_{p,s}$ is a vector space over $E_p=K[t]/p$ via the induced operator. Its $E_p$-dimension is $r_{p,s}$, as is seen on each primary block. The operator action is self-adjoint for $B_s$, so $B_s$ is the trace to $K$ of an $E_p$-bilinear symmetric form. To see this, define the value of that form by the identities
$\operatorname{Tr}_{E_p/K}(c\,\widetilde B_s(x,y))=B_s(cx,y)$ for all $c\in E_p$. Perfectness of the finite-field trace pairing and self-adjointness give existence, symmetry and linearity on both variables. Nondegeneracy of $B_s$ implies nondegeneracy of $\widetilde B_s$. The map of $u_0$ on $W_{p,s}$ is an isometry of $\widetilde B_s$. In particular its $E_p$-determinant is a sign.

For $V_{p,j}=\ker N^j/\ker N^{j-1}$, the map $N:V_{p,j+1}\to V_{p,j}$ is injective with cokernel $W_{p,j}$. Its injectivity follows since $Nx\in\ker N^{j-1}$ implies $x\in\ker N^j$. All these maps commute with $u_0$. By telescoping determinants on these exact sequences and multiplying over the layers,
$$
\det_K u_0=\prod_{p,s}
 \operatorname{Norm}_{E_p/K}\bigl(\det_{E_p} u_0|_{W_{p,s}}\bigr)^s .
$$
The norm of a sign is its $e$-th power. Hence only the blocks with $a e s$ odd can affect $(\det u_0)^a$. Attach the $E_p$-exterior algebras only on these spaces, whose dimensions are at most $w$. Use the corresponding subquotients on the target in the frame supplied by $f_0$. The typed equations tie every induced action to the original $f$, so their top lines and field norms read the actual determinant. The known frame factor is $(\det f_0)^a$.

## Read the matrix-mode determinant ratio

Every actual transporter obeys $P_B(f_Kx)=\mu P_A(x)$ with $\mu=\det h/\det g$ in $F^\times$.

Under the bounded factor-count condition, try all matches of the normalized factor lists and their multipliers. There are constantly many choices over fixed $K,r$. If
$$
P_X=c_X\prod_i Q_{X,i}^{e_i}, \qquad Q_{B,i}(f_Kx)=\gamma_i Q_{A,i}(x),
$$
then $\mu=(c_B/c_A)\prod_i\gamma_i^{e_i}$. Include the individual factor conditions in the same branch. They can be attached as polynomial vectors in graded parts of the truncated symmetric algebra on the label dual. The multiplication maps tie the action on each graded part to the actual dual action. This uses no polarization identity or factorial division in small characteristic. The degree is fixed, so the tables have polynomial size.

Under the second condition, use the intrinsic subspace $U=N^{s-1}V_p$. The top quotient $V_p/\ker N^{s-1}$ identifies with $U$ and with $W_{p,s}$, since $s$ is the maximal length and $NV_p\subseteq\ker N^{s-1}$. Its $E_p$-dimension is one. The preceding argument shows $u_0|_U=\epsilon I_U$, $\epsilon\in\{1,-1\}$. Recover the leading terms of $P_A|_U$ and $P_B(f_0\,\cdot)|_U$ in a chosen basis of $U$ by multiplying the leading terms of the restricted bounded-degree factors, checking for zero factors. If $P_B(f_0\,\cdot)|_U=0$ or the two leading monomials differ, no transporter can satisfy the branch. Otherwise let their leading coefficients be $c_A',c_B'$. Homogeneity gives
$$
\mu=(c_B'/c_A')\epsilon^v .
$$
Include any $K$-line of $U$ and its target $f_0$-image to read $\epsilon$ directly. This part has polynomial cost even if the base-field dimension of $U$ is unbounded. The input test that $P_A|_U$ is nonzero is exact via the same factor restrictions.

## Compile the joint test

Run the original tensor equations and the auxiliary conditions in one typed system per branch. To use $K$ and the $E_p$ inside a same-field instance, include their coordinate multiplication with fixed field bases, and the respective scalar actions. In particular the map $K\times V\to K\otimes_F V$ ties every scalar-extended map to its original base transporter. The other determinant lines are connected through field norms, scalar multiplications and duals as in the previous residual bilinear-form proof. Calibrate the final product by the known factors and pin it to $\eta$. Every branch solution yields a genuine base-field transporter of the required character. Every qualifying original transporter supplies all induced maps for a matching branch. Uniform packing of typed systems followed by positive OR packing constructs one ordinary TI instance. Its size is polynomial in the input and $2^w$, since the remaining computations are polynomial and use a fixed field. [Chen–Grochow–Qiao–Tang–Zhang, tensor-system compiler](https://arxiv.org/html/2306.03135v2#S4)

## A growing family with large repeated multiplicity and one-dimensional terminals

Work over $F=K=\mathbb F_3$, and let $u=v=2m+1$, $m\ge3$. On $x,y\in F^m,t\in F$, take
$$
Q_1=\sum_{i=1}^m(x_i+y_i)y_i,\qquad
Q_2=\sum_{i=1}^m x_i y_i+t^2.
$$
They have ranks $2m$ and $2m+1$ and are absolutely irreducible. In the $x,y$ block the operator $L$ has eigenvalue one with $m$ length-two blocks. On $t$ it is zero with one length-one block. Indeed the difference of the first form and the second restricted to the $x,y$ block is the form on the $y$ variables alone, producing the nonzero square-zero shift from $y$ to $x$. Thus the preceding compiler has $w\le1$, even though the multiplicity $m$ of the repeated Jordan blocks grows without bound.

Realize the determinant pencil
$$
y_1^{m-2} y_2^{m-1} Q_1 Q_2
$$
using the direct sum of two arrowhead blocks, of respective sizes $m,m+1$. For a form $a\ell-\sum_{i=1}^s u_i v_i$, use the matrix with first row $(a,u^{\mathsf T})$, first column $(a,v)$, and bottom block $\ell I_s$. Its determinant is $\ell^{s-1}(a\ell-\sum u_iv_i)$. Use $\ell=y_1$ in $Q_1$ and $\ell=y_2$ in $Q_2$; negative coefficients are absorbed in $u_i,v_i$. In the odd block the extra term $t^2$ uses one extra pair $u_i=t,v_i=-t$. The resulting pencil is concise: the odd block sees every label direction, and there are invertible slices, for example $y_1=y_2=1$, $t=0$, remaining $y_i=0$, and $x_1+x_2=2$. This example lies within the first determinant-ratio condition and works in all independently changed bases.

The proof combines the earlier raw quadratic-factor and residual determinant constructions with the explicit symmetric forms on primary multiplicity spaces. It leaves universal Step 17 open. In particular, normalized multiplication tensors can have determinant pencils involving only their semisimple residues, so the required quadratic factors do not follow from triangular normalization.

## Removing the common field restriction

The two conditions in the theorem also work when the bounded-degree absolute factors have no fixed common field of definition. Recover the factors in separate finite fields and use local norms to read coefficients after linear restriction, as in the companion proof [An orientation test with factors in separate finite fields](../SLSeparateFactorFields/Proof.md). For the bounded factor-count condition the common field already has bounded degree, since Frobenius acts on a bounded number of normalized factors. For the scalar-socle condition work in the compositum $K$ of the two selected source factor fields and the two candidate target factor fields. This is of polynomial degree. Retain only matches whose individual source and target field degrees agree. A base-field linear change preserves the field of definition of a projective factor line, so no genuine match is lost. For each retained match $K$ is the field generated by the two source factor fields. The primary widths and the scalar-socle condition can therefore be checked over that field on the source.

Write $\lambda=\lambda_2$ and $\rho=\lambda_1/\lambda_2$. In a feasible branch
$$
 L_B f_K=\rho f_K L,\qquad
 f_K^{\mathsf T}S'_2 f_K=\lambda S_2.
$$
Enumerate $\lambda$ by the equations
$$
 \lambda^{u}=d_0^2\,\det S'_2/\det S_2,\qquad d_0\in F^\times.
$$
These follow from $\det f=d_0$ for some base-field value. When $L$ is not nilpotent, take any nonzero non-leading coefficient $c_i$ of its characteristic polynomial. If $c'_i$ denotes the matching coefficient for $L_B$, all feasible $\rho$ solve $\rho^i=c'_i/c_i$. The binomials have degree at most $u$, so factoring over fixed characteristic lists their roots in polynomial time. Test the full characteristic-polynomial scale equations. Ivanyos–Qiao's constructive isometry algorithm then applies over the represented field $K$ at fixed characteristic. Each such branch uses the same multiplicity-space proof as above. The computation of $c_A',c_B'$ on the selected subspace uses the individual factors after linear restriction and multiplies their leading terms by local Frobenius norms. A zero restriction of a factor is detected in its own field.

When $L$ is nilpotent, the characteristic polynomial supplies no bound on the set of $\rho$ values. Instead separate the two square classes in $K^\times$, represented by $1$ and a nonsquare. A nonsquare can be obtained from the discriminant of a deterministically constructed irreducible quadratic over $K$. For each representative $\rho_0$ and each enumerated $\lambda$, compute a form reference $f_0$ with $L_Bf_0=\rho_0 f_0L$ and $f_0^{\mathsf T}S'_2 f_0=\lambda S_2$, or reject that branch.

The following construction explains why one representative per square class suffices. Orthogonally split the nilpotent self-adjoint $L$ into cyclic chains. To construct one maximal chain of length $s$, choose $v$ with $B(v,L^{s-1}v)\ne0$. This exists because the symmetric form $B(-,L^{s-1}-)$ is nonzero in odd characteristic, and a basis vector or sum of two basis vectors finds it. The chain is nondegenerate by its anti-triangular Gram matrix. Replace $v$ by $a(L)v$, where $a(t)$ has constant coefficient one. Solve successively for the coefficients of $a$ so that $B(a(L)v,L^k a(L)v)=0$ for $k=s-2,\ldots,0$, in that order. At the equation for $k$, the new coefficient $a_{s-1-k}$ has coefficient $2 B(v,L^{s-1}v)$, and subsequent coefficients cannot affect the equation. This gives an anti-diagonal Gram matrix on the chain. Its orthogonal complement is $L$-invariant, so repeat.

For $\tau\in K^\times$ let $D_\tau$ act on $L^jv$ in a length-$s$ chain as multiplication by $\tau^{s-1-2j}$. It has determinant one, is an isometry (the anti-diagonal exponents cancel), and satisfies $L D_\tau=\tau^2 D_\tau L$. Thus for $\rho=\rho_0\tau^2$, encoding an allowed $f_K$ is equivalent to encoding
$$
f_K=f_0D_\tau u_0
$$
where $u_0$ is an isometry commuting with $L$. In particular, failure to find the reference for $\rho_0$ excludes its whole square class.

Introduce a $K$-line on which the transported map scales by $\tau$. Form its inverse-square line using duality and a multiplication map. Tying this line to the map with value $L$ on the source and $\rho_0^{-1}L_B$ on the target enforces $L_B f_K=\rho_0\tau^2 f_K L$. Keep the original tensor and the $S_2$ similarity restriction in the same branch. The actual action of $f_K$ on $W_{t,s}$ in the paired $f_0$-frames has determinant $\tau^{(s-1)r_{t,s}}$ times the determinant of $u_0$ there. Divide by that known power of the attached $\tau$ line before taking its contribution to the prescribed character. The $D_\tau$ action on the whole label space has determinant one, so this reconstructs the label factor exactly. If the scalar-socle condition is used, the actual map on $U$ in the $f_0$-frames is the scalar $\tau^{1-s}\epsilon$. Its line reads that full scalar and the matrix-mode coefficient ratio uses its $v$-th power.

These additions preserve polynomial size in the input and $2^w$. The exponent arithmetic uses polynomial-size powering diagrams, the multiplication and inverse-square conditions are linear or bilinear maps between attached sorts, and all fields have polynomial representation degree. The original label map remains over $F$, even when the reference and the extra lines use $K$. The square-class construction is needed only for the nilpotent ratio, where $E_p=K$. This proves the same one-instance reduction with repeated spectrum and separate fields, including the nilpotent case. The remaining hypotheses concern the available quadratic pair, its contributing residue widths, and the bounded factor-count or scalar-socle condition.

### Keeping the tensor-system signature fixed

Each branch can have polynomially many auxiliary spaces and equations. Collect its spaces in a direct sum and use the bilinear action of a label algebra $F^I$ to project to the individual spaces. Pin the label idempotents by an ordered basis map, whose coordinate space is itself pinned by a shift and a cyclic vector. For each type of bilinear operation, take one copy of its three spaces for each operation record. Tie these copies to the original spaces by the linear maps from the first direct sum to each argument or result sum, using the coordinate projection on each record. A second pinned label algebra on the records forces each copy to follow its original space. The maps now combine into one blockwise bilinear map per type. Linear maps and named vectors use the same construction, with fixed one-dimensional arguments for named vectors. Evaluation pairings handle duals. Thus the signature stays fixed, and the compiler costs polynomial time in the total explicit dimension. For determinant lines carrying only a sign in a field extension, the scalar on an attached subline over the base of the extension is the same sign. The degree parity gives its norm directly, without an exterior algebra of the full extension degree.

### Combining the branch tests

For two tests of equality of isomorphism types, the multiset identity
$$
\{(a,c),(b,d)\}=\{(a,d),(b,c)\}
$$
holds exactly when $a=b$ or $c=d$. Use ordered pairs and unordered pairs as different node types in a rooted expression tree. A balanced OR over polynomially many tests has logarithmic depth, so this encoding has polynomial size when unfolded. Use the label algebra $F^P$ of tree nodes and separate label algebras for relation records. Their primitive idempotents encode the node types and the colored edge incidences by linear maps. Give each tensor leaf the action of its label idempotent on the three sums of all the leaf mode spaces. An isomorphism preserves the labeled summands and is precisely a tree isomorphism with the indicated leaf tensor isomorphisms. The signature has a fixed number of maps, so the tensor-system compiler is applied once to the full tree. The ordered and unordered pairing construction follows [Jenner, Köbler, McKenzie and Torán](https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.190/Mitarbeiter/toran/completeiso.pdf).
