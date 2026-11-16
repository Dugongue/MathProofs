# Exact local quivers over finite chain rings

**Theorem.** Let $Q$ be a finite quiver with named arrows and vertices, $k$ a finite field, and $M\ne0$ a $k$-representation. Suppose the associative algebra $B=\operatorname{End}_Q(M)$ is semisimple. Let $R$ be one of the explicitly encoded finite chain rings $\mathbb Z/p^e\mathbb Z$, with $k=\mathbb F_p$, or $k[t]/t^e$. There is a deterministic polynomial-time construction of a finite free $R$-algebra $\mathcal B$ reducing to $B$, and an affine slice for all free $R$-representations with reduction identified with $M$. Each raw lift normalizes to unique slice coordinates by a specified gauge congruent to the identity. The raw transporter of two lifts is in explicit bijection with the $\mathcal B^\times$-transporter of their slice coordinates. This transfers every transporter, and the exact number of them, over the given coefficient ring. No field factorization or scalar extension is needed. The all-zero dimension vector is trivial.

The slice representation reduces to the usual local $\operatorname{Ext}^1$ representation and includes nonsplit endomorphism fields. The premise concerns the endomorphism algebra itself, so it also covers a brick with endomorphism ring $k$ whose representation is not semisimple. For path relations, restricting the equations to the affine slice gives the same transporter statement on their zero locus, with the original degree bound for the matrix-entry equations. A separate result below gives deterministic polynomial-time exact counting of free fixed-arrow isomorphisms over these rings with arbitrary residue.

## 1. Split the derivative over the endomorphism algebra

Write $\pi$ for $p$ or $t$. With $M_a:M_{s(a)}\to M_{t(a)}$, use
$$
 C^0=\bigoplus_v\operatorname{End}_k(M_v),\qquad
 C^1=\bigoplus_a\operatorname{Hom}_k(M_{s(a)},M_{t(a)}),\qquad
 (dX)_a=X_{t(a)}M_a-M_aX_{s(a)}.
$$
The two spaces are $B$-bimodules by composition at the two endpoints. The differential is bimodule-linear because every element of $B$ commutes with the arrow maps on the appropriate sides, and its kernel is $B\subset C^0$.

The quotient $C^1/\operatorname{im}d$ is $\operatorname{Ext}^1_Q(M,M)$ with its natural bimodule actions. For an extension of $M$ by $M$, choose vector-space splittings at the vertices. Each arrow has two diagonal copies of $M_a$ and one free off-diagonal block. Changing the splittings adds a vector in $\operatorname{im}d$. This also describes the left and right actions. Here $\operatorname{Ext}^1_Q$ is for the quiver without relations.

A semisimple finite algebra over a finite field is separable, with semisimple enveloping algebra $B\otimes_k B^{\rm op}$. Consequently there are bimodule splittings
$$
 C^0=B\oplus K,\qquad C^1=dK\oplus E.
$$
Find them by solving linear equations for retractions. For example, ask for a linear map $C^0\to B$ that is the identity on $B$ and commutes with left and right multiplication by each member of a basis of $B$. The splitting of $dK\subset C^1$ is the same computation.

For $M=\bigoplus_i S_i\otimes_k k^{m_i}$ with distinct simple $S_i$ and $\operatorname{End}(S_i)=k$, the $i,j$ block of $E$ is $\operatorname{Ext}^1(S_j,S_i)\otimes_k\operatorname{Mat}_{m_i,m_j}(k)$. This is the usual split local quiver. With nonsplit summands the corresponding blocks use the $\operatorname{End}(S_i)$-$\operatorname{End}(S_j)$ bimodules of extensions. The table of $B$ and the two actions on $E$ are a model of this description over $k$, independent of choosing a splitting field. [Le Bruyn–Procesi, semisimple representations of quivers](https://doi.org/10.1090/S0002-9947-1990-0958897-0)

## 2. Construct a common center and preserve the splittings

In equal characteristic take constant scalar extensions of all this data. The following layer argument also works in mixed characteristic. Let $R_j=R/(\pi^j)$.

Lift $B$ to a free unital associative $R$-algebra $\mathcal B$ on a basis including $1$. At each step lift the multiplication constants from $R_j$ to $R_{j+1}$, retaining the unit. The defect $(xy)z-x(yz)$ is in the layer $\pi^j/\pi^{j+1}$, identified with $k$. Three arguments from the residue suffice to calculate it because the defect vanishes modulo $\pi^j$. Regard it as a normalized Hochschild three-cochain of $B$ with coefficients in $B$. The five terms of its differential cancel on expanding the two bracketings, so the defect is a cocycle. Adding a normalized two-cochain in this layer to the multiplication changes that defect by minus its Hochschild differential. Positive Hochschild cohomology of $B$ with any bimodule coefficients vanishes because $B$ is projective over its semisimple enveloping algebra. Thus a linear solve corrects every layer.

Lift the residual actions of $B$ on the vertices to $\mathcal B$-actions on the standard free $R$-modules $\mathcal V_v$. Given a tentative linear lift $\rho$ with the unit equation, its multiplicativity defect $\rho(x)\rho(y)-\rho(xy)$ is a two-cocycle in the new layer, with coefficients in $\operatorname{End}_k(M_v)$. This follows by associativity of the algebra and of the endomorphism products. Adding a one-cochain to $\rho$ adds its Hochschild differential to the defect, so a linear solve again corrects it. The combined map $\mathcal B\to\bigoplus_v\operatorname{End}_R(\mathcal V_v)$ is a split $R$-linear injection because its reduction has a full-rank minor.

The same argument lifts intertwiners. For free modules $P,L$ with already lifted actions, the defect of a tentative map $f$ is $x\mapsto\rho_L(x)f-f\rho_P(x)$. Modulo the next layer it is a one-cocycle of the residual algebra with coefficients in $\operatorname{Hom}_k(\overline P,\overline L)$. Add a zero-cochain correction to kill it. Thus all arrows lift to $\mathcal B$-linear maps $\mathcal M_a$, giving a common center $\mathcal M$ for comparison.

Lift the two bimodule retractions by applying intertwiner lifting to $\mathcal B\otimes_R\mathcal B^{\rm op}$, whose residue is separable. First lift $C^0\to B$ to a bimodule map. Its composite with the embedding of $\mathcal B$ is invertible since it is the identity upon reduction. Postcompose with the inverse of this composite and take the kernel $\mathcal K$. The lifted differential $d_{\mathcal M}$ is still bimodule-linear. Next lift a residual left inverse $C^1\to K$ of $d|_K$ to a bimodule map $\mathcal C^1\to\mathcal K$. Adjust it by the inverse of its composite with $d_{\mathcal M}|_{\mathcal K}$, and take the kernel $\mathcal E$. This yields
$$
 \mathcal C^0=\mathcal B\oplus\mathcal K,\qquad
 \mathcal C^1=d_{\mathcal M}\mathcal K\oplus\mathcal E.
$$
The kernels are free because they are direct summands of finite free modules over a local ring. Find bases by reducing the projections of ambient basis vectors and choosing independent columns. The modules, cochain systems, and output tables have sizes bounded by fixed polynomials in the input dimensions. There are $e-1$ layers. In the standard encodings with the modulus or full coefficient length explicit, these operations have polynomial bit complexity. [Gerstenhaber–Schack, relative Hochschild cohomology](https://www2.math.upenn.edu/~mgersten/papers/Barrfest.pdf)

## 3. Normalize all orders and identify the full transporter

The product group $G(R)=\prod_v\mathrm{GL}(\mathcal V_v)$ acts by $(gX)_a=g_{t(a)}X_a g_{s(a)}^{-1}$. Its subgroup $H(R)=\mathcal B^\times$ fixes $\mathcal M$ and preserves $\mathcal E$.

Every lift $X$ of $M$ has unique normalized parameters
$$
 X=(1+u)\cdot(\mathcal M+z),\qquad u\in\pi\mathcal K,\quad z\in\pi\mathcal E.
$$
Start with $u=z=0$ modulo $\pi$ and proceed modulo higher powers. If parameters are found modulo $\pi^j$, pick provisional compatible lifts. Changing them by $\pi^j\Delta u,\pi^j\Delta z$ changes the residual in the next layer by $d\Delta u+\Delta z$. All cross terms with $u,z$ vanish in this layer because these parameters vanish modulo $\pi$. The residual splitting of $C^1$ gives exactly one correction pair, proving existence, uniqueness, and the algorithm.

Every $g\in G(R)$ reducing to $B^\times$ factors uniquely as $g=(1+u)h$ with $u\in\pi\mathcal K$ and $h\in H(R)$. Start with its given residue $h_0$, which lifts to a unit of $\mathcal B$ because the reduction has nilpotent kernel. Refine the parameters layer by layer. The correction map at each stage is $(\Delta u,\Delta h)\mapsto\Delta u h_0+\Delta h$. It is invertible since right multiplication by $h_0$ acts invertibly on $K$, and $C^0=K\oplus B$.

If $g$ carries $\mathcal M+z$ to $\mathcal M+z'$, its reduction belongs to $B^\times$. Write $g=(1+u)h$. Then its image is $(1+u)\cdot(\mathcal M+h\cdot z)$. Uniqueness of normalization gives $u=0$ and $h\cdot z=z'$. Conversely every such $h$ is a raw transporter. Thus for raw normalizations with parameters $u_X,z$ and $u_Y,z'$, the full transporter bijection is
$$
 h\longmapsto (1+u_Y)h(1+u_X)^{-1}.
$$
If the input reductions are only known to be isomorphic, find one residue isomorphism by the fixed-arrow module isomorphism algorithm and lift its vertex matrices to align them. Nonisomorphic reductions imply nonisomorphic lifts. Semisimplicity of $B$ can be tested by the deterministic radical algorithm. [Chistov–Ivanyos–Karpinski, constructive module isomorphism](https://theory.cs.uni-bonn.de/marek/publications/85169-cs.pdf) · [Cohen–Ivanyos–Wales, radical algorithms](https://doi.org/10.1016/S0022-4049(97)00010-8)

Relations in a bound quiver transform by conjugation at their endpoints. The groupoid equivalence therefore restricts to their zero locus after substituting $\mathcal M+z$. In mixed characteristic the common center can violate the relations, and the resulting equations may have a nonzero constant term. The substitution remains affine-linear in the slice coordinates.

## 4. Exact deterministic counts for arbitrary reduction

For an arbitrary free fixed-arrow $R$-representation $X$, let $S=\operatorname{End}_Q(X)$ and let $F$ be its image in the endomorphism algebra of the reduction. Compute generators of $S$ and its size from the linear commutation equations by local Smith elimination. At each step choose an entry of least valuation, normalize it to a power of $\pi$, clear its row and column by divisibility, and recurse while tracking basis changes. Reduction of generators followed by elimination gives a basis of $F$ and $|\ker(S\to F)|=|S|/|F|$. The kernel is nilpotent because it consists of matrices divisible by $\pi$. Reduction of units is surjective with kernel $1+\ker(S\to F)$. Hence
$$
 |\operatorname{Aut}_Q(X)|=|\ker(S\to F)|\,|F^\times|.
$$
The number of isomorphisms from $X$ to $Y$ is zero if inequivalent and is this same number otherwise. Finite-ring module isomorphism is already deterministically polynomial time. To apply it, compute the linear span of the algebra generated by all arrow matrices and vertex idempotents on the direct sum of the two modules. Close the span under multiplication by generators. There are at most $e(\sum_v\dim_R(X_v\oplus Y_v))^2$ strict increases, as each adds at least a factor of $|k|$ to the order. Smith elimination computes generators of the span at each step and its presentation. In invariant additive cyclic coordinates give the multiplication table and both actions by linear solves. This meets the input requirements of finite-ring module isomorphism. [Ciocănea-Teodorescu](https://arxiv.org/abs/1512.08365)

Here is a factorization-free computation of $|F^\times|$. Compute the Jacobson radical $J$ of $F$, set $A=F/J$, and let $Z=Z(A)$ be the semisimple center. We get $|F^\times|=|k|^{\dim_k J}|A^\times|$. To group the field factors of $Z$ by the rank of $A$ over them, consider the current $Z$-module quotient of $A$. Choose a nonzero $v$, compute its annihilator ideal $I$, then find the identity $e_I$ of $I$ by imposing $e_I x=x$ on its basis with $e_I\in I$. The support of $Zv$ is $1-e_I$, and its rank is one on each supported field. Quotient by $Zv$ and iterate. Refine the partition of $1$ by the resulting support idempotents and count how many contain each part. These counts give the fieldwise ranks. There are at most $\dim_k Z$ nonzero parts and at most $\dim_k A$ iterations. A rank $r^2$ corresponds to matrix factors of size $r$. This is the support-idempotent procedure used in the earlier MathProofs Hochschild recovery work.

On a rank-$r^2$ center part, let $\Phi(x)=x^{|k|}$. For $1\le l\le\dim_k Z$ compute $w_l=\dim_k\ker(\Phi^l-1)$, which equals $\sum_i\gcd(l,f_i)$ for the field factor degrees $f_i$. Let $m_b$ count degrees divisible by $b$. Using $\gcd(l,f)=\sum_{b\mid l,\ b\mid f}\varphi(b)$ yields a triangular recursion
$$
 \varphi(l)m_l=w_l-\sum_{b\mid l,\ b<l}\varphi(b)m_b .
$$
Descending subtraction of strict multiples gives the number of factors of each exact degree. A factor of size $r$ over order $q^f$ contributes $\prod_{j=0}^{r-1}(q^{fr}-q^{fj})$ units. Multiply all contributions and the kernel sizes. Frobenius powering, linear solves, divisor computations up to $\dim_k Z$, and output bit lengths are polynomial in the input.

## Scope

The concrete results are an effective all-orders local quiver normalization in equal and mixed characteristic, a transporter bijection, and an exact counting algorithm. The arrow labels remain fixed. An arbitrary change of basis in an arrow family, as in ordinary tensor isomorphism, also acts on the controls used to locate the residue representation and its endomorphisms. The classical local-quiver tangent description and finite-ring decision/search algorithms are prior work. Publication priority for the stated refinements is unverified. These proofs are informal.
