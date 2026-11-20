# Forcing the Pfaffian sign with colored relation tuples

The finite harmonic projection in the accompanying proof replaced the label sum by a sum over the relation space of the split Pfaffian factors. Here the polynomial-size object keeps individual relation data and their signs. This gives an ordinary lock on the same raw transporter even in a case where the integer average vanishes and odd raw automorphisms actually exist. [Alpöge–Buckmaster's character projection at the pinned revision](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L126-L151)

## Theorem

Use the raw pencil convention and one-dimensional alternating multiplier condition from [the finite character average](PfaffianHarmonicReadout.md). Suppose the normalized first-input Pfaffian is nonzero, splits over $F=\mathbb F_3$, and has even degree. Write it as $p_X=c_X\prod_{i\in I}\ell_i^{e_i}$ with distinct normalized factor lines. Put
$$ R_X=\{w\in F^I : \sum_i w_i\ell_i=0\},\qquad t=\dim R_X,\qquad I_{\rm odd}=\{i:e_i\text{ is odd}\} .$$
Assume some ordered $k$-tuple of vectors of $R_X$ has union support containing $I_{\rm odd}$, where $k\ge1$ is a fixed integer. Then on this source family:

- Testing the left determinant sign reduces to one ordinary tensor isomorphism instance.
- Testing all three signs reduces to one one-sign tensor isomorphism instance, on the original label determinant through the one-sign compiler.

The reduction is deterministic and takes time polynomial in the dense input length and $3^{kt}$. In particular it is polynomial for fixed $k$ and logarithmic global nullity. It inspects raw inputs, computes normalized multipliers and factors, and rejects failed target computations. Ordinary equivalence carries all the promised source properties to the target. The two tests enforce the original signs on a single common raw transporter.

## 1. A color that tracks an actual determinant

Let $X,Y$ be ordinarily isomorphic and fix any actual raw transporter $(P,Q,C)$ in
$$ M_Y(Cz)=P M_X(z)Q^{\mathsf T}.$$
Right multiplication by the normalized generators $B_X,B_Y$ gives a congruence up to a scalar $a\in F^\times$. The even Pfaffian degree removes $a$, so
$$ p_Y(Cz)=\det(P)\,p_X(z). $$
Unique factorization gives a bijection $\sigma:I_X\to I_Y$ preserving $e_i$ and units $\lambda_i$ such that
$$ \ell_{Y,\sigma(i)}(Cz)=\lambda_i\ell_{X,i}(z),\qquad
 \det P=(c_Y/c_X)\prod_i\lambda_i^{e_i} .$$
A vector $w\in R_X$ therefore maps to a unique relation $w'\in R_Y$ given by
$$ w'_{\sigma(i)}=\lambda_i^{-1}w_i.$$

For an ordered tuple $\mathbf w=(w^{(1)},\ldots,w^{(k)})\in R_X^k$, call it admissible if at least one $w_i^{(j)}$ is nonzero for every $i\in I_{\rm odd}$. Let $j_i(\mathbf w)$ be its first nonzero position at $i$. Set
$$ \gamma_X(\mathbf w)=c_X\prod_{i\in I_{\rm odd}}w^{(j_i(\mathbf w))}_i\in F^\times .$$
Admissible tuples are preserved as a set by actual transporters because zero coordinates, the order of the tuple slots, and the odd factor indices are preserved. Consequently
$$
 \gamma_Y(\mathbf w')/\gamma_X(\mathbf w)
 =(c_Y/c_X)\prod_{i\in I_{\rm odd}}\lambda_i^{-1}
 =\det(P).
$$
The second equality uses $\lambda_i^2=1$. Thus every transporter either preserves the colors of all admissible tuples or flips their colors simultaneously. The set is nonempty by hypothesis, so existence of a color-preserving extension is exactly the condition $\det P=1$. No imbalance of color-class cardinalities is needed.

## 2. A polynomial ordinary encoding

Construct the following marked tensor system keeping the original raw tensor and its three roles. View pencils as bilinear multiplication into a matrix role with the evaluation pairing fixing the scalar field and with dual roles as necessary. Keeping a dual role uses an ordinary evaluation pairing and forces the inverse transpose of the associated raw map.

1. Include the scalar line $F$ fixed by its multiplication. Include the coordinate algebra $A=F^I$ with coordinatewise multiplication, and its natural module $Z=F^I$ under coordinatewise action $A\times Z\to Z$. Algebra isomorphisms of $A$ permute the primitive idempotents. Its action forces the map on $Z$ to send each coordinate line to the corresponding permuted line.
2. Include the single evaluation pairing $Z\times W\to F$ defined on the coordinate basis by $E(e_i,z)=\ell_i(z)$, where $W$ is the raw label space and its actual map is $C$. Preservation gives $g_Z(e_i)=\lambda_i^{-1}e_{\sigma(i)}$, with the same scales as in Section 1. Indeed nonproportionality ensures that the permutation here is forced by the actual map on the factor lines. The factor multiplicities then match by the covariance equation and unique factorization. One may include marks $\sum_{e_i=d'}e_i$ on $A$ for each $1\le d'\le\deg p_X$ to record the multiplicities directly.
3. Include the coordinate algebra $F^\mathcal W$ indexed by the admissible ordered tuples $\mathcal W$. Include for each $j=1,\ldots,k$ the linear map $F^\mathcal W\to Z$ sending the primitive idempotent of $\mathbf w$ to $w^{(j)}$. These maps determine the tuple permutation, since the vector of all their values uniquely identifies the tuple. Mark the vector $\sum_{\gamma_X(\mathbf w)=1} e_\mathbf w$ on this algebra. A permutation of idempotents preserves the mark exactly when it preserves the two colors.

The same construction applies to the target computed from its raw tensor. Every raw transporter with $\det(P)=1$ has the indicated extension on every new role, and the displayed maps force any extension to preserve $\det(P)=1$. Thus an ordinary simultaneous tensor-system comparison solves the one-sign problem. All maps have order at most three, including the algebra products and evaluation, and every space and map has size polynomial in $L$ and $3^{kt}$. In particular constructing the entire tuple index set by enumeration has this cost. The ordinary tensor-system compiler for order at most three gives one ordinary TI instance. [Ordinary compiler, Chen–Grochow–Qiao–Tang–Zhang §4](https://arxiv.org/html/2306.03135v2#S4)

For the three-sign problem, take determinants in the raw alternating multiplier equation. The scalar has even exponent equal to the matrix size, so every raw transporter satisfies
$$ \det P = (\det B_Y/\det B_X)\det Q . $$
This identity by itself permits dropping one of the matrix sign constraints while retaining the other. If $\det B_Y\ne\det B_X$, reject the three-sign comparison. Otherwise the ordinary lock on $P$ simultaneously fixes the sign on $Q$. Designate the raw label role in the prior one-sign compiler, so the remaining physical sign demands $\det C=1$ on the same original map. This proves the $P_3$ to $P_1$ assertion. Requiring equal corresponding sizes before compilation is valid since any admissible raw isomorphism induces bijections of all role bases. [Retaining a physical sign in the tensor-system compiler](https://github.com/Dugongue/MathProofs/blob/main/TensorSignChain/RetainedSigns.md)

## 3. A raw family requiring two relations and admitting an odd automorphism

Fix an odd $b\ge3$ and let $I$ have $4b$ elements in four groups of size $b$. Define $R\subset F^I$ to have two generators whose column pairs are $(1,0),(0,1),(1,1),(1,-1)$, once per group with all $b$ copies identical. Let $W=R^\perp$ and let the factor lines be the coordinate restrictions to $W$. Every nonzero relation has exactly one zero block because a nonzero two-dimensional vector is orthogonal to one of the four projective directions. Its support has size $3b$. The factor lines are thus distinct and nonzero, all circuits have size $3b$, and the overlapping circuits form a single component of nullity two.

Give each factor exponent one. The Pfaffian degree $4b$ is even. No one relation covers every factor position. Any two independent relations cover all of them because their common zero direction is empty. Formula (1) of the accompanying proof gives zero imbalance because its weighted sum needs a full-support relation. In fact this arrangement has a sign-changing symmetry, as follows.

On the two-dimensional column space, the matrix $H=\operatorname{diag}(-1,1)$ permutes the four projective directions. On the four chosen normalized column directions it has three negative scales. The block permutation, with each negative scale repeated $b$ times, gives a signed permutation on $F^I$ preserving both $R$ and $W$. To verify the action on the relation space, if $Hv_i=\lambda_i v_{\sigma(i)}$ then
$$
 (H^{-\mathsf T}a)\cdot v_{\sigma(i)}
 =\lambda_i^{-1} a\cdot v_i
$$
for every row parameter $a$. Hence the signed permutation maps the full relation space to itself. Its orthogonality for the coordinate pairing then preserves $W$.

Use the raw block pencil of the accompanying proof on $F^I\oplus F^I$, with the independent alternating $B$ labels. A signed permutation on $W$ of this kind acts as a congruence on the pencil by
$$ P=\operatorname{diag}(S_\sigma D_\lambda,S_\sigma), $$
where $S_\sigma$ is the index permutation matrix and $D_\lambda$ is the diagonal of the source-index scales. The $B$ labels are transported by $B\mapsto S_\sigma B S_\sigma^\mathsf T$. The congruence formula for the diagonal block is the stated signed permutation on $W$, using $\lambda_i^{-1}=\lambda_i$. Thus $P$ stabilizes the pencil up to its raw label map, and $\det P=\prod_i\lambda_i=-1$. The right multiplier remains a scalar line by the block calculation, independent of the presence of an odd automorphism. The raw pencil is concise. For an invertible slice, set the label coordinates all equal to $1$ in each group with $b=0$ modulo three, and otherwise choose $1$ or $-1$ within each group to make its coordinate sum zero. Such a choice exists for every $b\ge3$ because among the first three possible counts of sign changes there is one satisfying the mod-three sum. The resulting vector is in $W$ and has no zero entries.

This family demonstrates why an invariant scalar Fourier moment can fail altogether. A sign-changing automorphism multiplies every odd covariant scalar by $-1$ while permuting its internal data. The tuple construction keeps enough of those data to enforce on an actual map exactly whether its color permutation is allowed. Its polynomial cost does not rely on choosing an equivariant order of the factors.

## Scope

The main proofs are written proofs of restricted single-instance reductions. The split factors, relation nullity and support cover have explicit extraction or checking procedures. Arbitrary TI inputs have no supplied reduction to this Pfaffian class.
