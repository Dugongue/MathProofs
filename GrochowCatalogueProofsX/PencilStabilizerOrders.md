# Exact left-right stabilizer order of an arbitrary matrix pencil

## GP-0229

Given an arbitrary two-dimensional matrix space $S=\langle A,B\rangle\subseteq M_{m,n}(\mathbb F_q)$, one can compute the order of its setwise left-right stabilizer in $\mathrm{GL}_m(q)\times\mathrm{GL}_n(q)$ in deterministic polynomial bit time, without an equivalence oracle or finite-field factoring. This includes rectangular and singular pencils, repeated elementary divisors, common kernels, unused image dimensions, and arbitrary finite fields. The two multiplicative contributions are an endomorphism-algebra unit count and the base-field projective symmetry count of the labeled regular elementary divisors.

## Kernel contribution

Let
$$
\mathcal E=\{(X,Y)\in M_m(k)\oplus M_n(k): XA=AY,\ XB=BY\}.
$$
This is an algebra under componentwise multiplication, and its dimension $D$ is obtained by solving the displayed linear equations. Its units are exactly the pairs with both entries invertible: if $X,Y$ are invertible the pair of inverses also intertwines. Thus $\mathcal E^\times$ is the kernel of the stabilizer action on $S$ given by $(P,Q):M\mapsto PMQ^{-1}$.

Treat the ordered pencil as a Kronecker-quiver representation. Its direct-sum decomposition has indecomposables the left and right singular blocks (including minimal index zero), and the regular blocks indexed by a closed projective point and a positive block length. Write $r_J$ for the multiplicity of each isomorphism type $J$, and $d_J=1$ for singular blocks and rational points, with $d_J=\deg f$ for a block supported at an irreducible degree-$\deg f$ finite polynomial $f$. In a singular block there is one scalar endomorphism parameter, as follows by equating the two shift intertwining equations in the standard Kronecker bases, which force equal diagonal entries and zero off-diagonal ones. In a regular finite block the endomorphism algebra is $k[x]/(f^a)$, since one map is the identity and the other is multiplication by $x$ on this cyclic module. Infinity is the same description with reversed maps and $f=x$.

The semisimple quotient of $\mathcal E$ is consequently $\prod_J M_{r_J}(\mathbb F_{q^{d_J}})$. To see the quotient, group identical indecomposables together, reduce each block map between identical copies modulo its local radical, and discard maps between distinct types. Compositions through two nonisomorphic indecomposables cannot be units on a summand, since that would split off an isomorphic summand of the other indecomposable. The resulting map is a surjective algebra map. The resulting ideal is the Jacobson radical by the endomorphism version of Krull–Schmidt, which states that additive categories of finite-length modules have locally defined radicals on indecomposables. Here the modules are finite dimensional representations of the two-arrow quiver. Thus
$$
|\mathcal E^\times|=q^{D-\sum_J d_Jr_J^2}\prod_J |\mathrm{GL}_{r_J}(q^{d_J})|.
$$
Indeed the kernel on units is $1+\operatorname{rad}\mathcal E$, and every unit of the quotient lifts because the radical is nilpotent.

## Image contribution

The image in $\mathrm{GL}(S)\cong\mathrm{GL}_2(q)$ consists of changes of variables for which the transformed ordered pair is strictly equivalent to the original. All scalar changes occur by scaling one side of the pencil. Homogeneous substitution preserves both minimal-index multisets and acts on the elementary divisors by projectivity on the support points, preserving the multiset of block lengths attached to each point. Consequently the image has order $(q-1)|P|$, where $P$ is the subgroup of $\mathrm{PGL}_2(q)$ preserving the labeled projective support. This uses the full regular list, including its rational infinity label when present. [Strict-equivalence invariants of general pencils](https://gauss.uc3m.es/fdopico/papers/laa2016-4.pdf)

For geometric support of size $s\geq3$, use the finite reduced algebra of ordered distinct source and target triples from GP-0234 with the pencil on both sides. Its four disjoint candidate charts test rationality and preserve all labels. Work in those charts and let $D_{\rm pass}$ be the sum of their surviving dimensions over $k$. Dimension of a finite reduced algebra equals its number of geometric points, because after algebraic closure it is a product of copies of $\overline{k}$. Every $p\in P$ contributes precisely $s(s-1)(s-2)$ ordered triple pairs, one for each choice of ordered distinct source anchors and its unique image. Each retained pair has exactly one candidate projectivity. Therefore
$$
|P|=\frac{D_{\rm pass}}{s(s-1)(s-2)}.
$$
This counts the exact projective symmetries, even when most anchor coordinates live in extension fields. [The pencil algebra and arithmetic operations in GP-0234](RankTwoMatrixSpaceEquivalence.md)

When the support is empty, $P=\mathrm{PGL}_2(q)$ has order $q(q^2-1)$. With one support point it is rational and its stabilizer has order $q(q-1)$. With two rational points the pointwise stabilizer has order $q-1$, since after moving the pair to zero and infinity it consists of nonzero scalings. The order doubles exactly when the two labels agree. With a conjugate quadratic pair the labels always agree, and its unordered stabilizer has order $2(q+1)$. There are $q(q-1)/2$ conjugate unordered pairs, and the projective action on them is transitive because any two quadratic irrational elements in the same quadratic field are related by an affine map over $k$. The rationality type and whether the labels agree are read from the divisor arithmetic of GP-0234.

## Bit complexity without factoring

To evaluate the kernel formula, refine the finite squarefree support polynomial by the finite parts of all the projective divisors $D_{i,a}$ used to compare labels in GP-0234. Over the finite support, each resulting factor $h$ is squarefree and all its geometric roots have the same multiplicities $r_a$ of blocks of length $a$. The refinement starts with the whole support and splits each current factor by a gcd with the next divisor, keeping both nonconstant factors when the gcd is proper. All current factors are coprime and there are at most the support degree many of them, so this takes polynomial time. No irreducible factorization is needed. For each $d\leq\deg h$, let $g_d$ be the degree of $\gcd(h,z^{q^d}-z)$. Modular powering computes this in polynomial time. If $N_d$ is the number of irreducible factors of $h$ of degree $d$, finite-field splitting gives $g_d=\sum_{e\mid d}eN_e$. Recover all $N_d$ by the divisor recurrence. The contribution to the dimension subtraction on this polynomial is $\sum_{d,a}dN_dr_a^2$, and to the semisimple unit product it is $\prod_{d,a}|\mathrm{GL}_{r_a}(q^d)|^{N_d}$, omitting zero multiplicities. Add the infinity label and singular block multiplicities separately over the base field.

Multiply the kernel and image factors to obtain the answer. The algorithms use only field, polynomial, and integer arithmetic on polynomial-bit objects. The output integer has bit length at most that of $|\mathrm{GL}_m(q)|\,|\mathrm{GL}_n(q)|$. For a one-dimensional space generated by a rank-$r$ matrix, the kernel action is the invertible endomorphism algebra of the corresponding single linear map. By the same calculation, its semisimple quotient has factors $\mathrm{GL}_r(q)$, $\mathrm{GL}_{m-r}(q)$, and $\mathrm{GL}_{n-r}(q)$ on units, with a radical of dimension $r(m-r)+r(n-r)$. The image on the space is all $k^\times$. For a zero-dimensional space the whole ambient product is the stabilizer.
