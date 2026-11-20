# Exponential size for a class of natural determinant gadgets

The lower bound concerns determinant-line gadgets for a natural $n$-dimensional mode $V$, where $n\ge 2$. It gives an obstruction to encoding special-linear tensor isomorphism as ordinary tensor isomorphism. Each structural tensor is natural under $\mathrm{GL}(V)$, and each data tensor is produced equivariantly by a polynomial of degree at most $D$ in the input tensor. A fixed orientation mark on the determinant line is allowed. When the representation weights satisfy the balanced-weight hypothesis below, any successful gadget needs at least $2^{n-D}$ allocated dense coordinates in a single tensor. In particular, arbitrary arity and any number of auxiliary sorts do not yield dense polynomial size for $D=o(n)$.

## Model and theorem

Work over a field $F$ with a nontrivial $F^\times$, and use rational algebraic representations of $\mathrm{GL}(V)$ defined over $F$. Equivariance is an algebraic identity after extension to an algebraic closure. Each auxiliary role is a nonzero representation $W_j$ homogeneous for the scalar torus, meaning $tI_V$ acts by $t^{d_j}$ for an integer $d_j$. Decompose
$$
d_j=n a_j+r_j,\qquad -n/2<r_j\le n/2 .
$$
The original mode $V$ has $d=1$ and $a=0$, the other two original modes are trivial under this $\mathrm{GL}(V)$ and have $d=a=0$, and the orientation line $L=\bigwedge^n V$ has $d=n$, $a=1$. The convention includes the dual of a role as a signed occurrence of the same role, including when $n$ is even and the residue representative is $n/2$.

The balanced-weight hypothesis is that every role $W_j$, after scalar extension, contains a torus weight with entries $\lfloor d_j/n\rfloor$ and $\lceil d_j/n\rceil$ and total sum $d_j$. The symmetric group acts on the weights by conjugation with permutation matrices. There are therefore at least $\binom{n}{|r_j|}$ distinct weight spaces in $W_j$. Section 3 proves the hypothesis for all homogeneous rational modules in characteristic zero and for a specified large-characteristic regime. Exterior powers, their duals and determinant twists satisfy it over every field.

The gadget is a typed system of tensors. Each unmarked tensor slot consists of a tensor product of (possibly repeated) roles and their duals, with one factor per occurrence. A slot holds either a $\mathrm{GL}(V)$-invariant structural tensor, or a tensor $P(T)$ given by a $\mathrm{GL}(V)$-equivariant polynomial map of the input $T$ of degree at most $D$, where the scalar torus acts on $T$ by degree $1$. The orientations are additional point marks on $L$ or its tensor powers, and ordinary point marks on roles with $a_j=0$ that are preserved by the natural lift under consideration. Isomorphisms are allowed independent invertible linear maps on the roles, preserving all slots and marks. A linear or multilinear operation is included as a tensor with dualized input roles. Assume $0\le D<n$. Bit complexity is measured by the allocated dense coordinates in each slot. A gadget with representations known as homogeneous pieces of larger roles can present those pieces as separate roles and include their projections. Slot-by-slot bounds refer to this presentation.

**Theorem.** If every unmarked slot has fewer than $2^{n-D}$ dense coordinates, then every $\mathrm{GL}(V)$ map taking $T$ to $T'$ extends to an isomorphism of the marked gadgets, when the orientation marks use the same fixed coordinates on both sides. More precisely, a failure of the automatic extension requires a slot with degree $k\le D$ and occurrences $j_1,\ldots,j_m$ such that
$$
\sum_{i=1}^m |r_{j_i}|\ge n-k,\qquad
\prod_{i=1}^m\dim W_{j_i}\ge 2^{n-k}.
$$
For an all-structural system in this model, a failure of automatic extension at arity at most $m$ requires a role of dimension at least $\binom{n}{\lceil n/m\rceil}$ whenever this index is at most $\lfloor n/2\rfloor$. If $\lceil n/m\rceil>\lfloor n/2\rfloor$, automatic extension always holds. These conclusions apply to determinant extraction even when the slot count and arity grow with $n$.

## Proof

Give an occurrence sign $\epsilon_i=+1$ for a role and $\epsilon_i=-1$ for its dual. The scalar torus acts on the slot with degree $\sum_i\epsilon_i d_{j_i}$. If the slot is a nonzero structural tensor, this degree is zero. If a data polynomial map is nonzero, scalar equivariance forces it to be homogeneous of degree $k=\sum_i\epsilon_i d_{j_i}$. In fact a homogeneous component of degree $k'$ on the input scales by $t^{k'}$, and distinct powers are independent in the Laurent polynomial ring over $F$. A zero slot imposes no condition. Thus
$$
n\sum_i\epsilon_i a_{j_i}=k-\sum_i\epsilon_i r_{j_i}.
$$
If the sum of the signed $a$'s is nonzero, the absolute value of the left side is at least $n$, giving $\sum_i|r_{j_i}|\ge n-k$. For $0<t\le n/2$,
$$
\binom{n}{t}=\prod_{u=1}^t\frac{n-t+u}{u}\ge (n/t)^t\ge 2^t .
$$
The same last inequality holds for $t=0$. Multiply over occurrences and apply the dimension bound. The arity claim follows because some $|r_j|\ge\lceil n/m\rceil$ and binomial coefficients are increasing up to the midpoint.

There is a stronger numerical form of the dense bound. Set $u=\lfloor n/2\rfloor$ and write $n-k=bu+c$ with $0\le c<u$. The same slot must have at least $\binom{n}{u}^{b}\binom{n}{c}$ coordinates. To see this, reduce the sum of the nonnegative integers $|r_{j_i}|$ to exactly $n-k$ using the monotonicity of the binomial coefficients up to $u$. Whenever $0<v\le w<u$ occur, replacing $(v,w)$ by $(v-1,w+1)$ cannot increase the product, because the successive ratios $\binom{n}{z+1}/\binom{n}{z}$ decrease with $z$. These transfers strictly increase the sum of squares and terminate with at most one positive entry less than $u$. Thus a structural slot that obstructs the auxiliary scaling has at least $\binom{n}{n/2}^{\,2}$ coordinates for even $n$, and at least $n\binom{n}{(n-1)/2}^{\,2}$ for odd $n$.

If there is no nonzero signed $a$ sum, then for each $\lambda\in F^\times$ the scalar maps $\lambda^{a_j}I_{W_j}$ preserve every unmarked slot, including every data value. They are the identity on the original modes, and act as $\lambda$ on $L$. Lift the given $g\in\mathrm{GL}(V)$ by the natural actions $W_j(g)$. Compose on the target with the auxiliary scalar maps for $\lambda=(\det g)^{-1}$. This still lifts $g$, but it fixes the chosen orientation on $L$, and it fixes point marks inherited from that orientation on its tensor powers. It also preserves the other permitted marks. This proves the extension claim.

For every $n$ over $F$ with $F^\times\ne\{1\}$, use the tensor of the $n$ by $n$ identity matrix with a third mode of dimension one, and twist its first mode by a diagonal matrix of determinant different from one. The matrix determinant is preserved by determinant-one maps on the two matrix modes, while the special-linear group on the third mode is trivial. These tensors lie in distinct special-linear orbits. The automatic extension identifies the two gadgets. Therefore a correct reduction on all tensors in this model cannot meet the small-slot hypothesis. The same argument applies to a natural multi-mode system by restricting its equivariance to this selected factor and giving its other two original modes central degree zero. It also applies to the composition with a tensor-system compiler that preserves isomorphism.

## When the balanced-weight hypothesis holds

Let $W$ be a nonzero homogeneous rational $\mathrm{GL}_n$-representation. In characteristic zero a torus weight of total sum $d$ can be balanced by successive root moves. The same argument works in characteristic $p$ if all torus weights $\mu$ of $W$ satisfy $|\mu_i-\mu_j|<p$ for every $i,j$. To prove it, work over an algebraic closure. At a weight $\mu$ with $\mu_i-\mu_j=m\ge 2$, differentiate the two elementary root subgroups, giving operators $E,F$ that raise and lower by $e_i-e_j$ and their commutator $[E,F]=H$. On weight $\mu$, $H$ acts by the integer $m$ in the base field. For $v$ a nonzero vector of this weight, suppose $Fv=0$. Let $b$ be maximal with $E^b v\ne 0$, which exists because the weight set is finite. The commutator identity gives
$$
0=F E^{b+1}v=-(b+1)(m+b)E^b v .
$$
It follows by induction from $F E=E F-H$ and the weight shift of $E$. The coefficient is nonzero in characteristic zero. In characteristic $p$, the weight of $E^b v$ yields $m+2b<p$, so both factors are positive and less than $p$. This proves $Fv\ne0$ and gives the lower weight $\mu-e_i+e_j$. Its sum of squared entries is smaller by $2(m-1)$, so the process terminates in a weight with entries differing by at most one. Their sum is still $d$. This proves the hypothesis.

For example a subquotient of a direct sum of mixed tensor powers with at most $B$ factors from $V$ and $V^*$ in each summand has all coordinate differences at most $B$. Uniform determinant twists on a summand add the same integer to each weight coordinate and do not change this bound. The argument works for those representations in characteristic $p>B$. In every characteristic the balanced weights of exterior powers and their duals are read directly from a wedge basis, and determinant twists preserve balance. Arbitrary modular representations may fail the hypothesis. The Frobenius twist of the natural module has dimension $n$ and weights $p e_i$, which are unbalanced when $1<p<n$. The weight proof does not cover an arbitrary construction using such twists or merely finite-point equivariance.

## Sparse structural tensors in weight bases

A second obstruction applies to the structural version in characteristic zero or under the weight-spread bound of Section 3. Fix an integer $C\ge1$ and let $n\ge3(C+1)$. Assume every role has dimension less than $\binom{n}{C+1}$. This includes roles of dimension at most $n^C$ for sufficiently large $n$. Even with unbounded arity, a structural slot that breaks the auxiliary scaling must have at least $n!/(2C)^n$ nonzero coefficients if its factors are presented in torus-weight bases.

First consider any torus weight $\mu$ of a role. It has a coordinate value $b$ with multiplicity at least $n-C$. Otherwise, if a value occurs at least $C+1$ times, its multiplicity lies between $C+1$ and $n-C-1$. The symmetric orbit then has at least $\binom{n}{C+1}$ elements, by tracking the subset of positions with that value. If every multiplicity is at most $C$, greedily take whole value classes until their union first has size at least $C+1$. Its size is at most $2C$. Tracking that union yields the same contradiction. The dimension bound thus gives the claimed modal value.

Let $P$ be the sum of the positive deviations of $\mu_i$ from $b$, and $N$ the absolute sum of the negative deviations. If $P>C$, start with the at most $C$ positive positions. As long as there are at most $C$ of them, some positive deviation is at least two. Transfer one from that position to a position of value $b$ by the root move proved above. The new weight keeps $P$ unchanged and has one more positive position. Once there are $C+1$ positive positions, their support yields a symmetric orbit of size at least $\binom{n}{C+1}$, a contradiction. The reverse-sign argument gives $N\le C$. Therefore $|d_j-nb|\le C<n/2$, so $b=a_j$. In particular each weight differs from $a_j(1,\ldots,1)$ on at most $2C$ positions.

Consider a nonzero component of an invariant slot in the product weight decomposition, with weights $\mu^{(i)}$ taken in the underlying undualized roles. Invariance under the diagonal torus gives $\sum_i\epsilon_i\mu^{(i)}=0$. If $A=\sum_i\epsilon_i a_{j_i}\ne0$, the deviation vectors $\delta^{(i)}=\mu^{(i)}-a_{j_i}(1,\ldots,1)$ satisfy $\sum_i\epsilon_i\delta^{(i)}=-A(1,\ldots,1)$. At each coordinate the tuple of deviations across all factors is therefore nonzero. Each distinct tuple occurs on at most $2C$ coordinates, since it has a nonzero entry in a factor whose deviations are supported on at most $2C$ positions. Let the multiplicities of the distinct tuples be $e_1,\ldots,e_s$. The simultaneous permutation orbit of this ordered weight tuple has size $n!/\prod_\ell e_\ell!\ge n!/(2C)^n$. Permutation equivariance guarantees a nonzero component at every orbit member. Distinct product-weight components are disjoint blocks in the stated bases, so each requires at least one nonzero coefficient. This proves the sparse-coordinate bound in those bases.

## Sharp arity versus largest role

For $3\le m\le n$, set $t=\lceil n/m\rceil$. In the structural model over any field there is a determinant-extraction diagram of arity at most $m$ whose largest role has dimension exactly $\binom nt$. This matches the lower bound on the largest role. Partition $n$ into $m$ positive parts $s_1,\ldots,s_m$ differing by at most one. Use $\bigwedge^i V$ for $1\le i\le t$, with wedge-by-$V$ maps forcing the action on them. Indeed the wedge maps are surjective, so their preservation forces the induced action inductively. Include $L$ and $W=L\otimes(\bigwedge^{s_m}V)^*$, and the maps
$$
\bigotimes_{i=1}^{m-1}\bigwedge^{s_i}V\longrightarrow W,\qquad
W\otimes\bigwedge^{s_m}V\longrightarrow L .
$$
The first sends its arguments to their wedge, interpreted as an $L$-valued functional on the last exterior space. The second evaluates that functional. Their composite is wedge on all $n$ vectors. It forces the action on $L$ to be $\det g$ when the action on $V$ is $g$, since the composite is nonzero and the input exterior actions have already been forced. The arities count all input and output occurrences, and are at most $m$. The exterior degrees and the dual exterior degree of $W$ are at most $t$. Some part has size $t$ and either its exterior role or $W$ attains the claimed dimension. This sharpness concerns the largest role. The tensor entries still obey the dense coordinate lower bound.

The obstruction leaves open input-dependent nonpolynomial preprocessing, polynomial covariants of degree close to or above $n$, and succinct or nonnatural encodings that evade the slot assumptions. The unrestricted question remains [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5).
