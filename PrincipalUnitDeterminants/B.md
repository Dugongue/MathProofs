# Graph Isomorphism and principal units in square-zero extensions

Let $R$ be a fixed finite commutative local ring with maximal ideal
$\mathfrak m$ and residue field $k=\mathbb F_q$. Consider the class
of finite free unital $R$-algebras
$$
 A=S\oplus J,\qquad
 S=\prod_i M_{n_i}(R_i),\qquad J^2=0,
$$
where the $R_i$ are finite étale local $R$-algebras, $J$ is
an $S$-bimodule, and the multiplication uses its left and right
$S$-actions. The square-zero hypothesis is on the displayed
extension ideal. The Jacobson radical of $A$ is
$\mathfrak m S\oplus J$, and its square may be nonzero.

**Theorem.** The supplied-transporter determinant-one correction
problem on this class is in deterministic polynomial time if
$\operatorname{char}R=2$. For every fixed $R$ with
$\operatorname{char}R\ne2$, it is equivalent to Graph Isomorphism
under deterministic polynomial-time Turing reductions, with a
many-one hardness direction. That direction uses only $R_i=R$,
algebras with center $R$, and a supplied ordinary algebra isomorphism.
In particular over $\mathbb Z/4\mathbb Z$ a correction by the
principal unit $-1$ detects Graph Isomorphism, although every
supplied correction over its residue field is automatic.

The algorithm is for based multiplication tables promised to have
the displayed structural form. It does not require the decomposition
as input. It reads the combinatorial data from the reduction of the
source algebra modulo $\mathfrak m$.

## Exact determinant images

Let $\Omega$ be the set of geometric simple blocks of
$S/\mathfrak mS$, with widths $n_\omega$, the Frobenius successor
permutation, and the multiplicities $m_{\omega\tau}$ of natural
rectangular bimodules in the corresponding geometric corners of
$J/\mathfrak mJ$. For a rational block $i$, and any geometric
block $\omega$ above it, put
$$
 \ell_i=n_i+\sum_{\tau} n_\tau m_{\omega\tau},\qquad
 r_i=n_i+\sum_{\tau} n_\tau m_{\tau\omega}.
$$
These are independent of the chosen $\omega$.
Let $P$ consist of width- and multiplicity-preserving permutations
of $\Omega$ commuting with Frobenius. Let $\epsilon(\pi)$ be
the sign of the induced permutation of coordinates, using a diagonal
block of size $n_\omega^2$ and a radical block of size
$n_\omega n_\tau m_{\omega\tau}$. In particular a length-$c$
cycle on size-$w$ blocks contributes $(-1)^{w(c-1)}$.
Write $g$ for the gcd of $|\ell_i-r_i|$ and all $n_\omega n_\tau$
with $m_{\omega\tau}>0$. The gcd of an empty family is 0.

The determinant images in the original ring are exactly
$$
 D_L=(R^\times)^{\gcd_i\ell_i},\qquad
 D_R=(R^\times)^{\gcd_i r_i},\qquad
 D_{\mathrm{aut}}=(R^\times)^g\epsilon(P).
$$
In particular the image formula has the same integer exponents as
over the residue field. The ring unit group replaces the residue
multiplicative group, and every sign is interpreted in $R$.

### Norms are surjective on the principal units

If $E/R$ is finite étale local, its norm surjects onto $R^\times$.
This holds in mixed characteristic and without a principal maximal
ideal. The residue norm is surjective by finite-field cyclicity.
The residue trace is surjective because a finite field extension
is separable. Thus there is a lift $t\in E$ with trace 1, by
dividing an initial lift of a trace-one element by its unit trace.
For $a\in\mathfrak m^j$ with $j\ge1$, expand the determinant of
multiplication by $1+a t$ modulo $\mathfrak m^{j+1}$. The
constant term is 1, the linear term is $a\operatorname{Tr}(t)$,
and every term of higher degree is in $\mathfrak m^{j+1}$.
Consequently
$$
 N_{E/R}(1+a t)\equiv 1+a\pmod{\mathfrak m^{j+1}}.
$$
Correct the norm one layer at a time after lifting the residue norm.
Nilpotence of $\mathfrak m$ finishes the proof. The same argument
gives surjectivity from $1+\mathfrak m E$ onto $1+\mathfrak m$.
Finite étale local extensions are finite free, so these traces and
norms are determinants and traces of multiplication matrices.
[Finite étale algebras over henselian local rings](https://stacks.math.columbia.edu/tag/04GK)

### Unit determinants and alignment of the quotient

The algebra $S\otimes_R S^{\mathrm{op}}$ is a product of matrix
algebras over finite étale local factors $E$ of
$R_i\otimes_R R_j$. A multiplicity module for a corresponding
matrix block is $R$-projective, since cutting with a matrix unit
makes it a direct summand of the $R$-free module $J$.
It is also $E$-projective. Indeed an $R$-linear section of an
$E$-linear surjection can be averaged with the separability
idempotent of $E/R$ to obtain an $E$-linear section.
As $E$ is local, its finite projective modules are free.
The ranks of the multiplicity modules are exactly the residue
multiplicities, as claimed.

In the decomposition $S\oplus J$ a unit is $(s,j)$ with
$s\in S^\times$. Its left or right multiplication is block
triangular with diagonal blocks from $s$. On the $i$-th
component an independent determinant contributes
$N_{R_i/R}(\det s_i)^{\ell_i}$ on the left, and the analogous
right exponent. One can verify the exponents after a faithfully
flat finite étale splitting extension, where every column and row
is counted separately. Norm surjectivity and independent diagonal
matrices now give $D_L,D_R$, by Bézout.

For an automorphism $\phi$ of $A$, project $\phi|_S$ to $S$.
The result $\alpha$ is an algebra homomorphism. Its reduction
modulo $\mathfrak m$ gives the induced map on the semisimple
quotient, since $J/\mathfrak mJ$ is the residue Jacobson radical.
It is invertible by Nakayama's lemma. The permutation part of
$\alpha$ on geometric quotient blocks lies in $P$, by the
induced bimodule action on that residue radical.

Conversely, choose standard matrix coordinates and multiplicity
bases over the corresponding finite étale factors. Over a common
finite étale splitting extension, Frobenius permutes these
coordinates semilinearly. Every $\pi\in P$ lifts by permuting
the standard coordinate blocks, and commutation with Frobenius
gives descent to $R$. Its determinant is exactly
$\epsilon(\pi)$, computed after the faithfully flat extension.
The finite étale splitting extension is used for this proof
only. It is unnecessary to construct it in the algorithm.
[Finite étale descent over a henselian local ring](https://stacks.math.columbia.edu/tag/0D1W)

Undo this permutation. The remaining quotient automorphism is
inner on each $M_{n_i}(R_i)$, since it fixes its center.
For a direct proof, the images of the standard matrix units give
a decomposition of $R_i^{n_i}$ into isomorphic rank-one projective
summands. These are free over its local center. Transport a generator
of the first summand by the new matrix units and use the resulting
basis to align the systems. The determinant of conjugation by
$s\in S^\times$ is $\det L_s/\det R_s$, so these automorphisms
contribute all products of independent norms raised to
$\ell_i-r_i$.

It remains to align the complement after the projected quotient
automorphism is the identity. Then
$\phi(s)=s+d(s)$ for an $R$-linear derivation $d:S\to J$,
by $J^2=0$. The algebra $S$ is separable over $R$.
If $\sum x_a\otimes y_a$ is a separability element and
$t=\sum x_a d(y_a)$, applying $x\otimes y\mapsto x d(y)$
to its centralizing identity gives $s t=t s+d(s)$.
Thus conjugation by $1-t$ carries $s$ to $s+d(s)$.
This conjugation is the identity on $J$ and modulo $J$, so
its determinant is 1 over $R$. In a split matrix block the
same alignment has an elementary form. The sum
$\sum_a\phi(E_{a1})E_{1a}$ intertwines the old and new systems
of matrix units and is congruent to the identity. Sum this formula
over the central blocks for a single conjugator.

After alignment $\phi$ fixes $S$ pointwise. It may have a
nonzero component $J\to S$, but it is block triangular, and
its projected map $J\to J$ is an invertible $S$-bimodule map.
Every such bimodule map extends to an automorphism by the
identity on $S$, since $J^2=0$. On a multiplicity module
over $E$, a matrix $U$ contributes
$N_{E/R}(\det U)^{n_\omega n_\tau}$.
This proves the exact formula for $D_{\mathrm{aut}}$, including
the upper bound for automorphisms that do not preserve the chosen
extension ideal. For example when $R$ has characteristic 2 and
a nonzero square-zero scalar $a$, translating $z\mapsto z+a$
in $R[z]/z^2$ can move the ideal $(z)$. Its projected action
is the identity and its determinant is 1.

## Correction and the principal coordinate

For an ordinary transporter of determinants $x,y,z$, set
$\delta=z/(xy)$. The unit-isotopy normal form gives the
correction test
$$
 \delta\in D_{\mathrm{aut}},\qquad
 x^{-1}\delta^{-1}\in D_L,\qquad
 y^{-1}\delta^{-1}\in D_R .
$$
Indeed the stabilizer determinants are precisely
$(a\eta,b\eta,ab\eta)$ with independent $a,b,\eta$ in the three
images. The test specializes to $(\det P)^{-1}\in D_{\mathrm{aut}}$
if the supplied transporter is an algebra isomorphism $P$ on
all three legs. The orbit count is the product of the three
indices. [Earlier determinant-image calculation](https://github.com/Dugongue/MathProofs/tree/main/MultiplicationTensorDeterminants)

The abelian unit group decomposes canonically into its
prime-to-$p$ subgroup and the principal subgroup
$U=1+\mathfrak m$, where $p=\operatorname{char}k$. The former
maps isomorphically onto $k^\times$, since $U$ is a finite
$p$-group by the maximal-ideal filtration. In odd residue
characteristic, $-1$ is entirely prime to $p$. Hence the
principal part of $D_{\mathrm{aut}}$ is exactly $U^g$, and
the graph can affect only the residue correction. In residue
characteristic 2 the sign is principal. If $-1\ne1$, the
principal part is $U^g$ or $U^g\langle-1\rangle$, according
to the graph character. In characteristic 2 the two cases
coincide.

For fixed $R$, membership in the power subgroups is finite
arithmetic. The exponents and graph are computed from the
reduced algebra by the finite-field square-zero algorithm.
It computes the residue radical, the center fields and matrix-block
dimensions, then their corner multiplicities by simultaneous
eigenspaces over composita of pairs of center fields. All
composita have polynomial degree. It needs no simultaneous
splitting field for all the blocks at once. A GI oracle supplies
generators of the width-, multiplicity- and Frobenius-preserving
group by a colored graph stabilizer chain. Apply $\epsilon$
to these generators. In characteristic 2 that group computation
is unnecessary. [Field classification and algorithm](https://github.com/Dugongue/MathProofs/tree/main/DeterminantOneCorrection)

## The hardness family and the nilpotence boundary

Assume $-1\ne1$ and let $s=|R^\times|$, which is even.
Use the following decorated directed graph for two input simple
graphs $G,H$. For each input graph make a root of width 1.
Give each vertex two source copies of widths 3 and 5, and one
link sink of width $s$ reached from both copies and the root.
Give each edge a width-$2s$ sink reached from its two width-3
endpoints. Finally attach both roots to a common width-$3s$
sink. Give each arrow multiplicity $s$, and all other pairs
zero multiplicity. These data define a split square-zero extension
by the natural rectangular bimodules.

Its center is $R$. Commuting with the quotient block identities
eliminates all strictly off-diagonal central components. The
center of each matrix block consists of scalars, and each nonzero
free bimodule forces equality of the two adjacent scalars. The
underlying support is connected. Both unit determinant images
are full because a width-1 root has $\ell=r=1$ modulo $s$.
All $\ell_i-r_i$ are multiples of $s$, as is every
$n_\omega n_\tau$ on an arrow. Thus the power part of
$D_{\mathrm{aut}}$ is trivial. The widths 3 and 5 are paired
and have the same induced permutation, so their signs cancel.
Even-width quotient blocks and all radical blocks have even
dimension. The sign consequently equals the sign on the two roots.

Deleting the unique common sink leaves the two connected input
encodings. Their exchange is possible exactly when $G\cong H$:
the link sinks recover the paired vertices, and the other sinks
recover the original edges. Conversely an input isomorphism and
its inverse exchange the encodings. Thus the determinant group
is $\{1\}$ or $\langle-1\rangle$ according as the input
graphs are nonisomorphic or isomorphic. Reflect one coordinate
of the multiplication table by $P$ of determinant $-1$, in
the usual transported multiplication convention, and supply
$(P,P,P)$. The formula proves the claimed many-one reduction.
The side is
$$
 2+15s^2+(34+10s^2)(n_G+n_H)+16s^2(m_G+m_H).
$$
The ordinary orbit splits into $|R^\times|$ or
$|R^\times|/2$ special orbits, respectively.

Over a characteristic-2 local ring with nontrivial units, the
previous TI hardness construction already fits the analogous
class with extension ideal cube-zero. In its refined split
matrix-diagonal presentation, every product of two internal
payload arrows is killed by all further arrows. The outer
actions factor through the augmentation killing internal arrows,
and an outer product of a row and column terminates in the
source-to-sink corner, which also annihilates all other arrows.
This accounts for every radical triple in that construction.
Thus the square-zero class has a polynomial algorithm, while
the previous construction gives TI-over-$R$ hardness as soon
as the third power, rather than the second power, is required to
vanish. This is a comparison of exact results, without assuming
the complexity classes differ. [Earlier arbitrary-local-ring construction](https://github.com/Dugongue/MathProofs/tree/main/DeterminantOneCorrection)

The determinant and complexity theorems above have written proofs.
The Lean companion checks the first-order determinant computation,
the split matrix-unit alignment, and the square-zero conjugation
formula. The new principal-unit conclusions use the field formula
from the preceding round together with actual $R$-determinants
and the full norm-lifting argument. Bibliographic priority for
the combined classification remains open. [Lean source](B.lean)
