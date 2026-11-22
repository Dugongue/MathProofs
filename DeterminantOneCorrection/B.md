# Determinant-one correction for algebras with square-zero radical

Fix a finite field $k=\mathbb F_q$. The input is two based unital
associative multiplication tensors with square-zero Jacobson radical,
together with an explicit ordinary transporter. The question is
whether there is a transporter with determinant 1 on all three legs.

**Theorem.** For each fixed even $q$, this supplied-transporter problem
is in deterministic polynomial time. For each fixed odd $q$, it is
equivalent to Graph Isomorphism under deterministic polynomial-time
Turing reductions. The hardness direction is a many-one reduction.
Its outputs have center $k$, all residue fields equal to $k$, and
an ordinary transporter that is an algebra isomorphism. The ordinary
orbit of an output splits into $q-1$ or $(q-1)/2$ special orbits,
with the smaller count exactly on Graph Isomorphism yes instances.

The upper bound follows from an exact formula for all three determinant
images. Ordinary square-zero algebra isomorphism has a classical
incidence description. The extra task here is to determine which
incidence symmetries contribute a determinant and when that contribution
is needed for a known transporter. [Grochow and Qiao, §9](https://arxiv.org/html/1907.00309#S9)

## The exact automorphism determinant group

Write $J=J(A)$, with $J^2=0$, and
$$
 S=A/J=\prod_i M_{n_i}(k_i),\qquad [k_i:k]=f_i.
$$
The Wedderburn–Malcev theorem gives $A=S\oplus J$, with the usual
square-zero multiplication. The $S$-bimodule structure of $J$
is intrinsic because radical lifts give the same actions on $J$.

Over an algebraic closure, write $\Omega$ for the geometric simple
blocks of $S$. The blocks over $i$ form a Frobenius cycle of
length $f_i$. Give each geometric block its width $n_\omega=n_i$.
For $\omega,\tau\in\Omega$, let $m_{\omega\tau}$ be the multiplicity
in $e_\omega J_{\bar k}e_\tau$ of the natural rectangular bimodule
$\operatorname{Mat}_{n_\omega,n_\tau}(\bar k)$. These labels are
constant on Frobenius orbits of ordered pairs. Define $P$ to be the
group of permutations of $\Omega$ preserving widths and multiplicities
and commuting with Frobenius.

Every $\pi\in P$ permutes square blocks of size $n_\omega^2$ and
radical blocks of size $n_\omega n_\tau m_{\omega\tau}$, acting on
the internal coordinates by the identity. Let $\epsilon(\pi)\in k^\times$
be the sign of this permutation of all coordinates. It can be computed
by a weighted cycle count: permuting identical size-$w$ blocks by
a cycle of length $c$ contributes $(-1)^{w(c-1)}$.

Let $\ell_i,r_i$ be the left and right regular composition
multiplicities at $i$. For any $\omega$ over $i$, they are
$$
 \ell_i=n_i+\sum_{\tau\in\Omega}n_\tau m_{\omega\tau},
 \qquad
 r_i=n_i+\sum_{\tau\in\Omega}n_\tau m_{\tau\omega}.
$$
Define $g$ to be the gcd of the absolute differences
$|\ell_i-r_i|$ and all $n_\omega n_\tau$ for which
$m_{\omega\tau}>0$, with empty gcd 0. Then
$$
 \det\operatorname{Aut}_k(A)=(k^\times)^g\,\epsilon(P).
$$
The two unit determinant images are $(k^\times)^{\gcd_i\ell_i}$
and $(k^\times)^{\gcd_i r_i}$.

### Proof of the formula

Choose matrix-unit coordinates in each rational simple factor of
$S$. For each Frobenius orbit of supported ordered pairs choose
a multiplicity basis on its rational bimodule constituent over the
field of degree $\operatorname{lcm}(f_i,f_j)$. The field appears
because $k_i\otimes_k k_j$ splits as a product of fields of that degree, one per orbit of pairs
of embeddings. Over $\bar k$,
transport these bases around the orbit by Frobenius. The resulting
geometric coordinates have the standard matrix multiplication on
the diagonal blocks and standard matrix left and right actions on
each radical block. Frobenius permutes the coordinate bases in the
prescribed way and acts semilinearly on scalars.

An algebra automorphism induces a permutation in $P$. Conversely
the coordinate permutation just used to define $\epsilon(\pi)$
preserves the multiplication and commutes with semilinear Frobenius.
It therefore descends to a $k$-algebra automorphism with
determinant $\epsilon(\pi)$. This accounts for the full geometric
permutation part, including automorphisms of the residue fields.
There is no need to choose a normal basis for the determinant.

After removing that lift, the automorphism is inner on every
rational quotient block by Skolem–Noether, since the centers are
now fixed pointwise. Undo this by conjugating by a unit of $S$.
For $u=(u_i)\in S^\times$, the determinant of inner conjugation
is $\det L_u/\det R_u$. On a simple module of type $i$ the
determinant of multiplication equals $N_{k_i/k}(\det_{k_i} u_i)$.
Taking the product over a composition series gives
$$
 \det(\operatorname{Ad}u)=
 \prod_i N_{k_i/k}(\det_{k_i}u_i)^{\ell_i-r_i}.
$$
The corresponding norm factors vary independently over $k^\times$.
The same argument gives the left and right unit images. The displayed
multiplicity formulas follow after splitting into geometric blocks.
A left regular constituent of type $\omega$ occurs $n_i$ times
inside its square block and $n_\tau m_{\omega\tau}$ times in the
rectangular block headed by $(\omega,\tau)$.

Now the automorphism is the identity on the quotient. Two
Wedderburn complements lifting that quotient differ by conjugation
by an element of $1+J$. This conjugation acts as the identity
on $J$ and on $A/J$, so its determinant is 1. After undoing
it, we obtain exactly the $S$-bimodule automorphisms of $J$,
each extending by the identity on $S$.
An independent multiplicity map $H$ over a constituent field
$E$ contributes $N_{E/k}(\det_E H)^{n_\omega n_\tau}$.
Again finite-field norms and the scalar determinants are surjective.
Taking the product of these power subgroups with the inner ones
gives the single power subgroup of exponent $g$, by Bézout.
Adjoining the coordinate permutation signs proves the formula.
[Wedderburn–Malcev and the finite algebra algorithms](https://www.microsoft.com/en-us/research/wp-content/uploads/2011/01/smalldet.pdf)

## Test a supplied correction

The stabilizer of a unital associative multiplication tensor consists
of $(L_a\sigma,R_b\sigma,L_aR_b\sigma)$, with $a,b$ units and
$\sigma$ an algebra automorphism. This follows by setting each
input to 1 in the transport equation and cancelling the two unit
images of 1. Its determinant triple is
$(u\delta,v\delta,uv\delta)$, where $u,v,\delta$ vary independently
over the two unit images and the automorphism determinant group.

Given a supplied transporter of determinants $(x,y,z)$, put
$\delta=z/(xy)$. The exact correction criterion is that
$\delta$ lies in the automorphism image and
$x^{-1}/\delta,\ y^{-1}/\delta$ lie in the two unit images.
For the special case of a supplied algebra isomorphism with
determinant $d$, the two unit tests are automatic and the only
test is $d^{-1}$ in the automorphism image. For reference, the
orbit count itself is the product of the three image indices.

The group $(k^\times)^g$ is tested using the cyclic-group power
criterion. In even characteristic $-1=1$, so the permutation
part is irrelevant and all three tests are arithmetic. In odd
characteristic the only extra question is whether some $\pi\in P$
has negative weighted sign, and it is needed only if $-1$ lies
outside the power subgroup. That sign is a group character, so
testing it on a generating set suffices.

## Polynomial-time computation of the decorated graph

The input is an explicit multiplication table. Use the deterministic
finite-field radical algorithm. Find the center of the semisimple
quotient by linear equations. Its Frobenius-fixed subalgebra is
$k^r$ with one coordinate per simple block. A basis of that fixed
subalgebra separates the blocks, so repeated eigenspace splitting
at each of the $q$ possible eigenvalues yields the primitive
central idempotents. The center fields $k_i$ are now represented
by multiplication tables, and $n_i^2=\dim_k S_i/f_i$.
This requires no explicit matrix algebra isomorphism in the
algorithm. [Friedl and Rónyai](https://www.cs.uoregon.edu/Reports/TR-1985-003.pdf)

Identify all fields of one degree with a single model, by finding
a root of its defining irreducible polynomial in each represented
field. A full-degree element in a represented field can be found
deterministically. Its proper maximal subfields are the kernels of
$\mathrm{Frob}^{f_i/s}-I$ for primes $s\mid f_i$. A cyclic
multiplicative generator lies outside their union. Count points
outside the union in each affine coordinate prefix by inclusion
and exclusion and linear algebra. There are only polynomially
many intersections, since the number of distinct primes dividing
$f_i$ is at most $\log_2 f_i$. Select a nonempty prefix at each
step. Factoring the resulting defining polynomials over represented
extensions is deterministic in fixed characteristic. One can take
the Berlekamp fixed algebra and split using prime-field traces of
a dual basis, checking the finitely many prime-field values.
[Berlekamp on factoring over large finite fields](https://www.ams.org/mcom/1970-24-111/S0025-5718-1970-0276200-X/S0025-5718-1970-0276200-X.pdf)

For each ordered pair of residue degrees $d,e$, compute just
one compositum of degree $\operatorname{lcm}(d,e)\le de$ and
embed the two chosen models in it. For each pair of rational
blocks of these degrees, compute simultaneous eigenspaces of the
two center generators acting on the corresponding radical corner.
For each pair of geometric eigenvalues, divide the eigenspace
dimension over the compositum by $n_i n_j$ to get the multiplicity.
It is unnecessary to build a common splitting field of all the
residue fields. Replacing the chosen pair embeddings by another
pair shifts the two embedding indices by fixed amounts, common
to all ordered pairs of degrees $(d,e)$. All candidate
permutations preserve the degrees and commute with Frobenius
shifts, so this reindexing preserves the multiplicity test and
conjugates the induced permutation on the radical coordinate
blocks. It therefore preserves the signs as well.

Encode $\Omega$, the widths, the Frobenius successor relation,
and the weighted ordered-pair relation as a colored directed
incidence graph. Colored directed Graph Isomorphism reduces
to ordinary Graph Isomorphism by position markers and vertex colors.
A GI oracle computes generators for its automorphism group via
a pointwise stabilizer chain. For each base choice, first mark
the preceding vertices, find the orbit by colored isomorphism
tests and recover one isomorphism per orbit point by continued
pinning. The restrictions of these generators to $\Omega$
generate $P$, and their signs are easily read from the induced
coordinate permutations. This proves the claimed upper bounds.
It also computes the exact determinant-one orbit count.
[Mathon](https://doi.org/10.1016/0020-0190(79)90004-8)

## Hardness with a connected algebra and square-zero radical

For fixed odd $q$ put $s=q-1$, an even integer. Use a width on
each vertex as its split quotient matrix size, and give every
nonzero ordered radical corner multiplicity $s$. For each of the
two simple graphs build a directed incidence graph as follows.

- Use one root of width 1.
- For each vertex $a$, make a pair of sources $u_a,v_a$ of widths
  3 and 5, and a sink $l_a$ of width $s$. Put arrows into $l_a$
  from the root and from both members of the pair.
- For each edge $\{a,b\}$, make a sink of width $2s$. Its two
  incoming arrows come from $u_a,u_b$.

Use one common new sink of width $3s$ with the two roots as its
sources. Let $A$ be the split square-zero algebra given by this
width and multiplicity data. Its radical squares to zero by
construction. Its center is $k$, because a central radical
element has to be supported on diagonal corners and there are
none. The semisimple part of a central element is scalar on
each quotient matrix block, and arrows force equality of those
scalars across the connected underlying graph.

The gcd exponent formula gives $(k^\times)^g=\{1\}$. Every
$n_i n_j$ on an arrow is divisible by $s$ because its sink
has width a multiple of $s$. Every $\ell_i-r_i$ is a multiple
of $s$ because the radical multiplicities are all $s$.
The odd-width blocks are the roots and the vertex pairs.
All radical blocks and even-width quotient blocks have even
dimension. The link sinks force the same permutation on the
width-3 and width-5 indexed vertices, so their two signs cancel.
Consequently an automorphism is negative exactly when it
exchanges the two roots.

The common sink is the unique width-$3s$ node. Deleting it
gives two connected components. An exchange of those components
exists exactly when the original graphs are isomorphic, because
the links recover the paired vertices and the edge sinks recover
the unordered pairs. Conversely any graph isomorphism gives
such an exchange by applying it one way and its inverse the
other. Both unit determinant images are full, as the width-1
root has left and right multiplicities 1 modulo $q-1$.
Thus the claimed exact orbit counts follow.

Choose a coordinate reflection $P$ of determinant $-1$ and
present the same multiplication algebra in two frames:
$\mu$ and $\mu'(a,b)=P\mu(P^{-1}a,P^{-1}b)$. Supply $P$
as the ordinary algebra isomorphism, or $(P,P,P)$ as the ordinary
multiplication transporter. Its determinant-one correction exists
exactly when the automorphism determinant image contains $-1$.
The dimension of the common algebra is
$$
 2+15s^2+(34+10s^2)(n_G+n_H)+16s^2(m_G+m_H).
$$
Each coefficient counts matrix block dimensions and rectangular
radical multiplicities in the displayed construction. Dense
multiplication tables can therefore be emitted in polynomial time
for fixed $q$.

For comparison, in the basic square-zero class every width is 1,
so a nonzero radical yields $g=1$ and a full automorphism
determinant image. A zero radical is finite étale and its signs
are read directly from the residue field degrees. Thus supplied
correction has a polynomial-time algorithm in that basic class
over all fixed fields. This explains the role of the nonscalar
matrix blocks in the hardness construction.

## Prior work and verification

The November 19 $\mathbb F_3$ supplied-transporter theorem uses
a triangular amplifier and an exchange of connected components.
The later odd-field extension retains that mechanism and separately
uses three-layer path algebras for its GI result. Prior square-zero
work establishes determinant tests on one selected physical mode,
and ordinary square-zero algebra isomorphism already has graph
encodings. The result here keeps all three determinant constraints,
requires a square-zero radical even in the hard outputs, and gives
a matching oracle upper bound and an even-characteristic algorithm.
Priority for the combined classification and reductions remains open.
[November 19 supplied-transporter comparison](https://github.com/Dugongue/MathProofs/blob/main/TensorIsomorphismComposition/Results.md) ·
[One-mode square-zero result](https://github.com/Dugongue/MathProofs/blob/main/CubeZeroDeterminantAbsorption/OddAutomorphisms.md) ·
[Earlier odd-field result](https://github.com/Dugongue/MathProofs/blob/main/MultiplicationTensorDeterminants/D.md)

The full arguments above are written proofs. The Lean statements
check the matrix determinant for the radical shear, the contribution
from multiplicity coordinates, and the cancellation of paired
permutation signs. The finite control enumerated all 144 pairs of
labelled graphs through three vertices for each of three values of
s. It tested 3,162 decorated automorphisms by the signs of their
actual coordinate permutations. [Lean source](B.lean) · [Finite control](BCheck.py)
