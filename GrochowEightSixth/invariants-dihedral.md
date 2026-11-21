# Three answers on dihedral and orthogonal cubic recovery

These are informal proofs for the open questions in Edidin and Katz, *Generic orbit recovery from dihedral invariants of very low degree*. Write $D_n$ for the group of order $2n$ acting on the vertices of a regular $n$-gon. [Open questions, §§5.1–5.2](https://arxiv.org/html/2408.09599v2#S5) · [Algorithm question, Remark 3.13](https://arxiv.org/html/2408.09599v2#S3.SS1).

## Polynomial invariants over other fields

For every infinite field of characteristic prime to $2n$, cubic polynomial invariants of the natural $n$-dimensional representation generically separate $D_n$-orbits, with exactly one exception. For $n=5$, the cubic invariants have two generic dihedral orbits per fiber over an algebraic closure. Degree four repairs this exception. In particular the universal statement in §5.2 is negative even over $\mathbb C$. This also gives a correction to the $n=5$ case of Theorem 2.5 in the cited preprint. The example in §4.2 of that preprint exhibits a particular degenerate fiber. Here the two-orbit fiber occurs generically. [Theorem 2.5](https://arxiv.org/html/2408.09599v2#S2.SS2) · [Example 4.5 and §5.2](https://arxiv.org/html/2408.09599v2#S4.SS2).

### Fourier coordinates and consistent reflection choices

Work first over an algebraic closure and use Fourier coordinates $x_i$ indexed modulo $n$. Rotation multiplies $x_i$ by $\zeta^i$ and reflection exchanges $x_i$ and $x_{-i}$. Degree one gives $x_0$ and degree two gives $p_i=x_i x_{-i}$, including $p_h=x_h^2$ at $h=n/2$ when $n$ is even. For any zero-sum triple $(i,j,k)$ the cubic data give
$$
A+B,\qquad A=x_i x_j x_k,\quad B=x_{-i}x_{-j}x_{-k}.
$$
Its product $AB=p_i p_j p_k$ is known. Thus each such ordered pair has two possible orientations.

For comparing points $x,y$ in a generic fiber use ratios $t_i=y_i/x_i$ and $a_i=x_i/x_{-i}$. The equations from degree two give $t_{-i}=t_i^{-1}$ and $a_{-i}=a_i^{-1}$. For the even index $h$ this means $t_h^2=1$ and $a_h=1$. On a zero-sum triple, put $v=e_i+e_j+e_k$ with $e_{-i}=-e_i$ and, in the even case, $2e_h=0$. One has
$$
t^v\in\{1,a^{-v}\}.
$$
Here the $a_i$ for positive nonself-opposite indices are independent Laurent variables. Choose a branch $\epsilon_v\in\{0,1\}$ so the value is $a^{-\epsilon_v v}$.

The following use of an integer relation will synchronize these choices. Suppose a set of forms has a minimal linear dependence after projection to the free coordinates, and an integer dependence $\sum_v c_v v=0$ in the group with the even torsion coordinate. One can always clear denominators and multiply by two in the even case. All $c_v$ are nonzero. The branch choices imply
$$
a^{\sum_v c_v\epsilon_v v}=1.
$$
For a nonempty proper subset of its terms the projected exponent is nonzero by minimality. The corresponding Laurent equation is a proper closed condition on $x$. There are finitely many such tests in the proof. Away from their union all forms in the dependence have the same branch. Reflection switches all branches at once.

### The cases with cubic recovery

Let $k=\lfloor(n-1)/2\rfloor$. For $k\ge4$ use the nonwrap forms
$$
w_j=e_1+e_j-e_{j+1}\quad (1\le j<k),\qquad
v_{2j}=e_2+e_j-e_{j+2}\quad (2\le j\le k-2).
$$
The $w_j$ are independent over $\mathbb Q$. Since $v_{2j}=-w_1+w_j+w_{j+1}$, each of these relations has minimal support. They synchronize all $w_j$ with $w_1$. After a reflection if necessary we therefore have $t_i=t_1^i$ for $1\le i\le k$.

For odd $n=2k+1$, the triples $(1,k,k)$ and $(2,k-1,k)$ both give $t_1^n\in\{1,a^{-v}\}$. Their two nontrivial Laurent monomials differ generically. Thus $t_1^n=1$. For even $n=2k+2$ use the half-index triples $(1,k,h)$ and $(2,k-1,h)$. They similarly give $t_1^h t_h=1$, since the nontrivial Laurent monomials differ. Squaring gives $t_1^n=1$ and $t_h=t_1^h$. These are exactly the rotation ratios.

For $n=6,7,8$ the following relations suffice. The names in each row denote the displayed forms in order. Each relation has minimal support on projection to the free coordinates. This follows by taking the rank of the displayed two- or three-row matrix, which is one less than the number of forms, and observing that no coefficient in the relation vanishes.

| $n$ | Forms | Relation |
|---|---|---|
| $6$ | $v=2e_1-e_2$, $a=e_1+e_2+e_h$, $b=3e_2$ | $v+b-2a=0$ |
| $7$ | $v=2e_1-e_2$, $w=e_1+e_2-e_3$, $a=e_1+2e_3$, $b=2e_2+e_3$ | $v-w-a+b=0$ |
| $8$ | $v=2e_1-e_2$, $w=e_1+e_2-e_3$, $a=e_1+e_3+e_h$, $b=2e_2+e_h$ | $v-w-a+b=0$ |

The orders of the ratios then follow from the same chain and wrap equations. For $n=4$, the single half-index triple $(1,1,2)$ may be oriented using reflection. It gives $t_1^2t_2=1$ and $t_1^4=1$. For $n=3$ the action is the full symmetric action on three coordinates, so the elementary symmetric polynomials suffice. The smaller cases are immediate from the elementary symmetric polynomials as well.

These statements give field generation in the same degrees. Indeed the relevant oriented cubic monomials are roots of quadratics over the invariant-data field, generically with distinct roots. The half-frequency coordinate is obtained by a separable square root. A chain expresses every other coordinate in terms of $x_1$ and these algebraic quantities. A wrap monomial determines a power of $x_1$ whose exponent divides $n$ or is equal to $n$. Such a root extraction is separable in the stated characteristic. Thus the field extension is finite separable, and its degree agrees with the number of ordered points in a generic geometric fiber. For the nonexceptional cases that is the effective group order. Base change preserves the invariant field generation conclusion, and separation over an algebraic closure implies separation of the original-field points.

### The exceptional five-point action

The only nonzero-frequency triples, up to reflection and reorderings, are $(1,1,-2)$ and $(1,2,2)$. Terms involving $x_0$ add only information already in degrees one and two. With the products $p_1,p_2$ fixed, write
$$
u=x_1^2/x_2,\qquad v=x_1x_2^2.
$$
The monomial map from $(x_1,x_2)$ to $(u,v)$ has integer determinant five. It is onto over an algebraic closure and has kernel the rotations. Reflection simultaneously takes
$$
(u,v)\longmapsto\left(\frac{p_1^2}{p_2u},\frac{p_1p_2^2}{v}\right).
$$
The two cubic sums specify the first and second coordinates each only up to the displayed involution in that coordinate. Generically these are four distinct choices, all realized because the monomial map is onto. Simultaneous reflection pairs them into two dihedral orbits. Separability is again given by the two quadratics and the fifth-root extraction. In particular the cubic subfield has degree two inside the full invariant field.

The two-orbit fiber also occurs for generic real signals, correcting Proposition 3.1 at five points. In Fourier coordinates, reality is the condition $x_{-i}=\overline{x_i}$, and hence $p_i>0$ on the locus used here. The two branch involutions are complex conjugation on the respective circles for $u$ and $v$. At the fixed magnitudes of $x_1$ and $x_2$ the phase map to those two circles is the torus homomorphism with integer matrix $\left(\begin{smallmatrix}2&-1\\1&2\end{smallmatrix}\right)$. It is surjective by its nonzero determinant. Thus each independent branch choice is realized by a real signal with the original magnitudes. Generically both cubic monomials are nonreal, so there are again four cyclic orbits and two dihedral orbits. The same obstruction applies to unitary moments when signals are restricted to the real locus, where those moments agree with the polynomial moments.


The quartic invariant $x_1^3x_2+x_{-1}^3x_{-2}$ fixes the unordered reflection pair for the product $uv$. Its exponent form is the sum of the two cubic forms. The minimal dependence on these three forms forces the same branch on the two original forms, and hence a unique dihedral orbit. Thus the exact algebraic generic cutoff for $n=5$ is four.

## Unitary cubic recovery on complex vectors

The answer to §5.1 is affirmative for every $n$, including $n=5$. Use the paper's second and third tensors with one conjugated slot. In complex Fourier coordinates write $r_i=|x_i|^2$. The first tensor gives $x_0$ and the second gives $r_i+r_{-i}$. The third entry with pure frequencies $i,-i$ and conjugated frequency $0$ gives $2x_i x_{-i}\bar x_0$, up to a known nonzero factor from rotation averaging. We may assume $x_0\ne0$. Thus $p_i=x_i x_{-i}$ is known, so the two magnitudes in each pair are known as an unordered pair, by their sum and product. Generically the magnitudes for each nonself-opposite pair differ.

Take a nonzero-frequency zero-sum triple. As before let $A$ be the product of its coordinates, $B$ the product of the reflected coordinates, and put $U=A+B,V=A-B$. The mixed cubic entry conjugating the coordinate of index $-i$, multiplied by $p_i$, is
$$
r_{-i}A+r_iB.
$$
It is available for every index $i$ of the triple. At a candidate point with the same data, let $U',V'$ denote the analogous values. An orientation change of the magnitudes on the pair of index $i$ changes the sign of $r_i-r_{-i}$. The product $AB$ is known from the $p_i$, so $U'^2-V'^2=U^2-V^2$.

Suppose two indices $i,j$ of the triple belong to different nonself-opposite pairs. Set $a=(r_i-r_{-i})/(r_i+r_{-i})$ and $b=(r_j-r_{-j})/(r_j+r_{-j})$. If the candidate keeps the first orientation and reverses the second, equality of the two mixed entries gives
$$
U'-U=a(V'-V)=-b(V'+V).
$$
On the real Zariski open set where $a,b,a+b$ are nonzero this forces $V'=cV$ and $U'=U+a(c-1)V$, with $c=(a-b)/(a+b)$. The identity $U'^2-V'^2=U^2-V^2$ would then require
$$
2a(c-1)UV+\bigl(a^2(c-1)^2-c^2+1\bigr)V^2=0.
$$
It is a proper real-algebraic condition after clearing denominators. Indeed at fixed admissible magnitudes its first coefficient is nonzero, and $A/B$, and hence $U/V$, can vary with the phase of a Fourier coordinate occurring in $A$ only. Such a coordinate exists, because a nonzero triple containing opposite indices would also contain zero. The other mismatched case is excluded by globally reflecting the candidate, which leaves the data unchanged. Thus any two nonself-opposite pairs appearing in a triple have the same orientation choice generically.

The triples $(1,j,-1-j)$ for $2\le j\le k=\lfloor(n-1)/2\rfloor$ connect every nonspecial pair to the pair of index one. This includes the five-point case. After applying one reflection, the candidate and original have the same labeled magnitudes. At any triple with two distinct nonself-opposite pairs the two linear equations above now recover both $U$ and $V$, on the generic set where the corresponding normalized differences differ. A triple involving a self-opposite index and a nonspecial index also has two independent linear equations, since the self-opposite index has difference zero and the other one has nonzero difference. Therefore both oriented products are known on the chain triples $(1,j,-1-j)$ for $1\le j<k$. For odd $n\ge5$ use the wrap triple $(1,k,k)$. For even $n\ge4$ use $(1,k,h)$. Their oriented products are known by the same reasoning.

It follows that equality of unitary data yields $t_i=t_1^i$ on positive indices and $t_1^n=1$, with $t_h=t_1^h$ in the even case. Thus the candidate is a rotation of the original after the single reflection already used. At $n=3$ the sole relevant triple is $(1,1,1)$ and its reflection. After aligning the ordered magnitudes $r_1,r_{-1}$, the two possibilities from the mixed sum and $AB$ exchange $(A,B)$ with $((r_1/r_{-1})B,(r_{-1}/r_1)A)$. The magnitude of the replacement for $A=x_1^3$ would be $r_1\sqrt{r_{-1}}$, which differs from $r_1^{3/2}$ generically. Hence $A$ is recovered and the ratio is a third root of unity. At $n=2$ the known $p_1=x_1^2$ suffices along with $x_0$, and $n=1$ is trivial. All exclusions above are finitely many proper real-algebraic equalities, giving the required nonempty real Zariski open set.

## Polynomial-time reconstruction from the orthogonal bispectrum

For the real $O(2)$ bandlimited model on frequencies $1,\ldots,k$ with $k\ge4$, Remark 3.13 asks about avoiding exponential search over conjugate choices. On the generic locus the vector can be reconstructed up to $O(2)$ using $O(k)$ local tests on a constant number of quadratic roots. With rational invariant input this is an exact polynomial-bit algorithm with arithmetic-expression output.

The quadratic data give $p_i=|x_i|^2$. The cubic datum for $i+j\le k$ is $B_{ij}+\overline{B_{ij}}$, where $B_{ij}=x_i x_j\overline{x_{i+j}}$. Together with $B_{ij}\overline{B_{ij}}=p_i p_j p_{i+j}$ this gives two quadratic candidates. Fix either of the two candidates for $B_{11}$. This fixes the reflection convention. For each $j=2,\ldots,k-2$, select the candidates for $B_{2j},B_{1j},B_{1,j+1}$ satisfying
$$
p_{j+1} B_{2j}B_{11}=p_2 B_{1j}B_{1,j+1}.
$$
There are at most eight possibilities. The exponent relation here is exactly the minimal relation $v_{2j}=-w_1+w_j+w_{j+1}$ used above. Thus after fixing $B_{11}$ a second generic solution cannot reverse a proper nonempty subset of the other three branches. The relation holds for the true data, and also for their common conjugation. Consequently each test has exactly one completion once the reflection convention is fixed. These local tests recover every $B_{1j}$.

Choose $x_1=\sqrt{p_1}$ to fix the continuous rotation. Then sequentially put
$$
x_{j+1}=x_1 x_j p_{j+1}/B_{1j}.
$$
This reconstructs a representative of the orbit. With rational inputs each local branch test uses at most four quadratic roots, hence comparison takes place in a number field of degree bounded independently of $k$. The selected roots and the displayed recurrence give a polynomial-size arithmetic expression for the output, without any requirement to expand it into a common extension field.
