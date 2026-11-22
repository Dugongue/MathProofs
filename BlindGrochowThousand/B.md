# Determinant profiles for rooted matrix tuples

Let $K$ be a field and let $D=\operatorname{diag}(a_i)$ with distinct
labels $a_i$. Choose a root index $r$. Let $C$ have a column of ones at
$r$ and zeros elsewhere, and let $C_v$ have $i$-th entry $v_i/v_r$ in
that column, where $v_r\ne0$. Across all simultaneous transporters
$$
 X D=D X,\qquad X C=C_v X,
$$
the exact determinant range is
$$
 \left\{c^n\prod_i v_i\;:\;c\in K\right\}.
$$
Here $n$ is the common matrix side. This assertion includes the zero
determinant. A nonzero determinant is equivalent to an invertible
transporter, which then gives simultaneous conjugacy.

Indeed, distinct labels force $X$ diagonal. Comparing entry $(i,r)$ in
the column transport equation forces $X_{ii}=v_i X_{rr}/v_r$. Therefore
the only possible transporter is $\operatorname{diag}(c v_i)$ with
$c=X_{rr}/v_r$. Every such diagonal matrix satisfies both equations,
and its determinant has the claimed value. This family makes the standard
centralizer determinant mechanism explicit for an anchored two-matrix
tuple. The closely related problem of determinant images of centralizers
of individual matrices has a detailed classical theory. [Britnell and Wildon](https://arxiv.org/abs/1001.0811)

When all $v_i$ are nonzero, the invertible transporters realize one
coset of the $n$-th powers in $K^\times$. Over $\mathbb F_q$, this
gives an orbit splitting of size $\gcd(n,q-1)$ under passage from
ordinary conjugacy to determinant-one conjugacy for the fixed source
tuple. The Lean assertion is the exact attainable-set formula above.

## Concrete proof inventory

The source states one general determinant-profile theorem and 249
concrete matrix results over the prime fields with $5,7,11,13,17,19,23,29,31,37$
elements. The dimensions range from 2 to 8. Each case takes
$a_i=i+s$, twists $v_r$ by one nonzero field element, and sets the other
$v_i$ to 1. All triples of field size, dimension and shift are distinct.
For equal field size and dimension, different shifts give different
anchor traces, because $0<n<q$ and $\operatorname{tr}D$ changes by
$n$ times the shift difference. Thus shift variation supplies different
ordinary similarity classes of the anchor.

| Finite statement | Count |
|---|---:|
| A determinant-one transporter exists | 83 |
| A specified nonzero determinant is attainable and determinant one is excluded | 83 |
| The attainable determinants equal the displayed list, for every field element | 83 |

For example, $n=2$, $q=7$, $s=1$, $v_r=5$ gives a transporter of
determinant 5 and no determinant-one transporter. The determinant range
is the twist of the squares. Over $\mathbb F_{11}$ with $n=5$ and
$v_r=7$, the nonzero range is exactly $\{4,7\}$.

The generator proposes twists and finite images with integer modular
arithmetic. In the Lean source, the general classification reduces each
matrix statement to the corresponding bounded field predicate. Lean
then checks each finite predicate by kernel reduction. The concrete
statements test the classification with varying inputs and supply
explicit isomorphism examples. Their count does not represent separate
general classification theorems.

## Discovery provenance

The anonymous second queue includes motif 408910 with producers 74081,
47756. Its
cycle-type and detector-dimension inputs suggested rigid anchors
with a low-rank second matrix. Motif 495962 with producers 109675
and 79498 suggested isolating the residual power obstruction.
These are interpretations after the numeric queue was frozen. The
proof uses the resulting matrix structure and is checked separately.
[Proof source](B.lean) · [Reproducible proposal generator](B-gen.py)
