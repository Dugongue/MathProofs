# Exact affine equivalence of cubic polynomials in characteristic three

Let $k=\mathbb F_q$, with $q$ a power of three. For formal polynomials $f,g$ of degree at most three, homogenize them to cubics $F,G$ on $k^{n+1}$, and let $c$ be the greater contraction rank of their polarizations. One can decide affine equivalence, find one exact affine substitution when it exists, and count all such substitutions in time
$$
q^{\widetilde O(c^{3/2})}\operatorname{poly}(n,\log q).
$$
The bound becomes $q^{O(c)}\operatorname{poly}(n,\log q)$ if Graph Isomorphism is in $\mathsf P$. More generally these conclusions hold for homogeneous cubics with arbitrary lists of labelled linear marks, with an additional polynomial factor in the input size of the marks. Automorphism generators have the same bound for $c>0$, and an additional $q\operatorname{poly}(n,\log q)$ bound for $c=0$.

## Recover the affine chart as a linear mark

Write $V=k^{n+1}$ with coordinates $(x,t)$ and put $\tau(x,t)=t$. Every invertible linear $S$ with $\tau S=\tau$ has the form $(x,t)\mapsto(Ax+bt,t)$. Homogenization identifies exact formal affine substitution with the equations $G\circ S=F$ and $\tau S=\tau$, preserving the number of witnesses. For the general marked problem put all marks into $\tau_f:V_f\to E$ and $\tau_g:V_g\to E$, where $E$ is a labelled vector space. A transporter satisfies $G\circ S=F$ and $\tau_g S=\tau_f$.

## Reduce to the polarization quotients

Use the full polarization $P_F(x,y,z)=[s_1s_2s_3]F(s_1x+s_2y+s_3z)$. For every non-pure cubic monomial, evaluating its polarization on the corresponding basis triple reads its coefficient multiplied by $2$ or $1$. The pure cubes have zero polarization since $6=0$. Thus the kernel consists of exactly the pure-cube sums. Over $k$ each is uniquely a cube of a linear functional by Frobenius bijectivity.

Let $R_f,R_g$ be the contraction radicals, and reject if their dimensions differ. Choose complements $C_f,C_g$ of dimension $c$. In these bases the monomial check gives
$$
F(x+r)=F_C(x)+\ell_f(r)^3,\qquad G(y+r')=G_C(y)+\ell_g(r')^3.
$$
Indeed every non-pure coefficient involving a radical basis vector has zero corresponding tensor entry. A polarization transporter is exactly a block map
$$
x+r\longmapsto Bx+Wx+Ur,
$$
where $B:C_f\to C_g$ transports the quotient trilinear forms, $U:R_f\to R_g$ is invertible, and $W:C_f\to R_g$ is any linear map.

Combine the radical data in $L_i=(\tau_i|_{R_i},\ell_i):R_i\to E\oplus k$. The radical equation $L_g U=L_f$ admits an invertible $U$ exactly when $\operatorname{im}L_f=\operatorname{im}L_g=J$. To verify this, choose a lifted basis of $J$ and any basis of its preimage kernel on each side. Then $U$ consists of an arbitrary isomorphism on these kernels, the fixed identity on the lifted quotient, and an arbitrary shear into the target kernel. For $j=\dim J$ and $r=\dim R_f$, this gives $q^{j(r-j)}|\operatorname{GL}_{r-j}(k)|$ choices.

For a quotient polarization transporter $B$, let $d_B$ be the unique linear functional on $C_f$ with $d_B^3=F_C-G_C\circ B$. The remaining equations are
$$
L_g W=(\tau_f|_{C_f}-\tau_g|_{C_g}B,\ d_B).
$$
They are sufficient since the cube of a sum is the sum of the cubes. A solution exists precisely when the right side has image contained in $J$, and then there are $q^{c(r-j)}$ choices. Each admissible $B$ therefore lifts with the same multiplicity
$$
q^{(c+j)(r-j)}|\operatorname{GL}_{r-j}(k)|.
\tag{1}
$$

## Describe the admissible quotient substitutions

Write $I=\operatorname{pr}_E J$ and let $\bar\tau_f,\bar\tau_g$ be the marks from the chosen complements into $E/I$.

If $(0,1)\in J$, then $J=I\oplus k$. Every quotient polarization transporter satisfying $\bar\tau_g B=\bar\tau_f$ is admissible. The last coordinate of $L_gW$ can absorb any pure-cube discrepancy.

If $(0,1)\notin J$, then $J$ is the graph of a linear functional $\lambda:I\to k$. Extend $\lambda$ linearly to $E$, using the same extension for both inputs, and form
$$
H_f=F_C-(\lambda\tau_f|_{C_f})^3,\qquad
H_g=G_C-(\lambda\tau_g|_{C_g})^3.
$$
A quotient polarization transporter is admissible exactly when $\bar\tau_g B=\bar\tau_f$ and $H_g\circ B=H_f$. The graph condition requires $d_B=\lambda(\tau_f|_{C_f}-\tau_g|_{C_g}B)$. Cubing gives the adjusted cubic equality, and injectivity of cubing recovers the graph condition. Any two extensions of $\lambda$ give the same criterion, since the mark equation puts the difference of the original marks in $I$.

## Compute marked polarization transporters with linear-length tensors

Reject unequal images of the quotient marks. Replace their shared image by $D$ with a chosen basis $d_1,\ldots,d_d$, where $d\le c$. We need trilinear isometries $B$ with exact $\bar\tau_g B=\bar\tau_f$, optionally also with an ordered list of independent projective-line constraints on the argument spaces.

Put the trilinear form in three covector blocks linked by equality. Add a primal argument block linked by inverse transpose to the covector blocks. On the primal block use the deterministic Frucht incidence gadget for its line constraints, changing bases separately on the two inputs first. For $a\ge18$ lines use the edge-vertex incidence space of the Frucht graph with one edge subdivided to give $a$ edges. Put its edge contraction image on the pinned coordinate span. The support permutations of the two matrix factors give a side-preserving incidence graph automorphism, hence the identity. The resulting nonzero diagonals show that any further off-diagonal entry would require inclusion between distinct edge endpoint sets or vertex incident-edge sets. Those sets are incomparable by simplicity and minimum degree two. All diagonal actions extend by rescaling incidence directions. For $a<18$, pin each coordinate line with its own rank-one block and private one-dimensional directions.

Add a block for $D$ in the second tensor leg and use the same coordinate-line gadget on all its basis lines, with fresh auxiliary legs. Introduce one-dimensional blocks $L_1,L_2,L_3$, one per leg, all linked by equality. Put $1\otimes1\otimes1$ in $L_1\otimes L_2\otimes L_3$; their common scalar $u$ obeys $u^3=1$, hence $u=1$ in characteristic three. Put $1\otimes(\sum_i d_i)\otimes1$ in $L_1\otimes D\otimes L_3$. The diagonal action on $D$ must fix that vector and is therefore the identity. Finally put the quotient mark in $C^*\otimes D\otimes L_3$. Equivariance is exactly the required mark equation. If $d=0$, omit $D$ and its auxiliary blocks. The number of blocks is bounded by an absolute constant, including the fewer-than-18 cases, and all leg lengths are $O(c)$. Linked-partition conversion and partition removal preserve linear length. [Grochow and Qiao IV, Sections 4.5 and 5](https://arxiv.org/html/2306.16317#S5) · [Frucht](https://doi.org/10.4153/CJM-1949-033-6)

Use these decisions to assign images of the lines of an ordered argument basis one by one, testing at most $q^c$ candidate lines per step. Once all lines are pinned, test at most $(q-1)^c$ scalar combinations directly. For the target group, let $G_i$ fix the first $i$ lines. Enumerate the orbit of the next line using the same decisions and recover one witness for every orbit point with that pinned prefix. These witnesses form a transversal of $G_{i+1}$ in $G_i$. Enumerate the diagonal elements of $G_c$ directly. The orders multiply by the orbit sizes and the transversals together with $G_c$ generate the group. This yields one witness, the exact group order and generators using $q^{O(c)}$ queries and work.

## Recover, count and lift

If the last coordinate is absorbed by $J$, use the whole marked polarization transporter coset. Otherwise push $H_f$ forward by one marked polarization transporter and explore its orbit under the target marked polarization group. All states lie in the $q^c$-element affine polarization fiber of $H_g$. In fixed coordinates store each state by its pure-cube coefficients. Each generator acts by an affine transformation of those coefficients. Breadth-first search records a witness word if $H_g$ is reached and finds the orbit size $m$. In a nonempty match the number of quotient transporters is the marked polarization group order divided by $m$. Schreier edge products generate the cubic stabilizer. Lift its generators using the two radical equations, and adjoin generators of the kernel, which consists of the elementary shears and a linear group on $\ker L_g$. Listing all nonzero determinant scalars fits $q^{O(c)}$ for $c>0$. Multiply the quotient count by (1). For $c=0$ there are no tensor queries and the decisions, counts and witness reduce to radical linear systems and ordinary linear group orders.

Grochow–Qiao IV converts the linear-length tensor queries to alternating matrix-space congruence of length $O(c)$. Its $q^{\widetilde O(c^{3/2})}$ runtime absorbs the $q^{O(c)}$ overhead. The backend can be made deterministic by enumerating its two individualizing matrices and testing the rank condition on their kernel as in Section III-E. Their small side is of order the square root of the padded matrix dimension, so enumeration preserves the exponent. For the conditional bound, encode the three argument vector spaces by their addition and labelled scalar tables and encode the tensor by its trilinear value table. The fixed-arity relational structure and its colored incidence graph have size $q^{O(c)}$ and have precisely the corresponding linear tensor transporters as structure isomorphisms. [Grochow and Qiao IV, Theorem 2.1](https://arxiv.org/html/2306.16317#S2) · [Ivanyos et al., Theorem I.4 and Section III-E](https://chuanqizhang.com/assets/pdf/pdf/focs24.pdf)

## A translation example

Over $k$, put $f_a(x)=x^3-x+a$. All degree-three homogenizations of this family have the same polarization, since they differ by multiples of $t^3$. Comparing leading coefficients forces the linear part of an affine transporter to be $1$, and translation by $b$ changes the constant by $b^3-b$. This map has kernel $\mathbb F_3$ and image the kernel of the field trace to $\mathbb F_3$. Indeed the trace annihilates every such difference and the two subspaces have the same codimension, since the trace is a nonzero linear map of a finite separable extension. Thus the number of affine transporters between $f_a,f_{a'}$ is three if their traces are equal and zero otherwise.

Affine polynomial equivalence has been studied by Kayal and Grochow. Here the radical's joint image with the labelled marks determines which mark equations and which adjusted pure-cube equation survive, with an explicit fiber size for lifting every quotient witness. The proof is in prose and publication priority remains unverified. [Kayal](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/Poly20Equiv.pdf) · [Grochow](https://arxiv.org/abs/1112.2012)

[Affine.py](Affine.py) checks the counting formula on 512 ordered ternary cubic pairs with labelled marks, including each radical regime. It also checks all 81 ordered constant pairs in the trace example over the field of nine elements.

[MarkedCube.lean](MarkedCube.lean) independently checks the algebraic identity that converts the graph condition to the adjusted cubic equality over any commutative ring of characteristic three. The kernel and axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`.
