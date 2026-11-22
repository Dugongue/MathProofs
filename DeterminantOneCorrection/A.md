# An odd determinant character for supplied-transporter hardness

**Theorem.** Fix a finite field $k=\mathbb F_q$ for which $q-1$ has an odd prime divisor. Ordinary three-tensor isomorphism over $k$ reduces in deterministic polynomial time to determinant-one three-tensor isomorphism between genuine unital associative multiplication tensors, with a supplied ordinary transporter. Both output algebras are centrally indecomposable, meaning that their centers have only the idempotents 0 and 1. The result applies to every fixed field of characteristic two with more than two elements.

We use the TI-hardness of isomorphism for commutative local algebras with residue field $k$. In the reduction of Grochow and Qiao, symmetric matrix-space isometry first supplies commutative 3-nilpotent algebras, then one adjoins a unit. The nilpotent algebra is the maximal ideal of the resulting algebra, and its quotient is $k$. [Grochow and Qiao, Corollaries 7.4 and 8.5](https://arxiv.org/abs/1907.00309)

## Colored projective lines inside a multiplication algebra

Choose an odd prime $\ell\mid q-1$, put $L=\ell^{v_\ell(q-1)}$, and choose $\rho\in k^\times$ of order $\ell$. For local input algebras $A,A'$ as above, build an algebra from three layers with scalar endpoint corners. The middle layer consists of the following blocks.

- For $i\in\mathbb Z/\ell$, use $B_i=M_L(A_i)$, where $A_0=A$ and $A_i=A'$ for $i\ne 0$. Put $d_i=L$ and associate the vector $w_i=(\rho^i,1)$.
- Use one scalar block $B_i=k$ at $(1,0)$ and $r$ scalar blocks at $(0,1)$, with $d_i=1$. Take $r=L-3$ when $L>3$, and $r=3$ when $L=3$. Thus $r\ge2$ and $L\mid r+3$.

Every block $B_i$ has a quotient $\overline B_i=M_{d_i}(k)$. Write $B=\prod_i B_i$, $U_i=k^{1\times d_i}$, $V_i=k^{d_i\times1}$, $U=\bigoplus_i U_i$, and $V=\bigoplus_i V_i$. Let $W=k^2$. Form the algebra
$$
D(A,A')=
\begin{pmatrix}
 k&U&W\\
 0&B&V\\
 0&0&k
\end{pmatrix}.
$$
In this upper triangular notation, the ordinary block product uses the quotient right action on $U_i$, quotient left action on $V_i$, scalar action on $W$, and the product
$$
\beta(u,v)=\sum_i (u_i v_i)w_i .
$$
The identity $\beta(ub,v)=\beta(u,bv)$ follows from row and column multiplication in each quotient $M_{d_i}(k)$. Together with bilinearity and scalar compatibility, it proves associativity. The diagonal identity is the unit.

The radical is the ideal with zero scalar endpoint entries, radical middle entries, and arbitrary strictly upper entries. Its quotient is semisimple. The ideal itself is nilpotent because its image modulo the strictly upper ideal is nilpotent, while the cube of the strictly upper ideal is zero. Thus the claimed ideal is indeed the radical.

## What an automorphism can do

The original block idempotents lift the primitive central idempotents of the semisimple quotient. Any automorphism permutes their classes. It can be adjusted by inner conjugation to permute the idempotents themselves. In detail, for two complete orthogonal families $(e_i)$ and $(f_i)$ with $f_i\equiv e_i\pmod{\operatorname{rad}D}$, the unit $u=\sum_i f_i e_i$ is congruent to 1 and satisfies $ue_i=f_i u$. Conjugation by $u$ has determinant 1 because left multiplication by $u$ and right multiplication by $u^{-1}$ are unipotent.

Once the idempotents are aligned, the directed pattern of nonzero off-diagonal corners identifies the two endpoint idempotents. The source has outgoing corners and no incoming corners, and the sink has the reverse pattern. Each middle block has both. The matrix sizes of the simple quotient blocks distinguish the scalar markers from the input blocks. The induced linear automorphism $S$ on $W$ preserves the multiset of marker lines. Their distinct multiplicities 1 and $r$ pin $(1,0)$ and $(0,1)$ separately. Hence $S=\operatorname{diag}(x,y)$ with $x,y\ne 0$.

Consider a middle block sent from $i$ to $j$. Its induced quotient isomorphism is inner on $M_{d_i}(k)$, say $b\mapsto T b T^{-1}$. The semilinear arrow maps therefore have the form
$$
 u\longmapsto a_i uT^{-1},\qquad v\longmapsto b_i Tv
$$
for nonzero scalars $a_i,b_i$. Indeed, after removing the indicated $T$ actions, the maps commute with a full matrix algebra on its standard row and column modules, so they are scalar. The product relation gives $S w_i=\lambda_i w_j$ for $\lambda_i=a_i b_i$. The product of the two arrow determinants is $\lambda_i^{d_i}$, since the determinants of $T$ and $T^{-1}$ cancel. If corner blocks are permuted, the extra signs from permuting their ordered bases have order dividing 2.

Each $k$-automorphism of $M_L(A_i)$ has determinant in $(k^\times)^L$. Here is a direct argument. The images of the matrix units under such an automorphism decompose the right $A_i$-module $A_i^L$ into $L$ isomorphic summands. Each summand is rank one free by Krull–Schmidt applied to $A_i^L\simeq P^L$. A basis built using the image matrix units then conjugates them to the original units. An automorphism fixing the matrix units is entrywise application of an automorphism of $A_i$, with determinant a perfect $L^2$-th power. Left and right multiplication on the matrix algebra act on $L$ independent columns and rows, respectively. Their determinants are $L$-th powers, which also proves the claim for the conjugating inner automorphism.

## The determinant test

Suppose $A\not\simeq A'$. A middle block isomorphism induces an isomorphism on centers, so the sole block of type $M_L(A)$ cannot move. Its associated slope is 1, forcing $x=y=t$. All input blocks are then fixed because their slopes are distinct. Their middle and arrow determinants lie in $(k^\times)^L$. The two-dimensional space $W$ and the scalar marker arrows together contribute $t^2t^{1+r}=t^{3+r}$, also an $L$-th power. Permutation signs are $L$-th powers because $L$ is odd. Hence every determinant lies in $(k^\times)^L$, whose elements have order prime to $\ell$.

Suppose $A\simeq A'$. Choose identifications of all $A_i$ with one common algebra. Rotate the input blocks by $i\mapsto i+1$ using these identifications, apply $S=\operatorname{diag}(\rho,1)$ on $W$, and transport the associated standard row and column modules identically in their given coordinates. The quotient maps under the chosen identifications fix $k$, so the module actions are respected. As $Sw_i=w_{i+1}$, the input products are respected. At the marker $(1,0)$, multiply its incoming row module by $\rho$. The other marker arrows stay fixed. This defines an automorphism. The maps within the input cycle have product determinant 1 because the identifications telescope, and the block cycles have odd length $\ell$, giving sign 1. The determinant on $W$ is $\rho$ and the scaled marker arrow has determinant $\rho$. Thus the total determinant is $\rho^2$, of order $\ell$. We have proved
$$
\rho^2\in\det\operatorname{Aut}_k D(A,A')\quad\Longleftrightarrow\quad A\simeq A'.
$$

For central indecomposability, a central idempotent commutes with every block idempotent, hence is diagonal. The nonzero space $W$ forces the two scalar endpoints to agree at some $t\in\{0,1\}$. Commuting with the row and column corners then forces every middle quotient entry to be $tI$. If $t=0$ each middle idempotent lies in a nilpotent ideal and is zero. If $t=1$ the complementary idempotent is zero by the same argument.

## From a determinant character to the promised tensor instance

Let $\mu$ be the multiplication of $D(A,A')$. Choose a known linear map $f$ of determinant $\rho^{-2}$ by scaling one coordinate in $W$, leaving the unit fixed. Define the second multiplication by
$$
\mu'(x,y)=f\,\mu(f^{-1}x,f^{-1}y).
$$
This is a genuine unital associative product, and $(f,f,f)$ is the supplied ordinary bilinear-map transporter. In tensor coordinates, the input legs use the corresponding inverse transposes.

For associative unital products, three independent invertible maps satisfying $Z(xy)=X(x)Y(y)$ have an underlying algebra isomorphism $\sigma$ with determinant $\det X\det Y/\det Z$. In fact, put $a=X(1)$ and $b=Y(1)$. Evaluating at 1 gives $Z(x)=aY(x)=X(x)b$, and surjectivity makes multiplication by $a$ on the left and by $b$ on the right invertible. Then $\sigma(x)=a^{-1}Z(x)b^{-1}$ is an algebra isomorphism, and the determinant statement follows by cancellation. Thus a determinant-one transporter exists exactly when an algebra isomorphism of determinant 1 exists. Here every such isomorphism has the form $f\alpha$, with $\alpha$ an automorphism of $D(A,A')$. It has determinant 1 exactly when $\det\alpha=\rho^2$, which is precisely the desired input answer.

The output dimension is linear in the two input algebra dimensions for fixed $k$, with constants depending on $\ell$ and $L$. All structure constants and the supplied transporter are explicit. Over $\mathbb F_2$, the supplied-transporter promise alone forces a yes answer, since every invertible matrix already has determinant 1.

The algebra construction and reduction above are complete written proofs. The companion Lean file isolates the paired arrow determinant identity and the suppression of the common scalar. The prior literature supplies the hardness of the starting class. Priority of the odd-order determinant gadget remains open. [Lean components](A.lean)

## Exact determinant image and orbit counts over every fixed finite field

The construction can also make the determinant image exact and include fields whose unit group has power-of-two order. Choose any prime $\ell\mid q-1$, put $L=\ell^{v_\ell(q-1)}$ and $h=(q-1)/L$, and let $H=(k^\times)^L$, of order $h$. Retain the $\ell$ input blocks at $(\rho^i,1)$. Use just two marker blocks, both full matrix algebras over $k$. Their widths are
$$
d_\infty=2L,\qquad d_0=L(c-\ell-2)-2,\qquad c=1+h(\ell+5).
$$
Use the marker of width $d_\infty$ at $(1,0)$ and the marker of width $d_0$ at $(0,1)$, with the standard row and column modules of the corresponding widths. These widths are distinct from each other and from $L$. Their matrix sizes pin the two lines separately. Their internal automorphism determinants are 1 since the only automorphisms of a full matrix algebra over $k$ are inner and the row and column determinant contributions of inner conjugation cancel exactly.

All rotations of the input slopes have ratio $x/y$ in $\langle\rho\rangle$, since the slope 1 must map into the displayed set of slopes. An automorphism with ratio 1 fixes every input block as a block. In a general permutation of isomorphic input blocks, choose identifications with a common model for each isomorphism class. Their determinants telescope around each permutation cycle, leaving only determinants of automorphisms of the model. Those lie in $H$. The determinant contribution of the arrow modules at input blocks is always in $H$. The marker arrows contribute $x^{d_\infty}y^{d_0}$, and $W$ contributes $xy$. Their product is an element of $H\langle\rho\rangle$ because $d_\infty+d_0+2=L(c-\ell)$ and $d_\infty+1\equiv1\bmod\ell$. No extra block permutation sign affects this bound. A nontrivial rotation has a single cycle of length $\ell$, which is odd unless $\ell=2$. If $\ell=2$, both the input middle blocks and their arrow modules have even dimension because $L$ is even. The marker blocks and endpoints never move.

Every element of $H$ occurs already through the scalar action $S=tI$. Keep the middle blocks fixed and multiply each row arrow by $t$, preserving all the products. Its determinant is
$$
t^{2+\ell L+d_\infty+d_0}=t^{Lc}.
$$
Since $\gcd(c,h)=1$, these values exhaust $H$. If the inputs are isomorphic, the automorphism rotating the input blocks by 1 has $S=\operatorname{diag}(\rho,1)$. At the marker at infinity, multiply its row module by $\rho$. The determinant is $\rho^{1+d_\infty}=\rho$, with the input contributions and permutation signs equal to 1 as above. If the inputs are nonisomorphic, the unique input of its isomorphism type pins the slope 1, so the ratio is 1 and all determinants lie in $H$. We have computed the exact determinant image:
$$
\det\operatorname{Aut}_k D(A,A')=
\begin{cases}
H\langle\rho\rangle,& A\simeq A',\\
H,& A\not\simeq A'.
\end{cases}
$$
In particular twisting by a known determinant $\rho^{-1}$ proves the promised hardness for every fixed $q>2$.

In both variants the radical cubes to zero. The strictly upper ideal cubes to zero by the three-layer construction. The middle diagonal radicals cube to zero because the source nilpotent ideals do, and they annihilate the off-diagonal modules since these act through the semisimple quotient. This shows hardness within the stated centrally indecomposable class even with radical cube zero. The transported product has the same properties.

The maps sending a unit to the determinant of its left or right multiplication each surject onto $k^\times$. For left multiplication, scale the sink diagonal alone, which scales just its one-dimensional scalar corner. For right multiplication, use the source diagonal. The determinant ratio of the multiplication stabilizer then identifies its determinant image with the preimage of $\det\operatorname{Aut}(D)$ under $(a,b,c)\mapsto ab/c$. The kernel of the three determinant maps is the special linear group on the three legs. Thus the number of special-linear orbits in the ordinary orbit is the index of the computed determinant image. The reduction distinguishes exactly $L$ orbits from exactly $L/\ell$ orbits. For example, over $\mathbb F_4$ it distinguishes three from one.

The exact-image variant and its orbit count are written proofs. Its construction has dimension linear in the input algebra dimensions for each fixed field, with field-dependent constants.
