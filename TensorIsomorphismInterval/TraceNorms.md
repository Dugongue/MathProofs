# Six extension-field norm classes in the interval

For this packet the base field is $F=\mathbb F_3$, and the fields $E_2=\mathbb F_9$ and $E_3=\mathbb F_{27}$ have fixed bases over $F$. Encode finite-dimensional trilinear forms in raw dense coordinates. Unless a list of blocks is specified, require each input to be concise over its coefficient field with local centroid and residue equal to that coefficient field. For a list, require this of every block. These recognizable conditions define ordinary decision languages by rejecting inputs that fail them.

Over $E_r$, allow the same power $\sigma^k$ of the base-field Frobenius in all three modes. A transporter is $g_i=A_i\sigma^k$ in each mode, with each $A_i$ invertible over $E_r$, satisfying
$$
 S(g_1x,g_2y,g_3z)=\sigma^k(T(x,y,z)).
$$
For each such transporter put
$$
        d_i=(-1)^{(r-1)k n_i}N_{E_r/F}(\det_{E_r} A_i),
$$
where $n_i$ is the $E_r$-dimension of the mode. The six candidates are the lower closures under polynomial-time many-one reductions of the following problems.

| Complete problem | Constraint |
| --- | --- |
| Cubic-extension one-mode norm TI | $r=3$, and $d_1=1$. |
| Cubic-extension two-mode norm TI | $r=3$, and $d_1=d_2=1$. |
| Cubic-extension three-mode norm TI | $r=3$, and $d_1=d_2=d_3=1$. |
| Cubic-extension product norm TI | $r=3$, and $d_1d_2d_3=1$. |
| Quadratic-extension norm TI | $r=2$, and $d_1=d_2=d_3=1$, including the displayed Frobenius signs. |
| Mixed quadratic–cubic block norm TI | Each input is a list of both kinds of blocks. Permit a block permutation among compatible formats of equal field degree and independent Frobenius choices within blocks. Require determinant one of all three resulting $F$-linear maps, so the determinant of each full mode includes its block-permutation sign. |

## Exact trace reduction

Replace an $E_r$-trilinear form $T$ by $\operatorname{Tr}_{E_r/F}T$, using the three underlying $F$-spaces. The trace pairing is nondegenerate. Thus the traced form is concise, since a nonzero contraction over $E_r$ takes a nonzero value that can be scaled to have nonzero trace. Its $F$-centroid contains simultaneous multiplication by $E_r$ in the three modes. Since the centroid of a concise form is commutative, every centroid element commutes with these actions and is $E_r$-linear. The remaining centroid equations lift from trace equality to $E_r$-valued equality by scaling one argument and using the trace pairing. Thus its $F$-centroid is the original $E_r$-centroid, with the same elements viewed as $F$-linear operators.

The $E_r$ scalars are intrinsically identifiable as the elements $c$ of the local centroid satisfying $c^{3^r}=c$. They account for every possible residue in the given residue field, and two fixed elements with the same residue have a nilpotent difference fixed by Frobenius, hence are equal. An $F$-transporter between traced forms conjugates their centroids and so induces one common automorphism of this intrinsic scalar field on the three modes. It must be semilinear with the same exponent $k$ in all modes. Conversely and exactly, a traced transporter with that semilinearity satisfies the displayed $E_r$-equation. Vary $\lambda\in E_r$ by replacing $x$ with $\lambda x$ in the trace identity. Invariance of trace under $\sigma^k$ implies
$$
 \operatorname{Tr}_{E_r/F}\!\left(\lambda\bigl(\sigma^{-k}(S(g_1x,g_2y,g_3z))-T(x,y,z)\bigr)\right)=0.
$$
The trace pairing forces the desired equality.

The determinant of an $E_r$-linear map on the underlying $F$-space is the norm of its $E_r$-determinant. This follows by factoring an invertible matrix into transvections and diagonal maps and applying the norm formula to multiplication on a field line. On one field line Frobenius acts by an $r$-cycle in a normal basis. Its sign on $n_i$ copies at power $k$ is $(-1)^{(r-1)k n_i}$. Hence $d_i$ above is precisely the determinant of the traced transporter in mode $i$. On a list, direct-sum the traced tensors. Its centroid primitive factors distinguish the blocks; the residue degrees distinguish the two types. An $F$-transporter restricts to the claimed within-block maps, with exactly the block permutation contribution to the total determinant. Arbitrary compatible block maps and a permutation conversely give a transporter.

Recognition of the centroid conditions uses ordinary linear equations for the centroid and the kernel of a large Frobenius power for its nilradical. A finite commutative $E_r$-algebra has the required local residue exactly when its quotient by the nilradical has dimension one over $E_r$. All tests and trace computations take polynomial time. The traced determinant constraints on a single block belong to the indicated sign-subgroup problem in [the determinant proof](DeterminantGroups.md). The mixed problem reduces directly to full SL-TI. These are many-one upper reductions.

## Determinant-one witnesses for the lower reductions

First reduce $\mathrm{TI}_F$ to ordinary TI over $E_r$ with every output coefficient in $F$ and no extra isomorphisms from extension. Retain the original tensor as one part of a typed tensor system. For each of its three spaces $V$, attach the symmetric algebra truncated above degree three, the inclusion of $V$ in degree one, and the linear map $V\to\operatorname{Sym}^3(V)$ taking each coordinate vector $e_j$ to $e_j^3$, into the truncated algebra. The algebra multiplication is one trilinear-order component. Its isomorphism that preserves the degree-one inclusion is determined by its action $g$ on the algebra generators. Equivariance of the cube map then gives $g_{ij}^3=g_{ij}$ in every entry, using characteristic three. This forces precisely the base-field actions. Conversely any base-field transporter extends. The system has fixed signature and polynomial dimension. The fixed-signature tensor-system compiler uses block copies, zero blocks and identity rank tags and can be applied with coefficients in $F$; its correctness holds over $E_r$ for the same block construction. The resulting ordinary tensor pair over $E_r$ still has coefficients in $F$. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1 and Appendix B](https://arxiv.org/html/2306.03135v2#S4)

Now convert this ordinary $E_r$-pair to the scalar-centroid alternating suspension in [the structural proof](Structural.md). Use Grochow–Qiao's alternating matrix-space reduction, with its fixed $0,1,-1$ blocks, followed by the full cross-space suspension. Choose the dimension $b$ of its old matrix space divisible by $3^r-1$, adding at least one zero radical coordinate, and take $a=b^2+2b+1$. Ordered slice bases can be selected over $F$, since rank of a base-field matrix is unchanged by extension. Hence this second map still produces all coefficients in $F$. Its output has scalar centroid over $E_r$. Every positive ordinary pair has a transporter whose three $E_r$-determinants equal one, by choosing the determinant in the added radical coordinate and then in the cross-space factor. Every ordinary isomorphism of these outputs reflects an ordinary $E_r$-isomorphism of the compiled pair. These are exactly the two lower-reduction properties proved in the structural proof. [Grochow and Qiao, Theorem 2.1](https://arxiv.org/html/2306.16317v2#S2)

For each of the single-block problems use this output. A positive pair uses $k=0$ and the determinant-one transporter. For a negative pair, applying any $\sigma^k$ to the coordinates has no effect on these outputs, since their entries are in $F$; so a semilinear isomorphism would imply an ordinary $E_r$-isomorphism and contradict the base-field source. For the mixed problem use one $E_3$ hard block and a common fixed $E_2$ scalar trilinear block $xyz$, with identity on the latter in a positive case. The differing residue degrees prevent the active block from exchanging with the fixed block. These are many-one lower reductions from $\mathrm{TI}_F$.

The determinant correction within the concise alternating suspension is useful here because a zero padding coordinate in an extension-field block would break conciseness. The reduction uses trace, Frobenius and volume data already present in the earlier constructions. All six claimed containments are inclusive. They do not imply six different many-one degrees or strictness at either endpoint.
