# Actual subgroup transport in class-two groups of exponent four

**Theorem.** Let $G,G'$ be finite class-two $2$-groups given by Cayley tables, of exponent dividing four. For up to three ordered actual subgroup marks, transporter decision, witness search, exact counting, and stabilizer generation reduce deterministically in polynomial time to ordinary class-two $2$-group isomorphism decision. The oracle groups have order $N^{O(1)}$ for $N=\max(|G|,|G'|)$. The marks may be nonnormal and may intersect.

More generally the reduction works with an elementary abelian central kernel $C$ and elementary abelian quotient $A=G/C$, requiring the transporter to preserve the corresponding kernel. It works for any fixed number of marks if the central intersections $K_i=H_i\cap C$ on each side are spanned by subsets of one common basis of the kernel on that side. In the exponent-four case use the characteristic kernel $C=\Phi(G)=G^2[G,G]$. The class-two fourth-power identity forces $[x,y]^6=1$, since $x^4,y^4,(xy)^4$ are all trivial. Thus all commutators have order dividing two, all squares are central, and both $C$ and $A$ are elementary abelian.

## 1. Exact central correction

Write $U_i=\pi(H_i)\le A$. The original extension records are the commutator $\beta:A^2\to C$ and the square $q:A\to C$. The latter is well defined because $C$ is central and killed by two. A pair of linear isomorphisms $\alpha:A\to A'$, $\gamma:C\to C'$ lifts precisely when it preserves both records. For sufficiency take any target lifts of the images of a source quotient basis. The original central relations, basis commutators, and lift squares give a presentation by collection, and all hold for those images. The resulting homomorphism is bijective on the kernel and quotient and hence on the whole group. Require also that the pair carry all $U_i,K_i$ to $U'_i,K'_i$.

For any initial lift $f$ of such a pair, compare $f(H_i)$ with $H'_i$ in $G'/K'_i$. Both define homomorphic sections over $U'_i$. Their difference, in the direction target minus transported source, is a linear map $d_i:U'_i\to C'/K'_i$, since the difference is central. Changing the lift of the base pair amounts to postcomposing with $g\mapsto g\,s(gC')$ for a linear map $s:A'\to C'$. Thus a marked lift exists exactly when one $s$ simultaneously solves $s|_{U'_i}\bmod K'_i=d_i$ for every $i$. This system is solved by Gaussian elimination after a base pair is found.

## 2. Ordered-product quadratic records

For each nonempty subset $J$ of the indices put $K_J=\sum_{i\in J}K_i$, $D_J=C/K_J$, and $R_J=\ker(\bigoplus_{i\in J} U_i\to A)$, where the map sums the inclusions. The image of $H_i$ in $G/K_J$, for $i\in J$, is a section $s_i^J$ over $U_i$. On $r=(u_i)_{i\in J}\in R_J$ define
$$
t_J(r)=\prod_{i\in J} s_i^J(u_i)\in D_J
$$
using increasing index order. This is well defined since all changes of lifts lie in $K_J$ and the quotient coordinates sum to zero. Multiplying ordered products and moving each second factor to its own index gives
$$
t_J(r+r')=t_J(r)+t_J(r')+b_J(r,r'),\qquad
b_J(r,r')=\sum_{i>j}\beta(u_i,u'_j)\bmod K_J .
$$
The sign is immaterial since $D_J$ is killed by two. The polar is bilinear and alternating on $R_J$, as is also seen by setting $r=r'$. Thus this is precisely a square record on $R_J$ with central output $D_J$, commutator $b_J$, and basis-lift squares $t_J(r_j)$. Matching these records under the base pair says that $\sum_{i\in J}d_i(u_i)=0$ in $C'/K'_J$ for every relation in $R'_J$. Indeed replacing each section by the target section multiplies the ordered product by the corresponding central differences. A common correction implies all these equalities.

Suppose first that the $K'_i$ have a common coordinate decomposition. On a central line $L$ let $J$ be the indices for which $L$ survives in $C'/K'_i$. If $J$ is nonempty, project the equality for $R'_J$ to $L$, which survives in $C'/K'_J$. The summed $L$-valued discrepancy kills the kernel of the sum map and hence descends to $\sum_{i\in J}U'_i$. Extend it by a complementary subspace to $A'$. An empty $J$ needs no correction. Summing the component solutions gives one common correction. The records are intrinsic and use no choice of decomposition. In particular any two subspaces admit a common coordinate decomposition, by splitting their intersection, complements within each, and a complement of their sum. Every chain of subspaces also admits one by choosing successive complements.

## 3. Three arbitrary central intersections

Use in addition the linear record
$$
O=\bigcap_i U_i,\quad W=\left(\bigoplus_{i=1}^{3} C/K_i\right)/\Delta C,\qquad
\ell:O\longrightarrow W .
$$
Here $\Delta$ sends $c$ to its simultaneous images. To evaluate $\ell(u)$, choose $g$ over $u$ and $h_i\in H_i$ over the same $u$, and take the class of $(h_i g^{-1}\bmod K_i)_i$. Changing $h_i$ is killed by its own $K_i$; changing $g$ is killed by the diagonal quotient. For a pair of arguments use the products of the respective chosen lifts, so the expression adds since each difference $h_i g^{-1}$ is central. Thus $\ell$ is linear. Its preservation says $(d_i(u))_i\in\Delta C'$ for every $u\in O'$.

A triple of subspaces is a direct sum of lines with coordinate membership and planes on which the respective three subspaces are $\langle e\rangle,\langle f\rangle,\langle e+f\rangle$. To see this, split off any line $\langle v\rangle$ with $v$ outside the sum of the marked subspaces omitting it. A projection onto that line killing the sum preserves all three subspaces, as does the complementary projection. Continue until no such line remains. The residual subspaces span the ambient space, their pair intersections vanish, and each lies in the sum of the other two. A vector outside the total span, a nonzero vector in a pair intersection, or a vector of one subspace outside the sum of the other two would have allowed another line to split off. The first two residual subspaces are therefore complementary and the third is the graph of an isomorphism between them. Matched bases split this into the stated planes.

On the line components use Section 2. On a plane use coordinates in which the three discrepancies demand
$$
y|_{U'_1}=d_1,\qquad x|_{U'_2}=d_2,\qquad (x+y)|_{U'_3}=d_3.
$$
The overlap record says $d_1(u)+d_2(u)=d_3(u)$ on the triple intersection. This suffices since the sum of the three discrepancy maps on $U'_1\oplus U'_2\oplus U'_3$ kills the kernel of $(u,v,w)\mapsto(v+w,u+w)$. That kernel is the diagonal of the triple intersection. Descend to the image, extend to $A'\oplus A'$, and restrict to its two coordinates to obtain $x,y$. Taking the sum over the central components solves the one common correction system. All records are necessary by direct transport of their defining lifts, so the tests are exact.

## 4. Ordinary oracle and exact outputs

Compile the constant-size diagram of named abelian carriers, linear maps, and central presentations using the prior torsion-weighted paired markers and anchored dual frame. For every central output $Y$, bracket its own primal copy with a fixed full-order anchor onto that output. To record $m:X\to Y$, bracket $X$ with a separate fixed anchor into the same output via $m$. For a central presentation use its prescribed bracket on the named primal input block and its prescribed basis-lift powers in that output. Separate anchors distinguish the linear-map domains. Add frame anchors $u,v$ with $[u,v]=c$ and $u^2=c$ in a dedicated central line. The anchored frame fixes the anchor vectors and any required cyclic dual prefixes. This records the inclusions of $U_i,K_i$, the component maps out of $R_J$, the projections defining $D_J$, the intersection map out of $O$, and the inclusions and quotient maps defining $W$. The fixed anchors force the maps on central outputs to agree with their primal copies. The remaining diagrams use the original and ordered-product central presentations.

Each core block is recovered from the intersection of two paired-marker contraction images. In the core quotient the auxiliary coordinates have zero basis powers and their brackets disappear into the auxiliary center, so the old power records survive, as in the prior compiler. Brackets with fixed anchors then recover the named linear maps. Conversely a diagram isomorphism extends by inverse-duality on the private paired copies and identities on the fixed anchors and heavy blocks. The preserving-power criterion from the collecting presentation gives a group isomorphism. The maps on the auxiliary carriers are forced by the maps on $A,C$ because they are given by the indicated inclusions, joint projections or quotients. Feasibility of the diagram is therefore exactly feasibility of a base pair admitting an actual marked lift.

The total module length is $O_k(\log N)$ for $k$ fixed. In particular $|R_J|\le\prod_{i\in J}|U_i|$, each central quotient, intersection, and auxiliary direct sum costs a fixed sum of source lengths, and there are at most $2^k-1$ subsets. A fixed number of paired markers costs linear length, and the anchored dual prefix frame also costs linear length. Thus every explicit oracle table has polynomial order and is generated in polynomial time by the collecting formula.

For search fix images of source dual basis elements of $A,C$ one at a time in the diagram queries. These carriers have at most $N$ elements each, so testing all candidates uses polynomially many queries. On completing the pair, construct an ordinary lift and solve the correction system. Every feasible base pair has exactly $|\ker\rho|$ lifts, for $\rho(s)=(s|_{U_i}\bmod K_i)_i$, and the linear system yields this count and its kernel generators. For equal inputs, compute the orbit sizes and coset representatives in the basis-point stabilizer chain of the pair group using the same prefix tests. Their product gives the pair-group order, so multiplying by $|\ker\rho|$ gives the exact marked stabilizer order. Lifts of the representatives and the kernel generators generate the marked stabilizer. A nonempty transporter between different inputs is a coset of the source stabilizer.

This is a written reduction. The accompanying Lean file verifies the linear factorization and triangle correction used in Sections 2 and 3. The finite replay contrasts exact shift solvability with the record conditions and includes concrete group examples.

[Prior bare class-two compiler](https://github.com/Dugongue/MathProofs/blob/main/GrochowResearchSynthesis/CLASS-TWO-BLACK-BOX.md) · [Specified central-kernel compiler](https://github.com/Dugongue/MathProofs/blob/main/ClassTwoOracleApplications/CENTRAL-SHIFT-NORMALIZERS.md) · [Grochow and Qiao on group extensions](https://arxiv.org/abs/1309.1776) · [Wilkes on relative extensions](https://arxiv.org/abs/2209.06492)
