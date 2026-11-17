# A single orientation query when one tested mode is small

Work over $F=\mathbb F_3$, with ordinary 3-tensor transporters on explicit rectangular arrays. Suppose the query requires determinant one in two prescribed modes, and one of these modes has dimension $k$. There is an exact deterministic many-one map to **one** ordinary tensor pair with a determinant-one test on one mode. Its time and dense output size are polynomial in the input length and in $2^k$. In particular it is polynomial for each fixed $k\le c\log N$, where $N$ is dense input length. The second tested dimension and the untested dimension may both grow arbitrarily. No ordinary or oriented decision oracle is used to construct the output.

The construction uses the same two regular blocks and rectangular quotient readout as the earlier cubic norm and sign encodings. The new step puts one determinant condition into the multiplication table itself by identifying an exterior top wedge with an even power of a tag. The remaining determinant is measured by the one-sign query.

## 1. Reduction to concise even tested spaces

Use the bilinear formulation $\mu:U\times V\to W$, with both input determinants tested and $k=\dim U$. Mode permutation and dualization allow this choice, since determinants equal their inverses over $F$. Compare intrinsic supports, rejecting a mismatch. A deficient tested mode contributes an independent determinant correction, since its support has a nonzero unused complement; it can be dropped from the test. If a tested dimension is odd, a scalar stabilizer with scalar $-1$ on that mode and on the untested mode corrects its sign while fixing the other tested sign. Thus any such case is ordinary TI or one-sign TI, and can already be placed in one one-sign instance by assigning the orientation to the remaining mode or adding an unused direction to an ordinary instance. The zero cases are immediate.

Hence suppose both tested modes are concise, both dimensions are even, and $k\ge2$. Compact $W$ to the image because its determinant is untested. Now $\mu$ is concise in all three modes, including having no common kernel in either input and having output values spanning $W$.

## 2. Two local algebras with different tasks

Let $\omega=u_1\wedge\cdots\wedge u_k$ in the oriented coordinate basis. Form a unital algebra $C_U$ from the exterior algebra $\bigwedge U$ and a truncated string $F[z]/(z^{k+1})$ with common unit, all mixed radical products zero, and their two top elements identified by $z^k=\omega$. More precisely, start with the fiber product over the common scalar residue and quotient by the span of $z^k-\omega$; this span is an ideal because both top elements annihilate the entire radical. The algebra has a degree filtration, with $z$ of degree one. Its dimension is $2^k+k-1$, with a basis of exterior monomials and $z,\ldots,z^{k-1}$.

Let $J_U$ be its radical. The square-zero tangent vectors in $J_U/J_U^2$, tested in degree two, are exactly $U$: the square of $u+a z$ is $a^2z^2$, since the exterior square of a degree-one element is zero and mixed products vanish. Here $z^2\ne0$ even when $k=2$. The tangent common annihilator of $U$ in degree two is exactly the line $Fz$, since a nonzero $u$ has nonzero wedge product with some other tangent in $U$. These tests recover both subspaces intrinsically. Any algebra isomorphism between the coordinate copies of $C_U$ therefore induces a map $g_U$ on $U$ and scales $z$ on the tangent line by some $\lambda\in F^\times$. Applying the isomorphism in degree $k$ to $z^k=\omega$ gives
$$
                   \det g_U=\lambda^k=1 .
$$
This makes the first input orientation an ordinary algebra constraint. Conversely any determinant-one $g_U$ extends by exterior powers and fixes the tag $z$.

Let $C_V=F\,1\oplus V\oplus\langle t,t^2,t^3\rangle$ where $t^4=0$, products inside $V$ vanish and $V$ annihilates the tag. The square-zero tangent subspace is $V$, recovered by the same square test. On the quotient tag line the action is a scalar $\beta$. The two higher tag powers then have leading scales $\beta^2,\beta^3$, so the determinant on $C_V$ of any algebra isomorphism is precisely $\det g_V$, since $\beta^{1+2+3}=1$. Its dimension $\dim V+4$ is even. All maps $g_V$ on $V$ extend while fixing the tag.

Both algebras are local, with scalar residue and nilpotent radical. The arguments about terms and degrees take place in the radical filtration and allow arbitrary shears of higher degree.

## 3. Recover and retain the original tensor

Write $J_V$ for the positive ideal of $C_V$. Put the two local algebras into one local algebra $B_\mu$ with common unit and radical
$$
                 J_U\oplus J_V\oplus W\oplus R.
$$
Here $R$ is zero when $\dim W$ is even, and otherwise is an independent, commuting truncated string with basis $r,r^2,r^3$ and $r^4=0$. The only mixed product is $U\cdot V\to W$ given by $\mu$ on the degree-one subspaces. Higher degrees and both tag lines are ignored in this mixed product; $W$ annihilates the radical. Associativity follows because a mixed radical product lands in $W$ and vanishes upon further radical multiplication. In a triple having two factors in a single branch and a third in another branch, their product within that branch is of higher degree and so also gives zero if followed by a mixed product. The algebra is local, and its dimension is
$$
 \dim C_U+\dim C_V-1+\dim W+\dim R,
$$
which is even.

Mark the ideals
$$
   I_U=J_V\oplus W\oplus R,\qquad I_V=J_U\oplus W\oplus R .
$$
The corresponding quotients are $C_U,C_V$. The linear span $[I_U,I_V]$ of commutators is exactly $W$, using conciseness and the fact that $R$ is commuting. Thus an algebra isomorphism preserving these two marked ideals induces $g_U,g_V,g_W$ on the original tensor slots, with
$$
            \mu'(g_U u,g_V v)=g_W\mu(u,v).
$$
One can see this directly on commutators: the image of $u$ lies in $I_V'$, the image of $v$ lies in $I_U'$, and the mixed commutator reads only their recovered tangents. The first determinant is one by the exterior lock. Conversely every transporter of $\mu,\mu'$ with $\det g_U=1$ extends to an isomorphism of the local algebras preserving both ideals by exterior powers, the original $V,W$ actions and identity on the tag strings.

## 4. Read the second sign in one matrix mode

For either marked quotient $C=B_\mu/I$, let $\epsilon$ be its scalar residue and $e\in J_C^2$ be the corresponding nonzero tag square $z^2$ or $t^2$. The quotient-dependent pencil block is
$$
       K_C(a):F^2\longrightarrow C,\qquad
       K_C(a)=[\,\bar a,\ \epsilon(a)e\,].
$$
Use the pencil indexed by $B_\mu$ having two regular left-multiplication blocks $L_a$, one $K_{C_V}$ block and the transpose of one $K_{C_U}$ block. Use only the full **row** mode for the determinant-one test. The pencil is concise, since the regular representation is faithful and each block has joint kernel zero and full image span.

Here are the facts ensuring the block readout is exact. For fixed labels the regular block has local endomorphism ring given by right multiplications of $B_\mu$, hence is indecomposable as a two-vertex representation. For a rectangular block, write its input endomorphism as $\begin{pmatrix}p&q\\r&b\end{pmatrix}$. The second-column equation on the radical gives $q=0$. The first-column equation makes the output endomorphism $pI+r e\epsilon$, while the second-column equation at $1$ gives $b=p$. Thus it is indecomposable with local endomorphism ring, and the determinant of any fixed-label automorphism on its two-dimensional column space is $p^2=1$. Its row sign is neutral when $\dim C$ is even, as it is for $C_V$. The three block types have distinguishable ordered dimension pairs; the two regular copies are the only deliberate repeat. Thus by Krull–Schmidt every pencil transporter with a given linear label map $s$ admits a block-diagonal representative. All others for that label differ by a fixed-label unit. In the endomorphism ring of the direct sum, the semisimple quotient is a two-by-two matrix block for the repeated regular factor and scalar factors for the two nonisomorphic rectangular blocks. Radical parts are nilpotent and do not affect determinants of units. On two regular copies the matrix-block contribution is the determinant of its scalar two-by-two action raised to the even dimension of $B_\mu$. Consequently all fixed-label units act with determinant one in the tested row mode.

The ordinary transport equation on the faithful regular blocks gives $s(a)=u\phi(a)$, with $u$ a unit and $\phi$ an algebra isomorphism. Indeed the value at $1$ sets $L_u=hg^{-1}$ and the other values give $gL_ag^{-1}=L_{u^{-1}s(a)}$. The regular term contributes determinant one in the tested mode: its componentwise algebra isomorphism is doubled, its left unit has determinant $\epsilon(u)^{\dim B_\mu}=1$, and the module-unit factor is neutral as above. The kernel of a rectangular pencil in its label variable is exactly the marked ideal. Since the label map carries both kernels to their targets, and $u$ is a unit, $\phi$ preserves the two ideal marks.

For a rectangular comparison, write $s_C=u_C\phi_C$ and $P=\begin{pmatrix}p&q\\r&b\end{pmatrix}$ for its column map. In $H K_C(a)=K_{C'}(s(a))P$, the second-column equation on the radical gives $q=0$, and the first column gives
$$
                  H=p\,s_C+r\epsilon(u)e'\epsilon.
$$
On the tag square, the induced leading scale of $\phi_C$ is $\lambda^2$, the square of the leading tag scale (use $\beta$ in $C_V$); this follows even if the corresponding tag generator has a higher-degree shear. Evaluating the second column at $1$ and reading degree two gives $b=p\lambda^2$. Thus the column determinant is one for either quotient, independently of the quotient dimension. For $C_V$, whose dimension is even, the row determinant is exactly $\det\phi_{C_V}=\det g_V$. In fact $p\,s_C$ has that determinant because $p^{\dim C_V}$ and the left-unit determinant are both one, and its rank-one perturbation adds determinant factor one, since $s_C^{-1}e'$ has zero residue.

In the full pencil the $C_U$ block is transposed, so its contribution to the tested row mode is the neutral column determinant. The total row determinant is precisely $\det g_V$. Conversely the extensions constructed from original tensor witnesses fix the two tag squares and extend to all rectangular blocks with identity on their two-dimensional column spaces. The construction is therefore sound and complete.

The tables above have dimension polynomial in the raw tensor length and in $2^k$, and their entries are obtained by exterior monomial multiplication, bounded string multiplication and the raw coefficients of $\mu$. The only exponentially sized component in this proof is polynomially bounded when the protected dimension is logarithmic. The proof is informal and gives a sufficient single-instance condition for the two-sign question.

## One small factor in a conjunction

The exterior lock also gives a polynomial-time map from a **one-sign** instance with $k=O(\log N)$ in its tested mode to one **ordinary** TI instance. Compact the untested modes and use exactly the same tagged pencil, asking only for ordinary equivalence of its output. The regular and rectangular comparison still marks both ideals and reflects the original transporter, with $\det g_U=1$ by the exterior relation. Conversely the extension still works. The evenness of the untested dimension and the determinant calculation on the row mode are unnecessary for this ordinary comparison. This gives a reduction of a conjunction of two one-sign instances to one one-sign instance whenever at least one instance has a logarithmic tested dimension, by combining this ordinary query and the remaining oriented query using the determinant-neutral independent composition.

## A separate three-query comparison with full SL

Let $D\subseteq\mathbb F_2^3$ be the sign set of an ordinary transporter between any given tensors. It is empty or an affine subspace. Choose independent $u,v$. Then $0\in D$ holds exactly when $D$ meets all three lines $\langle u\rangle,\langle v\rangle,\langle u+v\rangle$. Indeed, if $0\notin D$ and all three meets succeed, $D$ contains the three nonzero representatives $u,v,u+v$. Their sum is zero and is an affine combination over $\mathbb F_2$, because there are three summands. Each of the three probes is in the two-sign tier. The conjunction can be produced nonadaptively and improves the comparison of unrestricted SL with three two-sign queries. The logarithmic protected-dimension theorem above is a one-instance reduction on its stated domain.
