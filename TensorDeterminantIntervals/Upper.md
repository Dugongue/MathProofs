# Determinant correction by operator spaces

Work over the fixed field F₃, with explicit three-tensor pairs and three independently acting mode maps. Write $B$ for two-sign TI and $S$ for special-linear TI. All forward reductions here are deterministic polynomial-time many-one reductions. This proof is informal.

For an ordinary comparison $X=(T,T')$, the attainable signs form a subset $D(X)$ of $V=\mathbb F_2^3$. On an ordinarily positive comparison, $D(X)=a+H$, where $H$ is the image of the source stabilizer under the determinant bits. On an ordinarily negative comparison $D(X)$ is empty.

## A family of explicit intermediate problems

Fix any linear subspace $\mathcal P$ of $\operatorname{End}(V)$ containing the identity. In the **operator-space correction problem** $C_{\mathcal P}$, the input is one raw tensor pair. It accepts exactly when some relative witness has sign vector corrected to zero by a sum of $\mathcal P$-reshaped determinant signs of source automorphisms. Equivalently, reject empty $D$ and otherwise accept just when

$$
 a\in\mathcal P H,\qquad
 \mathcal P H=\sum_{L\in\mathcal P} L(H).
$$

It suffices to use one independent source automorphism per matrix in a basis of $\mathcal P$ extending $I$. The complete compiled profile is $D+\sum_{L\in\mathrm{basis}\setminus\{I\}}L(H)$. Apply the earlier informal exact sign projection to the relative and self-comparisons, then use ordered format tags and the direct sum to realize their Minkowski sum as one raw pair. Thus $C_{\mathcal P}\le_m^p S$. This reuses an explicit construction on raw tensors and requires no sign oracle. [Prior exact sign projection and sum construction](SignProjection.md)

A lower bound $B\le_m^p C_{\mathcal P}$ holds when there exists a plane $U\le V$ with

$$
 \mathcal P v\cap U=\langle v\rangle\qquad(0\ne v\in U).
 \tag{1}
$$

Encode the two tested bits of the given $B$ pair in this plane with an exact sign map. For $H=0$ or $H=U$, the equality $\mathcal P H\cap U=H$ follows from the identity, and for line $H$ it follows from (1). Thus correction cannot change the $B$ answer. It preserves empty profiles as well.

One especially simple case fixes a vector $u\ne0$ and a subspace $W\le V^*$. Put $\mathcal P=\langle I\rangle+\{u f:f\in W\}$. The comparison permits one extra correction in $\langle u\rangle$ if some source sign is detected by some $f\in W$. Every complementary plane to $\langle u\rangle$ satisfies (1). With $u=e_3$, the choices $W=V^*$, $W=\langle e_1^*,e_3^*\rangle$, and $W=\langle e_1^*\rangle$ give three different problems on a chain beneath $S$. The last choice is the previously studied cross-mode stabilizer correction. To reduce from larger to smaller $W$, preprocess by explicitly applying the larger correction to the input profile. Its direction is closed under the smaller correction, because all additional images lie on the one line, which is either already present or never inserted. If $W=\langle e_3^*\rangle$, the test equals the shared-pair conjunction of a $B$ test on the first two bits and an $A$ test on the third. This follows by splitting into whether $e_3^*(H)=0$ or $e_3^*(H)=\mathbb F_2$.

The projector comparison also has exactly the degree of the prior independent conjunction of B and A. One direction uses those two tests on the same raw pair. For the other, project the independent B profile into the kernel plane of the projector and the independent A profile into its image line, and pack their direct sum. Their combined direction is already invariant under the projector. Thus the two tests hold exactly when the packed correction test accepts. This identifies row 2 below with a previous catalogue degree. Row 3 is the previously studied cross-mode correction.

Row 6 is the full diagonal matrix space. It has exactly the prior degree of three independent A questions joined by conjunction. For an arbitrary correction input, membership asks separately whether each coordinate of its sign profile admits zero. Conversely, pack independent A profiles into the three coordinate axes. Their combined direction is already stable under all diagonal operators, so correction preserves the three verdicts.

## Exact comparisons within affine preprocessing

An affine preprocessing transforms $a+H$ to $M a+b+E+\sum_i L_i H$, by independent copies of the relative profile and its direction with fixed linear maps, fixed shifts and fixed slack. Its direction includes $M H$, since the maps on relative copies sum to $M$. These transformations are available from the sign compiler when all matrices are fixed. A copy of $D$ can always be used with the zero map to implement rejection for an empty input.

A single such transformation gives an exact reduction $C_{\mathcal P}$ to $C_{\mathcal Q}$ on all affine profiles if and only if for some invertible $M$ the space

$$
 \mathcal L_M=\{L : \mathcal Q L v\subseteq M\mathcal P v
                     \text{ for every }v\in V\}
$$

has $M\in\mathcal L_M$ and satisfies $\mathcal Q\mathcal L_M v=M\mathcal P v$ for every $v$. For necessity, at $H=0$ only $a=0$ may be accepted, so $M$ is injective, the slack is zero, and $b=0$. At arbitrary $H$ exactness requires precisely the direction $M\mathcal P H$ after correction. This forces every individual $L_i$ into $\mathcal L_M$, by taking $H$ to be a line. It also forces $M\in\mathcal L_M$. Enlarging to $\mathcal L_M$ therefore attains all of $M\mathcal P v$ without growing beyond it. For sufficiency, use one transformed copy $MD$ and self copies with the basis matrices of $\mathcal L_M$. Corrected directions on all subspaces follow by summing the identities on lines.

Any such reduction has a simple necessary inequality of line profiles. In the source coordinates, every subspace $M^{-1}\mathcal Q M v$ is contained in $\mathcal P v$. Thus the score $\sum_{0\ne v\in V}|\mathcal P v|$ of the source is at least the score of the target. If scores are equal, containment is equality at every vector and the two line profiles differ only by coordinates. This argument also holds when allowing a finite disjunction of affine targets: at least one branch accepts the singleton $\{0\}$ and that same branch must reject each of the other singleton offsets. Its offset map is again invertible, and the same containment applies as its acceptance cannot exceed that of the source. The argument rules out a direct single-$B$ target, even with such a disjunction, since the accepting branch at $H=0,a=0$ would have to inject three bits into the two tested bits. Every affine set used here is realizable as an actual sign profile, by starting with a zero-tensor pair, projecting its full sign space to $H$, and reflecting target axes to set the offset. These limitations concern the specified preprocessing model and leave unrestricted many-one comparisons open.

## A seven-node chain in the upper interval

Encode the vectors of $V$ by the integers $0,\ldots,7$ in binary coordinates, with basis $1,2,4$. Encode a matrix with columns $c_1,c_2,c_3$ by $c_1+8c_2+64c_3$, so $I=273$. A row labelled $C(g_1,\ldots,g_s)$ means the correction by the linear span of the displayed matrices.

$$
\begin{aligned}
B\ &\le_m^p C(273,8,35,129)
 \le_m^p C(273,25,75)
 \le_m^p C(273,1,88)\\
 &\le_m^p C(273,1,16)
 \le_m^p C(273,17)
 \le_m^p S .
\end{aligned}
$$

For the leftmost edge from B use the witnessing plane with coded elements 0, 1, 4 and 5. The five successive edges whose source is a correction problem have the following certificates. Encode $S$ as $C(273)$. Each row preprocesses $D=a+H$ to $M D+\sum_{L\in E}M L(H)$. These are fixed sign projection and sum operations on raw pairs.

| Source | Target | $M$ | $E$ |
| --- | --- | ---: | --- |
| $C(273,8,35,129)$ | $C(273,25,75)$ | 140 | 8, 16, 32 |
| $C(273,25,75)$ | $C(273,1,88)$ | 428 | 1, 2, 24 |
| $C(273,1,88)$ | $C(273,1,16)$ | 84 | 1, 16, 72 |
| $C(273,1,16)$ | $C(273,17)$ | 84 | 1, 16 |
| $C(273,17)$ | $C(273)$ | 84 | 17 |

To check each row, for each of the seven nonzero $v$, span the values $QMLv$ with $Q$ from a basis of the target space and $L$ from $\{I\}\cup E$. The result equals $M\mathcal P v$ for that source. The scores of the six correction problems in displayed order are $44,36,30,26,20,14$. Consequently all six forward comparisons from $B$ onward lack a reverse reduction in the affine model. The unqualified forward reductions are polynomial many-one reductions.

## Catalogue and finite verification

The following 44 problems are the coordinate classes of all $\mathcal P$ passing (1) for some $U$. Row 1 is $S$, leaving 43 candidate intermediate formulations. Rows 43, 30, 14, 6, 2, and 1 give the chain above. Distinct rows are inequivalent even after finite disjunctions in the affine model by the equal-score necessity proved above. The numbers do not count strict unrestricted degrees.

| Row | Generator codes besides $I=273$ | Score |
| ---: | --- | ---: |
| 1 | none | 14 |
| 2 | 17 | 20 |
| 3 | 64 | 22 |
| 4 | 80 | 24 |
| 5 | 1, 64 | 24 |
| 6 | 1, 16 | 26 |
| 7 | 17, 72 | 26 |
| 8 | 8, 64 | 26 |
| 9 | 136 | 26 |
| 10 | 176 | 26 |
| 11 | 1, 80 | 28 |
| 12 | 3, 89 | 28 |
| 13 | 17, 64 | 30 |
| 14 | 1, 88 | 30 |
| 15 | 24, 129 | 30 |
| 16 | 48, 128 | 30 |
| 17 | 33, 128 | 30 |
| 18 | 16, 192 | 32 |
| 19 | 8, 66 | 32 |
| 20 | 11, 81 | 32 |
| 21 | 8, 82 | 32 |
| 22 | 25, 74 | 32 |
| 23 | 51, 67 | 32 |
| 24 | 18, 225 | 32 |
| 25 | 8, 129 | 34 |
| 26 | 8, 128 | 34 |
| 27 | 25, 128 | 34 |
| 28 | 33, 145 | 34 |
| 29 | 33, 209 | 34 |
| 30 | 25, 75 | 36 |
| 31 | 11, 64 | 36 |
| 32 | 33, 67 | 36 |
| 33 | 34, 64 | 36 |
| 34 | 19, 224 | 36 |
| 35 | 17, 64, 128 | 38 |
| 36 | 17, 225 | 38 |
| 37 | 112, 176 | 38 |
| 38 | 97, 129 | 38 |
| 39 | 19, 227 | 40 |
| 40 | 34, 193 | 40 |
| 41 | 98, 129 | 40 |
| 42 | 64, 176 | 42 |
| 43 | 8, 35, 129 | 44 |
| 44 | 2, 32, 152 | 44 |

For completeness the enumeration has only $3^3$ starting cases. By a coordinate change place the witnessing plane at $\{0,1,2,3\}$. For each $v\in\{1,2,3\}$, the image space $\mathcal P v$ is the line through $v$ or one of the two planes intersecting the witnessing plane in that line. For each choice of three image spaces, list the matrices taking each $v$ into its prescribed space. Enumerate their linear subspaces containing $I$, beginning with $\{0,I\}$ and repeatedly adjoining one matrix and taking its span until saturation. This exhausts the choices under (1). The count is 2268 matrix spaces when the witnessing plane is fixed, 803 distinct line profiles, and 44 profile orbits under the 168 coordinate changes. A line profile is the tuple of subspaces $(\mathcal P v)_{v=1}^7$. Conjugation by $G$ acts by replacing $\mathcal P v$ with $G\mathcal P(G^{-1}v)$. The representatives above sort by score and then lexicographically by tuple of bit masks of the seven subspaces.

Applying the exact criterion for a single affine transformation gives 193 strict ordered comparisons among the 44 types. To compute this, for each ordered source and target profile try all conjugates of the target, set $M=I$ in those coordinates, and enumerate the 512 choices of $L$ to build $\mathcal L_I$. Check all seven lines as in the criterion. On the strict directed comparison graph, score decreases along every arrow. In increasing score order, assign each vertex one plus the maximum length among its outgoing strict targets, using zero for the empty maximum. The greatest length is six among correction problems, or seven when including $B$. This maximum is scoped to the 44 predicates and single affine transformations. No unrestricted separation or publication priority is claimed.






## Exactly three affine queries for the three selected new rungs

For the three new rows 43, 30 and 14, respectively, use the following triples of matrix codes to preprocess the input profile by D ↦ MD. Accept if all three queries accept.

| Correction row | Three matrices |
| --- | --- |
| 43 | 324, 44, 364 |
| 30 | 388, 52, 436 |
| 14 | 266, 309, 427 |

This recovers the full SL-TI verdict. Every profile containing zero passes all three. The [verification script](verify_upper.py) checks each of the 35 nonempty affine profiles omitting zero and confirms each is excluded by at least one matrix. The empty profile fails each query. It also checks every pair of linear maps V→V and finds a negative profile accepted by both. Two fixed affine-copy probes cannot improve that result: any probe valid as a conjunct must accept the singleton zero. If it uses offset b and fixed slack E, this implies b∈P E. Its direction always contains MH, where M is the map it applies to the relative offset. Replacing the probe by the unshifted linear query MD preserves all positives and can only remove accepts, since Ma∈P MH implies Ma+b∈P(MH+E). Extra stabilizer copies only enlarge that set. Thus three is exact for conjunctions of fixed affine-copy probes. In particular, for any one of these three rungs, a binary conjunction compiler for that rung would suffice to obtain the full unrestricted SL-TI degree.
