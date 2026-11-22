# Counting corrections recovers the connectivity of failed tensor tests

Fix a finite commutative local ring $R$, write $s=|R^\times|$, and choose $\{1\}\ne\Gamma\le R^\times$. On each edge of a connected simple graph $G=(V,E)$ give two 3-tensors of the same positive format over $R$. Write $G_-$ for the subgraph of nonisomorphic pairs, with all vertices retained. Let $K$ be a collection of possible pin pairs, each a distinct unordered pair of vertices. For $F\subseteq K$, set $H_F=G_-\cup F$, and let $c_F$ be its number of components.

**Theorem.** There are polynomial-time constructible finite free unital associative $R$-algebras $A_F$, all of the same rank and with center $R$, whose determinant-one multiplication-tensor stabilizer orders $N_F$ satisfy
$$
\frac{N_\varnothing}{N_F}=|\Gamma|^{c_\varnothing-c_F}.
\tag{1}
$$
When $K$ contains a spanning tree on $V$, a neutral count and a query pinning that tree recover $c_\varnothing$. If $K$ contains every pair of a set of $k$ marked vertices, $O(k\log(k+1))$ further exact counts recover their full component partition in $G_-$. The construction only reads the given tensor entries. The base-$|\Gamma|$ logarithm of the ratio is the graphic matroid rank of $F$ after contracting the components of $G_-$.

For any integers $b_v$ summing to zero there is a weighted version. Set
$$
d_F=\left|\Gamma^{\,\gcd(\exp\Gamma,\{\sum_{v\in C}b_v:C\in\pi_0(H_F)\})}\right|.
$$
Then the ratio of ordinary multiplication-tensor stabilizer orders is again the right side of (1), while the determinant-one ratio is that quantity multiplied by $d_F/d_\varnothing$.

## Construction

Start with the graph-of-sides algebra for $G$. Its scalar source and sink have between them $W=R^V$, with basis $(e_v)$. For each oriented edge $vw$ and label $a\in\Gamma$, put a middle block $M_s(P(T_{vw}))$ at $a=1$ and $M_s(P(T'_{vw}))$ elsewhere. Here $P(T)$ has three scalar diagonal corners. Its upper positions are the tensor modules, with $T$ as their only product. Outer incoming rows and outgoing columns are standard modules over the first diagonal quotient $M_s(R)$. Their product is the perfect pairing times $ae_v+e_w$. Each vertex has a pure matrix marker $M_{m_v}(R)$ whose pairing line is $Re_v$. Choose distinct widths $m_v>s$ with $m_v+1\equiv b_v\bmod s$. Set every $b_v=0$ for (1). [Original graph-of-sides construction](https://github.com/Dugongue/MathProofs/blob/main/PolyhedralTensorDeterminants/A.md)

For every pair $uv\in K$, orient it once and add a pure matrix block $M_{\ell_{uv}}(R)$ of width a positive multiple of $s$, greater than all marker widths and distinct from all other pin widths. The balanced pairing of its row and column is multiplied by $e_u$ for $uv\notin F$, and by $e_u+e_v$ for $uv\in F$. This defines $A_F$. Choosing pin widths $O_R(|V|+|K|)$ keeps the rank polynomial for fixed $R$. All $A_F$ have the same underlying free modules. The products are associative by the balanced pairings and the vanishing of threefold strictly upper outer products. Their center is $R$ because each middle block has scalar center and all standard outer arrows force the middle scalars to agree with the endpoint scalars.

The matrix widths in the semisimple quotient distinguish all pins and markers. The outer endpoints are the only width-one factors and their directed corner fixes their order. The induced Peirce support among width-$s$ vertices recovers the data blocks. Its components each have two nonzero adjacent upper spaces, which determine the order of the three internal vertices. After aligning the diagonal vertex idempotents, the axis markers force diagonal action on $W$, say with scales $x_v$. Labelled edge lines require $x_v/x_w\in\Gamma$, and the unique exceptional label of a failed edge forces $x_v=x_w$. For a map between aligned data blocks, inner conjugations first remove its actions on the three diagonal matrix algebras. The matrix-unit argument below then recovers the underlying tensor isomorphism on the original spaces. Inactive pins add no constraints. Active pins force precisely $x_u=x_v$. Conversely, every such scale assignment is attained. Translate the labels of each edge via its ratio and use the tensor isomorphism to identify payloads whenever the ratio is nonidentity. Scale its row by $x_w$, and each pin row by $x_u$. Connectedness of $G$ gives $s|\Gamma|^{c_F-1}$ such assignments. The value at one root vertex can be arbitrary, and the $\Gamma$-phases relative to that root can be chosen independently on all other components of $H_F$.

Each pin's inner diagonal automorphism has determinant 1, and its two arrow determinants multiply to $x_u^{\ell_{uv}}=1$ by the perfect pairing. Each data arrow pair contributes $x_w^s=1$. Around each permutation cycle the product of determinants of data-block maps is the determinant of an amplified payload automorphism. Its entrywise part repeats on $s^2$ entries and its inner part repeats on $s$ rows or columns, so this determinant is 1. Data-block and arrow permutation signs vanish because their ranks are even when $s$ is even, while $-1=1$ when $s$ is odd. The marker row and column at $v$ contribute $x_v^{m_v}$, and $W$ contributes $\prod_v x_v$. The total determinant is $\prod_v x_v^{b_v}$. The common root scale cancels, leaving each component phase raised to its mass $\sum_{v\in C}b_v$. The Bezout identity then gives the determinant image size $d_F$.

## Counting the fibers

Let $J^\uparrow$ be the ideal of all strictly upper positions in the refined triangular presentation. Its size is determined by the shared ranks. For a fixed permutation $\pi$ of refined diagonal vertices that occurs, every transported idempotent $f_i$ has diagonal projection precisely that of its target $e_{\pi(i)}$. In each matrix diagonal factor an idempotent congruent to 0 or 1 modulo the maximal ideal equals 0 or 1. The unit $\sum_i f_i e_{\pi(i)}$ in $1+J^\uparrow$ conjugates all target idempotents to their transported idempotents. It is unique, since the only element of $1+J^\uparrow$ commuting with all diagonal vertex idempotents is 1. Therefore each aligned automorphism yields exactly $|J^\uparrow|$ automorphisms before alignment. These conjugations have determinant 1 by upper triangularity with identity diagonals.

Fix an admissible scale assignment. It prescribes every block destination, including the label translation $a\mapsto (x_v/x_w)a$. An aligned map of a middle block fixes or matches the corresponding internal vertex idempotents. The choices form a torsor for the aligned automorphism group of the source middle block. For a data block based on $T$ the number of choices is $p_s^3\alpha(T)$, where
$$
p_d=\frac{|\mathrm{GL}_d(R)|}{s},\qquad
\alpha(T)=|\operatorname{Stab}_{\mathrm{GL}\times\mathrm{GL}\times\mathrm{GL}}(T)|.
$$
Indeed, each of the three diagonal matrix factors has $p_s$ automorphisms, all inner. Any three conjugating matrices extend by a block diagonal inner automorphism. After removing it, the upper maps fix the matrix-unit actions. Each is consequently entrywise on its underlying tensor module, and preserving their product is exactly the condition defining $\alpha(T)$. A pure matrix block of width $d$ has $p_d$ maps. To obtain innerness over $R$, take a column in the image of the transported $E_{11}$ nonzero modulo the maximal ideal. Its translates under the transported $E_{i1}$ form a basis modulo the maximal ideal and hence over $R$. Conjugating matrices are unique up to one central unit.

For each middle-block map, the induced matrix action on the quotient through which its arrows act is conjugation by $S$. The compatible semilinear row and column maps have forms $r\mapsto t rS^{-1}$ and $c\mapsto u S c$. This follows by untwisting by $S$, since an endomorphism of either standard full-matrix module commuting with the matrix units is scalar. If the required pairing multiplier is $\lambda$, then $tu=\lambda$, leaving exactly $s$ choices independently at each middle block. There are no other choices, because every refined Peirce space has its prescribed destination and the endpoints and the map on $W$ are fixed.

Writing $h$ for the number of middle blocks gives the exact count
$$
|\operatorname{Aut}_R(A_F)|
=
|J^\uparrow|\,s^{h+1}|\Gamma|^{c_F-1}
\prod_{\text{data blocks }j}p_s^3\alpha(T_j)
\prod_{\text{pure blocks }j}p_{d_j}.
\tag{2}
$$
All factors except the component count are unchanged by pin activation.

## Counting tensor corrections

For an algebra $A$ with multiplication tensor $\mu_A$, ordinary autotopisms have unique parameters $(a,b,\sigma)\in A^\times\times A^\times\times\operatorname{Aut}_R(A)$, with maps $(L_a\sigma,R_b\sigma,L_aR_b\sigma)$. Indeed, the isotopy equations at the unit give $a=X(1)$, $b=Y(1)$, and invertibility of the corresponding multiplication maps, hence of $a,b$. Removing those maps gives the algebra automorphism $\sigma$. The determinant-one conditions require precisely $\det\sigma=\det L_a=\det R_b=1$, since $\det\sigma=(\det X)(\det Y)/\det Z$.

Both unit determinant maps for $A_F$ are onto $R^\times$. Left multiplication by a unit supported on the diagonal changes only the sink's one-dimensional block when its sole nonidentity entry is at the sink. The source gives the right analogue. Also, all $A_F$ have the same unit count $|J^\uparrow|\prod_i|\mathrm{GL}_{d_i}(R)|$, with the product now over refined diagonal factors, since the diagonal projection has nilpotent kernel $J^\uparrow$. The ordinary tensor stabilizer count is $|A_F^\times|^2$ times (2), and the determinant-one count is
$$
N_F=\left(\frac{|A_F^\times|}{s}\right)^2\frac{|\operatorname{Aut}_R(A_F)|}{d_F}.
\tag{3}
$$
This proves both ratios. For a supplied ordinary basis change of determinant $\delta^{-1}$ fixing the unit, its determinant-one transporter count equals $N_F$ if $\delta$ belongs to the algebra determinant image, and is zero otherwise. This uses that a nonempty transporter set is a coset of the stabilizer.

## Recovering a partition and counting raw transporters

If $K$ contains a spanning tree on $V$, pinning the tree gives $c_F=1$. To recover the partition on a marked vertex set, maintain one representative from each class encountered so far. For the next vertex $v$ and a nonempty subset $S$ of representatives, pin the star $\{vs:s\in S\}$. The component-count drop is $|S|-1$ if $v$ belongs to a represented component in $S$, and $|S|$ otherwise. Thus a test on all representatives and binary search identify the class or start a new one in $O(\log(k+1))$ queries per vertex. The same neutral reference is used each time.

Equations (2)–(3) also give a three-query nonadaptive polynomial-time reduction from counting arbitrary raw 3-tensor transporters to counting determinant-one stabilizers of unital associative multiplication tensors with center $R$. For a raw pair $T,T'$, use a one-edge graph and its one potential pin, with all weights zero. Two counts determine whether $T\cong T'$, since their ratio is $|\Gamma|$ for yes and 1 for no. A third count uses an unpinned one-edge graph with the same $T$ on both sides. Every data block then uses $T$, and the only unknown in (2)–(3) is $\alpha(T)^{|\Gamma|}$. Divide by the known factors and take the exact integer root. The known factors include $|\mathrm{GL}_d(R)|=|\mathfrak m|^{d^2}\prod_{i=0}^{d-1}(|k|^d-|k|^i)$, where $k=R/\mathfrak m$. Return $\alpha(T)$ if the two tensors are isomorphic and zero otherwise. All integer bit lengths are polynomial.

Grochow and Qiao developed counting-to-decision reductions for alternating matrix space isometry and certain $p$-groups. This result uses dimension-matched stabilizer counts to recover a graph partition and reduces raw transporter counting to determinant-one counting. The algebra construction and count theorem have written proofs. Lean verifies the normalized component-scale count and the two-arrow scalar fiber count. Finite controls check 359,424 coordinate counts, 5,616 partition decodings, and all 24 conjugation actions of $\mathrm{PGL}_2(\mathbb F_3)$ at both perfect-pairing multipliers. [Lean components](A.lean) · [Grochow–Qiao, CCC 2021](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2021.16) · [Grochow–Qiao on tensor-to-algebra encodings](https://arxiv.org/abs/1907.00309) · [Finite control](ACheck.py)
