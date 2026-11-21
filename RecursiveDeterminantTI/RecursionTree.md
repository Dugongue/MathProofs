# Determinant comparison through an independent rooted hierarchy

This appendix gives a polynomial-size compilation for a rooted hierarchy of independent pieces, with no bound on depth or branching. The tensor field stays $\mathbb F_3$. An ordinary switch system modulo a polynomial-size prime supplies the unmarked subtree comparisons. A second switch system over $\mathbb F_2$ computes the exact determinant sign using those comparisons. No signed compiled tensor is recursively fed into an ancestor's signed construction.

## 1. Independence and the determinant convention

An input is a finite rooted tree with a based local object at each node. A local object has ordinary and prescribed-sign comparison compilers to ordinary TI over $\mathbb F_3$. Its sign is a multiplicative character on local transporters, such as the determinant of a specified based space. Each local object also has a nonnegative integer weight, invariant under ordinary local isomorphism. Only its parity will be used. A typical weight is the dimension of the based space contributing to the determinant. Put $w_v$ equal to the sum of the local weights in the subtree of $v$.

The independence hypothesis is exact. At a pair of nodes, an unmarked subtree transporter is a local transporter and any bijection of their children equipped with a subtree transporter on each matched pair. Every such choice is admitted, with no extra agreement between the local or descendant maps. A child swap of two ordinarily isomorphic subtrees can therefore use an isomorphism and its inverse, independently of the rest of the tree. If the hierarchy comes from an underlying raw tensor rather than an explicitly typed input, both the recognition of this hierarchy and the lift and reflection of its transporters are separate requirements.

Fix any order on the children at each node, for the sign convention. A subtree's sign is its local sign times all child signs times the permutation sign on the odd-weight children. This is the determinant convention for concatenating the local block and the child blocks in the chosen order. Exchanging blocks of weights $r,s$ contributes $(-1)^{rs}$. The exact determinant in other raw bases can use the corresponding computable ratio of frame determinants. These signs form a multiplicative character on the full hierarchy groupoid.

**Theorem.** Under these hypotheses, an ordinary or a prescribed-sign comparison of the full hierarchies reduces in deterministic polynomial time to one ordinary TI instance over $\mathbb F_3$, for arbitrary depth and branching. The reduction uses the local comparison compilers and positive linear switches, without recovering answers to the local queries.

## 2. Ordinary subtree comparison without solving the children first

For two candidate subtrees, take a prime $p$ greater than their total number of nodes and at most twice that number, allowing a fixed small prime for the degenerate small cases. Bertrand's postulate supplies one and trial division finds it in polynomial time. View its residue field as the coefficient field of a linear switch system, not the tensor field. For each pair $v,z$ at equal relative depth make a scalar $x_{vz}\in\mathbb F_p$, enabled by their ordinary local comparison. The root pair has $x=1$. For each parent pair $v,z$, impose
\[
 \sum_{j\text{ child of }z}x_{ij}=x_{vz}
   \quad(i\text{ child of }v),\qquad
 \sum_{i\text{ child of }v}x_{ij}=x_{vz}
   \quad(j\text{ child of }z).
 \tag{1}
\]
Each nonroot pair has just one parent pair. Enabled means that $x$ is forced to zero if the local ordinary comparison is NO.

Every genuine matching gives a solution by selecting its matched pairs with value one and assigning zero elsewhere. Conversely every nonzero active pair is an ordinary subtree match. Prove this from the leaves upward. The nonzero pair is locally compatible. Every child-pair coefficient that is nonzero joins two ordinarily isomorphic child subtrees by induction. Fix any isomorphism type among their children. Sum the row equations of that type and the column equations of the same type. Both sums on the left are equal, since all nonzero coefficients from that type stay in that type. Thus
\[
 (n_{\rm source}-n_{\rm target})x_{vz}=0\quad\text{in }\mathbb F_p .
\]
As $x_{vz}\ne0$ and the two counts are less than $p$, the counts are equal as integers. This also excludes unmatched nonempty child lists against an empty list. A literal matching of children now exists and lifts by independence. The root activation proves ordinary subtree equivalence.

The linear-switch theorem compiles (1) into one ordinary TI comparison over $\mathbb F_3$ in time polynomial in the input and the explicit modulus $p$. Thus all ordinary subtree-pair comparisons used below are produced by separate flat polynomial-size constructions. In particular they do not require any signed subtree comparisons.

There is also a direct fixed-signature representation when the local objects are supplied by a fixed signature of tensor systems. Attach the coordinate algebra $\mathbb F_3^{V}$ of the subtree nodes, with its product, root marker and the linear map sending each nonroot idempotent to its parent's idempotent and the root to zero. For each local role take its external direct sum over all nodes and use the projection action of this coordinate algebra. Use blockwise sums of the local tensor records. Individual vector marks of a given type can be stored by a single linear map from the node coordinate algebra to that role. The coordinate algebra map is a rooted tree permutation, and these projection and blockwise records force exactly the local comparisons for that permutation. Conversely every independent local and recursive matching gives a system isomorphism. The number of records is constant, and the tensor-system compiler gives one ordinary TI comparison directly. The mod-$p$ construction is useful even when the local ordinary compilers are only provided as pairwise comparisons. [Linear-switch compiler](LinearSwitchCompiler.md) · [Tensor-system compiler](https://arxiv.org/html/2306.03135v2#S4)

## 3. The determinant flow

Keep the ordinary whole-tree comparison as a guard. Use the following positive queries on the target tree.

- Test every target local object for a negative local automorphism.
- For each pair of odd-weight target child subtrees at the same parent, test ordinary subtree equivalence by Section 2.

A YES in either list gives a negative automorphism of the whole target. In the first case insert the negative local map and identities elsewhere. In the second case exchange the two subtrees by a chosen isomorphism and its inverse. Their local signs multiply to one and the odd block exchange changes the total sign. Independence extends these maps to the full hierarchy, so either sign is attainable if the guard is true.

Suppose for the soundness part that both lists are negative. Every target subtree has only positive automorphism signs. This follows by induction. A local automorphism has positive sign, all child automorphisms have positive sign, and no odd children of the same type can be permuted. If several even children have the same type, choosing identifications with a representative makes the signs of their maps cancel around each permutation cycle. The block permutation itself is even on the based volume. Consequently the sign of every ordinary subtree comparison to a target subtree is constant among its transporters.

For the signed test create binary activations $x_{vz}$ for all candidate pairs at equal depth, now enabled by the ordinary **subtree** queries from Section 2. Set $x_{\rm root}=1$ and impose the conditional row and column equations (1) over $\mathbb F_2$. Add the following variables to this single system.

- For each node pair $v,z$, add two variables $d_{vz,s}$, $s=0,1$, enabled by the local comparison with sign $(-1)^s$. Require $\sum_s d_{vz,s}=x_{vz}$. Charge $d_{vz,1}$ in the final sign equation.
- For each pair $i<k$ of odd source children at $v$, and each pair of distinct odd target children $j,l$ at $z$, add a variable $y_{vz;ik;jl}$. Enable it by the ordinary conjunction of subtree comparisons $i\to j$ and $k\to l$. Require its sum over $j,l$ to equal $x_{vz}$ for each $v,z,i,k$. Charge the variable in the final sign equation exactly when $j>l$.

Set the sum of all charged variables to the requested bit, after any raw basis calibration. A conjunction of two queries is itself a positive switch instance, requiring both corresponding switches to equal one.

A genuine signed transporter gives a solution by taking its own pairs, local signs and inversions. For the converse with no free sign, analyze the total charge below any node pair $v,z$, including the pair's own variables. We claim it vanishes if $x_{vz}=0$ and equals the unique subtree sign bit if $x_{vz}=1$. Induct from the leaves. There is at most one enabled local sign, so the local charge has the stated behavior. Each odd source child has at most one compatible target child at $z$. Thus every inversion row has at most one enabled value, and the row equation forces its charge to vanish at activation zero and to equal the corresponding inversion at activation one.

It remains to add the child charges. By induction their nonzero contribution is $\sum_{i,j}x_{ij}\eta_{ij}$, where $\eta_{ij}$ is the unique subtree sign bit for each available child pair. For any fixed common ordinary subtree type, choose source identifications with a representative and target identifications from that representative. The available sign bits in this type then have the form $\eta_{ij}=u_i+v_j$, because every target automorphism has positive sign. Consequently its contribution, using (1), is
\[
 x_{vz}\left(\sum_i u_i+\sum_j v_j\right).
\]
This vanishes when the parent pair is inactive, even if some of its child activations were nonzero. When active it agrees with any literal matching of this type. The ordinary subtree query ensures such matchings exist at every active pair. This proves the claim for every node pair, including incompatible ones forced inactive. At the root the requested bit is therefore the actual sign.

The final test is the ordinary guard AND the OR of the free-sign disjunction and this determinant system. A positive OR enforces that the sum of its enabled binary switches is one. A positive AND forces each corresponding switch to be one. All ordinary subtree query inputs were constructed in one preliminary layer, the inversion availability queries take one more layer, and the entire determinant flow takes one switch layer for all depths. The number of candidate pairs and inversion rows is polynomial in the explicit trees. No level of recursion introduces another signed compiler call.

## 4. A family of arbitrary depth with a genuine sign constraint

Use three types of local pieces with all local automorphism signs positive. There is one even type $R$ of weight two, and two distinct odd types $P,Q$ of weight one. For a concrete tensor-system realization, $R$ is a two-dimensional vector space with both basis vectors marked. Use a one-dimensional space with two equal nonzero marks for $P$, and one with opposite nonzero marks for $Q$. The two odd types cannot be isomorphic, and the local maps fixing the displayed marks have determinant one.

Define $T_0$ to have local piece $R$ at its root and the two leaves $P,Q$. Define $T_h$ for $h>0$ to have the same local $R$ and leaves, plus two children of type $T_{h-1}$. Every subtree $T_i$ has even total weight, and the odd children of each interior node are the two distinct types. Hence every automorphism of $T_h$ has determinant one. For each copy of a nonterminal $T_i$ there is nevertheless a genuine exchange of its two even recursive children. The resulting effective permutation group has order at least $2^{2^h-1}$ and acts at depth $h$.

Compare the same typed hierarchy in a target frame that reverses the order of the two odd leaves at exactly one node. It is ordinarily isomorphic, and its subtree volume convention gives sign $-1$ for every transporter, by the multiplicative decomposition at that node. There is no free correction. The ordinary and signed hierarchy tests therefore differ for arbitrarily large depth and even-order symmetry group.

The local pieces may also be taken from the signed graph constructions instead of marked vector spaces. Use the even two-color alternating-path module for $R$ and two single-color matching modules with different part count profiles and odd total edge counts for $P,Q$. These have the indicated quotient color weights and sign-rigid characters. The hierarchy is then encoded with its explicit tree roles as above.

The theorem applies to independent hierarchical decompositions. It does not infer such a decomposition for arbitrary graph data or for a general connected cube-zero hard block, and it does not apply to overlapping modules whose separator maps still have to agree. The proofs are informal.
