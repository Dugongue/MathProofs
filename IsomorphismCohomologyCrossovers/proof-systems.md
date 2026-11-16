# Polynomial Calculus equivalence of two graph-to-tensor routes

**Theorem.** Over every field, the standard Graph Isomorphism (GI) equations reduce in both directions, in constant ordinary Polynomial Calculus (PC) degree, to Alternating Matrix Space Isometry (AMSI) on Grochow–Qiao's private-leaf graph spaces. Those AMSI equations and bare three-mode Tensor Isomorphism (TI) on the same alternating arrays also admit constant-degree reductions in both directions. Each substituted axiom has an explicit polynomial-size derivation. A second construction uses only $9n$ vertices and $m+10n$ edge slices for an $n$-vertex, $m$-edge graph. Combining either construction with the existing Grigoriev graph-algebra proof gives equivalence with its bare multiplication-tensor presentation.

This addresses two concrete branches of Galesi–Grochow–Pitassi–She Open Question 7.5. The AMSI instance is the published Grochow–Qiao output or the smaller alternative given here. The TI step is direct on those instances. The exact augmented tensors of Futorny–Grochow–Sergeichuk and the code and semisimple-Lie routes remain outside the theorem.

## Equations and degree accounting

Graphs are simple and undirected. We consider pairs with equal vertex and edge counts, which can be checked before constructing equations. In GI, $p_{ui}$ is the entry of the putative permutation from source vertex $i$ to target vertex $u$. The axioms are row and column sums equal to one, Boolean idempotence, row and column collisions, and $p_{ui}p_{vj}=0$ whenever the adjacency statuses of the two ordered pairs differ.

Let $V_G=F^{V(G)}$. Write $C_G:W_G\to\Lambda^2V_G$ for the injection sending an edge basis vector $ij$ of $W_G$ to $e_i\wedge e_j$ for $i<j$. Let $I_G:W_G\to V_G\otimes V_G$ be its image under $e_i\wedge e_j\mapsto e_i\otimes e_j-e_j\otimes e_i$. This latter map is injective in every characteristic and its full image consists of matrices with zero diagonal and skew transpose. Use $D(M)(v\wedge w)=Mv\wedge w+v\wedge Mw$, which is well-defined on $\Lambda^2V_G$ in all characteristics.

For AMSI, choose the convention
$$
(\Lambda^2X)C_G=C_H Z,\qquad XX'=X'X=I,\qquad ZZ'=Z'Z=I.
$$
For bare TI use $(X\otimes Y)I_G=I_H Z$ with two-sided inverse axioms for all three variable matrices. This convention and the usual cubic tensor group action are interderivable at constant degree after relabeling $Z$ as the inverse transpose of the usual third-mode map. Multiply by the witnessed inverse to pass between the conventions.

Matrix products below abbreviate entrywise expansions. Multiplying a proven line by a constant-degree polynomial costs at most polynomially many monomial multiplications. For a replacement in a product, multiply the difference by the remaining factors. Every proof below uses bounded-degree matrix expressions and a bounded number of variable-dependent factors per displayed identity, so each axiom simulation has constant degree and polynomial size.

## Recovering a graph from the AMSI equations

For any graph put
$$
\mathcal L_G=\{M:D(M)C_G\text{ has image in }\operatorname{im} C_G\}.
$$
For $u\ne v$, $M_{uv}$ is forbidden exactly when some $w\notin\{u,v\}$ is adjacent to $v$ and nonadjacent to $u$. Indeed, the coefficient of $e_u\wedge e_w$ in $D(M)(e_v\wedge e_w)$ is $M_{uv}$ up to sign, and every off-edge coefficient of a derivative has this form. Diagonal entries are always allowed.

Under the AMSI equations, for every fixed $M\in\mathcal L_G$, all forbidden entries of $XMX'$ in $\mathcal L_H$ vanish by constant-degree PC derivations. Write $D(M)C_G=C_GK$ for constant $K$. Use the identities
$$
D(XMX')(\Lambda^2 X)=(\Lambda^2 X)D(M),\qquad C_H=(\Lambda^2 X) C_G Z'
$$
to derive $D(XMX') C_H=C_H Z K Z'$. The first identity is obtained by expanding it on $v\wedge w$ and replacing $X'X v$ and $X'X w$ by $v$ and $w$. The second uses the action equation and $ZZ'=I$. Reading off the off-edge coefficients extracts each individual quadratic forbidden entry. The degree is at most five. By multiplying the action equation by $\Lambda^2X'$ on the left and $Z'$ on the right, one also gets $(\Lambda^2X')C_H=C_GZ'$, using the compound of $X'X=I$ and $ZZ'=I$. The same calculation transports $\mathcal L_H$ into $\mathcal L_G$ by $N\mapsto X'NX$.

### Grochow–Qiao's private leaves

Attach $n$ private leaves to each original vertex. This is the Grochow–Qiao transformation on graphical spaces. There are no nonisomorphic pairs with $n\le1$. For $n\ge2$, in each original column $v$ of $\mathcal L_G$ only the diagonal entry is allowed. For any $u\ne v$, take a leaf of $v$ other than $u$ as the witness $w$. A leaf column whose parent is $v$ permits the rows of $v$, the original neighbors of $v$, and the leaves of $v$. In original/leaf block coordinates this is the unital associative pattern algebra
$$
\mathcal L_G=\begin{pmatrix}F^n & R(G)\\ 0 & \bigoplus_v\operatorname{Mat}_n(F)\end{pmatrix},
$$
where the first block is diagonal and the top-right support is constant across leaf columns with a common parent.

Let $\mathcal K_G\subset\mathcal L_G$ consist of matrices with all original columns zero. It is the two-sided ideal generated by commutators. The top-left quotient is commutative, giving one inclusion. An allowed top-right matrix unit is $[E_{uu},E_{u\ell}]$. For distinct leaves $a,b$ with the same parent, $E_{ab}=[E_{aa},E_{ab}]$ and $E_{aa}=[E_{aa},E_{ab}]E_{ba}$. This gives all the remaining ideal basis elements. The formulas also work in characteristic two.

For any fixed matrix unit in $\mathcal K_H$, transport its displayed expression by conjugation $N\mapsto X'NX$. Conjugation of a product equals the product of conjugates by $XX'=I$, and each conjugated factor lies in $\mathcal L_G$ by the above equations. A commutator or its product with a third such factor has original columns zero, since the original blocks are diagonal and the bottom-left blocks vanish. This last step is a coordinate identity after removing the derived zero lines. Hence every original column of $X'E_{aa}X$ vanishes for a target leaf $a$. Left-multiply by $X$ and reduce $XX'=I$. This gives $X_{ai}=0$ for all original $i$. Running the same argument with $X'$ gives its leaf-row/original-column zero block. The inverse equations therefore restrict to the original-to-original blocks.

For original $i$, the original block of $M_i=XE_{ii}X'$ is diagonal. For original $u$, the same holds for $N_u=X'E_{uu}X$. Set $p_{ui}=X_{ui}X'_{iu}$ on originals. The two block inverse identities give row and column sums. Derive $M_iM_j=\delta_{ij}M_i$ and $N_uN_v=\delta_{uv}N_u$ using the inverse equations. Restrict these to originals. Terms through leaf rows vanish by the bottom-left zero block. Reading their diagonal entries derives idempotence and both row and column collisions.

For a source edge $ij$ and target distinct nonadjacent $u,v$ on originals, the off-edge coordinate of the action equation is $X_{ui}X_{vj}-X_{uj}X_{vi}=0$, up to sign. Multiply by $X'_{iu}X'_{jv}$. The first term becomes $p_{ui}p_{vj}$ and the second contains the off-diagonal original entry $X_{uj}X'_{jv}$ of $M_j$, already derived zero. Use the reverse action equation and $N_u$ for the opposite adjacency mismatch. Equal-endpoint mismatches already follow from collisions. This derives every original GI axiom under the degree-two substitution.

### Two private 5-cycles

Alternatively, attach two disjoint private 5-cycles to each original vertex, with that vertex identifying one vertex of each cycle. This makes $9n$ vertices and $m+10n$ edges. Each original has at least four neighbors. Given an original $v$ and any $u\ne v$, at least one of its four private neighbors $w$ differs from $u$ and is nonadjacent to $u$. Each private neighbor has exactly one neighbor other than $v$, and these four other neighbors are distinct. If $v$ is private, it has two neighbors. An adjacent $u$ cannot be adjacent to the other neighbor of $v$, because a triangle cannot contain a private vertex. A nonadjacent $u$ cannot be adjacent to both neighbors of $v$, because a 4-cycle cannot contain a private vertex. Thus the required witness exists for every $u\ne v$, and the entire $\mathcal L_G$ is diagonal.

The preceding idempotent extraction now gives the padded GI equations directly. To restrict them to original vertices, fix an original $i$ and a private $u$ and three distinct neighbors $j_1,j_2,j_3$ of $i$. Expand the product of $p_{ui}$ with their three column sums. Each term $p_{ui}\prod_h p_{v_h j_h}$ vanishes if any $v_h$ is nonadjacent to $u$, by the adjacency axiom. Otherwise two $v_h$ coincide, since $u$ has only two neighbors, and the term vanishes by collision. This derives $p_{ui}=0$ at degree four in the extracted padded permutation variables. Reverse source and target for the other block, and restrict all GI axioms to the original block. This argument works in every characteristic.

### Forward substitutions for both constructions

Extend an original permutation to the padding by sending each added vertex to the equally labeled added vertex of the target copy of its parent. Entrywise this uses original GI variables on matching original or private labels and zero elsewhere. Row and column axioms transfer, and the new adjacency cases use only equality or inequality of parents and the fixed private-label rule. Equality is enforced by Boolean idempotence and collisions. Derive $P^TP=PP^T=I$ from the permutation equations. Use $X=P$, $X'=P^T$ and the edge-to-edge blocks of $\Lambda^2P,\Lambda^2P^T$ for $Z,Z'$. Both exterior-square actions have zero off-edge entries in edge columns by the padded adjacency equations. Expanding the exterior-square inverse relations and using $P^TP=PP^T=I$ gives the two inverse equations on edge space. The AMSI action is the definition of $Z$ together with the off-edge zeros.

## Bare three-mode Tensor Isomorphism

Both graph extensions have no isolated vertices. In fact this step works on any two graphs with no isolated vertices. AMSI gives TI by setting $Y=X,\ Y'=X'$. For the converse put $R=X'Y$ and $S=Y'X$. Their inverse equations follow by two applications of known inverses. Multiplying by $X'$ in each of the first two modes of the TI action gives
$$
(I\otimes R)I_G=(X'\otimes X')I_H Z .
$$
The right side is alternating on each edge column by expansion. On $ij$, the left side is $e_i\otimes Re_j-e_j\otimes Re_i$. Zero diagonal gives $R_{ij}=R_{ji}=0$. The skew transpose gives $R_{kj}=R_{ki}=0$ for $k\notin\{i,j\}$, and $R_{ii}=R_{jj}$. With an incident edge at every vertex these give every off-diagonal entry of $R$ as an individual degree-two zero line. From $RS=I$ derive $R_{ii}S_{ii}=1$.

Let $L,L'$ be diagonal on source edge space with entry $R_{ii},S_{ii}$, respectively, on $ij$, choosing $i<j$. Their two inverse identities follow. Using $Y=XR$ and equality of the two diagonal entries for each edge, derive $(\Lambda^2X)C_G L=C_H Z$ by expansion. Right-multiply by $L'$. The AMSI edge witness is $ZL'$ with inverse $LZ'$, both degree at most three. The constant-degree derivation uses the original inverses and the newly derived edge inverses, without introducing any PC variables.

## Consequences and attribution

All substitutions and all simulations have degree bounded by absolute constants. In composition, replace each PC variable multiplier by its bounded-degree substitution and perform its monomial multiplications successively. Thus refutation degree transfers up to constant factors and an additive constant, with polynomial expanded proof sizes at bounded degree. The same proof comparisons combine with the existing MathProofs Grigoriev result. The new contribution is the explicit PC extraction via conjugation, first through the commutator-generated ideal for the actual Grochow–Qiao padding and then through the diagonal Lie algebra for smaller padding. The graphical stabilizer is related to the classical Dani–Mainkar analysis. The direct conversion from bare TI to AMSI on these graphs uses their edge columns to force the relative map $X'Y$ to be diagonal.

- Galesi, Grochow, Pitassi and She, [On the Algebraic Proof Complexity of Tensor Isomorphism, §7.5](https://arxiv.org/html/2305.19320#S7.SS5).
- Grochow and Qiao, [Isomorphism problems for tensors, groups, and cubic forms, Proposition 7.1 and Lemma 7.2](https://arxiv.org/html/1907.00309).
- He and Qiao, [On the Baer–Lovász–Tutte construction of groups from graphs](https://arxiv.org/abs/2003.07200).
- Dani and Mainkar, [Anosov automorphisms on compact nilmanifolds associated with graphs](https://repository.ias.ac.in/74514/1/22-PUB.pdf).
- MathProofs, [Low-degree Polynomial Calculus equivalence for Grigoriev graph tensors](https://github.com/Dugongue/MathProofs/blob/main/IsomorphismCrossoversRoundThree/proof-complexity.md).

AI-assisted informal proof. Publication priority for the PC statements remains unverified.
