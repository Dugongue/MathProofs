# Central epimorphisms above all automorphisms of a displayed simple quotient

## GP-0364

Let $G,H$ be finite perfect groups with specified central kernels $A,B$ and common quotient $Q$, where $Q$ is nonabelian simple and given by its multiplication table. Give $G$ by a finite presentation with the quotient image of each generator. Give $H$ by a central normal form using $Q$, a cyclic-factor basis of $B$ whose factor orders are in binary, and an evaluable normalized cocycle in that basis. There is a deterministic bit-polynomial algorithm to decide whether $G$ surjects onto $H$ above any automorphism of $Q$, to count all such maps, and to recover their generator images. The extensions themselves need not be given by tables.

Choose a generating pair of $Q$ by trying pairs and closing them under multiplication. Such a pair exists by finite simple two-generation. Try all images of the pair and propagate the map along the Cayley graph. Discard inconsistent or nonbijective maps. This gives every automorphism once, with at most $|Q|^2$ trials. [Finite simple two-generation](https://darkwing.uoregon.edu/~kantor/PAPERS/gkfinal.pdf)

Fix one automorphism $\sigma$. If $x_i$ is a source generator and $q_i$ its image in $Q$, select the displayed representative $y_i=s_H(\sigma q_i)$. Any compatible map sends $x_i$ to $y_i b_i$ for $b_i\in B$. For each source relator $r_j$, the word $r_j(y_1,\ldots,y_\ell)$ belongs to $B$; calculate its coordinate vector $c_j$ in the central normal form. Since the corrections $b_i$ are central, exactly the following congruences make the relators hold:
$$
\sum_i e_{ji} b_i=-c_j\quad\text{in }B ,
$$
where $e_{ji}$ is the signed exponent sum of $x_i$ in $r_j$. Straight-line programs for relators also work, since evaluation and exponent totals can be processed gate by gate. The coordinates of the corrections are independent unknowns modulo each binary factor order. Add one integer slack variable multiplied by that order to each corresponding equation and solve by Smith normal form with transformations. The cost is polynomial in the presented data and evaluation time of the supplied cocycle. [Polynomial Smith normal form](https://doi.org/10.1137/0208040)

Every solution gives a homomorphism by the presentation and sends $A$ into $B$. Its image $L$ satisfies $LB=H$, so $H'=(LB)'=L'\subseteq L$ by centrality. Perfection of $H$ makes it onto. Conversely every compatible epimorphism passes the system for its quotient map. Two lifts of the same $\sigma$ differ pointwise by a homomorphism $G\to B$, because their values agree modulo the central subgroup. Perfection of $G$ makes that homomorphism trivial. Each consistent system therefore contributes exactly one to the count. A solution yields the generator images without enumerating the extensions or their kernels.

The bit bound uses the displayed quotient table and target normal form. [Earlier central extension cosets](https://github.com/Dugongue/MathProofs/blob/cbce8131e2cb46db9fcc20e31490cb13eb850e95/CentralExtensionCosets/PROOF.md)
