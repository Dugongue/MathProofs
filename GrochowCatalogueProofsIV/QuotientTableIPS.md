# IPS with a supplied finite quotient table

## GP-0742

For circuit-described equations over an algebraically closed field, the existence of polynomial-size IPS refutations of all unsatisfiable systems is equivalent to the corresponding statement with a supplied, correct, one-dimensional quotient-algebra multiplication table and one formula with invertible residue in that quotient. The equivalence also holds for polynomial-time refutation construction and for search procedures with polynomial overhead in the refutation size. The table in the hard direction is always the same table, with displayed basis $\{1\}$.

### A uniform one-dimensional gadget

Take any unsatisfiable system $F_1(x)=\cdots=F_m(x)=0$. Introduce a selector $t$ and the ideal
$$
J=\langle t^2-t,\ (1-t)x_i\ (1\le i\le n),\ tF_j(x)\ (1\le j\le m)\rangle.
$$
The idempotent $t$ gives the product decomposition of the quotient into the branch $t=0$ and the branch $t=1$. The first branch is the ground field because all $x_i$ vanish. The second branch is the zero ring by the Nullstellensatz. Thus the source quotient is exactly the ground field, with the explicit residue map $x_i,t\mapsto0$. Supply its one-entry multiplication table, and add the single equation $1-t=0$, whose residue is $1$. The resulting full system has no common zero. Constructing the displayed data requires only the original circuits without deciding any new algebraic property.

An IPS refutation of the enlarged system specializes at $t=1$. The placeholders for $t^2-t$, $(1-t)x_i$, and $1-t$ can all be set to zero because those polynomials vanish at $t=1$. The remaining placeholders correspond to the original $F_j$, so the specialized circuit satisfies both IPS identities for the original system. Its size is at most that of the supplied refutation.

Conversely, take an IPS circuit $C(x,y)$ for the original system, with $C(x,0)=0$ and $C(x,F(x))=1$. In the enlarged system let $Y_j$ be the placeholder for $tF_j(x)$ and $Y_*$ be the placeholder for $1-t$. Replace $y_j$ by $Y_j+F_j(x)Y_*$. All placeholders zero give zero. Substituting the actual equations yields $C(x,F(x))=1$ because $tF_j+F_j(1-t)=F_j$. The forward circuit transformation has polynomial overhead. This gives both directions with exact restrictions, and proves the equivalences. If the table is instead required to describe the full inconsistent system, that full quotient is the zero algebra, whose empty table supplies no additional information.

### A sufficient condition for efficient extraction

There is a direct certificate when the quotient data also give certificates relating original generators to multiplication. For example, if from the specified equations $q_i(x)=0$ one has identity
$$
x_j b_\ell(x)-\sum_h M_{j,\ell,h} b_h(x)
=\sum_i A_{j,\ell,i}(x)q_i(x)
$$
for every basis product, with polynomial-size circuits for the $b_\ell,A_{j,\ell,i}$, the multiplication operations can be carried out while tracking such identities. More generally a circuit evaluation gate is represented by a quotient coordinate vector and an IPS expression for the difference from its basis representative. At addition add the two expressions. At a product use
$$
fg-\widehat f\widehat g=(f-\widehat f)g+\widehat f(g-\widehat g),
$$
and then use the certified basis product identities to replace $\widehat f\widehat g$ by its representative. Assume the data provide the residue identities for constants and variables and all basis products, with circuit representations and a displayed representative $1$ for the unit. Evaluate any added equation $g$ with this procedure, compute its inverse residue by linear algebra, and use the certified basis products once more to derive $g b-1\in J$ in IPS form. Adding the placeholder for $g$ with multiplier $b$ yields an IPS refutation. Shared circuit gates preserve polynomial overhead in the certificate inputs and table. The hard gadget shows why this sufficient condition requires certified reduction identities in addition to the abstract table.

The preceding catalogue derives controlled-degree Macaulay circuits in a structured univariate case. The selector construction isolates the missing information for arbitrary circuit axioms. [IPS definitions](https://www.cs.toronto.edu/~toni/Papers/jacm-gp.pdf) · [Prior Macaulay circuits](https://github.com/Dugongue/MathProofs/tree/4548210b7d800b5fb612d338d7daa77cdc7d8ae0/GrochowCatalogueProofsII)
