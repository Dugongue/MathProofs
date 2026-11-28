# The arithmetical hierarchy in finite homotopy extension games

**Status.** Complete informal proof. The quantifier hierarchy is classical. Here each level is realized by a fixed finite tower of inclusions and a single finite target, with one input degree. The same games have an input-independent outcome after replacing the integral target with any local coefficient target.

## Statement

For every \(k\ge 1\) and either initial quantifier, there are a finite simply connected CW pair of dimension at most four, a tower of subcomplex inclusions
\[
A_0\subset A_1\subset\cdots\subset A_k\subset X,
\]
and a single finite simply connected target \(Y\). The terminal test is either extendibility or nonextendibility of a map from \(A_k\) to \(X\), selected once for the template. An input \(e\in\mathbb N\) changes one degree coordinate of the specified initial map \(A_0\to Y\). At stage \(i\), the player corresponding to the \(i\)-th quantifier ranges over relative homotopy classes of maps \(A_i\to Y\) extending the map already chosen on \(A_{i-1}\). The truth set of this game in \(e\) is \(\Sigma_k^0\)-complete for an existential first move and \(\Pi_k^0\)-complete for a universal first move, for computable many-one reductions.

For the coefficient-natural targets \(Y_R\) of the same templates, over every commutative local ring \(R\) and over every direct product of such rings, the terminal map always extends, for every input and every sequence of moves. The integral quantifier hierarchy therefore persists even under this common local behavior. For every prescribed \(M\ge1\), the terminal extension space in these constructions can also be chosen to have input- and move-independent weak homotopy type over every finite product of local rings satisfying \(\mathfrak m^M=0\).

## Arithmetical normal form

Take a complete set for the indicated hierarchy level and write its membership as \(Q_1v_1\cdots Q_k v_k\,D(e,v_1,\ldots,v_k)\), with alternating number-quantifier blocks and a recursive predicate \(D\). If \(Q_k\) is existential, represent \(D\) by an existential Diophantine equality and absorb its witness variables into the final existential block. If \(Q_k\) is universal, represent the complement of \(D\) by an existential Diophantine equality, then negate and absorb the witnesses into the final universal block. This uses DPRM for recursive predicates. Replace original natural variables by sums of four integer squares, a surjective parametrization, and use integer witness variables as permitted by the same conversion. Thus for suitable finite integer tuples \(a_i\) and one fixed integer polynomial \(F\), the complete set has the form
\[
 Q_1 a_1\in\mathbb Z^{n_1}\cdots Q_k a_k\in\mathbb Z^{n_k}\quad F(e,a_1,\ldots,a_k)\mathrel{\triangleleft} 0,
\]
with \(\triangleleft\) equality in the first construction and inequality in the second. Polynomial evaluation is recursive. This also supplies the hierarchy upper bound for this fixed template.

## The finite topological game

For an integer \(M\ge1\), let \(S\) be the affine scheme over the parameter coordinates \((e,a)\) obtained as follows. Introduce \(z,t,u\) and put
\[
 H=(u^2+2)\bigl(z^2(F(e,a)^2+u^2)+(z-1)^2+t^2\bigr).
\]
Take the disjoint union of \(V(H^M)\) and \(D(H)\), using an idempotent and an inverse witness to give an affine presentation. For every given integer \((e,a)\) the fiber has a point precisely when \(F(e,a)=0\). The open part has no integer point since \(u^2+2\) is never a unit. In the closed part the sum of squares forces \(z=1\), \(t=u=0\) and \(F(e,a)=0\). Thus the affine fiber test or its negation gives the terminal predicate exactly.

Use the exact affine realization by a cup-product target. Mark the two anchor spheres, the input sphere, and one separate left wire sphere \(P\) for each scalar coordinate occurring in \(a_1,\ldots,a_k\). Omit the guard that would set the second degree of such a marked variable sphere to zero. Keep its right wire sphere \(Q\) unmarked, with its first degree forced to zero, and keep the usual gate equating the first degree of \(P\) to the second degree of \(Q\). Every occurrence of \(P\) in the circuit gates is paired either with the second anchor or with a right wire, both of which have first degree zero. Thus the omitted coordinate stays free and makes no contribution to any gate. The anchors prescribe \((1,0)\) and \((0,1)\), and the input sphere is fixed at \((e,0)\). Define \(A_0\) to be the wedge of these three spheres, and obtain \(A_i\) from \(A_{i-1}\) by adjoining the variable spheres for \(a_i\). Complete \(A_k\) to \(X\) by attaching the remaining circuit wire spheres and all four-dimensional gates. All templates, including the number of spheres and gates, depend only on the chosen hierarchy level and first quantifier. The affine construction and its finite target comparison apply in dimension four. [Exact affine realization](https://github.com/Dugongue/MathProofs/blob/main/Top10CrossoverProofs/UniversalRelativeMappingSchemes.md).

At each stage the new relative homotopy classes are exactly \((\mathbb Z^2)^{n_i}\). Indeed \(A_i\) is formed by adjoining the extra based spheres at the common basepoint, and \(\pi_2(Y)=\mathbb Z^2\). Replacing a representative by a homotopic map does not change whether it extends across a cofibration, by homotopy extension. The second coordinate of each new sphere is immaterial and the first coordinates fill the required block. Existential and universal quantification over \((\mathbb Z^2)^{n_i}\) therefore equals quantification over \(\mathbb Z^{n_i}\) for these tests. After all moves, restriction to \(X\) is possible exactly when the corresponding scheme fiber has a point. Taking the stated terminal test proves the reduction and the hierarchy assertion.

## Coefficient naturality and depth

For any ring \(R\), the moves of the coefficient game are relative classes in \((R^2)^{n_i}\). For every choice of the degree coordinates, set \(z=t=0\), so the parenthesized expression in \(H\) is 1. In a local ring, at least one of 2 and 3 is a unit. If 2 is a unit, use \(u=0\), and otherwise use \(u=1\), so \(H\) is a unit in either case. This defines a point on the open piece. Products of these points work in direct products of local rings. The terminal existence predicate consequently has constant value true, and its negation has constant value false. Every move set is nonempty, so the game has the corresponding constant outcome.

For a fixed \(M\) and the product probes with \(\mathfrak m^M=0\), the same scheme fiber projects bijectively and naturally to \(R^3\) on \((z,t,u)\). A value of \(H\) is either a unit or satisfies \(H^M=0\) on each local factor, selecting a unique scheme point above the coordinates. The relative cells of \((X,A_k)\) are two- and four-dimensional. As in the mapping-space computation in the bounded probe theorem, the space of maps to \(K(R,2)^2\) with fixed boundary has weakly discrete components and each component of the analogous space for \(K(R,4)\) has weak type \(K(H^2(X,A_k;R),2)\). Taking the homotopy fiber gives for each of the \(R^3\) terminal extension classes the same weak type \(K(H^2(X,A_k;R),1)\), regardless of the input or chosen moves.
