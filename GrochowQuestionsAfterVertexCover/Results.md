# Monotone permanent-oracle lower bounds and three isomorphism results

Of four published research targets, the argument for Joshua Grochow’s **Open Question 5.6** covers the full question. We have two informal derivations. We found no earlier explicit resolution in the sources examined. Publication priority, independent expert review, and machine verification remain outstanding.

| Published question | Result in this packet | Scope |
| --- | --- | --- |
| Grochow, *Monotone Projection Lower Bounds from Extended Formulation Lower Bounds*, Q5.6 | Exponential lower bounds for monotone circuits with permanent oracle gates computing the Hamiltonian-cycle, general perfect-matching, or cut polynomial | Full formal-polynomial question, including bounded depth, weakly skew, and general circuits |
| Chen–Grochow–Qiao–Tang–Zhang, Q1.9 | One polynomial-size ordinary TI instance preserves determinant-one isomorphism at every finite extension of a fixed odd finite field | Finite étale multiplication tables in coherent bases. Unrestricted SL-TI containment remains open |
| Grochow–Srivastava–Thakkar, Q3(3), also related to Q2 | Explicit criterion, construction, and exact count for epimorphisms of products of finite Heisenberg groups | Polynomial time on their Cayley tables. General genus-two epimorphism and unrestricted counting remain open |
| Grochow–Urisman, Q1.9 | Polynomial-time graph comparison when one input belongs to one of the specified affine rank-three series and the other graph is arbitrary | Includes every bilinear-forms graph H_q(2,e) with e at least two. The full symmetry-characterized promise remains open |

## Why the oracle lower bound works

A permanent gate can select any of m! permutations. Keeping one variable for every permutation would lose the lower bound. Instead, keep the m² expected counts of its matrix entries. The possible counts form a scaled doubly stochastic matrix, with forbidden entries fixed to zero. At a shared gate, add the occurrence counts arriving from every parent. Sampling a fresh local monomial each time a gate is visited proves that every feasible flow really is an average of valid expanded computations.

Consequently a circuit of ordinary description size s with permanent queries of orders m₁ through mₜ gives an extended formulation of its output Newton polytope of size O(s + t + ∑mᵢ²). Grochow’s three target polytopes require exponentially many inequalities. This rules out a polynomial-size reduction even with shared computation and arbitrary nesting. Our second proof gets the same bound by recording optimal row and column potentials separately at each oracle call. A further consequence applies to the formal polynomial listing the vertex covers encoded by tensor extension degrees. Evaluating a Boolean function on bit strings is a different question in Grochow’s paper. [Flow proof and prior art](Arithmetic.md) · [Independent assignment-duality proof](AssignmentAudit.md) · [Published question](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf#page=11)

## What transferred to isomorphism

**Tensors.** The previous lower bound charged an ordinary étale table exponentially for expressing a disjunction of prime-divisibility tests. A tree with ordered and exchangeable branches expresses the same disjunction with quadratically many leaves. Encoding the whole tree once as an ordinary tensor preserves every scalar extension. [Proof](Tensors.md) · [Original question](https://arxiv.org/html/2306.03135v2#S1.SS5)

**Groups.** Surjectivity forces each surviving source Heisenberg factor into one target factor. Field divisibility determines which assignments are legal. Symplectic dimension gives the exact capacity to be filled at each target. This also explains a striking input-size distinction. The full group tables allow a polynomial-time algorithm, whereas compact rank lists already encode strong 3-Partition. [Proof and count](Groups.md) · [Original questions](https://arxiv.org/html/2609.07429v1#S7)

**Graphs.** In a bilinear-forms graph the neighbors of zero split according to the two projective directions of a rank-one matrix. The quotient is a rectangular rook graph. Recognizing these neighborhoods, checking the global intersection conditions, and applying the published characterization gives a sound test against arbitrary input graphs. The other geometries and parameter ranges are specified in the proof. [Recognition algorithms](Graphs.md) · [Original question](https://arxiv.org/html/2606.26244v2#S1.SS3)
