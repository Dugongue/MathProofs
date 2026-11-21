# Minimum faithful actions with a small noncyclic commutator part

Let \(G\) be a class-two group given by permutation generators of bit length \(L\). For each prime \(p\), write the derived subgroup of its Sylow group \(P\) as
\[
[P,P]\cong C_{p^a}\times B_p,
\]
where the first factor is a largest cyclic direct factor, and \(B_p=1\) if the derived subgroup is trivial or cyclic. There is a deterministic algorithm of time
\[
(1+\max_p |B_p|)\operatorname{poly}(L)
\]
for computing the minimum faithful degree and generators of stabilizers for a minimum action. The explicit new permutations can be printed with additional time polynomial in the input length and the output degree. In particular the succinct permutation-generator problem is polynomial-time solvable for every class-two group with cyclic derived subgroup, even with an unbounded center. The earlier algorithm was parameterized by \(|Z(G)|\). [Earlier class-two algorithm and constructive cyclic-center calculation](https://github.com/Dugongue/MathProofs/blob/main/GrochowGroupFrontier/MinimumAction.md) · [Kantor–Luks, §13](https://pages.uoregon.edu/kantor/PAPERS/quotient.pdf#page=9)

## Marking one uncovered vector

Work one Sylow factor \(P\) at a time and put \(S=Z(P)[p]\). A coset action family is faithful exactly when its stabilizer traces on \(S\) intersect trivially. A minimum action can use hyperplane traces on \(S\). In fact, for a stabilizer \(H\) with \(D=H\cap S\) of codimension \(d\ge1\), choose \(d\) hyperplanes \(D_i\) of \(S\) intersecting in \(D\). The new stabilizers \(HD_i\) have exactly the traces \(D_i\) and each has index \([P:H]/p^{d-1}\). Their total costs are at most the old cost, because \(d\le p^{d-1}\). An orbit whose trace is all of \(S\) can be dropped, and dependent hyperplane marks can also be dropped. This is the central-socle matroid formulation of the minimum action. [Elias–Silberman–Takloo-Bighash](https://arxiv.org/abs/0705.4122)

Suppose an independent set of cheapest marks has already been chosen. Let \(T\subseteq S\) be its joint kernel. The next minimum-cost independent mark is the cheapest one nonzero on one of any basis of \(T\). For a nonzero test vector \(z\) of that basis, compute a largest subgroup \(H\) with \(z\notin H\). Such an optimum can be chosen with hyperplane trace: pick a hyperplane \(D_0\) containing \(H\cap S\) and avoiding \(z\), and replace \(H\) by \(HD_0\). This preserves avoidance and does not increase cost. One call per basis vector of \(T\) therefore implements one step of the minimum-weight basis algorithm. This eliminates enumeration of all characters of \(S\).

## Avoidance with a small character search

Fix \(z\) and put \(D=[P,P]\langle z\rangle\), a central abelian subgroup. For any subgroup \(H\) avoiding \(z\), choose a character \(\theta:D\to\mathbb Q/\mathbb Z\) killing \(H\cap D\) and nonzero on \(z\). It exists by extending the character defined on \(\langle z\rangle(H\cap D)\) inside the finite abelian group \(D\). If \(J=\ker\theta\), replacing \(H\) by \(HJ\) still avoids \(z\), since its trace on \(D\) is \(J\). Conversely a subgroup of \(Q=P/J\) disjoint from \(D/J\) lifts to a subgroup avoiding \(z\). Thus it suffices to consider kernels of cyclic quotient maps from \(D\) that are nontrivial on \(z\), and maximize the order of the lifted subgroup.

For each such kernel the cyclic group \(D/J\) is central in \(Q\), contains its derived subgroup, and has a faithful character. The central-character extension algorithm from the earlier proof applies with \(D/J\) as the distinguished cyclic subgroup. To recall the mechanism, a subgroup disjoint from \(D/J\) can be enlarged by the kernel of a character on \(Z(Q)\) extending the distinguished one. The new quotient has cyclic center because all commutators lie in \(D/J\). For each extension order, the commutator pairing gives the common square-root term in the best subgroup index. The least extension order is found by testing which powers of the center the distinguished character can kill. The exceptional binary Arf test among order-two extensions is a quadratic-form test on an affine space. These are polynomial-bit computations on abelian sections. This part depends on the quotient kernel and not on a choice of generator of its cyclic image. [Cyclic-center construction and the extension optimization](https://github.com/Dugongue/MathProofs/blob/main/GrochowGroupFrontier/MinimumAction.md#4-optimize-over-extensions-without-enumerating-the-larger-center)

To bound the enumeration, write \(D=\prod_i C_{p^{e_i}}\) with \(e_1\) largest. For each target order \(p^j\), an epimorphism has at least one generator with unit image in \(C_{p^j}\). Normalize its first such image to one, by multiplying the whole map by a unique unit. The chosen coordinate has exponent at least \(j\). Enumerate all images on the remaining coordinates consistent with their orders, discarding any map with an earlier unit or killing \(z\). For each chosen coordinate the number of tuples is at most
\[
p^{\sum_i\min(e_i,j)-j}\le \prod_{i>1}p^{e_i}.
\]
This lists all possible kernels. If \(z\) belongs to the derived subgroup the bound is \(|B_p|\). Otherwise \(D=[P,P]\times\langle z\rangle\) and the bound is at most \(p|B_p|\). Both the number of target orders and the rank of \(D\) are polynomially bounded in the input length, and \(p\) is at most the supplied permutation degree for a nontrivial Sylow group. The cyclic quotient search therefore costs \(|B_p|\operatorname{poly}(L)\) for each test vector.

Constructive subgroup membership, Sylow splitting by CRT powering and abelian section coordinates are as in the earlier proof. A finite nilpotent group's degree is the sum of the Sylow degrees, obtained by replacing mixed-prime coset actions by separate Sylow coset actions. Combining the stabilizer lists proves the result. For instance, products of extraspecial groups with arbitrarily many central abelian direct factors can have huge centers but still fall in the polynomial case whenever the total derived subgroup is cyclic.
