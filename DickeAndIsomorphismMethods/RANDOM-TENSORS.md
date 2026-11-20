# The first stabilizer correction for random concise three-tensors

## Theorem

Fix a prime power \(q\). Choose \(T\) uniformly from the concise tensors in \((\mathbb F_q^n)^{\otimes3}\), where concise means that all three flattenings have rank \(n\). Use independent mode changes of basis. Divide the stabilizer by the scalar kernel
\[
K=\{(\lambda I,\mu I,\nu I):\lambda\mu\nu=1\},
\qquad \Gamma=\operatorname{GL}_n(\mathbb F_q)^3/K .
\]
Set
\[
a_n=\frac{1}{q-1}\left(\frac{(q^n-1)(q^{n-1}-1)}{q-1}\right)^2,\qquad
b_n=\begin{cases}
\left(q^{n-1}(q^n-1)/(q-1)\right)^2& q>2,\\
0 & q=2 .
\end{cases}
\]
As \(n\) grows through positive integers,
\[
\begin{split}
\Pr(\operatorname{Stab}_{\Gamma}(T)\ne1)
 &=3(a_n+b_n)\,q^{-2n^2+2n}\bigl(1+O_q(q^{-n})\bigr),\\
\mathbb E\bigl(|\operatorname{Stab}_{\Gamma}(T)|-1\bigr)
 &=3\bigl((q-1)a_n+(q-2)b_n\bigr)
          q^{-2n^2+2n}\bigl(1+O_q(q^{-n})\bigr).
\end{split}
\]
In particular the first probability is \(\Theta_q(q^{-2n^2+6n})\). Conditional on a nontrivial effective stabilizer, with probability \(1-o(1)\) it is one of two explicitly embedded groups: the additive group of \(\mathbb F_q\) acting by a paired rank-one transvection in two modes, or the multiplicative group of \(\mathbb F_q\) acting on a paired one-dimensional summand in two modes. The second type is absent for \(q=2\).

If \(c_n\) is the number of concise arrays, their number of ordinary tensor orbits is exactly \(c_n/|\Gamma|\) times \(1+\mathbb E(|\operatorname{Stab}_\Gamma(T)|-1)\), by the orbit-counting lemma. The second display thus gives the leading correction to that orbit count. This is a written proof for fixed \(q\).

## 1. Fixed-space estimates

For a matrix \(A\in\operatorname{GL}_n(\mathbb F_q)\), put
\[
r(A)=n-\max_{\lambda\in\overline{\mathbb F}_q}\dim\ker(A-\lambda I).
\]
For any invertible \(n^2\)-dimensional matrix \(D\),
\[
\operatorname{codim}\operatorname{Fix}(A\otimes D)\ge r(A)n^2 .
\tag{1}
\]
Indeed the fixed vectors can be written as matrices \(M\) satisfying \(A M=M(D^{\mathsf T})^{-1}\). Over the algebraic closure, against an input Jordan block of size \(b\) and eigenvalue \(\lambda\), the dimension of intertwiners is the sum of \(\min(b,b_j)\) over the matching target blocks of sizes \(b_j\). This is at most \(b\) times the number of those target blocks, hence at most \(b(n-r(A))\). Sum over the input blocks. Ranks are unchanged by field extension.

If any of three mode changes has \(r(A)\ge6\), (1) gives fixed probability at most \(q^{-6n^2}\) on uniform arrays. Summing over at most \(q^{3n^2}\) triples gives \(q^{-3n^2}\), both for the probability and as a bound on this part of the expected number of witnesses.

Suppose all three deficits \(r_i\) are at most \(5\) and \(n>10\). The eigenspace of dimension \(n-r_i>n/2\) is unique, so its eigenvalue \(\lambda_i\) is rational by Frobenius. The exceptional matrix \(A_i-\lambda_i I\) has rank \(r_i\). There are at most \(q^{O(n)}\) such triples for fixed \(q\), since a rank-at-most-five matrix is a product of an \(n\)-by-\(5\) matrix and a \(5\)-by-\(n\) matrix. If \(\lambda_1\lambda_2\lambda_3\ne1\), the threefold product of the large eigenspaces is a subspace disjoint from the fixed subspace, of dimension at least \((n-5)^3\). These triples have negligible total fixed probability.

If \(\lambda_1\lambda_2\lambda_3=1\), divide the three mode matrices by their large eigenvalues. This is normalization by \(K\) and yields representatives \(A_i=I+U_i\) with \(U_i\) of rank \(r_i\). Write \(H_i=\ker U_i\) and \(L_i=\operatorname{im}U_i\). The image of the tensor operator minus identity contains
\[
L_1\otimes H_2\otimes H_3,\quad
H_1\otimes L_2\otimes H_3,\quad
H_1\otimes H_2\otimes L_3 .
\]
For example the first is the image on the full first mode tensored with the other two kernels. For each mode choose a basis adapted to its two subspaces \(L_i,H_i\), by extending a basis of their intersection in both. The three displayed spaces are then coordinate subspaces in one tensor basis. Their summed dimension is at least the sum of the three dimensions minus the sum of the pairwise intersection dimensions. The latter are at most \(r_i r_j n\) for pair \(i,j\). In particular, when \(\sum_i r_i\ge3\) the codimension of the fixed space is at least \(3n^2-O(n)\). After summing over all the low-deficit triples this proves a total bound \(q^{-3n^2+O_q(n)}\) for all classes so far considered. All these estimates bound both a union probability and the expected number of the indicated nonidentity effective elements, since their number is bounded by the number of triples.

A single nonscalar mode fixes no concise tensor, regardless of the other two scalar factors. Its fixed tensors have their corresponding support inside one eigenspace, of dimension less than \(n\). It follows that the only still uncounted nonscalar witnesses on concise tensors are normalized triples with one identity and two rank-one updates.

## 2. Counting the paired rank-one conditions

For a chosen pair of active modes, regard the tensor as \(n\) matrix slices \(M\) in those modes. The fixed condition is \(A M=M D\), with \(D=(B^{\mathsf T})^{-1}\) for the other mode matrix \(B\). After normalization write \(A=I+U\), \(D=I+Z\), where \(U,Z\) are nonzero rank-one matrices. A rank-one update of the identity is either unipotent (the rank-one part is square zero) or diagonalizable with one eigenvalue \(a\ne1\) on a line and eigenvalue 1 on a hyperplane. If only one of \(A,D\) has an exceptional eigenvalue different from 1, or if both have different exceptional eigenvalues, the matching intertwiner condition leaves one side with a missing direction, contradicting conciseness. Thus either both rank-one parts are nilpotent, or \(U=tP\), \(Z=tQ\) for a common nonzero \(t\ne-1\) and two rank-one projections \(P,Q\).

In each case \(U\) and \(Z\) are similar over \(\mathbb F_q\). An intertwining change of basis in one mode identifies the slice space with the centralizer \(W=\{M:UM=MU\}\). It has dimension \(n^2-2n+2\). In the diagonalizable case it is the block-diagonal matrix space on a line and its complementary hyperplane. In the nilpotent case choose \(U=E_{12}\); its Jordan type has one block of size two and \(n-2\) of size one. Summing the matching-block dimensions gives \((n-1)^2+1\). Thus in either case one condition on all \(n\) slices has probability \(q^{-2n^2+2n}\).

There are \((q^n-1)(q^{n-1}-1)/(q-1)\) nonzero rank-one nilpotents. Write them as \(u\phi\) with \(u\ne0\), nonzero \(\phi\) vanishing on \(u\), and divide by the \(q-1\) rescalings of the pair. A nilpotent condition is given by a pair \((U,Z)\), up to simultaneous nonzero scalar. This gives \(a_n\) conditions, each containing \(q-1\) nonidentity effective witnesses. For the diagonalizable conditions choose separately the image line and complementary kernel hyperplane in each mode. The line count is \((q^n-1)/(q-1)\), and the number of complementary hyperplanes is \(q^{n-1}\). The condition \(P M=M Q\) is independent of the choice of \(t\in\mathbb F_q^\times\setminus\{-1\}\). This gives \(b_n\) conditions, with \(q-2\) nonidentity effective witnesses each. Section 4 verifies that no further identifications of these conditions are possible. The nonidentity witnesses in a single condition, together with the identity, form the corresponding additive or multiplicative subgroup described in the theorem.

## 3. Conciseness on each leading fixed space

After the intertwining identification above, the slices are independent uniform matrices in the centralizer \(W\). With \(H=\ker U\) and \(\ell=\operatorname{im}U\), this centralizer contains
\[
W_0=\{M\mid\operatorname{im}M\subset H,\quad M\ell=0\}.
\]
For a nonzero vector \(v\notin\ell\), the map \(M\mapsto Mv\) has rank at least \(n-1\) on \(W\), since already \(W_0 v=H\). For \(v\in\ell\setminus\{0\}\), the rank is at least one because \(I\in W\). There is only one corresponding projective line. The probability that all \(n\) slices have a common nonzero right kernel is consequently at most
\[
q^{-n}+\frac{q^n-1}{q-1}q^{-n(n-1)} .
\]
For the common left kernel use \(W_0\) and the exceptional line \(H^\perp\), giving the same bound. Failure of conciseness in the slice mode is linear dependence of \(n\) independent uniform vectors in \(W\), with probability at most \((q^n-1)q^{-\dim W}\) by a union bound over nonzero coefficient vectors. Thus the conditional probability of conciseness on every leading fixed space is \(1-O_q(q^{-n})\). On all arrays, conciseness has probability \(1-O_q(q^{-n^2+n})\), by testing each of the three possible missing covector lines.

## 4. Overlap of two leading fixed spaces

First take two conditions on the same active pair. Use the intertwining coordinates for the first, so that its equation is \(UM=MU\). In these coordinates the second equation is \(U'M=MZ'\) with \(U',Z'\) rank one. Consider its linear residual on \(W_0=H\otimes\ell^\perp\). If \(U'|_H\ne0\), choose \(x\in H\) with \(U'x\ne0\), and vary \(\phi\in\ell^\perp\) with \(\phi Z'=0\). This gives a residual \((U'x)\phi\) of rank at least \(n-2\) as a linear map of the choices of \(\phi\). If some \(\phi\in\ell^\perp\) has \(\phi Z'\ne0\), fix it and vary \(x\in H\cap\ker U'\); the residual \(-x(\phi Z')\) gives the same bound.

In the remaining case, \(U'\) has kernel \(H\) and \(Z'\) has image \(\ell\). Every \(M\in W\) preserves \(H,\ell\) and acts by the same scalar \(c(M)\) on \(\ell\) and on \(V/H\), because it commutes with the rank-one map \(U\). The new residual on \(W\) is \(c(M)(U'-Z')\). If \(U'\ne Z'\) all common fixed slices kill \(\ell\), so the tensor is nonconcise. If \(U'=Z'\), it is a scalar multiple of \(U\) by its kernel and image. The condition is identical to the first. This proves both the exact identifications used in Section 2 and the extra codimension \(n(n-2)\) for distinct conditions with a concise intersection.

For different active pairs, reorder modes so the first condition is on modes 1 and 2 and the second is on 1 and 3. In the centralizer coordinates for the first, use the subspace
\[
(H\cap\ker U')\otimes\ell^\perp\otimes V_3
\subset W_0\otimes V_3 ,
\]
where \(I+U'\) is the second condition's first mode. On this subspace its operator minus identity is the nonzero rank-one update in the third mode only. The image has dimension at least \((n-2)(n-1)\). Thus the intersection also has the extra codimension \(\Omega(n^2)\) with leading coefficient one. Once summed over all pairs of conditions, of which there are at most \(q^{O_q(n)}\), the intersection contribution among concise tensors is at most \(q^{-3n^2+O_q(n)}\).

## 5. Assemble the asymptotics

There are three choices of the active pair. Summing the leading fixed-space probabilities and subtracting pair intersections bounds their union above and below with difference \(q^{-3n^2+O_q(n)}\), after restricting to concise tensors. The expected number of effective nonidentity witnesses is a sum of their individual probabilities. Their multiplicities within a condition are \(q-1\) and \(q-2\), respectively. The estimates of Section 1 supply at most \(q^{-3n^2+O_q(n)}\) in both calculations from all remaining cases. The leading terms have order \(q^{-2n^2+6n}\) up to positive constants depending only on \(q\), and the restriction to concise tensors changes their factors by \(1+O_q(q^{-n})\) as proved in Section 3. These observations give the two formulas. They also show that almost every exceptional concise tensor satisfies just one leading condition and has no remaining witness, so its effective stabilizer is exactly the indicated group.

## Relation to earlier work

The orbit-counting identity is classical. Fixed-point arguments and constant bounds on average tensor automorphism orders have already been studied in the finite-field tensor setting. The theorem here identifies the leading correction after conditioning on conciseness, including its coefficient and the typical structure of the exceptional effective stabilizer. These results are distinct from average-case algorithms for recovering transporters. Publication priority is unestablished.

[Yinan Li, Random Tensors over Finite Fields](https://www.mittag-leffler.se/seminar/yinan-li-ws1-random-tensors-over-finite-fields-2/) · [Li–Li–Qiao–Tao–Wang, average-case TI](https://arxiv.org/abs/2604.00591).

