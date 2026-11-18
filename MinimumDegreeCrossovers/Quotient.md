# Exponential hardness of minimum faithful degree for central quotients

Fix an odd prime $p$. Write $H_p$ for the Heisenberg group of order $p^3$ and exponent $p$. All input permutations are specified as complete image lists. The quotient input consists of generators of an ambient permutation group $G$, generators of $N\trianglelefteq G$ on the same point set, and a binary bound when applicable. This note gives informal proofs.

**Theorem.** The minimum faithful permutation degree threshold problem for $G/N$ is NP-complete even when $G=H_p^M$ on its minimum-degree action of degree $p^2M$ and $N$ is central. Every displayed ambient orbit has $p^2$ points. Estimating the degree within a two-sided multiplicative factor $p^{D/(10p^2)}$ is NP-hard, where $D=p^2M$ is the ambient permutation degree. In total explicit input length $L$, the resulting hardness factor is $2^{c_p\sqrt{L/\log(2+L)}}$ for a constant $c_p>0$. This scale matches a numerical upper estimator up to a constant in the exponent. In addition,
$$
  \max_{N\le Z(H_p^M)}\mu(H_p^M/N)=p^{M+1}\qquad (M\ge1).
$$
Thus a very simple fixed ambient family already realizes the full complexity of the original Kantor–Luks quotient model and can have exponentially larger optimal quotient actions. The NP-hardness in this proof concerns the degree as a number. In the worst case an explicit optimal action itself would have exponential size in the ambient degree. [Kantor and Luks, Computing in Quotient Groups, §13 Problem 1](https://pages.uoregon.edu/kantor/PAPERS/quotient.pdf#page=9) · [Levet, Srivastava and Thakkar, general NP upper bound](https://arxiv.org/html/2501.16039v4#S1)

## Orbit cost from a scalar commutator

Let $Q$ be a finite group of class at most two and exponent dividing $p$. Set $Z=Z(Q)$ and $V=Q/Z$, using elementary abelian coordinates. The commutator gives an alternating map $\beta:V\times V\to Z$. For every nonzero central functional $\lambda:Z\to\mathbb F_p$, the least size of an orbit with point stabilizer $B$ satisfying $B\cap Z=\ker\lambda$ is
$$
  p^{1+\operatorname{rank}(\lambda\beta)/2}.
$$
Indeed the image of $B$ in $V$ is isotropic for $\lambda\beta$, and $[Q:B]=p[V:BZ/Z]$. An alternating form of rank $2r$ has a maximum isotropic subspace of codimension $r$, by passing to its nonsingular quotient and choosing half of a symplectic basis. This gives the lower bound. For the upper bound use the ordinary class-two exponent-$p$ coordinates
$(v,z)(v',z')=(v+v',z+z'+\beta(v,v')/2)$.
In these coordinates the direct sum of a maximum isotropic subspace with $\ker\lambda$ is a subgroup of the claimed index. The coordinates follow by making the original group law commutative through subtraction of half the commutator, then choosing a linear section of $Q\to V$.

The minimum degree of a faithful action is consequently the minimum total of these costs over bases of $Z^*$. For completeness, every nontrivial normal subgroup of a finite $p$-group meets the center, so an orbit family is faithful exactly when the intersections of its point stabilizers with $Z$ have trivial common intersection. A minimum action uses only stabilizer intersections of codimension one. Codimension zero gives a removable orbit. For codimension $h\ge2$, take two complementary nonzero subspaces of $Z/(B\cap Z)$. Their preimages $Z_1,Z_2$ give subgroups $BZ_1,BZ_2$ whose central intersections meet in $B\cap Z$. Each index is at most $[Q:B]/p$, so replacement by the two new orbits strictly reduces total degree. Here odd $p$ ensures $2/p<1$. The remaining functional lines span $Z^*$ by faithfulness and must be independent by minimality. This uses the independent central marks argument from the bounded-orbit minimum-degree proof. Comparable central-socle descriptions of minimal actions are classical. [Elias, Silberman and Takloo-Bighash, Minimal Permutation Representations of Nilpotent Groups](https://doi.org/10.1080/10586458.2010.10129066)

## Central quotients of one fixed direct-product family

The ambient group $G=H_p^M$ has center $Z(G)=\mathbb F_p^M$ with one coordinate per factor. Its tangent has $M$ symplectic planes and its commutator uses the standard alternating form on plane $j$ into central coordinate $j$. For a code $C\le\mathbb F_p^M$, quotient by $N=C^\perp$ in the center. Put $S=\bigcup_{c\in C}\operatorname{supp}(c)$ and $u=|S|$. The coordinates outside $S$ have lost their central commutator directions and contribute $2(M-u)$ independent central tangent coordinates of the quotient. The active tangent, on the planes indexed by $S$, has no common radical. To see this, a nonzero tangent coordinate in an active plane is detected by some $c\in C$ nonzero on that plane and by testing the commutator against a vector supported there. The remaining center is $W=\mathbb F_p^M/N$, with $W^*=C$.

For a mark on the entire quotient center, let $c\in C$ be its restriction to $W$. The scalar commutator has rank $2\operatorname{wt}(c)$, where $\operatorname{wt}$ denotes Hamming weight. Its least orbit cost is $p^{1+\operatorname{wt}(c)}$. Any basis of all central marks has a subset projecting to a basis of $C$, and the remaining $2(M-u)$ costs are at least $p$. The lower bound is attained by lifting a minimum-cost basis of $C$ and taking the coordinate characters on the inactive tangent. Hence the exact formula is
$$
 \mu(G/N)=2p(M-u)+\min_{\mathcal B\text{ basis of }C}\sum_{c\in\mathcal B}p^{1+\operatorname{wt}(c)} .
$$
This gives a concrete identification of the permutation degree with a weighted basis problem for linear codes. For the ambient group $C=\mathbb F_p^M$, the coordinate basis gives $\mu(G)=p^2M$, since every nonzero mark has weight at least one.

There is a direct explicit presentation at this optimum. Realize each $H_p$ by upper unitriangular $3\times 3$ matrices, acting on affine column vectors $(u,v,1)^\mathsf{T}$. The action is transitive on $p^2$ points and each element is recovered from its affine map, so it is faithful. Use their disjoint union and the two standard noncentral generators per factor. Their commutator generates the central translations on that factor. Gaussian elimination computes a basis of $C^\perp$, and each basis vector gives one central translation on the union. Thus the input generators of both $G$ and $N$ are polynomial-size arrays, with bit length $O_p(M^2\log(2M))$, even though the quotient group may have exponentially many elements.

## An elementary reduction from exact cover

Reduce from Exact Cover by 3-Sets. Write $m=3r$ for the number of items, with $r\ge1$, $n$ for the number of sets, and $A\in\{0,1\}^{m\times n}$ for the incidence matrix. Write $\operatorname{rep}(y)$ for the vector obtained by repeating each coordinate of $y$ exactly $r+1$ times. Consider words
$$
     (x,\operatorname{rep}(Ax-\mathbf 1)),\qquad x\in\mathbb F_p^n .
$$
Such a word has weight at most $r$ exactly when its support selects an exact cover with coefficient one on each selected set. A nonzero syndrome coordinate alone costs $r+1$, so a word of weight at most $r$ has $Ax=\mathbf1$. Every item lies in at least one selected set. The at most $r$ chosen triples thus cover all $3r$ items and must be disjoint. The equation now forces each selected coefficient to be one. Conversely the incidence vector of an exact cover gives a word of weight exactly $r$. This argument avoids any concern about modular cancellation within overlapping triples. [Garey and Johnson, Computers and Intractability, problem SP2](https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf)

For a replication parameter $t$, form the linear code
$$
 C=\left\{ \bigl(x_i,\operatorname{rep}(Ax_i-c\mathbf1)\bigr)_{i=1}^t :
     x_i\in\mathbb F_p^n,\ c\in\mathbb F_p\right\}
 \le\mathbb F_p^{\,M},\qquad M=t(n+m(r+1)).
$$
The vector $c$ is a shared scalar, while the $x_i$ are independent. These parameters determine distinct words since the original $x_i$ are carried explicitly and $\mathbf1\ne0$. Thus $\dim C=tn+1$, and $c=0$ defines a hyperplane $C_0$. The code has full support. A variable $x_i$ reaches its own original coordinate, and $c=1,x_i=0$ reaches every syndrome coordinate. The hyperplane $C_0$ has the basis of words obtained by turning on one variable at a time. Each such word has weight $1+3(r+1)$, since its incidence column has exactly three ones.

Any code basis needs a word with $c\ne0$. Scaling makes $c=1$ without changing its weight, and the minimum weight in that affine coset is the sum of the separate minima in the $t$ blocks. In the yes case append a weight-$tr$ word to the displayed $C_0$ basis. In the no case each word with $c\ne0$ has weight at least $t(r+1)$. The group formula gives
$$
 \begin{aligned}
 \text{yes: }\quad\mu(G/N)&\le tn\,p^{3r+5}+p^{tr+1},\\
 \text{no: }\quad\mu(G/N)&\ge p^{t(r+1)+1}.
 \end{aligned}
$$
For polynomially large $t$ the yes bound is at most $2p^{tr+1}$. In particular one can choose $t$ so $t\ge 10(B+1)^2$, where $B$ is the explicit source input length. This ensures $tn\le p^{(t-3)r-4}$. Thus the two cases differ by a factor at least $p^t/2$. The binary threshold $2p^{tr+1}$ has polynomial bit length and gives exact NP-hardness, which combines with the published general NP upper bound.

For the approximation assertion choose $t=10(B+1)^a$ for a sufficiently large fixed integer $a$. The number of coordinates satisfies $M=O(tB^2)$. The complete written length satisfies $L=O_p(t^2B^4\log(tB))$, including the subgroup generators. For a given $\varepsilon>0$, taking $a>1/\varepsilon$ gives $L^{1/2-\varepsilon}=o(t)$ as $B\to\infty$. For a given $\eta>0$, taking $a>2/\eta$ gives $D^{1-\eta}=o(t)$. Bounded source sizes can be handled directly, or $t$ increased by a fixed factor. Therefore even estimates with two-sided factor $2^{L^{1/2-\varepsilon}}$, or with two-sided factor $2^{D^{1-\eta}}$, distinguish the cases. The gap exceeds the square of each claimed factor, so the reduction also handles algorithms reporting approximate values without outputting actions. The threshold separating the two estimate ranges can be computed, for example by a binary power of $p$ in the middle of the gap.

## Exponential approximation hardness with the optimal input-length scale

For the stronger quantitative bound, use Håstad's hardness for Max-E3-Lin over the additive group of $\mathbb F_p$. At fixed odd $p$, it is NP-hard to distinguish systems in which at most $1/8$ of the equations need be violated from systems in which at least $1/2$ must be violated. These constants follow from completeness $1-\delta$ and soundness $1/p+\delta$, taking any sufficiently small fixed $\delta$. Use an explicit list of unweighted equations, permitting repetitions. Rational weights, if used, can be normalized to total weight one and rounded to integer multiplicities with common denominator polynomial in the number of equations. The total variation error can be made smaller than any fixed chosen slack in the two bounds. [Håstad, Some Optimal Inapproximability Results, Theorem 5.9](https://people.kth.se/~johanh/optimalinap.pdf)

Repeat the equation list if necessary so its length is at least eight, and append the always-false equation $0=1$. In the resulting system $Ax=b$ with $m\ge9$ rows, $b\notin\operatorname{im}(A)$. In the yes case a solution candidate violates at most $m/4$ rows, and in the no case every candidate violates at least $m/2$ rows. Every original row has a nonzero coefficient or a nonzero right hand side, and the appended row has a nonzero right hand side.

Use eight blocks with one common scalar $c$, each having its own $x_i$, to form
$$
 C=\{(Ax_1-cb,\ldots,Ax_8-cb):x_i\in\mathbb F_p^n,\ c\in\mathbb F_p\}\le\mathbb F_p^{\,M},
 \qquad M=8m.
$$
The scalar $c$ is uniquely determined by the word because $b\notin\operatorname{im}(A)$. The code has full support by the row condition. The words with $c=0$ form a hyperplane, the direct sum of eight copies of $\operatorname{im}(A)$, and this hyperplane has a basis of at most $8m$ words each supported on one block and of weight at most $m$. In the yes case one can extend this basis with a $c=1$ word of weight at most $2m$. In the no case every $c\ne0$ word has weight at least $4m$, since scaling to $c=1$ preserves weight. Therefore
$$
 \begin{aligned}
 \text{yes: }\quad \mu(H_p^M/C^\perp)&\le 8m\,p^{m+1}+p^{2m+1}\le 2p^{2m+1},\\
 \text{no: }\quad \mu(H_p^M/C^\perp)&\ge p^{4m+1}.
 \end{aligned}
$$
The last yes inequality uses $8m\le p^m$ for $m\ge9$ and $p\ge3$. An approximation factor $p^{M/10}=p^{0.8m}$, allowed in either direction, still separates the two cases by comparison to $p^{3m+1}$. This proves the claimed factor as a function of $D=p^2M$.

In the specified encoding each of the $2M$ ambient generators is a full permutation list, and the at most $M$ subgroup generators have the same format. Including the binary threshold, the written length is $L=\Theta_p(M^2\log(2M))$ on these instances. Consequently there is a constant $c_p>0$ such that $2^{c_p\sqrt{L/\log(2+L)}}\le p^{M/10}$ throughout the reduction.

## Matching exponent for the explicit input length

For context, a trivial numerical upper estimator for all class-two exponent-$p$ quotient inputs has approximation factor $2^{O_p(\sqrt{L/\log(2+L)})}$. Suppose $G$ is represented on $D$ points by $g$ generators, and $G/N=Q$ is nontrivial. Set $k=\min(g,\lfloor D/(p-1)\rfloor)$. Since $|G|$ divides $D!$, one has $\log_p|G|\le D/(p-1)$. The tangent $Q/Z(Q)$ is elementary abelian generated by at most $g$ images, so its dimension is at most $k$. By the orbit cost bound, $\mu(Q)\le \lfloor D/(p-1)\rfloor p^{1+\lfloor k/2\rfloor}$. Return that bound as the estimate, or return zero for the trivial quotient after testing whether all ambient generators lie in $N$. The complete permutation format gives $L\ge gD\log_2 D$ for $D\ge2$. If $D\ge L^{1/4}$, then $k\le\sqrt{gD/(p-1)}=O_p(\sqrt{L/\log(2+L)})$. If $D<L^{1/4}$, the bound $k\le D/(p-1)$ gives the same conclusion. The prefactor $D/(p-1)$ costs only $O(\log L)$ bits in the log of the estimate. The hardness thus matches the exponent scale attainable by an upper estimator under the complete-image-list convention. It concerns numerical estimates, since an action can exceed the input size.

## Exact largest quotient degree in the direct-power family

In the formula for $H_p^M/N$, let $s=\dim C$ and $u=|S|$. If $s>0$, use the active coordinates and a systematic basis of $C$. Every basis vector in this basis has weight at most $u-s+1$. Its cost gives
$$
 \mu(H_p^M/N)\le 2p(M-u)+s\,p^{u-s+2}
               \le 2p(M-u)+p^{u+1}
               \le p^{M+1}.
$$
The second inequality uses $s\le p^{s-1}$. For the third, each increase of an exponent from $j+1$ to $j+2$ adds at least $2p$ for $p\ge3$. If $s=0$, the quotient is elementary abelian of rank $2M$, of minimum degree $2pM\le p^{M+1}$. The one-dimensional repetition code spanned by $\mathbf1$ has $u=M$ and its single mark has weight $M$. The formula gives exactly $p^{M+1}$. The quotient in this equality case is the extraspecial exponent-$p$ group obtained by identifying the central factors. The classical quotient blowup phenomenon already appears in Kantor and Luks's introduction via Neumann's extraspecial example. The bounds here give the exact maximum over all central quotients of this fixed direct-power family and a separate near-exponential hardness result for the quotient input model. [Kantor and Luks, introduction](https://pages.uoregon.edu/kantor/PAPERS/quotient.pdf#page=1)


## The same quotient family has exactly the code-equivalence isomorphism problem

For two linear codes $C\le\mathbb F_p^M$ and $C'\le\mathbb F_p^{M'}$, write $Q_C$ and $Q_{C'}$ for their Heisenberg-power quotients. They are abstractly isomorphic exactly when the codes are monomially equivalent. Moreover an isomorphism of the quotients induces a change of basis on the derived group that occurs in a monomial equivalence, and every such monomial equivalence lifts to an isomorphism. In the displayed minimum-degree affine actions the monomial equivalence also gives simultaneous conjugacy of the ambient pair $G,N$.

Let $z_i$ be the image of the $i$-th coordinate generator of the ambient center in the derived group $W=\mathbb F_p^M/C^\perp$ of the quotient. The vectors $z_i$ are the column vectors of a generator matrix for $C$ in any chosen dual coordinate chart on $W$. The inactive coordinates are exactly the indices with $z_i=0$. Their number is determined by $\dim Z(Q_C)-\dim W=2(M-u)$, while the number of active indices is determined by $\dim(Q_C/Z(Q_C))=2u$. In particular the quotient determines $M$. In the active tangent planes the scalar commutator has the block diagonal matrix whose $i$-th block is the standard symplectic $2\times 2$ matrix multiplied by $\lambda(z_i)$. Its determinant, as a polynomial in indeterminate coordinates of $\lambda\in W^*$, is
$$
                 \prod_{i:z_i\ne0}\lambda(z_i)^2 .
$$
Here the polynomial is used formally, so the argument does not require that the base field contain enough points to distinguish all polynomials by evaluation. An isomorphism induces a change of basis on $W$ and a congruence on the tangent. The determinant therefore agrees up to the nonzero square of a tangent basis determinant. Unique factorization of linear polynomials implies that the multisets of active projective columns correspond under the induced map on $W$, including all multiplicities. Reinsert the known number of zero columns. Matching columns projectively is exactly monomial equivalence of the row-space codes.

Conversely, such a matching gives a $\psi:W\to W'$ and pairs indices with $\psi(z_i)=a_i z'_{\pi(i)}$ for some $a_i\ne0$. On the matched tangent planes use a two-by-two map of determinant $a_i$, and on the inactive central tangent choose any bijection. Together these maps preserve the bracket because the standard symplectic form on a plane scales by the determinant of its map. They define a quotient group isomorphism by class-two exponent-$p$ coordinates. The corresponding scaling of each ambient central coordinate is realized in the affine model by conjugation by $(u,v)\mapsto(a_i u,v)$. Permuting the orbit blocks then gives one ambient permutation conjugating both $G$ and the subgroups $C^\perp,(C')^\perp$. Any simultaneous conjugacy of ambient pairs in turn induces a quotient isomorphism. Therefore the same quotient input family realizes monomial code equivalence under both interpretations, while its optimum faithful permutation degree has the exponential approximation hardness proved above. [Grochow and Qiao, On p-Group Isomorphism: Search-To-Decision](https://drops.dagstuhl.de/opus/volltexte/2021/14290/pdf/LIPIcs-CCC-2021-16.pdf)

## Binary extension with an ambient power of D₈

The corresponding theorem holds for central quotients of $D_8^M$, supplied in its minimum-degree action on $4M$ points, with four-point orbits. Here $\mu(D_8^M/N)$ has the same Hamming-weight formula at $p=2$. The degree decision is NP-complete, and a two-sided factor $2^{M/10}$ is NP-hard. The exact largest degree is $2^{M+1}$. Monomial code equivalence here specializes to binary coordinate-permutation equivalence.

Use the binary law of [the cross commutator construction](PrimeHardness.md), with independent one-dimensional left and right slots in each factor and central quotient $N=C^\perp$. A central functional with component $c\in C$ on the derived group gives the scalar square form $\sum_i c_i x_i y_i$ on the active tangent. The polarized alternating matrix has rank $2\operatorname{wt}(c)$. As before any point stabilizer for this mark projects to an isotropic subspace for the polarization, so its index is at least $2^{1+\operatorname{wt}(c)}$. That bound is attainable. In the quotient by the kernel of the mark the cocycle vanishes on the tangent subspace retaining all left coordinates and the right coordinates at indices where $c_i=0$. With the inactive central tangent split off, the preimage of this tangent subspace is elementary abelian and has a complement to the central line. Lifting that complement yields the desired stabilizer. For a mark nonzero only on the inactive center, the same construction uses the full active tangent and produces index two. The independent-mark proof applies at $p=2$ by selecting a minimum action with the maximum number of orbits, so the cost formula follows as above.

The elementary exact-cover gap then works verbatim, giving NP-hardness of threshold testing with the general NP upper bound. For the exponential gap use Håstad's binary completeness and soundness with $\delta=1/16$, repeating the equation list to at least sixteen rows before appending $0=1$. After the addition the fraction violated is at most $1/8$ in the positive case and at least $3/8$ in the negative case. With sixteen blocks sharing $c$, the basis of the hyperplane $c=0$ has at most $16m$ vectors of weight at most $m$. A $c=1$ word can have weight at most $2m$ in the positive case and must have weight at least $6m$ in the negative case. Thus $\mu_{\rm yes}\le 2\cdot 2^{2m+1}$ and $\mu_{\rm no}\ge 2^{6m+1}$. Since $M=16m$, approximation within $2^{M/10}$ in either direction separates them at $2^{4m+1}$. This gives the same order of inapproximability in complete-image-list bit length. The exact maximum proof still applies using $s\le 2^{s-1}$ and $4M\le2^{M+1}$ for $M\ge1$. It also gives a numerical estimator of the matching exponent scale on this family. The lower bound on the written length follows since the minimum number of ambient generators is $2M$.

The determinant of the polarized commutator still recovers the multiset of active projective columns over $\mathbb F_2$. Its factors are used as formal polynomials and unique factorization applies. The resulting permutation of the matched planes preserves their binary square forms too. The correspondence preserves the cocycle presentation directly, and permuting blocks in the displayed ambient action simultaneously conjugates the pair. This proves the binary isomorphism assertion.
