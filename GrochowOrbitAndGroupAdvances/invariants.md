# Two nonisomorphic real orthogonal groups with the same orbit Gram graph

Mixon and Vose's Conjecture 2.7 is false. Two nonisomorphic groups of order \(3\cdot 2^{34}\) have faithful orthogonal representations on the same \(\mathbb R^{72}\) whose orbit Gram graphs are isomorphic for every common seed. This is an informal proof. [Mixon–Vose, Conjecture 2.7](https://arxiv.org/html/2411.17434#S2)

## Nine projective points

Write \(\mathbb F_4=\mathbb F_2(\omega)\) with \(\omega^2+\omega+1=0\), conjugation \(\bar t=t^2\), and \(^{*}\) for conjugate transpose. In \(U=\mathbb F_4^4\), use the projective points represented by
\[
 S=\{e_1,e_2,e_3,e_4,\ e_1+\omega e_2,\ e_3+\omega e_2,\ e_3+e_4,\ e_4+e_1,\ p\},
 \qquad p=e_1+e_2+e_3+e_4 .
\]
Put \(W=\operatorname{span}_{\mathbb F_2}\{vv^*:[v]\in S\}\). Since every nonzero scalar has norm one, \(vv^*\) depends only on the point. Every rank-one Hermitian matrix is of this form: write it as \(uw^*\), use Hermitian symmetry to see that \(w\) is proportional to \(u\), and use that the only nonzero scalar fixed by conjugation is \(1\).

The rank-one matrices in \(W\) give exactly \(S\). For \(uu^*\in W\), entries \(13\) and \(24\) both equal the coefficient \(\lambda\in\mathbb F_2\) of \(pp^*\), since the other generators have off-diagonal entries only on the four cycle edges \(12,23,34,41\). If \(\lambda=0\), the support of \(u\) is a clique in that cycle and has size at most two. Singleton support gives a basis point. On an edge, the nonzero off-diagonal entry must match that of the unique edge generator, which fixes the ratio of the nonzero coordinates and gives the marked point. If \(\lambda=1\), the equations \(u_1\bar u_3=u_2\bar u_4=1\) imply \(u_1=u_3\ne0\) and \(u_2=u_4\ne0\). At position \(34\), the two possible contributions from \(pp^*\) and the edge term are both \(1\). Thus the nonzero entry \(u_3\bar u_4\) is \(1\), so all coordinates are equal and the point is \(p\).

There is no invertible semilinear stabilizer of \(S\) with companion automorphism \(t\mapsto\bar t\). The only projective lines containing three or more marked points are the four cycle-edge lines. Indeed, a combination of vectors supported on two distinct adjacent edges has support of size three or, after cancellation, support on the nonedge joining their remaining endpoints. A combination of vectors supported on opposite edges has size-four support, but cannot give \(p\) since one edge in each opposite pair has unequal coordinates. Combining a basis vector with an edge point off that basis vector's incident edges has support of size three. A line through \(p\) and two other marked points would require two disjoint edge supports to span \(p\), which was excluded.

The basis points are exactly those on two of the lines with at least three marked points, and \(p\) is the sole marked point on none. A semilinear stabilizer must therefore permute the basis points and fix \(p\). Its linear part is a permutation matrix times a global scalar because the coordinates of \(p\) are all \(1\). It must preserve the two edges with unequal marked coordinate ratios as a set, so it fixes their common basis point \(e_2\). Both marked points have ratio \(\omega\) of their \(e_2\) coefficient to the other coefficient. Applying the nontrivial field automorphism changes that ratio to \(\omega^2\), which is absent. Consequently \(S\) and its conjugate \(\bar S\) are not linearly projectively equivalent.

## The two groups

Use the unit quaternion group \(Q_8=\{\pm1,\pm i,\pm j,\pm k\}\) and identify its quotient by \(\{\pm1\}\) with the additive group of \(\mathbb F_4\), by \(i\mapsto1,\ j\mapsto\omega,\ k\mapsto\omega^2\). The order-three unit quaternion \(s=-(1+i+j+k)/2\) conjugates \(i\) to \(j\), \(j\) to \(k\), and \(k\) to \(i\). Thus \(Q_8\langle s\rangle\) is the binary tetrahedral group, and conjugation by \(s\) induces multiplication by \(\omega\) on the quotient.

Let \(C\) be the image of \(U\to\mathbb F_4^9\), \(x\mapsto(v^*x)_{[v]\in S}\), using the listed representatives. This map is injective because the list contains the basis. Let \(N\) be the inverse image of \(C\) under \(Q_8^9\to\mathbb F_4^9\). Conjugation by \(s_{\rm diag}=(s,\ldots,s)\) gives an automorphism \(\theta\) of \(N\), since it multiplies all quotient coordinates by \(\omega\). The center \(Z(N)\) is \(\{\pm1\}^9\): projection onto every \(Q_8\) is surjective because each \(v^*x\) is surjective and \(N\) contains the full ambient center. Hence \(N/Z(N)=U\) via the evaluation map, and \(|N|=2^9\cdot4^4\).

Put \(B=N\rtimes\langle s_{\rm diag}\rangle\), with quotient \(q:B\to\mathbb Z/3\mathbb Z\). Inside \(B\times B\) take
\[
 G=\{(a,b):q(a)=q(b)\},\qquad H=\{(a,b):q(a)=-q(b)\}.
\]
In each group \(N\times N\) is the unique Sylow \(2\)-subgroup. The action of a quotient generator is respectively \((\theta,\theta)\) and \((\theta,\theta^{-1})\).

## Nonisomorphism from the square maps

The square of an element of \(Q_8\) is \(-1\) exactly when its image in the additive quotient is nonzero. Thus the square map of \(N\), from \(U=N/Z(N)\) to \(Z(N)\), has binary coordinates \(x\mapsto(x^*vv^*x)_{[v]\in S}\). It is well-defined since central elements have square \(1\). Composing it with all binary linear functionals on the center gives the intrinsic space of quadratic forms \(x\mapsto x^*M x\) for \(M\in W\). Its polar form is \((x,y)\mapsto\operatorname{Tr}_{4/2}(x^*M y)\), with radical \(\ker M\) by nondegeneracy of the trace pairing. In particular the association of Hermitian matrices to quadratic forms is injective, and the polar rank is twice the Hermitian rank. The same statements apply to \(N\times N\) with block diagonal matrices.

An isomorphism \(G\to H\) would induce a binary linear map on the quotients of their unique Sylow \(2\)-subgroups by their centers. It would identify their order-three quotient generators up to \(\varepsilon\in\{1,-1\}\). Since inner automorphisms of \(N\times N\) act trivially modulo the center, the binary linear map intertwines uniform multiplication by \(\omega\) on the source with \((\omega^\varepsilon,\omega^{-\varepsilon})\) on the target. Conjugate the field coordinates in whichever target block has action by \(\omega^{-1}\). Then the map commutes with multiplication by \(\omega\) and is therefore \(\mathbb F_4\)-linear. Preservation of the square-map space gives a congruence of the block diagonal Hermitian spaces \(W\oplus W\) and \(W\oplus\bar W\), after ordering the target blocks.

Pullback by an invertible linear map \(T\) sends \(vv^*\) to \((T^*v)(T^*v)^*\). The rank-one locus in either block diagonal space lies in exactly one summand. The hypothesized congruence consequently induces a linear projective equivalence of the union of two copies of \(S\) on complementary summands with the analogous union of \(S\) and \(\bar S\). The two summands' point configurations are precisely the connected components of the linear matroid, where points are connected by chains of minimal dependent sets. A minimal dependent set cannot cross the direct sum. In each summand the four basis points together with \(p\) form one minimal dependent set, and every edge point lies in a minimal dependent triple with its two endpoints. The equivalence must therefore take a copy of \(S\) to \(\bar S\), which is impossible. This proves \(G\not\cong H\).

## Matching Gram graphs

Both groups act faithfully and orthogonally on \(\mathbb H^{18}=\mathbb R^{72}\) by left multiplication in each coordinate. The set map \(G\to H\), \((a,b)\mapsto(a,b^{-1})\), is a bijection. For units \(u,v\) in a coordinate and any seed coordinate \(x\),
\[
 \langle ux,vx\rangle=|x|^2\operatorname{Re}(\bar u v)
 =|x|^2\operatorname{Re}(u\bar v)
 =\langle u^{-1}x,v^{-1}x\rangle .
\]
The middle equality follows from symmetry of the real Euclidean inner product on the quaternions. Summing gives equality of Gram matrices under the bijection on group labels. When all seed coordinates are nonzero, both orbit labellings are bijective. With zero coordinates, the correspondence still descends to the orbit sets because equality of points is detected by zero squared distance in the Gram matrix. Generic free seeds can be chosen in the intersection of both generic loci and the open set where every coordinate is nonzero.

Mixon and Vose's two-orbit theorem now gives the sharp worst-case number of generic real orbits for abstract recovery, namely two when the data include cross-orbit inner products. The same example rules out universal recovery of the regular permutation action from a single generic orbit. [Mixon–Vose, Theorem 2.12 and §4](https://arxiv.org/html/2411.17434#S2)
