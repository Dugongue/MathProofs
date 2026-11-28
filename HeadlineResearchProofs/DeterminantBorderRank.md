# The exact border partition rank of the determinant

Let \(\det_n\) be the determinant with its \(n\) columns as the variable blocks, over an arbitrary field \(K\). Define geometric border partition rank by taking the Zariski closure of each bounded-rank locus over an algebraic closure of \(K\). Then, for \(n\ge2\),

\[
\underline{\operatorname{prk}}(\det_n)=\operatorname{prk}(\det_n)=
\begin{cases}
n,&n\text{ odd or }n=2,\\
n-1,&n\text{ even and }n\ge4.
\end{cases}
\]

For even \(n\ge4\), every layout that attains this border rank is the star of splits isolating \(\{i,j\}\) for one fixed column \(i\) and all \(j\ne i\), with the three unordered splits for \(n=4\) admitting any center. A layout specifies the variable blocks in each factor. The theorem concerns the splits in the generic decomposition along the degeneration, even when its coefficients have poles.

The argument is a specialization statement for Chow obstructions. It also proves that the homogeneous border strength of a prime-size determinant equals its size. Here strength counts arbitrary products of positive-degree homogeneous factors whose degrees add to the degree of the determinant, without imposing column multidegrees.

## A Chow obstruction that survives coefficient degeneration

Let \(R\) be a discrete valuation ring with fraction field \(L\) and residue field \(k\). Let \(X_R\) be a product of projective spaces over \(R\). Suppose \(T\) is a section of an invertible sheaf on \(X_R\) and its special fiber \(T_k\) is nonzero. Assume there is a generic identity

\[
T_L=\sum_{j=1}^{r} F_jG_j
\]

where \(F_j\) is a section of a fixed multidegree line bundle \(M_j\) on \(X_L\) and \(G_j\) is a section of the complementary line bundle. Each \(M_j\) is defined over \(R\) by the multidegree. Put \(E_R=\bigoplus_j M_j\). Then

\[
c_r(E_k)\Big|_{X_k\setminus V(T_k)}=0
\quad\text{in }\operatorname{CH}^{r}(X_k\setminus V(T_k)).
\tag{1}
\]

Indeed, on \(X_L\setminus V(T_L)\) the section \((F_1,\ldots,F_r)\) of \(E_L\) is nowhere zero. This yields a trivial line subbundle and implies vanishing of the top Chern class there. Chow localization now represents \(c_r(E_L)\cap[X_L]\) by an integer combination of cycles supported on \(V(T_L)\), whether or not the common-zero scheme of the \(F_j\) has excess dimension.

To see directly that these supporting cycles specialize as required, write \(D=\dim(X_L)\). Take the schematic closure of each integral \((D-r)\)-dimensional cycle component in \(X_R\). This closure is integral, dominant over \(R\), proper, and flat over \(R\) because multiplication by any nonzero element of \(R\) is injective on its coordinate rings. Its special fiber is contained in \(V(T_k)\) because the total family \(V(T)\) is closed. Take the fundamental cycle of its special fiber in dimension \(D-r\), including its scheme multiplicities. The class of this cycle has the same coefficients in the standard Chow basis of the product of projective spaces as the class on the generic fiber. In detail, for each positive integral polarization \(\mathcal O(a_1,\ldots,a_s)\), the top intersection of the polarization with the cycle is the leading Hilbert polynomial coefficient times \((D-r)!\). Proper flatness preserves that Hilbert polynomial. The resulting polynomial in \((a_1,\ldots,a_s)\) determines all mixed intersection degrees, so the two classes agree in the monomial bases of their Chow groups. Embedded components of smaller dimension have no effect on these top coefficients. This is also the usual specialization of Chow cycles over a discrete valuation ring. [Fulton, *Intersection Theory*, §20.3](https://link.springer.com/book/10.1007/978-1-4612-1700-8).

Apply this to the linear combination representing \(c_r(E_L)\cap[X_L]\). The Chern class is the same product of multidegree linear forms in the hyperplane classes in both fibers. The specialized combination represents it and is supported in \(V(T_k)\). Localization on the special fiber gives (1). No assumption about the characteristic is used, and the argument does not require extending the individual factor sections over \(R\).

## From border membership to a discrete valuation ring

Work over an algebraically closed field \(k\) and fix a layout. The map from the affine coefficient space of its factors to the space of tensors is polynomial, so its image is constructible and contains a dense open subset of its irreducible closure. If a tensor lies in the closure but outside this open subset, take an integral curve through it whose generic point lies in the open subset. For clarity, Noether normalization gives a finite map from the affine closure to affine space. Take a line through the image of the tensor that is not contained in the image of the complement of the dense open. The inverse image has a one-dimensional component through the tensor by the dimension theorem for cutting by hyperplanes, and this component has the required generic point. Normalize this curve and choose a point over the tensor. Over a finite extension of the function field, the generic tensor admits factors for the chosen layout, since its fiber in the coefficient space is nonempty over an algebraic closure. Normalize again in that finite extension and take a local ring above the chosen point. This gives a DVR with residue field \(k\), an integral tensor family specializing to the original tensor, and the required generic decomposition. The case where the tensor is already in the image uses a constant family. Only finitely many layouts occur for a given rank bound, so membership in the overall closure implies membership in the closure for at least one layout.

## Applying the obstruction to the determinant

For a column layout, use \(X=(\mathbb P^{n-1})^n\) and \(M_j=\bigotimes_{i\in I_j}\mathcal O_i(1)\). The complement of the determinant hypersurface is the variety of \(n\) ordered independent lines. Mapping an independent sequence to the complete flag given by its successive spans is a tower of affine-space bundles: after the preceding lines have been chosen, lifting the next graded line is choosing a splitting of a vector bundle extension. The Chow ring is therefore the complete flag Chow ring \(\mathbb Z[x_1,\ldots,x_n]/(e_1,\ldots,e_n)\), with \(x_i\) the Chern class of the dual of the \(i\)-th chosen line. Applying (1) gives the same class obstruction as for ordinary decomposition:

\[
\prod_{j=1}^r\biggl(\sum_{i\in I_j}x_i\biggr)=0
\quad\text{in }\mathbb Z[x_1,\ldots,x_n]/(e_1,\ldots,e_n).
\tag{2}
\]

Here is the numerical test for (2), included to account for all parities. For any placement of all complex \(n\)-th roots of unity \(\alpha_i\), the map \(x_i\mapsto t\alpha_i\) into \(\mathbb C[t]/(t^n)\) kills the elementary symmetric relations. For \(r<n\), (2) therefore means that in every placement at least one \(I_j\) has zero sum. For a uniformly random placement, a fixed subset of size \(s=1\) or \(n-1\) has no chance to sum to zero. For \(2\le s\le n-2\), double count the swaps between zero-sum and nonzero-sum \(s\)-subsets of the roots. Every zero-sum subset has \(s(n-s)\) such neighbors. A nonzero-sum subset with sum \(z\) has at most two swaps back, because the circle and its translate by \(z\) intersect at at most two points. If \(n\) is odd it has at most one. Indeed the two possible ordered pairs with difference \(z\) are related by \((b,a)\mapsto(-a,-b)\), and both cannot consist of odd-order roots. Thus the probability is at most \(2/(s(n-s)+2)\le1/(n-1)\) for even \(n\), and at most \(1/(s(n-s)+1)\le1/(2n-3)\) for odd \(n\ge5\). For \(n=2,3\) all proper subsets have nonzero sum. The union bound now gives impossibility for \(r\le n-2\) when \(n\) is even, and for \(r\le n-1\) when \(n\) is odd or \(n=2\). The ordinary Laplace and Pfaffian expansions give matching border upper bounds. [Portfolio proof of the ordinary Chow obstruction](https://github.com/Dugongue/MathProofs/blob/main/GrochowOpenProblemSolutions2/DETERMINANT-PARTITION-RANK.md) · [Krishnan–Moshkovitz, exact ordinary rank](https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf).

For \(r=n-1\) and even \(n\), equality forces each subset to have size \(2\) or \(n-2\) and forces the zero-sum events to be pairwise disjoint. After taking pair sides, two disjoint edges can be assigned opposite root pairs simultaneously and thus cannot occur. Distinct pairwise intersecting edges form a star or a triangle, with the triangle available only for \(n=4\), when it corresponds to the same unordered splits by complementation. This proves the layout claim. [Optimal factor rigidity](DeterminantPfaffianRigidity.md).

## Prime-size homogeneous border strength

For homogeneous strength, take the single projective space \(X=\mathbb P(\operatorname{Mat}_{p})\) for a prime size \(p\), with selected factor degrees \(d_j\) satisfying \(1\le d_j\le p-1\). Criterion (1) forces \((\prod_j d_j)h^r=0\) in the Chow ring of the invertible-matrix locus \(\mathrm{PGL}_p\), with \(h\) the hyperplane class. As in Chen and Zhao's ordinary strength proof, this ring is \(\mathbb Z[h]/(ph,h^p)\). For \(r<p\) the class \(h^r\) is nonzero and multiplication by \(\prod_j d_j\) cannot kill it. Laplace gives the matching upper bound, so \(\underline{\operatorname{str}}(\det_p)=p\). [Chen–Zhao, Chow ring and ordinary strength](https://arxiv.org/html/2607.21015v1#S4).

## The quartic determinant and the permanent

The quartic determinant also retains exact homogeneous strength under degeneration, \(\underline{\operatorname{str}}(\det_4)=3\). Suppose its formal generic deformation had strength at most two. The common zero locus of all factors in \(\mathbb P^{15}_L\) has a component of dimension at least 11 by the projective dimension theorem, and every first partial derivative of the generic polynomial vanishes there by the product rule. At least one nonzero factor has degree at most two. Scale that individual factor by a power of the uniformizer to give it coefficients in \(R\), at least one of them a unit. The closure of the selected component has a special fiber contained both in the locus where the partial derivatives of \(\det_4\) vanish and in the zero locus of the nonzero limiting factor. As in the specialization proof above, projective flatness preserves its dimension. The first locus is the irreducible 11-dimensional projective variety of matrices of rank at most two. Thus the limiting factor vanishes on that entire locus. Its ideal is generated by the cubic minors and has no nonzero elements of degree at most two. This contradicts the choice of a primitive factor. The even Pfaffian formula supplies the upper bound three. The argument specializes the singular-locus method of Chen–Zhao's Lemma 6.2.

For \(n\ge2\) and characteristic different from two, Xie's codimension theorem gives \(\underline{\operatorname{str}}(\operatorname{per}_n)=n\). If a generic deformation had a strength decomposition of length \(r<n\), all its \(2r\) factors would have a common-zero component in \(\mathbb P^{n^2-1}_L\) of dimension at least \(n^2-1-2r\). Its closure would specialize to that dimension inside the projective critical locus of the permanent, whose dimension is \(n^2-1-2n\) when nonempty. The same argument rules it out when the critical locus is empty. Laplace expansion by permanental minors gives the upper bound. [Xie, codimension of the permanent's critical locus](https://arxiv.org/abs/2609.27320).

The ordinary rank theorem alone does not give the border result: bounded partition-rank loci can fail to be closed. The method here transfers a particular intersection-theoretic obstruction through limits. [Baily–Danelon, nonclosed partition-rank loci](https://arxiv.org/abs/2610.28792).
