# All minimal ordinary decompositions of the squarefree cubic

## GP-0216

Let $k$ be any field of characteristic different from two and define $T\in(k^3)^{\otimes3}$ as the sum of the six words in which each of $e_1,e_2,e_3$ occurs once. The ordinary rank is four. Every minimal decomposition, considered as an unordered list of rank-one summand tensors, is
$$
T=\frac1{4abc}\sum_{s,t\in\{1,-1\}} st\,
   (ae_1+sbe_2+tce_3)^{\otimes3},
\qquad a,b,c\in k^\times .
$$
Thus over $\mathbb C$ the parameter space of decompositions is the two-dimensional torus of ratios $b/a,c/a$, with the two independent sign changes identified. In particular there is one orbit under the simultaneous diagonal stabilizer, acting by $D^{\otimes3}/\det D$ on summand tensors. The four-term upper bound is the cubic permanent identity. The additional claim is exhaustion of arbitrary ordinary decompositions. [Ilten and Teitler, product ranks of the determinant and permanent](https://doi.org/10.4153/CMB-2015-076-1)

## Exhausting all four-term decompositions

The last-two-mode slice space $S$ is the three-dimensional space of hollow symmetric $3\times3$ matrices, with elementary basis $E_{12}+E_{21},E_{13}+E_{31},E_{23}+E_{32}$. It contains no nonzero rank-one matrix. A symmetric rank-one matrix over $k$ has the form $\lambda vv^{\mathsf T}$ with $\lambda\ne0$, whose diagonal cannot be identically zero. Therefore rank at most three is impossible, since its rank-one matrix factors would have to span exactly $S$. The displayed decomposition is verified by summing the two independent signs. A word of length three survives precisely when its second and third symbol counts are both odd, which forces all three counts to be one.

Consider any four-term decomposition. Its four rank-one matrix factors span a four-dimensional space $L$ containing $S$. None lies in $S$. Rescale each factor $M_i$ so that its image in $L/S$ is a common nonzero vector, compensating in the first-mode vectors. Every difference $M_i-M_j$ now belongs to $S$, so the factors share their diagonal and their alternating parts $M_i-M_i^{\mathsf T}$. If this common alternating part is nonzero, write $M_i=u_i v_i^{\mathsf T}$. The image of the alternating part is exactly $\langle u_i,v_i\rangle$, since independence of the pair makes the two dual row functionals independent. In particular every $M_i$ would have image in the same plane, contrary to the fact that the images of the slices in $S$ span $k^3$. Thus all four $M_i$ are symmetric rank-one matrices.

Write $M_i=\lambda_i v_i v_i^{\mathsf T}$. Every entry of the common diagonal is nonzero, since a zero in diagonal position $j$ would force $v_{ij}=0$ for all four factors, again contradicting the images of $S$. Normalize the first coordinate of each $v_i$ to the same nonzero $a$, compensating in $\lambda_i$. Equality of diagonals then gives the same nonzero $\lambda_i=\lambda$ and each later coordinate equals one chosen value or its negative. Independence of the four $M_i$ forces all four different sign patterns. The displayed four-term formula has exactly these last-two-mode factors after absorbing $\lambda$ into the first-mode vectors. The coefficients in the first mode are unique because the four matrices are independent. This proves the classification. Two normalized parameter pairs give the same set exactly when they differ by the independent sign changes, as follows by comparing the uniquely normalized vectors with first coordinate one.

The argument applies to the squarefree degree-three case. The decomposition problem for larger squarefree degrees is outside the theorem.
