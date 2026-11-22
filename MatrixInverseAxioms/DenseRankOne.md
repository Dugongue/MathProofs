# Exactly cubic sparse conjugacy with two dense isospectral inputs

Let \(A,B\) have side \(n\) over any field. Suppose a polynomial \(f\) of degree at most two satisfies \(\operatorname{rank} f(B)\le 1\) and \(\operatorname{rank} f(A)>\operatorname{rank} f(B)\). On \(H=XA-BX,\ XY-I,\ YX-I\), the minimum ordinary Polynomial Calculus (PC) degree is at most three and there is a refutation of sparse size \(O(n^3\log(2n))\) in the given coordinates. No row sparsity is required of either matrix. In every characteristic there is a family in this class with **both matrices having quadratically many nonzero entries**, the same characteristic and minimal polynomials, exact PC degree three, and exact sparse size order \(\Theta(n^3)\). Size counts all used monomial occurrences, and all the lower bounds allow arbitrary proof degree. [Question and equations](https://arxiv.org/html/2305.19320#S7.SS3)

## A cubic bound up to one logarithm in arbitrary bases

Write \(k=\operatorname{rank} f(B)\), which is zero or one. Select \(k+1\) standard coordinate vectors \(e_{j_i}\) such that \(u_i=f(A)e_{j_i}\) are independent. Derive the \(n\) components of \(X u_i-f(B)X e_{j_i}\) for each chosen column. For the quadratic term use
\[
(XA^2-B^2X)e_{j_i}=H(Ae_{j_i})+B H e_{j_i}.
\]
For a specified component the first summand is a combination of \(n\) entries in one row of \(H\), and the second summand a combination of \(n\) entries in one column. Each input has at most \(2n\) terms. Balanced binary sums have cost \(O(n^2\log(2n))\) per component. The linear term uses \(H e_{j_i}\), and the constant term cancels. Each final line has at most \(2n\) terms because \(e_{j_i}\) is a standard coordinate vector. The cost of all these linear equations is \(O(n^3\log(2n))\).

Choose \(k+1\) coordinate rows, with selector \(R\), such that \(T=[R u_i]_i\) is invertible. Factor \(f(B)=UV\) through \(k\) coordinates and set \(P=T^{-1}RYU,\ Q=[VX e_{j_i}]_i\). From the available equations and \(YX-I\) one obtains \(P Q=I_{k+1}\). Indeed for each selected row, multiply every component of each derived linear equation by the corresponding literal variable of \(RY\) and add. Combine with \((RYX-R)u_i\). Each added term has support \(O(n)\) and there are \(O(n)\) such terms per entry. Finally take the bounded-size linear combination for \(T^{-1}\). This uses degree at most two and \(O(n^2\log(2n))\) occurrences. If \(k=0\) this already yields one.

For \(k=1\), write \(P=(p_1,p_2)^T,\ Q=(q_1,q_2)\). Each of these forms has \(O(n)\) terms. The expression
\[
q_1(p_2q_2-1)-q_2(p_2q_1)=-q_1
\]
derives \(q_1=0\), then \(p_1q_1=0\) and \(p_1q_1-1=0\) give the contradiction. Multiplying by \(q_i\) is implemented by multiplying by each variable once and summing the results in a balanced tree. The two initial quadratic lines each have \(O(n^2)\) monomials, so this operation costs \(O(n^3\log(2n))\). The derivation uses the original variables and degree at most three.

## Dense inputs with matching characteristic and minimal polynomials

Take an even integer \(h\ge2\), first using side \(2h+1\). On the source use
\[
A_0=\begin{pmatrix}0&M&0\\0&0&u\\0&0&0\end{pmatrix},\qquad
M=I_h+u v^T
\]
in block sizes \((h,h,1)\), where \(u=(1,\ldots,1)^T\) and \(v=(1,-1,1,-1,\ldots)^T\). Since \(v^Tu=0\), \(M\) is invertible with \(Mu=u\), and the source has rank \(h+1\) and square \(t z^T\), where \(t=(u,0,0)^T\) and \(z\) is the last coordinate vector. In the target take \(\ker B_0\) to be the first \(h+1\) coordinates. Define the block mapping the remaining \(h\) coordinates into the first ones by \(C(I_h+a b^T)\), where \(C e_j=e_j-e_{j+1}\), \(a=(1,0,1,0,\ldots)^T\), and \(b=(0,1,0,1,\ldots)^T\). Since \(b^T a=0\), the factor \(I_h+a b^T\) is invertible. Thus \(\operatorname{im}B_0\) is the coordinate-sum-zero hyperplane in its kernel. This also proves \(\operatorname{rank}B_0=h\) and \(B_0^2=0\).

The source block \(M\) has every off-diagonal entry nonzero. In the target, \(Ca\) has nonzero entries in all the first \(h\) coordinates, including in characteristic two. Each even-indexed column of \(C(I_h+a b^T)=C+(Ca)b^T\) therefore has at least \(h-2\) nonzero entries. Both input matrices are dense as claimed. Append the same size-three nilpotent Jordan block to \(A_0,B_0\), giving \(A,B\). They have characteristic polynomial \(s^n\) and minimal polynomial \(s^3\), and the ranks of their squares are two and one. The degree-two criterion excludes degree two, so the degree is exactly three. Padding both sides with a common zero block of side at most three allows all sufficiently large dimensions. [Conjugacy degree test](ConjugacyDegree.md)

## Why every proof of the dense family has cubic size

For a middle source column \(j\) in \(A_0\), choose a row \(a_j^T\) supported in the first source block with \(a_j^TA_0=e_j^T\), possible because \(M\) is invertible. Since \(e_j^TA_0=z^T\) and \(A_0^2=tz^T\), we have \(a_j^Tt=1\). The matrix
\[
C_j=(I-ta_j^T)A_0=A_0-t e_j^T
\]
is square-zero of rank \(h\). Squaring uses \(A_0t=0,\ e_j^Tt=0,\ t e_j^T A_0=A_0^2\). The rank follows because \(I-ta_j^T\) kills exactly one dimension in \(\operatorname{im}A_0\), namely the line \(Ft\), and forces its image into \(\ker a_j^T\). In particular \(t\in\ker C_j\setminus\operatorname{im}C_j\).

For every first-block target coordinate \(i\le h+1\), \(e_i\) lies in \(\ker B_0\setminus\operatorname{im}B_0\). The two square-zero matrices of rank \(h\) admit Jordan bases having \(t,e_i\) as their respective singleton blocks. To construct these bases, take an image basis, choose preimages, and append the indicated kernel vector outside the image. Therefore there is an invertible \(X_0\) with \(X_0 C_j=B_0X_0\) and \(X_0 t=e_i\). Consequently \(X_0 A_0-B_0X_0=e_i e_j^T\). Extend by identity on the common summands and take \(Y=X^{-1}\). The assignment satisfies all equations except the one selected \(H_{ij}\). Thus each of the \(h(h+1)\) corresponding indexed forward equations must be used. Each contains at least \(h-1\) distinct monomials from \(M\). These have columns outside the middle source column \(j\), whereas \((BX)_{ij}\) uses only column \(j\). No such monomial cancels. Index pairs give distinct necessary axioms, as their omission witnesses show. Their input occurrences alone cost \(\Omega(n^3)\).

## Removing the logarithm in the upper bound for this family

In this family \(B=S+a' (b')^T\), where \(S\) has bounded row support and \(a',b'\) are the embedded vectors \(Ca,b\) on the corresponding old blocks. Use one anchor row \(i_0\) with \(a'_{i_0}\ne0\). Subtract \((a'_i/a'_{i_0})H_{i_0j}\) from \(H_{ij}\). The rank-one contribution to the resulting \(\widetilde H_{ij}\) cancels. Preparing all these entries costs \(O(n^3)\), since they are sums of two raw lines. For each non-anchor row, a partial sum of entries of \(\widetilde H\) across \(m\) columns has at most \(2n+O(m)\) monomials. The two \(XA\) contributions lie in the two fixed \(X\) rows \(i,i_0\), and the \(SX\) contributions lie in boundedly many rows and in the \(m\) specified columns. At a level of a balanced tree there are at most \(\lceil n/2^\ell\rceil\) groups and their total number of columns is at most \(n\). Summing the resulting bounds over levels gives \(O(n^2)\) per non-anchor row to form \((\widetilde H A e_j)_i\). Compute the anchor contraction \((H A e_j)_{i_0}\) separately at cost \(O(n^2\log(2n))\), then restore it to each desired row. The anchor contraction has at most \(n^2\) monomials, and reuse over \(n\) rows costs \(O(n^3)\). This yields \(H A e_j\) at cost \(O(n^3)\) for each of the two chosen columns.

For \(B H e_j\) compute the shared scalar line \((b')^T H e_j\) once, at cost \(O(n^2\log(2n))\) and support at most \(n^2\). Its \(n\) scalar multiples and sums with \(S H e_j\) cost \(O(n^3)\). Combining the two terms gives the desired contractions for \(f(s)=s^2\) in total size \(O(n^3)\). Finally \(B^2\) is a single matrix unit in the untouched common Jordan block. It has a rank-one factorization \(UV\) into standard unit column and row. The two \(q_i=V X e_{j_i}\) are literal variables, so the degree-three step above does not need any expanded linear multiplier. The remainder after the contractions costs \(O(n^2\log(2n))\), giving the exact total order \(\Theta(n^3)\).

The claims are written proofs. The dense family retains the earlier rank-one omission construction while allowing a rank-one dense perturbation on the formerly sparse side. [Earlier construction](CubicConjugacy.md)
