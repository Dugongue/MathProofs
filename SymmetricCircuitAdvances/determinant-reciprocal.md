# A single reciprocal suffices for symmetric determinant circuits

For every field and every matrix order \(n\), polynomial-size arithmetic circuits with one reciprocal gate compute the determinant and all characteristic coefficients as rational functions. The circuits preserve simultaneous row and column permutations and matrix transposition. Their common denominator is a nonzero polynomial in every characteristic. The construction also gives polynomial-size circuits for the adjugate with the same reciprocal and the corresponding output action. This addresses the rational model associated to Dawar and Wilsenach's question about arbitrary fields. Their division-free question is a separate statement. [Dawar–Wilsenach, §8](https://theoryofcomputing.org/articles/v021a014/v021a014.pdf)

Let \(e\) be the all-ones vector, and set \(m_j=e^{\mathsf T}X^j e\) for \(0\le j\le2n-1\). For \(0\le i,j<n\) put \(H_{ij}=m_{i+j}\) and \(H'_{ij}=m_{i+j+1}\). Let \(R\) have columns \(X^j e\) and \(L\) have rows \(e^{\mathsf T}X^i\). Then \(H=LR\) and \(H'=LXR\), giving the identity
\[
\det(zH-H')=\det(H)\det(zI-X).
\]
On the diagonal matrix \(\operatorname{diag}(t_1,\ldots,t_n)\) of independent indeterminates, \(L=R^{\mathsf T}\) and \(R\) is Vandermonde. Thus \(\det H=\prod_{i<j}(t_j-t_i)^2\) there, which is nonzero as a polynomial over every field, including small finite fields. Division by \(\det H\) in the function field is therefore legitimate.

All the moments have small physical circuits. Compute the two vector sequences \(w_i=X^i e\) and \(u_i=(X^{\mathsf T})^i e\) by matrix-vector multiplication with unordered sums. Conjugating by a permutation permutes coordinates, and transposition interchanges the two sequences. Use \(m_{2i}=u_i^{\mathsf T}w_i\) and \(m_{2i+1}=u_i^{\mathsf T}Xw_i\). For the latter use the explicit unordered double sum over coordinates, so transposition swaps the two summation indices while permuting the factors of each product. These circuits have polynomial size and each moment output gate is fixed.

The Hankel labels \(i,j\) are time indices, so they are themselves fixed by the symmetries. Use any ordered division-free determinant circuit, such as Berkowitz's, on \(H,H'\). For the full characteristic polynomial use it on \(zH-H'\), doing coefficient arithmetic modulo \(z^{n+1}\) by schoolbook polynomial multiplication. The determinant has degree at most \(n\) in \(z\), so this recovers every coefficient with polynomial overhead. All gates in these ordered routines can be fixed by the symmetry because their input gates are fixed. Multiply their outputs by the single reciprocal of \(\det H\). This gives the characteristic coefficients and hence determinant with precisely the stated symmetry. [Berkowitz's division-free determinant circuit](https://doi.org/10.1016/0020-0190(84)90018-8)

For the adjugate, the characteristic polynomial \(z^n+c_1z^{n-1}+\cdots+c_n\) gives
\[
\operatorname{adj}(X)=(-1)^{n-1}\bigl(X^{n-1}+c_1 X^{n-2}+\cdots+c_{n-1}I\bigr).
\]
To retain transposition at the level of gates, compute even powers by squaring and odd powers \(X^{2j+1}\) by the direct entrywise triple product \(X^jXX^j\). Reversal under transposition permutes the two internal indices and interchanges the outer factors of each commutative product. This needs only polynomially many gates. The adjugate output indices carry the usual simultaneous permutation and transpose actions.

On any input where the common denominator is nonzero the circuit also gives a pointwise computation. Over a finite field it is possible for an input to have zero denominator, and the theorem concerns the rational-function identity. Both the nonzero denominator and the single reciprocal matter to the distinction from division-free arithmetic circuits.
