# Exact extraction from symmetric minors and a small-characteristic counterexample

GP178 has a positive answer with the same order exponent as ordinary determinantal extraction. GP177 has a negative answer in its exact division-free bounded-depth oracle model.

## GP178 · Symmetric determinantal ideals

**Theorem.** Let $F$ have characteristic zero and $1\le r\le n$. In the polynomial ring in the independent entries of a symmetric $n$-by-$n$ matrix $S$, let $I_r^{\mathrm{sym}}$ be the ideal of all $r$-minors, including nonprincipal minors. For any nonzero $f\in I_r^{\mathrm{sym}}$ of degree $d$, a constant-depth $f$-oracle circuit of size polynomial in $n,d$ computes the ordinary determinant of order $\Theta(r^{1/3})$. The same construction works over sufficiently large fields with characteristic greater than $d$.

Let $X$ be a matrix of independent variables and set $g(X)=f(X+X^{\mathsf T})$. Symmetrization has the linear section $S\mapsto S/2$. Hence substituting $X=S/2$ returns $f$ as a polynomial identity, so $g\ne0$ and $\deg g=d$.

Put $k=\lceil r/2\rceil$. Each $r$-minor of $X+X^{\mathsf T}$ belongs to the ordinary determinantal ideal $I_k$ of $X$. Expand the determinant by choosing in each column either the contribution from $X$ or the contribution from $X^{\mathsf T}$. In a summand with $j$ columns from $X$, expand along those columns. Each resulting product has a $j$-minor of $X$ and an $(r-j)$-minor of $X^{\mathsf T}$, with the empty minor interpreted as 1. At least one of these orders is at least $k$. A minor of that order lies in $I_k$ by Laplace expansion. Transposing a minor leaves its determinant unchanged after interchanging row and column sets. Pulling back a polynomial combination of the symmetric generators now gives $g\in I_k$. This is an ideal inclusion in the polynomial ring itself.

Apply Dey–Guo's exact determinant extraction, Corollary 3.19 of the arXiv version, to $g$ at parameter $k$. It gives a determinant of order $\Theta(k^{1/3})$ by a depth-three $g$-oracle circuit of size polynomial in $n,d$. Implement each $g$-gate by forming the sums of its input matrix entries with their transposes and calling $f$ on the independent entries. This adds $O(n^2)$ gates per call and bounded depth. The same argument transfers their arbitrary-ABP variant at parameter $k$ under its stated degree and size hypotheses. [Dey–Guo extraction theorem](https://arxiv.org/html/2511.16492#S3) · [Symmetric-ideal question](https://arxiv.org/html/2511.16492#S5)

## GP177 · A fixed-characteristic counterexample

**Theorem.** Fix a prime $p$. There is an explicit polynomial-degree family $f_r$ in ordinary $r$-minor ideals over $\mathbb F_p$ for which no polynomial-size, constant-depth family of exact division-free $f_r$-oracle circuits computes a determinant of order $\Theta(r^{1/3})$. This holds over every extension of $\mathbb F_p$, with arbitrary constants in that extension.

In a generic $2r$-by-$2r$ matrix $Y$, write $h_r(Y)$ for the leading $r$-minor. Take $Q=p^e$ to be the least power of $p$ at least $r$, and let $f_r=h_r^Q$. The polynomial belongs to the $r$-minor ideal, is nonzero, and has degree $rQ\le p r^2$.

Consider a division-free oracle circuit on output variables $x$. An oracle gate on its actual polynomial arguments $A(x)$ evaluates to $h_r(A(x))^Q$, even when those arguments depend on earlier oracle calls. With $\mathfrak m=(x)$ and $a=h_r(A(0))$, the Frobenius identity gives
$$
h_r(A(x))^Q-a^Q
=\big(h_r(A(x))-h_r(A(0))\big)^Q\in\mathfrak m^Q.
$$
Replace each oracle gate by its value at the origin in the original circuit. The resulting ordinary circuit agrees with the original modulo $\mathfrak m^Q$. This follows by induction in topological order. The oracle case is the displayed identity, and the ordinary gates preserve the congruence.

If the circuit computes a determinant of order $t<Q$, the replacement circuit has the desired determinant as its homogeneous component of degree $t$. An ordinary wire-size-$s$ depth-$D$ arithmetic circuit has degree at most $(s+1)^D$. Substitute $zx$ for $x$ and recover the coefficient of $z^t$ by interpolating at more than $(s+1)^D$ distinct scalars in the algebraic closure. This is a fixed linear combination of copies of the ordinary circuit with scaled inputs. When $D$ is constant and $s$ is polynomial in $r$, the result is an ordinary constant-depth polynomial-size circuit for the determinant.

Forbes's all-characteristic lower bound for iterated matrix multiplication rules this out. For completeness, put the matrices of an iterated product in successive superdiagonal blocks of a strictly upper triangular matrix $L$. An entry of $(I-L)^{-1}=I+L+\cdots+L^d$, between the first and last blocks, is the desired product entry. It is a signed minor of $I-L$, whose determinant is 1. This expresses the hard family as an affine specialization of a determinant of order polynomial in the size parameter. Padding with an identity block embeds that determinant into a larger one. A family of order-$\Theta(r^{1/3})$ determinants allows $r$ polynomial in the iterated-product size parameter, so it would contradict the lower bound. The same counterexample can use a larger polynomial Frobenius exponent to obstruct any prescribed target order of polynomial growth that is bounded below by a positive power of $r$.

The proof concerns formal equality of polynomials and also works with a symmetric matrix oracle of the same powered-minor form. Frobenius inversion as a function on a specified finite field addresses a different model. The positive theorem that extracts a Frobenius power remains applicable. [Dey–Guo small-characteristic question](https://arxiv.org/html/2511.16492#S5) · [Forbes, all-characteristic lower bound](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2024.31)

The circuit conclusions are written proofs. The accompanying Lean file verifies the symmetrization section, its matrix rank bound, and the ideal-power estimate for the Frobenius difference.
