# Transferring sparse proofs between conjugacy and nonsymmetric congruence

Use ordinary Polynomial Calculus in the original entry variables, with binary scalar linear combinations and multiplication by a single variable. Size counts all monomial occurrences, including the input lines actually used. Write $L_{\rm sim}(M,N)$ and $L_{\rm cong}(A,B)$ for minimum refutation sizes when these exist.

**Theorem.** Given square matrices $M,N$ of side $n$ over any field, put
$$
 K(M)=\begin{pmatrix}0&I\\ M&0\end{pmatrix}.
$$
Suppose no eigenvalue of $M$ times an eigenvalue of $N$, taken in a common algebraic closure, equals one. The two conjugacy and congruence systems are then equisatisfiable over every extension, and their minimum sparse refutation sizes differ by at most an additive polynomial in $n$. Their degrees agree above three, in the sense that clipping both minimum degrees below at three gives equal values. For an infinite field, or a field with more than $2n^2+2n$ elements, a common scalar shift gives this reduction for every pair, with both output matrices invertible. The resulting forms can be chosen nonsymmetric by also avoiding the shift making either input the identity, which costs at most two extra exclusions (equivalently enlarge the stated field-size bound by two for this last assertion).

**From the congruence equations to conjugacy.** Write the four blocks of $X$ as $U,C,D,V$ in row order, and those of its designated inverse $Y$ as $S,G,H,T$. The forward congruence and both inverse equations give $XK(M)=K(N)Y^T$ and $XK(M)^T=K(N)^T Y^T$ in degree three, by multiplying the Gram equation and its transpose by $Y^T$ and removing the inverse errors. These linear equations imply
$$
 U=T^T,\quad V=S^T,\quad VM=NV,\quad C=N^T C M,\quad D= N D M^T .
$$
The last two linear operators on the off-diagonal entries have only eigenvalues that are products of eigenvalues of $M,N$. This follows by triangularization after scalar extension, or the Kronecker product formula. Thus $C=D=0$ are scalar combinations of available lines over the original field. The lower-right blocks of $XY=I$ and $YX=I$ give $VT=TV=I$ after removal of terms involving $D$ and $C$. All of this uses polynomially many lines each of at most polynomial sparsity. A proof for conjugacy can now be replayed verbatim on the single entries of $V,T$. In particular extra size is additive, even for high-degree subsequent lines.

**From conjugacy to the congruence equations.** Given the two literal conjugacy matrices of variables $Z,W$, substitute $X=\operatorname{diag}(W^T,Z)$ and $Y=\operatorname{diag}(Z^T,W)$. Each original variable becomes a single variable or zero. The off-diagonal Gram blocks are $(ZW)^T$ and $ZMW$. The latter equals $N$ by the linear equation $ZM=NZ$ multiplied on the right by $W$ and the inverse equation $ZW=I$. All inverse entries specialize to zero or original inverse entries and their transposes. The specialized inputs therefore have polynomial-size degree-three derivations. Each subsequent monomial has at most one image, so replay adds at most the size of the supplied proof. Polynomial identities also establish both witness implications. Finally $M+cI,N+cI$ give precisely the same conjugacy equations, and each of at most $n^2$ eigenvalue pairs excludes at most two values of $c$. Avoiding singular shifts costs at most another $2n$ values. These arguments need neither density assumptions on the displayed matrices nor a chosen Jordan basis.

**A fixed construction over small fields.** For any pair with different ranks there is a transfer of sparse lower bounds from its conjugacy equations to invertible nonsymmetric congruence of side $12n$, over the very same field. Let
$$
 W_M=\begin{pmatrix}0&M\\0&0\end{pmatrix},\quad
 T_M=\begin{pmatrix}0&0&I+W_M\\I&0&I\\0&I&0\end{pmatrix},\quad
 f(t)=t^3-t-1 .
$$
Here $T_M$ has side $6n$. Direct block multiplication gives $f(T_M)=\operatorname{diag}(W_M,W_M,W_M)$, so $f(T_M)^2=0$ and $\operatorname{rank} f(T_M)=3\operatorname{rank}M$. Both $T_M$ and $K(T_M)$ are invertible and $K(T_M)$ is nonsymmetric. No two roots of $f$ are reciprocals in any characteristic: if $t$ and $1/t$ were both roots, adding $f(t)=0$ and $t^3 f(1/t)=0$ would give $t^2+t=0$, but neither zero nor $-1$ is a root. Thus $T_M,T_N$ satisfy the separation hypothesis. The distinct ranks of $f(T_M),f(T_N)$ exclude conjugacy over every extension. In a purported conjugacy proof for $T_M,T_N$, specialize each matrix of variables to six copies of $Z$, respectively $W$, on the diagonal and zeros elsewhere. Its input intertwining equations become zeros or copies of $ZM-NZ$ and its inverse equations become repetitions or zeros. Composing the two substitutions gives
$$
 L_{\rm sim}(M,N)\le L_{\rm cong}(K(T_M),K(T_N))+\operatorname{poly}(n).
$$
In fact all polynomial overhead in this inequality can be bounded by a constant times $(n+1)^8$: after the composite substitution there are $O(n^2)$ Gram or inverse inputs to supply, each a sum of at most $O(n)$ products of original linear intertwiner inputs by one variable and $O(n)$ scalar multiples of inverse inputs. Each intermediate sum has $O(n^2)$ monomials. Thus in any superpolynomial regime the sparse exponent for the diagonal idempotent lower bounds carries over to genuinely nonsymmetric nonsingular congruence. This transfer makes no assertion that minimum sparse size is invariant under arbitrary dense changes of basis. [Matrix proof systems](https://arxiv.org/html/2305.19320#S7.SS3)
