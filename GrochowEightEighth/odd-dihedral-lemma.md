# Odd-polygon lemma used in the doubling proof

This supporting proof appeared in the preceding packet. It is reproduced here so the even-polygon argument can be read independently.

## Sharp dihedral moment cutoffs in characteristic two

Edidin and Katz ask in §5.2 whether generic recovery from the first three polynomial invariant tensors extends to arbitrary infinite fields. Here the tensor is the unnormalized group-sum tensor. In characteristic two these tensors have positive-dimensional fibers for every natural dihedral action. For the action on an odd number \(n\ge5\) of points, orders through four suffice and are sharp. For \(n=3\), orders through five are required and suffice. When using all polynomial invariants instead of tensor entries in characteristic two, the sharp generic cutoff for odd \(n\ge3\) is three except at \(n=5\), where it is four. [Edidin and Katz, Theorem 2.6 and §5.2](https://arxiv.org/html/2408.09599v4#S5.SS2)

Let \(D_n\) have order \(2n\), and define
\[
T_d(x)=\sum_{g\in D_n}(gx)^{\otimes d}.
\]
The normalization by \(2n\) is unavailable in characteristic two. For \(d=1,2\), each monomial specifying an entry in the permutation basis is fixed by at least one reflection. For a pair of distinct indices \(i,j\), the reflection sends an index \(l\) to \(i+j-l\) modulo \(n\). The group sum can be paired under that reflection, so \(T_1=T_2=0\). The zeroth group sum is also zero. A constant vector \(\mathbf 1\) is fixed by the group. Expanding \(T_3(x+a\mathbf 1)\) and collecting the terms by their number of ordinary slots gives \(T_3(x)\), since each lower-order tensor vanishes. Each such affine line has infinitely many points over an infinite field, while an orbit is finite. A nonempty Zariski open set containing \(x\) meets that line in a nonempty open subset. This proves the lower bound even for recovery restricted to a generic locus.

### Recovering the quadratic Fourier information at order four

For odd \(n\), work over a field containing a primitive \(n\)-th root of unity. In Fourier coordinates \(x_i\), indexed modulo \(n\), rotation multiplies \(x_i\) by \(\zeta^i\), and reflection interchanges \(x_i,x_{-i}\). Let \(\overline m\) denote the reflected monomial, and put \([m]=m+\overline m\) and \(p_i=x_i x_{-i}\). The entries of \(T_d\) give \([m]\) for each degree-\(d\) monomial of weight zero. Indeed rotation contributes the nonzero factor \(n\) at weight zero and cancels every other monomial. Reflected fixed monomials have zero trace. If \(n\ge3\), the cubic trace \(S=[x_1^2x_{-2}]\) is a nonzero polynomial, so \(T_4\) gives the zero-frequency coordinate from \(x_0S/S\) on the open set where \(S\ne0\).

For odd \(n\ge7\), put \(k=(n-1)/2\). For distinct \(a,b\in\{1,\ldots,k\}\), use the cubic monomials
\[
 A=x_a x_b x_{-a-b},\qquad B=x_{-a}x_b x_{a-b}.
\]
Expanding their trace product by \([A][B]=[AB]+[A\overline B]\) gives
\[
 [A][B]=p_a C_{ab}+p_b D_{ab},\qquad
 C_{ab}=[x_b^2x_{-a-b}x_{a-b}],\quad D_{ab}=[x_a^2x_{-a-b}x_{b-a}].
\]
Both quartic traces are nonzero polynomials. For example, the unreflected monomial in \(D_{ab}\) includes \(x_a^2\), and to be fixed under reflection its other two factors would both have to be \(x_{-a}\). This would force \(b=0\). The same reasoning applies to \(C_{ab}\).

Use rows \((a,b)=(1,2),(1,3),(2,3)\). Their determinant on \(p_1,p_2,p_3\) is \(C_{12}D_{13}C_{23}+D_{12}C_{13}D_{23}\). It is nonzero for every odd \(n\ge7\). The two products involve the following triples of weight lists before reflection.
\[
\begin{array}{c|ccc}
&\text{first factor}&\text{second factor}&\text{third factor}\\
 C_{12}D_{13}C_{23}&(2,2,-3,-1)&(1,1,-4,2)&(3,3,-5,-1)\\
 D_{12}C_{13}D_{23}&(1,1,1,-3)&(3,3,-4,-2)&(2,2,-5,1)
\end{array}
\]
To check a nonzero coefficient, the table below records the triples of exponents of \(x_1,x_2,x_3\) in the eight terms of each product. A digit string \(243\) here means the triple \((2,4,3)\). Signs of individual factors are chosen independently.

| Modulus | First product | Second product |
|---|---|---|
| \(7\) | \(243,324,032,113,331,412,120,201\) | \(433,134,440,141,303,004,310,011\) |
| Odd \(n\ge9\) | \(232,313,022,103,330,411,120,201\) | \(422,123,430,131,302,003,310,011\) |

In each row the first product's unreflected term has a triple occurring exactly once across both products. For \(n\ge9\), none of the signed indices \(\pm4,\pm5\) reduce to \(1,2,3\), which makes the table uniform. This proves nonvanishing even in characteristic two. Solving this system recovers \(p_1,p_2,p_3\) rationally from the moment entries. Then use the row \((1,j)\) and divide by \(D_{1j}\) to recover each remaining \(p_j\). All divisions are by nonzero polynomials, so these steps work on a single generic locus.

For \(n=5\) write \(a=x_1,b=x_2,c=x_3,d=x_4\), \(p=ad,q=bc\), and take traces
\[
 S=a^2c+d^2b,\qquad T=ab^2+dc^2,\qquad
 U=a^3b+d^3c,\qquad V=b^3d+c^3a.
\]
Expansion gives \(ST=qU+pV\) and \(UV=pT^2+qS^2\). The second identity uses the characteristic-two squaring law. The determinant \(VS^2+UT^2\) takes the value one at \((a,b,c,d)=(1,1,0,0)\), so the two equations recover \(p,q\) generically.

### Recovering the orbit from the extracted information

For any odd \(n\), ordinary degree-one and degree-two polynomial invariants give \(x_0,p_i\) directly. The cubic invariants add the traces of weight-zero cubic monomials. Each pair \((m,\overline m)\) is determined up to exchange by its sum and product: the product is a known monomial in the \(p_i\) when \(m\) has no zero-frequency factor. For a generic candidate \(y\) with the same data, let \(t_i=y_i/x_i\) and \(a_i=x_i/x_{-i}\). The products give \(t_{-i}=t_i^{-1}\), and put \(e_{-i}=-e_i\). Each cubic triple with form \(v=e_i+e_j+e_l\) constrains \(t^v\) to either \(1\) or \(a^{-v}\). On the generic nonzero locus the \(a_i\) for \(1\le i\le k\) are independent Laurent variables. Consequently a minimal integer dependence among such forms synchronizes their choices. To see this, for \(\sum_v c_v v=0\) the chosen alternative branches imply \(a^{\sum_v c_v\epsilon_v v}=1\), with \(\epsilon_v\in\{0,1\}\). A proper nonempty subset of the terms has nonzero sum by minimality, and its Laurent equality is excluded generically.

For \(n=2k+1,\ k\ge4\), the forms \(w_j=e_1+e_j-e_{j+1}\), \(1\le j<k\), are independent. The cubic forms \(e_2+e_j-e_{j+2}=-w_1+w_j+w_{j+1}\) for \(2\le j\le k-2\) give minimal dependences and synchronize every \(w_j\). Reflecting once if necessary makes all these branches equal to \(1\), yielding \(t_i=t_1^i\) for \(1\le i\le k\). The two triples \((1,k,k)\) and \((2,k-1,k)\) then constrain \(t_1^n\) to \(1\) or their respective distinct Laurent monomials in the \(a_i\). This forces \(t_1^n=1\) generically, which is exactly the remaining rotation freedom. For \(n=7\), the four forms \(v=2e_1-e_2,\ w=e_1+e_2-e_3,\ a=e_1+2e_3,\ b=2e_2+e_3\) have the minimal dependence \(v-w-a+b=0\), as seen from rank three and its four nonzero coefficients. Synchronizing them also gives the same chain and wrap conclusion. These branch arguments use multiplicative identities and remain valid in characteristic two.

For \(n=5\) the only nonzero-frequency cubic pairs are the ones traced by \(S,T\) above. Put \(u=a^2/b,\ v=ab^2\). With \(p,q\) fixed, \((a,b)\mapsto(u,v)\) is onto over an algebraic closure and has kernel exactly the rotations, since its exponent determinant is five. The traces fix \(u,v\) up to independent inversion with the reflection factors \(p^2/q,\ pq^2\), respectively. Generically the four choices are distinct and give two dihedral orbits. The quartic trace \(U\) specifies the unordered reflection pair for \(uv\). Since the exponent form for \(uv\) is the sum of the two cubic forms, the minimal dependence synchronizes the two branches and proves quartic sufficiency. For ordinary polynomial invariants, at all odd \(n\ge3\) degree two gives only \(x_0,p_1,\ldots,p_k\), so its fibers have positive dimension. Degree three suffices at \(n=3\) by the elementary symmetric polynomials.

For the tensor cutoff at \(n=3\), the only nonzero-frequency monomials of degree at most four with nonzero trace are the two orientations of \(x_1^3\). The remaining weight-zero monomials of degree at most four on those frequencies are powers of \(p_1\), hence have trace zero. Thus through order four the data generate just the field of \(x_0,S=[x_1^3]\). At order five the trace \(p_1S\) recovers \(p_1\). The sum \(S\) and product \(p_1^3\) recover the unordered pair \(x_1^3,x_2^3\), and the known product \(p_1\) makes the remaining third roots exactly the rotations. This proves the stated sharp cutoff.

The geometric statements also give rational invariant field generation in the stated sufficient degrees. Over the Fourier splitting field the oriented monomials satisfy quadratic equations with a generically nonzero linear coefficient, and the remaining rotation ambiguity comes from an \(n\)-th root with \(n\) odd. The extensions are separable, and the generic fiber has exactly the group order, which is also the degree over the full fixed field. The resulting field equality descends along the finite separable Fourier splitting field. For example, base change of invariant polynomial spaces follows by writing the spaces as simultaneous kernels of linear differences, and the rational fixed field is the fraction field of the invariant polynomials by clearing denominators with an orbit product.
