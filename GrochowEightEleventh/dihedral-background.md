# Earlier proofs used in the all-characteristic classification

These excerpts preserve the previous proofs for the cases outside even polygons in characteristic two.

## Polynomial invariants over other fields

For every infinite field of characteristic prime to $2n$, cubic polynomial invariants of the natural $n$-dimensional representation generically separate $D_n$-orbits, with exactly one exception. For $n=5$, the cubic invariants have two generic dihedral orbits per fiber over an algebraic closure. Degree four repairs this exception. In particular the universal statement in §5.2 is negative even over $\mathbb C$. This also gives a correction to the $n=5$ case of Theorem 2.5 in the cited preprint. The example in §4.2 of that preprint exhibits a particular degenerate fiber. Here the two-orbit fiber occurs generically. [Theorem 2.5](https://arxiv.org/html/2408.09599v2#S2.SS2) · [Example 4.5 and §5.2](https://arxiv.org/html/2408.09599v2#S4.SS2).

### Fourier coordinates and consistent reflection choices

Work first over an algebraic closure and use Fourier coordinates $x_i$ indexed modulo $n$. Rotation multiplies $x_i$ by $\zeta^i$ and reflection exchanges $x_i$ and $x_{-i}$. Degree one gives $x_0$ and degree two gives $p_i=x_i x_{-i}$, including $p_h=x_h^2$ at $h=n/2$ when $n$ is even. For any zero-sum triple $(i,j,k)$ the cubic data give
$$
A+B,\qquad A=x_i x_j x_k,\quad B=x_{-i}x_{-j}x_{-k}.
$$
Its product $AB=p_i p_j p_k$ is known. Thus each such ordered pair has two possible orientations.

For comparing points $x,y$ in a generic fiber use ratios $t_i=y_i/x_i$ and $a_i=x_i/x_{-i}$. The equations from degree two give $t_{-i}=t_i^{-1}$ and $a_{-i}=a_i^{-1}$. For the even index $h$ this means $t_h^2=1$ and $a_h=1$. On a zero-sum triple, put $v=e_i+e_j+e_k$ with $e_{-i}=-e_i$ and, in the even case, $2e_h=0$. One has
$$
t^v\in\{1,a^{-v}\}.
$$
Here the $a_i$ for positive nonself-opposite indices are independent Laurent variables. Choose a branch $\epsilon_v\in\{0,1\}$ so the value is $a^{-\epsilon_v v}$.

The following use of an integer relation will synchronize these choices. Suppose a set of forms has a minimal linear dependence after projection to the free coordinates, and an integer dependence $\sum_v c_v v=0$ in the group with the even torsion coordinate. One can always clear denominators and multiply by two in the even case. All $c_v$ are nonzero. The branch choices imply
$$
a^{\sum_v c_v\epsilon_v v}=1.
$$
For a nonempty proper subset of its terms the projected exponent is nonzero by minimality. The corresponding Laurent equation is a proper closed condition on $x$. There are finitely many such tests in the proof. Away from their union all forms in the dependence have the same branch. Reflection switches all branches at once.

### The cases with cubic recovery

Let $k=\lfloor(n-1)/2\rfloor$. For $k\ge4$ use the nonwrap forms
$$
w_j=e_1+e_j-e_{j+1}\quad (1\le j<k),\qquad
v_{2j}=e_2+e_j-e_{j+2}\quad (2\le j\le k-2).
$$
The $w_j$ are independent over $\mathbb Q$. Since $v_{2j}=-w_1+w_j+w_{j+1}$, each of these relations has minimal support. They synchronize all $w_j$ with $w_1$. After a reflection if necessary we therefore have $t_i=t_1^i$ for $1\le i\le k$.

For odd $n=2k+1$, the triples $(1,k,k)$ and $(2,k-1,k)$ both give $t_1^n\in\{1,a^{-v}\}$. Their two nontrivial Laurent monomials differ generically. Thus $t_1^n=1$. For even $n=2k+2$ use the half-index triples $(1,k,h)$ and $(2,k-1,h)$. They similarly give $t_1^h t_h=1$, since the nontrivial Laurent monomials differ. Squaring gives $t_1^n=1$ and $t_h=t_1^h$. These are exactly the rotation ratios.

For $n=6,7,8$ the following relations suffice. The names in each row denote the displayed forms in order. Each relation has minimal support on projection to the free coordinates. This follows by taking the rank of the displayed two- or three-row matrix, which is one less than the number of forms, and observing that no coefficient in the relation vanishes.

| $n$ | Forms | Relation |
|---|---|---|
| $6$ | $v=2e_1-e_2$, $a=e_1+e_2+e_h$, $b=3e_2$ | $v+b-2a=0$ |
| $7$ | $v=2e_1-e_2$, $w=e_1+e_2-e_3$, $a=e_1+2e_3$, $b=2e_2+e_3$ | $v-w-a+b=0$ |
| $8$ | $v=2e_1-e_2$, $w=e_1+e_2-e_3$, $a=e_1+e_3+e_h$, $b=2e_2+e_h$ | $v-w-a+b=0$ |

The orders of the ratios then follow from the same chain and wrap equations. For $n=4$, the single half-index triple $(1,1,2)$ may be oriented using reflection. It gives $t_1^2t_2=1$ and $t_1^4=1$. For $n=3$ the action is the full symmetric action on three coordinates, so the elementary symmetric polynomials suffice. The smaller cases are immediate from the elementary symmetric polynomials as well.

These statements give field generation in the same degrees. Indeed the relevant oriented cubic monomials are roots of quadratics over the invariant-data field, generically with distinct roots. The half-frequency coordinate is obtained by a separable square root. A chain expresses every other coordinate in terms of $x_1$ and these algebraic quantities. A wrap monomial determines a power of $x_1$ whose exponent divides $n$ or is equal to $n$. Such a root extraction is separable in the stated characteristic. Thus the field extension is finite separable, and its degree agrees with the number of ordered points in a generic geometric fiber. For the nonexceptional cases that is the effective group order. Base change preserves the invariant field generation conclusion, and separation over an algebraic closure implies separation of the original-field points.

### The exceptional five-point action

The only nonzero-frequency triples, up to reflection and reorderings, are $(1,1,-2)$ and $(1,2,2)$. Terms involving $x_0$ add only information already in degrees one and two. With the products $p_1,p_2$ fixed, write
$$
u=x_1^2/x_2,\qquad v=x_1x_2^2.
$$
The monomial map from $(x_1,x_2)$ to $(u,v)$ has integer determinant five. It is onto over an algebraic closure and has kernel the rotations. Reflection simultaneously takes
$$
(u,v)\longmapsto\left(\frac{p_1^2}{p_2u},\frac{p_1p_2^2}{v}\right).
$$
The two cubic sums specify the first and second coordinates each only up to the displayed involution in that coordinate. Generically these are four distinct choices, all realized because the monomial map is onto. Simultaneous reflection pairs them into two dihedral orbits. Separability is again given by the two quadratics and the fifth-root extraction. In particular the cubic subfield has degree two inside the full invariant field.

The quartic invariant $x_1^3x_2+x_{-1}^3x_{-2}$ fixes the unordered reflection pair for the product $uv$. Its exponent form is the sum of the two cubic forms. The minimal dependence on these three forms forces the same branch on the two original forms, and hence a unique dihedral orbit. Thus the exact algebraic generic cutoff for $n=5$ is four.

## Sharp dihedral moment cutoffs in characteristic two

Edidin and Katz ask in §5.2 whether generic recovery from the first three polynomial invariant tensors extends to arbitrary infinite fields. Here the tensor is the unnormalized group-sum tensor. In characteristic two these tensors have positive-dimensional fibers for every natural dihedral action. For the action on an odd number $n\ge5$ of points, orders through four suffice and are sharp. For $n=3$, orders through five are required and suffice. When using all polynomial invariants instead of tensor entries in characteristic two, the sharp generic cutoff for odd $n\ge3$ is three except at $n=5$, where it is four. [Edidin and Katz, Theorem 2.6 and §5.2](https://arxiv.org/html/2408.09599v4#S5.SS2)

Let $D_n$ have order $2n$, and define
$$
T_d(x)=\sum_{g\in D_n}(gx)^{\otimes d}.
$$
The normalization by $2n$ is unavailable in characteristic two. For $d=1,2$, each monomial specifying an entry in the permutation basis is fixed by at least one reflection. For a pair of distinct indices $i,j$, the reflection sends an index $l$ to $i+j-l$ modulo $n$. The group sum can be paired under that reflection, so $T_1=T_2=0$. The zeroth group sum is also zero. A constant vector $\mathbf 1$ is fixed by the group. Expanding $T_3(x+a\mathbf 1)$ and collecting the terms by their number of ordinary slots gives $T_3(x)$, since each lower-order tensor vanishes. Each such affine line has infinitely many points over an infinite field, while an orbit is finite. A nonempty Zariski open set containing $x$ meets that line in a nonempty open subset. This proves the lower bound even for recovery restricted to a generic locus.

### Recovering the quadratic Fourier information at order four

For odd $n$, work over a field containing a primitive $n$-th root of unity. In Fourier coordinates $x_i$, indexed modulo $n$, rotation multiplies $x_i$ by $\zeta^i$, and reflection interchanges $x_i,x_{-i}$. Let $\overline m$ denote the reflected monomial, and put $[m]=m+\overline m$ and $p_i=x_i x_{-i}$. The entries of $T_d$ give $[m]$ for each degree-$d$ monomial of weight zero. Indeed rotation contributes the nonzero factor $n$ at weight zero and cancels every other monomial. Reflected fixed monomials have zero trace. If $n\ge3$, the cubic trace $S=[x_1^2x_{-2}]$ is a nonzero polynomial, so $T_4$ gives the zero-frequency coordinate from $x_0S/S$ on the open set where $S\ne0$.

For odd $n\ge7$, put $k=(n-1)/2$. For distinct $a,b\in\{1,\ldots,k\}$, use the cubic monomials
$$
 A=x_a x_b x_{-a-b},\qquad B=x_{-a}x_b x_{a-b}.
$$
Expanding their trace product by $[A][B]=[AB]+[A\overline B]$ gives
$$
 [A][B]=p_a C_{ab}+p_b D_{ab},\qquad
 C_{ab}=[x_b^2x_{-a-b}x_{a-b}],\quad D_{ab}=[x_a^2x_{-a-b}x_{b-a}].
$$
Both quartic traces are nonzero polynomials. For example, the unreflected monomial in $D_{ab}$ includes $x_a^2$, and to be fixed under reflection its other two factors would both have to be $x_{-a}$. This would force $b=0$. The same reasoning applies to $C_{ab}$.

Use rows $(a,b)=(1,2),(1,3),(2,3)$. Their determinant on $p_1,p_2,p_3$ is $C_{12}D_{13}C_{23}+D_{12}C_{13}D_{23}$. It is nonzero for every odd $n\ge7$. The two products involve the following triples of weight lists before reflection.
$$
\begin{array}{c|ccc}
&\text{first factor}&\text{second factor}&\text{third factor}\\
 C_{12}D_{13}C_{23}&(2,2,-3,-1)&(1,1,-4,2)&(3,3,-5,-1)\\
 D_{12}C_{13}D_{23}&(1,1,1,-3)&(3,3,-4,-2)&(2,2,-5,1)
\end{array}
$$
To check a nonzero coefficient, the table below records the triples of exponents of $x_1,x_2,x_3$ in the eight terms of each product. A digit string $243$ here means the triple $(2,4,3)$. Signs of individual factors are chosen independently.

| Modulus | First product | Second product |
|---|---|---|
| $7$ | $243,324,032,113,331,412,120,201$ | $433,134,440,141,303,004,310,011$ |
| Odd $n\ge9$ | $232,313,022,103,330,411,120,201$ | $422,123,430,131,302,003,310,011$ |

In each row the first product's unreflected term has a triple occurring exactly once across both products. For $n\ge9$, none of the signed indices $\pm4,\pm5$ reduce to $1,2,3$, which makes the table uniform. This proves nonvanishing even in characteristic two. Solving this system recovers $p_1,p_2,p_3$ rationally from the moment entries. Then use the row $(1,j)$ and divide by $D_{1j}$ to recover each remaining $p_j$. All divisions are by nonzero polynomials, so these steps work on a single generic locus.

For $n=5$ write $a=x_1,b=x_2,c=x_3,d=x_4$, $p=ad,q=bc$, and take traces
$$
 S=a^2c+d^2b,\qquad T=ab^2+dc^2,\qquad
 U=a^3b+d^3c,\qquad V=b^3d+c^3a.
$$
Expansion gives $ST=qU+pV$ and $UV=pT^2+qS^2$. The second identity uses the characteristic-two squaring law. The determinant $VS^2+UT^2$ takes the value one at $(a,b,c,d)=(1,1,0,0)$, so the two equations recover $p,q$ generically.

### Recovering the orbit from the extracted information

For any odd $n$, ordinary degree-one and degree-two polynomial invariants give $x_0,p_i$ directly. The cubic invariants add the traces of weight-zero cubic monomials. Each pair $(m,\overline m)$ is determined up to exchange by its sum and product: the product is a known monomial in the $p_i$ when $m$ has no zero-frequency factor. For a generic candidate $y$ with the same data, let $t_i=y_i/x_i$ and $a_i=x_i/x_{-i}$. The products give $t_{-i}=t_i^{-1}$, and put $e_{-i}=-e_i$. Each cubic triple with form $v=e_i+e_j+e_l$ constrains $t^v$ to either $1$ or $a^{-v}$. On the generic nonzero locus the $a_i$ for $1\le i\le k$ are independent Laurent variables. Consequently a minimal integer dependence among such forms synchronizes their choices. To see this, for $\sum_v c_v v=0$ the chosen alternative branches imply $a^{\sum_v c_v\epsilon_v v}=1$, with $\epsilon_v\in\{0,1\}$. A proper nonempty subset of the terms has nonzero sum by minimality, and its Laurent equality is excluded generically.

For $n=2k+1,\ k\ge4$, the forms $w_j=e_1+e_j-e_{j+1}$, $1\le j<k$, are independent. The cubic forms $e_2+e_j-e_{j+2}=-w_1+w_j+w_{j+1}$ for $2\le j\le k-2$ give minimal dependences and synchronize every $w_j$. Reflecting once if necessary makes all these branches equal to $1$, yielding $t_i=t_1^i$ for $1\le i\le k$. The two triples $(1,k,k)$ and $(2,k-1,k)$ then constrain $t_1^n$ to $1$ or their respective distinct Laurent monomials in the $a_i$. This forces $t_1^n=1$ generically, which is exactly the remaining rotation freedom. For $n=7$, the four forms $v=2e_1-e_2,\ w=e_1+e_2-e_3,\ a=e_1+2e_3,\ b=2e_2+e_3$ have the minimal dependence $v-w-a+b=0$, as seen from rank three and its four nonzero coefficients. Synchronizing them also gives the same chain and wrap conclusion. These branch arguments use multiplicative identities and remain valid in characteristic two.

For $n=5$ the only nonzero-frequency cubic pairs are the ones traced by $S,T$ above. Put $u=a^2/b,\ v=ab^2$. With $p,q$ fixed, $(a,b)\mapsto(u,v)$ is onto over an algebraic closure and has kernel exactly the rotations, since its exponent determinant is five. The traces fix $u,v$ up to independent inversion with the reflection factors $p^2/q,\ pq^2$, respectively. Generically the four choices are distinct and give two dihedral orbits. The quartic trace $U$ specifies the unordered reflection pair for $uv$. Since the exponent form for $uv$ is the sum of the two cubic forms, the minimal dependence synchronizes the two branches and proves quartic sufficiency. For ordinary polynomial invariants, at all odd $n\ge3$ degree two gives only $x_0,p_1,\ldots,p_k$, so its fibers have positive dimension. Degree three suffices at $n=3$ by the elementary symmetric polynomials.

For the tensor cutoff at $n=3$, the only nonzero-frequency monomials of degree at most four with nonzero trace are the two orientations of $x_1^3$. The remaining weight-zero monomials of degree at most four on those frequencies are powers of $p_1$, hence have trace zero. Thus through order four the data generate just the field of $x_0,S=[x_1^3]$. At order five the trace $p_1S$ recovers $p_1$. The sum $S$ and product $p_1^3$ recover the unordered pair $x_1^3,x_2^3$, and the known product $p_1$ makes the remaining third roots exactly the rotations. This proves the stated sharp cutoff.

The geometric statements also give rational invariant field generation in the stated sufficient degrees. Over the Fourier splitting field the oriented monomials satisfy quadratic equations with a generically nonzero linear coefficient, and the remaining rotation ambiguity comes from an $n$-th root with $n$ odd. The extensions are separable, and the generic fiber has exactly the group order, which is also the degree over the full fixed field. The resulting field equality descends along the finite separable Fourier splitting field. For example, base change of invariant polynomial spaces follows by writing the spaces as simultaneous kernels of linear differences, and the rational fixed field is the fraction field of the invariant polynomials by clearing denominators with an orbit product.

## Sharp odd modular dihedral moment cutoffs

Let $K$ be an infinite field of odd characteristic $p$ and suppose $p\mid n$. For the natural action of the order-$2n$ group $D_n$, use the unnormalized group-sum tensors
$$
 T_d(x)=\sum_{g\in D_n}(gx)^{\otimes d}.
$$
The entries through order three generate the invariant field for every $n\ne3$, and three is the exact generic geometric separation cutoff. For $n=p=3$ the cutoff is exactly four. This answers the odd modular part of the question about polynomial invariant tensors. [Edidin and Katz, §5.2](https://arxiv.org/html/2408.09599v4#S5.SS2)

### Group-algebra form of the data

Write $X(z)=\sum_{i=0}^{n-1}x_i z^i$ in $K[z]/(z^n-1)$, and let $X^*(z)=X(z^{-1})$. Rotation multiplies $X$ by $z$, and reflection is $*$. Orders one and two give $X(1)$ and $XX^*$, since the coefficient of $z^r$ in $XX^*$ is $\sum_i x_i x_{i+r}$, and the group-sum coefficient is twice this. The order-three entries at positions $(0,i,j)$ are the coefficients of
$$
 A+B,\qquad A=X(z)X(w)X((zw)^{-1}),\quad
 B=X(z^{-1})X(w^{-1})X(zw).
$$
For example the rotation sum at $(0,i,j)$ is $\sum_l x_lx_{l+i}x_{l+j}$, which is the coefficient of $z^i w^j$ in $A$; reflection adds the coefficient from $B$. For an invertible group-algebra element $F$, put $\delta F=F(z)F(w)/F(zw)$. On the generic locus all relevant $X$'s are units. For a candidate $Y$ with the same data, set $U=Y/X$ and $R=X^*/X$. The quadratic data give $UU^*=1$. Comparing the cubic data, with $\nu=\delta U$, gives the equation
$$
 (\nu-1)(\nu-\delta R)=0. \tag{1}
$$

### The prime-power calculation

Put $n=q=p^r\ge5$. Use coordinates $z=1+T,\ w=1+W$, so the one-variable ring is $K[T]/(T^q)$ and the two-variable ring is $K[T,W]/(T^q,W^q)$. Write $T\oplus W=T+W+TW$. Work with $X(1)\ne0$. There is a unique square root $E$ of $XX^*$ with constant term $X(1)$, found by triangular coefficient recursion since $2X(1)\ne0$. Uniqueness gives $E^*=E$. Set $F=X/E$. It has constant term one and satisfies $FF^*=1$. Dividing the cubic data by $E(z)E(w)E(zw)$ gives $V+V^{-1}$ for $V=\delta F$. Since $V(0,0)=1$, the Cayley transform $J=(V-1)/(V+1)$ is defined and these data are equivalent to knowing $J^2$. Indeed $V+V^{-1}=2(1+J^2)/(1-J^2)$.

We use the following description of the first nonzero homogeneous term of $\delta H-1$ for any $H(0)=1,\ HH^*=1$. Characters are the elements $(1+T)^e$, with $e$ an integer modulo $q$. If $H$ is a character then $\delta H=1$. Otherwise its leading discrepancy is a nonzero scalar times one of
$$
 L_k(T,W)=T^k+W^k-(T+W)^k
 \quad(3\le k\le q-2,\ k\text{ odd and not a }p\text{-power}),
$$
$$
 C_p(T^{p^s},W^{p^s})
 \quad(0\le s<r),\qquad
 C_p(T,W)=\sum_{i=1}^{p-1}\frac{T^iW^{p-i}}{i!(p-i)!}.
 \tag{2}
$$
To prove this, repeatedly remove an actual character when the first nonconstant term is $aT^{p^s}$ with $a\in\mathbb F_p$, using $(1+T)^{a p^s}$ with $a$ interpreted as an integer representative. This does not change $\delta H$, and it raises the first possible nonzero degree. If the first remaining term is $aT^k$ with $k$ not a $p$-power, the norm equation and $T^*=-T/(1+T)$ force $k$ odd, and the leading discrepancy is $aL_k$. The polynomial $L_k$ is nonzero for such $k$: if $k=\sum k_jp^j$, the expansion of $(1+T)^k$ as $\prod(1+T^{p^j})^{k_j}$ contains a nonzero intermediate coefficient unless $k$ is a $p$-power.

If instead the leading term is $aT^k$ with $k=p^s$ and $a\notin\mathbb F_p$, compare with the truncated binomial $\sum_{i=0}^{p-1}\binom ai T^{ki}$. Its norm is one through degree $kp-1$. Its leading multiplicative discrepancy is of total degree $kp$ and equals $(a^p-a)C_p(T^k,W^k)$. To see this, first take $k=1$. The formal binomial identity through degrees less than $p$ is valid modulo $p$ because its denominators are invertible. At total degree $p$ and at mixed exponent $i,p-i$, the omitted term $\binom ap(T+W+TW)^p$ contributes
$\prod_{j=0}^{p-1}(a-j)/(i!(p-i)!)$, whose reduction is the displayed coefficient. This argument uses formal identities over the localization of $\mathbb Z[a]$ at integers prime to $p$, since the mixed coefficient has that displayed invertible denominator. Substitute $T^k,W^k$ and use $(T\oplus W)^k=T^k\oplus W^k$. A first discrepancy of the ratio from this model in a degree strictly between $k$ and $kp$ has odd degree by the norm condition, and cannot be a $p$-power. It contributes the first type in (2). A discrepancy at degree $kp$, if present, contributes zero at that degree since $kp$ is a $p$-power. Higher discrepancies cannot affect the leading term. This proves (2).

Generically the leading term of $J$ is a nonzero multiple of $P=TW(T+W)$. For $p\ge5$, no discrepancy has degree less than three and $L_3=-3P$; a nonzero cubic parameter is realized by the norm-one element $(1+cT^3)/(1+c(T^*)^3)$. For $p=3$ and $q\ge9$, the degree-three discrepancy is a multiple of $C_3(T,W)=P/2$ with scalar $a^3-a$, where $a$ is the linear coefficient of $F$. This scalar is generically nonzero because $a$ varies freely on the norm-one units, as seen by using $(1+cT)/(1+cT^*)$.

The product of $P$ with every possible leader in (2) is nonzero in $K[T,W]/(T^q,W^q)$. If the product has total degree less than $q$ this is immediate. For $L_{q-2}$, the coefficient of $T^{q-2}W^3$ is, up to sign, $k+\binom k2=k(k+1)/2$ with $k=q-2$, which is nonzero in odd characteristic. For a second-type leader of degree $q$ with $r=1$, $p=q\ge5$. The coefficient of $T^4W^{p-1}$ is $c_2+c_3=c_2/3\ne0$, with $c_i=1/(i!(p-i)!)$, and both exponents are below $p$. If $r>1$, take the term $T^{p^{r-1}}W^{(p-1)p^{r-1}}$ and multiply it by $TW^2$. Both exponents are below $q$ since $p^{r-1}\ge3$, and their residues modulo $p^{r-1}$ distinguish this contribution from multiplication by $T^2W$. Second-type leaders below degree $q$ have degree at most $q/p$, whose sum with three is below $q$ in the applicable cases.

Now let $F'$ be a candidate, with Cayley transform $J'$. Because $P^2$ survives in the truncated ring, equality $J'^2=J^2$ determines the leading scalar of $J'$ up to sign. Reflect the candidate if needed to make the scalars equal. The leading term of $J'+J$ is then twice that of $J$. If $H=F'/F$ is not a character, the leading term of $J'-J$ is a nonzero scalar times the leader of $\delta H-1$: the difference of the Cayley transforms is $2(V'-V)/((V'+1)(V+1))$. By the product calculation, $(J'-J)(J'+J)\ne0$, a contradiction. Hence $H$ is a character, which is exactly the rotation ambiguity. This proves cubic separation for $q\ge5$.

The same argument gives an injective differential. Over dual numbers a tangent candidate replaces $F$ by $F(1+\varepsilon h)$ with $h(0)=0$ and $h+h^*=0$. The leader classification still applies to a nonzero $h$, with its leading scalar carried by $\varepsilon$. There are no nonzero removable scalar characters, and in the binomial step the coefficient $(\varepsilon a)^p-\varepsilon a=-\varepsilon a$ is nonzero. The nonzero product above contradicts equality of squares to first order. The square root $E$ was determined by the quadratic data, so the differential kernel of the full moment map is zero.

### Adding the prime-to-characteristic factor

Write $n=q m$, where $q=p^r$, $p\nmid m$. Work in a splitting field of $z^m-1$, with local coordinates $z=\eta(1+T)$ at $\eta\in\mu_m$. Each component is $K[T]/(T^q)$, and multiplication of two local arguments takes $(\eta,T),(\theta,W)$ to $(\eta\theta,T\oplus W)$. Use subscripts $\eta$ for local components and write $L_F=(1+T)(\partial_TF)/F$ for the logarithmic derivative of a unit. We use the open conditions that $L_{R_1}(0)\ne L_{R_\eta}(0)$ for $\eta\ne1$, and each normalized $R_\eta/R_\eta(0)$ is not a local character. These are generic. The linear coefficient of $R_\eta=X^*_\eta/X_\eta$ depends on the independent coefficients at the roots $\eta,\eta^{-1}$, and at a self-inverse root it is minus twice the normalized linear coefficient of $X_\eta$. Each can thus avoid the finitely many character values, and the coefficient at $1$ can vary independently from any other inversion pair. We also retain the prime-power open condition that $\delta R_1-1$ has a nonzero degree-three term for $q\ge5$, which follows from the calculation for $F$ since $R_1=F^{-2}$.

For $q\ge5$, the prime-power calculation in the component at $1$ lets us reflect and rotate the candidate so that $U_1=1$. On the component $(\eta,1)$, both $\nu-1$ and $\delta R-1$ are divisible by $W$. After canceling the two explicit powers of $W$ in (1), work modulo $W^{q-2}$. The divided factors differ by a unit because the coefficient of $W$ in $\delta R-1$ has nonzero constant term at $T=0$. Since this is a local ring, one factor must be a unit and the other must vanish. Thus $\nu\equiv1$ or $\nu\equiv\delta R\bmod W^{q-1}$. The first congruence gives $U_\eta(T\oplus W)=U_\eta(T)\bmod W^{q-1}$. By setting $T=0$, the only possible nonconstant term in $U_\eta$ is $aT^{q-1}$, and the coefficient of $W$ in the congruence then forces $a=0$. For the second congruence put $H_\eta=U_\eta/R_\eta$. It says $H_\eta(T)/H_\eta(T\oplus W)=R_1(W)\bmod W^{q-1}$. At $T=0$ this identifies $H_\eta(W)$ with $H_\eta(0)/R_1(W)$ through degree $q-2$. Substituting that information back through total degree three forces $R_1(T\oplus W)=R_1(T)R_1(W)$ through that degree, contradicting the generic degree-three term. Thus each $U_\eta$ is constant.

For $q=3$ and $m\ge2$, apply the same divided-factor calculation at $(\eta,1)$ for $\eta\ne1$, without first normalizing $U_1$. Write $d=L_{U_1}(0)$, $r_0=L_{R_1}(0)$. Comparison of the coefficients of $W$ now gives one of the two exact one-variable identities
$$
 L_{U_\eta}=d,\qquad L_{U_\eta/R_\eta}=d-r_0.
$$
The derivation $(1+T)\partial_T$ on the local ring is diagonal on the basis $(1+T)^j$, $j=0,1,2$, with eigenvalues $0,1,2$. A unit with constant logarithmic derivative is therefore a scalar times one of these characters, and its logarithmic derivative lies in $\mathbb F_3$. Generically $r_0\notin\mathbb F_3$, so the two kinds of identities cannot occur for different $\eta$. In the first case all the $U_\eta$'s away from $1$ are scalar times one common character. In the second, all the $U_\eta/R_\eta$'s have this property. At $1$, either $U_1$ or $U_1/R_1$ respectively has constant term one and norm one. Such a length-three unit is determined by its linear coefficient: the quadratic coefficient is forced by multiplying by its star. It is therefore the same character at $1$. Replacing $X$ by $X^*$ in the second case and rotating the candidate in either case reduces again to constant $U_\eta$'s.

With $U_\eta=c_\eta$, on any component $(\eta,\theta)$ the value of $\nu=c_\eta c_\theta/c_{\eta\theta}$ is a nonzero constant. Equation (1) forces $\nu=1$ unless $\delta R$ is constant on that component. In the latter event, after dividing each local $R_\eta$ by its constant, setting $T=0$ and $W=0$ identifies the three normalized units at $\eta,\theta,\eta\theta$ and makes their common value multiplicative under $\oplus$. Such a group-like unit is a character: expanding in the basis $(1+T)^j$, $0\le j<q$, the multiplicativity identity has only diagonal terms on its comultiplication side and forces exactly one coefficient to be one, all others zero. This contradicts the generic condition. Thus the $c_\eta$ form a character of $\mu_m$, and the Chinese remainder theorem realizes it by a rotation whose exponent is zero modulo $q$. Cubic separation follows for all $n\ne3$ in the claimed range.

For completeness the moment map is also separable in the mixed case. Write a tangent candidate as $U=1+\varepsilon h$. For $q\ge5$ the root-$1$ calculation gives $h_1=0$. On $(\eta,1)$ the divided second factor of (1) is a unit modulo $W^{q-2}$ by the same nonzero derivative condition, so the first factor vanishes there. For $q\ge5$ the first-branch argument gives $h_\eta$ constant. For $q=3$ it gives $(1+T)\partial_T h_\eta=((1+T)\partial_T h_1)(0)$ for every $\eta\ne1$. The diagonal derivative on the character basis has image with zero coefficient at the constant character. Therefore the common right-hand side is zero and the $h_\eta$ are constant. At $1$ the tangent norm condition and the vanishing linear coefficient then give $h_1=0$. Finally (1) with constant $h_\eta$'s and nonconstant $\delta R$ forces $h_{\eta\theta}=h_\eta+h_\theta$ for every pair. The additive group has no nonzero $m$-torsion, so these constants vanish. This proves injectivity of the differential.

The rational field extension induced by the moment entries is finite by geometric generic separation, and separable by the differential calculation. Its degree is consequently the size of the generic geometric fiber, which is $2n$, the degree over the fixed field. Thus the moment-data field equals the fixed field. Formation of invariant polynomial spaces and of polynomial spaces spanned by moment entries commutes with scalar extension, because their defining equations are linear over the original field. Taking fraction fields, and clearing an invariant denominator by an orbit product for rational invariants, descends the equality from the finite splitting field to $K$.

### Sharpness and the modular triangle

The quadratic information has transcendence degree at most $\lfloor n/2\rfloor+1<n$, because $XX^*$ is fixed by star and $X(1)^2=(XX^*)(1)$. Therefore degree two does not even give a finite generic fiber. For $n=p=3$ the group is $S_3$. Write $e_i$ for the elementary symmetric polynomials and $p_j$ for the sums of $j$-th powers. Orders one and two recover $e_1,e_2$, and cubic traces add nothing: the possible monomial types give $2p_3=2e_1^3$, $e_1e_2-3e_3=e_1e_2$, and $6e_3=0$. Order four includes the trace of $x_1^3x_2$, namely $p_3p_1-p_4=e_2p_2-e_1e_3$ by Newton's identities. This recovers $e_3$ generically, establishing the sharp cutoff and field generation also in this case.
