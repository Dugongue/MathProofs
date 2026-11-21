# Coprime determinant descent and an ordinary tensor reduction for noncyclic norms

## Determinant norm transfer over finite fields

Let $F=\mathbf F_q$, let $H$ be a linear algebraic group over $F$, and take its reduced subgroup, which has the same points over all finite extensions. Let $H^\circ$ be its geometric identity component and $\Gamma$ the finite group of geometric components. Write $\Phi$ for Frobenius and $\sigma$ for its action on $\Gamma$. Let $\delta:H\to\mathbf G_m^r$ be an $F$-defined homomorphism, such as the three determinant characters of a tensor stabilizer.

**Theorem.** For $k\ge1$ and $B=\Gamma^{\sigma^k}$, if $\gcd(k,|B|)=1$ or $\gcd(k,\operatorname{ord}\sigma)=1$, then
$$
N_{\mathbf F_{q^k}/\mathbf F_q}\big(\delta(H(\mathbf F_{q^k}))\big)
 \subseteq \delta(H(\mathbf F_q)),
$$
with entrywise norms. In particular, if a prescribed tuple $d\in(F^\times)^r$ of order prime to $k$ is attained over $\mathbf F_{q^k}$, it is attained over $F$. For this membership conclusion it also suffices that $\Gamma$ have a normal Hall subgroup for the primes dividing the order of $d$.

For a tensor pair ordinarily isomorphic over $F$, apply this to the general-linear stabilizer of the source and the inverse determinant tuple of any chosen rational ordinary transporter. The special-linear question is exactly membership of that tuple.

For a connected group and $x\in H(\mathbf F_{q^k})$ put $y=x\Phi(x)\cdots\Phi^{k-1}(x)$. Then $\Phi(y)=x^{-1}yx$. Lang gives $z\in H(\overline F)$ with $\Phi(z)=zx$, so $zyz^{-1}$ is rational. Its $\delta$ value is the field norm of $\delta(x)$, since $\delta$ has abelian target and is defined over $F$. This is the determinant consequence of Shintani normalization. Also, every geometric component fixed by a Frobenius power contains a rational point over the corresponding field. For any point $u$ of that component, $u^{-1}\Phi^j(u)\in H^\circ$, and Lang on the connected group adjusts $u$ to a fixed point. [Lang, Algebraic Groups over Finite Fields](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf), [Shintani, finite general linear groups](https://www.jstage.jst.go.jp/article/jmath1948/28/2/28_2_396/_pdf)

Let $x\in H(\mathbf F_{q^k})$ have component $\gamma\in B$. If $\gcd(k,\operatorname{ord}\sigma)=1$, then $\gamma$ is $\sigma$-fixed. Choose $h\in H(F)$ in that component and apply the connected result to $xh^{-1}$, then multiply its rational determinant by $\delta(h)^k$.

If $\gcd(k,|B|)=1$, form the semidirect product $B\rtimes C_k$ with generator $\tau$ acting by $\sigma$. The element $\gamma\tau$ has order $ke_0$ for $e_0\mid |B|$. Choose $a\equiv1\bmod k$ and $a\equiv0\bmod e_0$. The element $(\gamma\tau)^a$ has order $k$, projects to $\tau$, and generates a complement to $B$. Schur–Zassenhaus, using the solvable cyclic quotient, conjugates this complement by $b\in B$ to the displayed $C_k$. The remaining factor $(\gamma\tau)((\gamma\tau)^a)^{-1}$ lies in $B$ and commutes with the complement generator. After this same conjugation it is $\eta\in B^\sigma$, so $b^{-1}\gamma\sigma(b)=\eta$. [Kurzweil and Stellmacher, Theorem 6.2.1](https://theory.uchicago.edu/~sethi/Teaching/P342-W2017/Kurzweil-Stellmacher_Theory%20of%20finite%20groups.pdf)

Lift $b$ to $v\in H(\mathbf F_{q^k})$ and $\eta$ to $h\in H(F)$ by Lang on components. The element $x'=v^{-1}x\Phi(v)$ is in the component of $h$. Its $\delta$ norm equals that of $x$, since the norm of $\Phi(\delta(v))/\delta(v)$ equals one. The connected result for $x'h^{-1}$, followed by multiplication by $\delta(h)^k$, gives the inclusion.

If $\delta(x)=d$ is rational, then its norm equals $d^k$, and taking a power inverse to $k$ modulo the order attains $d$. For the Hall claim let $\Pi$ be the set of prime divisors of the order of $d$, and $P$ the normal Hall $\Pi$ subgroup. It is unique and Frobenius-stable. Raise $x$ to the prime-to-$\Pi$ part $c_0$ of its component order. Its new component is a $\Pi$ element, hence belongs to $P$. Run the semidirect-product proof in $P^{\sigma^k}$, whose order is prime to $k$. Its lifts still lie in $H$. The rational determinant attained is $d^{c_0k}$, and the exponent is invertible modulo the order of $d$.

Over $\mathbf F_3$ the correction tuple has order at most two. If $\Gamma$ has a normal Sylow two-subgroup, odd-degree extensions preserve the answer. More generally a solution at degree $2^a b$ with $b$ odd descends to degree $2^a$ using the same correction tuple in that intermediate field. The exact spectrum is consequently empty or the multiples of one power of two. This works even with disconnected general-linear stabilizers.

In general let $m$ be the least successful degree if a solution exists. For a prime $\ell\mid m$ outside the order of the original correction tuple, apply the theorem from degree $m$ to degree $m/\ell$. It descends if $\ell$ does not divide $|\Gamma|$. It also descends if $v_\ell(m)>v_\ell(\operatorname{ord}\sigma)$ since $\sigma^{m/\ell}$ then has order prime to $\ell$. Either descent contradicts minimality. In particular over $\mathbf F_3$ the odd part of $m$ divides the odd part of $\operatorname{ord}\sigma$, with primes dividing $|\Gamma|$.

## Exact connected spectra and closed pencil examples

For connected $H$ over a finite field, pass to the reductive quotient by the unipotent radical, then to the torus quotient by the derived group. Both kernels are smooth connected, and the characters factor through the torus $T$. Its invariant sublattice $X^*(T)^\sigma$ is saturated since the character lattice is torsion-free. The torus with that invariant character lattice is the maximal split quotient $S$ of $T$, with connected torus kernel. Every base-defined character factors through this same $S$, and Lang gives surjectivity of the composite map on points over every finite extension. No larger splitting field or recomputation of fixed lattices is needed for the fixed base characters. This uses the ordinary finite-field torus and reductive group structure. [Milne, Reductive Groups, §§9 and 17](https://www.jmilne.org/math/CourseNotes/RG.pdf)

In Smith coordinates for the resulting integer exponent matrix, test the target against powers $s_i>0$ in $\mathbf F_{q^k}^\times$. A transformed target $b_i$ passes precisely if
$$
\operatorname{ord}(b_i)\mid\frac{q^k-1}{\gcd(q^k-1,s_i)}.
$$
Rows with no nonzero exponent require target $1$. Over $\mathbf F_3$, let $b$ be the largest $v_2(s_i)$ on nonzero rows with target $-1$. If there is no such row or $b=0$, all degrees work once zero rows pass. Otherwise exactly the multiples of $2^{\max(1,b-1)}$ work. In fact the power image contains $-1$ iff $v_2(3^k-1)>b$. The valuation is one for odd $k$ and $2+v_2(k)$ for even $k$, by successive squaring from $3^2-1=8$ and the odd geometric sum for an odd exponent. This is an exact spectrum calculation from the supplied exponent matrix. It is also a polynomial arithmetic decision with that matrix and the target as data, without claiming to extract the matrix from unrestricted tensors.

All these powers of two occur for full-support pencils with connected geometric general-linear stabilizers and closed geometric special-linear orbits. For desired minimum $2^a$ with $a\ge1$, take label dimension $r=2^{a+1}$. For minimum one, take odd $r\ge3$. Let $A(x)$ have diagonal scalar blocks on $x_1,\ldots,x_r,\sum_i x_i$, with distinct multiplicities initially $w_i=4r^2+i$. Increase the last by a number in $[0,r-1]$ so that $r$ divides the total row dimension $N$. The weights stay distinct and $\max_i w_i<N/r$.

An ordinary automorphism $A(fx)g=hA(x)$ fixes every factor line in the slice determinant by distinct multiplicities. Hence $f=\lambda I_r$. Choose an invertible slice and normalize the others by it. This gives diagonal matrices with distinct joint eigenvalue tuples on the distinct blocks. The ordered action is therefore exactly block-diagonal $g$ and $h=\lambda g$. The geometric general-linear stabilizer is isomorphic as a variety to $\mathbf G_m\times\prod_i \mathrm{GL}_{w_i}$, and is connected.

Put $c=-1$ and choose rational $f_0,h_0$ with determinants $c^{-1},c^{-N/r}$. Set $B(x)=h_0A(f_0^{-1}x)$. The pair has ordinary transporter $(f_0,I,h_0)$. Special-linear correction requires $\lambda^r=c$, from the label determinant. It suffices by taking the source automorphism $(\lambda I_r,I,\lambda I_N)$. The formula for the two-adic valuation of $3^k-1$ shows that the minimum is exactly $2^a$ for the chosen $r$, and odd $r$ allows $\lambda=c$ over the base field.

For closedness, every proper $d$-dimensional subspace of the label dual has at most $d$ form lines because they form a projective frame. Its total weight is therefore strictly smaller than $dN/r$. In a valuation degeneration take a Smith form of the generic label matrix with integral invertible outer matrices and exponents $\gamma_1\le\cdots\le\gamma_r$ of sum zero. For each form let $a_i$ be the minimum valuation of its transformed coefficients. The integral determinant polynomial gives $\sum_i w_i a_i\ge0$, since the product of the primitive reduced linear factors is nonzero. The first unit coordinate of a primitive form in the reduced first Smith basis bounds $a_i$ by its corresponding $\gamma_j$. Summing these upper bounds yields
$$
N\gamma_1+\sum_{j=1}^{r-1}(\gamma_{j+1}-\gamma_j)
 \sum_{i: \,L_i\in W_j} w_i ,
$$
where $W_j$ is the subspace with first $j$ coordinates zero in that reduced basis. By the strict weight bound this is less than $(N/r)\sum_j\gamma_j=0$ if a gap exists. Hence the label matrix is integral special-linear.

Undo the label matrix and choose a constant invertible slice. The transported invertible slice has unit determinant and integral inverse. Normalizing by the respective invertible slices leaves a simultaneous conjugacy of constant diagonal tuples with distinct joint eigenvalues. Interpolation on these eigenvalue tuples gives integral projectors of the transported matrices. Their free images and the direct sum decomposition give integral conjugating bases. Rescaling one column by a unit makes the conjugator special-linear. The other matrix is fixed by the chosen slice and also has determinant one. Thus every valuation degeneration stays in the orbit, proving closedness over the algebraic closure. [Stacks Project, discrete valuation specialization, Tag 054F](https://stacks.math.columbia.edu/tag/054F)

The earlier graph pencils have geometric general-linear component group equal to the graph group: each permitted permutation has connected fibre consisting of a scalar and the ordered block units. Frobenius acts on those components by conjugation by the collective rotation. The generalized dihedral group with nontrivial odd rotation part has nonnormal Sylow two-subgroups, consistent with its odd-degree spectrum. The earlier Frobenius-component spectrum uses the stabilizer of the action actually being tested. Connectedness of the general-linear stabilizer cannot be substituted for connectedness of the determinant kernel. The closed weighted-frame examples show this distinction without relying on a null-cone example.

## A relative norm compiler over the original field

Let $E/K$ be finite separable of degree $n$ and $c\in K^\times$. Suppose one has an explicitly represented nonzero finite commutative unital $K$-algebra $S$ and unital $K$-algebra maps $\iota_1,\ldots,\iota_n:E\to S$ with
$$
\prod_j\iota_j(u)=N_{E/K}(u)\,1_S\qquad(u\in E).
$$
For example take all embeddings into a supplied common splitting field. There is a deterministic polynomial-size reduction of the relative norm equation to one ordinary tensor isomorphism instance over $K$. Neither cyclicity nor normality of $E/K$ is required.

Take a space $W$ with one block $E$, one block $V_j=S$ for each embedding, and prefix blocks $P_0,\ldots,P_n$ each equal to $S$. Use a tag space $D$ with one basis index for each block projector on $W$ and for multiplication by every displayed basis element on each block, extended by zero outside that block. Give $D$ a fixed cyclic nilpotent shift $J$ and its cyclic first vector $\eta$. The bilinear map $D\times W\to W$ with the indicated operator slices is the third fixed tensor. Preserving $J,\eta$ fixes the entire tag basis. Hence a transporter on $W$ commutes with all its specified operators. The projectors make it block diagonal. On a commutative algebra block any such map is multiplication by its own value at one, by commuting with every regular multiplier. Invertibility makes this value a unit, and conversely every unit multiplication meets these requirements.

Include one linear operator $I$ on $W$ whose nonzero blocks from $E$ to $V_j$ are the maps $\iota_j$. Commutation forces the unit on $V_j$ to be $\iota_j(u)$ where $u$ is the unit on $E$. Include one bilinear map on $W$ whose block on $P_{j-1}\times V_j$ is multiplication in $S$ into $P_j$. Equivariance says exactly $w_j=w_{j-1}\iota_j(u)$ for the prefix units. Necessity follows at $(1,1)$, and sufficiency on the whole block follows by commutativity. A marked vector has entries $1,1$ on the source $P_0,P_n$ and $1,c\,1_S$ on the target. Its equation enforces the desired norm. Conversely a unit of that norm supplies all maps, by forming the indicated prefix products. Since $S$ is a nonzero unital algebra over the field $K$, equality of its scalar entries gives equality in $K$.

There are six ordered tensors of order at most three: $J,\eta$, the operator slice map, $I$, the prefix map, and the marked vector. Their dimensions are polynomial in the supplied data. The number of ordered tensor objects is independent of the number of field embeddings, so the constant-size tensor-system compiler converts this system into a single ordinary three-tensor pair with polynomial dimensions. Dual and repeated appearances of $W$ are linked in that compiler. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1 and the Futorny–Grochow–Sergeichuk compiler](https://arxiv.org/html/2306.03135v2)

## Explicit cubic and bounded-step tower reductions

For a separable monic presentation $E=K[X]/(f)$, build a finite free splitting algebra by adjoining one root, dividing monically by its linear factor, adjoining a root of the remaining quotient, and continuing. At every stage this is a monic quotient and admits an explicit basis. Over the algebraic closure, the Chinese remainder theorem inductively identifies the final algebra with the product indexed by the $n!$ orders of the distinct roots. Sending the original generator to each of the $n$ adjoined roots gives the required unital maps. On every geometric factor the product evaluates to the full original norm, hence the equality holds over $K$. No factoring occurs. The resulting algebra can be a product, which the compiler allows.

In particular for a separable cubic $f=X^3+a_2X^2+a_1X+a_0$, use
$$
S=E[\beta]/\big(f(X)/(X-\alpha)\big),
$$
with $\alpha$ the given root in $E$. Here $\beta$ denotes the class of the variable in the displayed monic quadratic quotient. The three roots in $S$ are $\alpha,\beta,-a_2-\alpha-\beta$. This is dimension six over $K$ and works in characteristic two as well. The relative norm for every presented separable cubic therefore reduces to ordinary TI, including non-Galois cubics. For rational coefficients the bit complexity is polynomial, since all construction dimensions and the number of auxiliary arithmetic operations are bounded for the fixed degree. The same bounded-size observation applies to any fixed separable degree.

For an explicit tower $K=K_0\subset\cdots\subset K_t=E$ of separable monic step presentations of degrees $d_\nu\le d$, use a splitting algebra $S_\nu$ of rank $d_\nu!$ over $K_{\nu-1}$ at each step. Regard every such algebra as a $K$-algebra. Introduce a block for each $K_\nu$ and the embedding and prefix blocks for each $S_\nu$. In the one operator $I$ also put the natural inclusion from the $K_{\nu-1}$ block to the last prefix block for step $\nu$. This forces equality of terminal prefix and embedded lower unit. Put all multiplication recurrences into the same prefix map and mark all first prefix entries $1$, as well as $1$ going to $c$ in $K_0$. These equations are exactly
$$
N_{K_\nu/K_{\nu-1}}(u_\nu)=u_{\nu-1}\quad(1\le \nu\le t),\qquad u_0=c .
$$
Their composition is the original norm. Conversely a unit of that norm gives the lower units by successive norms and all auxiliary units by prefix products. The degrees of the auxiliary algebras over $K$ are bounded by $d!\,[E:K]$, and explicit tables and tensor sizes are polynomial in the tower data and $d!$. In particular bounded-degree towers are polynomial in the arithmetic model, and also in bit time over explicitly represented finite fields. With explicit step tables, this avoids building the full normal closure even if its degree is much larger.

The fixed-size and tower cases are distinct from taking a larger field norm while keeping the target fixed. Each conjugate embedding acts on the same original upper unit, and each tower recurrence uses the correct relative norm. The generic factorial bound for an unrestricted step remains. No arbitrary-small splitting table, universal norm compiler, or reduction for all determinant-constrained tensors is asserted.

## Products of norms and coprime descent over arbitrary fields

The same constant-signature compiler decides systems of signed norm-product equations over $K$. Given independent field units $u_i\in E_i^\times$, supported norm data for each $E_i/K$ as above, binary integers $e_{ji}$ of either sign, and targets $c_j\in K^\times$, the system is
$$
\prod_i N_{E_i/K}(u_i)^{e_{ji}}=c_j \qquad\text{for every }j.
$$
Keep one $K$-unit block for each norm value, tying it to the final prefix from its relative norm computation by the scalar inclusion in $I$. Add $K$-blocks for the prescribed products and powers. A multiplication equation on three slots is enforced by a single product block of the same prefix multiplication tensor. Reuse a slot in both inputs to enforce a square. For a negative exponent first require an inverse slot by multiplication into a block marked to equal one, then apply binary powering to the absolute exponent. Positive powers are repeated squares and products, and exponent zero can be omitted. Prefix products are anchored at one and their final values are marked by the corresponding $c_j$. Use distinct slots for the independently marked values. For a row with no active factors, check $c_j=1$ directly. If one ordered input pair contributes to several multiplication equations, give the multiplication map those different output blocks. Blockwise equivariance enforces each output equation independently.

There are at most a constant times the total binary exponent bit length plus the number of equations and norm slots many extra blocks. The field scalars in added constraints are only the written targets and fixed small constants. No numerical exponentiation of coefficients by the given exponents takes place. This gives one ordinary-TI instance for the entire system and a polynomial arithmetic bound in the explicit norm data and exponent bit lengths. For bounded-degree rational tower steps with explicit multiplication tables over $\mathbf Q$ and inclusion matrices, the auxiliary splitting tables are obtained by a bounded number, dependent only on the degree bound, of algebra operations per entry over the tabulated lower field. Written coefficient bit lengths of the auxiliary tensors are polynomial in these explicit tables and the exponent/input bit lengths. The arithmetic-model theorem does not assume a bit bound for expanding a succinct tower whose lower fields are supplied only implicitly.

A separate arithmetic descent statement holds over any ground field $K$. Let $E/K$ be finite separable of degree $n$, and let $L/K$ be any finite field extension of degree $k$. Put $B=E\otimes_K L$. If $c\in K^\times$ is attained by the relative norm $N_{B/L}$ on $B^\times$, then $c^k$ is attained by $N_{E/K}$. Indeed $B$ is a finite étale algebra over $L$, hence a product of fields, and each factor is also a finite extension of the embedded $E$. For $u\in B^\times$, transitivity of field norms in each factor and multiplication over the factors give
$$
N_{E/K}\big(N_{B/E}(u)\big)
 =N_{B/K}(u)
 =N_{L/K}\big(N_{B/L}(u)\big).
$$
If the last inner norm is $c$ then the right side is $c^k$. Field-norm transitivity holds also for inseparable finite extensions. The class of $c$ modulo $N_{E/K}(E^\times)$ has order dividing $n$, since $N_{E/K}(c)=c^n$. Thus if $\gcd(k,n)=1$, norm membership over $L$ implies norm membership over $K$. The converse holds for every $k$ by determinant base change. This proof does not replace the original relative norm by a norm from a normal closure.

These are paper proofs. The coprime and Hall theorems give positive descent regimes despite the known large odd-extension spectra. The norm result settles noncyclic and bounded-step instances without presuming either an unrestricted tensor-class collapse or its negation.
