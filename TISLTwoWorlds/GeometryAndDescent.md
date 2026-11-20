# Closed-orbit descent spectra and conditional separations for special-linear tensor isomorphism

## A prescribed extension spectrum on closed orbits

Fix $F=\mathbf F_3$. Let $p_1,\ldots,p_s$ be any nonempty list of distinct odd primes, and put
$$
A=\prod_{i=1}^s \mathbf F_{3^{p_i}},\qquad n=\sum_i p_i.
$$
Use displayed $F$-bases for the factors and concatenate them. Let $T$ be the multiplication bimap on $A$. Choose a linear map $J:A\to A$ of determinant $-1$ in this basis, for example the matrix that negates its first coordinate, and let $U=J\circ T$.

The two tensors are ordinarily isomorphic already over $F$. Their geometric special-linear orbits over $\overline F$ are closed and equal. Their exact rational extension spectrum is
$$
T\cong_{\mathrm{SL},\,\mathbf F_{3^k}} U
\quad\Longleftrightarrow\quad
p_i\mid k\ \text{for at least one }i.
$$
Thus the minimum extension degree can be an arbitrarily large odd prime, despite the geometric orbit being closed and despite a given rational ordinary transporter. The tensors are full-support, since the algebra has a unit and its multiplication values span it. Multiplication tables for these fields can be constructed deterministically in time polynomial in $\sum_i p_i$ over $F$, by constructing irreducible polynomials and multiplying modulo them. The same mathematical conclusions hold over any odd finite field with $3$ replaced by its order. [Shoup, deterministic irreducible polynomial construction in small characteristic](https://www.shoup.net/papers/detirred.pdf)

### The determinant and field calculation

Use transporter convention $U(Px,Qy)=R T(x,y)$. In this convention the transporters of a unital associative multiplication to itself have exactly the form
$$
P=L_a\phi,\qquad Q=R_b\phi,\qquad R=L_aR_b\phi
$$
for units $a,b$ and an algebra automorphism $\phi$. Indeed, put $a=P(1)$ and $b=Q(1)$. The equations with one argument $1$ imply that the two corresponding left and right multiplications are invertible, hence $a,b$ are units. Then $\phi(x)=a^{-1}R(x)b^{-1}$ is unital and multiplicative by the full bimap equation. Conversely the displayed triple preserves multiplication with the specified handedness.

For any scalar extension let $d=\det\phi$ and let $N(a),N(b)$ be the determinants of multiplication by the corresponding units. The fixed transporter $(I,I,J)$ from $T$ to $U$, composed on the right with the displayed automorphism, gives the determinant triple
$$
\big(N(a)d,\ N(b)d,\ -N(a)N(b)d\big).
$$
The first two entries are both $1$ precisely when $N(a)=N(b)=d^{-1}$. With those values the third is $-d^{-1}$, which is $1$ exactly when $d=-1$. Each finite scalar extension of $A$ is a product of finite fields. Its total multiplication norm onto the base field is surjective, since the norm on each finite field is a surjective power map by cyclicity. It follows that the three determinants can simultaneously be repaired exactly when the scalar-extended algebra has an automorphism of determinant $-1$. The same conclusion over the algebraic closure follows because the algebra there splits as a product of lines and multiplication norms are products of coordinates.

For a factor of degree $p_i$, base change to $\mathbf F_{3^k}$ splits it into $\gcd(p_i,k)$ field factors of relative degree $p_i/\gcd(p_i,k)$. One way to see this is to take the $p_i$ embeddings into $\overline F$, and group them into orbits for the $k$th power of Frobenius. Cycles of that permutation correspond to the simple finite-field factors. All relative degrees here are odd. A Frobenius automorphism of an odd-degree factor has determinant $+1$: over the algebraic closure it permutes primitive idempotents by a power of an odd cycle, so base-change invariance of determinant gives the result. Swapping two same-degree factors gives determinant $(-1)^e=-1$ for relative degree $e$ odd. If no $p_i$ divides $k$, there are no equal-degree factors and every automorphism is an internal Frobenius automorphism on each factor. If some $p_i$ divides $k$, its repeated factors supply an odd swap. This proves the spectrum. Over the algebraic closure a single transposition of two primitive idempotents suffices, so $T,U$ are geometrically special-linearly equivalent.

Exactly the same proof works for pairwise distinct odd degrees $d_i$ in place of the primes. The condition becomes $\gcd(d_i,k)>1$ for some $i$.

### Closedness of the diagonal tensor orbit in every characteristic

Let $K$ be algebraically closed, and let
$$
D_n=\sum_{i=1}^n e_i\otimes e_i\otimes e_i
$$
in the tensor product of three $n$-dimensional spaces. We prove that its orbit under the product of the three special-linear groups is Zariski closed. This argument does not require an analytic moment map.

Consider a discrete valuation ring $\mathcal O$ with uniformizer $\pi$ and fraction field $L$. Suppose a tensor $V\in\mathcal O^{n^3}$ lies in the orbit of $D_n$ over $L$, exhibited as
$$
V=\sum_i u_i\otimes v_i\otimes w_i,
$$
with the three column matrices each of determinant $1$. In the first mode write $u_i=\pi^{a_i}\widetilde u_i$ where $\widetilde u_i$ has integral coordinates and at least one coordinate a unit. Since $\det[u_i]=1$, the integer $\sum_i a_i$ is at most zero. On the other hand the determinant of the square slice obtained by contracting $V$ against a variable first-mode covector $x$ is
$$
\prod_i \langle x,u_i\rangle
 =\pi^{\sum_i a_i}\prod_i\langle x,\widetilde u_i\rangle.
$$
The determinants of the other two column matrices are $1$, so no further factor occurs. This polynomial is integral since the tensor is integral. The product of the primitive integral linear polynomials on the right has a unit coefficient, because their reductions are nonzero and the polynomial ring over the residue field is a domain. Thus $\sum_i a_i\ge0$. The sum is zero and the normalized first column matrix has determinant $1$ over $\mathcal O$.

The same argument in the other two modes writes $v_i=\pi^{b_i}\widetilde v_i$ and $w_i=\pi^{c_i}\widetilde w_i$, with each new column matrix in $\mathrm{SL}_n(\mathcal O)$ and $\sum_i b_i=\sum_i c_i=0$. Apply the inverses of these three integral matrices to $V$. The result is the diagonal tensor whose $i$th coefficient is $\pi^{a_i+b_i+c_i}$. All these exponents are nonnegative by integrality and sum to zero. They are therefore all zero. In particular the special tensor of any such specialization remains in the special-linear orbit.

To pass to Zariski closedness, if a $K$-point were in the boundary of the orbit closure, specialize the generic point of that irreducible closure to the boundary point along a discrete valuation ring. The generic fibre of the dominant orbit map from $\mathrm{SL}_n^3$ has a point over a finite extension of the generic residue field. The valuation-ring specialization can be chosen with that extension as its fraction field. The calculation applies and yields a special-fibre transporter over the residue field of the ring. This makes the fibre of the orbit map over the chosen boundary point nonempty, and that finite-type fibre has a $K$-point because $K$ is algebraically closed. This contradicts being a boundary point. [Stacks Project, discrete valuation rings realizing specializations, Tag 054F](https://stacks.math.columbia.edu/tag/054F)

The geometric multiplication tensor of a finite étale algebra is $D_n$ in its primitive idempotent bases, with the two input factors dualized as appropriate. A basis change from the displayed bases normalizes the product special-linear action inside the product general-linear action. Hence it transports its closed orbit to a closed orbit. This proves closedness for $T,U$ above.

## What invariant and geometric tests can establish

The preceding example has rational ordinary isomorphism, geometric special-linear isomorphism, a closed geometric orbit, and equality of all algebraic special-linear invariant polynomials. It still fails rational special-linear isomorphism over $F$. In particular deciding whether a closed orbit has the requested rational transporter cannot be replaced by geometric equality or equality of a complete set of algebraic invariants. This includes arbitrarily large finite families of evaluated invariants of any degrees, since the two tensors lie in one geometric special-linear orbit. Invariants under only the finite group of rational points are a different object here. [Lysikov and Walter, orbit closure intersection versus orbit equality](https://arxiv.org/html/2411.04639v2)

The [earlier determinantal hypersurface constructions](PriorDeterminantalFamilies.md) using reduced marker degrees and their absolutely irreducible suspensions transfer this exact extension spectrum. Those constructions work over each field with the same formulas, and their correctness compares rational linear transporters, or abstract rational isomorphisms in the suspension case. Apply their forward construction to $T,U$ over $F$ and then base-change the two output varieties to $\mathbf F_{3^k}$. Their projective-linear equivalences, and abstract isomorphisms for the suspension family, occur precisely when some $p_i$ divides $k$. That supplies descent examples in the explicit geometric family as well as in the tensor representation.

These examples are not complexity hard instances by themselves. Their extension spectrum is read off from the displayed degrees. Their force is the failure of a proposed geometric criterion, independent of whether the full computational collapse holds.

## Frobenius components and field-uniform reductions

There is an exact general restriction for a reduction intended to commute with scalar extension. For any pair of tensors that are geometrically ordinarily isomorphic over a finite base field, form the algebraic transporter $X$ of the pair. Work with geometric points and the reduced stabilizer $H$ of the source. Its identity component $H^0$ is a connected smooth algebraic group, since the base is perfect. The components of $X$ are cosets for $H^0$, and Frobenius permutes this finite component set.

For each positive $k$, the transporter has a point over the degree-$k$ extension if and only if the $k$th Frobenius power fixes some component. Necessity is immediate. If the power $\Phi^k$ preserves a component and $x$ is one of its geometric points, then $c=x^{-1}\Phi^k(x)\in H^0$. Lang's theorem gives $a\in H^0$ with $a\Phi^k(a)^{-1}=c$. Thus $xa$ is a rational transporter over the degree-$k$ extension. Therefore the extension spectrum is the union, over cycles on the component set, of the multiples of their lengths. [Lang, Algebraic Groups over Finite Fields](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf)

Suppose a reduction from special-linear isomorphism to ordinary TI produces one output pair over $F$, commutes with extension on that pair, and is correct over every finite extension on the displayed division-spectrum inputs. The output for our example must have a Frobenius component cycle of length $p_i$ for each $i$. Indeed $k=p_i$ must give a transporter and $k=1$ must fail. A component cycle length dividing the prime $p_i$ is therefore equal to $p_i$. The output transporter has at least $\sum_i p_i$ geometric components. In particular a method with connected geometric stabilizers on every output cannot be such a field-uniform reduction.

A concrete excluded target model under these hypotheses is ordered matrix tuple equivalence. For an ordered tuple $(A_i)$ under the left-right action the geometric stabilizer is the unit group of the finite-dimensional algebra
$$
D=\{(g,h): hA_i=A_i g\text{ for all }i\}.
$$
The invertible pairs form a nonempty Zariski-open subset of the affine linear space $D$, so this group is geometrically connected. The same rationale applies to automorphisms of a finite-dimensional module, which form the unit group of its endomorphism algebra. This restriction does not apply to arbitrary ordinary tensor objects with disconnected stabilizers, or to a fixed-field reduction whose correctness and behavior after scalar extension are unspecified.

## Closed-orbit pencils with a superpolynomial minimum extension degree

The union-of-multiples example above can be replaced by an intersection-of-multiples example. For distinct odd primes $p_1,\ldots,p_s$ put $m=\prod_i p_i$ and $L=\sum_i p_i$. One can construct full-support square matrix-pencil tensors $A,B$ over $\mathbf F_3$ in deterministic time polynomial in $L$ with the following properties.

- The tensors are ordinarily isomorphic over $\mathbf F_3$ by a specified label map.
- They are special-linearly isomorphic over $\mathbf F_{3^k}$ exactly when $m\mid k$.
- Their common geometric special-linear orbit is closed.

The proof also works mathematically over any odd finite field. The running-time assertion is for the fixed field $\mathbf F_3$.

### The colored graph

Make disjoint cycles with vertices $v_{i,a}$ indexed by $a\in\mathbb Z/p_i\mathbb Z$, and use one edge color on all cycle edges. Make two common sign vertices indexed by $\epsilon=\pm1$. For each cycle and each $a,\epsilon$ add a vertex $b_{i,a,\epsilon}$. It is joined to $v_{i,a}$ by a tail-colored edge, to $v_{i,a+\epsilon}$ by a head-colored edge, and to the sign vertex $\epsilon$ by a sign-colored edge. These three edge colors are distinct and different from the cycle color. Add a root vertex joined to both sign vertices by edges of a new color.

The preservation of edge colors identifies the cycles individually by their distinct sizes. It then identifies each $b$ through its tail, head and sign incidences. The sign pair and root are invariant by their respective incidences. A graph automorphism on cycle $i$ is of the form $a\mapsto a_i+\epsilon_i a$. Its action on the $b$ vertices forces $\epsilon_i$ to agree with whether it preserves or swaps the two common sign vertices. Thus all $\epsilon_i$ equal one sign $\epsilon$. Conversely arbitrary $a_i$ and this one sign determine a unique graph automorphism. The graph is connected.

Every translation has even permutation sign, since its individual cycles are of odd length. The common reflection swaps the sign vertices. On each original cycle its permutation is a product of $(p_i-1)/2$ transpositions, and on the two sets of $b$ vertices it is a product of $p_i$ transpositions. If the common reflection as so far constructed is even, attach one new vertex to each sign vertex by a new edge color. These two new vertices are necessarily swapped by the reflection and fixed by all translations. The automorphism group has not changed and the reflection is now odd. If the total number $r$ of graph vertices is even, attach one further vertex to the fixed root by another new edge color. This vertex is fixed by all automorphisms, and $r$ is now odd. Thus the odd graph automorphisms are exactly those with $\epsilon=-1$.

Let $\sigma$ be the translation by one in every cycle, carrying the $b$ vertices along their indices and fixing the root and sign vertices and any added vertices. Its order is $m$. All translations commute with it, and each common reflection conjugates it to its inverse. Since $m$ is odd, an odd graph automorphism commutes with $\sigma^k$ exactly when $\sigma^k=1$, equivalently $m\mid k$.

### A rational pencil with that label group

Give each edge color its own positive even weight and denote an edge's weight by $w_{uv}$. There are a fixed number of edge colors, so these weights may be bounded by a constant. Let $E$ be the sum of all edge weights and choose odd $C>2E$. Give vertex $v$ the weight
$$
w_v=C-\tfrac12\sum_{u: \,uv\text{ is an edge}}w_{uv}.
$$
The weights are positive integers and every vertex weight exceeds every edge weight. Their combined sum over vertices and edges is $N=rC$, which is odd. Every automorphism of the edge-colored graph preserves the vertex weights. Over the algebraic closure let the label dual coordinate basis have one form $\ell_v$ per vertex. The desired diagonal pencil has a block $L_\alpha(x)I_{w_\alpha}$ for each vertex or edge, where
$$
L_v=\ell_v,\qquad L_{uv}=\ell_u+\ell_v.
$$
These all have distinct lines. The weight $w_\alpha$ is their indicated vertex or edge weight.

Here is an explicit rational realization with Frobenius $\sigma$. For each vertex orbit of length $d$ under $\sigma$, use one label coordinate in the field $\mathbf F_{3^d}$, regarded as a vector over $\mathbf F_3$. Choose one representative per orbit and assign the forms on that orbit to the embeddings $x\mapsto x^{3^a}$, in the order indexed by the $\sigma$ iterates. These form a coordinate basis after scalar extension, and applying Frobenius to their coefficients advances the vertex by $\sigma$.

For each $\sigma$ orbit of vertex blocks or edge blocks, use $w_\alpha$ copies of its orbit field as both the row and column blocks. The representative vertex block is multiplication by the value of its representative form. The representative edge block is multiplication by the sum of its two endpoint values. Within each cycle, use the same polynomial-basis model of $\mathbf F_{3^{p_i}}$ for every orbit of length $p_i$. An endpoint's value in this model is a known Frobenius power of its label coordinate. If an endpoint is fixed, take its value in the base field. Every edge orbit has length $p_i$ or one, since edges either stay in a single cycle and its markers, attach those markers to fixed vertices, or join fixed vertices. Thus these sums and multiplications all take place in a known field of degree $p_i$ or one. In split idempotent bases the resulting rational pencil is exactly the diagonal one specified above. Frobenius permutes the split label forms and block coordinate idempotents by $\sigma$, with no changes in the multiplicity coordinates.

There are $O(L)$ vertices and edges. Since $C=O(L)$, $N=O(L^2)$. Constructing the degree-$p_i$ fields with Shoup's algorithm, computing endpoint Frobenius powers and writing the multiplication blocks take polynomial time in $L$. The explicit dense tensor coefficient list has $O(rN^2)=O(L^5)$ entries over $\mathbf F_3$. The construction never constructs an extension field of degree $m$. [Shoup, deterministic irreducible polynomial construction](https://www.shoup.net/papers/detirred.pdf)

### Exact orientation and descent

Work over an arbitrary finite extension $K=\mathbf F_{3^k}$. Use matrix-map transporter convention $A(fx)g=hA(x)$ for automorphisms. Its determinant identity shows that $f$ permutes the lines of the forms $L_\alpha$ preserving their multiplicities. The vertex forms are distinguished from the edge forms by their strictly larger multiplicities. Thus $f$ sends vertex forms to scaled vertex forms and induces a vertex permutation $\pi$. The edge factors then force $\pi$ to preserve the edge colors. Their two equal coefficients force the scales on their two endpoints to agree. Since the graph is connected, $f^*$ on the label dual has the form $\lambda P_\pi$ for one common scalar $\lambda$ and the permutation matrix of $\pi$. This argument works over the algebraic closure and applies to every rational label map.

The map $\lambda P_\pi$ is $K$-rational exactly when $\lambda\in K$ and $\pi$ commutes with $\sigma^k$. Indeed Frobenius conjugates its permutation matrix by $\sigma$, and the nonzero positions determine the permutation uniquely. The scalar on those positions must then be fixed. For any commuting $\pi$ the induced permutation of all split output blocks is also $K$-rational. It preserves their multiplicities. With a choice of direction for its block permutation matrix $Q$, the label with scale $\lambda=1$ satisfies $A(fx)=Q A(x)Q^{-1}$. The fixed root's split block exists over the base field and has positive dimension. Scaling one coordinate there by an arbitrary nonzero unit commutes with the full pencil. Thus $Q$ can be multiplied by such a commuting map so that its determinant becomes one, without affecting its conjugation of the pencil. This yields a reference transporter with $g=h$ and $\det g=\det h=1$.

Choose any $F$-rational label map $f_0$ of determinant $-1$ and put $B(x)=A(f_0^{-1}x)$. The pair $(A,B)$ has the ordinary transporter $(f_0,I,I)$, and all other ordinary transporters are its right coset by the source automorphism group. A special-linear transporter needs an automorphism with $\det f=-1$ and $\det g=\det h=1$. For a label of the form $\lambda P_\pi$, the determinant of the pencil scales by $\lambda^N$, with no additional factor because the factors are permuted. Hence $\det g=\det h=1$ forces $\lambda^N=1$. Since $N$ is odd, $\lambda^r$ cannot be $-1$. The equation $\det f=\lambda^r\operatorname{sgn}(\pi)=-1$ is consequently possible precisely for an odd $\pi$, and for such $\pi$ it is possible with $\lambda=1$ and the row and column maps just constructed. This is equivalent to $m\mid k$, by the graph calculation. It also proves geometric special-linear equivalence, since the common graph reflection is available over the algebraic closure. The label forms span the dual and the pencil is generically invertible, so all three mode supports are full.

### Closedness with these weights

Let the ground field be algebraically closed for the geometric argument. In any label-dual subspace $W$ of dimension $0<d<r$, the total weight of the form lines contained in $W$ is strictly less than $Cd$. If $W$ contains exactly $d$ coordinate lines $\ell_v$, it is the coordinate span of the corresponding vertex set $S$. The total weight inside that span is
$$
C|S|-\tfrac12\sum_{\substack{uv\text{ an edge}\\|\{u,v\}\cap S|=1}}w_{uv}
<C|S|,
$$
because the connected graph has a crossing edge. If $W$ contains fewer than $d$ coordinate lines, its vertex weight is at most $C(d-1)$ and its total edge weight is at most $E<C$. This proves the same strict bound. The proof works over every extension of the algebraically closed coefficient field.

Consider an integral specialization of the pencil along a discrete valuation ring as in the earlier orbit argument, with three special-linear transporters over its fraction field. Use a Smith decomposition $f=P\operatorname{diag}(\pi^{\gamma_1},\ldots,\pi^{\gamma_r})Q$ for the label map, where $P,Q$ are integral invertible matrices, the integers $\gamma_i$ increase weakly and have sum zero. For each form $L_\alpha$, let $a_\alpha$ be the minimum valuation of the coefficients of $L_\alpha f$. Right multiplication by $Q$ leaves this minimum unchanged. The row $L_\alpha P$ is primitive, and its first unit coordinate gives an upper bound for $a_\alpha$ equal to the corresponding $\gamma_i$. For $j=1,\ldots,r-1$, let $W_j$ be the subspace of label-dual forms whose first $j$ coordinates after multiplication by the reduced matrix $\bar P$ vanish. It has dimension $r-j$. Summing the upper bounds by levels gives
$$
\sum_\alpha w_\alpha a_\alpha
\ \le\
N\gamma_1+\sum_{j=1}^{r-1}(\gamma_{j+1}-\gamma_j)
   \sum_{\alpha:L_\alpha\in W_j} w_\alpha .
$$
The strict subspace bound makes this strictly smaller than
$$
N\gamma_1+C\sum_{j=1}^{r-1}(\gamma_{j+1}-\gamma_j)(r-j)
=C\sum_i\gamma_i=0
$$
if some $\gamma_{j+1}>\gamma_j$. But the slice determinant of the integral pencil is the product of the $L_\alpha f$ to their weights, since the other modes have determinant one. Gauss's lemma for primitive integral polynomials gives $\sum_\alpha w_\alpha a_\alpha\ge0$. Thus all $\gamma_i=0$ and the label map is already integral invertible with determinant one.

Undo the integral label map for the remainder of the specialization. Choose a constant label direction $x_0$ avoiding the form hyperplanes, possible over the algebraically closed field. Its original slice $A_0$ is constant invertible, and its transported slice $B_0$ is integral invertible since its determinant equals that of $A_0$. The matrices $A_0^{-1}A_i$ for the original label coordinates are constant diagonal, with distinct joint eigenvalue tuples for the separate form blocks. Indeed those tuples are the coefficients of $L_\alpha/L_\alpha(x_0)$, which are distinct because the form lines are distinct. The corresponding integral matrices $B_0^{-1}B_i$ are simultaneously conjugate to that tuple over the fraction field. Interpolating on the finitely many distinct joint eigenvalue tuples gives their joint projectors as polynomials in the matrices with constant coefficients. The transported projectors are therefore integral idempotents with free images forming a direct sum over the valuation ring. Choosing bases of these images gives an integral invertible conjugating matrix $R$. Rescale one column by the inverse of its determinant, a unit, to get $\det R=1$ without affecting the conjugation. The other row-column matrix $B_0 R A_0^{-1}$ also has determinant one and is integral invertible. Thus the specialization remains in the special-linear orbit. The same specialization argument as for the diagonal tensor now proves geometric orbit closedness.

### Growth and the component obstruction

Take the first $s$ odd primes. Bertrand's postulate gives $p_{i+1}<2p_i$, hence $\log L=O(s)$. Since $p_i\ge i+2$, one has $\log m=\Omega(s\log s)$. The dense tensor input size is polynomial in $L$, so the minimum extension degree $m$ grows faster than every fixed polynomial of that input size. [Erdős, proof of Bertrand's postulate](https://www.renyi.hu/~p_erdos/1932-01.pdf)

An extension-compatible reduction on these inputs has an output transporter whose component Frobenius permutation contains a cycle of length exactly $m$. Indeed it must have a fixed component at the $m$th power, and no fixed component at any positive power smaller than $m$. Thus the output transporter has at least $m$ geometric connected components. This rules out field-uniform reductions whose output transporters have only polynomially many components in the source input size. Ordinary tensor stabilizers in general may have many components, so the bound does not exclude arbitrary ordinary-TI reductions.

## A precise computational split between the two hypotheses

Over $F=\mathbf F_3$, let $\mathsf{GSL}$ be the problem on $F$-coefficient tensor pairs that asks for a special-linear transporter over $\overline F$. Let $\mathsf{Descent}$ be the promise problem whose input is an ordinarily isomorphic pair over $F$ that is also special-linearly isomorphic over $\overline F$. It asks whether a special-linear transporter exists over $F$. Use deterministic polynomial many-one reductions. A reduction for the promise problem is required to be a total polynomial map, with its correctness required only on promised inputs.

If $\mathsf{GSL}$ and $\mathsf{Descent}$ both reduce to ordinary TI, then so does rational $\mathsf{TI}_{\rm SL}$. On every input, combine the ordinary rational TI test, the geometric special-linear test, and the promise descent test in conjunction. Failing either antecedent already rules out rational special-linear isomorphism. Passing both makes the input promised and the third test gives the answer. One ordinary TI instance can express the fixed conjunction of three ordinary TI instances by putting their tensors in distinct ordered spaces and using the constant-size tensor-system compiler. Conversely any ordinary TI reduction for rational $\mathsf{TI}_{\rm SL}$ restricts to the promised $\mathsf{Descent}$ task. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2)

In particular, conditional on a reduction $\mathsf{GSL}\le_m^{\rm P}\mathsf{TI}$, the proposed collapse is equivalent to $\mathsf{Descent}\le_m^{\rm P}\mathsf{TI}$ in this promise sense. If the proposed collapse fails, at least one of the geometric test and the rational descent test lacks an ordinary TI reduction. If the collapse holds, this promise descent test and the explicitly equivalent determinantal families reduce to ordinary TI, while the invariant and field-extension counterexamples still hold. No implication from the collapse to a reduction of the general $\mathsf{GSL}$ task is proved here.

These are paper proofs. The conclusions separate arithmetic descent from geometric equality and identify restrictions on specific field-uniform constructions. They do not establish either computational hypothesis.
