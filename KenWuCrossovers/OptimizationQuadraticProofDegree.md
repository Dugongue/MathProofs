# Bounded-degree quadratic optimization with an exact unit gap and exponential proof size

**Theorem.** There is a family of unconstrained binary quadratic minimization instances with \(N\) binary variables, uniformly bounded interaction degree, and linear and quadratic coefficients of absolute value at most two, whose exact minimum is one. For the exact Boolean cost encoding below, refuting the existence of a zero-cost assignment by polynomial calculus over any field requires degree \(\Omega(N)\) and expanded monomial size \(2^{\Omega(N)}\). The encoding has \(O(N)\) variables and axiom degree at most three. It checks ordinary integer cost in every characteristic. In this construction the cost and graph-colouring systems also simulate one another at the original proof degree once it exceeds a universal constant, with additive \(O(N)\) expanded monomial size.

The construction connects the distinction between feasible points and optimality in Wu’s quadratic benchmark report to the MathProofs program on polynomial-calculus degree and sparse size. The graph-colouring lower bound is an external theorem. The new assertion is the exact-cost transfer and simultaneous unit optimum for sparse unconstrained instances. [Wu’s QPLIB result](https://kenwu-lab.wooqianghao.workers.dev/qplib-3347-better-point/) · [MathProofs sparse polynomial-calculus transfer](https://github.com/Dugongue/MathProofs/blob/main/OrdinaryTensorTransferFallout/Mixed.md) · [Conneryd, de Rezende, Nordström, Pang and Risse](https://arxiv.org/abs/2503.17022).

## Sparse objective with minimum one

Take a sequence of non-three-colourable graphs \(G\) on \(n\) vertices of bounded degree for which the Boolean indicator encoding of three-colourability requires polynomial calculus degree \(\Omega(n)\) over every field. Such a sequence follows from the fixed-degree random regular case of the cited graph-colouring theorem. On the same vertex set choose an inclusion-minimal set of edges \(E(H)\subseteq E(G)\) whose graph \(H\) is still not three-colourable. Every refutation of three-colourability of \(H\) is a refutation of three-colourability of \(G\), since its axioms are a subset. The lower bound is therefore inherited by \(H\).

Use three bits \(x_{v,1},x_{v,2},x_{v,3}\) at every vertex. Writing \(k_v=\sum_{c=1}^3x_{v,c}\), minimize

\[
Q_H(x)=\sum_{v}(k_v-1)^2+
  \sum_{\{v,w\}\in E(H)}\sum_{c=1}^3 x_{v,c}x_{w,c}
\]

over all binary assignments. On such inputs the square at \(v\) equals \(1-k_v+2\sum_{c<c'}x_{v,c}x_{v,c'}\). The constant term is \(n\), every linear coefficient is \(-1\), and the quadratic coefficients are one or two. Each \(x_{v,c}\) interacts with its two other vertex bits and with at most \(\deg_H(v)\) adjacent bits of the same colour. Thus \(N=3n\) and the interaction degree is bounded. Each summand in the first display is a nonnegative integer on binary inputs, and total cost zero would give an exact one-hot proper colouring of \(H\). If any one edge is deleted, the remainder has a proper three-colouring. It has exactly one monochromatic \(H\)-edge, namely the deleted edge, so its cost in \(H\) is one.

## Exact quadratic cost, independent of the field

All variables in the certificate system have Boolean equations \(z^2-z=0\). This forces each variable to be zero or one over every field. For a vertex with bits \(a,b,c\), introduce two output bits

\[
L=(1-a)(1-b)(1-c)+ab(1-c)+ac(1-b)+bc(1-a),
\qquad U=abc.
\]

These are polynomial defining equations, of degree at most three. For Boolean inputs the expression for \(L\) is the indicator of \(k_v=0\) or \(2\), since the four summands are indicators of disjoint possibilities. The vertex cost is therefore \(L+4U\). For the edge-colour cost introduce a bit defined by \(x_{v,c}x_{w,c}\). Compute the integer sum of the local contributions by a binary work-efficient addition tree, with the leading two zero bits of \(4U\) supplied by constants as necessary. For Boolean bits \(a,b,c\) the full-adder output and carry have polynomials

\[
s=a+b+c-2(ab+ac+bc)+4abc,\qquad
t=ab+ac+bc-2abc .
\]

These give the ordinary Boolean sum and carry by inspection on the eight inputs, so the equations work also in characteristic two. Padding the number of inputs to a power of two, at tree level \(j\) there are \(O(N/2^j)\) adders of width \(O(j+1)\), each made from that many full-adder gates. The total gate count is \(O(N)\). Widths include enough leading positions to avoid overflow. Impose that every final output bit is zero. This finite polynomial system, denoted \(S_H\), has a solution over a field precisely when some binary input has integer cost zero. The integer sum is enforced by gates and Boolean axioms, so modular cancellation of different violations cannot create a spurious assignment.

## Polynomial calculus pullback

Use the standard Boolean three-colouring system \(C_H\). Its vertex axioms are \(k_v-1=0\), \(x_{v,c}^2-x_{v,c}=0\) and \(x_{v,c}x_{v,c'}=0\) for distinct colours at a vertex, and its edge axioms are \(x_{v,c}x_{w,c}=0\) on edges. Replace every cost bit, intermediate bit and output bit of \(S_H\) by the constant zero, leaving the input bits unchanged. The full-adder axioms and zero-output axioms become zero polynomials. The edge defining axioms become signed edge axioms of \(C_H\). At a vertex the polynomial \(abc\) follows from a pairwise vertex axiom by multiplying by the third variable. The polynomial \((1-a)(1-b)(1-c)\) expands to \(1-k_v+ab+ac+bc-abc\), and each other summand of \(L\) follows from its pairwise axiom, subtracting \(abc\). Thus the two vertex defining axioms are derivable in degree at most three, over every field.

Polynomial calculus allows linear combinations and multiplication of an earlier line by a variable. Under substitution by zero or an input variable, each inference either remains such an inference or becomes zero. It follows that any degree-\(D\) refutation of \(S_H\) gives a degree-\(\max\{D,3\}\) refutation of \(C_H\). The lower bound for \(H\) proves that \(D=\Omega(N)\). The polynomial calculus size–degree theorem applied to \(S_H\), with \(O(N)\) Boolean variables and initial degree at most three, gives size \(\exp(\Omega((D-3)^2/N))=2^{\Omega(N)}\). [Impagliazzo, Pudlák and Sgall](https://doi.org/10.1007/s000370050024).

## Reverse simulation

A local fact over every field is that, in a fixed number \(k\) of Boolean variables, an equation \(p=0\) valid on the satisfying Boolean assignments of local equations can be derived from them and the Boolean axioms in degree at most \(k+\max\{\deg p,\max_f\deg f,2\}\). For each Boolean tuple \(\epsilon\) let \(\chi_\epsilon\) be the product of its \(k\) literal indicators. If \(\epsilon\) violates an equation \(f=0\), multiply the axiom \(f\) by these \(k\) factors and use the Boolean axioms to obtain \(f(\epsilon)\chi_\epsilon=0\), then divide by the nonzero scalar. Multiplication by a factor \(1-x\) is one variable multiplication and a linear combination. The identity \(\chi_\epsilon f=f(\epsilon)\chi_\epsilon\) modulo the Boolean axioms follows by reducing squares or by substituting each literal value in turn. All such reductions stay within the degree of the product. Multilinear expansion expresses \(p\) modulo the Boolean axioms as \(\sum_\epsilon p(\epsilon)\chi_\epsilon\), whose nonzero terms can only come from those excluded tuples. This proves the fact and gives constant expanded derivation size when the number of variables and degrees are bounded.

For a full adder the two outputs being zero force all three inputs to be zero, since on Boolean tuples its output represents their ordinary integer sum. Apply the local fact to that implication. At each adder node, process the positions downwards, starting with the top output carry bit and the most significant sum bit, which vanish. This produces zero on its inputs and on the carry from the next lower position. All input positions vanish in turn. Applying this calculation from the root down the tree forces every local cost bit to zero. For an edge the defining axiom of its cost bit now gives its graph-colouring axiom. At a vertex \(L=U=0\) forces exactly one colour, so the three-pair and sum equations follow by the same local fact on the vertex bits and their two cost bits. Thus all graph-colouring axioms follow with constant degree and total \(O(N)\) expanded monomial size, and any subsequent refutation replays on the unchanged input bits. The forward direction already had this size bound, since the substitution there sends each monomial to one monomial or zero, and the added local derivations have constant size.

The lower bound concerns this exact binary circuit formulation. It makes a claim about the cost comparison even though an optimal assignment with cost one is furnished by a colouring of any proper edge-deleted instance.
