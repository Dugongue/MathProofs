# Same-prime class reduction at the Lazard boundary

**Theorem (GP010).** For every odd prime \(p\), there is an instancewise reduction from isomorphism of finite groups of exponent dividing \(p\) and nilpotency class at most \(p\) to isomorphism of groups of class at most two and exponent dividing \(p\), at the same prime. Given Cayley tables, the reduction and witness decoder run in deterministic polynomial bit time, and the output order is at most a fixed power of the input order, with an absolute exponent. This extends the known reduction from class strictly below \(p\). [GP010](https://github.com/Dugongue/MathProofs/blob/main/GrochowOpenProblems/ISOMORPHISM.md#gp010) · [Grochow–Qiao, Part IV, Section 7.2](https://arxiv.org/html/2306.16317#S7.SS2)

## 1. Compact data from the augmentation filtration

Let \(I\) be the augmentation ideal of \(\mathbb F_p[G]\). The modular dimension subgroup formula states that \(G\cap(1+I^s)=\prod_{ip^j\ge s}\gamma_i(G)^{p^j}\). Since \(G\) has exponent dividing \(p\), this is exactly \(\gamma_s(G)\). Thus \(G\) embeds in the units of \(E=\mathbb F_p[G]/I^{p+1}\), and its image modulo \(I^p\) is \(Q=G/C\) for \(C=\gamma_p(G)\). The subgroup \(C\) is central, and \(Q\) has class less than \(p\). [Jennings](https://doi.org/10.2307/1989916) · [Dimension subgroup formula and related short-series results](https://arxiv.org/html/2610.40868)

For each \(g\in G\), define
\[
 \ell(g)=\sum_{k=1}^{p-1}(-1)^{k+1}(g-1)^k/k\quad\text{in }E.
\]
Here and below we use the same notation for the image of an ideal in a quotient. The input hypothesis gives \((g-1)^p=0\), so the exponential truncated at degree \(p-1\) inverts this logarithm on that element. The identity \(\ell(g^s)=s\ell(g)\) follows in \(\mathbb F_p[t]/(t^p)\) by reducing the one-variable formal identity modulo \(p\). This holds for every \(s\in\mathbb F_p\), using its integer representative as an exponent.

Use two vector spaces:
\[
 A=\{\ell(g)\bmod I^p:g\in G\},\qquad
 D=\{\ell(d):d\in[G,G]\}\subseteq E.
\]
The ordinary class-\(<p\) Lazard correspondence identifies \(A\) with the Lie algebra of \(Q\), using the ordinary associative commutator in \(\mathbb F_p[G]/I^p\) as bracket. Similarly, \([G,G]\subset 1+I^2\), and \(1+I^2\) in \(E\) has nilpotency class at most \(\lfloor p/2\rfloor<p\). Its logarithms lie in a Lazard Lie algebra with the associative commutator. Thus \(D\) is the Lie algebra of \([G,G]\) and is a genuine linear subspace. In both applications the associative ideal involved has \(p\)-th power zero, so the displayed truncated exponential and logarithm give the usual BCH formulas and functorial subgroup correspondence. Let \(j:D\to A\) be truncation modulo \(I^p\). Its kernel is \(\ell(C)\).

For \(x,y\in A\), take \(g,h\in G\) representing them and set
\[
 \beta(x,y)=[\ell(g),\ell(h)]_{\mathrm{ass}}\in E.
\]
Changing either logarithm by an element of \(I^p\) has no effect on the commutator in \(E\). Consequently \(\beta\) is well defined, bilinear, and alternating. We claim that it takes values in \(D\).

Use the convention \([g,h]=ghg^{-1}h^{-1}\) and write \(X=\ell(g)\), \(Y=\ell(h)\). The expression \(\ell([g^s,h^t])\) is a polynomial in \(s,t\). Indeed it is obtained by multiplying the truncated exponentials of \(sX,tY,-sX,-tY\) and taking the truncated logarithm. Terms of total degree above \(p\) vanish in \(E\). The only terms that remain are mixed, since at \(s=0\) or \(t=0\) the respective products cancel as polynomial identities. Each individual degree is therefore at most \(p-1\). The coefficient of \(st\) is \(XY-YX\). Interpolating in the two variables on \(\mathbb F_p^2\) expresses this coefficient as an \(\mathbb F_p\)-linear combination of the evaluations \(\ell([g^s,h^t])\), all in the subspace \(D\). This proves the claim. Let \(B\) be the Lie bracket of \(A\). Directly from truncation, \(j\beta=B\).

## 2. Recovering all group commutators

In the rational free associative algebra on \(X,Y\) completed by word length, take the homogeneous terms of degrees through \(p\) of
\[
 L(X,Y)=\log\!\left(\exp X\exp Y\exp(-X)\exp(-Y)\right).
\]
This is a Lie polynomial in the stated degree range, by the rational BCH theorem. It is an associative polynomial over \(\mathbb Z_{(p)}\). To verify integrality, first expand the product of exponentials. Pure terms in one variable cancel. A mixed monomial of degree at most \(p\) uses fewer than \(p\) copies of either variable, so the factorial denominators from the exponentials are prime to \(p\). The logarithm now applies to \(1\) plus terms of degree at least two, and hence uses only denominators \(1,\ldots,\lfloor p/2\rfloor\) through degree \(p\). Moreover the integral free Lie algebra embeds as a direct summand in each word-degree part of the integral free associative algebra. This follows by choosing an integral homogeneous Hall basis of the free Lie algebra and taking the ordered PBW monomials as a basis of its enveloping algebra. The individual Hall basis elements are among the PBW monomials. Therefore \(L\) is a Lie polynomial over \(\mathbb Z_{(p)}\) in these degrees.

Reducing that polynomial modulo \(p\) and substituting \(\ell(g),\ell(h)\) evaluates exactly to \(\ell([g,h])\) in \(E\). The pure terms canceled above, and the remaining coefficients use the same truncated expressions as the actual \(\ell\) and \(\exp\). Every nested bracket in this evaluation can be computed from \(\beta\) and \(j\). The initial inputs are the classes in \(A\). At each bracket, take the \(A\)-classes of the two inputs, use \(\beta\) to obtain the value in \(D\), and use \(j\) if its class is needed at a subsequent bracket. An intermediate value in \(D\) is a logarithm of an actual element of \([G,G]\), so it is one of the possible lifts of its \(j\)-class. This justifies the recursion in \(E\).

In fact \(D\) is spanned by the values of \(\beta\). Their span is a Lie subalgebra, because for \(d,d'\in D\) the associative bracket is \(\beta(jd,jd')\). The Lie-polynomial evaluation just given puts the logarithm of each group commutator in this span. The group commutators generate \([G,G]\), so their logarithms generate \(D\) as a Lie algebra under the Lazard correspondence. This proves the span assertion. Since \(j\beta=B\), the two alternating bilinear maps \(B,\beta\) therefore determine \(j\) and its kernel without a separate mark.

## 3. Exact isomorphism reflection

Any group isomorphism induces an isomorphism of the two bilinear maps by functoriality of the group algebra, its augmentation filtration, and the truncated logarithm. Conversely let \(\alpha:A_1\to A_2\) and \(\delta:D_1\to D_2\) be linear isomorphisms preserving \(B,\beta\). They preserve \(j\) because \(j\beta=B\) and the image of \(\beta\) spans \(D\). The map \(\alpha\) thus induces an isomorphism of the quotients \(Q_1,Q_2\), which we identify with \(Q\). The map \(\delta\) is a Lie isomorphism since the Lie bracket on \(D\) is \(\beta(jd,jd')\). Its group isomorphism \(\psi:[G_1,G_1]\to[G_2,G_2]\) restricts to an isomorphism \(\gamma:C_1\to C_2\). By the previous section, whenever \(g,h\in G_1\) and \(g',h'\in G_2\) have the corresponding images in \(Q\),
\[
 \psi([g,h])=[g',h'].
\]

Form the fiber product \(P=G_1\times_Q G_2\). Its derived subgroup is the graph of \(\psi\). It is contained in that graph by the commutator equation, and it projects onto \([G_1,G_1]\) because \(P\to G_1\) is surjective. Quotient \(P\) by the central subgroup \(J=\{(c,\gamma(c)):c\in C_1\}\), and call the result \(K\). Then \(K\to Q\) is a central extension whose kernel intersects \([K,K]\) trivially, since the graph of \(\psi\) meets \(C_1\times C_2\) exactly in \(J\). Since \(Q\) has class at most \(p-1\), \(\gamma_p(K)\) lies both in this kernel and in \([K,K]\), and hence is trivial. Also \(K\) has exponent dividing \(p\).

Apply the ordinary Lazard correspondence to \(K\to Q\). The resulting central Lie extension is an isomorphism on the derived ideals, because the group homomorphism is surjective and its kernel misses the derived subgroup. Take the inverse on the target derived ideal and extend to a linear section on the entire Lie algebra of \(Q\). The section preserves brackets. For any two inputs, the bracket of their lifts lies in the source derived ideal and projects to the target bracket, so it equals the prescribed inverse value. This gives a group section \(Q\to K\).

The inverse image in \(P\) of the section's image is a subgroup \(M\) projecting bijectively to each \(G_i\). Each projection is surjective by lifting the desired quotient element and adjusting its coordinate by \(J\). An element of \(M\) in either projection kernel has zero class in the central kernel of \(K\to Q\), because the section meets that kernel only in the identity. Such an element lies in \(J\), which meets each projection kernel trivially. Thus \(M\) gives an isomorphism of \(G_1,G_2\). This proves both reflection and the algebraic part of a decoder.

## 4. One class-two group with an explicit decoder

Here is the size-preserving encoding of the two maps. It uses the private-pair marker construction over a field. [Earlier paired markers](https://github.com/Dugongue/MathProofs/blob/main/GrochowResearchSynthesis/CLASS-TWO-BLACK-BOX.md)

The primal core \(V_0=A\oplus D\oplus k u\), for \(k=\mathbb F_p\), has three blocks. The base output \(W_0=\bar A\oplus\bar D\) consists of copies of the first two. Define the alternating core bracket by
\[
  [a,a']_0=(B(a,a'),\beta(a,a')),\qquad
  [a,u]_0=\bar a,\qquad [d,u]_0=\bar d,
\]
with the other block pairs zero and skew-symmetry supplying their reversals. For each core block put in two marker forms, so there are six markers in an intrinsically intended order. For a marker \(i\) on a block \(V_i\), add a private primal copy \(P_i=V_i^*\), a private even-dimensional symplectic space \(H_i\), and a private central line \(k b_i\). Marker \(F_i\) is the evaluation pairing \(V_i\times P_i\) skew-extended, plus the fixed symplectic form on \(H_i\), and is zero on all other pairs. With \(d_0=\dim V_0\), choose
\[
   w_i=\dim H_i=2(10+i)(3d_0+1)\quad (1\le i\le6).
\]
Let \(\widehat V\) be the primal core plus all private primal spaces and let \(\widehat W=W_0\oplus\bigoplus_i k b_i\). The full bracket has the given core component and the six marker components. The group law on \(\widehat V\oplus\widehat W\) is
\[
  (v,w)(v',w')=(v+v',w+w'+\tfrac12[v,v']).
\]
Bilinearity makes this associative. It has exponent dividing \(p\) and class two. Its derived subgroup is \(\widehat W\), since the core anchor pairs span the base outputs and the private heavy forms span their respective output lines.

Any output group isomorphism acts on the primal quotient and dually on the central form space, preserving alternating-form ranks. The abelianization dimension is \(3d_0+\sum_i w_i\), a strictly increasing function of \(d_0\), so two isomorphic outputs have matching \(d_0\). On the form space a covector is represented uniquely as \(Q+\sum_i a_i F_i\) with \(Q\) supported on the core. Its rank is in the interval
\[
  \left[\sum_{i:a_i\ne0} w_i,\ \sum_{i:a_i\ne0}w_i+3d_0\right],
\]
since the heavy blocks are independent and the nonheavy space has dimension \(3d_0\). The zero-marker band, the six singleton bands, and the range for two or more markers are disjoint. Thus the transported pure marker \(F_i\) has exactly the \(i\)-th marker coefficient nonzero.

For a form with just that nonzero marker coefficient, its nonheavy rank is \(2\dim V_i\) plus the rank of the residual form on the complement of \(V_i\oplus P_i\) in the nonheavy space. Indeed projection of its contraction image to \(V_i^*\oplus P_i^*\) is onto. Solve for the \(V_i\) input from the requested \(P_i^*\)-output, then for the \(P_i\) input from the requested \(V_i^*\)-output. In the kernel of this projection, the \(V_i\) input is zero and \(P_i\) cancels the \(V_i^*\)-output from any remaining input, leaving precisely the residual contraction image. Comparing the transported pure-marker rank in each direction proves equality of the two formats' \(\dim V_i\). With these dimensions equal the residual form vanishes, by the same rank formula.

The two contraction images for the private markers of one block intersect in exactly that named core dual block, both before and after transport. In the latter case the first contraction has zero output on the second private dual space and vice versa. An element in the intersection thus has zero output on both private dual spaces and both heavy spaces. For either contraction, zero output on its private dual forces the \(V_i\) input to be zero. The residual form has just been shown to vanish, leaving only the output in \(V_i^*\). Every element of \(V_i^*\) is attained by varying the private input. This proves the claimed intersection and recovers the three named primal quotient blocks by duality. Base forms are then recovered as the forms supported on the recovered dual core. Their annihilator in the center is precisely the sum of the marker lines, so the intrinsic central quotient is the base output \(W_0\).

On the recovered core let the witness maps be \(h_A,h_D\), and let the anchor have multiplier \(t\ne0\). Each base output block is the image of its core block paired with the anchor. Its recovered map is therefore \(t h_A\) or \(t h_D\). Preservation on the core pair \(A\times A\) gives preservation of \(B,\beta\) by \(t^{-1}h_A,t^{-1}h_D\). Conversely an isomorphism of the bilinear data gives a group isomorphism by fixing the anchor, carrying each private dual by inverse duality, and matching the heavy blocks identically. This is an objectwise reduction, including different input dimensions, since the singleton rank comparisons above force equality of the three block dimensions whenever outputs are isomorphic.

## 5. Uniform bounds and scope

The ambient group algebra has dimension \(|G|\). Its multiplication is read from the Cayley table. Compute augmentation powers by multiplying generators of successive subspaces and applying Gaussian elimination, at most \(p+1\) iterations. For a nontrivial input \(p\le|G|\). Compute the logarithm vectors and the bases of the displayed spaces by linear algebra, and directly evaluate the two brackets on their bases. No symbolic Hall basis construction or interpolation is needed by the algorithm. The proof of closure uses those tools only to identify the mathematical relations. The spaces have dimensions \(\log_p|Q|\) and \(\log_p|[G,G]|\), so the marker table above has order \(p^{O(d_0)}=|G|^{O(1)}\) for nontrivial \(G\), with an absolute exponent. Map the trivial input to the trivial group, which cannot be confused with the nontrivial marker outputs.

The decoder computes the induced maps of the output isomorphism on the group-derived subgroup and the abelianization. The displayed rank recoveries and quotient operations reconstruct the bilinear witness by linear algebra. It then builds the fiber product, of order at most \(|G_1||G_2|\), and the quotient \(K\) using their ordinary finite tables. The class-\(<p\) Lazard calculation for \(K,Q\) can again be performed by their group algebras modulo the \(p\)-th augmentation power, using the dimension subgroup formula. Compute the Lie-linear section and scan the resulting subgroup graph in the fiber product to return an actual group isomorphism. All these operations are polynomial in the table sizes with no factor exponential in \(p\).

This is a paper proof. It uses the marked subgroup of group elements in its group algebra through their explicit table description. The conclusion is an isomorphism reduction between Cayley-table problems, rather than a recovery claim from an arbitrary isomorphism of abstract modular group algebras.

# No compact composition-compatible decoder for arbitrary exponents

**Theorem (GP011).** Fix an odd prime \(p\). There is no assignment \(G\mapsto H(G)\) sending every finite class-two \(p\)-group to a class-two group of exponent dividing \(p\) of order polynomial in \(|G|\) and admitting surjective composition-compatible maps from output isomorphisms to input isomorphisms. For \(G=C_{p^e}\), such a decoder would force
\[
 |H(G)|\ \ge\ p^{\,p^{e-2}+1}\qquad(e\ge2).
\]
The same lower bound holds on strictly class-two inputs \(G=C_{p^e}\times U_3(\mathbb F_p)\). This refutes the requested combination of compactness, surjectivity, and composition compatibility. [Catalog GP011](https://github.com/Dugongue/MathProofs/blob/main/GrochowOpenProblems/ISOMORPHISM.md#gp011)

On a repeated input, a composition-compatible surjection of isomorphism sets is a surjective group homomorphism
\[
 \operatorname{Aut}(H(G))\longrightarrow\operatorname{Aut}(G).
\]
The automorphism given by multiplication by \(1+p\) on \(C_{p^e}\) has order \(p^{e-1}\). For completeness, if \(a=1+u p^r\) for \(r\ge1\) and \(p\nmid u\), then \(v_p(a^p-1)=r+1\). The first term of the binomial expansion has valuation \(r+1\), while every other term has valuation at least \(r+2\) for odd \(p\). Induction gives \(v_p((1+p)^{p^j}-1)=1+j\). For the strictly class-two example, act by this automorphism on the cyclic factor and the identity on \(U_3(\mathbb F_p)\).

If a finite group maps onto a group with a \(p\)-element of order \(p^{e-1}\), it contains a \(p\)-element of order at least \(p^{e-1}\). In fact choose a preimage \(g\) and write its order as \(p^a m\) with \(p\nmid m\). Then \(g^m\) has \(p\)-power order and its image still has order \(p^{e-1}\).

For \(H=H(G)\), the class-two Baer correspondence makes the underlying set of \(H\) into the corresponding Lie algebra over \(\mathbb F_p\), of dimension \(M=\log_p|H|\). It is functorial and faithful on automorphisms. Thus \(\operatorname{Aut}(H)\) is a subgroup of \(\mathrm{GL}_M(\mathbb F_p)\). A \(p\)-element of this general linear group is \(I+N\) with \(N^M=0\), since its minimal polynomial divides a power of \(X-1\). It satisfies \((I+N)^{p^r}=I+N^{p^r}\). Therefore a \(p\)-element of order at least \(p^{e-1}\) requires \(M>p^{e-2}\). This gives the claimed lower bound, which is larger than \(|G|^c\) for every fixed \(c\) as \(e\) grows even at one fixed prime.

The obstruction is to the transporter requirement in the stated question. The complexity of an instancewise decision-only reduction for mixed exponents remains open. This is a paper proof.
