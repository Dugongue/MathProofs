# Marked group algorithms for nonassociative rings and nonfree tensors

This note gives two algorithmic consequences of the Qiao–Zhang Cayley-table group isomorphism theorem. The first concerns any finite abelian group equipped with a biadditive multiplication. The second concerns arbitrary finite modules over finite commutative principal ideal rings whose local chain lengths are bounded. Both algorithms return a representative and generators of the source stabilizer, or detect that the transporter is empty. The proofs are informal. The running times use cardinalities of explicitly presented structures. [Qiao–Zhang](https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1723.pdf) · [Zhang–Wang–Zhuang](https://arxiv.org/html/2611.18084v1)

## 1. Nonassociative multiplication

Let $M$ be a finite abelian group of order $N>1$ with a biadditive multiplication $\mu$, and let $m$ be its additive exponent. Put $R=\mathbb Z/m\mathbb Z$. Form the additive group $A_\mu=R^2\oplus M$ with multiplication
$$
 (r,s,x)(r',s',y)=(rr',ss',ry+s'x+\mu(x,y)).
$$
This is biadditive and has unit $(1,1,0)$. Put $e=(1,0,0)$ and $f=1-e$. The expression $(eA_\mu)f$, with the displayed parentheses, is exactly the copy of $M$. The multiplication on that copy is $\mu$. A unital isomorphism preserving $e$ fixes both scalar coordinates and is precisely an additive multiplicative bijection on $M$. Conversely every such bijection extends by the identity on the scalar coordinates. This is a bijection of transporter sets compatible with composition.

For any unital biadditive ring $A$, construct the group on $A^3$ with law
$$
 (a,b,c)(a',b',c')=(a+a',b+b',c+c'+ab').
$$
Biadditivity proves associativity of this group law. Its identity is the zero triple and the inverse is $(-a,-b,-c+ab)$. The commutator has central coordinate $ab'-a'b$; testing against $(1,0,0)$ and $(0,1,0)$ shows that the center is exactly the third copy of $A$. The centralizers of these two elements, modulo the center, recover the first and second additive copies. A group isomorphism preserving the two marks therefore induces additive bijections $P,Q,S$ on the first, second, and central copies satisfying $S(ab)=P(a)Q(b)$. The marks give $P(1)=Q(1)=1$, so $P=Q=S$ by setting one factor at a time equal to $1$. The resulting map is a unital ring isomorphism. Every such ring isomorphism extends to the group coordinatewise. Any additional marked ring element can be marked in the center.

Apply Qiao–Zhang to the explicit group tables and impose the two unit marks and the central mark for $e$ by successive pointwise permutation stabilizers. The resulting coset maps onto exactly the original multiplication-isomorphism coset. Restriction of one representative and the computed source generators therefore gives the required output. Group order is $m^6N^3\le N^9$. Table construction and mark restriction are polynomial in the order. Different orders or additive exponents are rejected, and the one-element case is immediate. This applies in particular to finite Lie rings and finite Jordan rings given by operation tables.

The two-mark interpretation is Mal’cev's construction. Khoussainov and Slinko discuss the nonassociative unital case in odd prime characteristic in Section 5. The extra marked corner above makes the construction work for an arbitrary finite biadditive multiplication, with no unit in the input and any additive exponent. Section 3 of Zhang–Wang–Zhuang uses the two-mark construction for associative rings. These precedents supply the group mechanism used here. Publication priority for the extensions is unverified. [Khoussainov–Slinko](https://www.math.auckland.ac.nz/~slinko/Research/Rings-Groups.pdf) · [Zhang–Wang–Zhuang, Section 3](https://arxiv.org/html/2611.18084v1#S3)

## 2. A finite family of modules and bilinear maps

Let $R$ be a finite commutative ring with identity. Take named finite $R$-modules $M_1,\ldots,M_s$, with named $R$-bilinear maps between ordered pairs of sorts and designated output sorts. Assume at most one operation for each ordered pair of input sorts. The following construction computes the coset of simultaneous $R$-linear isomorphisms preserving the maps and any additional marked elements.

On $A=R^{s+1}\oplus\bigoplus_i M_i$, use coordinatewise multiplication on the scalar blocks. For scalars $r,w\in R^{s+1}$ and module entries $x,y$, the $i$-th module coordinate of the product is
$$
 r_i y_i+w_*x_i+\sum_{\beta_{jk}\,\mathrm{with\ output}\,i}\beta_{jk}(x_j,y_k).
$$
The star labels the extra scalar block and refers only to that coordinate. The unit has all scalar coordinates $1$ and all module coordinates zero. Let $e_i,e_*$ denote the scalar coordinate idempotents. Mark them and all elements of the scalar diagonal $r\mapsto(r,\ldots,r,0)$. For $i\ne *$, the bracketed corner $(e_i A)e_*$ is the $i$-th module. Multiplication by the marked scalar diagonal forces $R$-linearity on its action. Multiplying elements of two module sorts recovers the prescribed bilinear map, or zero in an unused slot. A marked isomorphism is consequently equivalent to a simultaneous isomorphism of this family of modules and operations. Conversely the simultaneous isomorphism extends by the identity on the scalar blocks, and this extension preserves the defined product.

The group construction from Section 1 applies to this unital biadditive ring. Marked ring constraints become pointwise group constraints via the center. Thus the computational bound is polynomial in $|R|^{s+1}\prod_i|M_i|$ and the original bit length. The family of sorts below always has distinct ordered input pairs.

## 3. Nonfree three-tensors over a chain ring

Let $R$ be a finite commutative chain ring, with maximal ideal $(\pi)$, and let $e$ be the least positive integer with $\pi^e=0$. Write $R_t=R/(\pi^t)$ for $1\le t\le e$. Given finite $R$-modules $U_1,U_2,U_3$ and
$$
 T\in U_1\otimes_R U_2\otimes_R U_3,
$$
represent $T$ by a written sum of pure tensors or by cyclic-summand coefficients. Use full module and ring tables, or any presentation allowing those tables to be expanded within polynomial time in the orders and the input bit length.

For each $i,t$ put $D_{i,t}=\operatorname{Hom}_R(U_i,R_t)$. The evaluations
$$
 \mathcal E_{T,t}(a_1,a_2,a_3)=(a_1\otimes a_2\otimes a_3)(T)\in R_t
$$
use multiplication of the three scalar outputs. All evaluations together distinguish tensors. Indeed, a finitely generated module over a chain ring is a direct sum of modules $R/(\pi^d)$, by diagonal reduction of a presentation matrix. A triple of cyclic summands contributes one copy of $R/(\pi^t)$, where $t$ is the minimum of their three exponents. Project each module onto its chosen summand and send its generator to $1\in R_t$. The evaluated value is that triple's coefficient. This proof of detection does not require any chosen splitting in the algorithm.

Apply Section 2 to the following named module sorts and binary operations.

- Sorts are the three $U_i$, all the $D_{i,t}$, the modules $E_t=\operatorname{Hom}_R(D_{3,t},R_t)$, and the $R_t$. Mark $1$ in each $R_t$ sort. An $R$-linear map fixing this element fixes the whole sort.
- Include the pairings $U_i\times D_{i,t}\to R_t$ and $D_{3,t}\times E_t\to R_t$, evaluated in the indicated order.
- Include $\beta_{T,t}:D_{1,t}\times D_{2,t}\to E_t$ sending $a_1,a_2$ to the functional $a_3\mapsto\mathcal E_{T,t}(a_1,a_2,a_3)$.

Preserving the first evaluation maps forces each $D_{i,t}$-action to be precomposition by the inverse of the corresponding $U_i$-action. The next pairing forces the $E_t$-action to be the corresponding dual. The remaining conditions say that all evaluations of the transformed tensor coincide with those of the target tensor. Detection proves equality of the transformed and target tensors. Conversely a tensor transporter gives every required induced map and preserves every pairing and $\beta_{T,t}$. Restriction and extension are compatible with composition. This establishes the full tensor transporter coset.

Each $D_{i,t}$ has at most $|U_i|$ elements. On a summand $R/(\pi^d)$, its homomorphisms into $R_t$ correspond to elements of $R_t$ killed by $\pi^d$, a set of cardinality $|R/(\pi^{\min(d,t)})|$. The same estimate applied to $D_{3,t}$ bounds $|E_t|\le |U_3|$. These modules can be constructed by listing allowed images of cyclic generators and evaluating maps in those coordinates. The cyclic decomposition itself can be computed from the full module tables by presenting the module with one symbol per element and relations for addition and scalar multiplication, and performing pivot reduction over the chain ring. A nonzero pivot of smallest $\pi$-valuation divides every entry of its submatrix. Elementary operations diagonalize it and then recur on the complementary submatrix. All valuations and exact quotients needed in those operations can also be found by enumerating $R$.

There are $3+5e$ sorts, with all values and group orders bounded by
$$
 |R|^{O(e)}\bigl(|U_1||U_2||U_3|\bigr)^{O(e)}
$$
up to a factor polynomial in the original bit length. Thus the computation is polynomial in the ring and module orders at fixed chain length. Neither the proof of detection nor the classification of transporters requires free factors.

A finite commutative principal ideal ring is a product of finite chain rings. From the ring table, enumerate primitive idempotents and split each module by these idempotents. The cross-component terms in any tensor vanish, since for distinct central idempotents $c_i,c_j$ one has $c_i c_j=0$ and can move a scalar from one tensor factor to another. An $R$-linear transporter preserves these components. Solve the local instances and take the componentwise product of representatives and stabilizer generators. This gives polynomial-order complexity whenever the maximum local chain length is bounded, including mixed-characteristic rings of this type with an unbounded number of direct factors.

This is an extension of the free-tensor application in the follow-up preprint. Their identification of tensors with bilinear maps uses freeness. The use of all quotient levels above handles nonfree factors over finite principal ideal rings. The exponent in the order bound depends on local chain length. For succinct presentations, the structure orders can be exponential in the written input length. [Zhang–Wang–Zhuang, Section 4.2](https://arxiv.org/html/2611.18084v1#S4.SS2) · [Grochow–Qiao–Stange–Sun](https://arxiv.org/abs/2611.00735)
