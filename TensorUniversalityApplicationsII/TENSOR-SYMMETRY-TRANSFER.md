# Forgetting tensor symmetries in restrictions, spectra and finite-field isomorphisms

Let $K$ be a field and partition the $d\ge2$ positions into blocks $B_1,\ldots,B_b$ of sizes $s_1,\ldots,s_b$. In each block $B_j$ use copies of a single space $V_j$. A block-symmetric tensor is invariant under permutations within each block. A tied restriction $T\to_\Pi T'$ uses a single linear map $V_j\to V'_j$ at all positions in $B_j$. An ordinary restriction $T\to T'$ may use independent maps. These are all linear maps, including singular and rectangular ones.

**Theorem 1.** Suppose either the characteristic is $p>\max_j s_j$, or it is zero and for some block $B_j$ the scalar $-1$ is a sum of $s_j$-th powers in $K$. The second condition holds if a block has odd size or if $K$ is algebraically closed. There is a constant $C$ such that, for all block-symmetric tensors $T,T'$, ordinary restriction $T\to T'$ implies
$$
\langle C\rangle\otimes T\to_\Pi T',
$$
where $\langle C\rangle$ is the diagonal tensor with $C$ entries equal to one. For $p>\max s_j$, one may take $C=(\min_j s_j)\prod_j(2^{s_j}-1)$, independently of the field and the characteristic. Forgetting the ties reflects the Strassen asymptotic restriction preorder with subexponential diagonal multipliers, and every tied spectral point is the restriction of an ordinary spectral point. The ordinary and tied asymptotic ranks are equal.

The constructions also compare two different partitions of the positions. For a refinement, the permutation labels are replaced by labels whose multiplicities are the sizes of the refining blocks. The exact modular scope is stated in Section 3.

**Theorem 2.** Fix a finite field $\mathbb F_q$ of characteristic $p$, an order $s\ge2$, and a dimension bound $n\ge1$. Forgetting full symmetry is a functor on all homomorphisms. An ordinary isomorphism between two symmetric $s$-tensors always implies the existence of a tied isomorphism in dimensions at most $n$ if and only if
$$
\gcd(s,q^j-1)=1\quad(1\le j\le n),\qquad
n=1\ \,\text{or}\,\ p\nmid s.
$$
In the affirmative case an invertible ordinary witness can be turned into a tied witness in deterministic polynomial time in the explicit input length. The same sufficient test works for partially symmetric tensors, applied separately to each block. Over an algebraically closed field, for $n\ge2$, the exact criterion is that the characteristic does not divide $s$. For $n=1$ forgetting always reflects isomorphism over an algebraically closed field.

These results concern the morphism and asymptotic-spectrum directions of Grochow–Qiao's Open Question 7.5. The spectral argument extends the fully symmetric case of Christandl–Fawzi–Ta–Zuiddam to independent partial symmetries and to fields that need not be algebraically closed. The witness simulation uses permanent labels in separate auxiliary coordinates, as in the earlier partition compiler, and preserves all morphisms directly, with no inverses. [Grochow–Qiao, Part I](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full) · [Christandl–Fawzi–Ta–Zuiddam, §§3–4](https://arxiv.org/abs/2104.01130) · [MathProofs, partitioned tensor reduction](https://github.com/Dugongue/MathProofs/tree/main/TensorUniversalityApplications)

## 1. Simulating independent maps by tied maps

For one block of size $s$, let $E=K^s$ with basis $e_1,\ldots,e_s$. Use the normalized label tensor
$$
H_s=\frac1{s!}\sum_{\sigma\in S_s}e_{\sigma(1)}\otimes\cdots\otimes e_{\sigma(s)}.
$$
On all positions together let $H$ be the external tensor product of the $H_{s_j}$, with factors ordered by the original positions. For a given ordinary arrow, write its position maps within a block as $A_1,\ldots,A_s$. On $V\otimes E$ use the single linear map $B$ given by $B(x\otimes e_i)=A_i(x)\otimes e_i$. The term of $T\otimes H$ with label word $(\sigma(1),\ldots,\sigma(s))$ has its data transformed by the permuted position maps. The transformed data is $T'$ because both source and target are block-symmetric. All terms therefore give exactly $T'\otimes H$. This argument is blockwise and works with simultaneous permutations in all blocks.

The map $B$ preserves each label and applies the designated linear map there. Thus it preserves identities and compositions when the labels are retained. Forgetting labels at the end means applying, in each block, the linear map $V'\otimes E\to V'$ sending $x\otimes e_i$ to $x$ for every $i$. The sum of coefficients of each normalized label tensor is one, so this gives $T\otimes H\to_\Pi T'$. This simulation is a categorical construction with a fixed auxiliary tensor and an exact identity on its output, before the final contraction of labels.

To supply $H$ using diagonal copies, consider the identity
$$
\sum_{J\subseteq [s]}(-1)^{s-|J|}\left(\sum_{i\in J}e_i\right)^{\otimes s}
=\sum_{\sigma\in S_s}e_{\sigma(1)}\otimes\cdots\otimes e_{\sigma(s)}.
$$
In the expansion, the coefficient of a basis word is the signed sum over the subsets containing every label of that word. It is zero unless all labels occur. A surviving word contains each label exactly once and has coefficient one. Expanding the external product, $H$ is a linear combination of at most $M=\prod_j(2^{s_j}-1)$ tensors of the form $\bigotimes_j v_j^{\otimes s_j}$, with coefficients in the prime field.

Choose a block of size $m=\min_j s_j$ in characteristic $p>\max s_j$. In $\mathbb F_p$ the set $A$ of $m$-th powers has size $1+(p-1)/\gcd(m,p-1)$. The Cauchy–Davenport bound on the $m$-fold sumset gives size at least $\min(p,1+m(|A|-1))=p$. Every scalar weight in the displayed expansion is therefore a sum of at most $m$ $m$-th powers. For each weight assign those powers to scalings of the repeated vector in the chosen block. This converts the weighted terms to at most $mM$ unweighted terms, each of the same tied form. The reduction works in every extension of the prime field. [Cauchy–Davenport bound and its iterated form](https://doi.org/10.1016/j.ffa.2014.02.004)

In characteristic zero choose a block of size $m$ where $-1$ is a sum of finitely many $m$-th powers. Scalar inclusion–exclusion on $(x/m!,1,\ldots,1)$ expresses any scalar $x$ as a signed sum of at most $2^m-1$ $m$-th powers. Each negative term can be replaced by a sum using the chosen representation of $-1$. The number of unweighted terms is bounded in terms of the pattern and that representation. With a block of size one, every coefficient can instead be assigned directly to that vector. Over an algebraically closed field each coefficient has a root of the needed order.

An unweighted sum of $C$ tied pure tensors is a tied restriction of $\langle C\rangle$: send the $i$-th standard basis vector to the $i$-th prescribed vector in each block, using zeros if there are fewer summands. Hence $\langle C\rangle\to_\Pi H$. Tensor with $T$ and compose with the label simulation to prove the claimed bound.

## 2. Consequences for the asymptotic spectrum

Direct sum and the positionwise tensor product preserve block symmetry and tied restrictions. Pass, as usual, to equivalence classes under mutual restriction in each preorder. The class of the zero tensor is the additive identity, and $\langle1\rangle$ is the multiplicative identity, where $\langle r\rangle$ denotes the direct sum of $r$ copies of $\langle1\rangle$. The ordinary and tied natural-number classes have the usual order by the ordinary flattening-rank lower bound and by coordinate projection in each block. An ordinary rank decomposition of any $T$ and Section 1 show that $\langle C\,R(T)\rangle\to_\Pi T$. For any nonzero tensor $U$, the ordinary restriction $U\to\langle1\rangle$ and the same simulation show that $\langle C\rangle\otimes U\to_\Pi\langle1\rangle$. Together these give the domination axiom of a Strassen preorder. Thus the tied preorder admits the usual spectrum theorem. [Strassen preorder and spectrum extension theorem, Zuiddam, §2 and Corollary 2.18](https://ir.cwi.nl/pub/28021/Thesis_J_Zuiddam)

For any ordinary restriction $T\to T'$, apply the converter to the $r$-th tensor powers. If $\phi$ is a tied spectral point, monotonicity, additivity, normalization and multiplicativity give $\phi(T')^r\le C\phi(T)^r$. Taking $r$-th roots gives $\phi(T')\le\phi(T)$. In particular $\phi$ is constant on ordinary mutual restriction equivalence classes. It defines a monotone semiring homomorphism on the image of the block-symmetric tensors in the ordinary restriction semiring. By Strassen's spectrum extension theorem this homomorphism extends to an ordinary spectral point. In the opposite direction every ordinary spectral point pulls back along the forgetful map. This proves surjectivity of that pullback.

For the asymptotic preorder, an ordinary sequence $\langle r_k\rangle\otimes T^{\otimes k}\to (T')^{\otimes k}$ with $\lim r_k^{1/k}=1$ becomes a tied sequence with multipliers $Cr_k$ by applying the converter to each arrow. Conversely a tied sequence consists of ordinary arrows. The two preorders thus agree on the indicated objects after allowing subexponential diagonal multipliers. Applying the finite overhead bound to ordinary rank decompositions of $T^{\otimes k}$ proves $R(T^{\otimes k})\le R_\Pi(T^{\otimes k})\le C R(T^{\otimes k})$. Taking $k$-th roots gives equality of asymptotic ranks.

## 3. Refinement and the exact modular condition for the label construction

Let $\Pi'$ refine $\Pi$. In a block of size $s$ let the refining blocks have sizes $d_1,\ldots,d_r$, and use $r$ basis labels. Put $\mu=\binom{s}{d_1,\ldots,d_r}$. The normalized tensor that is the sum of all words having these multiplicities, divided by $\mu$, works whenever $\mu$ is nonzero in $K$. Indeed, each word corresponds to a permutation of the positions, and equal labels use the same $\Pi'$-map. The same label-preserving linear map and final contraction give the simulation. In characteristic $p$, $\mu\ne0$ is equivalent to the absence of carries in adding the $d_i$ in base $p$. This follows from $v_p(t!)=\sum_{j\ge1}\lfloor t/p^j\rfloor$ applied to the numerator and denominator.

For a diagonal supply of this tensor, suppose $K$ has at least $1+\max_j s_j$ elements and there is a block of size $m$ whose $m$-th powers additively generate $K$ with a fixed bound on the number of summands. This holds over algebraically closed fields, over any field if $m=1$, and over a finite field if $\gcd(m,|K|-1)=1$. In a parent block, the unnormalized label tensor is the coefficient of $z_1^{d_1}\cdots z_r^{d_r}$ in $(\sum_i z_i e_i)^{\otimes s}$. Evaluate on a grid with $s+1$ distinct elements in each coordinate, and extract this coefficient by successive univariate Vandermonde inversion. This expresses it as a linear combination of at most $(s+1)^r$ pure repeated powers. Multiply these expansions over the blocks and absorb all weights using the selected block, just as above. Thus a constant diagonal multiplier simulates every refined restriction between $\Pi$-symmetric tensors, even in the stated modular cases. An example is splitting a block of size three into sizes one and two over $\mathbb F_8$, where $\mu=3$ is nonzero and every scalar has a cube root.

For any field, a vanishing multinomial in one block rules out such a universal diagonal multiplier. Use the unnormalized label tensor of that block as the input, with pure one-dimensional factors in all other blocks. The refined maps read their own label and produce $\langle1\rangle$. Under a tied restriction to one-dimensional spaces, every term of the sum contributes the same scalar product. The resulting coefficient is zero because it is multiplied by $\mu$. A tied functional on a direct sum of copies restricts separately to each copy, so any number of diagonal copies still gives zero. This shows that the no-carry condition is exact under the stated diagonal supply hypotheses. Section 2 makes spectral claims in the scope of Theorem 1.

## 4. Exact finite-field criterion for isomorphisms

Fix one block of size $s$ with space $V$ and let $T,T'$ be symmetric on it. Other blocks can be treated as shared coefficient positions throughout this argument. Suppose an invertible ordinary tuple transports $T$ to $T'$. In the selected block call its maps $P_1,\ldots,P_s$, from $V$ to $V'$, and let $A_i=P_1^{-1}P_i$. Swapping positions 1 and $i$ leaves the source and target tensors unchanged. Cancelling the original maps and multiplying on position $i$ by $A_i$ gives
$$
(A_i)_1T=(A_i)_iT.
$$
Here $(A)_j$ applies $A$ only in position $j$. By symmetry, equality holds between every pair of positions of that block. Call this property transferability.

For $s\ge3$, transferable endomorphisms $A,B$ commute on the tensor in each slot. In three distinct positions $i,j,k$,
$$
A_iB_i T=A_iB_j T=B_jA_i T=B_jA_k T=A_kB_j T=A_kB_i T=B_iA_k T=B_iA_i T.
$$
The same computation and the commutation of operators on distinct factors show that $AB$ is transferable. All powers of one transferable operator are transferable, also when $s=2$, because the two position copies commute. Consequently, for $s\ge3$ take the ordered product $D=A_2\cdots A_s$, and for $s=2$ take $D=A_2$. Then $D$ is transferable, and applying $(1,A_2,\ldots,A_s)$ gives $D$ in the first slot alone. Move the operators to the first slot in order $2,\ldots,s$, applying the transfer law to the original tensor and commuting with each remaining slot operator. For any transferable $B$ with $B^s=D$, applying $B$ in every position also gives $D$ in the first slot. Therefore the single map $P_1B$ in all positions realizes the original transformation of that block.

Over $\mathbb F_q$, if $s$ is coprime to the order of $\mathrm{GL}(V)$, choose $e$ with $se\equiv1\bmod |\mathrm{GL}(V)|$. Then $B=D^e$ is an invertible transferable root. In dimension $t$ the order is $q^{t(t-1)/2}\prod_{j=1}^t(q^j-1)$, which proves sufficiency under the stated condition. Its bit length is $O(t^2\log q)$, so modular inverse and repeated squaring extract the witness in polynomial time. Other blocks are kept fixed during extraction and can then be processed in the same way. This argument includes tensors of zero support and arbitrary radicals.

For necessity when $s\ge3$, let $R$ be a finite-dimensional commutative $K$-algebra with a linear functional $\lambda$ such that $(x,y)\mapsto\lambda(xy)$ is nondegenerate. For each unit $a$ define the symmetric tensor by its $s$-linear form on $R$
$$
T_a(x_1,\ldots,x_s)=\lambda(a x_1\cdots x_s).
$$
These tensors are all ordinarily equivalent, by multiplication in one argument. Their transferable endomorphisms on the argument space are exactly the multiplication maps by elements of $R$. To see this, transfer an endomorphism $P$ between the first two slots and vary the third input, taking all others equal to one. Nondegeneracy gives $P(x)y=xP(y)$ for all $x,y$, and setting $y=1$ completes the characterization.

A tied isomorphism between two of the forms conjugates their transfer algebras. It therefore induces a $K$-algebra automorphism $\sigma$ of $R$. The isomorphism on $R$ has the form $x\mapsto u\sigma(x)$, by applying it to multiplication of one, and $u$ is a unit by invertibility. For $R=\mathbb F_{q^j}$ and $\lambda=\operatorname{Tr}_{R/K}$ the pairing is nondegenerate and $\lambda\circ\sigma=\lambda$. Thus $T_a$ and $T_1$ are tied-isomorphic exactly when $a$ is an $s$-th power in $R^\times$. The cyclic group $R^\times$ gives a counterexample in dimension $j$ whenever $\gcd(s,q^j-1)>1$.

If $p\mid s$ and $n\ge2$, use $R=K[t]/(t^2)$ with $\lambda$ extracting the coefficient of $t$. The argument works for every $s\ge2$ and every field of that characteristic. For $a=1+t$ the forms $T_a$ and $T_1$ are ordinarily equivalent by the one-slot multiplication argument. Every $x^s$ belongs to $K$ because $p\mid s$, so $T_1(x,\ldots,x)=0$ identically. Yet $T_a(1,\ldots,1)=1$. An invertible tied map preserves identically zero diagonal evaluation. This proves the forms are in distinct tied classes, and the argument persists over every extension field.

For order two in odd characteristic, the finite-field criterion fails already in dimension one, where a nonsquare scalar gives distinct tied classes and one ordinary class. In characteristic two, dimension one satisfies the criterion, and the dual-number argument covers every larger dimension bound. This completes the finite-field criterion.

### Algebraically closed fields

Suppose $K$ is algebraically closed and has characteristic prime to $s$, or characteristic zero. Every invertible matrix $D$ has an $s$-th root in $K[D]$. Factor its minimal polynomial into powers of $x-\lambda$ with $\lambda\ne0$. On the local factor $K[z]/(z^a)$ at $x=\lambda+z$, start with any $s$-th root $b_0$ of $\lambda$. Given an approximate root through degree $j-1$, adding $c z^j$ changes the degree-$j$ coefficient of its $s$-th power by $s b_0^{s-1}c$. This scalar coefficient is invertible, so lift to the required root one coefficient at a time. The Chinese remainder theorem gives a polynomial root of $D$. If $D$ is transferable then so is that polynomial, by linearity and the power rule. Apply the same equalization step as over finite fields. In dimension one scalar roots suffice in every characteristic. The dual-number example proves necessity for dimension bound at least two when $p\mid s$.

The equalization also applies to the general vector-valued symmetric-equivalence condition. For maps $F:U^s\to V$ and $G:(U')^s\to V'$, suppose that one invertible output map $\psi$ and invertible input maps $P_1,\ldots,P_s$ satisfy
$$
G(P_{\sigma(1)}x_1,\ldots,P_{\sigma(s)}x_s)=\psi F(x_1,\ldots,x_s)
$$
for all permutations $\sigma$ and all inputs. For any slots $j,k$, compare the identity with $P_1$ at $j$ and $P_i$ at $k$ to the identity with these assignments swapped. Writing $A_i=P_1^{-1}P_i$, the first identity evaluated on $(A_i x_j,x_k)$ and the swapped one on $(x_j,A_i x_k)$ have the same two arguments of $G$. Thus $A_i$ can move between arbitrary input slots of $F$. Its inverse also transfers by multiplying the two commuting slot operators by their inverses. Expressing $F,G$ as tensors on the dual input modes and the output mode, the relative maps $(A_i^{-1})^*$ transfer on the tensor of $F$. The preceding product and polynomial-root proof produces one common invertible input map with the same output map $\psi$. This gives the congruence conclusion without requiring $F,G$ themselves to be symmetric.

This corrects the field hypothesis of Theorem 2(a) in the available manuscript *Congruence of matrix spaces, matrix tuples, and multilinear maps*. That theorem states the congruence conclusion for algebraically closed fields of characteristic different from two. Its Section 4 uses polynomial roots of exponent $r+1$ while equalizing groups of maps. For order three in characteristic three, the dual-number forms above are a counterexample even over the algebraic closure. Allowing an invertible coefficient map preserves the vanishing or nonvanishing of diagonal evaluation, so this also contradicts the vector-valued formulation. The corrected uniform conclusion over algebraically closed fields depends on divisibility of the tensor order. In particular the positive conclusion also applies in characteristic two at odd orders. [Belitskii–Futorny–Muzychuk–Sergeichuk, Theorems 2(a), 3(a) and §4](https://arxiv.org/abs/2009.13894)

The argument that equalizes transferable operators generalizes the usual multilinear congruence argument over the complex numbers. The finite-field criterion addresses the exact dimension range where the forgetting functor reflects isomorphism, including the modular obstruction. [Belitskii–Sergeichuk, *Congruence of multilinear forms*](https://arxiv.org/abs/0710.0834)

## Verification

The full scope is proved in writing. The Lean companion checks the transfer step for a single operator, the three-slot calculation for a pair, the normalized averaging identity, and the characteristic-power identity behind the dual-number example. The exact finite replay checks the label maps, modular coefficient cases and finite-field criterion controls. Historical priority and external review remain open.
