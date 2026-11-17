# Succinct power equations and exponential fields of tensor isomorphism

**Theorem.** Let $F$ be a field, let $c\in F^\times$, and let $M\geq 1$ be given in binary. There is an explicit pair of ordinary three-tensors over $F$, of common format with each side $O(1+\log M)$, which are isomorphic over an extension field $E/F$ exactly when $c$ is an $M$-th power in $E^\times$. The construction has polynomial cost in the dense output size and in the field-element encoding. For $F=\mathbb F_5$, $c=2$, and $M=2^r$, the pair becomes isomorphic over $\mathbb F_{5^d}$ exactly when $2^r$ divides $d$. Thus tensors of side lengths $O(r)$ can have least successful extension degree $2^r$ over $\mathbb F_5$. The same exponential phenomenon occurs over every fixed finite field, including $\mathbb F_2$.

This is an informal result about base change for ordinary tensor isomorphism. It bears on the form problem discussed alongside Grochow–Qiao Open Question 7.6 in the journal version, numbered 10.6 in the preprint. [Grochow–Qiao, §10.2](https://arxiv.org/html/1907.00309#S10.SS2)

## 1. Compile an addition chain

Choose an addition chain $1=m_0,m_1,\ldots,m_R=M$, with each $m_j=m_{a_j}+m_{b_j}$ for indices $a_j,b_j<j$. Binary doubling and adding $1$ needs at most $2\lfloor\log_2 M\rfloor$ steps. When $M=1$, take $R=0$. We first make a partitioned tensor in which an allowed isomorphism acts separately on each block of each mode. All field extensions use these same block labels.

Let $X,Y$ each have dimension $R+1$, with bases $(x_j)$ and $(y_j)$ indexed from $0$ to $R$. In each mode put five blocks $X,X^*,Y,Y^*,L$, using copies in that mode, where $L$ is a line with basis $l$. Subscripts indicate modes. The initial tensor has the following common blocks on both sides.

1. Add $l_1\otimes l_2\otimes l_3$.
2. For $Z=X,Y$ and each ordered pair of distinct modes $i,k$, add the identity tensor on $Z_i\otimes Z_k^*$, multiplied by the anchor vector in the unused mode.
3. Add the tensor
   $$
   D=\sum_{j=0}^R x_j\otimes x_j^*\otimes y_j
   \quad\text{in }X_1\otimes X_2^*\otimes Y_3 .
   $$
4. Add the directed-path tensor
   $$
   P=\sum_{j=0}^{R-1}y_j\otimes y_{j+1}\otimes l_3
   \quad\text{in }Y_1\otimes Y_2\otimes L_3 .
   $$
5. Add the addition-chain tensor
   $$
   B=\sum_{j=1}^R x_{a_j}\otimes x_{b_j}\otimes x_j^*
   \quad\text{in }X_1\otimes X_2\otimes X_3^* .
   $$

In the block $X_1\otimes L_2\otimes L_3$, place $x_R\otimes l_2\otimes l_3$ in the source and $c\,x_R\otimes l_2\otimes l_3$ in the target. Every listed block is distinct, so each equation for the block-preserving isomorphism can be read separately.

## 2. Read the scalar equations from every transporter

Work over any extension field $E$. Write $t_i\in E^\times$ for the action on the anchor in mode $i$. The first tensor block imposes $t_1t_2t_3=1$. Divide each non-anchor block matrix in mode $i$ by $t_i$. This leaves every tensor equation unchanged in normalized matrices because each tensor block has one factor in each mode. All anchors now act as $1$.

For each $Z$, the identity pairing between a plus block in mode $i$ and a dual block in mode $k$ forces their normalized matrices to be inverse transposes. The six pairs with $i\ne k$ form a connected six-cycle on the three plus copies and three dual copies. Thus each plus copy of $X$ has one common action $G$, each dual copy has $G^{-T}$, and the corresponding actions on $Y,Y^*$ have the form $H,H^{-T}$.

In the $D$ block, identify $x_j\otimes x_j^*$ with the standard rank-one idempotent $E_{jj}$. Contracting along $Y_3$ produces the full diagonal algebra in $\operatorname{End}(X)$. Preservation of $D$ implies $G$ normalizes this algebra because $H$ is invertible. Conjugation permutes its primitive idempotents, so $Gx_j=u_jx_{\sigma(j)}$ for a permutation $\sigma$ and nonzero $u_j$. The coefficient identity for $D$ then gives $Hy_j=y_{\sigma(j)}$, with no additional scalar multipliers. Preservation of $P$ forces $\sigma$ to preserve the directed path on $0,\ldots,R$. Its unique source and directed distances fix every vertex when $R\geq 1$, and the only permutation for $R=0$ also fixes the vertex. Thus $G$ is diagonal and $H=I$.

Since the $j$-th summand of $B$ has its own third coordinate, preservation of $B$ gives $u_j=u_{a_j}u_{b_j}$ for each $j$. The last block gives $u_R=c$. Induction along the chain gives $u_j=u_0^{m_j}$, so $u_0^M=c$. Conversely, for a root $u_0\in E^\times$, take the indicated diagonal $G$, $H=I$, their dual actions, and all anchor multipliers equal to $1$. This sends the source to the target on every block.

## 3. Remove the partition and analyze extensions

There are five blocks per mode, with total length $4(R+1)+1$ in each mode. Apply Grochow–Qiao's partition-removal construction to each tensor. The construction adds basis-coordinate gadgets over the given field and the proof of equivalence holds over every field. Applying it to the pair over $F$ and extending scalars to $E$ therefore gives the same equivalence with the partitioned instance over $E$. The output side lengths grow by a constant factor for five blocks. Padding each mode with zero coordinates to the maximum side length, if desired, preserves isomorphism over every field because isomorphisms restrict to the intrinsic spans of all contractions and can be extended from those spans. [Grochow–Qiao, Part IV, Theorem 5.1](https://arxiv.org/html/2306.16317#S5)

For the example, an element $u$ satisfying $u^{2^r}=2$ must have multiplicative order $2^{r+2}$, since $2$ has order $4$. Conversely, in a cyclic group containing an element of order $2^{r+2}$, the $2^r$-power map on that subgroup contains both elements of order $4$. Thus the equation is solvable in $\mathbb F_{5^d}$ exactly when $2^{r+2}\mid 5^d-1$. The valuation identity
$$
 v_2(5^d-1)=2+v_2(d)
$$
follows first for odd $d$ by factoring $5^d-1=(5-1)(1+\cdots+5^{d-1})$, and then by doubling $d$, since $5^d+1\equiv 2\bmod4$. This proves the asserted extension spectrum.

More generally, fix $F=\mathbb F_q$, take $c$ to generate $F^\times$, and allow $M$ supported on primes dividing $q-1$. If $M$ is even assume $q\equiv1\bmod4$. For each prime $\ell\mid M$, the $\ell$-part of $c$ has order $\ell^{v_\ell(q-1)}$. The cyclic-group power equation is solvable precisely when $v_\ell(q^d-1)\geq v_\ell(q-1)+v_\ell(M)$ for every such $\ell$. The lifting-the-exponent identity gives $v_\ell(q^d-1)=v_\ell(q-1)+v_\ell(d)$ under the stated conditions. The extension spectrum is therefore all multiples of $M$, still with tensor sides $O(1+\log M)$.

## 4. Exponential extension degrees over every fixed finite field

Let $F=\mathbb F_q$, and fix an odd prime $\ell$ different from the characteristic. Put $h=\operatorname{ord}_{\ell}(q)$, $K=\mathbb F_{q^h}$, and fix a generator $c$ of $K^\times$. Construct the partitioned pair above over $K$, with $M=\ell^r$. There is a constant-block restriction-of-scalars construction turning this into a pair of ordinary tensors over $F$, with sides $O(h(1+r\log\ell))$. Over every extension $E/F$ its isomorphism is exactly the partitioned isomorphism over $K\otimes_F E$.

Write the coefficient arrays in each supported block triple as $K$-trilinear forms on coordinate spaces, using the correspondence between tensors and forms in fixed bases. The transformation of a form is pullback by the mode matrices, with transposes changing between the two conventions. In each mode restrict each block space to an $F$-space. Retain the $F$-linear map of multiplication by a fixed field generator $\theta$ on each restricted block. On every block triple replace the form $b$ by $\operatorname{Tr}_{K/F}(b)$. After extending to $E$, commutation with multiplication by $\theta$ is equivalent to $K\otimes_F E$-linearity, since $\theta$ generates the scalar algebra even after extension. If a tuple of such transporters preserves the traced form, replacing its first argument by every scalar multiple from $K\otimes_F E$ shows that the form defect pairs to zero with every scalar in the trace pairing. That trace pairing is nondegenerate since $K/F$ is separable and its nondegenerate Gram matrix extends to $E$. Thus the full forms are preserved. The converse follows by taking traces.

For an explicit compilation, treat every restricted block as a distinct space type. Add a plus copy and a dual copy in each of the three modes for each type, and one anchor line per mode. The anchor and the identity pairings for each type have the same role as in Section 2. Use five of the six edges, so the graph of pairings remains connected. On its sixth edge put the multiplication-by-$\theta$ endomorphism in the plus and dual blocks, tensored with the remaining anchor. This forces the common normalized action for that type to commute with the endomorphism. Place the traced forms in their corresponding triples of dual blocks. All block supports of this construction are distinct. The normalized action on these forms is pullback by inverses, which gives precisely the trilinear-form isomorphism condition. The original pair has five blocks per mode, so the compiled partition has a constant number of parts. Apply the same partition removal to obtain one ordinary tensor pair, over $F$ and after every base change.

For $E=\mathbb F_{q^d}$, the scalar algebra $K\otimes_F E$ is a product of $\gcd(h,d)$ fields of order $q^{\operatorname{lcm}(h,d)}$. The partitioned isomorphism problem over the product is solved independently in all factors. In each factor the image of $c$ has the same multiplicative order $q^h-1$. Therefore all factors give a yes answer exactly when
$$
 v_\ell(q^{\operatorname{lcm}(h,d)}-1)\ \geq\ v_\ell(q^h-1)+r.
$$
The left side equals $v_\ell(q^h-1)+v_\ell(d)$ by the lifting-the-exponent formula, since $h\mid\ell-1$ and hence $h$ is prime to $\ell$. This gives the exact spectrum $\ell^r\mathbb Z_{>0}$. For instance, over $\mathbb F_2$ take $\ell=3$ and $h=2$. The least successful degree is $3^r$ with tensor sides $O(r)$.

## Scope

The construction realizes arbitrary binary-encoded power equations as ordinary tensor isomorphism over all extensions of their coefficient field. Over finite fields it gives exponentially large least successful extension degrees in the tensor side length. It strengthens the earlier local examples using products of finite étale algebras. The construction and calculation leave Grochow–Qiao's arbitrary cross-characteristic reduction question open. Publication priority for this construction remains unverified.
