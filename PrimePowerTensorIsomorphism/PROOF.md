# Tensor isomorphism over fixed prime-power rings reduces to prime-field tensor isomorphism

**Theorem.** For every fixed prime $p$ and positive integer $e$, there is a deterministic polynomial-time many-one reduction from 3-tensor isomorphism over $\mathbb Z/p^e\mathbb Z$ to ordinary 3-tensor isomorphism over $\mathbb F_p$. It applies to tensors in the tensor product of three explicitly presented modules, including nonfree modules. The reverse reduction already lands in free modules. In the notation of Grochow–Qiao–Stange–Sun, this gives

$$
\mathsf{3TI}_{\mathbb Z/p^e\mathbb Z} = \mathsf{3FTI}_{\mathbb Z/p^e\mathbb Z} = \mathsf{3TI}_{\mathbb F_p}.
$$

In particular, unrestricted $\mathbb Z/4\mathbb Z$ tensor isomorphism and ordinary binary tensor isomorphism are polynomial-time many-one equivalent. More generally, the free and arbitrary-module versions over fixed nonzero finite commutative rings with the same prime divisors of their characteristics are all equivalent under deterministic polynomial-time many-one reductions. The proof uses explicit presentations and explicit tensor coefficients in the product of the module generators. The proof is informal.

## 1. A polynomial-size binary structure that keeps the carry

First take $k=\mathbb F_2$ and a finite abelian group $A=\bigoplus_i \mathbb Z/2^{a_i}\mathbb Z$ with $1\leq a_i\leq 2$. Write $[u]$ for the group-algebra basis symbol for $u\in A$, so $[u][v]=[u+v]$, and let $I$ be the kernel of the augmentation $[u]\mapsto 1$. Let

$$
H=k[A]/I^3,\qquad J=I/I^3,\qquad K=(H\otimes_k H)\big/\sum_{r+s\geq 3}J^r\otimes_k J^s,
$$

where $J^0=H$. Keep the multiplication and augmentation of $H$, the bilinear quotient map $q(u,v)=u\otimes v\bmod\sum_{r+s\geq 3}J^r\otimes J^s$, and the linear map $\Delta\colon H\to K$ induced by $[u]\mapsto [u]\otimes[u]$. The basis variables $x_i=[e_i]-1$ for cyclic generators $e_i$ satisfy $x_i^{2^{a_i}}=0$. The full group algebra has precisely those relations: the variables generate and the dimension of the indicated polynomial quotient is $|A|$. In $H$ discard all monomials of degree at least three. The formula

$$
\Delta(x_i)=x_i\otimes 1+1\otimes x_i+x_i\otimes x_i
$$

shows why the coproduct descends to $K$. In $K$, the retained bidegrees have total degree at most two. Denote the image of $[u]$ in $H$ by $j(u)$.

The solutions in $H$ to $\epsilon(g)=1$ and $\Delta(g)=q(g,g)$ are exactly the $j(u)$. Indeed, write

$$
g=1+\sum_i b_i x_i+\sum_{a_i=2}c_i x_i^2+\sum_{i<j}d_{ij}x_ix_j.
$$

Terms of bidegree $(0,s)$ or $(s,0)$ agree automatically. In bidegree $(1,1)$, $\Delta(x_i^2)$ contributes zero, $\Delta(x_i)$ supplies $x_i\otimes x_i$, and $\Delta(x_ix_j)$ supplies $x_i\otimes x_j+x_j\otimes x_i$. Thus the equations are $b_i=b_i^2$ and $d_{ij}=b_i b_j$. The resulting elements are precisely

$$
j(u)=\prod_i(1+x_i)^{b_i+2c_i}
$$

with $c_i=0$ for $a_i=1$. Each tuple of digits is unique by the coefficients of $x_i$ and $x_i^2$. Multiplication of two such jets multiplies the original group-algebra symbols and therefore gives addition in $A$. On an order-four coordinate the output digits are $b_i+b_i'$ and $c_i+c_i'+b_i b_i'$ in $k$. The second-degree coefficients retain the carry explicitly.

An isomorphism of the recorded linear structure preserves this equation, so it gives an additive isomorphism on $A$. Every additive isomorphism induces an isomorphism of the structure because the maps come from group algebra. Conversely the recovered map determines the action on $H$ because the $j(u)$ span it, and it determines the action on $K$ because the images of $q$ span it. This works also for the trivial group, where $H=K=k$.

## 2. Fixed prime powers

Put $k=\mathbb F_p$ and $D=p^{e-1}$. For a finite abelian group $A$ of exponent dividing $p^e$, replace $I^3$ above by $I^{D+1}$ and replace the cutoff $r+s\geq 3$ by $r+s>D$. Again the coproduct descends, since each term of $\Delta(x_i)$ has total augmentation degree at least one. In cyclic coordinates $A=\bigoplus_i\mathbb Z/p^{a_i}\mathbb Z$, the algebra has the monomial basis with $0\leq \alpha_i<p^{a_i}$ and $\sum_i\alpha_i\leq D$. This follows from $(1+x_i)^{p^{a_i}}=1+x_i^{p^{a_i}}$ and the same dimension argument as above.

We verify that the same equation recovers exactly $j(A)$. Every $j(u)$ satisfies it. To prove injectivity, take $u\ne 0$ and let $r$ be the smallest index of a nonzero base-$p$ digit among all its cyclic coordinates. Its image has a nonzero term of degree $p^r$ in $j(u)-1$. The contribution from each coordinate with a nonzero digit at index $r$ is that digit times $x_i^{p^r}$. These distinct monomials are retained by the exponent bounds and the cutoff. Thus $j(u)\ne 1$, which gives injectivity because $j$ is multiplicative on the additive group.

Let $g\ne 1$ satisfy the equation, and let $h_s$ be the first nonzero homogeneous part of $g-1$, of degree $s$. At total degree $s$, the equation reads

$$
h_s(x+y)=h_s(x)+h_s(y),
$$

with the cyclic-power exponent bounds in both sets of variables. The term $x_i\otimes x_i$ in the coproduct affects only higher total degrees in this equality. Every surviving monomial with at least two distinct variables has a mixed output term obtained by placing all powers of one of its variables on the left and all remaining powers on the right. This term has coefficient one and can come from no other monomial. For a pure power of exponent $s$ that is not a power of $p$, choose a nonzero base-$p$ digit at index $r$ with $p^r<s$. The coefficient of $x_i^{p^r}y_i^{s-p^r}$ is nonzero, as seen by expanding $(1+z)^s=\prod_t(1+z^{p^t})^{s_t}$ for the digits $s_t$. Both factors meet the exponent bounds, and again no other monomial contributes. Consequently $h_s$ is a linear combination of pure powers $x_i^{p^r}$ of degree $s=p^r$.

For each such power, $j(p^re_i)=1+x_i^{p^r}$. Choose a product of these genuine images with powers in $\{0,\ldots,p-1\}$ whose degree-$s$ part is $h_s$. Dividing $g$ by this product cancels the degree-$s$ term and preserves the equation. For the latter assertion, every element with augmentation one is a unit, and both $\Delta$ and the map from $H\otimes H$ to $K$ are algebra homomorphisms. Iterating until degree $D$ is passed writes $g$ as a product of genuine images. Thus the isomorphism correspondence of Section 1 holds for every fixed $p,e$.

## 3. Encoding biadditive maps and the tensor

If $B\colon A\times A'\to C$ is biadditive, consider the linear map on the tensor product of the full group algebras that sends $[u]\otimes[v]$ to $[B(u,v)]$. For each fixed $v$, the map on the first group algebra is induced by a group homomorphism, preserves augmentation, and takes $I_A^{D+1}$ into $I_C^{D+1}$. The same holds in the other argument for each fixed $u$. Since the group symbols span the respective algebras, the map descends to a bilinear map

$$
\widehat B\colon H(A)\times H(A')\longrightarrow H(C),\qquad
\widehat B(j(u),j(v))=j(B(u,v)).
$$

An isomorphism of the recorded structures intertwines $\widehat B$ exactly when its recovered group maps intertwine $B$. The forward direction follows by injectivity of $j$. For the reverse direction, test on group symbols and extend by bilinearity.

Over $R=\mathbb Z/p^e\mathbb Z$, every additive isomorphism between the underlying groups of $R$-modules is $R$-linear. For a tensor $T\in M_1\otimes_R M_2\otimes_R M_3$, form $M_{12}=M_1\otimes_R M_2$ and $M_{123}=M_{12}\otimes_R M_3$. Give each of the five modules its $H,K$ sorts and maps. Include the two bilinear maps $\widehat B$ arising from the two canonical pure tensor maps. Include a marked line $k$ with field multiplication and a linear map from the line to $H(M_{123})$ sending $1$ to $j(T)$. Place the augmentation maps into this same line. An invertible linear map on a line preserving multiplication fixes $1$ and thus fixes the line pointwise.

Given an $R$-module transporter of the input tensors, the actions on $M_{12}$ and $M_{123}$ are its induced tensor-product maps. Functoriality gives a transporter of all the marked data. Conversely, a structure transporter recovers one $R$-linear map on each module. It intertwines both pure tensor maps, so the maps on the two auxiliary modules are forced to be the induced tensor-product maps, since pure tensors generate each tensor product additively. Preservation of the marked element implies that these maps send $T$ to the target tensor. This proves the exact correspondence, including zero tensors, modules with torsion, and tensors failing conciseness in any mode.

Free arrays permit a smaller construction. Regard $T$ as the bilinear map $M_1^*\times M_2^*\to M_3$ given by contraction in the first two modes. An action by $(g_1,g_2,g_3)$ on the tensor is precisely a transporter of that map with matrices $g_1^{-\mathsf T},g_2^{-\mathsf T},g_3$. Keep the three corresponding module structures and lift this single bilinear map. This avoids the two auxiliary tensor-product modules. For $\mathbb Z/4\mathbb Z$ the total dimension of the marked structure is quadratic in the sum of the three mode dimensions.

## 4. Constructing the ordinary tensor instance in polynomial time

For each module presentation over $\mathbb Z/p^e\mathbb Z$, obtain cyclic coordinates and the necessary basis changes by elementary Smith operations. To diagonalize, move an entry of smallest $p$-valuation into the pivot position, normalize it by a unit, then clear its row and column using divisibility by the pivot. Recurse on the remaining rectangle. The operations and changes of generators have polynomial size because $p,e$ are fixed. Tensor products have presentations on the products of generators, with relations given by the relations of either factor paired with each generator of the other factor. This constructs both auxiliary presentations and the two pure tensor maps, and permits changing the given coordinates of $T$ into cyclic coordinates of $M_{123}$. For zero free modes given as dimensions of an array with no entries, handle the zero tensor directly by comparing the respective mode dimensions.

For a module with $n$ cyclic factors, both jet sorts have dimension polynomial in $n$. The first basis contains at most $\binom{n+D}{D}$ monomials. The basis for $K$ contains at most $\binom{2n+D}{D}$ pairs of monomials, obtained by retaining total degree at most $D$. All structure maps can be computed with these bases. To compute a bilinear map $\widehat B$ on two basis monomials, express each as a signed sum of at most $2^D$ group symbols by expanding the factors $[e_i]-1$. Evaluate $B$ on the resulting pairs using the original module coordinates and represent its values using the truncated binomial products for $j$. This prescription only uses a constant number of evaluations per basis pair and polynomially many field operations to write their images. Multiplication, augmentation, quotient and coproduct are computed by the explicit monomial identities. This algorithm never builds an entire group algebra of exponential dimension.

If corresponding sorts in the two structures have different dimensions, output a fixed NO instance. Otherwise put the sorts into one direct sum and include a unary subspace relation marking each summand. Extend each marked linear or bilinear map by zero off its specified input summands. The resulting basis-explicit linear structure has fixed signature, with all relation arities at most one and all function arities at most two. Its isomorphisms are exactly the original sortwise isomorphisms. Apply the Futorny–Grochow–Sergeichuk compiler in the basis-explicit formulation of Grochow–Qiao, Theorem 10.3. It gives one instance of ordinary 3-tensor isomorphism over $k$ in deterministic polynomial time. The final instance uses the plain product of three general linear groups. [Wildness for tensors](https://arxiv.org/abs/1810.09219), [basis-explicit compiler, Theorem 10.3](https://arxiv.org/html/1907.00309#S10.SS1)

## 5. Reverse reduction and fixed finite commutative rings

For the reverse reduction map a field tensor $T$ to $p^{e-1}\widetilde T$, where $\widetilde T$ is any entrywise lift to $R=\mathbb Z/p^e\mathbb Z$. The map is independent of the lift. Reduction of invertible matrices over $R$ gives invertible matrices over the field, and each invertible field matrix admits an invertible lift because its determinant lifts to a unit. Matrix action on the entries $p^{e-1}R$ depends only on the field reductions of the matrices. The embedded tensor pair is therefore isomorphic over $R$ exactly when the original pair is isomorphic over $\mathbb F_p$. Both tensors are in free modules. Together with Sections 2–4, this proves the claimed equality of classes.

For the upper reduction over a fixed finite commutative ring $R$ of characteristic $p^e$, the underlying additive groups still have exponent dividing $p^e$. For every scalar $r\in R$, include the unary map induced on each $H$ by the additive map $a\mapsto ra$. Each is computed by linear extension on group symbols and descends by augmentation. Intertwining the unary maps is equivalent to commuting with all scalars, by injectivity and spanning. The signature remains fixed. To find the additive presentations in polynomial time, choose once an additive cyclic presentation of $R$ over $\mathbb Z/p^e\mathbb Z$. Translate an $R$-module presentation by taking that many additive generators per $R$-generator and imposing all their cyclic relations. For each given defining relation impose its products by the additive generators of $R$. Those products generate the relation submodule additively. Use the same translation for the two $R$-tensor product presentations and evaluate their coordinate maps by multiplication in the fixed ring. This proves the stated upper reduction without a freeness or principal-ideal assumption on $R$.

## 6. Fixed finite rings with the same prime divisors

For a nonzero fixed finite commutative ring $S$ of characteristic $p^e$, choose a minimal nonzero ideal $I=Sx$. Its annihilator $\mathfrak m$ is maximal because $I$ is simple as an $S$-module. Set $k'=S/\mathfrak m$, a finite field of characteristic $p$. The map $\bar s\mapsto sx$ identifies $k'$ with $I$ as an $S$-module. Therefore an entrywise embedding of $k'$-tensors into $I$ ensures that action by free-mode matrices over $S$ is exactly the action of their images over $k'$. Every invertible matrix over $k'$ lifts to an invertible matrix over $S$. Indeed, a finite commutative ring is a product of its local factors, and a matrix lifting it in the factor with residue $k'$ has unit determinant. Use identity matrices in the other factors. This gives a many-one reduction from $k'$-tensor isomorphism to free tensor isomorphism over $S$.

Use our fixed-characteristic reduction from $\mathbb F_p$ to $k'$ before this embedding. For completeness, the constraint on a putative $k'$-linear transporter $G$ on a base sort $X$ can be included by marking the multiplication maps between successive symmetric powers up to degree $p$. These force the actions on each power to be $\operatorname{Sym}^r(G)$, since products of basis monomials span the next power. Mark also a companion copy of $X$, its identity link to $X$, and the linear map from its basis vectors to $e_i^p$ in $\operatorname{Sym}^p X$. Preservation of the latter two maps gives $G^{[p]}=G$, with the exponent applied entrywise. This is equivalent to $G$ having entries in $\mathbb F_p$. Conversely, every prime-field transporter extends to all the marked spaces. Together with the source tensor over $k'$ and the same compiler, this gives one $k'$ instance, of polynomial size for fixed $p$. [Fixed Characteristic Field Independence for Tensor Isomorphism](https://github.com/Dugongue/MathProofs/tree/main/FixedCharacteristicTensorIsomorphism)

Now let $R,S$ be any two fixed nonzero finite commutative rings with the same set $P$ of prime divisors of their characteristics. Chinese remaindering the scalar integer ring decomposes $R=\prod_{p\in P}R_p$ and $S=\prod_{p\in P}S_p$ by central idempotents, with each factor of prime-power characteristic. The same idempotents split every module, and cross-factor pure tensors vanish by the balancing equations. Thus modules, tensor products and the isomorphism question split componentwise. In each component, apply the upper reduction over $R_p$ to get an $\mathbb F_p$ pair and then use the preceding construction to get a pair over a residue field of $S_p$.

Before embedding these field pairs into the ideals of $S_p$, equalize their three mode dimensions across $p$ by padding with zeros in each mode. Padding preserves field TI: every tensor lies in the product of its three mode support spaces (the images of the flattenings), and an isomorphism of padded tensors restricts to isomorphisms of these supports. Since the original format of the two tensors in each pair is the same, extend those isomorphisms to invertible maps on the original mode spaces. Conversely extend any original transporter by the identity on the added coordinates. If a produced field pair has unequal formats, it can instead be replaced by a scalar NO pair before padding. Finally embed each padded pair into its chosen ideal of $S_p$ and assemble the entries by Chinese remaindering. The two resulting free $S$-tensors are isomorphic exactly when all component pairs are. Swapping $R,S$ proves the asserted equivalence, including between the free and arbitrary-module versions.

## Provenance and scope


The augmentation quotient belongs to the classical Passi construction. This proof uses a coproduct with a total-degree cutoff to recover the original group elements, extends each input biadditive map to the truncated algebras, and then applies the existing linear-structure compiler. Grochow–Qiao–Stange–Sun's Theorem 1.6 compares five tensor actions within $\mathbb Z/p^e\mathbb Z$. The reduction here changes the coefficient ring. The running time is polynomial for each fixed ring, with constants and degree allowed to depend on the ring. Publication priority for this particular application has not been established. [Passi, *Group Rings and Their Augmentation Ideals*](https://link.springer.com/book/10.1007/BFb0067186), [Grochow–Qiao–Stange–Sun, *Over commutative rings*](https://arxiv.org/html/2611.00735v1#S1.Thmtheorem6)

The accompanying [binary carry check](CARRY_CHECK.py) exhaustively verifies the group-like equation and addition for the ten group types with at most three cyclic factors of order two or four. It tests 1,023 augmentation-one candidates, 155 distinct group elements, and 5,797 ordered addition pairs, summed across group types. This check covers the quadratic encoding on these finite examples. The all-input reduction is established by the informal proof above. The exposition and checker were prepared for MathProofs with AI assistance. No third-party code is included.
