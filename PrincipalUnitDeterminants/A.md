# Exact congruence profiles for determinant-one correction

Let $R$ be a finite commutative local ring, let
$$
R=I_0\supsetneq I_1\supsetneq\cdots\supsetneq I_r
$$
be a chain with all $I_j$ proper for $j\ge1$, and put $S_j=R/I_j$. Choose subgroups $H_j\le S_j^\times$. Say the family is compatible if $S_{j+1}^\times\to S_j^\times$ sends $H_{j+1}$ into $H_j$.

**Theorem.** Compatibility is necessary and sufficient for a single finite free unital associative $R$-algebra $E$ to satisfy
$$
\det\operatorname{Aut}_{S_j}(E\otimes_R S_j)=H_j
\quad\text{for every }j.
$$
The algebra can have center exactly $R$, with center exactly $S_j$ after every displayed reduction. In each quotient, the ordinary orbit of its multiplication tensor then contains exactly $[S_j^\times:H_j]$ determinant-one orbits. A construction uses diagonal matrix tensors of format $N\times N\times1$ where $N\le 1+r(|R^\times|-1)$, with overhead depending on $R$.

Necessity holds for every finite free algebra. Reducing an automorphism and its inverse gives an automorphism over the shallower quotient, and determinants reduce with the matrices. The sufficiency uses one algebra with fixed multiplication constants, together with exact accounts of how both labels and ordinary isomorphism classes can coalesce upon reduction.

## Determinants of a labelled construction after any quotient

Fix $\Gamma\le R^\times$, put $s=|R^\times|$, and assign an arbitrary tensor $T_a$ of the same positive format to each $a\in\Gamma$. Suppose first that $s>1$. For a nonzero quotient $S=R/I$, let $\Gamma_S$ be the image of $\Gamma$ in $S^\times$. For $b\in\Gamma_S$, define the multiset
$$
M_{S,b}
=\{\!\{\,[T_a\otimes_R S]_{\mathrm{GL}}\;:\;a\in\Gamma,\ \bar a=b\,\}\!\}.
$$
We construct one $R$-algebra, independent of $I$, with exact determinant image
$$
D_S=\{h\in\Gamma_S\mid M_{S,hb}=M_{S,b}\text{ for every }b\in\Gamma_S\}.
\tag{1}
$$
Repeated labels in a quotient matter because they may carry different payloads. Formula (1) compares their actual multisets.

For a tensor $T:U\times V\to W$, let $P(T)$ have three diagonal copies of $R$, with $U,V,W$ in positions $(1,2),(2,3),(1,3)$. The strictly upper product is $uv=T(u,v)$, and the diagonal acts by scalars. This is associative, since three strictly upper factors multiply to zero. The augmentation is projection onto diagonal entry $(1,1)$.

Construct $E$ with a scalar source and a scalar sink. Between them put $L=R^2$. Put an amplified payload $B_a=M_s(P(T_a))$ at each label $a\in\Gamma$, acting on its standard row and column spaces via its augmented quotient $M_s(R)$. Pair its row with its column by their scalar product times $(a,1)$ in $L$. Also put two pure matrix blocks of widths $2s$ and $4s-2$, whose row-column pairings take values in $R(1,0)$ and $R(0,1)$, respectively. All other strictly upper products between these outer blocks vanish. The pairing is balanced over each augmented matrix quotient. Hence it is associative, and there is a diagonal unit. All operations take place in finite free modules, and reduction modulo any ideal gives the same construction with reduced constants and the same matrix widths.

We give the details that control reduction. The strictly upper ideal on all the refined vertices, including the three internal vertices of each payload, is nilpotent. The radical also includes the maximal-ideal matrices on the diagonal. Their sum is nilpotent, and the quotient is the product of the simple matrix algebras over the residue field. Thus this sum is the radical. An automorphism permutes its primitive central quotient idempotents. If transported orthogonal idempotents $(f_i)$ agree modulo the radical with the designated $(e_i)$, the element $u=\sum_i f_i e_i$ is invertible and satisfies $ue_i=f_i u$. Its diagonal blocks are exactly the identities. Indeed each diagonal projection of an $f_i$ is an idempotent congruent to 0 or 1, so it equals 0 or 1 by nilpotence of the diagonal radical. Therefore $u-1$ is strictly upper triangular on the refined blocks. Left multiplication by $u$ and right multiplication by $u^{-1}$ are triangular with identity diagonal, ordered respectively by starting and ending vertices of the Peirce components. Inner conjugation by $u$ has determinant 1 even over $S$.

After this adjustment the automorphism permutes the actual block idempotents. The width-one endpoints are fixed by their directed source-to-sink corner. The two matrix markers have distinct widths, both larger than $s$, so they are individually fixed. The width-$s$ vertices, with edges wherever their Peirce components are nonzero, have connected components precisely the payloads, since $U,V$ are nonzero free modules at every reduction. Thus the payloads are permuted as whole blocks. An isomorphism of $P(T_a)$ and $P(T_{a'})$ aligns its three internal idempotents in their directed order and restricts to an ordinary tensor isomorphism on $U,V,W$. Conversely a tensor isomorphism extends to an augmentation-preserving isomorphism of $P(T)$.

Matrix amplification preserves and reflects algebra isomorphism here. For an isomorphism $M_s(A)\to M_s(A')$, the image matrix units decompose the free right $A'$-module $(A')^s$ into $s$ copies of the same summand $Q$. Krull–Schmidt yields $Q\simeq A'$ from $Q^s\simeq(A')^s$, so a basis change aligns the matrix units, and the first corner gives $A\simeq A'$. The same construction for automorphisms factors them into inner and entrywise maps. Left and right multiplications repeat on independent columns or rows and have $s$-th-power determinants. An entrywise automorphism has determinant an $s^2$-th power. Since $S^\times$ is a quotient of $R^\times$, every automorphism of an amplified payload has determinant 1 over $S$. A full matrix marker has only inner $S$-automorphisms and their determinants are exactly 1 by cancellation of its column and row multipliers. [Krull–Schmidt–Azumaya](https://math.hawaii.edu/~lee/algebra/exch.pdf)

The action on $L\otimes_R S$ is diagonal, say $\operatorname{diag}(x,y)$, because the two marker products pin its coordinate axes. For a payload permutation $\tau$ one obtains
$$
\operatorname{diag}(x,y) S(\bar a,1)=S(\overline{\tau(a)},1),
\qquad
\overline{\tau(a)}=(x/y)\bar a .
$$
Comparing the second coordinates proves the second equality over $S$, even when the difference between any two labels is a zero divisor. The multiplier $h=x/y$ belongs to $\Gamma_S$ by considering label 1. Each payload moves to one with the same reduced tensor class. This forces precisely the multiset condition in (1).

Conversely, for any multiplier satisfying that condition, choose bijections between the corresponding classes within the label fibres. Choose augmentation-preserving identifications of all resulting isomorphic payloads with one model for each class. Permute payloads using these identifications and permute their arrow modules by the standard bases. Act on $L$ by $\operatorname{diag}(h,1)$, scale the row at the first marker by $h$, and fix the remaining components. This is an algebra automorphism. The payload identifications have telescoping determinant product. The block permutation sign is 1 because either $s$ is even and all payload and arrow ranks are even, or $s$ is odd and $-1=1$ in $R$ and its quotients. The remaining determinant is $h^{2s+1}=h$.

Every automorphism with multiplier 1 has determinant 1. After aligning the idempotents, its action on $L$ is $tI$. The payload isomorphisms have telescoping determinant product modulo automorphisms of one model, each with determinant 1 as proved above. On a row-column pair of width $d$, preservation of the scalar pairing up to $t$ gives determinant product $t^d$. All block permutation signs are again 1. The input arrow pairs contribute $t^s=1$ apiece, and the two marker pairs and $L$ give $t^{2+2s+(4s-2)}=1$. Comparing an arbitrary automorphism to the explicit one with its multiplier proves that its determinant is its multiplier. This establishes (1).

Commuting with the idempotents makes a central element diagonal. Within $P(T)$, commuting with its nonzero free $U$ and $V$ forces all three diagonal scalars equal. This gives scalar center for every payload and matrix marker. Commuting with the outer arrow modules and $L$ forces all these scalars to agree with the two endpoints. Thus the center of each reduced algebra is precisely $S$. The determinant images of left and right multiplication by units are both full. For the left image use a unit scaling just the sink diagonal, and for the right image use the source diagonal. The three-leg determinant-orbit count is consequently $[S^\times:D_S]$. Indeed the determinant triples of the multiplication stabilizer are $(\ell\delta,r\delta,\ell r\delta)$, by normalizing a multiplication isotopy with its two input values at the unit. Here $\ell,r$ independently range over $S^\times$ and $\delta$ over $D_S$. The ratio of the first two entries to the third recovers $\delta$ and gives the claimed index.

## Encoding an arbitrary compatible system

Now take $\Gamma=R^\times$, whose image in each quotient unit group is full. Let $K_j\le\Gamma$ be the inverse image of $H_j$. Compatibility gives $K_{j+1}\le K_j$. Choose an injective code $c_j\colon\Gamma/K_j\longrightarrow\{0,\ldots,s-1\}$. Choose $\alpha_j\in I_{j-1}\setminus I_j$, with $\alpha_1=1$. For label $a$, take the matrix $D_a$ with $c_i(aK_i)$ copies of $\alpha_i$ on its diagonal, for every $i$, padded with zeros to a common size $N=1+r(s-1)$. Regard it as the single-slice tensor $T_a(u,v)=u^\mathsf{T}D_a v$.

At level $j$, the entries of types $i>j$ vanish and those of types $i\le j$ survive. Their generated ideals in $S_j$ are distinct: if $i<i'\le j$, reduce the two ideals further to $R/I_i$, where the first has nonzero image and the second vanishes. Each nonunit surviving entry gives an indecomposable cyclic cokernel module $S_j/(\bar\alpha_i)$. Its endomorphism ring is the local ring $S_j/(\bar\alpha_i)$, and its annihilator is the corresponding ideal, so different entry types give nonisomorphic summands. Zero entries give free rank-one summands. An ordinary tensor isomorphism implies ordinary matrix equivalence, since the scalar third-leg action can be absorbed into a row scaling. It therefore preserves the cokernel module. Krull–Schmidt recovers all nonunit multiplicities and the zero multiplicity. The common matrix size then recovers the unit multiplicity. Conversely equality of the surviving multiplicities yields literal equality of diagonals up to a permutation. Hence
$$
[T_a\otimes S_j]_{\mathrm{GL}}=[T_b\otimes S_j]_{\mathrm{GL}}
\quad\Longleftrightarrow\quad aK_j=bK_j .
$$
Here the last coset determines all earlier coset codes because the $K_i$ are nested.

Since $K_j$ contains the label-reduction kernel, each fibre of $\Gamma\to S_j^\times$ is monochromatic, with color given by its $H_j$-coset. All fibres have the same size. Their translation stabilizer in (1) is exactly $H_j$. The reverse inclusion follows by checking the color of the label 1. This proves sufficiency. If $s=1$, the only possibility is $R=\mathbb F_2$ and the algebra $E=R$ realizes the unique compatible system.

For example, take $R=\mathbb F_2[\epsilon]/(\epsilon^4)$ with its powers-of-$\epsilon$ quotients. Prescribe $H_1=\{1\}$, $H_2=S_2^\times$, $H_3=\{1\}$ and $H_4=\langle1+\epsilon^3\rangle$. It is compatible. The four determinant image sizes are $1,2,1,2$ and the four determinant-one orbit counts are $1,1,4,4$. The determinant image need not have monotone size.

There can be a gain in determinant corrections with no merger of payload isomorphism types. For $R=\mathbb F_2[\epsilon]/(\epsilon^3)$, take $\Gamma=\langle g\rangle$ of order 4 with $g=1+\epsilon$. Put the scalar tensor $uv$ at labels $1,g$ and the zero scalar tensor at $g^2,g^3$. At full precision the two color classes are consecutive pairs in the four-cycle of labels, with trivial translation stabilizer. Modulo $\epsilon^2$ there are two collapsed labels, each carrying one tensor of each type, so the full quotient unit group of order 2 occurs as determinant image. The two scalar tensor types remain distinct over both rings.

## Exact correction depth and a relative obstruction

For a single exceptional label 1 carrying $T$, with all other labels carrying $T'$, (1) gives precisely $\{1\}$ at level $j$ if $T$ and $T'$ remain inequivalent there, and otherwise all of $\Gamma_{S_j}$. Fix $\rho\in\Gamma$. Twisting the multiplication by a based map of determinant $\rho^{-1}$ supplies an ordinary transporter at every depth. The determinant-one question at $j$ answers yes exactly when $\rho$ reduces to 1 or the original input tensors become ordinarily isomorphic over $S_j$. Consequently its last successful depth is the maximum of the last depth that hides $\rho$ and the ordinary tensor isomorphism depth. Each set of successful depths is an initial segment by reduction.

However, an automorphism of any of the displayed algebras that is the identity modulo the maximal ideal already fixes every semisimple block. Its multiplier is 1, hence its determinant is 1. Choose a nontrivial attainable principal unit $\rho$ and twist by scaling one coordinate of $L$ by $\rho^{-1}$, leaving the identity fixed. The supplied ordinary transporter reduces to the identity, and determinant-one correction exists. Any determinant-one correction agreeing with the supplied transporter modulo the maximal ideal would normalize to an algebra isomorphism still agreeing there. Composing with the inverse supplied map would give an automorphism trivial modulo the maximal ideal with determinant $\rho$. Thus every valid correction in this example uses a different residue transporter.

The earlier fixed-ring selector handles two payload classes at the top ring. The earlier extension spectra concern field extensions, and earlier fixed-residue linearizations concern correction within a specified congruence class. This result instead gives an exact multiset formula for reduction of a single selector, and realizes every compatible determinant subgroup profile along an arbitrary ideal chain. The construction and orbit counts have written proofs. A finite control independently checked all 22 compatible subgroup systems on the four powers-of-the-maximal-ideal quotients of the ring in the first example. The companion Lean file checks the exact translation stabilizer of quotient coset colors and normalized-line rigidity over commutative rings. [Lean components](A.lean) · [Finite controls](ACheck.py)
