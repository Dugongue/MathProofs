# Linear-logarithmic Cayley encodings of finite-field tensors

## GP-0092

For every finite field $\mathbb F_q$ there is an exact object-by-object encoding from three-tensors of a fixed format $(a,b,c)$ to class-two $p$-groups, where $p$ is the characteristic. The group has order $q^{O(a+b+c+1)}$, and its Cayley table has that same asymptotic size exponent. Odd-characteristic outputs have exponent dividing $p$, and binary outputs have exponent dividing four. On balanced growing formats, no object-by-object exact encoding into arbitrary finite groups can have group order $q^{o(n)}$ at fixed $q$. Thus the linear logarithm of the output order is optimal in this model.

### The encoded group

Use the input tensor as a bilinear map $T:U\times W\to C$ over $F=\mathbb F_q$, using dual bases on its two inputs if necessary. Restrict scalars to the prime field $k=\mathbb F_p$. Add a space $G$ of scalar guards with a named $k$-basis. If $F=k$, use two guards per input, both equipped with the identity operator. Otherwise use three guards per input, paired with multiplication operators $I$, $m_\theta$, and $m_{\theta+1}$, where $\theta$ is the element in a field presentation $F=k[\theta]$ of degree $e>1$. These three multiplications are invertible. Denote the total number of guards by $g\le 6$, with index sets $I_U,I_W$ specifying the input paired with each guard.

Choose $M>\dim_k U+\dim_k W+\dim_k C+g$. For guard $j$ take a private $k$-space $X_j$ of dimension $2^j M$, indexing guards from zero. Let $L=U\oplus W\oplus \bigoplus_j X_j$ and $E=L\oplus G$. Take the central space $Z$ to be the direct sum of $C$, copies $U',W'$ of the two inputs, and copies $X'_j$ of the private spaces. For $s=\sum_j s_jg_j$ in $G$, define the linear map $D_s:L\to U'\oplus W'\oplus\bigoplus_j X'_j$ by multiplying $u$ by $\sum_{j\in I_U}s_j\gamma_j$, multiplying $w$ by $\sum_{j\in I_W}s_j\gamma_j$, and multiplying $x_j$ by $s_j$, with $\gamma_j$ the indicated scalar $1,\theta,\theta+1$ or two copies of $1$. All the operators and dimensions are explicitly given.

The group has underlying set $E\oplus Z$. For $v=(u,w,x,s)$ and $v'=(u',w',x',s')$, put
$$
(v,z)(v',z')=(v+v',z+z'+T(u,w')+D_{s'}(u,w,x)).
$$
Bilinearity gives associativity and inverses. Its commutator is the difference of the two bilinear cross terms. Thus the group has class at most two. The $m$th power of $(v,z)$ is $(mv,mz+\binom m2\, (T(u,w)+D_s(u,w,x)))$, proving the asserted exponents. The displayed $Z$ is the whole center. A nonzero guard component pairs nontrivially with its private $X_j$. When the guards vanish, pairing with individual guards detects each nonzero $u,w,x_j$ in its own summand. The quotient by the center is therefore the elementary abelian group $E$.

### Reflection by ranks of linear maps

On $E$ use the intrinsic commutator map $\beta:E\times E\to Z$. Every vector of $L$ has adjoint rank at most $\dim_k C+g$, since its brackets with $L$ are in $C$ and there are only $g$ guard columns. A vector with a nonzero guard coordinate $s_j$ has adjoint rank at least $\dim_k X_j\ge M$, witnessed by bracketing with $X_j$. This recovers $L$ intrinsically. The subspace $C_T=[L,L]$ is exactly the linear span of the values of $T$.

The pairing $L\times (E/L)\to Z/C_T$ is well-defined, and its maps on $L$ are exactly the displayed $D_s$ with zero component in $C/C_T$. If $s$ has support $J$, the rank of $D_s$ equals $\sum_{j\in J}2^j M$ plus a number between zero and $\dim_k U+\dim_k W$, since all private target spaces and the two data targets are disjoint. Therefore the integer part of the rank divided by $M$ recovers the binary support mask, even if one of the combined field multipliers vanishes. This detects each guard line individually. Intersections of the kernels of the guards outside $I_U$, together with quotienting out the intrinsic private spaces, recover $U$, and the same procedure recovers $W$. Each $X_j$ is the intersection of all guard kernels except the $j$th. Both inputs have another guard acting invertibly, and every other private space is detected by its own guard. Quotient $L$ by $\bigoplus_j X_j$ and $Z/C_T$ by the span of the intrinsic images $D_{g_j}(X_j)$. The input and output summands are now intrinsically separated by guard types, without assuming that $T$ has zero radical.

A group isomorphism supplies invertible $k$-linear maps $P:U\to U$ and $P':U'\to U'$, with the analogous pair on $W$. Under the fixed identifications $U=U'$, compatibility with each guard gives
$$
P'm_\gamma=k_\gamma m_\gamma P,\qquad k_\gamma\in k^\times.
$$
If $F=k$ there is no further condition to enforce. Otherwise use $\gamma=1,\theta,\theta+1$. Adding the first two identities and comparing with the third, after right-multiplication by $P^{-1}$ we find $k_1 I+k_\theta m_\theta=k_{\theta+1}(I+m_\theta)$. As long as $U\ne0$, $I$ and $m_\theta$ are independent over $k$, so the three scalars are equal. Thus $P$ commutes with $m_\theta$ and is $F$-linear. The same holds for $W$. Zero modes yield the trivial tensor case. The map on $C_T$ is $F$-linear because the commutator intertwines $T$ and the two recovered input maps, and $T(\theta u,w)=\theta T(u,w)$. Extend the map to an $F$-linear isomorphism on the supplied output space $C$ by choosing complements. This reflects exactly the original tensor isomorphism. Conversely a genuine $F$-linear equivalence on the three tensor slots extends to an isomorphism of the displayed group law by using identity maps on guards and tags and copying the input maps on $U',W'$. All arguments concern group isomorphism on a common input format. A pair of unequal formats can be handled directly.

### Size and its optimality

The total prime-field dimension of $E\oplus Z$ is $O(e(a+b+c)+1)$, since the number of tags is bounded independently of all input dimensions and of the field. The group order and table size are therefore $q^{O(a+b+c+1)}$. Before writing the table, every structure constant can be computed in time polynomial in the dense tensor encoding and explicitly given field presentation.

For the contrasting bound, in balanced side $n$ there are at least $q^{n^3-3n^2}$ tensor isomorphism classes, because an orbit has size at most $q^{3n^2}$. The number of group isomorphism classes of order at most $N$ is at most $\exp(O((\log N)^3))$ by the finite-group enumeration theorem, summing the bounds for individual orders up to $N$. An object-by-object exact equivalence map injects these tensor classes into the group classes. At fixed $q$ this forces $\log N=\Omega(n)$. This counting bound applies to pure group outputs without extra markings. General reductions that can inspect both tensors together are outside its scope.

The previous class-two reductions used larger functorial tensors or linear-length alternating gadgets. The present construction gives direct bilinear output of linear total dimension, handles finite extensions by the three simultaneous field operators, and retains the exponent-four binary case while measuring the actual explicit Cayley cost. [Grochow–Qiao, linear-length reductions](https://arxiv.org/abs/2306.16317) · [Prior functorial group reduction](https://github.com/Dugongue/MathProofs/blob/f1a463ce1a77aa494b7d33b81a4cbaac5dcb708b/FunctorialTensorReductions/PROOF.md) · [Finite-group enumeration](https://annals.math.princeton.edu/wp-content/uploads/annals-v173-n2-p04-p.pdf)
