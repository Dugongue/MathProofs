# Tensor isomorphism is complete in one congruence class

**Theorem.** Let $R$ be a finite commutative local ring with nonzero maximal ideal $\mathfrak m$, residue field $k$, and a chosen nonzero $s\in\operatorname{Ann}_R(\mathfrak m)$. There is a deterministic many-one reduction from ordinary three-tensor isomorphism over $k$ to ordinary three-tensor isomorphism on free $R$-modules with the following properties.

- An input of format $(a,b,c)$ maps to an $N\times N\times N$ tensor, where $a+b+c+1\le N\le a+b+c+2$.
- Every output flattening has an $N\times N$ minor of determinant $1$ or $-1$.
- Modulo the ideal $sR$, every output of that format is exactly the same multiplication tensor. It is the multiplication of the unitization of a square-zero module of rank $N-1$, over $R/sR$.
- Every output transporter gives an input transporter, by computing linear maps on explicit quotients and extending them in the respective modes.

The construction uses time polynomial in the dense input and ring-arithmetic costs given $s$ and residue representatives. For $R=\mathbb Z/p^e\mathbb Z$ and $e\ge 2$, take $s=p^{e-1}$. The construction is uniform in $p,e$, with input and output coefficients explicitly represented, and all digits below the last are input-independent. For each fixed $R$, the promised problem is polynomial-time many-one equivalent to unrestricted tensor isomorphism over $R$ and over the prime field of $k$, by the fixed-ring theorem. The proof below is written. [Fixed-ring theorem](https://github.com/Dugongue/MathProofs/blob/main/PrimePowerTensorIsomorphism/PROOF.md)

## 1. A unital associative lift

View the input tensor as a bimap $t:k^a\times k^b\to k^c$, with independent changes in the two input modes and the output mode. Write $B=U\oplus V\oplus W\oplus P$ over $R$, of ranks $a,b,c,d$. Choose $d\in\{0,1\}$ so that $N=1+a+b+c+d$ is prime to the residue characteristic. Multiplication by $s$ identifies $k$ with $sR$ as $R$-modules. Indeed, $\operatorname{Ann}(s)$ contains $\mathfrak m$ and is a proper ideal, so it is $\mathfrak m$. Also $s\in\mathfrak m$, since a unit cannot annihilate $\mathfrak m\ne 0$.

Define the product in $B$ by
$$
xy=s\,\widetilde{t}(\overline{x_U},\overline{y_V})\in sW,
$$
where the notation means entrywise application of $k\cong sR$, so the result is independent of representatives. This is $R$-bilinear and all products involving $W$ vanish. Both bracketings of a triple product in $B$ are zero. Unitize $B$ to $A_t=R1\oplus B$ with
$$
(r,x)(q,y)=(rq,ry+qx+xy).
$$
The output is the multiplication tensor of $A_t$, an ordinary tensor in $A_t^*\otimes_R A_t^*\otimes_R A_t$. Its entries modulo $sR$ are precisely the products involving the unit, independent of $t$. In the first flattening select the columns where the second input is the unit and the output ranges over the basis. For the second flattening do the same with the first input the unit. In the third flattening use columns for the first input the unit and the second ranging over the basis. These three submatrices are identities up to order or transpose.

## 2. Normalizing an arbitrary tensor transporter

A tensor transporter between two multiplication tensors is a triple of invertible $R$-linear maps $f,g,h:A_t\to A_{t'}$ with
$$
h(xy)=f(x)g(y).
$$
Set $a_0=f(1)$, $b_0=g(1)$. The maps of left multiplication by $a_0$ and right multiplication by $b_0$ are bijective, because $h(y)=a_0g(y)$ and $h(x)=f(x)b_0$. A bijective left multiplication supplies a right inverse $a_0u=1$. Injectivity then gives $ua_0=1$ from $a_0(ua_0)=a_0$. Right multiplication gives the corresponding argument for $b_0$. Using these units,
$$
h(xy)=h(x)b_0^{-1}a_0^{-1}h(y).
$$
Therefore $x\mapsto h(x)(a_0b_0)^{-1}$ is an invertible $R$-linear, multiplicative, unital map. Conversely an algebra isomorphism supplies a transporter by taking all three maps equal. This is the associative unital isotopy identity, included here with its ring-level proof. See the companion Lean file for the normalization once the units are given. [Albert, *Non-associative algebras, I*](https://doi.org/10.2307/1968960), [Alsaody–Gille–Pumplün on isotopy over rings](https://doi.org/10.1017/fms.2023.7)

## 3. Recovering the field tensor

In the ordered decomposition $R1,U,V,W,P$, left multiplication by every $x\in B$ sends $1$ into $B$, sends $V$ into $W$, and kills $U,W,P$. All diagonal entries are zero. For $r1+x\in A_t$, the trace of left multiplication is therefore $Nr$. The scalar $N$ is a unit, and traces are invariant under algebra isomorphism, by conjugation of left multiplication. Hence the augmentation ideal $B$ is the intrinsic trace kernel, even in mixed characteristic. No preservation of the displayed blocks is required of the transporter.

Recover on $\bar B=B/\mathfrak mB$ the bimap $q(\bar x,\bar y)$ obtained by applying the inverse of the canonical $R$-linear isomorphism $\bar B\to sB,\ \bar z\mapsto sz$, to $xy$. The product depends only on the residue inputs because its image is annihilated by $\mathfrak m$. An algebra isomorphism restricts to $B$, and its residual map intertwines $q$ because multiplication by $s$ is natural under $R$-linear maps.

Let $L_q=\{x:q(x,-)=0\}$, $R_q=\{y:q(-,y)=0\}$, and $I_q=\operatorname{span}_k q(\bar B,\bar B)$. On $\bar B/L_q,\bar B/R_q,I_q$, the induced bimap is exactly $t$ on its two support quotients and its image. Thus every algebra isomorphism gives a transporter of the supported input bimaps. To obtain a transporter on the original spaces, extend each quotient isomorphism by choosing a complement and a bijection of the corresponding input radicals, and extend the output map from $I_q$ using a bijection of complements. The dimensions match because the original formats match. These are independent operations on the original three roles. They include the zero bimap case. Conversely, a field transporter lifts entrywise on the three indicated blocks to invertible $R$-linear maps, since determinants lifting nonzero residues are units. Use the identity on $1,P$. The resulting block map preserves the product, since all data terms use only residue inputs and lie in $sW$. Inputs of different formats can be rejected before the construction or mapped to a fixed promised NO pair from the format $(1,1,1)$, using the zero and nonzero scalar tensors.

All the maps in the construction are explicit. The output has $N^3$ entries, with input-dependent entries only on the original $U,V,W$ block. For the fixed-ring upper bound, apply the unrestricted fixed-ring reduction to the promised instances. The fixed-characteristic field equivalence takes care of the residue extension. Thus even a common full-flattening lift of one prescribed lower-precision tensor is complete. The identity is a lower-precision transporter for every pair. Full isomorphism requires finding a lower-precision transporter that lifts.
