# Tensor isomorphism and stable equivalence of Morita type

**Theorem.** Over every field, ordinary tensor isomorphism is polynomial-time equivalent to stable equivalence of Morita type on an explicit family of commutative split-local symmetric algebras. The algebras have standard grading with Hilbert function $(1,D,D,1)$ and radical fourth power zero. The forward reduction outputs an ordinary multiplication table with no grading, distinguished ideal or symmetrizing functional marked. On the image family, stable equivalence of Morita type is exactly algebra isomorphism. This is an informal theorem about equivalences induced by the usual bimodule data.

The proof reuses the earlier MathProofs constructions of homogeneous quadratic spaces and Gorenstein algebras. The new step is recovery of the tensor from the stable center after quotienting out the entire socle.

## 1. Encode a tensor by a homogeneous quadratic space

Write the tensor as a linear pencil $A(z)\colon V\to U$ with parameter space $Z$. Introduce four distinct pairs of variable blocks. The first pair holds its bilinear form $u^*A(z)v$. Each of the other three pairs holds one universal row $t\,w(z)$ in scalar $t$ and dual variable $w$. Pad the eight blocks to distinct dimensions, all linear in the original maximum dimension, by unused variables. Let $B(z)$ be the sum of the four mixed forms. In the symmetric square of the sum of the blocks, form $H_A$ as the sum of $B(Z)$ and all internal quadratic monomials within individual blocks. Each $B(z)$ for $z\ne0$ has left-versus-right matrix rank at least three from the three independent row copies, so the pencil map is injective.

For a nonzero linear form $\ell$, the space of all $\ell'$ with $\ell\ell'\in H_A$ is intrinsic. The left-versus-right part of a product has rank at most two, so this product has zero $B(Z)$ part. Thus every cross-block term of the product vanishes. If $\ell$ is in a single block, $\ell'$ must be in the same block. If $\ell$ meets two or more blocks, its cross-term equations force each occupied component of $\ell'$ to be proportional to the corresponding component of $\ell$, with opposing proportionality constants across pairs. Unoccupied components of $\ell'$ vanish. The solution space then has dimension at most one. Over an algebraic closure, the maximal linear components of the locus with dimension at least two are exactly the original variable blocks. Their dimensions distinguish them. This exact recovery also forces block preservation under rational equivalence.

A block-preserving equivalence carries the mixed space $B(Z)$ to its counterpart and hence yields one invertible change of parameter $z$. The first pair gives an equivalence of the padded matrices. It restricts to their summed image spaces and descends to the quotients by the common kernels. Extending these maps by arbitrary choices on the unused complements gives an equivalence of the original pencils. Conversely a pencil equivalence extends on every block, using the same parameter change on each row copy. Thus equivalence of unmarked homogeneous quadratic subspaces is TI-hard, including in characteristic two.

## 2. From quadratic spaces to symmetric algebras

Let $H\subseteq\operatorname{Sym}^2(V_0)$ be a quadratic space from the previous step. Put $U_0=V_0\oplus k^{\dim V_0+1}$, $N=\dim U_0$, and $W=\operatorname{Sym}^2(U_0)/H$. The product map is $\beta\colon U_0\times U_0\to W$. For every nonzero $u$, the linear map $B_u=\beta(u,-)$ has rank greater than $N/2$. Indeed, on the added variables $u$ times any nonzero linear form is nonzero and cannot lie in $H$. If $u$ already uses an added variable, $u$ times any nonzero linear form has a term involving added variables, as can be checked after making the added component of $u$ the first added basis vector. In that case $B_u$ is injective.

Make $C=k\oplus U_0\oplus W$ with products of positive-degree elements given by $\beta$ in degree two and zero otherwise. Form the symmetric trivial extension $A=C\ltimes C^*$ with multiplication $(x,f)(y,g)=(xy,xg+yf)$. It is commutative and its symmetrizing functional is $(x,f)\mapsto f(1)$. With $Y=W^*$ its degrees are
$$
  k,\qquad L=U_0\oplus Y,\qquad B=W\oplus U_0^*,\qquad k s .
$$
The degree-one product is $(u,0)(v,0)=\beta(u,v)$, $u\eta=\beta(u,-)^*\eta$ and $YY=0$. The degree-one to degree-two pairing into $ks$ is evaluation on the displayed dual factors. Surjectivity of $\beta$ generates the $W$ component. The $u\eta$ span $U_0^*$, since any vector annihilated by all of them would satisfy $\beta(u,v)=0$ for all $u$, contrary to the rank gap for nonzero $v$. Thus the grading is generated in degree one. The radical $J$ has third power $ks$ and fourth power zero, and $ks$ is the socle by the nondegenerate evaluations and the degree-zero pairing. The Hilbert function is $(1,D,D,1)$ for $D=N+\dim W$.

## 3. Recover the input after the socle is removed

In $A/J^3$, both $L=\operatorname{rad}/\operatorname{rad}^2$ and $B=\operatorname{rad}^2$ are intrinsic. Multiplication by $\ell=(u,\eta)$ from $L$ to $B$ has block matrix
$$
 \begin{pmatrix} B_u&0\\ B_\eta&B_u^{\mathsf T}\end{pmatrix}.
$$
If $u=0$, the rank is at most $N$. If $u\ne0$, the $Y$-inputs give rank $\operatorname{rank} B_u$ inside $U_0^*$, and projection of the other inputs to $W$ gives the same rank again. The rank is therefore greater than $N$. Thus the intrinsic rank-$\le N$ locus equals $Y$. Moreover $YL=U_0^*$ by the spanning argument above. This recovers the original bilinear map on $L/Y$ with target $B/(YL)$ directly from the socle quotient. Its symmetric-square kernel is the original padded $H$.

To cancel the padding, the least subspace supporting $H$ is intrinsic. The identity
$$
 \operatorname{Sym}^2 E_1\cap\operatorname{Sym}^2 E_2
   =\operatorname{Sym}^2(E_1\cap E_2)
$$
follows by using a basis adapted to the intersection, so the intersection of supporting subspaces supports $H$. An equivalence of padded $H$'s induces an equivalence between those minimal supports. They lie in the original equal-dimensional variable spaces, where the maps extend invertibly. Conversely an original equivalence extends to the padding and then to the trivial extensions. The rank threshold $N$ is common for each tensor-format pair. The reduction uses rank recovery in the correctness proof, without needing to solve equations for the locus.

## 4. Stable equivalence forces this socle quotient to agree

For a symmetric algebra $A$, the stable center $Z^{\rm st}(A)$ is the center modulo the ideal of bimodule endomorphisms of $A$ factoring through projective bimodules. It is preserved as an algebra under stable equivalence of Morita type. Its projective ideal is the Higman image. In our commutative algebra the Higman map is multiplication by $\sum_i x_i y_i$ for dual bases of the symmetrizing pairing. Pairing this element against $a\in A$ gives the trace of multiplication by $a$. Every such trace is $(\dim_k A)\bar a$ because multiplication by a radical element is nilpotent, where $\bar a\in k$ is the residue. In particular the Higman image lies in $J^3=ks$. Thus quotienting the stable center by the third power of its radical recovers exactly $A/J^3$, over every characteristic. The stable center is already the full center when $\dim_k A$ is zero in $k$, including characteristic two for this family. [Broué, stable center and the Higman ideal](https://webusers.imj-prg.fr/~michel.broue/Higman.pdf).

It follows that a stable equivalence of Morita type between outputs gives an equivalence of the original pencils. An input equivalence gives an algebra isomorphism, which gives a stable equivalence of Morita type by its invertible bimodule. The multiplication tables have polynomial size. For the reverse reduction on this image family, use the original table itself as a multiplication tensor. A tensor equivalence of unital associative multiplication tensors is an isotopy $R(xy)=P(x)Q(y)$. Writing $a=P(1)$ and $b=Q(1)$ gives $R(x)=P(x)b=aQ(x)$; invertibility forces $a,b$ to be units. Then $x\mapsto a^{-1}R(x)b^{-1}$ is a unital algebra isomorphism. Thus the reverse ordinary TI comparison is exact on the stated image family. [Multiplication tensors and TI-completeness](https://arxiv.org/abs/1907.00309).
