# Single-generator tensors recover principal-unit groups

Let $R$ be a nonzero finite commutative ring and $U=R^\times$. For $d\ge1$ put $A_d=R[t]/(t^d)$ and let $c_R(d)$ be the number of determinant-one orbits inside the ordinary three-leg orbit of its multiplication tensor. For an integer $e\ge0$, write $U^e=\{u^e:u\in U\}$ and $U[e]=\{u\in U:u^e=1\}$.

**Theorem.** The two multiplication-by-unit determinant images on $A_d$ are $U^d$. Its algebra automorphism determinant image is $U^{\binom d2}$. Consequently
$$
c_R(d)=|U[d]|^2\,|U[\tbinom d2]|.
$$
The function $d\mapsto c_R(d)$ recovers the isomorphism type of the finite abelian group $R^\times$.

Suppose further that $R$ is local with maximal ideal $\mathfrak m$, residue cardinal $q$, and residue characteristic $p$. Put $P=1+\mathfrak m$. For each $j\ge0$ the single truncation
$$
d_j=1+2(q-1)p^j
$$
has both unit determinant images full and its automorphism determinant image exactly $P^{p^j}$. Thus its ordinary tensor orbit contains precisely $(q-1)|P[p^j]|$ determinant-one orbits. These counts recover every cyclic primary factor of $P$, even in residue characteristic two.

For example, $\mathbb Z/8$ and $\mathbb F_2[\epsilon]/(\epsilon^3)$ have the same cardinality and the same residue field. Their principal-unit groups are $C_2\times C_2$ and $C_4$. The count at $d=2$ is 16 for the former and four for the latter. The special probe $d_1=5$ has determinant image $\{1\}$ for the former and $\{1,1+\epsilon^2\}$ for the latter, with counts four and two.

## Substitution determinants with nilpotent constants

The free basis of $A_d$ is $1,t,\ldots,t^{d-1}$. A unit of $A_d$ has unit constant coefficient, and any element with unit constant coefficient is a unit because $tA_d$ is nilpotent. Multiplying by such an element gives a triangular matrix whose diagonal is its constant coefficient repeated $d$ times. Constant units realize all the $d$-th powers.

For $d\ge2$, an algebra endomorphism is determined by $f=\sigma(t)=a+g$, where $a\in R$, $g\in tA_d$, and $f^d=0$. The constant $a$ can be a nonzero nilpotent element. The substitution matrix has columns given by the coordinates of $f^i$. Let $G$ have columns given by the coordinates of $g^i$. Binomial expansion gives the matrix identity
$$
\bigl[1,f,\ldots,f^{d-1}\bigr]
=G\,P(a),\qquad
P(a)_{ji}=
\begin{cases}
\binom ij a^{i-j}&j\le i,\\
0&j>i .
\end{cases}
$$
Here $P(a)$ is an auxiliary matrix on the power basis. The identity needs no assumption that translation by $a$ preserves the ideal $(t^d)$. Its determinant is one by upper triangularity. If $b$ is the coefficient of $t$ in $g$, column $i$ of $G$ starts in degree $i$ and has coefficient $b^i$ there. Therefore $\det(\sigma)=b^{\binom d2}$. An invertible substitution has unit $b$ because this determinant is a unit and the exponent is positive. Conversely every unit $b$ occurs in the automorphism $t\mapsto bt$. For $d=1$ the algebra is $R$, and its sole $R$-algebra automorphism has determinant one, as given by the zero exponent.

## Determinant-one orbits and arithmetic recovery

On the multiplication tensor, the normal form of an ordinary stabilizer consists of $X=L_u\sigma$, $Y=R_v\sigma$, $Z=L_uR_v\sigma$ with independent units $u,v$ and an algebra automorphism $\sigma$. Indeed evaluate $Z(xy)=X(x)Y(y)$ at one, use invertibility to see that $X(1),Y(1)$ are units, and normalize $Z$ by these two units to obtain $\sigma$. If $(d_X,d_Y,d_Z)$ are the three determinants, then the coordinates
$$
(d_Xd_Y/d_Z,\ d_Z/d_Y,\ d_Z/d_X)
$$
are precisely the automorphism determinant and the left and right unit determinants. This coordinate change is an isomorphism of $U^3$. The three determinant maps from the groups of free changes of basis are surjective, and each orbit of their common kernel corresponds to a coset of the stabilizer determinant image. The exact quotient is therefore $U/U^{\binom d2}\times(U/U^d)^2$. Taking cardinalities gives the formula because the index of a power image in a finite abelian group equals the size of its kernel. [Background on tensor and algebra isomorphism](https://arxiv.org/abs/1907.00309)

In the local case, reduction on units is onto $\mathbb F_q^\times$ with kernel $P$. This kernel is a $p$-group, since $x\mapsto1+x$ bijects it with $\mathfrak m$ and the successive maximal-ideal quotients are vector spaces over the residue field. Raising to $q-1$ is an automorphism on $P$ and kills the residue unit, so $U^{q-1}=P$. For $d_j=1+2(q-1)p^j$, we have $d_j\equiv1\pmod{q-1}$ and $p\nmid d_j$. For the latter, $d_j\equiv1\pmod p$ if $j>0$, and $d_0\equiv-1\pmod p$. Thus $U^{d_j}=U$. The automorphism exponent is $d_j(q-1)p^j$, and its image is $P^{p^j}$ because the $d_j$-th power is invertible on $P$. If $b_j=\log_p |P[p^j]|$, the difference $b_j-b_{j-1}$ counts the cyclic factors of order at least $p^j$ in $P$. The displayed family gives all these differences directly.

The probe size is sharp within the single-generator family when (P
e{1}). Let (p^e) be the exponent of (P), and fix (0le jle e). Suppose (dge2) has both unit determinant images full and automorphism determinant image (P^{p^j}). Surjectivity of the (d)-th power implies (gcd(d,|U|)=1). The group (U) has even order, because either (q-1) is even or (P) is a nontrivial 2-group, so (d) is odd. Triviality of the automorphism image in the cyclic residue unit group implies (q-1mid d(d-1)/2). Since (d) is coprime to (q-1), write (d=1+2(q-1)a) with (age1). The automorphism exponent is (d(q-1)a), whose image in (P) is (P^{p^{v_p(a)}}). These power subgroups are strictly decreasing until (P^{p^e}={1}), as can be seen on a cyclic direct factor of order (p^e). Thus (v_p(a)=j) when (j<e) and (v_p(a)ge e) when (j=e). In both cases (dge d_j). For the trivial determinant image, the separate one-dimensional algebra (d=1) is also available.

For general finite $R$, $c_R(1)=|U|$. For a prime $\ell$ dividing this order, put $a_j=\log_\ell|U[\ell^j]|$, with $a_0=0$. If $\ell$ is odd then
$$
v_\ell(c_R(\ell^j))=3a_j
$$
because $v_\ell\bigl(\binom{\ell^j}{2}\bigr)=j$. If $\ell=2$, then
$$
v_2(c_R(2^j))=2a_j+a_{j-1}.
$$
The counts determine the $a_j$ recursively. The differences $a_j-a_{j-1}$, for each $\ell$, again recover the orders of the cyclic factors. This proves that two finite commutative rings have the same full sequence of these orbit counts exactly when their unit groups are isomorphic.

## Scope and verification

The earlier finite-field formula treated the constant term of an automorphism as zero. Scalar translation in the power-basis matrix gives the determinant calculation over a ring and permits nonzero nilpotent constants. The theorem then specializes the general stabilizer calculation to a small connected algebra family, instead of building a separate gadget for each principal-unit power subgroup. Prior work on ring determinants and finite étale orientations provides the broader setting. Bibliographic priority for the orbit-count recovery statement remains open. [Stacks project on determinants over rings](https://stacks.math.columbia.edu/tag/0GSX) · [Grochow–Qiao](https://arxiv.org/abs/1907.00309)

The determinant image and arithmetic recovery have written proofs above. The Lean companion verifies the Pascal factorization and determinant invariance under scalar translation for arbitrary commutative scalar rings. The finite control compares direct substitution matrices and unit multipliers over small rings, including 1,852 invertible substitutions with nonzero constant term. It checked 30,658 substitutions in 23 cases, 42 principal subgroup probes and 16 sharp lengths. [Lean component](C.lean) · [Finite controls](CCheck.py)
