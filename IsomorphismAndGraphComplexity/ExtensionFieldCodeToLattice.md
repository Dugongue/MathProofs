# Reducing linear code equivalence over extension fields to lattice isomorphism

Bennett and Win proved a reduction from linear code equivalence over prime fields of polynomially bounded order to lattice isomorphism. Cheraghchi, Shagrithaya and Veliche asked for a reduction from a code-equivalence variant over non-prime fields, and Horlemann, Mazumder, Schaller and Weger asked specifically about linear equivalence. The construction here works over every finite field with running time polynomial in the input length and the field order. In particular it is a deterministic polynomial-time many-one reduction over every fixed non-prime finite field, and uniformly when the field order is polynomially bounded. [Bennett–Win](https://eprint.iacr.org/2024/782) · [Cheraghchi–Shagrithaya–Veliche, introduction](https://arxiv.org/abs/2502.07916) · [Horlemann et al., Section 6](https://arxiv.org/html/2607.12870v1#S6)

## 1. Code equivalence as a multiset of lines

Let $F=\mathbb F_p$, let $K=F[\alpha]$ have order $q=p^d$, and suppose $d\ge2$. Use the usual polynomial-basis representation of $K$, so $\alpha$ is the residue class of the polynomial variable. Let $G_1,G_2$ be full-row-rank $k\times n$ generator matrices over $K$. A monomial equivalence is represented by $G_2=S G_1 D P$ for some invertible row operation $S$ over $K$, invertible diagonal matrix $D$ over $K$ and permutation matrix $P$. Different lengths or ranks give inequivalence. Rank zero is trivial, so take $k>0$.

For each $G_a$, let $\mu_a(\ell)$ denote the number of its nonzero columns on each one-dimensional $K$-subspace $\ell\subset K^k$. Count zero columns separately. Monomial equivalence holds exactly when the two counts of zero columns agree and some $S\in\operatorname{GL}_k(K)$ sends the multiset of lines for $G_1$ to that for $G_2$. The forward direction follows by taking the line of each nonzero column of $S G_1 D P$. Conversely, match columns in each projective class by multiplicity, match zero columns arbitrarily, and choose the nonzero diagonal scalars to match the resulting representatives.

## 2. Keeping extension-field linearity after restriction of scalars

Use $U=K^k$ viewed as an $F$-vector space, and put $W=U\oplus U$. Let $L\colon U\to U$ be multiplication by $\alpha$. On each side form four families of columns by applying the following linear maps to every nonzero $x$ of every supported $K$-line $\ell$.
$$
 f_0(x)=(x,0),\qquad f_1(x)=(0,x),\qquad
 f_2(x)=(x,x),\qquad f_3(x)=(x,Lx).
$$
Include exactly $R(jn+\mu_a(\ell))$ copies of each $f_j(x)$, where $R=p^2+1$. Write $H_a$ for the resulting matrix over $F$ after writing the vectors in the chosen prime-field coordinates. Each $H_a$ has $2kd$ rows.

The four image subspaces have pairwise zero intersection since $\alpha\notin\{0,1\}$. Within one family, images of different supported $K$-lines also intersect only at zero. Thus an $F$-projective line in the $j$-th family over $\ell$ contains exactly $p-1$ distinct included vectors, each occurring $R(jn+\mu_a(\ell))$ times. Dividing its column multiplicity by $R(p-1)$ recovers $jn+\mu_a(\ell)$. The intervals $jn+1,\ldots,jn+n$ are disjoint, so this recovers both $j$ and $\mu_a(\ell)$.

The union of the supported $K$-lines spans $U$ over $F$. It contains all $K$-multiples of any $K$-basis selected from the original columns, so its $F$-span is the whole of $U$. Hence the columns with each given family label $j$ span $f_j(U)$. In particular $H_a$ has full row rank because the first two families span $W$.

Suppose $T\in\operatorname{GL}_F(W)$ sends the $F$-projective column multiset of $H_1$ to that of $H_2$. It preserves each family label by multiplicity, hence sends each of the four image subspaces onto itself. Preservation of the first two gives $T(x,y)=(A x,B y)$ with $A,B\in\operatorname{GL}_F(U)$. Preservation of the diagonal gives $A=B$. Preservation of the graph of $L$ then gives $A L=L A$. Since $K=F[\alpha]$, commuting with $L$ is exactly $K$-linearity. The columns of family zero recover the original multiset of supported $K$-lines and their multiplicities. Namely $T$ sends the full set of $F$-lines inside any supported original $K$-line to the full set inside its image under the $K$-linear map $A$. The image line is supported and has the same decoded multiplicity.

Conversely, any $K$-linear $A$ sending the original multisets of $K$-lines to each other yields $T=A\oplus A$. The map $T$ carries $f_j(x)$ to $f_j(Ax)$, with the same multiplicity, for all four families. It therefore sends the exact vector multiset of columns to the other exact vector multiset. A column permutation realizes this equality of multisets, with no column rescaling required.

As a result, when the original zero-column counts agree, the following conditions are equivalent.

- The original $K$-linear codes are monomially equivalent.
- The row codes of $H_1,H_2$ are permutation equivalent over $F$.
- Those row codes are signed permutation equivalent over $F$, where signs belong to $\{1,-1\}\subset F^\times$.

The implication from signed permutation equivalence back to the original codes uses full row rank to produce $T\in\operatorname{GL}_F(W)$ from the equality of row spaces. Individual signs disappear upon passing to projective lines. When $p=2$ the signed and plain permutations coincide.

## 3. Lattices and their shortest vectors

For either row code $C\subset F^N$ of the matrices above, every nonzero codeword has Hamming weight at least $R$. Indeed a nonzero row functional on $W$ is nonzero on at least one column by full row rank. It is nonzero on every repeated copy of that column and that column appears at least $R$ times.

Use Construction A at the prime field
$$
 \Lambda(C)=\{z\in\mathbb Z^N: z\bmod p\in C\}\subset\mathbb R^N.
$$
Every nonzero vector of $p\mathbb Z^N$ has Euclidean norm at least $p$, with equality exactly for the signed axis vectors $\pm p e_i$. Every vector of $\Lambda(C)$ outside $p\mathbb Z^N$ has at least $R>p^2$ coordinates nonzero modulo $p$ and hence squared norm at least $R$. Thus the complete shortest nonzero vector set of $\Lambda(C)$ is $\{\pm p e_i:i=1,\ldots,N\}$.

An orthogonal isomorphism between the two lattices must permute those shortest vectors. After dividing by $p$ it sends each unit axis to a signed unit axis, so is a signed permutation matrix. Reducing that matrix modulo $p$ gives a signed permutation equivalence of the two row codes because each code equals the modular image of its lattice. Conversely a signed permutation carrying one row code to the other carries its whole integral preimage to the other lattice. These are precisely the shortest-vector and isomorphism arguments behind the prime-field step of Bennett and Win. Here the repetitions have ensured the required minimum-distance hypothesis and the graph families retain the field action. [Bennett–Win, Construction A reduction](https://eprint.iacr.org/2024/782)

An integral lattice basis is computable by Gaussian elimination. After permuting the coordinate columns and choosing a row basis, write the row code in systematic form $[I\mid B]$. Its lattice has basis with rows from $[I\mid\widetilde B]$ followed by $[0\mid pI]$, with $\widetilde B$ the entrywise integral lift of $B$. These rows lie in the lattice. For any lattice vector, subtract its integer first-coordinate entries times the first group of rows, leaving a vector supported on the last coordinates and divisible by $p$. The second group generates that remainder. Undo the column permutation to express the basis in the original coordinate order.

## 4. Input and running time

Precheck lengths, ranks and zero-column counts. If either pair of constructed row codes has different lengths, the original codes are inequivalent because an original equivalence preserves the four exact vector multisets. Output any fixed nonisomorphic pair on these immediately detectable no cases, and a fixed isomorphic pair for the trivial yes cases. The construction also handles prime fields by omitting the three extra families and using only the projective line expansion and repetition in one copy of the original row space.

There are at most $n$ supported $K$-lines per side. Each contributes $q-1$ nonzero vectors, four families and at most $4nR$ copies per vector per family. Thus the column length is at most $16n^2(q-1)(p^2+1)$. Field arithmetic, enumeration, systematic form and the explicit basis construction all take time polynomial in $n,k,q$ and the field representation length. This gives a uniform $\operatorname{poly}(n,k,q)$ bound and a polynomial-time many-one reduction in the usual input length for every fixed field or when $q$ is polynomially bounded in the input length. The stronger target of a uniform bound polynomial in $n,k,\log q$ is separate from this result.

Informal proof. The novelty search found the prime-field reduction and the subsequently stated extension-field question. It did not locate a matching extension-field reduction.
