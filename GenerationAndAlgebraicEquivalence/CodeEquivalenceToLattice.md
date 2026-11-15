# Permutation code equivalence over extension fields reduces to lattice isomorphism in bit-polynomial time

For a finite field $K=\mathbb F_{p^e}$ given by a polynomial-basis representation, permutation equivalence of length-$n$ linear codes given by generator matrices with at most $n$ rows reduces by a deterministic many-one reduction to lattice isomorphism in $\operatorname{poly}(n,\log|K|)$ bit operations. The same bound holds for signed permutation equivalence. The proof combines synchronized field descent, a sign marker, and a Construction A lift with a bit-polynomial length bound. This is an informal proof.

The introduction of *Reductions Between Code Equivalence Problems* asks for a reduction to lattice isomorphism from a code-equivalence variant over nonprime fields. This gives the requested reduction with bit-polynomial dependence on the field order for the permutation and signed-permutation variants. The repository's earlier result in *Extension-field codes to lattices* covers the monomial variant in time polynomial in the field order. That result and the separate monomial bit-polynomial question have different runtime scopes. [Cheraghchi–Shagrithaya–Veliche, introduction and Corollary 1.3](https://arxiv.org/html/2502.07916v1) · [Earlier repository proof](https://github.com/Dugongue/MathProofs/blob/main/IsomorphismAndGraphComplexity/ExtensionFieldCodeToLattice.md) · [Horlemann et al., Section 6](https://arxiv.org/html/2607.12870v2#S6)

## Restriction to the prime subfield with synchronized coordinate permutations

Take generator matrices of the two codes and compute full-row-rank generator matrices over $K$. Different block lengths or ranks give immediate no instances, and rank zero gives an immediate yes instance when lengths agree. Let $v_1,\dots,v_n\in K^k$ denote the columns on one side. The problem is whether an invertible $K$-linear map takes the column multiset on one side to that on the other. This follows from the characterization of equality of two row spaces by an invertible change of row basis.

Put $F=\mathbb F_p$, let $U$ be $K^k$ regarded as an $F$-vector space, and fix an $F$-basis $b_0=1,b_1,\dots,b_{e-1}$ of $K$. On $U\oplus F^n\oplus F^e$, with standard bases $u_i$ in the second component and $h_a$ in the third, construct a generator matrix over $F$ with these columns. Write $B=ne$.

| Columns | Number of copies |
|---|---:|
| $(b_a v_i,0,0)$ for every $(a,i)$ | One per pair, counting coincident vectors with their accumulated multiplicity |
| $(0,u_i,0)$ for every $i$ | $B+1$ |
| $(b_a v_i,u_i,h_a)$ for every $(a,i)$ | $B+2$ |
| $(0,0,h_a)$ for every $a$ | $B+3+a$ |

The four families have disjoint supports in the ambient space. The first family can contain coincident vectors, including zero. Its multiplicities are between 1 and $B$. The columns within each of the other families are distinct before repetition. The first family spans $U$, since the original columns span $K^k$ over $K$ and the $b_a$ form an $F$-basis. The second and fourth families span the other two components. Thus the new generator matrix has full row rank even with zero or repeated source columns.

Any $F$-linear isomorphism of the expanded multisets preserves multiplicity exactly. It carries $U$ onto $U$, permutes the second-component basis by one permutation $\pi$, and fixes the third-component basis pointwise. Write $A\in\operatorname{GL}_F(U)$ for its restriction to $U$. The image of $(b_a v_i,u_i,h_a)$ has second and third components $(u_{\pi(i)},h_a)$, which index a unique mixed column in the target. Hence

$$
 A(b_a v_i)=b_a v'_{\pi(i)}\qquad (0\le a<e,\ 1\le i\le n).
$$

By $F$-linearity this identity extends from $b_a$ to any multiplier in $K$. For $x=\sum_i\lambda_i v_i$ and $t\in K$, it gives $A(tx)=\sum_i t\lambda_i v'_{\pi(i)}=tA(x)$. Thus $A$ is $K$-linear and carries the original column multisets to each other. Conversely, an original equivalence witnessed by $A$ and $\pi$ induces the block-diagonal map with restrictions $A$, the permutation $\pi$, and the identity. This map matches all four expanded column multisets.

The matrix has $ek+n+e$ rows and

$$
 B+n(B+1)+B(B+2)+\sum_{a=0}^{e-1}(B+3+a)
$$

columns. Both dimensions are polynomial in $n,e$. All arithmetic is in the given field representation, and writing $F$-coordinates requires $O(\log p)$ bits per entry. Computing the columns and writing the matrices therefore take $\operatorname{poly}(n,e,\log p)$ bit operations; this bound is $\operatorname{poly}(n,\log|K|)$. The construction gives a single prime-field permutation-code-equivalence instance.

## Encoding permutations by signed permutations over the prime subfield

Given two prime-field permutation-code-equivalence inputs, count their zero columns. If the counts agree, delete them from both sides. This preserves permutation equivalence. Unequal counts give an immediate no, and an empty remaining column list is a trivial case. Let $a_1,\ldots,a_s\in F^k$ be the nonzero columns on one side. In $F^k\oplus F$, include one copy of $(a_i,1)$ and $s+1$ copies of $(a_i,0)$ for every $i$, and $s(s+1)+1$ copies of $(0,1)$. Each resulting matrix has full row rank. This is a multiplicity construction of the kind used by Cheraghchi, Shagrithaya and Veliche. [Theorem 3.2 and Construction 3.6](https://arxiv.org/html/2502.07916v1#S3)

Signed permutation equivalence of these new matrices is equivalent to an invertible row map carrying their multisets of sign orbits to each other. Each sign orbit in the first family has multiplicity at most $s$; in the second, multiplicity between $s+1$ and $s(s+1)$; in the third, multiplicity $s(s+1)+1$. These families are disjoint even after passing to sign orbits because the source columns are nonzero. The second family spans $F^k\oplus 0$ and the third spans $0\oplus F$, so any such row map has the form $A\oplus\delta$ with $\delta\in\{1,-1\}$. Matching first-family sign orbits then sends the source column multiset to the target column multiset under $\delta^{-1}A$. A permutation equivalence of the original columns gives an equivalence of all three augmented families under $A\oplus1$. This proves the desired polynomial-size reduction.

## Construction A with short input

Let $a_1,\ldots,a_s$ now denote the columns of a full-row-rank signed-permutation-equivalence input over $F$. Take $D=\lceil\log_2 p\rceil$ and $R=17sD+17$. Replace each $a_i$ by $R$ copies of $a_i$ and 17 copies of each $2^j a_i$ for $1\le j\le D$. The new length is $M=s(R+17D)$. A signed permutation equivalence of the original matrices induces one of the enlarged matrices. Conversely, in the enlarged sign-orbit multiset, divide each orbit multiplicity by $R$ and take the floor. The total number of columns contributed by all the powers with $j\ge1$ is $17sD<R$, so this recovers the original sign-orbit multiset. Any invertible row map matching enlarged sign-orbit multisets must therefore match the original ones.

For a nonzero $x\in F$, some $j\in\{0,\ldots,D\}$ has the least absolute representative of $2^j x$ of absolute value at least $p/4$. Indeed, start at the representative with absolute value at least 1. At any step with absolute value below $p/4$, doubling has absolute value below $p/2$ and so yields another least absolute representative. The threshold is reached by step $D$. It holds immediately for $p=2$.

If a codeword of the enlarged code is nonzero, its generating row functional is nonzero on some original column $a_i$, since the original columns span and each enlarged column is a multiple of an original column. Apply the preceding observation to its value on $a_i$. In the enlarged codeword, at least 17 positions have least absolute representatives of absolute value at least $p/4$, using the $R$ copies if $j=0$. Therefore every integral lift of this codeword has squared Euclidean norm at least $17(p/4)^2>p^2$.

For the enlarged code $C\le F^M$, form

$$
\Lambda(C)=\{z\in\mathbb Z^M:z\bmod p\in C\}.
$$

The preceding norm bound implies that its shortest nonzero vectors are exactly $\{\pm p e_i:1\le i\le M\}$, since these are the shortest nonzero vectors in $p\mathbb Z^M$. An orthogonal lattice isomorphism must map this set to the corresponding set on the other side. Its matrix is consequently a signed permutation, which reduces modulo $p$ to an equivalence of the enlarged codes. Conversely an equivalence by a signed permutation over $F$ lifts to an orthogonal signed permutation over the integers that maps the modular preimages. This uses the Construction A shortest-vector argument of Bennett and Win. The doubling copies supply the required Euclidean norm bound with $O(\log p)$ distinct multipliers. [Bennett–Win, Theorem 5.1](https://eprint.iacr.org/2024/782)

An explicit basis for $\Lambda(C)$ can be constructed by Gaussian elimination over $F$. Put the code in systematic form $[I\mid B]$ after a column permutation. The integer row lifts $[I\mid\widetilde B]$, together with the rows of $[0\mid pI]$, form a basis after undoing the column permutation. In fact, subtracting integer multiples of the first rows cancels the first coordinates of any lattice vector. Its remaining coordinates are then multiples of $p$, which the other rows generate. This lattice reduction has size and bit time polynomial in $s,\log p$. Composing with the previous constructions gives the claimed many-one reduction. Immediate yes or no cases can be sent to fixed corresponding lattice pairs, for example $(\mathbb Z,\mathbb Z)$ or $(\mathbb Z,2\mathbb Z)$.

## Signed permutations over the extension field

For signed permutation equivalence, replace each source generator column $v_i$ by the two columns $v_i,-v_i$ before applying the construction. A signed permutation equivalence induces a permutation equivalence of the expanded lists because it permutes each two-element sign orbit. Conversely, upon passing to sign orbits, each original column contributes two copies of its orbit. An invertible row map taking the expanded lists to each other therefore matches the original columns by sign orbit and multiplicity. Choosing one sign per matched pair recovers the original signed permutation equivalence, also when the field has characteristic two or some columns are zero. This list expansion is the sign-closure reduction credited to Ducas and Gibbons. [Signed-to-permutation reduction, cited in the introduction](https://arxiv.org/html/2502.07916v1)

## Priority and scope

The closest prior prime-field reductions identified are Bennett–Win and Cheraghchi–Shagrithaya–Veliche. The earlier extension-field proof in this repository uses four graph subspaces and expands each supported extension-field line into all $|K|-1$ nonzero scalar multiples. The column construction above preserves the smaller permutation action and needs only the $e$ vectors corresponding to a prime-subfield basis per coordinate. The literature search did not find this bit-polynomial field-descent reduction. This is a priority assessment from the sources checked. [Bennett–Win](https://eprint.iacr.org/2024/782) · [Code-equivalence survey](https://arxiv.org/html/2607.12870v2#S6)
