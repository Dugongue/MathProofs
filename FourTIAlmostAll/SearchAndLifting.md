# Transporters and prime-power lifting from almost every first tensor

For every fixed $\mathbb F_q$, the [almost-all four-tensor decision theorem](FullCoverage.md) has a deterministic search version. On a $1-o(1)$ fraction of uniform first tensors, it decides against every target and returns an explicit transporter when one exists. The same statement holds over the standard Galois rings with residue field $\mathbb F_q$, uniformly in the exponent of the ring. This includes $\mathbb Z/p^e\mathbb Z$ for fixed prime $p$ and arbitrary $e$. Time is polynomial in the explicit binary input length, with the modulus given in binary and the ring in its standard polynomial-quotient representation. The algorithms may abstain on exceptional first inputs.

## 1. Generic stabilizers

Put $k=\mathbb F_q$. For a nonzero tensor the scalar stabilizer consists of $(u_1I,\ldots,u_4I)$ with $u_i\in k^\times$ and $\prod_i u_i=1$. Almost every tensor has exactly this stabilizer. Indeed if some $g_i$ is nonscalar, choose $v$ with $g_iv$ outside its line. Restrict $\bigotimes_i g_i-I$ to the tensors $v\otimes y$ in that mode and project its output modulo that line. The result is injective because the other three mode maps are invertible. The rank is at least $n^3$, so the probability a specified such tuple fixes a uniform tensor is at most $q^{-n^3}$. Union over at most $q^{4n^2}$ tuples. The zero tensor has probability $q^{-n^4}$.

The infinitesimal condition is the analogous scalar kernel for
$$
D_T(X)=\sum_{i=1}^4 (I\otimes\cdots\otimes X_i\otimes\cdots\otimes I)T .
$$
For some nonscalar $X_i$, the restriction to $v\otimes y$ and the same projection give rank at least $n^3$, by eliminating all terms from the other modes. Union over all tuples of $X_i$ proves that $\ker D_T$ consists exactly of scalar tuples with scalar sum zero with probability $1-o(1)$. Its dimension can be checked by elimination.

## 2. Inverting a successful field-unit test

In each comparison branch of [the decision theorem](FullCoverage.md), all choices are fixed except for the units on the multiplicity-one fields. Use the compatible field models of its proof. The remaining homomorphism $\Phi$ from these units to the nonzero cell units has entries
$$
 \Phi_s(x)=\prod_j x_j^{a_{sj}},
$$
where the embeddings into the cell are implicit and $a_{sj}$ includes the corresponding Frobenius twists. This notation also accommodates the negative powers of the two dual modes in the [singular-cut construction](https://github.com/Dugongue/MathProofs/blob/main/FixedFieldOrdinaryFourTI/PROOF.md). Put $h=q-1$, and let $m_j$ be the order of the variable field's unit group.

There is an exact inverse on every successful comparison branch whose kernel has exponent dividing $h$. After checking membership of $y$ in the image, solve for each $i$ the integer congruences
$$
 \sum_s b_{is}a_{sj}\equiv h\,\mathbf1_{i=j}\pmod{m_j}\qquad\text{for every }j .
$$
Solvability for every $i$ is equivalent to the exponent condition. Indeed the $i$-th $h$-power coordinate character descends to the image exactly when it kills the kernel. Any character of the image into the algebraic closure's multiplicative group extends to the whole output product. To see this, adjoin generators of the product one at a time, choosing a root of the character value on the first positive power of the new generator in the current subgroup. This defines an extension by the relation specifying that first power. Each character of the output product is a product of its coordinate characters to integer powers, giving precisely the displayed congruences. Integer Smith or Hermite normal form gives solutions of polynomial bit length.

For a preimage $x$, the field value $w_i=\prod_s y_s^{b_{is}}$ equals $x_i^h$. It is computed without constructing the common compositum. Split all the displayed field unit orders into powers of pairwise coprime bases. Starting with the distinct orders, repeatedly split two unequal overlapping bases by their gcd and exact divisions, merging duplicates and recording the changed exponent vectors. Each split decreases the sum of the log sizes of the distinct bases by at least one bit. This is a polynomial-bit algorithm. By cyclic-group CRT powering, separate each contributing field value into the components for these bases. For one base use a field slot with maximal exponent of that base among the displayed orders. Each component can be transported there through the common subfield, since its order divides both field orders. Multiply the contributions there, then transport the product for that base into the variable field for $i$. The latter transport is valid because the entire product lies in that field, and so does each of its CRT components. The gcd-degree subfield identity and all transport algorithms are as in the decision proof.

Factor $z^h-w_i$ in the variable field and select a root $x_i^0$. The degree $h$ is fixed, and the distinct factors are obtained by the same deterministic étale splitting. Any actual preimage differs from this tuple of roots by elements of $k^\times$. Hence the ratio $y/\Phi(x^0)$ has entries in $k^\times$. Solve for a correction in that group by taking logs only in the fixed base field and solving linear congruences modulo $h$. This yields a verified preimage. The kernel is a subgroup of the product of these base-field unit groups, with generators obtained from the same homogeneous congruences. When $q=2$ the kernel and the correction are trivial. All the operations have polynomial bit cost.

## 3. Certification on raw first inputs

On the invertible branch the kernel on each successful comparison branch consists of actual stabilizers, with the already chosen repeated-primary maps pinned. If the raw stabilizer is scalar, the kernel has exponent dividing $q-1$. On the singular branch an element of the field-unit kernel acts on the two enlarged spaces of the singular-cut construction and restricts to a stabilizer of the original tensor on the four supports. When the raw stabilizer is scalar, consider its action $U$ on one enlarged space $E$. Its restrictions on the two original paired modes are scalars $u,v$ with $uv=1$, since they preserve the chosen nonzero kernel form. Divide $U$ by $u$. The result fixes the first original space pointwise and is the identity on the quotient $V_2^*$ dual to the embedded second space. The kernel of the quotient lies in the first space. Thus $u^{-1}U=I+X$ with $X^2=0$. Its order is prime to $p$, since the field-unit actions and $u$ have order prime to $p$. This forces $X=0$. The other enlarged space has the same property, so the field-unit kernel again has exponent dividing $q-1$.

To certify the scalar stabilizer from the first input, run the accepted decision procedure against the first input itself. In every successful comparison branch test the exponent condition, recover one witness and the kernel generators, and verify that their restrictions to the original modes are scalar. Abstain if a test fails. Every successful branch consists of one witness times the kernel, with its repeated-primary choices fixed. Every actual stabilizer occurs in some branch. On the singular branch this follows by transporting the chosen kernel forms and extending the isometry of each form to the enlarged space, as in the decision proof. Thus the test certifies precisely the scalar stabilizer on accepted inputs and succeeds whenever the raw stabilizer is scalar. On any target the exact comparison then either rejects all branches or produces a witness from a successful branch with the same bounded-exponent guarantee. Direct evaluation verifies the witness.

The scalar-stabilizer estimate and the almost-all decision theorem prove $1-o(1)$ coverage for this search procedure. In particular, over the fixed field, determinant constraints on the four mode maps can be tested on this same recognition domain. Given a witness, its other witnesses are obtained by multiplying by the scalar stabilizer, and checking the determinants requires only testing the resulting $n$-th powers in the fixed group $k^\times$.

## 4. Lifting through all powers

Let $R$ be a standard Galois ring with residue $k$ and modulus $p^e$. Apply the field search and both scalar tests to the residue of the first tensor. The stabilizer at every modulus $p^a$ then consists of the scalar unit tuples of product one. Induct on $a$. A stabilizer at level $a+1$ reduces to a scalar tuple at level $a$. Lift those units with product one and divide by them. The remaining element is $(I+p^a X_i)_i$. Its stabilizer equation at level $a+1$ is $D_{\bar T}(X)=0$, so it is scalar of product one by the infinitesimal test.

After finding any residue transporter, lift it arbitrarily to an invertible tuple $\widetilde g$ at the next level. Solve
$$
 D_{\bar T}(X)=\frac{\widetilde g^{-1}T'-T}{p^a}\pmod p.
$$
The division uses the canonical identification of $p^a R/(p^{a+1})$ with $k$. A solution gives the corrected witness $\widetilde g(I+p^a X)$ at that level. If the system is inconsistent, there can be no transporter there. Every possible transporter's lower-level reduction differs from the current one by a scalar stabilizer which lifts and can be removed. Each step is a linear system with $4n^2$ unknowns and $n^4$ equations. There are $e-1$ steps, with polynomial-bit arithmetic in the modulus. The first tensor's reduction is uniform and the applicability tests use it alone, so the coverage bound is uniform in $e$.

These are informal search and lifting proofs. They use the same exact finite-field cell calculation as the decision proof, together with scalar stabilizer certification and lifting.
