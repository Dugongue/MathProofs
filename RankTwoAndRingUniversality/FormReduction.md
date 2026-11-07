# A smaller tensor-isomorphism reduction for formal forms

**Theorem.** For every field \(F\) and every fixed degree \(d\ge3\), equivalence of formal degree-\(d\) forms in \(n\) variables under invertible linear substitution reduces to ordinary three-tensor isomorphism over \(F\). The largest output mode has dimension \(\operatorname{poly}(d)n^{\lfloor d/2\rfloor+1}\). In particular, cubic forms in characteristics two and three reduce with side \(O(n^2)\). If the characteristic does not divide the multinomial coefficient of the balanced split of \(d\) into three parts, there is a smaller bound of \(\operatorname{poly}(d)n^{\lceil d/3\rceil}\). The all-characteristic result uses upper-block off-diagonal variables to account for the kernel of symmetrization.

## Group the tensor positions and generate the quotient relations

Write \(V=F^n\) for the span of the variables. The degree-\(d\) symmetric algebra is the quotient
\[
\pi:V^{\otimes d}\longrightarrow\operatorname{Sym}^d V .
\]
Its kernel is the sum of \(\operatorname{im}(I-s)\) for any generating set of transpositions \(s\) of the symmetric group. Indeed, differences under all permutations span the kernel by grouping word basis vectors with the same monomial. If \(s_1,\ldots,s_k\) are generators in a product, its difference from identity is a telescoping sum of operators \((I-s_i)s_{i-1}\cdots s_1\). No averaging or division is needed. Choose for each form \(f\) a lift \(\widetilde f\) by placing each monomial coefficient in one fixed ordered word basis entry.

Partition the \(d\) tensor positions into \(I_1,I_2,I_3\). The third group is a singleton, and the first two groups split the other \(d-1\) positions as evenly as possible. Put \(W_i=\bigotimes_{a\in I_i}V\). Generate permutations by the \(d-1\) transpositions that exchange the singleton with one of the other positions. For each generator \(s\), choose the large group \(I_{i(s)}\) that it does not touch. With \(i=i(s)\) and \(j,\ell\) the other two groups, put \(C_s=W_j\otimes W_\ell\) and \(H_s=C_s^*\). On the full ordered tensor product \(s\) acts by identity on \(W_i\) and by a fixed permutation operator \(s_C\) on \(C_s\).

## Encode every kernel correction in a single transporter

Use three enlarged mode spaces
\[
E_i=W_i\oplus\bigoplus_{s:i(s)=i}H_s.
\]
Treat \(V,W_i,C_s,H_s,E_i\) as separately named sorts in a tensor system. Use fixed tensor-product identifications to force the \(W_i,C_s\) maps to be the indicated tensor powers of one common \(g\in\mathrm{GL}(V)\). Use the fixed evaluation pairing on \(C_s\) and \(H_s\), with fixed scalar output, to force the contragredient map on \(H_s\).

For each \(i\), include the fixed inclusion \(W_i\to E_i\) and all quotient projections \(E_i\to H_s\). This requires the \(E_i\) map to have diagonal blocks given by the already prescribed maps on \(W_i\) and \(H_s\), zero blocks between distinct \(H_s\), and arbitrary off-diagonal blocks \(Z_s:H_s\to W_i\). Every such map is invertible because its diagonal blocks are invertible. There are no further restrictions on the \(Z_s\).

Write \(\operatorname{coev}_{C_s}=\sum_\alpha c^\alpha\otimes c_\alpha\in H_s\otimes C_s\) for the identity pairing tensor, and put
\[
D_s=(1\otimes(I-s_C))\operatorname{coev}_{C_s}.
\]
Embed \(D_s\) into \(E_1\otimes E_2\otimes E_3\) with \(H_s\) in slot \(i(s)\), and \(W_j,W_\ell\) in the other slots. The one data tensor in this enlarged product is
\[
\Theta_f=\widetilde f+\sum_sD_s .
\]
The diagonal blocks in a transporter fix each \(D_s\) in its own graded block. This follows from the identity pairing and commutation of \(g^{\otimes(d-|I_i|)}\) with \(s_C\). Since \(D_s\) has an enlarged summand in exactly one slot, there are no terms involving a product of off-diagonal blocks. The sole remaining contribution from \(D_s\) is in the base block and equals
\[
(Z_s\otimes A_{C_s})D_s,\qquad A_{C_s}=g^{\otimes(d-|I_i|)} .
\]
As \(Z_s\) ranges over all linear maps, \((Z_s\otimes A_{C_s})\operatorname{coev}_{C_s}\) ranges over all of \(W_i\otimes C_s\). Commutation with \(s_C\) shows the displayed contribution ranges exactly over \(\operatorname{im}(I-s)\) on the original ordered tensor product.

It follows that a system isomorphism carries \(\Theta_f\) to \(\Theta_{f'}\) precisely when there is one \(g\) with
\[
\widetilde f'-g^{\otimes d}\widetilde f\in\ker\pi.
\]
This is exactly \(\operatorname{Sym}^d(g)f=f'\), including in small characteristic. The reverse construction takes a decomposition of the difference as a sum of generator differences, then selects the independent \(Z_s\) realizing them. The algorithm constructing the two instance tensors does not need to find this decomposition or any isomorphism.

## Compile without squaring the side bound

Put the named sorts in a shared direct sum \(X\). Force tensor powers by binary tensor-product identifications through intermediate powers, with degree-one copies tied to the common \(V\) by identity maps. Aggregate these bilinear maps and evaluation maps into one map \(B:X\times X\to X\), using their named input and output blocks. Include multiplication on the scalar sort, so its invertible action must be the identity. Aggregate inclusions, quotient projections and required linear identities into a linear operator \(A:X\to X\). Retain each identical repeated block only once, so adding duplicate constraints does not cancel coefficients in positive characteristic. The complete list of sorts has size polynomial in \(d\).

Assign distinct binary codes to the sorts. For each bit use a diagonal projection \(D_j\) that is identity on the sorts carrying that bit and zero elsewhere. A map commuting with every \(D_j\) preserves all named summands over every field. Thus a common invertible map on \(X\) preserving \(B,A\), all \(D_j\), and the embedded data tensor is exactly the required system isomorphism.

Here is a partitioned 3-tensor encoding whose number of parts is \(O(\log d)\). In each of its three modes use a positive and a negative copy \(X_i^+,X_i^-\) of \(X\), and a marker line \(L_i\). Put a nonzero scalar tensor in \(L_1\otimes L_2\otimes L_3\). If the marker actions are \(c_i\), its preservation gives \(c_1c_2c_3=1\). For each ordered pair \(i\ne j\), put the coevaluation tensor in \(X_i^+\otimes X_j^-\otimes L_k\), in the appropriate slot order, with \(k\) the remaining mode. Dividing each action in mode \(i\) by \(c_i\), the six equations give a connected bipartite graph of coevaluations. They force all normalized positive actions to equal one map and all normalized negative actions to be its inverse transpose.

Put the tensor for \(B\) in the two-negative, one-positive block, and put \(\Theta_f\) in the all-positive block. Encode \(A\) and the projections \(D_j\) in distinct blocks \(X_1^+\otimes X_2^-\otimes M_j\), where each \(M_j\) is an additional named line in the third mode. A nonzero scalar component in \(L_1\otimes L_2\otimes M_j\) forces its action to equal \(c_3\). Each encoded tensor therefore has the same cancelling factor \(c_1c_2c_3\). The block constraints impose exactly the desired common action, and conversely that action extends by identity on all marker lines. [Earlier arity construction](https://github.com/Dugongue/MathProofs/blob/35925fc470bef3d72491015e1e4bab230237f94b/TensorFormQuestions/ArityReduction.md)

Apply Grochow–Qiao IV, Theorem 5.1, to remove the partitions. Its cost is exponential only in the number of partition parts and linear in the original mode sizes. A conservative choice of identity-tag ranks in a stage with original slice size \(n_0\times m_0\) is \((1+n_0+m_0)2^{I-1}\). The possible untagged rank contribution is at most \(n_0+m_0\), so distinct binary tag supports have disjoint rank intervals. The remaining identity blocks in the partition construction enforce the required block structure. As there are only \(O(\log d)\) parts, the total dimension overhead after the three stages is polynomial in \(d\). [Partition compiler](https://arxiv.org/html/2306.16317#S5)

The largest auxiliary power has degree at most
\[
d-\min(|I_1|,|I_2|)=\lfloor d/2\rfloor+1.
\]
There are polynomially many sorts in \(d\), including copies \(H_s\), so the claimed side bound follows. For fixed \(d\), construction time is polynomial in the expanded form input. All entries are copied coefficients or field constants from the fixed structure. This is a size result, not a new worst-case time bound.

## The near-cube-root bound with a nonvanishing multinomial

Let \(a+b+c=d\) be the balanced split. The multidegree-\((a,b,c)\) component of the coproduct \(f(x+y+z)\) defines a \(\mathrm{GL}(V)\)-equivariant map
\[
\Delta_{a,b,c}:\operatorname{Sym}^d V\longrightarrow
\operatorname{Sym}^a V\otimes\operatorname{Sym}^b V\otimes\operatorname{Sym}^c V.
\]
Composing with multiplication gives \(\binom{d}{a,b,c}\operatorname{id}\), as follows by replacing \(x,y,z\) by \(t_1x,t_2x,t_3x\) and comparing the scalar multidegree. If this scalar is nonzero, the map is injective. It gives one trilinear data tensor on the three smaller spaces. Force their actions using the symmetric-algebra product maps through degrees at most \(\lceil d/3\rceil\), and compile as above. This condition holds in characteristic zero and characteristic greater than \(d\). The star-transposition construction supplies the unconditional result without requiring the multinomial to be nonzero.

The previous all-field symmetric-algebra reduction through the entire degree-\(d\) space has side at most \(O_d(n^d)\) using a linear-length compiler. The quotient corrections above improve that size bound. The proof is informal. It does not establish an all-characteristic cube-root bound, and no separate named open question demanding the exact improved exponent was located.

