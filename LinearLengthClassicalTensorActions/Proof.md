# Linear-length reductions between the five classical tensor actions

**Published question.** Section 1.5 of Chen–Grochow–Qiao–Tang–Zhang, *On the Complexity of Isomorphism Problems for Tensors, Groups, and Polynomials III: Actions by Classical Groups*, asks for linear-length reductions between the five actions for classical groups. The authors identify preservation of the form during block cancellation as an obstacle. [Journal paper](https://link.springer.com/article/10.1007/s00037-026-00294-x) · [Question and action definitions](https://arxiv.org/html/2306.03135v2#S1.SS5)

**Answer.** There are constant-free polynomial-time kernel reductions between every ordered pair of the five actions for the standard unitary groups over \(\mathbb C\) and \(\mathbb F_{q^2}/\mathbb F_q\), and for the standard orthogonal groups over any field. All output side lengths are \(O(n_1+n_2+n_3)\), with a constant independent of the field. The construction uses a single input-independent layout at each format. This is an informal proof. Publication priority has not been established.

## 1. Field and conventions

Let \(K\) be a field with an involution \(x\mapsto\bar x\), including the identity involution. Write \(U(d)=\{P\mid\bar P^{\,T}P=I_d\}\). Standard coordinate subspaces in an orthogonal direct sum are nondegenerate even if the form has isotropic vectors. Every matrix in \(U(d)\) satisfies \(P^{-T}=\bar P\). Conjugation here acts entrywise. All matrix and slice ranks below are taken over \(K\).

A *partitioned independent action* has each of the three spaces decomposed into standard coordinate blocks, and uses a separate unitary transformation on each block. The proof first removes a fixed number of block constraints in linear length, then uses this operation to implement all five actions.

## 2. Recover every block from two marked slices

Let a tensor \(S\) occupy the three data spaces \(V_1,V_2,V_3\), with prescribed coordinate blocks. Put \(n=\sum_i\dim V_i\). Label two markers for each prescribed block by distinct integers \(j=1,\ldots,b\). Here \(b\) is fixed. Set \(M=n+b+1\). For marker \(j\) assigned to a block \(B\subseteq V_i\), add:

- a private row space \(R_j\) of dimension \(p_j=M+n+j-\dim B\) in mode \(i\)
- a private partner space \(D_j\) of dimension \(s_j=M+n+j\) in mode \(i+1\)
- a private tag line \(Kz_j\) in mode \(i+2\)

Mode subscripts are cyclic. All added spaces are separate coordinate blocks. Insert the identity pairing between \(B\oplus R_j\) and \(D_j\), supported at \(z_j\) in the remaining mode. The word pairing here denotes the tensor \(\sum_{\ell=1}^{s_j}e_\ell\otimes d_\ell\) in the two indicated spaces. Let \(E(S)\) be the sum of \(S\) and all such markers.

### Find the tag lines without choosing any slices

In any mode, view contraction as a map from the mode dual into matrices on the two remaining modes.

1. If the covector annihilates the tags in this mode, the data contribution has rank at most \(n\). Each surviving marker retains a tag vector in one of the other two modes and therefore contributes rank at most one. The rank is at most \(n+b=M-1\).
2. If a covector is nonzero on a tag in this mode, restrict its matrix to the private rows and the corresponding private columns of that marker. On this submatrix the marker is a nonzero scalar times an identity of size \(p_j\ge M\). Other contributions vanish there. Thus its rank is at least \(M\).

Consequently the low-rank covectors are exactly the annihilator of the tag space. Every unitary transporter between two encoded inputs preserves this subspace of the dual and its orthogonal complement. This complement consists of covectors supported only on the tags. This argument uses orthogonal decomposition of coordinate spaces and does not use definiteness or eigenvalues.

In the tag-supported covectors, a nonzero covector on tag \(j\) alone has rank \(s_j<2M\). A covector with at least two nonzero tag coordinates has rank at least \(2M\). To see the latter, keep the two private row and column spaces in the other modes. The resulting submatrix includes their two nonzero private identities as disjoint diagonal blocks, with zero cross blocks. The nonzero rank-\(<2M\) locus in the tag-supported space is therefore the union of individual tag lines. The ranks \(s_j\) are distinct, so each line is preserved individually. The argument works when the field is finite and a nonzero line has only one nonzero element.

### Recover the data blocks and reflect isomorphism

The slice at tag \(j\) identifies its row support \(B\oplus R_j\) and column support \(D_j\). More precisely, these are the two image spaces of its matrix tensor, so any transporter for the encoded tensors preserves them, even when the tag is multiplied by a scalar. Intersect the recovered row supports of the two markers assigned to \(B\). The intersection is exactly \(B\). It follows that every transporter restricts to unitary transformations on all prescribed blocks. Orthogonal projection onto the tensor product of the three data spaces commutes with these transformations and recovers \(S\). This proves the backward implication.

For the forward implication choose a given block transporter \(P_B\) on each \(B\). Act by the identity on private rows and tag lines. On \(D_j\), extend by \(\overline{P_B\oplus I_{R_j}}\). For any unitary matrix \(L\), the identity tensor is fixed by \((L,\bar L)\) because \(L\bar L^T=I\). The extension thus fixes every marker and transports the data. The partner spaces are private, so these choices are simultaneously consistent.

The resulting independent action can also be implemented using **any** target action of the five. Use disjoint copies for the enlarged mode spaces in the common target space wherever the action repeats a group variable. If modes 1 and 2 share a variable, their spaces are two disjoint coordinate summands of that variable's space. If all three share a variable, take the direct sum of all three. A target isomorphism induces three unitary actions, with the prescribed dual on a negative slot. The rank argument applies unchanged in these larger ambient spaces. Conversely, for any independent transporter of the constructed tensor, assign its three matrices on the three disjoint summands. On a negative slot assign the entrywise conjugate of the desired matrix, so that the dual acts by the desired matrix. Extend by the identity on complements. This yields a valid tied target transporter.

## 3. Implement all five source actions

Start with three role spaces holding the three data modes. Include a distinct pin line \(Ka_i\) in mode \(i\) and the tensor \(a_1\otimes a_2\otimes a_3\). Treat all role spaces, pins, and any auxiliary copies below as distinct prescribed coordinate blocks for Section 2. A partitioned transporter acts on the pins by unit-norm scalars \(t_i\), with \(t_1t_2t_3=1\).

For blocks of equal dimension in modes \(i,j\), a wire is the identity tensor between them, tensored with the pin in the remaining mode \(k\). If \(R,R'\) are the block actions on the wired slots, the wire equation is \(t_k R(R')^T=I\). Normalize the action on every block in mode \(i\) by dividing by \(t_i\). The normalized matrices remain unitary. The wire equation becomes \(Q(Q')^T=I\), or \(Q'=\bar Q\). A wire therefore enforces conjugate actions, and two wires along a path enforce equal actions. The normalized action on the three data slots is the same as the original action on the data tensor, since the three scalar factors multiply to one.

Use this layout for the paper's five source actions:

| Source action | Wiring between the three data blocks |
|---|---|
| \((P,Q,R)\) | No wires |
| \((P,P,Q)\) | Join 1 to 2 by a two-wire path through a fresh copy in mode 3 |
| \((P,\bar P,Q)\) | One wire between 1 and 2 |
| \((P,P,\bar P)\) | Join 1 to 2 by a two-wire path through a fresh copy in mode 3, and join 1 to 3 by one wire |
| \((P,P,P)\) | Join 1 to 2 through a fresh copy in mode 3, and join 1 to 3 through a fresh copy in mode 2 |

Every wire occupies a different triple of prescribed blocks. Those triples are distinct from the pin triple and from the data triple. Therefore the wire equations and the pin equation can all be read separately. Conversely, a source transporter extends over the wire paths by alternating \(P\) and \(\bar P\) on their vertices and taking all pin scalars equal to one. This proves exact preservation and reflection of the source action in the partitioned independent problem. Section 2 then removes the partitions and realizes the chosen target action.

## 4. Size, constants, and relation to earlier methods

There are at most eight prescribed blocks across the three modes, including pins and the intermediate blocks. Every dimension added per marker is \(O(n)\) and there are only two markers per block. Direct sums required for a tied target keep the same order of growth. Each output coefficient is zero, one, or a copy of one input coefficient. The construction is a linear-length constant-free p-projection and takes polynomial time for dense inputs. It uses no extensions of the field.

The rank tags retain the rank-invariance idea behind the partition gadgets of Futorny–Grochow–Sergeichuk and Grochow–Qiao. The construction here recovers each prescribed block as the intersection of two marked row supports. It avoids the need to perform any row or column operations inside the form-preserving group. This also uses the observation from the pencil-depth work that slice mixing acts on the whole matrix space, so a marked slice has to be recovered intrinsically from the contraction map. [Linear-length general-linear construction](https://arxiv.org/abs/2306.16317) · [Classical-group question](https://arxiv.org/html/2306.03135v2#S1.SS5)
