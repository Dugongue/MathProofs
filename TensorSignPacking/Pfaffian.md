# One sign from a Pfaffian evaluation diagram

Let $A$ be first-mode determinant-one isomorphism of explicit three-tensors over $F=\mathbb F_3$, and let $O$ be ordinary tensor isomorphism. View a tensor of format $n\times n\times r$ as a linear pencil $M:W\to\operatorname{Mat}_n(F)$, where $W=F^r$ is the space of contraction arguments. The target has pencil $N$ on $W'$. The source and target coordinates identify the tested mode with the left matrix action.

**Theorem.** Suppose $n$ is even, and each of the two spaces of matrices
$$
\mathcal C_M=\{B: M(z)B\text{ is alternating for all }z\in W\},
\qquad
\mathcal C_N=\{B: N(z)B\text{ is alternating for all }z\in W'\}
$$
is one-dimensional with an invertible generator. If the alternating pencil obtained by applying the source generator on the right has an invertible value over $K=\mathbb F_{3^e}$, then the signed comparison reduces to one ordinary three-tensor comparison over $F$ with size and construction time polynomial in the dense input size and $3^{er}$. The reduction is deterministic and needs neither supplied frames nor a supplied nonsingular value. In particular, it is polynomial when the dense input length is $L$ and $er=O(\log L)$, with the constant in this size bound fixed in advance. An arbitrary second $A$ comparison can then be packed with this one into a single $A$ instance.

A fixed extension, including $K=F$, permits $r=O(\log L)$ and an arbitrarily large tested dimension. No conclusion is made here when the scanned alternating pencil has only singular values.

## 1. Recover the congruence description without changing the tested sign

Compute each displayed space by imposing the alternating equations on the $r$ coordinate slices. These are homogeneous linear conditions on the entries of $B$. Choose the generators $B_M,B_N$ by a fixed basis rule and test invertibility. Right multiplication by these generators makes the pencils alternating:
$$
\widehat M(z)=M(z)B_M,\qquad
\widehat N(z')=N(z')B_N.
$$
Only the untested matrix coordinate was rebased. For the recovered pencils the spaces $\mathcal C_{\widehat M}$ and $\mathcal C_{\widehat N}$ equal $F I$ by the bijective right-coordinate change and because $I$ belongs to both spaces.

Write an ordinary left-right transporter between the recovered pencils as
$$
\widehat N(Cz)=P\widehat M(z)Q^{\mathsf T},
$$
where $P,Q$ and $C:W\to W'$ are invertible. This convention absorbs the inverse transpose from the tensor's third mode into the contraction argument map $C$. Put $J=P^{-1}Q$. Since $P^{-1}\widehat N(Cz)P^{-\mathsf T}$ is alternating, the matrix $\widehat M(z)J^{\mathsf T}$ is alternating for every $z$. Hence $J^{\mathsf T}=\alpha I$ for some $\alpha\in F^\times$. Replace $C$ by $\alpha^{-1}C$. Then
$$
\widehat N(\alpha^{-1}C z)=P\widehat M(z)P^{\mathsf T}.
$$
The first map $P$ is unchanged. Conversely such a congruence transporter is an ordinary left-right transporter using $Q=P$. Thus the signed comparison is precisely congruence with arbitrary argument map and $\det P=1$. The dimension-one condition used here concerns only the space of right multipliers that make every slice alternating. In particular, a scalar pair-adjoint algebra is sufficient but is not required.

## 2. Evaluate the relative invariant over a small extension

Take
$$
p_M(z)=\operatorname{Pf}(\widehat M(z)),\qquad
p_N(z')=\operatorname{Pf}(\widehat N(z'))\qquad (z\in K^r,\ z'\in K^r).
$$
Compute all values by polynomial-time elimination for alternating matrices over $K$. Swapping two indices changes the Pfaffian by a sign, and eliminating the first nonzero paired pivot factors out that pivot. This gives a direct algorithm through the alternating block diagonal normal form and returns zero on singular matrices. The field can be constructed deterministically by enumerating monic degree-$e$ polynomials over $F$ and testing irreducibility. The enumeration is within the stated budget when $r\ge1$. For $r=0$ the active nonsingular condition fails in positive dimension.

Every congruence transporter as above has the covariance
$$
p_N(Cz)=\det(P)p_M(z).
$$
This is the standard Pfaffian congruence identity over any field of odd characteristic. It follows over the integers by alternating multilinearity, or by the top exterior-power identity over characteristic zero followed by reduction of the polynomial identity modulo three. At a nonsingular value $p_M(z)$ is nonzero. Thus equality of the two tables along the same argument map is equivalent to $\det(P)=1$. Equality is required for all points, but the nonzero test is used only to justify the reverse implication.

## 3. Encode table comparison as ordinary tensor isomorphism

Use a tensor system with the original alternating tensor on $V\otimes V\otimes W^*$, and the same $V$ action on both occurrences. Add the split algebra $D=F^{K^r}$, with basis $\{u_z:z\in K^r\}$ of coordinate idempotents. Include its multiplication and unit. An isomorphism of this algebra permutes the coordinate idempotents, by the intrinsic description of the primitive idempotents of a product of fields.

Fix the $F$-coordinate space $E=F^e$ of $K$ on both sides by marking a first basis vector and a directed nilpotent shift on this space. An isomorphism that respects these marks fixes all the consecutive images of the marked basis vector, hence is the identity on $E$. Include $W\otimes_F E$, linked to $W$ and $E$ by their usual bilinear tensor-product map. Give the two linear maps
$$
D\longrightarrow W\otimes_F E,\quad u_z\longmapsto z,
\qquad
D\longrightarrow E,\quad u_z\longmapsto p_M(z)
$$
in the chosen field coordinates, with the analogous maps for $N$. The first map uniquely forces the permutation of idempotents to be $u_z\mapsto u_{Cz}$ for the argument map $C$ in the alternating-tensor comparison. The second map enforces equality of Pfaffian values along exactly that permutation. In particular a table permutation cannot substitute for a different argument map on the original pencil.

A positive original transporter extends to the whole diagram by its induced linear maps and permutation of field points. Conversely a diagram isomorphism gives the congruence transporter and the table equality, hence the original signed result. There are a fixed number of sorts and maps, each of fixed tensor order. Apply the ordinary fixed-signature tensor-system compiler to get a single ordinary three-tensor instance. The dense multiplication table of $D$ and all other arrays have polynomial size in $L+3^{er}$. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

The size and nonzero conditions are directly checkable. When only one endpoint passes the one-dimensional alternating recovery or the nonzero table test, the two tensors cannot be ordinary-isomorphic: the recovery is transported by a left-right rebase, and recovered congruence carries nonsingular points by the same base-field argument map. For a binary packing instance, use this theorem when one original comparison satisfies the full condition, then append its resulting ordinary comparison to the other signed test via the existing determinant-neutral conjunction construction. No oracle is called. These are informal proofs.
