# Exact orientation from a commutative Casimir centralizer

Work over $F=\mathbb F_3$. For an ordered basis of a space $D$ of alternating forms on $V$, write $\rho_Y:D\to D'$ for the action $B\mapsto Y^{-\mathsf T}BY^{-1}$ of a congruence $Y:V\to V'$, and compute $\det\rho_Y$ in the supplied bases of $D,D'$. The question is whether an ordinary congruence exists with $\det Y\det\rho_Y=s$, for prescribed $s\in\{1,-1\}$.

**Theorem.** Suppose the inputs are supplied with ordered nonzero nonsingular forms $A\in D$ and $A'\in D'$. Require the congruence to carry $FA$ to $FA'$. Normalize the spaces to the codes $A^{-1}D$ and $(A')^{-1}D'$ in the endomorphisms of $V,V'$. Assume the trace pairing restricted to each normalized code is nondegenerate. On each code $C$ compute an ordered, polynomial-size family of conjugation-covariant matrices, for example the first $n^2$ iterates of its Casimir operator on $I$. If the common centralizer algebra of the source covariants is commutative, there is a deterministic polynomial-time reduction to one ordinary three-tensor isomorphism instance for the prescribed sign. There is no width bound on $D$ or its annihilator. In particular, a cyclic matrix among the covariants, or among their simultaneous word algebra, suffices. The same conclusion holds on unmarked inputs with a polynomial-time, polynomial-size, covariant bank of projective anchor lines containing at least one nonsingular line meeting this test. A bank is covariant when every ordinary congruence carries the bank bijectively to its target bank.

## 1. Normalize the form and align the covariants

For each code $C$, define its Casimir operator by
$$
\Phi_C(M)=\sum_i R_i M R^i,\qquad
\operatorname{tr}(R_iR^j)=\delta_{ij},
$$
where the $R_i$ are any basis. The nondegeneracy hypothesis ensures the dual basis exists. This operator is basis independent and commutes with simultaneous conjugation of all its data. The identities are proved by the Lean declarations Mathproof.CasimirCovariants20261002.casimir_baseChange and Mathproof.CasimirCovariants20261002.casimir_conjFam. Iteration on $I$ gives the indicated covariants. One may enlarge this tuple by generating an ordered linear basis from $I$ using products and applications of $\Phi_C$. At each round test candidates in a prescribed order and retain independent ones. Multiplication, $\Phi_C$, and independence are transported by conjugation, so the resulting ordered list is covariant. The list grows at most $n^2$ times, and each round tests polynomially many candidates.

If the anchor multiplier is $\epsilon$, so $\rho_Y(A)=\epsilon A'$, then for every $B\in D$,
$$
(A')^{-1}\rho_Y(B)=\epsilon Y(A^{-1}B)Y^{-1}.
$$
Thus the normalized codes are conjugate by $Y$ regardless of $\epsilon$, since scalar multiplication does not change a code's span. In particular $Y$ intertwines the ordered covariant tuples. Compute an invertible simultaneous intertwiner $Y_0$ of just these tuples or reject if none exists. This is constructive module isomorphism for the free associative algebra on the labels of the tuple. Its input consists of the displayed matrices, and its cost is polynomial. The intertwining maps then have the form $Y_0 c$ for $c$ in the unit group of the source common centralizer algebra $\mathcal A$. These statements are about the tuple only. Keep the full congruence substitution as part of the final comparison. [Brooksbank–Luks, Testing isomorphism of modules, Theorem 3.5](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

Write $D''=Y_0^{\mathsf T}D'Y_0$ for the transported target space in $\bigwedge^2 V^*$, and carry its supplied basis along by that same pullback. Now the action on forms is $\rho_c=\bigwedge^2(c^{-\mathsf T})$, taking $D$ to $D''$. The determinant of this map in the supplied basis of $D$ and the pulled-back basis of $D''$ equals the original $\det\rho_Y$. The ambient determinant is supplied by the anchor in each of the two branches $\epsilon=\pm1$. If $n=2m$ then
$$
\det(Y)=\epsilon^{-m}\,\frac{\operatorname{Pf}(A)}{\operatorname{Pf}(A')},
$$
because $Y^{\mathsf T}A'Y=\epsilon^{-1}A$. Pfaffians are computed in the original ambient bases by alternating elimination. A nonsingular alternating anchor already implies that $n$ is even. Without an anchor, odd $n$ offers a separate elementary case. The scalar automorphism $-I_V$ changes the ambient sign and acts trivially on all alternating forms, so either prescribed product sign is equivalent to ordinary congruence.

## 2. Refine the exterior square to scalar actions on fields

The algebra $\mathcal A$ is a finite commutative $F$-algebra acting on $V^*$ by the transpose action, which is a representation because $\mathcal A$ is commutative. Use a composition flag of this module. Its ordered successive quotients are explicitly based regular modules $E_i$ of finite fields over $F$, and each $c^{-\mathsf T}$ acts on the $i$-th quotient as multiplication by some $a_i\in E_i^\times$. To construct the flag, find the nilradical as the kernel of a sufficiently high power of Frobenius on $\mathcal A$, and split the reduced quotient into fields. This split uses linear algebra on the fixed space of Frobenius in the reduced quotient, which is a product of copies of $F$. Simultaneous projections for a basis of that fixed space recover its primitive idempotents. The radical-power filtration of $V^*$ has semisimple layers, whose field summands split into field lines by choosing field bases. All dimensions and compositions are computed by linear algebra using the displayed multiplication and module tables.

Choose any vector-space lifts of the successive quotients of the flag. The induced exterior-square flag has components $E_i\otimes_F E_j$ for $i<j$ and $\bigwedge^2_F E_i$ for $i=j$. To see that there is a flag with these precise quotients, write the original flag in a split vector-space basis and order pairs by the larger index, then the smaller index. A map preserving the original flag sends each paired block into itself and earlier paired blocks. The action on the paired block modulo the earlier blocks is the tensor product of the quotient maps, or their exterior square if the indices coincide.

In a cross quotient $E_i\otimes_F E_j$ the action is multiplication by $a_i\otimes a_j$. The tensor product is finite étale and splits by the same Frobenius linear algebra into field components. These refine the flag to scalar field quotients. For an equal-index quotient with $E/F$ of degree $e$, use that odd characteristic identifies $\bigwedge^2_F E$ with the negative eigenspace of the interchange map on $E\otimes_F E$. Explicitly identify
$$
E\otimes_F E\simeq\prod_{j=0}^{e-1} E,\qquad
(u\otimes v)_j=u v^{3^j}.
$$
In these coordinates the interchange acts by taking coordinate $e-j$ and applying its $3^j$-power. Multiplication by $a$ in both tensor factors acts on coordinate $j$ by $a a^{3^j}$. For a nonfixed pair $j,e-j$ the negative eigenspace is identified with one copy of $E$ by projection onto $j$. Coordinate zero contributes nothing. If $e$ is even the remaining fixed coordinate $j=e/2$ contributes the trace-zero line of $E$ over the fixed subfield $K$ of the involution $u\mapsto u^{3^{e/2}}$. Here $a a^{3^{e/2}}\in K$, so the action on this line is scalar multiplication over $K$. The line can be identified with $K$ by choosing a nonzero vector using linear algebra. This proves that all refined successive quotients of the ambient exterior-square flag are explicit fields with scalar-multiplication actions. Choices of field-coordinate bases and lifts are shared after transporting the target by $Y_0^{-1}$.

## 3. Recover determinants on arbitrary subspaces of the field quotients

Intersect $D,D''$ with each stage of that same flag and take the successive images. On a field quotient $E$, write them as $U,U'\subseteq E$. The images need not be field modules for all of $E$. If the dimensions differ, reject. Omit zero-dimensional layers. For a nonzero layer define by linear equations
$$
I(U,U')=\{a\in E:aU\subseteq U'\},\qquad K_U=\{k\in E:kU\subseteq U\}.
$$
The set $K_U$ is a finite subfield. It is a unital subalgebra of the field $E$, and every nonzero multiplier acts injectively on $U$. In finite dimension it maps $U$ onto itself and its inverse preserves $U$. If $I(U,U')$ is zero, reject. Choose any nonzero $a_0\in I(U,U')$. It maps $U$ onto $U'$ since the dimensions are equal. Then $I(U,U')=a_0K_U$ since multiplying by $a_0^{-1}$ changes the condition to preserving $U$. Consequently, for every scalar transporter $a$ on this layer,
$$
\det_F(a:U\to U')
=\det_F(a_0:U\to U')\
  N_{K_U/F}(a_0^{-1}a)^{\dim_{K_U}U}.
$$
Indeed $a_0^{-1}a$ acts by the same scalar on every coordinate of a $K_U$-basis of $U$. The determinant of $a_0$ is computed in independently chosen bases of $U,U'$. This step requires neither a small dimension of $U$ nor a shared compatible action on the rest of the tensor by the reference multiplier $a_0$.

The norm formula is a constraint on the actual transporter. Include the ambient exterior action, flag quotients, subspace intersections and inclusions in the typed system. Link the action of $V^*$ to the dual of $V$ by its evaluation pairing and that on $\bigwedge^2 V^*$ by the alternating surjection from $V^*\times V^*$. In a field grade $E$ include scalar multiplication by its explicitly based field whose entries are fixed with basis marks. Insert a new $K_U$ role through $k\mapsto k$ into the source $E$ and through $k\mapsto a_0k$ into the target $E$. Any permitted scalar map on $E$ acts on this common $K_U$ role by $a_0^{-1}a$. Use the linked Frobenius product norm construction to get its norm on an $F$-line. In detail, attach copies of $K_U$ linked from that role by the Frobenius powers. The coefficient on the $i$-th copy is $(a_0^{-1}a)^{3^i}$. Chain field multiplication maps to multiply these coefficients and then use $F\cdot1$ in the final copy. One-dimensional multiplication maps then take the specified exponent and multiply the contributions from the different grades. The same norm construction is proved in the earlier trace and norm construction in the Alpöge tensor reductions.

## 4. Calibrate and compile

Choose bases adapted to the induced flags on $D,D''$ by lifting the already chosen grade bases. Let $\beta_T,\beta_S$ be the determinants of the adapted frame matrices relative to the supplied basis of $D$ and the pulled-back supplied basis of $D''$. Let $a_{0,j}$ be the reference multiplier on a nonzero grade. The product of all linked norm lines has multiplier $\ell$, where
$$
\det\rho_Y=\frac{\beta_S}{\beta_T}\left(\prod_j \det_F(a_{0,j}:U_j\to U'_j)\right)\ell .
$$
In the branch $\epsilon$, multiply the known factor on the right by the Pfaffian formula for $\det Y$ from Section 1. Mark the output line at the appropriately calibrated scalar so that the result is the required $s$. Include the marks requiring the actual anchor multiplier to be $\epsilon$, the actual congruence condition on $D,D''$, and the equality of the ordered covariant actions after pulling back by $Y_0$. Every original witness meeting the branch and sign conditions preserves these flags and extends by the stated norm coefficients. Every marked witness projects to an actual congruence with that product sign.

All maps used are linear or bilinear. The exterior square has dimension at most $n^2$. Its flag length, the field degrees, and the total number of attached norm steps and scalar product maps are polynomial. A polynomial list of linked linear and bilinear maps becomes a constant-signature tensor system by the uniform labelled-role packing. One can use the coordinate algebra with a separately distinguished multiplicity for each primitive label, and separate occurrence roles for each tensor slot. Under the packing maps, each role copy then carries the same action as its named original role. The usual reduction of this fixed tensor-system signature gives one ordinary three-tensor comparison. Combine the two branches by the binary TI OR construction. For unmarked classes, choose one eligible source member of the covariant bank and try all target bank members that satisfy the same invariant hypotheses. Every genuine transporter carries the chosen source line to one of these target lines. The polynomial list of branch comparisons combines by the linear-growth balanced positive OR packing. [Tensor-system reduction, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4) · [Partitioned TI linear-size reduction, Theorem 5.1](https://arxiv.org/pdf/2306.16317)

This proves exact equivalence on the stated class in written mathematics. The Casimir covariance identities have prior Lean implementations. The general classification of alternating spaces by this criterion is open. Some spaces have no nonsingular member and the trace form or commutative-centralizer criterion can also fail on a nonempty bank.


## 5. Extension to centralizers with small simple ranks

The commutativity hypothesis can be replaced by a polynomially testable condition on the simple factors of the common centralizer. Let $L$ be the dense input length. Write the semisimple quotient of the common centralizer algebra as
$$
\mathcal A/\operatorname{rad}\mathcal A \simeq \prod_i M_{d_i}(E_i).
$$
If each $d_i=O(\sqrt{\log L})$ with a fixed implied constant, the same ordinary-TI reduction holds. It also holds with no bound on these $d_i$ whenever the later grade stabilizer algebras have only logarithmic simple ranks among factors whose multiplicity on their relevant grade is odd. This latter condition can be checked separately for each explicitly generated branch.

### 5.1 Exterior grades over fields

Construct a composition flag for the transpose algebra $\mathcal A^{\mathrm{op}}$ acting on $V^*$. The transpose is an algebra representation of this opposite algebra. In particular every $c^{-\mathsf T}$ preserves the flag. Compute the radical and the explicit matrix presentations of the semisimple quotient over the fixed field. These are deterministic polynomial-time operations using finite-field polynomial factorization. Over fixed characteristic three, deterministic factorization over any explicitly represented finite extension is available by the fixed-space step of Berlekamp and splitting down to prime-field values by trace. Explicitly, in a squarefree quotient the base-field Frobenius fixed algebra is the product of copies of the base field; take a basis and compose multiplication by base-field elements followed by trace to the prime field. The latter map separates any two distinct base-field values by trace nondegeneracy, and splits are then performed with gcds over the three possible trace values. The same factoring algorithm suffices for the constructive matrix-algebra decomposition. [Rónyai, Computing the Structure of Finite Algebras](https://www.sciencedirect.com/science/article/pii/S074771710880017X)

On successive radical layers, construct the simple summands using the computed matrix units. On a factor $M_d(E)$ select an $E$-basis in the image of its first diagonal matrix unit. Its images under the first-column matrix units give simple $E^d$ modules. They form a direct sum because the first-row matrix units recover their first coordinates and the diagonal units sum to identity. Lifting their flags through the radical filtration gives a composition flag in $V^*$. Each simple quotient is now $E_i^{d_i}$ and every $c^{-\mathsf T}$ acts there by an $E_i$-linear matrix.

Use the same triangular ordering of pairs as in Section 2. A cross grade $E_i^{d_i}\otimes_F E_j^{d_j}$ splits into grades of rank $d_i d_j$ over the field factors of $E_i\otimes_F E_j$. A same-layer grade $\bigwedge_F^2 E^d$ is the negative eigenspace of swap on $E^d\otimes_F E^d$. In the product coordinates of Section 2 it is a subspace of $e$ copies of $M_d(E)$. If $X_j$ is coordinate $j$, swap sends it to $(X_{e-j}^{\mathsf T})^{3^j}$, with Frobenius applied entrywise. An $E$-linear map $P$ acts on that coordinate by
$$
X_j\longmapsto P X_j (P^{3^j})^{\mathsf T}.
$$
The negative swap subspace for a nonfixed pair is identified with an arbitrary matrix over $E$, of rank $d^2$ over $E$. At coordinate zero one has the ordinary skew-symmetric space of rank $\binom d2$ over $E$. At the coordinate $e/2$ when $e$ is even, one has the skew-Hermitian space
$$
X=-\left(X^{3^{e/2}}\right)^{\mathsf T}
$$
of rank $d^2$ over the fixed field. Its off-diagonal pairs are parametrized by one entry of $E$ and each diagonal entry by a trace-zero line. The displayed action remains linear over this fixed field. Each of these spaces is invariant under every quotient action. Refining by their partial sums and taking preimages through the original flag proves that the ambient exterior-square flag has explicit grades $W=E^r$ on which all allowed actions are $E$-linear, with $r\le(\max_i d_i)^2$. All calculations can be made by linear equations over $F$, by the same field idempotent splitting and Frobenius formulas as above.

### 5.2 Orientation on a grade subspace without its full exterior algebra

As before, take successive images $U,U'\subseteq W$ of the two comparable spaces. Compute an $E$-linear isomorphism $T_0:W\to W$ carrying $U$ onto $U'$ or reject the branch if none exists. This is constructive module isomorphism with two vertex spaces $U,W$: the arrows consist of the inclusion $U\hookrightarrow W$ and the endomorphisms of $W$ that multiply by a chosen $F$-basis of $E$. Treat this as a module for the path algebra of the two vertices and those arrows. The vertex idempotents force the map to split across vertices, the arrows from the field basis enforce $E$-linearity, and the inclusion enforces the actual restriction. The finite matrices for all vertex and arrow maps give the input to Brooksbank–Luks with polynomial lengths. [Brooksbank–Luks, Theorem 3.5](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

Define the grade stabilizer algebra
$$
R_U=\{B\in\operatorname{End}_E(W):BU\subseteq U\}.
$$
It is computed by linear equations, and the allowable maps on the grade are exactly $T_0R_U^\times$. Indeed invertibility in $W$ forces an inverse in the unital matrix algebra $R_U$ by Cayley–Hamilton, and preservation of the same-dimensional space $U$ is then equality. Each actual map emitted by the full congruence still has to satisfy all earlier marks. No simultaneous compatibility of the independently chosen reference maps $T_0$ need be assumed.

Every factor $M_d(E')$ in the semisimple quotient of $R_U$ has $d\le r$. To verify the bound, extend scalars to an algebraic closure $\overline F$. The representation on $W$ is faithful and splits into $[E:F]$ invariant summands of dimension $r$, by extending the action of the field $E$. The radical extends to the radical, since the original radical is nilpotent and the semisimple quotient splits over $\overline F$. Every simple factor of the extended algebra must occur in a composition series of one of the invariant $r$-dimensional summands. Otherwise lift a nonzero idempotent from the absent factor, using lifting modulo a nilpotent ideal. It acts as zero on every composition quotient of $W$ and hence nilpotently on $W$. An idempotent acting nilpotently acts as zero, contradicting faithfulness. The simple dimensions of every split matrix factor are therefore at most $r$, as claimed.

Compute the radical powers on $U$ for $R_U$. On each grade of this radical filtration decompose under the semisimple quotient, using the matrix units as in Section 5.1. For each simple factor of multiplicity $m$ across all these layers, pick one occurrence if $m$ is odd. On that occurrence the action of $c=T_0^{-1}T$ is $E'$-linear. Its determinant, after taking the norm to $F$, raised to the multiplicity $m$, is the contribution to $\det_F(c|_U)$. This follows by multiplying determinants on the radical layers and using the restriction-of-scalars identity $\det_F M=N_{E'/F}(\det_{E'}M)$. For that identity, extend scalars to a splitting field and multiply the determinants from the conjugate matrix blocks. Even multiplicities contribute one over $F$ and require no occurrence.

Attach the radical subspaces and all relevant quotient and inclusion maps on the source, and their $T_0$-images on the target. Every actual $c$ preserves each chosen simple occurrence because it is an $R_U$-submodule of a layer. Mark its center $E'$ action alone. On the target identify this action by transport along $T_0$. The actual restriction is now an $E'$-linear map on a space of dimension $d$. Its exterior algebra over $E'$ gives the top determinant line with $F$-dimension $[E':F]2^d$ for the full attachment. The linked Frobenius norm maps then read its contribution. In particular the width bound applies to the rank $d$ of the simple factor measured over its own center, even when the underlying $F$-dimension of $U$ is very large. Each grade is calibrated by $\det_F(T_0:U\to U')$ in the two chosen grade bases. Multiply all contributions with the frame ratio and the known Pfaffian multiplier as in Section 4.

Thus the source and target each use polynomially many field-algebra and module calculations and markings. The only possible exterior growth comes from simple occurrences contributing their determinants, with $d\le r\le(\max_i d_i)^2$. Taking $d=O(\log L)$ on those occurrences gives polynomial dense size. If $\max_i d_i=O(\sqrt{\log L})$ this follows uniformly. Every marked isomorphism obeys the exact original congruence and desired determinant product, and each original witness in a retained branch induces all the marks. The extension keeps the same two scalar anchor branches and admits the same covariant anchor-bank application. The claims in this section are written mathematics.
