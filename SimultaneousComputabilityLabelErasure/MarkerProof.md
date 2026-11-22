# Linear-size block erasure with constant-degree polynomial calculus

## 1. Path rigidity in a split diagonal quotient

Let $F$ be any field. All PC derivations below use scalar linear combinations and multiplication by individual variables. A polynomial equality abbreviates the line given by its difference. Multiplication by a polynomial of bounded degree is implemented by multiplying successively by the variables in each monomial and taking linear combinations.

**Lemma 1 (ordered path).** Let $\Gamma,\Gamma'$ be directed supports on vertices $1,\dots,h$. Every edge in either support points from a smaller index to a larger one, and $\Gamma$ contains every edge $i\to i+1$. Suppose polynomial coordinates $P_{ai}$ satisfy row and column sums one, row and column collision identities, and
$$
 P_{ai}P_{bj}=0\qquad\text{whenever } i\to j\text{ in }\Gamma,\quad
 a\not\to b\text{ in }\Gamma'.
$$
Then $P_{ai}=\delta_{ai}$ has a PC derivation using these identities with a constant number of additional factors per line, independent of $h$. When the $P_{ai}$ themselves are variables and the displayed identities are axioms, degree two suffices.

**Proof.** Induct on the column $i$ to derive $P_{ai}=0$ for $a<i$. The first column requires no proof. In the induction step, for $b\le i$, the column sum gives
$$
 P_{b,i+1}=\sum_a P_{ai}P_{b,i+1}.
$$
Every term with $a<i$ vanishes by induction, and every term with $a\ge i$ vanishes by the missing edge identity for $i\to i+1$, since $a\ge b$. The new facts are linear in $P$, so the next step uses the same degree. Now row $1$ gives $P_{11}=1$, and column collisions give $P_{a1}=0$ for $a\neq1$. Inducting on the rows gives all the remaining columns in the same way. There are polynomially many lines, and all coefficient sums are expanded by binary additions. $\square$

The hypothesis of this lemma can be obtained from ordinary algebra isomorphism equations without comparing ranks in the coefficient field. Suppose two finite free unital algebras $A,A'$ have designated ideals $J,J'$ that are spanned by commutators, with $J^3=(J')^3=0$ and diagonal quotients $A/J=(F)^h=A'/J'$. Assume specified coordinate bases of the quotients by the ideals and of $J/J^2,(J')/(J')^2$, with each ideal square spanned by explicit products of ideal basis elements. Label the diagonal primitive idempotents $e_i,e'_a$, and equip $J/J^2$ and its counterpart with their Peirce supports, where an edge means its $(i,j)$ corner is nonzero.

Let $K,L$ be the algebra witness and its supplied inverse. The inverse is multiplicative by applying $L$ to the multiplication equation for $K$ at $Lx,Ly$. The maps preserve the unit by using the multiplication equation and substituting the inverse's value at the unit. Commutator representations of the strict basis and product representations of its square show that both maps preserve the indicated subspaces with bounded-degree entrywise proofs. In particular, the induced forward and reverse maps on each quotient have both inverse equations. Write $P,Q$ for their matrices on the diagonal quotients. Multiplicativity gives idempotence and row collisions for both $P,Q$, and the unit identities give their row sums. Multiply the $(a,b)$ entry of $PQ=I$ by $P_{ai}$ and use row collisions and idempotence to derive
$$
 P_{ai}Q_{ib}=\delta_{ab}P_{ai}.
$$
Likewise multiplying the $(i,j)$ entry of $QP=I$ by $Q_{ib}$ gives $Q_{ib}P_{bj}=\delta_{ij}Q_{ib}$. Taking $b=a,j=i$ gives $P_{ai}=Q_{ia}$, hence column sums and collisions for $P$.

For the missing-edge identity pick a basis vector $x$ of the source corner $(i,j)$ in $J/J^2$. Its image $\overline K(x)$ satisfies the coordinate relations from $x=e_i x e_j$. In target corner $(c,d)$ these give
$$
 \overline K(x)_{cd}=P_{ci}P_{dj}\overline K(x)_{cd}.
$$
Multiplying by $P_{ai}P_{bj}$ makes every coordinate other than $(a,b)$ vanish by column collisions. If $(a,b)$ is absent, the entire weighted image is zero. Apply the quotient inverse and take the $x$-coordinate to derive $P_{ai}P_{bj}=0$. Each step uses a bounded number of matrix factors and constant-coordinate maps. Thus Lemma 1 gives $P=Q=I$ at an absolute PC degree cutoff whenever the stated path and order occur. All computations also hold over commutative rings when the indicated decompositions have the same coordinate descriptions.

## 2. A linear ordinary-tensor compiler for arbitrary numbers of blocks

A block-preserving isomorphism of bilinear maps $B:X\times Y\to Z$ and $B':X'\times Y'\to Z'$ is given by invertible maps in all three roles, with common specified block formats in each role. Its PC equations give transport on every basis pair, and both inverse equations in every named block. The inverse maps are explicit witnesses. Dropping zero-rank summands does not change the equations. Let $N=\dim X+\dim Y+\dim Z$.

**Theorem 2 (uniform block erasure).** Over every field there is an explicit compiler from this problem to ordinary three-tensor isomorphism with side $O(N+1)$, independent of the number of named blocks. An absolute constant $C$ has the following properties.

- A PC refutation of the ordinary instance of degree $D$ and sparse size $S$ yields a source refutation of degree at most $\max(D,C)$ and sparse size at most $S+(N+1)^{O(1)}$.
- A degree-$D$ source refutation yields an ordinary refutation of degree at most $\max(CD,C)$. At any fixed degree cutoff the sparse cost is polynomial in $S+N+1$.

Both statements hold with field equations over the same finite field. The semantic construction and its witness maps work over arbitrary commutative unital rings with the stated free-block format.

**Proof.** First make a bilinear map $M$ with only the first two modes labelled and with products spanning the output by specified basis products. Set
$$
 \widetilde X=X\oplus \bigoplus_l Z_l^{(L)}\oplus F x_0,\qquad
 \widetilde Y=Y\oplus F y_0,\qquad
 \widetilde Z=Z\oplus F z_0,
$$
where $Z_l^{(L)}$ is a separate copy of every output block. Preserve each displayed left and right block, including both scalar blocks. In addition to the data product $XY\to Z$, use $x_0 y_0=z_0$ and $z^{(L)}y_0=z$ for $z\in Z$, and declare all other products zero. For a block-preserving isotopy on $M$, evaluation on $Z_l^{(L)}\times y_0$ forces the output map to preserve $Z_l$ and be the left map on its copy times the right scalar. The same equation with the inverse maps gives preservation and inverse identities in each output block. Evaluation on $x_0,y_0$ forces preservation of $Fz_0$; restriction to $X\times Y$ gives the original data equations. The reverse lift places the output map on each left output copy, fixes the new scalar blocks, and uses the original maps on the remaining blocks. These lifts on individual entries are original coordinates or constants. The readout uses output block entries and bounded-degree inverse and transport identities.

Use the triangular unital associative algebra with core vertices $0,1,2$ and strict corners
$$
 e_0Ae_1=\widetilde X,\quad e_1Ae_2=\widetilde Y,\quad
 e_0Ae_2=\widetilde Z.
$$
The first two compose by $M$. For each left block $U_i$ add a vertex $s_i$, a scalar arrow $1\to s_i$, and a corner $0\to s_i$ that is a copy of $U_i$. Compose $\widetilde X$ with this scalar arrow by the projection onto $U_i$. For each right block $V_j$ add a vertex $t_j$, a scalar arrow $t_j\to1$, and a corner $t_j\to2$ that is a copy of $V_j$, with the analogous projection. All diagonal corners are copies of $F$, acting on incident corners by scalars.

Order the old vertices as $0,t_1,\dots,t_\ell,1,s_1,\dots,s_k,2$. Between any consecutive old vertices $a,b$ insert a single intermediate vertex $u$ and one scalar arrow on each of $a\to u$ and $u\to b$. Set every product of two strict elements involving an inserted arrow to zero. All strict products other than the core and projection compositions are also zero. The images of the specified strict products annihilate all strict corners on either side, so the multiplication is associative. Every strict basis element is a commutator $[e_i,x]$, and the diagonal quotient is commutative. The strict ideal $J$ therefore equals the commutator span. Its square is exactly the direct sum of the three types of output corner, $\widetilde Z$ and the two sets of projection outputs; this follows from the prescribed basis products. All arrows point forward in the extended order, and the full directed path survives in $J/J^2$. These properties are unchanged across all field or ring probes.

An algebra isomorphism now has $K(e_a)\equiv e'_a\bmod J'$ by Lemma 1 and its quotient derivation. Write $u=\sum_a K(e_a)e'_a=1+j$, $j\in J'$. The polynomial $1-j+j^2$ is its inverse by $(J')^3=0$. Orthogonality and idempotence give $K(e_a)u=ue'_a$. The map $x\mapsto u^{-1}K(x)u$ and its inverse consequently preserve every actual corner. Its action on each scalar projection arrow is a scalar with the inverse obtained from the inverse witness. For $x\in U_i$, multiplication by the scalar arrow for any $U_{i'}$ with $i'\neq i$ is zero. Transport this equation and cancel the witnessed scalar to derive vanishing of the $U_{i'}$-component of the corner map on $x$. The same proof for the inverse and for the right-side projections recovers two-sided invertible maps on all prescribed blocks. The transport on the core product is exactly the equation of $M$. In the reverse direction a block-preserving isotopy on $M$ extends on the projection output corners by the corresponding block maps and fixes the diagonal idempotents and scalar arrows. Its entries and inverse entries are each a coordinate or constant. The sum of all corner dimensions, vertices and new arrows is $O(N+1)$, since the nonempty block count is at most the dimension sum after the first padding.

Finally take the ordinary multiplication tensor of the resulting algebra. Its transport equation in isotopy convention is $H(xy)=F(x)G(y)$, with all three maps invertible. In the covariant three-tensor convention, this is obtained by substituting the two supplied inverse input maps into the action equation, or by relabelling the inverse transpose variables and using the inverse equations. This has bounded degree cost. For an isotopy put
$$
 a=F(1),\quad b=G(1),\quad c=G(H^{-1}(1)),\quad d=F(H^{-1}(1)).
$$
The identities $H=L_aG=R_bF$ show that $GH^{-1}$ and $FH^{-1}$ are inverse matrices to left multiplication $L_a$ and right multiplication $R_b$, respectively. Hence $ac=db=1$. Apply those inverses to $a(ca-1)=0$ and $(bd-1)b=0$ to obtain $ca=bd=1$. Substitution gives
$$
 H(xy)=H(x)dcH(y),\qquad K(x)=dcH(x),\qquad K^{-1}(y)=H^{-1}(ab\,y).
$$
These maps are multiplicative, inverse and unital by the displayed identities. An algebra isomorphism lifts to an isotopy by repeating its matrices. Thus the entire lift from source witnesses to ordinary tensor witnesses uses just entry identifications, zeros and ones. Its image axioms have bounded-degree derivations, so a target refutation replays at degree at most $\max(D,C)$, with a one-time polynomial cost and without increasing the support of each substituted line. Reusing a surviving line when an image is zero or a scalar prevents an extra sparse cost. The opposite readout gives polynomial substitutions of bounded degree, so each source multiplication can be expanded into single-variable multiplications at degree at most $\max(CD,C)$. All derivations invoke only bounded-length products and polynomially many constant-coefficient sums. Lemma 1 can run for many columns, but all its newly derived equations are linear in the entries of the same quotient map. This keeps the uniform degree bound and polynomial fixed-degree size.

For field equations in the coordinate lift, each image is a field axiom or zero. For a polynomial readout $f$ of degree $c$, Frobenius reduces $f^q-f$ to a sum of monomial differences. A monomial difference telescopes against the original variable field equations in degree $cq$. This cost is needed only if a source proof uses a field axiom, in which case $D\ge q$. No division by a dimension appears in the construction or witness identities. $\square$

Earlier semantic reductions include the original rank-weight augmentation and linear-length tensor gadgets. Earlier proof transfers gave all-field PC simulations with a fixed number of labels, or for the exact original rank-weight augmentation with characteristic restrictions. The new uniformity is the absolute proof-degree bound as the number of blocks grows, with linear side overhead and both directions of simulation. The compiler is a different explicit output from the original FGS tensor. [Futorny–Grochow–Sergeichuk, Lemma 2.2](https://arxiv.org/abs/1810.09219) · [Grochow–Qiao, Part IV](https://arxiv.org/abs/2306.16317) · [Earlier fixed-type proof transfer](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/IntrinsicIsomorphismCrossovers/proof-transfer.md) · [Earlier original-gadget obstruction](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/GrochowEightFollowup/fgs-obstruction.md)

## 3. Labelled conjugacy inside ordinary tensor isomorphism

**Corollary 3.** For two ordered lists of $m$ endomorphisms of an $n$-space, the simultaneous conjugacy systems $PL_i=L'_iP,\ PQ=QP=I$ admit the same two PC simulations into ordinary tensor isomorphism of side $O(n+m+1)$. The degree and size constants are independent of the list length.

**Proof.** Use left blocks $V,Fx_0$, right scalar blocks $Fy_0,\dots,Fy_m$, and output $V\oplus Fz_0$. The only nonzero prescribed products are
$$
 vy_0=v,\qquad vy_i=L_i v\ (1\le i\le m),\qquad
 x_0y_i=z_0\ (0\le i\le m).
$$
All products still span the output by fixed basis products. The equations from $x_0y_i$ give $\alpha\beta_i=\gamma$ for $\alpha$ the left scalar, $\beta_i$ the right scalar, and $\gamma$ the output scalar. Cancel the supplied inverse to obtain $\beta_i=\beta_0$. The $vy_0$ equation gives the output map $\beta_0P$ on $V$. The $vy_i$ equations give $PL_i=L'_iP$ after cancelling $\beta_0$. This gives the readout; conversely use $P$ on both $V$'s and fix all scalar coordinates. Apply Theorem 2 (or start directly with its unlabelled-output step). $\square$

## 4. Characteristic-dependent amplification in ordinary tensors

For an integer $M\ge 32$, pick $g=1$ for odd $M$ and $g=2$ for even $M$. Put $r=(M-g)/2,\ s=(M+g)/2,\ \Delta=gM$. The following tensor family has a joint resource profile across all fields with a single integer input pair. Define
$$
 b(F)=
 \begin{cases}
 1,&\operatorname{char}F=0,\\
 p^{v_p(\Delta)},&\operatorname{char}F=p>0.
 \end{cases}
$$

**Theorem 4.** There are pairs of ordinary $0,1$ multiplication tensors of common side $N=\Theta(M^2)$, with coefficient equations generated in polynomial time, for which over every field the raw PC degree is $\Theta(b(F))$ and the minimum sparse size is $N^{\Theta(b(F))}$. The estimates hold also with the field equations at every finite field probe. At primes not dividing $\Delta$, the degree is bounded independently of $M$. Before compiling, the two constituent one-label conjugacy comparisons each have raw degree at most $4$ over every field. The labelled tensor product comparison has exact raw degree $2b(F)$.

**Proof.** The constituent comparison is $A=\operatorname{diag}(I_r,0_s)$ versus $B=\operatorname{diag}(I_s,0_r)$. The ordered tensor product comparisons are
$$
 (A\otimes I_M,\ I_M\otimes A)\qquad\text{and}\qquad
 (B\otimes I_M,\ I_M\otimes B).
$$
Their four joint eigenspaces for the words $11,10,01,00$ have dimensions $r^2,rs,rs,s^2$ and $s^2,rs,rs,r^2$, respectively. In the labelled equations every off-word entry of $P$ vanishes by a linear input equation. The matching corners of $PQ=QP=I$ therefore give the independent two-sided rectangular inverse systems in degree two by discarding monomials containing an off-word entry of $P$. Conversely, setting all off-word entries of $P,Q$ to zero specializes the labelled instance to disjoint rectangular systems. Their joint refutation degree is the minimum of the individual degrees. For the lower direction, at cutoff $D$, choose in each local polynomial space a basis adapted to degree and to the local degree-$D$ consequence space. The span of tensor basis products with a local consequence factor contains the input axioms. Its intersection with terms of total degree at most $D-1$ is spanned by just those products within this lower cutoff. Multiplication by one variable preserves a consequence factor, so the span contains every proof line of degree at most $D$. It excludes $1$ if each local consequence space excludes $1$. The upper direction uses a refutation in the cheapest local block. Matching blocks are satisfiable. For unequal positive sizes $a<c$, the prior exact raw rectangular degree is $2$ in characteristic zero and $\min(a+2,2p^{v_p(c-a)})$ in characteristic $p$. The constituent gap $g$ is at most $2$. The unmatched word gap is $s^2-r^2=\Delta$, and $r^2+2\ge 2\Delta$ for $M\ge32$. This proves the exact labelled degree. [Exact rectangular inverse degree](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/ExactMatrixProofDegrees/ConjugacyDegree.md)

For the sparse lower bound specialize the two matched words to the identity. The remaining two labels coincide and form a complementary projection pair with smaller multiplicity $R=r^2$ and gap $\Delta=O(\sqrt R)$. Under the matching substitution for the two mismatched blocks, use the same rectangular board and its transpose. Off-diagonal products vanish under Boolean matching normalization and diagonal inverse equations map to row or column totalities. Field equations map either identically to zero or to zero in that Boolean normal form, since the substituted entries are constants or Boolean variables.

Here is the growing-gap argument for these parameters. In the prior matching proof, retain independently uniform live sets of $u=2b(F)$ rows and $v=2b(F)+\Delta$ columns, and match the nonlive complements by a uniform bijection pinned to one. All other nonlive edges are zero. Inside the live board, normalized matching degree below $b(F)$ cannot refute the totalities. Indeed Riis's normalized designs have order $b(F)-1$ there and extend as required on the board with one row and column removed, since its smaller side is $2b(F)-1$ and its gap is still $\Delta$. Pairing with designs proves closure under low-degree normalized products by forcing the next multiplied edge and extending the restricted design. When $b(F)=1$, an order-zero calculation cannot use a nonzero totality. Consequently every restricted refutation has some original monomial occurrence surviving with at least $b(F)$ live edges before its line's normalization and cancellation. [Riis, Section 14](https://arxiv.org/html/2611.07280v1#S14) · [Earlier sparse matrix-conjugacy proof](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/SparseMatrixProofBounds/SparseConjugacy.md)

Write $b=b(F)$. A monomial with collisions cannot survive, and powers reduce to a single occurrence. For a support of fewer than $2b$ distinct compatible edges, specify $b$ live edges in at most $4^b$ ways. Their endpoint-inclusion probability is at most $(u/R)^b(v/(R+\Delta))^b$, giving $R^{-\Omega(b)}$ because $b\le\Delta=O(\sqrt R)$. For a larger support fix $2b$ of its distinct edges. Each fixed edge needs its row to be live or its precise nonlive match to be pinned. For a set of $j$ live rows the probability is at most $(u/R)^j/(R-u)_{2b-j}$, where the falling factorial comes from the pinned bijection, and impossible configurations contribute zero. Summing over the at most $2^{2b}$ assignments gives $R^{-\Omega(b)}$ uniformly for $R$ sufficiently large. A union bound over the monomial occurrences proves size $R^{\Omega(b)}$ for the labelled comparison, with or without field equations. The same argument applies in characteristic zero with $b=1$.

Apply Corollary 3. The coordinate lift transfers sparse lower bounds with only a fixed polynomial preprocessing term. For all sufficiently large $b$, subtracting that term preserves the $N^{\Omega(b)}$ lower bound. For bounded $b$, an ordinary refutation must use an original inverse axiom because the all-zero assignment satisfies every action and field equation. Each inverse axiom has at least $N$ monomials, giving the claimed bound also in this range. A degree-$d$ PC refutation in $t=O(N^2)$ variables can be reproduced using a basis of its degree-$d$ consequence span, recovering omitted parents by linear combinations. This has sparse size polynomial in $\binom{t+d}{d}$. Thus the sparse lower bound implies degree $\Omega(b)$ also at finite field probes. The raw degree-$2b$ labelled proof compiles to degree $O(b)$; this proof remains valid after adding field equations. The dimension estimate then gives size $N^{O(b)}$. $\square$

In particular, for odd $M=p^h$ this produces ordinary tensors of side $\Theta(M^2)$ with degree $\Theta(M)$ and size $N^{\Theta(M)}$ in characteristic $p$, and bounded degree in every other characteristic. For $M=2^h$ the same selective phenomenon holds in characteristic two. Choosing composite $M$ gives simultaneous peaks at its prime-power divisors. The original labelled amplifier only required two labels. The compiler also handles an arbitrary number of them, and the resulting tensors have no partitions in their isomorphism equations.

## Verification scope

These are written proofs. An exact symbolic check verified 5,479 linear outputs of the quadratic path derivation on vertex counts through 64, using the complete forward target support. No Lean formalization is claimed. The size statement uses expanded sparse PC and the indicated ordinary action and two-sided inverse equations. The exact degree formula is for the labelled source; the ordinary output has the stated two-sided order estimate. The compiler proves the positive arbitrary-block replacement statement, with a different ordinary output from the FGS rank-marker construction. The original proof-complexity questions and the exact reductions they refer to are stated by Galesi, Grochow, Pitassi and She. [Section 7](https://arxiv.org/html/2305.19320#S7)
