# Coordinate label recovery for triangular algebras

This note proves two quantitative statements about the label-erasure step. Consecutive arrows in a directed order force the label permutation by constant-degree ordinary Polynomial Calculus (PC), and the same constraints give polynomial-size, constant-depth Nullstellensatz coefficient formulas. For graded triangular algebras, the recovered labelled witness coordinates are literally coordinates of the two unlabelled algebra witnesses. In that step an arbitrary sparse proof can be reused with only a polynomial preparation cost.

Use ordinary PC over a field $F$: linear combinations and multiplication by a variable, with expanded monomial count as size. An algebra transporter has maps $X,Y$, both inverse axioms, both unit axioms, and multiplication preservation for $X$ and $Y$. Writing multiplication just in the forward direction changes the preparation by a constant-degree derivation: substitute $Yu,Yv$ in the forward defect and correct $XY=YX=I$. The same argument recovers the reverse unit axiom.

## 1. Ordered labels from consecutive constraints

**Theorem 1.** Let $P=(p_{ai})_{1\le a,i\le n}$ satisfy the following written polynomial equations: row and column sums equal one, idempotence of each entry, pairwise collisions equal zero along any row or column, and
$$
 p_{ai}p_{b,i+1}=0
 \qquad (1\le i<n,\ a\ge b).
$$
There are degree-two ordinary PC derivations of $p_{ai}=\delta_{ai}$ over every field. The same conclusion holds over every commutative ring for solutions. For each conclusion there is also a Nullstellensatz-style ideal identity whose coefficient polynomials have polynomial-size constant-depth formulas with unbounded fan-in addition and multiplication over the integers. Both statements are uniform in $n$.

*Proof.* Put $U_i=\sum_{a<i}p_{ai}$ and $L_i=\sum_{a>i}p_{ai}$, with $U_1=L_n=0$. Let $C_i=\sum_a p_{ai}-1$. Summing forbidden products and using column sums gives, for every applicable index,
$$
\begin{aligned}
 U_i-U_iU_{i-1}
   &=\sum_{a<i}\sum_{b\ge i-1}p_{b,i-1}p_{ai}-U_i C_{i-1},\\
 L_i-L_iL_{i+1}
   &=\sum_{a>i}\sum_{b\le i+1}p_{ai}p_{b,i+1}-L_i C_{i+1}.
\end{aligned}
$$
In the first double sum $b\ge i-1\ge a$, and in the second $a\ge i+1\ge b$. The equations on both right sides are therefore written axioms or their linear multiples. Induct forwards for $U_i=0$, and backwards for $L_i=0$, multiplying the previous linear line by the current linear sum. Each step is legal at degree two irrespective of $i$. The [Lean companion](ChainResidual.lean) verifies the underlying ideal implication.

For $a<i$, multiply $U_i$ by $p_{ai}$. Idempotence and the written same-column collision equations reduce this to $p_{ai}=0$; use $L_i$ for $a>i$. The column sum gives the diagonal. These derivations use at most polynomially many monomials in total.

For the formulas, denote the first residual by $R_i=U_i-U_iU_{i-1}$. The direct identity
$$
 U_i=\sum_{j=2}^i \left(\prod_{k=j+1}^i U_k\right)R_j
$$
is a telescoping sum, including the terminal $U_1=0$. The backward formula for $L_i$ is obtained by reversing order. Each residual is already a linear combination of written axioms with degree-at-most-one coefficients. Multiplying a displayed formula by one entry and using collision axioms gives the identities for individual entries. Every coefficient has a formula using a bounded number of alternating sum and product layers, and at most polynomially many leaves, since each displayed product has at most $n$ factors and each factor is a sum of at most $n$ entries. The identities have integer coefficients and hence specialize in every characteristic. $\square$

The two proof representations carry different information. The PC derivations reuse consecutive linear consequences to stay at degree two. The coefficient formulas use longer products to obtain bounded depth directly. Substituting polynomial entries of bounded degree into the latter adds the depth of those entries, and substituting any explicit coefficient formulas for the written generators adds their depth. One can therefore compose this label certificate in the constant-depth Hilbert-like IPS model whenever the local algebra computations have constant-depth coefficient formulas. [Grochow–Pitassi, the Ideal Proof System](https://arxiv.org/abs/1404.3820).

## 2. Recovering the ordered-label equations from multiplication

A triangular algebra here has a fixed vector-space decomposition
$$
 A=F^n\oplus N,\qquad N=\bigoplus_{i<j} e_i N e_j,
$$
where the $e_i$ are a complete set of orthogonal diagonal idempotents and $N$ is a two-sided ideal. It is nilpotent. Let $B$ have the same number of diagonal vertices. Suppose $N_A/N_A^2$ has a nonzero consecutive corner $(i,i+1)$ for every $i$. Other corners are unrestricted subject to triangularity. Use fixed bases of $N,N^2$ and a chosen complement. The existence of these decompositions is a hypothesis on the supplied algebra format, with all spaces computed on the input coefficients.

**Theorem 2.** The literal algebra-isomorphism equations for $A,B$ imply, by constant-degree PC with polynomially many expanded monomials, that the map on $A/N_A\to B/N_B$ is the identity on the ordered vertices. The degree is independent of dimensions, the number of vertices, and the characteristic. The same conclusion holds for the inverse. The local derivations of the ordered-label constraints admit constant-depth polynomial-size coefficient formulas in the algebra axioms. Thus the vertex-fixing equations also have polynomial-size constant-depth coefficient formulas in those axioms.

*Proof.* The linear span of commutators is exactly $N$: the quotient is commutative, and every $u\in e_i N e_j$ with $i<j$ equals $[e_i,u]$. Applying $X$ to this last identity and using two multiplication equations proves that $Xu$ has no diagonal coordinates. The same holds for $Y$. Applying $X$ to an explicit expression for a basis of $N^2$ as linear combinations of products in $N$ then proves that $X(N^2)$ has no component outside $N^2$, using the just-derived vanishing coordinates in the product. Use $Y$ likewise. Quotient maps on $F^n$ and $N/N^2$ now have witnessed inverses by block multiplication and projection. These are constant-degree operations. They can equally be written as polynomial-ideal identities by expanding each product difference into its factors, with polynomially many terms and a fixed number of product factors. A basis of $N^2$ can be selected among products of input basis elements, so no expression requires more than polynomial length.

Let $P,Q$ be the quotient matrices of $X,Y$ on the diagonal. The image of each idempotent and the pairwise zero products give idempotence and row collisions for both $P,Q$, and the two unit axioms give row sums. To see that $q_{ia}=p_{ai}$, multiply the $(a,a)$ entry of $PQ=I$ by $p_{ai}$ and use the row collisions and idempotence. This gives $p_{ai}q_{ia}=p_{ai}$. The $(i,i)$ entry of $QP=I$ times $q_{ia}$ gives the same product equal to $q_{ia}$. Consequently $P$ has column sums and column collisions as well. The substitutions here use degrees at most three in quotient entries.

For an input consecutive corner pick a basis vector $u$ of $(e_iN_Ae_{i+1}+N_A^2)/N_A^2$, and write $W$ for its image in $N_B/N_B^2$. The two equations $e_i u=u=u e_{i+1}$ give, in target corner $(c,d)$,
$$
 W_{cd}=p_{ci}W_{cd}=p_{d,i+1}W_{cd}.
$$
Put $z=p_{ai}p_{b,i+1}$ for $a\ge b$. Multiplying these equalities by $z$ and using column collisions shows $zW_{cd}=0$ unless $c=a,d=b$. That corner is zero by triangularity. Now multiply by the witnessed inverse on $N/N^2$ to get $zu=0$, and take the chosen basis coordinate to get $z=0$. Every step uses only a bounded number of polynomial factors, and the longest dependency chain through the quotient and corner operations has fixed length. This establishes the written axioms of Theorem 1 with the claimed local degree, size, and formula bounds. Apply that theorem. $\square$

The essential condition is a nonzero link between every pair of consecutive labels in the quotient $N/N^2$. Support is tested with a single chosen vector, so this step incurs no degree cost proportional to a block rank.

## 3. Sparse simulation for the graded algebra step

Assume now that both algebras are positively graded triangular algebras of a fixed grading length $h$, with
$$
 A=\bigoplus_{t=0}^h A_t,\qquad A_0=F^n,\qquad N_A^i=\bigoplus_{t\ge i} A_t
$$
and equally for $B$. The grade spaces are given in the input bases and each is partitioned into its diagonal-idempotent corners. Take the labelled algebra equations to be multiplication and inverse equations on the block-diagonal transporter respecting grades and corners, with the diagonal units fixed. Assume the two labelled formats have the same slot dimensions. The statement below still applies when the old data are empty or a corner rank is zero. There is no stage that enumerates label permutations.

**Theorem 3.** If $N_A/N_A^2$ meets the consecutive condition of Theorem 2, the labelled and unlabelled algebra-isomorphism presentations admit two-way PC simulations with bounded additive preparation degree, where the bound depends only on $h$. For every sparse proof, its translated size is at most the original size plus a polynomial in the input presentation size, with exponent depending only on $h$. These claims also hold with coordinate field equations, when the field-equation preparation is counted in the literal input size. In field equations written $z^q-z$, a recovered coordinate is the same original variable or a constant. Consequently the degree cost of the additional axioms is at most their own degree.

*Proof.* First obtain filtrations $X(N_A^i)\subseteq N_B^i$ and $Y(N_B^i)\subseteq N_A^i$ by induction, using $N^i=N\cdot N^{i-1}$ and the multiplication equations. Each of the boundedly many steps proves a linear constraint from products with at most a bounded number of variables. On graded quotients the induced matrices consist of the corresponding diagonal-grade blocks of the original coordinate matrices. Their inverse identities follow by projecting the original inverse products and discarding off-filter components using the linear constraints. This amounts to multiplying the linear constraints by one coordinate at a time. Multiplicativity on graded quotients follows by projecting each written product to its total grade; higher output components disappear in that projection. These are again only bounded-degree preparations.

By Theorem 2 the grade-zero coordinates agree with the prescribed units. For an element $u$ of grade $t$ in a specified corner $(i,j)$, the equations $e_i u=u=u e_j$ now show that its grade-$t$ image belongs to the same corner, since all other corner projections are zero. All omitted components of the grade-diagonal matrices are therefore derived zero lines. The remaining block coordinates give the labelled algebra witness and its inverse. In the grading stated in the hypotheses, projection to the associated graded recovers exactly the original labelled multiplication constants. Thus each substituted labelled axiom has a derivation by the bounded-degree preparation. For graded coordinates corresponding to absent components or to prescribed 0 and 1 entries use constants.

The crucial size point is that each variable in the labelled polynomial ring goes to a single original coordinate or a constant, even after all the preparations. Hence a proof line cannot gain monomials under this substitution. A multiplication by a constant or a zero image can be omitted or absorbed into the following linear combination. After deriving the substituted input axioms once, every remaining line is transferred with its original bound. The new size is thus the original size plus the preparation size. Conversely substitute the blockwise diagonal matrices into the unlabelled equations. Extra terms vanish identically, the surviving identities are labelled equations, and the same sparse bound applies. Coordinate field equations specialize to field equations or zero, so the additional statements follow. $\square$

Here is one way to use the hypothesis when the input carries a public topological order but no consecutive arrows. Add one new intermediate vertex between each consecutive pair of old vertices and two one-dimensional arrows through that vertex. Give each new arrow degree one. All products involving one new arrow and another positive-grade element are zero, and the diagonal idempotents act by endpoints. This is associative because both ways of composing two strict arrows with a new arrow are zero, and all remaining products are the old ones. No added corner belongs to the square. The old graded-power equalities for grades at least two remain true. The resulting support is triangular, and its consecutive arrows meet the hypothesis. There are $O(n)$ new dimensions. Once labels are recovered, deleting the added vertices and arrows gives the old labelled comparison by coordinate projection. Every old labelled witness extends by the identity on new arrows. The construction is field-uniform. This proves a sufficient label-erasure statement for graded triangular input algebras and an exact sparse simulation of that layer. The jump from algebra-isomorphism variables to fully independent multiplication-tensor variables is a separate layer and may increase the number of monomials.

## 4. Composing proof bounds through the tensor layer

Suppose an input polynomial system is translated using polynomial entries of degree at most $b$, each having at most $M$ monomials, and every substituted axiom has a preliminary PC derivation through degree $D_0$, with total expanded size $S_0$. For a proof of degree $D$ and size $S$, replay under the substitution. A line of degree $d$ with $s$ terms has at most $sM^d$ terms in its image. A variable multiplication is replayed by multiplying the parent image separately by the monomials of the substituted variable, then taking linear combinations. Intermediate degree is at most $bD$, because a source multiplication through degree $D$ starts with a parent of degree at most $D-1$. At most polynomially many extra monomials in $S,M,b$, times $M^D$, are needed for the replay, including the intermediate partial sums. This gives the rigorous bound $\max(D_0,bD)$ and polynomial expanded size for fixed $D$. Theorem 3 is stronger at its own layer since $M=1$ there.

For circuits the dependence on $D$ is absent. Annotate each preparation line by a linear combination of the target axioms with circuit coefficients. Addition and multiplication by a variable update that vector componentwise. Sharing the vector circuits across lines gives polynomial total gate count in the preparation and number of target axioms. Substitute these axiom combinations and the entry circuits into a source Hilbert-like IPS certificate. The resulting identity is again linear in the target placeholders and has polynomial circuit size. Thus an existing polynomial-size circuit refutation can be transferred through all these layers even if the expanded PC bound grows. This argument works over every characteristic, and over finite fields the images of field equations are represented using the $q$-power identities with repeated squaring. This composition makes the resource guarantees explicit for the ordinary tensor compilers in the companion notes. [Grochow–Pitassi, IPS](https://arxiv.org/abs/1404.3820).

**Corollary 4.** For each fixed prime $p$, the ordinary $0,1$ tensors in [MarkerProof.md](MarkerProof.md), Theorem 4, with $M$ a power of $p$, have polynomial-size Hilbert-like IPS refutations and minimum expanded PC size $N^{\Theta(\sqrt N)}$ in characteristic $p$, where $N$ is their common side length.

*Proof.* The source is a labelled comparison of two diagonal operators. Take one mismatched joint eigenspace. Its rectangular inverse equations follow by constant-degree PC as in the marker proof. If $U$ is $r$-by-$s$ and $V$ is $s$-by-$r$ with $r>s$, then $\det(UV)=0$ identically. Replace the rows of $UV$ by the rows of $I_r$ one by one. Each determinant change is a linear combination of the entries of the corresponding row defect, with cofactors as coefficients. Division-free determinant circuits of size polynomial in $r$ therefore give a polynomial-size Hilbert-like IPS refutation of the rectangular system in every characteristic. Compose this refutation through the constant-degree prepared equations and the bounded-degree compiler readout using the circuit argument above. The stated PC size follows from Theorem 4 since its $b$ is proportional to $M$ and $N=\Theta(M^2)$. The same circuit refutation remains valid after adding field equations. [Berkowitz, division-free determinant circuits](https://doi.org/10.1016/0020-0190(84)90018-8).
$\square$

These are written proofs with a kernel-checked ideal lemma in the first section. The constant-depth claim is an axiom-identity statement for the ordered labels. It asserts a constant-depth transfer for a further layer only when the coefficient formulas for that layer have the stipulated depth. The unrestricted sparse-size theorem above applies to the graded algebra layer. Rank-marker failure for the original ordinary tensor compiler is a separate phenomenon. [Original FGS gadget](https://arxiv.org/abs/1810.09219) · [Prior positive-characteristic failure](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/GrochowEightFollowup/fgs-obstruction.md).
