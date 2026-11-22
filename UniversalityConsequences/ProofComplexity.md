# The linear tensor compiler preserves ordinary PC degree and circuit IPS

## Main theorem

Let two labelled tensor networks of the same format be given over any field. Use one matrix of variables per named sort, two-sided inverse witnesses, and the literal multilinear action equations for every record. The order of each record is at most three. Compile each network by the directed-path construction for [uniform ring universality](https://github.com/Dugongue/MathProofs/tree/b3bde958f05b17ea912394edb1edd18852b9c85d/HigherOrderUniversality) and take the bare ordinary three-tensor of its associative multiplication table.

The literal network system and the ordinary cubic TI system for those output tensors reduce to each other in ordinary Polynomial Calculus (PC), with absolute constant substitution and derivation degrees. The derivations of individual substituted axioms have polynomial expanded size. Consequently, on geometrically negative instances over fields, minimum PC refutation degrees are equivalent up to absolute constant factors and an additive constant. A sparse PC refutation of the output transfers to a refutation of the network with polynomial sparse-size overhead, even at unbounded degree. Arbitrary circuit Ideal Proof System (IPS) certificates have polynomial size in either system if and only if they have polynomial size in the other. The same holds for Hilbert-like circuit IPS. For source tensors of maximum order $d$ these assertions hold with degree factors depending only on $d$, by using the product ladder. A relation supplied as generator columns is regarded as a labelled linear-map record with the compiler's padded generator-domain change of basis.

The main point is to recover the compiler's hidden labels inside ordinary PC. The high-rank sentinel from the decision proof is unnecessary for this step. Its source is characterized by the absence of incoming arrows in a specific algebra quotient, and the remainder of the path is fixed by comparing only ranks one and two. This avoids invoking ordinary PC to compare unbounded ranks. [Galesi–Grochow–Pitassi–She, proof complexity of TI](https://arxiv.org/html/2305.19320) · [Earlier graph-algebra special case and general isotopy step](https://github.com/Dugongue/MathProofs/blob/b3bde958f05b17ea912394edb1edd18852b9c85d/IsomorphismCrossoversRoundThree/proof-complexity.md)

## Conventions and degree bookkeeping

Use ordinary PC with coefficients in the base field, with scalar linear combinations and multiplication by one variable. Its size here counts monomial occurrences in expanded lines. Matrix identities and evaluations below mean their coordinate equations. Multiplication by a polynomial of bounded degree can be implemented by expanding its monomials and applying the variable-multiplication rule successively. The number of monomials is polynomial in the number of variables, because the degree bound is absolute. Replacing one factor by an already derived equal expression in a product uses the difference multiplied by the other factors.

For labelled order-three records it is convenient to write the equations as
$$
G_W B(x,y)=B'(G_U x,G_V y)
$$
on basis pairs of typed bilinear maps $B:U\times V\to W$. Duals use the transpose of the appropriate inverse witness. This presentation and the literal tensor action are equivalent in constant PC degree: multiply by the witnessed inverse in each input slot and expand, then reduce the two resulting inverse pairs. The same calculation in the opposite direction recovers the original tensor equations. Unary and binary records can be padded using a scalar sort with displayed multiplication. If its scalar witness is $\ell$ with inverse $\ell'$, then $\ell^2-\ell=0$ and $\ell\ell'=1$ derive $\ell=1$ in degree at most three. Padding extends a source witness by $1$ on this sort, and the resulting action equations imply the corresponding literal original equations.

For the algebra stage, let $M:A\to A'$ and $N:A'\to A$ be linear witness matrices. The equations are multiplicativity of $M$ on basis pairs and $MN=NM=I$, with units either included or derived. In fact $(L_{M(1)}-I)M=0$ gives $M(1)=1$ after multiplying by the inverse witness and evaluating at the unit. To derive multiplicativity of $N$, apply the equations for $M$ to two linear inverse images, reduce the two $MN$ products, and apply $N$. These are constant-degree PC calculations.

We use the general unital algebra step from the earlier graph-algebra proof, recalled here for clarity. The cubic three-mode equations on a multiplication tensor are interderivable in constant degree with isotopy equations $H(ab)=X(a)Y(b)$ and the three two-sided inverses. Given an isotopy set $u=X(1),v=Y(1)$, and put $u'=Y H^{-1}(1), v'=X H^{-1}(1)$, where all inverse maps denote witness variables. Expanding the equations at $1$ gives $H=L_uY=R_vX$. Multiplying by the inverses gives $L_u=H Y^{-1}$ and $R_v=H X^{-1}$ and their two-sided inverse identities with $YH^{-1}$ and $XH^{-1}$. Evaluation gives $uu'=v'v=1$. The other products are derived by left- or right-multiplying the associativity identities by the witnessed inverses of $L_u,R_v$. The polynomial substitutions
$$
M(a)=u'H(a)v',\qquad N(b)=H^{-1}(u b v)
$$
then satisfy the algebra equations by expanding and replacing the available inverse factors. For multiplicativity, for example,
$$
M(ab)=u'X(a)Y(b)v'=u'H(a)v'u'H(b)v'=M(a)M(b).
$$
All displayed expressions have an absolute bound on the number of variable factors. In the easy direction substitute $X=Y=H=M$ and all three inverses equal to $N$. Converting between the isotopy and ordinary cubic conventions uses the two input inverse-transposes, a linear relabelling of variables.

## 1. The quotient used by the compiler

Use the publicly indexed corner bases of the two compiled algebras. In each algebra let $J$ denote the direct sum of the off-diagonal corners and $J^2$ its product ideal. Both are invariants that can be recovered in ordinary PC on these witnesses.

For each off-diagonal basis element $x$ in corner $i\to j$ with $i\ne j$, the identity $x=[e_i,x]$ holds. Subtract the two multiplicativity equations and project to the vertex quotient, where all commutators vanish identically. This derives the linear equations that the vertex coordinates of $M(x)$ are zero. Use the multiplicativity of $N$ for the reverse containment. Thus both maps preserve $J$ in the PC calculation.

Every product of two elements of $J$ lies in a specified output corner. In this compiler the output corners are the core $Z$, and the output corners for the projections onto the designated $X$ and $Y$ summands. Every basis vector of each such corner is the product of two explicitly given off-diagonal vectors. For $Z$ this is a scalar-copy product, or the product on the scalar copies for $Z_0$. For a projection corner it is a basis vector of the summand paired with the indicated scalar $1$. Hence $J^2$ is precisely the coordinate direct sum of these entire output corners, independent of the input records. In a multiplicativity equation for one of the displayed products, discard terms containing the already proved zero vertex coordinates. The result after projecting off $J^2$ is the linear equality that the image of that basis vector has no coordinates outside $J^2$. Again the same argument applies to $N$.

The two inverse equations now project to inverse equations on $A/J$ and on $J/J^2$. This needs only deletion of terms containing the already derived linear zero blocks. Write $P=(p_{ui})$ for the induced map on the vertex quotient, and $\widetilde P$ for its inverse. Let $W,W'$ be the induced maps on $J/J^2$ in the two directions. They are literal submatrices of $M,N$ in the fixed coordinate decompositions.

Vertex orthogonality, idempotence and units give row orthogonality, idempotent entries, and row sums equal to one for both $P,\widetilde P$. For row $u$ of $P$, multiplying $(P\widetilde P-I)_{uv}$ by $p_{ui}$ and using row orthogonality gives
$$
p_{ui}\widetilde p_{iv}=\delta_{uv}p_{ui}.
$$
Applying the same calculation to row $i$ of $\widetilde P$ gives
$$
\widetilde p_{iu}p_{uj}=\delta_{ij}\widetilde p_{iu}.
$$
Taking $v=u,j=i$ and subtracting yields $\widetilde p_{iu}=p_{ui}$. Thus the corresponding column sums and column orthogonality also have constant-degree derivations.

## 2. Comparing ranks only on a chosen pair of edges

Let $E_{ij}$ denote the $i\to j$ corner of $J/J^2$ of the source and $E'_{uv}$ the $u\to v$ corner of the target. Write $t=p_{ui}p_{vj}$ for the branch selecting these two endpoints. For any basis vector of $E_{ij}$, a coefficient $w$ of its image in a corner $E'_{ab}$ satisfies
$$
p_{ai}w=w,\qquad p_{bj}w=w.
$$
These are the projected multiplicativity equations for left multiplication by $e_i$ and right multiplication by $e_j$. Terms using two radical factors disappear in $J/J^2$, and the previously derived linear zeros project the equations exactly. If $(a,b)\ne(u,v)$ then the appropriate column orthogonality equation gives $tw=0$. For example, if $a\ne u$, multiply $(p_{ai}-1)w=0$ by $p_{ui}p_{vj}$ and subtract the column collision multiplied by $p_{vj}w$.

Multiply the entries of the source $E_{ij}$ block of $W'W=I$ by $t$. Remove terms indexed by other target corners using these zero equations. This proves, entrywise,
$$
t\bigl(W'_{E_{ij},E'_{uv}}W_{E'_{uv},E_{ij}}-I_{\dim E_{ij}}\bigr)=0.
$$
All derivations have constant degree. If $E_{ij}$ is nonzero and $E'_{uv}$ is zero, a diagonal entry gives $t=0$. If $\dim E_{ij}=2$ and $\dim E'_{uv}=1$, the middle product, say $C$, is a $2\times2$ matrix that factors through one column. Thus $\det C=0$ identically as a polynomial over the field, including in characteristic two. The weighted inverse entries derive
$$
t(\det C-1)=t(C_{11}-1)C_{22}+t(C_{22}-1)-tC_{12}C_{21}=0.
$$
Therefore $t=0$ in constant degree. In the zero versus nonzero case the reverse direction is available by applying the same argument to $N$ and replacing $\widetilde P$ by $P^{\mathsf T}$. In particular an edge in only one of the two branches suffices to kill $t$.

## 3. Fixing all directed-path labels

The directed support of $J/J^2$ consists of the surviving input-side and marker corners. Its sentinel arrow goes from $q$ to $p_0$. Each path vertex $p_i$ has one outgoing rank-one arrow to its tag $v_i$, and, unless it is the last path vertex, one outgoing rank-two arrow to its successor. No other arrow leaves a path vertex. Every original vertex has an incoming tag, every path vertex has an incoming path or sentinel arrow, and no arrow enters $q$. Therefore $q$ is the unique vertex of indegree zero.

Fix any target vertex $u\ne q$ and choose an incoming target edge $a\to u$. No source edge enters $q$. The reverse edge test from Section 2 gives $p_{ai}p_{uq}=0$ for every source vertex $i$. Summing and using the row sum at $a$ gives $p_{uq}=0$. Consequently $p_{qq}=1$ by the column sum at $q$. The only target edge out of $q$ leads to $p_0$, so the forward edge test applied at the source sentinel gives $p_{u,p_0}=0$ for all $u\ne p_0$. Thus $p_{p_0,p_0}=1$.

Suppose $p_i$ is fixed. The forward edge test on its source rank-two arrow leaves only the two possible images $p_{i+1},v_i$ for $p_{i+1}$. The rank-two versus rank-one test eliminates $v_i$. The resulting column sum fixes $p_{i+1}$. Applying the forward test to the source tag leaves only these same two possible images for $v_i$, and row orthogonality with the fixed successor eliminates $p_{i+1}$. The column sum fixes $v_i$. For the last path vertex only the tag remains, so one edge test and column sum suffice.

In this induction each previously established equation $p_{p_i,p_i}=1$ is a previously derived linear line. For example a branch equality $p_{p_i,p_i}p_{u,j}=0$ gives $p_{u,j}=0$ by subtracting $p_{u,j}(p_{p_i,p_i}-1)$. The degree therefore stays bounded by one absolute constant throughout the path. The number of required edge tests, and the number of individual expanded lines, are polynomial in the output size. All vertices are fixed on the quotient by explicit PC derivations.

## 4. Conjugation and recovery of each tensor record

Set $U=\sum_i M(e_i)e_i$ in the target, with the second idempotent in its target standard basis. The previous section derives $U=1+j$ where $j$ is its off-diagonal projection. Since $J^3=0$, the polynomial $1-j+j^2$ is a two-sided inverse of $U$ modulo the already derived equations. Orthogonality of the $M(e_i)$ gives $M(e_i)U=Ue_i$ by expansion. Define
$$
M_0(a)=(1-j+j^2)M(a)(1+j),\qquad N_0(b)=N((1+j)b(1-j+j^2)).
$$
Expanding verifies the inverse and multiplication identities for these new polynomial expressions, and $M_0(e_i)=e_i$ follows from the preceding intertwining identity. The inverse equations give $N_0(e_i)=e_i$. Thus every corner is preserved in both directions: for $x\in e_i A e_j$, apply multiplicativity twice to $x=e_i x e_j$. Every calculation uses an absolute bounded number of factors in $M,N$. In particular the derived zeros off the diagonal corner blocks allow the inverse equations to be restricted to direct corner restrictions.

For a projection onto $X_i$, let $c$ be the scalar map on the one-dimensional argument corner $e_1 A e_{s_i}$ after conjugation. Its inverse is the corresponding scalar from $N_0$. For each source vector in the kernel of the projection, the multiplication by the argument $1$ is zero. Project its multiplicativity equation to the projection target. This gives $c$ times the projected image of that vector equal to zero. Multiplying by the scalar inverse and using its inverse equation proves that this image lies in the corresponding target projection kernel. The same applies to the inverse and to projections from $Y$. Taking all those coordinate zeros preserves each designated $X_i,Y_j$ summand, and gives the inverse equations on the designated summands separately.

Read the scalar-copy equations of the compiler in the core. If $a,b$ are the scalars on $X_0,Y_0$, they have polynomial inverse witnesses from $N_0$. For each index $i$ let $g_i$ be $a^{-1}$ times its $X_i$ block and take its inverse to be $a$ times the corresponding restriction of $N_0$. The copy products give the maps $ag_i,bg_i,abg_i$ on the three copies, first by deriving preservation of each $Z_i$ and then comparing its two scalar-copy formulas. The private-scalar products give the scalar $b$ on that argument and equality of each occurrence map with its reference map. The evaluation products impose the inverse-transpose identities, by evaluating on each basis pair and multiplying by the available inverses. Finally, in each data block, multiplicativity and the three copy formulas give precisely the original typed bilinear equation after multiplying by the polynomial witnesses for $a^{-1},b^{-1}$. Every derived equality uses only a bounded number of variable factors and already derived zeros. In particular the new substitutions and each substituted input axiom have absolute bounded degree in the algebra variables.

## 5. Simulations and consequences

For the other direction, a network witness gives the block map on all three copies of every label, with the two common scalars set equal to one. The projection outputs take the corresponding summand map and the projection arguments take the identity. All other fixed marker corners and vertex basis elements take the identity. This makes the algebra map and its inverse coordinatewise zero, one or an input witness entry. Its inverse equations are blockwise inverse equations or structural identities. Multiplicativity is verified on each allowed product: the copy, data, evaluation, link and projection blocks are exactly the network equations or inverse identities, and all products declared zero remain zero. Choosing the same algebra map in all three isotopy slots gives the ordinary multiplication-tensor witnesses. The input-mode witnesses in the cubic convention are inverse-transposes, so these entries are still constants or single source witness entries. Each substituted output axiom is derived in constant degree.

The product ladder for higher arity lifts a source witness by assigning a product sort the corresponding Kronecker-product matrices and their inverses. Each witness entry in an auxiliary product sort is a monomial of degree at most $d$ in literal source matrix or inverse entries. Conversely a decoded ladder witness satisfies the product-marker equalities, which identify its auxiliary matrices with those Kronecker products by expanding one marker at a time. To recover the original action, replace the product factors in the compiled record by the products over its slots. For fixed $d$, all these compositions use bounded-degree identities and polynomial-size derivations. The monomial property of the extension is retained.

A bounded-degree PC substitution transforms a proof linewise. In a variable-multiplication step, expand the substituted multiplier and carry out its monomial multiplications. Thus a degree-$D$ refutation transforms with degree at most the maximum of the per-axiom derivation degree and a constant multiple of $D$, with constants depending only on $d$ in the higher-arity case. In the output-to-source refutation simulation the substitution for witness entries is always a monomial or constant. A substituted line cannot have more monomials than the original. Intermediate multiplications by factors of the substituted monomial have the same bound, and the standard per-axiom derivations have polynomial size. This proves the sparse-size assertion.

For the IPS assertion, use circuit placeholders for the input axioms of the receiving system, and lift each derived polynomial in the per-axiom PC calculations by the same linear combinations and variable multiplications, with shared circuit nodes. The resulting circuit vanishes when all placeholders are zero and evaluates to the substituted axiom when the placeholders are the receiving axioms. It is linear in the placeholders. Compose these circuits and the variable substitutions into any given IPS certificate. The two required identities follow by substitution, and sharing gives polynomial total circuit size since all the per-axiom calculations have polynomial size. A Hilbert-like certificate remains linear in its placeholders. This claims polynomial circuit size rather than a Hilbert-like certificate degree bound.

Thus the directed-path linear tensor compiler gives a proof-complexity comparison of full literal systems. The unital isotopy step is reused from the earlier graph-algebra work. The new ingredient is the uniform degree-bounded reverse simulation of the actual path and projection markers of the arbitrary-label compiler, over every field. The theorem has a written proof.

## Finite-field equations and commutative coefficient rings

Over $F_q$, one can include the field equation $x^q-x=0$ for every entry of every witness, including the inverse witnesses, in both systems. All conclusions then apply to base-field nonisomorphism with the same degree factors for fixed $q$. In either substitution let $g(z)=\sum_m c_m m(z)$ be a substituted coordinate. The Frobenius identity expresses $g^q-g$ as $\sum_m c_m(m^q-m)$ since $c_m^q=c_m$. Each $m^q-m$ is a telescoping sum of multiples of the equations $z_j^q-z_j$, obtained by replacing one factor at a time in the product of the variable powers. The substituted field equations therefore have PC derivations of degree at most $q\deg(g)$ and polynomial size for fixed $q$ and bounded source arity. These derivations can be included in the IPS translations as well.

The formal identities also give the same simulation over an arbitrary commutative coefficient ring when PC is defined using its ring scalars and IPS identities are interpreted in its polynomial ring. No derivation divides by a ring element. Cancellation of the scalar map of a rank-one corner uses its inverse witness. The claim over rings compares derivations and certificates for the specified systems.

## Verification

An independent written audit checked the recovery and the two simulations. Lean 4.33.0 kernel-checked the weighted two-by-two determinant identity used in Section 2. Its axiom dependency is propext. [Lean source](WeightedRankTwoCorner.lean)
