# Exact special-linear equivalence for matrix slices from split local algebras

View a tensor of shape $n\times n\times s$ over $K$ as an ordered independent list of square matrix slices. This note concerns the class for which the span $\mathcal M$ is $H D$ with $H$ invertible and
$$
D \ \simeq\ \prod_{j=1}^{h} K[t_j]/(t_j^{e_j})
\ \subseteq \operatorname{End}_K(V)
$$
a unital algebra on an $n$-dimensional space $V$. The action of $D$ on $V$ is faithful, and its left and right ambient tensor spaces can have unrelated given bases.

**Theorem.** On this class, the literal three-mode determinant-one transporter question is equivalent to comparing the local algebra and module types, followed by at most four explicit tests for membership in a three-row integer monomial image over $K^\times$. The criterion is necessary and sufficient over the input field, with explicit witness lifts. The class is recognizable and the equivalence problem is deterministic polynomial time over each fixed finite field and over $\mathbb Q$. With a supplied verified decomposition, the finite-field decision step is polynomial also in $\log |K|$. All three modes can be full support and arbitrarily large. This gives a reduction to ordinary tensor isomorphism on the stated class, by outputting fixed yes and no instances after the direct decision.

The proof is informal. The tensor action convention is that a triple $(P,Q,R)$ takes a slice basis $(A_i)$ to the basis whose $i$th slice is $\sum_j R_{ij} P A_j Q^{\mathsf T}$.

## 1. Find the ordinary transporter type

Each $D_j=K[t_j]/(t_j^{e_j})$ has a central identity idempotent, which splits off a module $V_j$ of $V$. On $V_j$ the action of $t_j$ is nilpotent and has a Jordan decomposition
$$
V_j \simeq \bigoplus_{k=1}^{e_j} (K[t_j]/(t_j^k))^{m_{jk}} .
$$
Faithfulness forces $m_{j,e_j}>0$. Set
$$
v_j=\sum_k k m_{jk},\qquad p_j=\binom{e_j}{2},\qquad
q_j=\sum_k m_{jk}\binom{k}{2}.
$$
The local type is the list $(e_j,m_{j1},\ldots,m_{j,e_j})$.

Any invertible matrix in $\mathcal M$ can serve as the left factor $H$. Indeed the old inverse times the new choice lies in $D$ and is a unit there, since the inverse of an invertible matrix is a polynomial in that matrix. Multiplication by a unit of $D$ preserves $D$ as a linear space. Once $H$, the local idempotents, and the local generators are known, choose a basis $X$ of $V$ by Jordan chains for each local action. Order the local blocks by their types and the chain bases by chain length. The first two maps $X^{-1}H^{-1}$ and $X^{\mathsf T}$ carry $H D$ to the canonical split model. A third-mode basis change gives the canonical slice basis consisting of $1,t_j,\ldots,t_j^{e_j-1}$ on each local block, with $1$ meaning the identity of that block. Call this ordinary transporter $C_T$, and record each of its three determinants.

Here the ordinary types are complete. For unital normalized spaces $D,D'$, suppose $P D Q^{\mathsf T}=D'$. The matrix $d=P Q^{\mathsf T}$ lies in $(D')^\times$. Thus $P D P^{-1}=D'$, by right multiplication by $d^{-1}$. This conjugation induces an algebra isomorphism and a compatible module isomorphism, so the local types match as multisets. Conversely equal local types yield the same canonical tensor. In the following computation assume both tensors have that common canonical representative.

## 2. Compute the entire determinant image of the stabilizer

Let $T_0$ be the canonical tensor. Its ordinary stabilizer is parametrized by $P$ in the matrix normalizer of $D$ and $d\in D^\times$. Take $Q^{\mathsf T}=P^{-1}d$ and let $R$ be the inverse of the slice basis action, in the convention above. More precisely, if $\alpha(A)=PAP^{-1}$, the left-right action on the slice space is $A\mapsto \alpha(A)d$, and the determinant of $R$ is the reciprocal of the determinant of this map. This describes every stabilizer triple by Section 1 and the independence of the slices.

An algebra automorphism permutes the local factors of equal $e_j$. After matching local generators, its restriction on a fixed factor with $e_j>1$ sends $t_j$ to $a_jt_j$ plus higher powers, with $a_j\ne0$. Its action on the layers $t_j^r D_j/t_j^{r+1}D_j$ is multiplication by $a_j^r$. Hence its determinant on a local algebra block is $a_j^{p_j}$. For a lift to $V$, an allowed permutation must preserve the full local types. Every such permutation lifts by exchanging based module blocks. Every parameter change lifts by the same substitution on each cyclic summand, because it preserves the ideal $(t_j^k)$. Its determinant on $V_j$ is $a_j^{q_j}$. When $e_j=1$ the two exponents are zero and there is no parameter change.

Any two lifts of the same algebra automorphism differ by a $D$-linear automorphism of $V$. Its full determinant image can be read from the $t_j$-adic filtrations. For fixed $j$, a map from a chain of length $k$ to one of length $l$ sends its generator to a vector divisible by $t_j^{\max(0,l-k)}$ in the target. On each layer $t_j^r V_j/t_j^{r+1}V_j$, ordered by chain length, its matrix is therefore block triangular. The block on chains of length $k$ is the same constant coefficient matrix $B_{jk}$ on each of the $k$ layers in which these chains survive. A module automorphism has all these blocks invertible, and its determinant on $V_j$ is $\prod_k(\det B_{jk})^k$. Conversely arbitrary $B_{jk}\in\operatorname{GL}_{m_{jk}}(K)$ lift by constant matrices on the groups of equal-length chains. This determines the precise determinant freedom in the lift.

Finally, if $d\in D^\times$ has scalar residues $u_j$ on the local factors, its determinant on $V$ is $\prod_j u_j^{v_j}$ and the determinant of multiplication by $d$ on $D$ is $\prod_j u_j^{e_j}$. These assertions also follow by the $t_j$-adic filtrations. All residues $u_j\ne0$ are allowed.

Combine the independent variables $a_j,u_j,z_{jk}$, where $z_{jk}=\det B_{jk}\in K^\times$. Let $\mathcal L$ be the integer matrix with three rows and columns
$$
(q_j,-q_j,-p_j),\qquad (0,v_j,-e_j),\qquad
(k,-k,0)\quad (m_{jk}>0).
$$
The third kind of column is included for each occupied chain length of each factor. The monomial image of $\mathcal L$ in $(K^\times)^3$ gives the determinant triples realized without permuting the local factors.

The only additional determinant factors are the sign triples from permutations among equal local types. A transposition exchanges two blocks of size $v_j$ on $V$ and two blocks of size $e_j$ on $D$, giving
$$
\left((-1)^{v_j},\;(-1)^{v_j},\;(-1)^{e_j}\right).
$$
Include this generator for each repeated type. The group they generate has size at most four. The determinant image of the full ordinary stabilizer is exactly the product of this sign group and the monomial image. Each parameter and each allowed sign is realized by the lifts just given, so the formula specifies both the restrictions and all attainable triples.

For inputs $T,S$ of common type, write $\delta(C_T)$ and $\delta(C_S)$ for their triples of calibration determinants. The exact test is
$$
\delta(C_S)\,\delta(C_T)^{-1}\in
\delta(\operatorname{Aut}_{\rm GL^3}(T_0)).
$$
Indeed every ordinary transporter is $C_S^{-1} A C_T$ with $A$ an ordinary stabilizer of $T_0$. A solution of the monomial equations and an allowed sign explicitly supply $A$, and hence a literal special-linear transporter from $T$ to $S$.

## 3. Test monomial membership

For each admissible sign shift, compute a Smith form of $\mathcal L$. Unimodular row and column operations give bijective monomial coordinate changes on products of $K^\times$. Thus diagonal entries $d_i>0$ give tests of whether the transformed target coordinate is a $d_i$th power. A zero diagonal entry requires the transformed coordinate to equal $1$. This is a decision reduction over any field to at most three power-membership tests per sign shift, with a same-field lifting formula in the reverse direction.

Over $\mathbb F_q$, a nonzero scalar $u$ is a $d_i$th power exactly when $u^{(q-1)/\gcd(d_i,q-1)}=1$. Repeated squaring gives a polynomial-time test in the usual exact encodings, without computing discrete logarithms or finding a generator of $\mathbb F_q^\times$. Witness roots can be found by field enumeration when $q$ is fixed. Over an algebraically closed field, each positive power test always succeeds. Over $\mathbb Q$, the tests are deterministic polynomial time in the input bit length, even if the Smith change-of-basis entries have large numerical values. Represent all numerators and denominators of the input calibration scalars on pairwise coprime integer bases obtained by repeated gcd splitting. Each split decreases the total logarithmic size of the factors before duplicates are merged. This is a polynomial-size representation of all transformed rationals as signed products of those bases with integer exponents written in binary. For each exponent $a$ on a base $b>1$, its contribution is a $d_i$th power exactly when $b$ is a $(d_i/\gcd(d_i,|a|))$th power. Check this by integer roots. Pairwise coprimeness makes the tests independent, and for even $d_i$ positivity is required as well. The equality-to-$1$ test uses the sign and binary exponents directly. Standard deterministic Smith algorithms suffice for the integer part. [Kannan–Bachem](https://doi.org/10.1137/0208040)

## 4. Recover the slice algebra with ordinary linear algebra

The input need not contain an invertible matrix among its listed slices. Form the intertwined endomorphism algebra
$$
\mathcal E=\{(P,Q)\in M_n(K)^2 : P A_i=A_i Q\text{ for all }i\}.
$$
Its vector space is a linear kernel and multiplication is componentwise matrix multiplication. Compute its center by commuting with a basis. Under the hypothesis $\mathcal M=HD$, multiplication by $H^{-1}$ shows that $P=HQH^{-1}$ and that $Q$ commutes with all of $D$. Thus $\mathcal E$ is isomorphic to $\operatorname{End}_D(V)$ by projection to its second coordinate.

Faithfulness provides at least one length-$e_j$ chain for every factor. Consequently $V$ contains a copy $W\cong D$ as a regular direct summand over $D$. A central member of $\operatorname{End}_D(V)$ commutes with the projection onto $W$ and acts there by multiplication by some $d\in D$. For every $v\in V$, the map $W\to V$ sending $1$ to $v$ is $D$-linear and extends by zero on the chosen complement of $W$. Commuting with these maps forces the central member to agree with multiplication by $d$ on every $v$. Conversely multiplication by each $d\in D$ is central. This identifies the entire center with $D$ without first finding $H$.

Recover the primitive central idempotents as pairs $(P_j,Q_j)$. Their first and second components project onto the matched row and column summands. The matrices $P_j A_i=A_iQ_j$ are in $\mathcal M$ under the class hypothesis and span the $j$th local part of the space. In that part, some projected slice is invertible between its row and column spaces. Indeed its local scalar residue must span $K$ as the slices range through a spanning list, and a nonzero scalar residue gives an invertible map on the local module. Choose one of maximal local rank by testing the listed projections, and sum these choices over $j$. This yields an invertible $H$ in $\mathcal M$ with no determinant polynomial search.

For recognition, verify that every needed projected slice belongs to $\mathcal M$, that the constructed $H$ is invertible, and that $H^{-1}\mathcal M$ is the second projection of the computed center. For a local algebra component, choose a generator $t_j$ of its nilpotent ideal and verify directly that $1,t_j,\ldots,t_j^{e_j-1}$ are a basis and $t_j^{e_j}=0$. The idempotents and these bases certify the split product structure. On a promised local factor of dimension greater than one, any nonzero class of its nilradical modulo its square gives a suitable generator. In dimension one take $t_j=0$. These checks give sound recognition, and the preceding analysis gives completeness on the stated class.

Over $\mathbb F_q$, use Frobenius to compute the needed radical and idempotents of the commutative center. The kernel of $x\mapsto x^{q^u}$ for $q^u\ge\dim\mathcal E$ gives its nilradical, since nilpotent elements have nilpotency index bounded by the dimension, while a power of a nonnilpotent element is never zero. The solutions of $x^q=x$ in the center form an $\mathbb F_q$-linear subalgebra. Under the split hypothesis this is exactly $\mathbb F_q^h$ inside the split product. Simultaneously split the multiplication operators of a basis of this subalgebra by computing their common eigenspaces. The one-dimensional common eigenspaces give the primitive idempotents by rescaling any nonzero vector in each. Enumerating the $q$ possible eigenvalues gives a deterministic $\operatorname{poly}(q,N)$ recognition procedure, hence polynomial time over each fixed finite field. For variable $q$, one can instead use a split polynomial factoring routine in this step or verify supplied idempotents and generators in polynomial bit time. The power-membership step in Section 3 uses neither eigenvalue enumeration nor factoring.

Over $\mathbb Q$ the deterministic polynomial-time algorithms of Lenstra and Silverberg find primitive idempotents and the nilradical of the commutative center from structure constants. The remaining operations are exact elimination, matrix multiplication, and nilpotent Jordan-chain construction. These give deterministic polynomial-time recognition and calibration. Over an arbitrary field the theorem is structural with supplied verified data and the stated power tests, or with whatever coefficient operations are needed to find such data. [Lenstra–Silverberg](https://arxiv.org/abs/1509.08843) · [Eberly–Giesbrecht](https://doi.org/10.1006/jsco.1999.0308)

## 5. Finite-field extension to nonsplit local factors

A supplied, consistently based local decomposition also gives an exact finite-field criterion for products of $L_j[t_j]/(t_j^{e_j})$ with $L_j=\mathbb F_{q^{f_j}}$ over $K=\mathbb F_q$. Define $v_j,p_j,q_j$ using dimensions and chain multiplicities over $L_j$, and include $f_j$ in the local type. The exponent columns in Section 2 stay the same, while the sign group has two sources:

- A swap of equal local types gives $\bigl((-1)^{f_jv_j},(-1)^{f_jv_j},(-1)^{f_je_j}\bigr)$.
- The field Frobenius on any one local factor gives $\bigl((-1)^{(f_j-1)v_j},(-1)^{(f_j-1)v_j},(-1)^{(f_j-1)e_j}\bigr)$.

To verify this, the coefficient field inside a local factor is intrinsic as the set of $q^{f_j}$-Frobenius fixed points. Each algebra automorphism on a factor consists of a field automorphism and a change of parameter with nonzero linear term. Determinants of the $L_j$-linear layer maps as $K$-linear maps are field norms of their $L_j$ determinants. These norms range over all of $K^\times$, so each variable in the monomial image remains independent and unrestricted. The regular action of the field Frobenius on $L_j$ has determinant $(-1)^{f_j-1}$. After extension to an algebraic closure its action permutes the $f_j$ distinct embeddings in one cycle. There are $e_j$ field copies in the algebra and $v_j$ in the module, giving the displayed signs. Every listed sign and every norm contribution has the concrete same-field lifts described by the local maps and their residues. This proves the profile formula, and the same finite-field power tests apply. The extension presumes the verified normalization and matched field models; the recognition algorithm above was proved for the split class.

## 6. An arbitrarily large example and relation to prior work

Over $\mathbb F_3$, take any number $h$ of copies of $\mathbb F_3[t]/(t^2)$, each acting on $m$ copies of its length-two cyclic module. The tensor has shape $2hm\times 2hm\times 2h$, with all three modes full. The stabilizer profile is exactly
$$
\{(a^m,a^{-m},a^{-1}):a\in\mathbb F_3^\times\}.
$$
Indeed a unit residue on an algebra component contributes even powers, all module centralizer exponents are two, and every allowed block permutation has even signs on both $D$ and $V$. The parameter automorphisms supply the displayed two possibilities. Applying a single ambient reflection on the first mode gives an ordinary-equivalent tensor with calibration ratio $(-1,1,1)$, outside the profile. Thus literal special-linear equivalence is a genuine extra condition in this class, rather than automatic after one observes ordinary equivalence.

Britnell and Wildon give the determinant image of the centralizer of a matrix over finite fields. In the nilpotent case the image is generated by powers given by the Jordan length data. The calculation here incorporates those powers together with local algebra parameter changes, unit multiplication in a normalized slice space, and determinant signs of indistinguishable local block permutations. All three determinant constraints then enter one exact arithmetic calculation. The endomorphism-center step uses the regular summand of this particular representation to recover the slice algebra even in the absence of an invertible listed slice. [Britnell–Wildon, Section 3](https://arxiv.org/abs/1001.0811)

Grochow and coauthors develop reductions between tensor and matrix-space actions and ask about special-linear actions in their classical-group paper. The present result is a direct same-field decision procedure and hence a many-one reduction on the specified normalized slice class. The unrestricted same-field reverse reduction remains open in this work. The cited results establish the antecedents for centralizer determinants and algebra algorithms. Publication priority for the combined criterion remains unverified. [Chen–Grochow–Qiao–Tang–Zhang, Section 1](https://arxiv.org/html/2306.03135v2#S1) · [Grochow–Qiao, Part IV](https://arxiv.org/abs/2306.16317) · [Grochow–Qiao–Stange–Sun, Part V](https://arxiv.org/abs/2611.00735)

The companion [Tensor.py](Tensor.py) checks 4,608 pairs of ambient invertible matrices over $\mathbb F_3$ for the two dimension-two slice spaces. It finds respectively two and eight stabilizer determinant triples for the truncated algebra and split diagonal algebra. It also checks all 6,561 endomorphism pairs for a split space with two singular listed slices and reconstructs an invertible member of their span from the central idempotents.
