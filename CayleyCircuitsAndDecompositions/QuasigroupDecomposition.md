# Polynomial-time direct product decomposition of quasigroups

**Theorem.** A deterministic polynomial-time algorithm takes the multiplication table of any finite quasigroup and produces multiplication tables for directly indecomposable factors and an explicit isomorphism to their direct product. This answers Question 7.4 of Johnson, Levet, Vojtěchovský and Widholm. [The published question](https://arxiv.org/html/2508.06478v3#S7).

## 1. Encode multiplication by a transitive action with two operators

Write the input operation as $x*y$. Choose $a,b$ in the quasigroup and put $o=a*b$. The permutations $R_b(x)=x*b$ and $L_a(y)=a*y$ give a loop operation with identity $o$ and recover the original operation:
$$
x\circ y=R_b^{-1}(x)*L_a^{-1}(y),\qquad
x*y=R_b(x)\circ L_a(y).
$$
The two identity equations for $\circ$ follow by substituting $o$, since $R_b^{-1}(o)=a$ and $L_a^{-1}(o)=b$. Denote by $L^\circ_u$ the loop left translation by $u$. For each $T=R_b,L_a$, set $f_T=(L^\circ_{T(o)})^{-1}T$, a permutation fixing $o$.

Let $G$ be the smallest permutation group on the input set containing all left and right translations of the loop and normalized by the two permutations $f_T$. Starting from the loop multiplication group, repeatedly adjoin conjugates of current generators by the two $f_T$. Each strict enlargement at least doubles the order, and the order is at most $n!$, where $n$ is the quasigroup order. Membership and order tests keep this process polynomial and generators can be pruned by membership each time. When no enlargement is needed, conjugation by each $f_T$ maps $G$ onto itself by finiteness. Write $\Omega$ for these two conjugation automorphisms and $H=G_o$ for the point stabilizer. The action of $G$ is transitive since it contains the loop translations. It is faithful because $G$ is a permutation subgroup in this action. In particular, $H$ contains no nontrivial normal subgroup of $G$.

There is a nontrivial direct product decomposition of the quasigroup if and only if
$$
G=U\times V,\qquad H=(H\cap U)(H\cap V)
$$
with $U,V\ne 1$ and both factors invariant under $\Omega$.

For the forward implication, any product of quasigroups expresses $a,b,o$, the principal isotope, and the permutations $f_T$ coordinatewise. The translations of the product loop generate the direct product of the two coordinate multiplication groups. Indeed, a coordinate translation occurs independently by choosing the identity in the other coordinate. Closing under conjugation by the $f_T$ preserves this independent generation: the conjugate of a permutation supported in one coordinate remains supported there, and coordinates can be conjugated independently by starting from these individual generators. Hence the enlarged $G$ is the direct product of the two correspondingly enlarged coordinate groups. Their transitive actions each have more than one point, and the stabilizer of $o$ is the product of its coordinate stabilizers.

Conversely, for such a group decomposition the original set is the transitive coset space
$$
G/H\simeq U/(H\cap U)\times V/(H\cap V).
$$
Each coordinate equality is invariant under the action of $G$. It is compatible with $\circ$ because first holding the second operand fixed uses a loop right translation and then holding the first operand fixed uses a loop left translation. Each $f_T$ acts on the coset space by its conjugation automorphism of $G$, since $f_T$ fixes $o$. This automorphism preserves $H,U,V$, so $f_T$ and its inverse preserve both coordinate equalities. The loop translations and their inverses do the same. Consequently both $R_b,L_a$, their inverses, and the original operation descend to the two quotients. Each original left or right translation is a composition of one of $R_b,L_a$ with a loop translation, so the induced translations are permutations and the quotient operations are quasigroup operations. The displayed bijection preserves the original operation. Both quotients have more than one point because a nontrivial normal factor of $G$ cannot be contained in $H$. Orbit and table scans give the quotient tables and the coordinate bijection in polynomial time.

## 2. Permutation group computations

We use deterministic polynomial-time permutation group routines for stabilizers, order, constructive membership, normal closure, centralizers of normal subgroups, and constructive presentations. A constructive membership test returns a straight-line program in specified group generators. A constructive presentation supplies generators, relators and constructive membership in the presentation generators. We also use Wilson's deterministic polynomial-time algorithm for a Remak decomposition with specified automorphism operators. In our input the images under an operator are explicit permutations and can be converted by constructive membership to words in the supplied generators. Wilson's framework includes this representation of operator groups. [Wilson, *Finding direct product decompositions in polynomial time*, §2.6 and Theorem 6.4](https://arxiv.org/pdf/1005.0548).

In a known decomposition into subgroups with given generators we compute each group projection by rewriting an element in the union of the generator sets and evaluating that word after replacing the generators of the other factors by identities. The images of a subgroup's generators then give its projected subgroup. The kernel of a homomorphism between explicit permutation groups, given by generator images, is also computable with these routines. In detail, take a constructive presentation of the image. Rewrite its presentation generators in the given images and lift those words to the domain. The kernel is the normal closure of the lifted relators and the relations identifying each domain generator with the lift of its image's word in the presentation generators. These relations give precisely the kernel because the resulting quotient has the presentation of the image, with the corresponding generators. Standard membership operations and these presentations use straight-line programs of polynomial size.

The center $Z=Z(G)$ acts semiregularly. A central element fixing $o$ fixes every $g(o)$, since it commutes with all $g\in G$, and hence is the identity. Thus $H\cap Z=1$ and $|Z|\le n$. To enumerate the center explicitly, use orbit breadth-first search to pick a permutation $g_x\in G$ taking $o$ to each $x$, with $g_o=1$. For each $y$ test the map $x\mapsto g_x(y)$ for bijectivity, membership in $G$, and commutation with the group generators. Every central element with image $y$ at $o$ has exactly this map, and every accepted map is central. This gives explicit cyclic coordinates for the finite abelian group $Z$, for example using a constructive abelian presentation and Smith normal form. The same Smith normal form solves polynomial-size linear systems with variables in $Z$, even with given homomorphisms between cyclic coordinate groups in the coefficients. [Kannan and Bachem, *Polynomial algorithms for computing the Smith and Hermite normal forms of an integer matrix*](https://doi.org/10.1137/0208040).

## 3. Restrict the possible noncentral coordinates

Apply Wilson's algorithm to obtain an operator-invariant Remak decomposition
$$
G=\prod_{i\in I}G_i.
$$
Let $I_0\subseteq I$ be the indices of the nonabelian $G_i$, and write bars for images in $G/Z$. This quotient is the direct product of $\overline{G_i}$ over $i\in I_0$. The operator Krull–Remak–Schmidt theorem sends this fixed decomposition to any other operator-invariant Remak decomposition by an automorphism commuting with $\Omega$ and with all inner automorphisms of $G$. Such an automorphism is central: commuting with inner conjugation by $g$ makes conjugation by its image equal to conjugation by $g$. Thus it induces the identity modulo $Z$. It follows that in any $G=U\times V$ with invariant factors, the quotient factors are a partition of the nonabelian coordinates of this fixed decomposition. To see this, refine $U,V$ in the operator category, apply the theorem and group the matching reference factors. [Wilson, Theorem 2.10](https://arxiv.org/pdf/1005.0548).

For $S\subseteq I_0$, let $P_S$ project $\bar G$ onto those coordinates, viewed as a subgroup of $\bar G$. Call $S$ admissible when $P_S$ takes $\bar H$ into $\bar H$. In that case $S^c$ is admissible as well and $\bar H=P_S(\bar H)\times P_{S^c}(\bar H)$. Intersection follows by composition of coordinate projections. Hence the admissible sets are exactly the unions of the blocks of a partition of $I_0$, obtained by successively finding any admissible proper nonempty split of an active block. The same criterion on a block $B$ uses the projected subgroup $P_B(\bar H)$ and is equivalent to further splitting that block. Every stabilizer-compatible group decomposition as in Section 1 has an admissible partition of its noncentral coordinates.

There are at most $\log_2 n$ blocks. Indeed, for each block $B$, put $G_B=\prod_{i\in B}G_i$. If $P_B(\bar H)=\overline{G_B}$, then, since $B$ is admissible, $G_B\subseteq HZ$. Consequently $G_B'\subseteq (HZ)'=H'\subseteq H$. This is a nontrivial normal subgroup of $G$, since $G_B$ is a nonabelian direct factor. This contradicts the faithful action. Thus every block contributes a factor of at least two to $[\bar G: \bar H]$, which is at most $[G:H]=n$ by the quotient map. The empty coordinate set needs no partition.

## 4. Compute the stabilizer blocks without enumerating subsets

For any $S\subseteq I_0$, the order $b(S)=|P_S(\bar H)|$ is computable in polynomial time. Compute the subgroup $J_S$ obtained by projecting $H$ onto $G_S=\prod_{i\in S}G_i$ in $G$. Then
$$
b(S)=\frac{|J_S|}{|J_S\cap Z(G_S)|}.
$$
The intersection size is computed by testing membership of each element of $Z(G_S)$ in $J_S$. The center $Z(G_S)$ is the projection of the already enumerated $Z$.

Fix an active block $B$ and set $r(S)=\log_2 b(S)$ for $S\subseteq B$. This is submodular. The projected subgroup on $S\cup T$ embeds in the fiber product of the projected subgroups on $S,T$ over the projected subgroup on $S\cap T$. Both projections to the overlap are surjective, so the fiber product has order $b(S)b(T)/b(S\cap T)$. Taking logarithms proves the inequality. The cut expression
$$
r(S)+r(B\setminus S)-r(B)
$$
is zero exactly when the projected subgroup on $B$ is the full direct product of its two projected subgroups on the cut. If nonzero, it is at least one, since it is the base-two logarithm of the index of the projected subgroup in that product.

Here is an integer oracle for which ordinary exact submodular minimization suffices. Put $m=|B|$, $M=100(m+1)^2$, and define
$$
u(S)=\lfloor \log_2(b(S)^M)\rfloor+3|S|(m-|S|).
$$
The floor is computed exactly as one less than the bit length of the indicated integer power. Both the power and its bit length have polynomial-size computations, since $b(S)\le n!$ and $M$ is polynomial. The floor perturbs each $Mr(S)$ by a number in $(-1,0]$. For incomparable $S,T$, the quadratic correction contributes $6|S\setminus T|\,|T\setminus S|$ to the submodular slack, which exceeds the maximum loss from rounding. For comparable subsets the submodular inequality is an equality for every set function. Thus $u$ is a submodular integer set function. The symmetric cut function $u(S)+u(B\setminus S)-u(B)-u(\varnothing)$ is also submodular. The error between it and $M(r(S)+r(B\setminus S)-r(B))$ is at most $6m^2+4$ in absolute value, so its value is less than $M/2$ exactly for genuine splitting cuts.

Find a minimum cut subject to containing a fixed coordinate $i$ and omitting $j$, for each $j\ne i$, by minimizing the restricted submodular integer oracle. One of these restrictions contains any given proper nonempty splitting cut or its complement. A minimum below $M/2$ supplies a split. Recurse within both pieces until there are no such cuts. The number of calls is polynomial in the number of Remak factors and all function values have polynomial bit length. [Iwata, Fleischer and Fujishige, *A Combinatorial, Strongly Polynomial-Time Algorithm for Minimizing Submodular Functions*](https://arxiv.org/abs/math/0004089).

## 5. Solve the central correction by linear equations and stable powers

Consider a nonempty proper union $S$ of the computed blocks. The number of such masks is at most $n$. Let $\pi_S:G\to G_S$ be the fixed group projection, with the projection killing all abelian factors and all other nonabelian coordinates. Use the same symbol for the corresponding endomorphism of $G$. It commutes with both operators. Every endomorphism of $G$ inducing $P_S$ modulo $Z$ is of the form
$$
e(x)=\pi_S(x)c(x)
$$
for a homomorphism $c:G\to Z$. Indeed two homomorphisms agreeing modulo the center differ pointwise by a central homomorphism. Conversely every such $c$ gives an endomorphism of this form.

Since $Z\cap H=1$, the map $H\to\bar H$ is an isomorphism. Let $H_S,H_{S^c}$ be the corresponding subgroups of $H$ supported on their indicated coordinates modulo $Z$. They form a direct product in $H$, because $S$ is admissible. Compute generators for $H_S$ as follows. Let $J$ be the projected subgroup of $H$ on $G_{S^c}$, using the nonabelian factors there. First compute the kernel of $H\to J$ as in Section 2. Then adjoin to that kernel a preimage in $H$ of each member of $J\cap Z(G_{S^c})$. Find the intersection by scanning the projected center and testing membership in $J$. Lift each intersecting element by constructive membership in the images of the given generators of $H$. The resulting group is exactly the preimage of the intersection, hence exactly $H_S$. The other subgroup is obtained by the same procedure with the two sides exchanged.

We seek $c$ for which $e$ commutes with both operators and satisfies
$$
e(h)=h\quad(h\in H_S),\qquad e(h)=1\quad(h\in H_{S^c}).
$$
The latter equations suffice on given subgroup generators. Their required values for $c(h)$ are central, by the definition of $H_S,H_{S^c}$. The operator equations on a generator $x$ for an operator $\alpha$ are
$$
c(\alpha(x))=\alpha(c(x)).
$$
These are linear conditions in the abelian group $Z$. For the homomorphism condition choose a constructive presentation of $G$, give each generator an unknown image in $Z$, and impose every defining relator. Evaluation of every word in $Z$ is linear in the unknowns using its signed generator exponent sums. If a word is a straight-line program, compute the sums by applying the program to exponent vectors modulo $|Z|$. The image of each element mentioned in a constraint can therefore be written as a linear expression. The actions of the two operators on $Z$ are known linear maps in its cyclic coordinates. Smith normal form decides the complete system and produces a solution when one exists.

We do not require $e^2=e$ in this system. For any resulting $e$, choose $k$ large enough that the kernels and images of its powers stabilize on both $G$ and $H$. For example $k=2+\lceil\log_2(n!)\rceil$ suffices, since every strict inclusion of finite subgroups changes the order by a factor of at least two, and after an equality the same chain remains stationary. Set $U=\operatorname{im}e^k$ and $V=\ker e^k$. The restriction of $e^k$ to $U$ is a surjection onto $U$, so $U\cap V=1$. The first isomorphism theorem gives $|U||V|=|G|$. Furthermore $e^k$ induces $P_S$ on the central quotient. Every element of $U$ lies in $G_SZ$, and every element of $V$ lies in $\ker(\pi_S)Z$. These two groups commute, so $G=U\times V$. The identical stable power construction inside $H$, which $e$ preserves, gives $H=(H\cap U)(H\cap V)$. The intersection $H\cap U$ contains $e^k(H)$. The map $e^k$ takes the finite set $H\cap U$ injectively to itself, so it is onto that intersection, proving equality. Both $U,V$ are invariant under the operators. Both are nontrivial, because $P_S$ is a nonzero proper projection, so $U$ maps onto its nontrivial quotient image, and $UV=G$ forces $V$ to account for the nontrivial complementary quotient.

Conversely, any compatible split whose two factors are nonabelian yields one of the tested masks by Section 3. Its actual projection onto the first factor has the form $\pi_Sc$. The hypotheses on $H$ and its injective map into $\bar G$ make the two stabilizer subgroups precisely $H_S,H_{S^c}$, so this projection supplies a solution to the system. Thus these tests are exact for detecting a split with two nonabelian sides.

## 6. Detect a central factor

A split with an abelian side has that side in $Z$, because it is a direct factor of $G$. Its projection is a homomorphism $c:G\to Z$ commuting with the operators and killing $H$. Indeed it maps $H$ into the intersection of $H$ with the abelian side, which is trivial.

For nonabelian $G$, enumerate nonidentity $z\in Z$ and solve for a homomorphism $c:G\to Z$ commuting with the operators, with $c(H)=1$ and $c(z)=z$. Use the same linear system as before with $\pi_S=1$, where $1$ denotes the trivial group homomorphism. The fixed nonidentity element ensures the stable image is nontrivial. It is central and proper since $G$ is nonabelian. The stable kernel is therefore nontrivial, and it contains $H$. The stable image and kernel form a direct product by the intersection and order argument of Section 5, with commutation immediate from centrality. If $G$ is abelian, its faithful transitive action is regular and $G=Z$ has at most $n$ elements. In this case also enumerate nonidentity $w\in Z$ and demand $c(w)=1$, ensuring that the kernel is nontrivial. In either case a genuine compatible split with an abelian side gives a feasible system by choosing a nonidentity $z$ in that side and, in the abelian case, a nonidentity $w$ in its complement.

Construct $U,V$ from a successful system by evaluating the $k$-fold power on generators, using constructive membership to express their successive images. The resulting homomorphism is represented by generator images, and its kernel is computed as in Section 2. The number of those powers and the size of every group representation used in this procedure are polynomial in $n$.

## 7. Fully refine the quotient tables

Test the central case and the at most $n$ noncentral masks. If none succeeds, the equivalence of Section 1 and the two necessity arguments prove that the input quasigroup is directly indecomposable. If one succeeds, compute the two quotient multiplication tables and coordinate map by the action construction. Apply the same procedure to each quotient until every factor is directly indecomposable. There are at most $\lfloor\log_2 n\rfloor$ nontrivial final factors for $n>1$, since their orders multiply to $n$ and each is at least two. The size-one quasigroup gives an empty product. Composing the coordinate maps yields the explicit product isomorphism. Overall the number of calls and each local calculation are polynomial in the input table size.

The argument is an informal proof. Wilson's Remak algorithm supplies the unconstrained operator-group factors. The stabilizer-block computation and the conversion of central homomorphism solutions into stabilizer-compatible factors provide the additional steps needed for the quasigroup question.
