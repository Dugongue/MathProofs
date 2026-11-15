# Polynomial isomorphism of diagrams of abelian group extensions

**Status.** AI-assisted informal proof. The algorithmic conclusion is deterministic polynomial time in the specified input encoding. This manuscript has not been Lean-verified or independently peer-reviewed. The underlying translation from group extensions to module extensions is classical. The contribution presented here is an explicit finite encoding, a reduction to one finite-module isomorphism instance, and its simultaneous and marked versions.

## The theorem and the published questions

**Theorem 1.** Let a finite directed graph index two diagrams of finite groups. At each vertex $i$, supply an abelian normal subgroup $A_i\unlhd G_i$ and $A'_i\unlhd G'_i$, and an isomorphism
$$
\alpha_i:G_i/A_i\longrightarrow G'_i/A'_i.
$$
For each arrow, supply homomorphisms between the corresponding groups, carrying the specified kernels into the specified kernels. Require the two induced quotient maps to commute with the supplied $\alpha_i$. Optionally supply pairs of marked elements at any vertices.

There is a deterministic polynomial-time algorithm deciding whether there are isomorphisms $\phi_i:G_i\to G'_i$ that induce the $\alpha_i$, commute with every arrow, and send every marked element to its prescribed partner. If they exist, the algorithm returns them. A single finite-module isomorphism instance suffices.

For Cayley-table inputs the algorithm also computes the entire solution coset, generators for its automorphism group, and the exact number of solutions in deterministic polynomial time. The number of vertices, arrows, marks, quotient generators, and cyclic factors of the kernels is unrestricted and is charged to the input length.

Decision and search also have a stronger encoding bound. The kernels may be given by cyclic coordinates with their orders in binary, the quotients by explicit tables, the actions by matrices in cyclic coordinates, and the normalized cocycles by explicit tables. Arrow homomorphisms may be given by their maps on kernel generators and quotient sections. The runtime is polynomial in the bit length of this data, even when the kernels have exponentially many elements. The counting and automorphism-generator assertion above is made for explicit Cayley tables, not for this succinct encoding.

With one vertex and no arrows or marks this removes the quotient-generator restriction in Skresanov's Theorem 1.1, answering the question following Corollary 1.5. It also supplies the extension of Theorem 6.11 requested in the first part of Grochow–Qiao Open Problem 8.1. The second part, a polynomial-time algorithm for all groups with abelian solvable radical without a supplied quotient isomorphism, is not established. [Skresanov](https://arxiv.org/html/2602.15497v2#S1), [Grochow–Qiao, Section 8.1](https://opus.lib.uts.edu.au/rest/bitstreams/0a860f36-47a1-4392-adef-100a1cc03886/retrieve).

## 1. Extension coordinates

Transport each target quotient along its supplied isomorphism. At each vertex both quotients are now the same explicitly labeled group $Q$, and the desired quotient map is the identity. Choose normalized sections. Write an extension as
$$
E_f=A\times Q,\qquad
(a,x)(b,y)=(a+\rho_x(b)+f(x,y),xy),
$$
where $\rho:Q\to\operatorname{Aut}(A)$ and
$$
f(1,x)=f(x,1)=0,\qquad
\rho_x f(y,z)+f(x,yz)=f(x,y)+f(xy,z).
\tag{1}
$$
All these data are extracted in polynomial time from Cayley tables. In the succinct model they are the input; the action, cocycle, and arrow identities can be checked in polynomial time as well.

Choose one integer $e\ge2$ annihilating every kernel in both diagrams. Take the least common multiple of their exponents, except that when this is 1 use $e=2$. Its bit length is at most the sum of the kernel exponent bit lengths. Set $K=\mathbb Z/e\mathbb Z$. Every abelian group below is a $K$-module. No factorization of $e$ is required.

## 2. A finite module containing the whole extension

Let $I_Q$ be the free $K$-module on symbols $d_x$, for $x\ne1$, and put $d_1=0$. Give it the action
$$
q\cdot d_x=d_{qx}-d_q.
$$
This is the augmentation ideal of $K[Q]$, with $d_x=x-1$.

On the additive module $M_f=A\oplus I_Q$, define
$$
q\cdot(a,0)=(\rho_q(a),0),\qquad
q\cdot(0,d_x)=(f(q,x),d_{qx}-d_q).
\tag{2}
$$
Extend $K$-linearly. This is well-defined because $eA=0$. It is a group action: on the kernel it follows from $\rho$, and on $d_x$ the first component of $q(r(0,d_x))$ is
$$
\rho_q f(r,x)+f(q,rx)-f(q,r)=f(qr,x)
$$
by (1). The second component is $d_{qrx}-d_{qr}$. The identity acts identically, so the action of $q^{-1}$ supplies the inverse.

Projection gives an exact sequence of finite $K[Q]$-modules
$$
0\longrightarrow A\longrightarrow M_f\xrightarrow{\pi} I_Q\longrightarrow0.
\tag{3}
$$
Although $M_f$ may have exponentially many elements, its cyclic-coordinate description has bit length
$$
\log_2|M_f|=\log_2|A|+(|Q|-1)\log_2 e.
\tag{4}
$$
We never enumerate its elements.

The classical background is the translation between abelian group extensions and extensions of the augmentation ideal. Formula (2) is sufficient to verify all properties needed here directly, including reduction modulo the common annihilator. [Atsuta–Kataoka, Definition 2.1 and Proposition 2.2, describing Gruenberg's translation functor](https://ems.press/content/serial-article-files/51549).

## 3. Exact recovery of group homomorphisms

Consider two extensions of the same $Q$. A $K[Q]$-linear map $L:M_f\to M_{f'}$ inducing the identity on $I_Q$ has the form
$$
L(a,0)=(u(a),0),\qquad L(0,d_x)=(v(x),d_x),\quad v(1)=0.
$$
Its intertwining conditions are exactly
$$
u\rho_q=\rho'_q u,\qquad
u f(q,x)-f'(q,x)=v(q)+\rho'_qv(x)-v(qx).
\tag{5}
$$
Consequently
$$
\phi(a,x)=(u(a)+v(x),x)
\tag{6}
$$
is a homomorphism of groups over $Q$. Conversely every group homomorphism over $Q$ gives (5), hence a unique such $L$. The maps are invertible simultaneously, since both are invertible exactly when $u$ is invertible.

Define $\tau_f(a,x)=(a,d_x)\in M_f$. Its values generate $M_f$ additively, and
$$
\tau_f(gh)=\tau_f(g)+\overline g\cdot\tau_f(h).
$$
It is injective: the symbols $0,d_x$ are distinct over $K$ because $e\ge2$, and within each fiber the first component records $a$. Equation (6) is equivalently $L\tau_f=\tau_{f'}\phi$.

This correspondence also covers arrows with different quotient groups. If $F:E_f\to E_h$ induces $\beta:Q\to R$, write
$$
F(a,x)=(u(a)+v(x),\beta(x)).
$$
Define the additive map $\widehat F:M_f\to M_h$ by
$$
\widehat F(a,0)=(u(a),0),\qquad
\widehat F(0,d_x)=(v(x),d_{\beta(x)}).
\tag{7}
$$
Then $\widehat F\tau_f=\tau_h F$. This construction preserves composition, because the $\tau_f(g)$ generate. Thus commutation of group arrows is equivalent to commutation of their additive maps, once the vertex maps satisfy (5). No faithfulness or surjectivity assumption on an arrow is needed.

## 4. One cyclic anchor forces every quotient map

Build the additive module
$$
X=K\oplus\bigoplus_i(I_{Q_i}\oplus M_{f_i})
$$
and its counterpart $Y$ for the target diagram. Prescribe a tuple of additive endomorphisms on each of them:

1. Projections onto the anchor $K$ and onto each individual $I_{Q_i}$ and $M_{f_i}$.
2. The action of every $q\in Q_i$ on $M_{f_i}$, extended by zero on other summands.
3. The arrows $\pi_i:M_{f_i}\to I_{Q_i}$, extended by zero.
4. For each quotient basis vector, an arrow $K\to I_{Q_i}$ taking $1$ to $d_x$.
5. The maps (7) for all diagram arrows.
6. For each marked element $g$, an arrow $K\to M_{f_i}$ taking $1$ to $\tau_{f_i}(g)$, paired with the corresponding target mark.

Each arrow between distinct summands is regarded as an endomorphism of the direct sum. Multiple arrows, loops, and cycles cause no problem. For a loop use the corresponding endomorphism on that summand.

Let $T:X\to Y$ be an additive isomorphism intertwining all paired endomorphisms. The projections make it block diagonal. Its anchor block is multiplication by a unit $\lambda\in K^\times$. The basis arrows force its $I_{Q_i}$ block to be $\lambda\operatorname{id}$, for every $i$. Commutation with the projections $\pi_i$ therefore gives
$$
\pi'_i T_i=\lambda\pi_i.
$$
Normalize *all* blocks by the same scalar $\lambda^{-1}$. The resulting maps still intertwine every arrow and action, and each $M$-block now induces the identity on $I_{Q_i}$. Section 3 produces exactly the required group isomorphisms. The marked arrows enforce exactly the required marked-element images after the same normalization.

Conversely, a solution of the original diagram problem gives such a $T$, with anchor block 1, by Sections 2–3. This proves equivalence, not merely one direction. A trivial quotient contributes a zero $I_Q$ and causes no exception.

The cyclic anchor is important. It forces the scalar used in normalization to be a *unit* even for composite $e$; invertibility of an unrelated block is never used to infer that a nonunit scalar is invertible.

For a small composite-modulus example, take a trivial action of $Q=C_2$ on $A=C_4$, and let $c=f(q,q)$. On $M_f=(\mathbb Z/4)^2$ the action of the nonidentity quotient element is the matrix
$$
\begin{pmatrix}1&c\\0&-1\end{pmatrix}.
$$
An anchored intertwiner has matrix $\left(\begin{smallmatrix}u&v\\0&\lambda\end{smallmatrix}\right)$, with both $u$ and $\lambda$ odd, and the remaining equation is $uc-\lambda c'=2v$. Thus $c=1,c'=0$ is correctly rejected, distinguishing $C_8$ from the split extension $C_4\times C_2$, whereas $c=2,c'=0$ admits $u=\lambda=v=1$. The construction never divides by 2 in $\mathbb Z/4$.

## 5. Compiling the paired operators into one finite ring

For each paired operator $(s_X,s_Y)$, regard it as an element of
$$
\operatorname{End}(X)\times\operatorname{End}(Y).
$$
Let $B$ be the unital subring they generate. The coordinate projections make $X,Y$ into finite left $B$-modules. A $B$-module isomorphism is exactly an additive isomorphism intertwining every paired operator.

Compute $B$ by additive subgroup closure and multiplication, in cyclic coordinates. Start with the identity and all paired operators. Maintain additive generators for their span; adjoin products of these generators until the span is multiplicatively closed. Each unsuccessful closure strictly enlarges a finite additive subgroup and therefore at least doubles its order. If $L=\log_2|X|+\log_2|Y|$, then
$$
\log_2|\operatorname{End}(X)\times\operatorname{End}(Y)|\le L^2.
$$
There are at most $L^2$ strict enlargements. A finite abelian group of this logarithmic order needs at most $L^2$ cyclic generators. Images of cyclic generators describe endomorphisms; the order constraints are linear congruences. Smith or Hermite normal form computes subgroup membership, cyclic coordinates, and multiplication coordinates with polynomial bit complexity. Every modulus and intermediate reduced generator has polynomial bit length. These operations construct a finite-ring presentation and the two module actions with polynomial encoding length.

Apply the deterministic finite-module isomorphism algorithm of Ciocănea-Teodorescu to $(B,X,Y)$. If it rejects, no required group isomorphisms exist. If it returns an isomorphism, normalize its anchor and decode using (6). This proves decision and search, including the binary-encoded-kernel assertion. The published module algorithm handles finite rings without a field hypothesis and without a prime-size factor in its polynomial bound. [Ciocănea-Teodorescu, Theorem 1.1](https://arxiv.org/abs/1512.08365).

## 6. Entire cosets without computing ring unit groups

For Cayley tables let $\Omega$ be the disjoint union of the elements of all source vertex groups. Its size is polynomial in the input. First obtain a particular isomorphism to the target diagram, or reject. The remaining solutions form its coset under the source diagram automorphism group fixing all source marks.

Compute that automorphism group by a base-and-orbit procedure. Order $\Omega$. At stage $j$, fix all previous points, and for each possible image $y$ of the next point $x$, call the marked version of the decision-and-search algorithm with the extra requirement $x\mapsto y$. Points can map only within their own vertex group. Retain a witness for every achievable image.

These witnesses are an orbit transversal for the current point stabilizer. After every point is fixed the residual group is trivial. Induction up the stabilizer chain shows that the union of the retained witnesses generates the full diagram automorphism group: any automorphism can be multiplied by the inverse of a matching transversal element to fix the next point. The product of the successive orbit sizes is its order. Thus at most $|\Omega|^2$ calls give generators, the exact order, and the full solution coset.

This is a polynomial-time use of marked searches in the original Cayley-table size. It does not enumerate the much larger compiled modules and does not call a finite-ring unit-group algorithm. The usual generating-set compression by permutation stabilizer chains is optional.

## 7. Consequences for Grochow and Qiao

**Corollary 2.** Let $S(G)$ be any polynomial-time-computable characteristic abelian subgroup. If quotient isomorphisms $G/S(G)\to H/S(H)$ can be listed in time $t(n)$, then isomorphism, witnesses, the entire coset, and exact counts for $G,H$ can be computed in time $t(n)n^{O(1)}$.

Apply Theorem 1 to every listed quotient map. The solution fibers are disjoint, so their counts add. To generate all automorphisms, apply this to a group against itself, retain one representative over each liftable quotient map, and adjoin the kernel generators over the quotient identity. Every automorphism is a retained representative times a kernel element.

This is Theorem 6.11 with arbitrary characteristic abelian kernels, rather than elementary abelian kernels. In particular it supplies the first requested extension in Open Problem 8.1. The known enumeration bounds for the quotient by the solvable radical then give $n^{c\log_2\log_2 n+O(1)}$ time for arbitrary abelian radicals, with $c=1/\log_2 60$, and polynomial time when the radical quotient has $O(\log n/\log\log n)$ minimal normal subgroups, for a fixed implied constant. These quotient bounds are the existing ingredients in Grochow–Qiao Theorems 5.5–5.6. [Grochow–Qiao](https://opus.lib.uts.edu.au/rest/bitstreams/0a860f36-47a1-4392-adef-100a1cc03886/retrieve).

The algorithm also gives simultaneous compatibility for many extension problems sharing data through arrows. Solving the extensions independently would not ensure that the chosen isomorphisms commute; the single compiled module enforces those conditions together.

The supplied quotient maps remain essential. An unknown automorphism of $Q$ permutes the labels $d_q$ and twists the action labels. Fixing their coordinates by the anchor does not search over those possibilities. Consequently neither general Group Isomorphism nor unrestricted TI versus SL-TI follows from this proof.

## 8. Attribution and novelty scope

The source of the question and the action/cohomology framework is Grochow–Qiao. Gruenberg's translation functor is classical; Atsuta–Kataoka give a precise modern account. Finite-module isomorphism is the algorithm of Ciocănea-Teodorescu. The generator-bound question is explicitly present in Skresanov's 2026 paper. Stabilizer-chain recovery from marked searches is standard.

The result here combines those ingredients with the explicit common scalar anchor, the polynomial-size generated-ring construction, and the diagram encoding. It gives a separate proof of the recent abelian-kernel lifting result in this collection and extends its scope to simultaneous diagrams and binary-encoded kernels. The cited papers do not supply this complete construction. A targeted literature search is not a guarantee of priority; the appropriate external claim is an informal proof submitted for expert assessment, with the exact first-part versus full-question distinction above.
