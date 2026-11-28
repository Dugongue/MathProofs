# Taylor operations on finite Postnikov pieces

Let $W$ be a pointed connected CW complex with finitely generated homotopy groups and only finitely many nonzero homotopy groups. A **normalized Taylor operation** on $W$ is a map $t:W^a\to W$ with $t\Delta_a\simeq\mathrm{id}_W$, together with, for every position $i$, an identity up to free homotopy between two minors of $t$ specified by words in $\{x,y\}^a$ that differ at $i$.

**Theorem.** Under these hypotheses, $W$ admits a normalized Taylor operation if and only if it has a multiplication with a pointed homotopy unit. This is a written proof using the local-to-global theorem in [Local H-structures on finite Postnikov pieces](LC/LC_FullProof.md), Theorem 1.1.

## Taylor identities imply simplicity

A homotopy at the basepoint allows us to replace $t$ by a pointed map. Free homotopies between the resulting pointed maps induce conjugate homomorphisms on the fundamental group. On higher homotopy groups they differ by the action of a single element of the fundamental group.

Put $G=\pi_1W$. Let $\phi_i:G\to G$ be induced by the $i$th axis of $t$ and $H_i=\phi_i(G)$. The $H_i$ commute pairwise for distinct indices, since $t_*$ is a homomorphism out of the direct product. The product map $g\mapsto\prod_i\phi_i(g)$ is an inner automorphism by diagonal normalization. Consequently the $H_i$ generate $G$, and each $H_i$ is normal since it is normalized by itself and centralized by all the others.

Use the Taylor identity at position $i$, with $x$ on the left there and $y$ on the right. Restrict the identity to $(x,*)$. The left side on $G$ is the product of the $\phi_j$ indexed by a set $A$ containing $i$, and the right side is the corresponding product indexed by a set $B$ omitting $i$. These two homomorphisms are conjugate. The product over $B$ centralizes $H_i$, and this remains true after conjugation because $H_i$ is normal. The factors on the left with $j\ne i$ already centralize $H_i$. It follows that $H_i$ is abelian. This holds for every $i$, so $G$ is abelian. Normalization now says that $g=\sum_j\phi_j(g)$ in additive notation.

For $n\ge 2$, let $T_j$ be the axis endomorphism of $\pi_nW$ and write $\rho$ for the fundamental-group action. Naturality of this action gives $\rho(\phi_i(g))T_j=T_j$ if $i\ne j$, since the $i$th copy of $G$ acts trivially on the $j$th summand of $\pi_n(W^a)$. The same Taylor identity gives $\sum_{j\in A}T_j=\rho(c)\sum_{j\in B}T_j$ for some $c\in G$. Since $G$ is abelian, $\rho(\phi_i(g))$ commutes with $\rho(c)$, fixes the right side, and fixes all terms on the left except possibly $T_i$. It therefore fixes $T_i$ as well. As the $H_i$ generate $G$, all $T_j$ have images fixed by $G$. Diagonal normalization says that $\sum_j T_j$ is the action of an element of $G$, in particular surjective. Hence $G$ acts trivially on $\pi_nW$ and $\sum_jT_j$ is the identity. This proves simplicity and shows that the linearizations of the free homotopy identities are exact identities on homotopy groups.

## Taylor identities give each prime-local multiplication

Fix a prime $p$ and write $U=W_{(p)}$. Localization preserves the finite products of the nilpotent space $W$, so the pointed operation localizes to $U$. The linearized identities carry over to the localized homotopy groups. The graded direct sum $M=\bigoplus_n\pi_nU$ is a finitely generated module over $\mathbb Z_{(p)}$. The induced operation has the linear form $\sum_i A_i x_i$ on $M$, where each $A_i$ is the direct sum of the axis endomorphisms. Products on homotopy groups identify all the normalized Taylor identities with linear identities, so reducing modulo $p$ gives a finite idempotent Taylor algebra on $M/pM$.

Take a prime $q>\max(p,|M/pM|)$. The finite cyclic-term theorem of Barto and Kozik gives a $q$-ary cyclic term in this algebra. Evaluated in the localized topological operation, it gives a pointed map $c:U^q\to U$. The coefficient maps of its induced operation on $M/pM$ are all equal by cyclicity, and their sum is the identity by idempotence. Every coefficient is therefore $q^{-1}$ times the identity modulo $p$.

Use the binary minor $b(x,y)=c(x,y,*,\ldots,*)$, where $*$ is the basepoint. Both axis maps of $b$ induce automorphisms on $M/pM$. Nakayama's lemma makes their maps on $M$ surjective, and a surjective endomorphism of a finitely generated module over the Noetherian ring $\mathbb Z_{(p)}$ is injective. The latter follows by stabilization of the ascending chain of kernels of its powers. The axes are thus pointed homotopy equivalences by Whitehead's theorem. Composing $b$ with a pointed homotopy inverse on each separate input gives a multiplication on $U$ with both axes homotopic to the identity.

## Rational invariants and integral gluing

Let $V=W_{\mathbb Q}$. Rationalizing a local multiplication makes $V$ an H-space. We verify that its rational Postnikov invariants vanish, as needed for the gluing theorem.

The first stage of $V$ is $K(\pi_1V,1)$. Suppose $P_{n-1}V$ is a product of rational Eilenberg–Mac Lane spaces in degrees at most $n-1$. The H-space multiplication induces a multiplication $\mu$ on this stage and induces addition on $\pi_nV$ by its unit axiom. Naturality of the principal Postnikov class $k\in H^{n+1}(P_{n-1}V;\pi_nV)$ under the multiplication gives

$$
\mu^*k=\operatorname{pr}_1^*k+\operatorname{pr}_2^*k.
$$

For $s=\mu\Delta$, this says $s^*k=2k$. The rational cohomology of this lower stage is free graded-commutative on generators in degrees at most $n-1$. If $I$ is the positive-degree ideal, the two unit restrictions on $\mu$ imply that $s^*$ acts by $2$ on $I/I^2$ and hence by $2^r$ on $I^r/I^{r+1}$. In degree $n+1$, each coordinate of $k$ under a basis of the finite-dimensional vector space $\pi_nV$ lies in $I^2$. A nonzero coordinate would have a nonzero first class in $I^r/I^{r+1}$ for some $r\ge2$. The two expressions for $s^*k$ would make it an eigenvector of both $2^r$ and $2$, which is impossible over $\mathbb Q$. Thus $k=0$. The stage splits, and induction proves the vanishing in all degrees.

Theorem 1.1 of the local-to-global proof now applies to $W$, since it is simple, has finitely generated homotopy and finite height, has split rational Postnikov tower, and has an H-space multiplication at every prime. It gives an integral H-space multiplication on $W$.

## An H-space gives a normalized Taylor operation

Let $\mu:W\times W\to W$ have a pointed homotopy unit. Its shear map $(u,v)\mapsto(\mu(u,v),v)$ is a homotopy equivalence. Indeed the two axis restrictions induce the identity on every homotopy group and their images commute, including on $\pi_1$. Consequently the shear induces the isomorphism $(a,b)\mapsto(a+b,b)$ on homotopy groups, and Whitehead applies. A pointed homotopy inverse can be written, up to homotopy, as $(w,v)\mapsto(d(w,v),v)$ since the shear preserves the second projection. It gives $\mu(d(w,v),v)\simeq w$ and $d(\mu(u,v),v)\simeq u$. Substituting the basepoint for $u$ shows $d(v,v)\simeq *$. Thus $m(x,y,z)=\mu(d(x,y),z)$ satisfies

$$
m(x,y,y)\simeq x,\qquad m(y,y,z)\simeq z.
$$

In particular $m(x,y,y)\simeq m(y,y,x)$ differs in positions 1 and 3, while $m(x,x,x)\simeq m(x,y,y)$ differs in positions 2 and 3. The operation is normalized and Taylor.

## Siggers identities and the rational version

An H-space also has an idempotent Siggers operation. For the Mal'cev operation $m$ just constructed put $s(x_1,x_2,x_3,x_4)=m(x_3,x_1,x_4)$. The minors $s(a,r,e,a)$ and $s(r,a,r,e)$ are both homotopic to $e$. Conversely the identity between those minors changes the variable at every slot. Substituting two variables for $a,r,e$ separately for each slot supplies the Taylor identities. Idempotence is part of the Siggers hypothesis here.

For a connected rational space of finite Postnikov height whose homotopy groups are rational vector spaces of finite dimension, the same Taylor-to-H-space implication holds without the integral finite-generation hypothesis. Simplicity follows as before. In a fixed basis of the graded rational homotopy groups, clear the finitely many denominators of the axis matrices and work over $\mathbb Z[1/b]$ for their common denominator $b$. Reduce modulo a prime $p$ not dividing $b$. The exact linear identities again give a finite Taylor algebra, and a cyclic term of prime arity larger than $p$ and the carrier size. Two axes of the corresponding topological operation are invertible modulo $p$, hence invertible over $\mathbb Q$. Their pointed Whitehead inverses produce a multiplication on the rational space itself. This argument does not require the integral gluing theorem.

## References

The simplicity argument follows the analysis of free homotopy identities in the virtually nilpotent extension work. The prime-local argument uses the Gemini/Claude cyclic-term approach.

- Libor Barto and Marcin Kozik, *Absorbing Subalgebras, Cyclic Terms, and the Constraint Satisfaction Problem*, Theorem 4.1. [Journal article](https://lmcs.episciences.org/673)
- J. Peter May and Kate Ponto, *More Concise Algebraic Topology*, Lemma 3.4.2, Theorem 6.1.2, Propositions 6.2.3 and 6.7.2. [Author's text](https://www.math.uchicago.edu/~may/PAPERS/116.pdf)
- Allen Hatcher, *Algebraic Topology*, Theorem 4.5. [Author's text](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf)
