# Arithmetic profiles in bounded degree

Fix a number field $K$. A probe is a finite extension $E/K$, with $K$-embeddings as arrows. The integral profile of a family $X_e$ at $E$ is the language $\{e:X_e(\mathcal O_E)\ne\varnothing\}$. A simultaneous profile on an effectively presented list $(E_i)$ is uniformly computably enumerable (c.e.) when the set of pairs $(e,i)$ for positive tests is c.e. It is monotone when its positives persist along embeddings.

The results below are unconditional mathematical proofs. They concern integral points and their transport under embeddings. The smoothing also controls every completion. The earlier finite-probe construction preserves both bounded-degree field and integral points. [Simultaneous computability](https://github.com/Dugongue/MathProofs/blob/7724fc270f13b7c3f174b60b16b8901c0f84433f/FourFieldProposals/SimultaneousComputability.md) · [Arithmetic traces](https://github.com/Dugongue/MathProofs/blob/0d5a4dcb98b86d977e6d7363cf612744d675b5a8/FourResearchPrograms/ArithmeticTraces.md)

## 1. Effective integral trace smoothing

**Theorem 1.** Given $K$, $D\ge1$, and $r$ polynomials $f_i\in\mathcal O_K[x_1,\ldots,x_n]$ of degree at most $b$, there is an effective hypersurface $H$ over $\mathcal O_K$ in $n+2$ variables with the following properties.

- $H$ is a principal open of affine $(n+1)$-space over $\mathcal O_K$, hence smooth with geometrically integral rational fibers at every prime and over $K$.
- Projection to the first $n$ coordinates gives a bijection
  $$
  H(\mathcal O_E)\ \longrightarrow\ \{x\in\mathcal O_E^n:f_1(x)=\cdots=f_r(x)=0\}
  \qquad([E:K]\le D).
  $$
  The inverse adjoins the same two coordinates $(0,1)$ over every such extension, so the bijections commute with all probe embeddings.
- Over every finite extension $E/K$, every $x\in\mathcal O_{E_w}^n$ at any finite place $w$ lifts to an integral point of $H$. Every $x\in E_w^n$ lifts to a point at every infinite place. Over any infinite field extending $K$, every $x$ lifts to an ordinary field point.
- If $s$ is any prime greater than $\max(D,r)$, then the defining equation has degree at most $1+sD[K: \mathbb Q]\max(1,b)$.

*Proof.* Choose a rational prime $\pi$ unramified in $K$, so $T^s-\pi$ is Eisenstein at each prime of $K$ above $\pi$. Let $\alpha^s=\pi$ and put
$$
 G(x,u)=\operatorname{Nm}_{K(\alpha)/K}\!\left(u+\sum_{i=1}^r\alpha^i f_i(x)\right).
$$
Its coefficients are in $\mathcal O_K$ by integrality and Galois invariance, it is monic of degree $s$ in $u$, and its total degree is at most $s\max(1,b)$. For $[E:K]\le D$, the integer $[E(\alpha):K]$ is divisible by $s$ and $[E:K]$ is coprime to $s$. The bound $[E(\alpha):E]\le s$ gives equality. Thus the displayed norm becomes the field norm over $E$, and $G(x,u)=0$ holds exactly when $u=f_1(x)=\cdots=f_r(x)=0$.

Set $M=D[K: \mathbb Q]$, $q=(sM+1)!$, and
$$
 P(x,u)=\prod_{j=1}^{M}(1+jqG(x,u)),\qquad H\colon wP(x,u)=1.
$$
Projection onto $(x,u)$ identifies $H$ with the principal open $D(P)$. In each residue field any factor of $P$ is either $1$ or has degree $s$ in $u$ and nonzero leading coefficient. Its product is nonzero, so every fiber is a nonempty principal open of affine space. This also proves the claimed total degree bound.

For $(x,u,w)\in H(\mathcal O_E)$, each $1+jqG(x,u)$ is a unit. With $g=G(x,u)$, the integral polynomial
$$
 N(Z)=\operatorname{Nm}_{E/\mathbb Q}(1+Zqg)
$$
has degree at most $M$, satisfies $N(0)=1$, and at $j=1,\ldots,M$ takes the value $+1$ or $-1$. Since $N(Z)\equiv1\bmod q$, each such value is $+1$. Interpolation now gives $N(Z)=1$. If $g\ne0$, its leading coefficient in degree $[E: \mathbb Q]$ is $\operatorname{Nm}_{E/\mathbb Q}(qg)\ne0$. Thus $g=0$, whence the input is an old solution and $u=0,w=1$. These extra coordinates also give a lift of every old solution.

Fix $x$ over a finite completion and consider the polynomial $P(x,u)$ over its residue field. When the residue characteristic divides $q$, the polynomial is $1$. Otherwise, the residue field has size greater than $sM$ and the polynomial is nonzero of degree at most $sM$. Choose a residue $u$ where it is nonzero, lift the residue and take $w=P^{-1}$. At infinite places, and over any infinite field extending $K$, the same nonzero polynomial in one variable has a nonroot and its value can be inverted. All choices in the construction of the equation are effective. $\square$

This construction can be applied to equations with a parameter $e$ kept as a distinguished variable. It produces one polynomial template, with identical degree and dimension bounds for all specializations. The multiplier $q$ has bit length $O(sM\log(sM))$, and $s$ can be chosen of order $D+r+1$. The open immersion gives raw field points over every infinite $K$-field. The distinction between the constrained integral test and the raw field test is therefore essential.

**Corollary 1.1 (unbounded totally real smoothing).** If $K$ is totally real, one can preserve the same exact integral witnesses on *every* totally real algebraic extension $E/K$, including infinite extensions, with one equation of degree at most $1+2\max(1,b)$. All the local lifting and geometric assertions of Theorem 1 still hold.

*Proof.* Use
$$
 w\bigl(1+6G(x,u)\bigr)=1,\qquad G(x,u)=u^2+\sum_{i=1}^r f_i(x)^2.
$$
For a finite totally real $E$, $1+6G$ is a unit and all its conjugates are real and at least one. Their product is a positive integer unit, hence one. Every conjugate equals one, so the sum of squares vanishes and each $f_i(x)$ and $u$ is zero. In an infinite totally real extension, every integral solution, including $w$, is defined over a finite totally real subextension. The converse lift is again $(0,1)$. The equation is a principal open and its defining open polynomial in $u$ is either one modulo residue characteristic $2$ or $3$, or has degree two in a residue field of size at least five. This proves the same local lifting statement. $\square$

## 2. Exact isolation and least extension degree

**Theorem 2.** Fix $K,D$ and finitely many pairwise $K$-nonisomorphic extensions $L_i/K$ with $D/2<[L_i:K]\le D$. Assign any c.e. language $A_i$ to each $L_i$. There is a fixed hypersurface template of the form in Theorem 1 giving, for every $[E:K]\le D$,
$$
 H_e(\mathcal O_E)\ne\varnothing
 \quad\Longleftrightarrow\quad
 E\cong_K L_i\text{ and }e\in A_i\text{ for some }i.
$$
The same statement includes the case of any finite set of extensions all of degree $D$.

*Proof.* Choose a finite Galois extension $B/\mathbb Q$ containing all $L_i$ as well as $K$. The theorem of Koymans and Pagano supplies an existential polynomial definition of $\mathbb Z$ in $\mathcal O_B$. Expand all its equations in an integral basis of $\mathcal O_B$, using its integer multiplication table. Over any $\mathcal O_{L_i}$, the expanded formula is evaluation of the original formula in $\mathcal O_B\otimes_{\mathbb Z}\mathcal O_{L_i}$, with the tested element $t$ interpreted as $1\otimes t$. A solution descends under the multiplication homomorphism to $\mathcal O_B$ and implies $t\in\mathbb Z$. Conversely, when $t\in\mathbb Z$, witnesses in $\mathcal O_B\otimes 1$ give the expanded solution. This is one common formula with integer coefficients for all selected fields. [Koymans–Pagano, Theorem 1.2](https://arxiv.org/html/2412.01768v3#S1.SS2)

In branch $i$, require a root of the monic minimal polynomial over $K$ of an integral primitive generator of $L_i$. Independently require a Matiyasevich–Robinson–Davis–Putnam representation of $A_i$, constraining each arithmetic witness by the common formula. The finite disjunction is an existential system of equations. For example, a selector $z$ is constrained by $\prod_i(z-i)=0$, and each equation of branch $i$ is multiplied by $\prod_{j\ne i}(z-j)$. A branch can be satisfied over $E$ only if $L_i$ embeds in $E$. Since $[L_i:K]>D/2$, divisibility and the cutoff force $E\cong_K L_i$. On that field the integer definition and MRDP equivalence give the exact acceptance condition. Apply Theorem 1. The empty list is handled by smoothing the inconsistent equation $1=0$. $\square$

The argument uses the existence theorem for the finite common integer formula. Given such a formula, all steps that produce the polynomial template from MRDP equations and the selected fields are effective.

For a probe cutoff $D$, the **truncated least integral extension degree** is
$$
 d_{H,D}(e)=\min\{[E:K]:[E:K]\le D,\ H_e(\mathcal O_E)\ne\varnothing\},
$$
with minimum of the empty set equal to $\infty$.

**Corollary 3.** Let $\delta:\mathbb N\to\{\lfloor D/2\rfloor+1,\ldots,D\}\cup\{\infty\}$. There is a family as in Theorem 1 with $d_{H,D}=\delta$ exactly when each lower cut $\{e: \delta(e)\le d\}$ is c.e. One field type $L_d$ can be selected in advance at every allowed degree $d$, and all other fields of degree at most $D$ can be made negative at every input.

*Proof.* For each $d$ in the range choose $L_d=K(\sqrt[d]{\pi_d})$ with $\pi_d$ rational and unramified in $K$. The polynomial is Eisenstein, so its degree is exactly $d$. Different degrees give nonisomorphic fields and the cutoff ensures that none embeds in another. Use the lower cut at $d$ as $A_d$. The smallest accepted $d$ is exactly $\delta(e)$. Conversely, finite extensions of bounded degree and their rings of integers can be effectively enumerated by monic irreducible polynomials and integral bases. Dovetail their tuples and check the equations to enumerate every lower cut. $\square$

## 3. Countable probe categories with a uniform integer formula

Say a class of bounded-degree probes has a **uniform integer formula** if one finite existential system with coefficients in $\mathcal O_K$ defines $\mathbb Z$ in $\mathcal O_E$ for each probe $E$ in the class. Say the list of probes is effective if one can compute a monic integral primitive polynomial for each $E_i/K$ from $i$.

**Theorem 4.** On any effective class of probes of bounded degree with a uniform integer formula, the profiles of computable families of integral polynomial systems are exactly the uniformly c.e. monotone profiles. Every such profile is realized by one hypersurface template as in Theorem 1.

*Proof.* Necessity follows by enumeration of integral tuples and by transport along embeddings. For sufficiency, take a uniformly c.e. monotone profile $R(e,i)$. Represent the coefficients of a monic integral primitive polynomial $g_i(T)$ in a fixed integral basis of $K$. Pad the list by zero coefficients to the common degree bound. The relation on $(e,i,\mathbf a)$ saying $R(e,i)$ holds and $\mathbf a$ is the coefficient tuple of $g_i$ is c.e. Encode it by MRDP. Constrain all the resulting arithmetic unknowns, including $i,\mathbf a$, by the uniform integer formula. Add $\sum_{h=0}^{D}a_h T^h=0$, where the $a_h$ are the $\mathcal O_K$-linear combinations of the integer coordinates in $\mathbf a$. Over $E_j$, solutions exist exactly when some $E_i$ with $R(e,i)$ embeds into $E_j$. Monotonicity and the identity embedding give equivalence to $R(e,j)$. Theorem 1 finishes the construction. $\square$

This also gives one template for the profile index as well as the input. Apply MRDP to a universal c.e. relation whose distinguished additional integer parameter is an enumeration program. For each program enumerating a monotone profile, the same hypersurface template realizes that profile upon specialization. For any program whatsoever the formula realizes the upward closure of its enumerated relation.

## 4. Exact classification on imaginary quadratic probes

The following short uniform integer definition is adapted from the use of CM units and Pell congruences by Mazur, Rubin and Shlapentokh. The proof here uses one fixed real quadratic auxiliary field and an explicit modulus. [Mazur–Rubin–Shlapentokh, Lemma 4.1 and Remark 4.7](https://arxiv.org/html/2303.02521#S4)

**Lemma 5.** One finite system of existential polynomial equations over $\mathbb Z$ defines $\mathbb Z$ in $\mathcal O_F$ for every imaginary quadratic field $F$. On every integer input the system has witnesses in $\mathbb Z$.

*Proof.* Put $M_0=\mathbb Q(\sqrt3)$, $L=FM_0$ and $A=\mathcal O_F[\sqrt3]$. Work with coefficient pairs over $\mathcal O_F$ in $A$. Existentially require $\delta_1,\delta_2$ to be units of $A$, using inverse pairs, and put $\varepsilon_i=\delta_i^{120}$. If $c$ denotes complex conjugation in the CM field $L$, each conjugate of $\delta_i/c(\delta_i)$ has modulus one. This quotient is an algebraic integer since both factors are units. Kronecker's theorem makes it a root of unity. Every root-of-unity order in a number field of degree at most four divides $120$, because the possible orders $h$ have $\varphi(h)\le4$. Consequently $c(\varepsilon_i)=\varepsilon_i$, so $\varepsilon_i\in\mathcal O_{M_0}=\mathbb Z[\sqrt3]$.

Accept $w=0,1,2,3$ in four explicit branches. In the remaining branch put $D(w)=w(w-1)(w-2)(w-3)$ and require
$$
 \varepsilon_1\ne1,\qquad
 \varepsilon_1-1\in D(w)A,\qquad
 \varepsilon_2-1-w(\varepsilon_1-1)\in(\varepsilon_1-1)^2 A .
$$
Divisibility is expressed by existential coefficient pairs. For the disequality, if $\varepsilon_1=u_1+v_1\sqrt3$, impose $(u_1-1)^2+3v_1^2\ne0$. In the ring of integers of any number field, one can express $z\ne0$ as $\exists a,b\, zb=(2a+1)(3a+1)$. Indeed, for $z\ne0$, put $m=|\operatorname{Nm}_{F/\mathbb Q}z|$. For each prime power dividing $m$, at least one of $2,3$ is a unit, so CRT gives an integer $a$ making the product divisible by $m$. The integer $m$ is a multiple of $z$ in $\mathcal O_F$, by the constant coefficient identity in the characteristic polynomial of multiplication by $z$. For $z=0$, a witness would give an integral rational root $-1/2$ or $-1/3$, which is impossible. This argument gives integer witnesses for nonzero $z\in\mathbb Z$. The nonzero element $\varepsilon_1-1$ in the chosen branch also implies $D(w)\ne0$. [Sun, Lemma 2.1, for the predicate over $\mathbb Z$](https://arxiv.org/html/2608.03992v1#S2)

To prove soundness, write $\mathcal O_F=\mathbb Z+\mathbb Z\omega$ and $w=a+b\omega$. Division of the last congruence by $\varepsilon_1-1$ shows that $(\varepsilon_2-1)/(\varepsilon_1-1)$ is in $A\cap M_0=\mathcal O_{M_0}$. Since $A=\mathcal O_{M_0}+\mathcal O_{M_0}\omega$ with unique coordinates, comparison of the $\omega$ coefficient after division gives $b\in(\varepsilon_1-1)\mathcal O_{M_0}$. Thus $b/D(w)\in A\cap F=\mathcal O_F$.

For $b\ne0$, one has $|\operatorname{Im}\omega|\ge\sqrt3/2$. If $|b|\ge2$, each of the four factors of $D(w)$ has modulus at least $\sqrt3|b|/2$, so $|D(w)|>|b|$. If $|b|=1$, at least one of the distances from $\operatorname{Re}w$ to $0,1,2,3$ is at least $3/2$. Its factor has modulus at least $\sqrt3$, and the other factors have modulus at least $\sqrt3/2$, giving $|D(w)|\ge 9/8>1$. In both cases $b/D(w)$ would be a nonzero imaginary-quadratic integer of modulus less than one, which contradicts its positive integer norm. Thus $b=0$ and $w\in\mathbb Z$.

For completeness on $w\in\mathbb Z$ with $D(w)\ne0$, take $\delta_1$ to be a positive power of $2+\sqrt3$ congruent to $1$ modulo $D(w)\mathcal O_{M_0}$, which exists by finiteness of the residue ring. Take $\delta_2=\delta_1^w$, using the unit inverse for negative $w$. The identity $u^w\equiv1+w(u-1)\bmod (u-1)^2$ holds for units $u$ and all integer $w$, and $\varepsilon_1\ne1$. Every congruence witness belongs to $\mathbb Z[\sqrt3]$, so its coefficient pairs are in $\mathbb Z$. $\square$

**Theorem 6.** Index all imaginary quadratic fields without repetition by $F_d=\mathbb Q(\sqrt{-d})$, where $d\ge1$ is squarefree. For every c.e. set of pairs $R(e,d)$ on these indices, there is one computable hypersurface template as in Theorem 1 such that
$$
 H_e(\mathcal O_{F_d})\ne\varnothing\ \Longleftrightarrow\ R(e,d).
$$
For $E=\mathbb Q$ and every real quadratic $E$, $H_e(\mathcal O_E)=\varnothing$ for all inputs. Conversely, all computable families of integral polynomial systems have c.e. profiles on the imaginary quadratic fields.

*Proof.* Use Lemma 5 to constrain the MRDP witnesses and the label $d$ for the c.e. relation $R$. In addition to $t^2=-d$, require $t^2+1+\sum_{h=1}^4 v_h^2=0$. In $F_d$ the first equation isolates its label, and the second is soluble by the four-square theorem applied to $d-1$. Over a field with a real embedding, the second equation is impossible independently of the behavior of the integer formula there. Apply Theorem 1 with $D=2$. The converse is direct enumeration. $\square$

## 5. Exact classification on the entire quadratic antichain

**Lemma 7.** There is one finite existential polynomial system $\Phi_{\rm R}(w)$ over $\mathbb Z$ defining $\mathbb Z$ in the ring of integers of every real quadratic field. It has no positive tests in $\mathbb Q$ or in any imaginary quadratic field.

*Proof.* Require units $u_i$ using inverse witnesses, and write $\delta_i=u_i^{12}$ and $T_i=\delta_i+\delta_i^{-1}-2$. In a real quadratic field the conjugate of $\delta_i$ is its inverse, since $\operatorname{Nm}(\delta_i)=1$. Thus each $T_i$ is an integer. All units in the imaginary quadratic fields and in $\mathbb Q$ have order dividing $12$. The condition $T_1\ne0$, expressed using the disequality predicate in Lemma 5, therefore excludes those probes.

Under $T_1\ne0$, accept $w=0,1,2,3$ in four explicit branches. In the remaining branch require
$$
 D(w)=4\prod_{k=0}^3(w-k),\qquad
 T_1\in D(w)\mathcal O_F,\qquad
 T_2\equiv w^2T_1\bmod T_1^2,\qquad
 T_3\equiv(w+1)^2T_1\bmod T_1^2 .
$$
Dividing the two congruences by $T_1$ shows that the rational numbers $T_i/T_1$ are integral, hence integers. Write $w=a+b\omega$ in an integral basis $1,\omega$ of $F$. The $\omega$-coefficients of $w^2$ and $(w+1)^2$ are both multiples of $T_1$ in $\mathbb Z$. Subtracting gives $2b\in T_1\mathbb Z$, so $2b/D(w)\in\mathcal O_F$.

Suppose $b\ne0$, and write $w'$ for the real conjugate of $w$. Then $\Delta=|w-w'|\ge\sqrt5|b|$, because the discriminant of a real quadratic field is at least $5$. Each of $w,w'$ is at distance less than $1/2$ from at most one shift $k$ in $\{0,1,2,3\}$. At least two shifts therefore have both distances at least $1/2$. For each such shift the larger distance is at least $\Delta/2$, giving $|\operatorname{Nm}(w-k)|\ge\Delta/4$. For the remaining factors, nonzero integral norms have absolute value at least one. It follows that $|\operatorname{Nm}D(w)|\ge16(\Delta/4)^2\ge5b^2$. The nonzero algebraic integer $2b/D(w)$ would then have absolute norm at most $4/5$, a contradiction.

For any $w\in\mathbb Z$ with $D(w)\ne0$, take $u_1$ to be a positive power of an infinite-order unit reducing to one modulo $D(w)\mathcal O_F$, so $D(w)\mid T_1$. Here $T_1\ne0$ since $\delta_1\ne1$. Take $u_2=u_1^w,u_3=u_1^{w+1}$. The polynomial identity
$$
 z^m+z^{-m}-2\ \equiv\ m^2(z+z^{-1}-2)\pmod{(z+z^{-1}-2)^2}
$$
holds in $\mathbb Z[z,z^{-1}]$ for every integer $m$. Indeed, writing $S_m=z^m+z^{-m}$ and $T=z+z^{-1}-2$, the recursion $S_{m+1}=(2+T)S_m-S_{m-1}$ with $S_0=2,S_1=2+T$ gives constant coefficient $2$ and linear coefficient $m^2$ in $T$, and $S_{-m}=S_m$. This gives the required congruences. The four exceptional integers only require an infinite-order unit. $\square$

**Theorem 8.** On the set of all quadratic number fields, every uniformly c.e. profile is realized by one computable hypersurface template as in Theorem 1 with $K=\mathbb Q,D=2$. All integral tests at $\mathbb Q$ can be made negative. Conversely, every integral profile of a computable family on the quadratic fields is uniformly c.e.

*Proof.* The equation $s^2+1+\sum_{h=1}^4 v_h^2=0$ has integral witnesses in every imaginary quadratic field by the four-square argument in Theorem 6. It cannot hold over a field with a real embedding. Disjoin $\Phi_{\rm R}(w)$ with the conjunction of this test and the predicate of Lemma 5. This gives one uniform integer formula on all quadratic fields and a predicate empty over $\mathbb Q$. They form a computable antichain of probes up to isomorphism. Apply Theorem 4 with this integer formula, including it also on the witness for the integer index of the probe. Thus the input system is unsatisfiable at $\mathbb Q$. Theorem 1 preserves this exact test. The converse again follows by enumeration. $\square$

## 6. A subclass with a prescribed base-field profile

**Corollary 9.** Let $\mathcal P$ be the set consisting of every imaginary quadratic field and every $\mathbb Q(\sqrt{5p})$ for a prime $p\equiv3\bmod8$. Every uniformly c.e. monotone profile on $\mathcal P\cup\{\mathbb Q\}$ is realized by one hypersurface template as in Theorem 1 with $K=\mathbb Q,D=2$.

*Proof.* Use the elliptic curve $A:y^2=x^3-25x$. The point $(-4,6)$ has infinite order because its double has nonintegral $x$-coordinate $1681/144$, so the Nagell–Lutz theorem precludes torsion. In the quadratic extension associated to $5p$, the rank equals the sum of the ranks of $A$ and its quadratic twist, via the two rational eigenspaces of conjugation on the Mordell–Weil group tensored with $\mathbb Q$. The twist is isomorphic over $\mathbb Q$ to $y^2=x^3-p^2x$. For example, the coefficient of $x$ in the twist is $-(25p)^2=-625p^2$, which is transformed to $-p^2$ by scaling $x$ by $5^2$ and $y$ by $5^3$. The twist has rank zero for $p\equiv3\bmod8$. Hence these real quadratic fields all have rank stability for the same positive-rank curve $A$. [Evink–Top–Top, Proposition 2.3 and Corollary 2.4](https://pure.rug.nl/ws/portalfiles/portal/573891781/A_remark_on_prime_non_congruent_numbers.pdf)

The uniform Diophantine definition of Mazur, Rubin and Shlapentokh applies to every one of these real quadratic fields, with witnesses in $\mathbb Z$ for integer inputs. Conjoin it with Lemma 5. The conjunction defines $\mathbb Z$ in every probe in $\mathcal P$, because the relevant one of the two conjuncts is sound and both have integer witnesses on all integers. The same conjunction also defines $\mathbb Z$ at the probe $\mathbb Q$, because both formulas have integer witnesses there and the ambient ring already equals $\mathbb Z$. Apply Theorem 4 to this enlarged class. [Mazur–Rubin–Shlapentokh, Theorem 3.1 and Remarks 3.2, 3.6](https://arxiv.org/html/2208.09963#S3) $\square$

**Corollary 10.** For every fixed imaginary quadratic field $K$, every uniformly c.e. profile on all quadratic extensions of $K$ is realized by one hypersurface template as in Theorem 1 over $\mathcal O_K$. The integral test at $K$ itself is always negative.

*Proof.* Fix a quadratic extension $F/K$, with nonidentity $K$-automorphism denoted $w\mapsto w'$. The group $\mathcal O_K^\times$ has exponent dividing $12$. Thus for any unit $u\in\mathcal O_F^\times$, $\delta=u^{12}$ has relative norm one and $T=\delta+\delta^{-1}-2\in\mathcal O_K$. The field $F$ has two complex conjugate pairs and no real embeddings, so its unit rank is one. The base $K$ has unit rank zero.

Use the equations of Lemma 7 with $D(w)=9\prod_{k=0}^3(w-k)$, retaining the requirement $T_1\ne0$ in every branch. The integer inputs still have witnesses by the same unit power argument. At $K$ the $T_1\ne0$ requirement is impossible. To check soundness at $F$ outside the four exceptional integer inputs, divide and subtract the two congruences to obtain $2w+1\equiv c\bmod T_1\mathcal O_F$ for $c\in\mathcal O_K$. Indeed the divided ratios lie in $K\cap\mathcal O_F=\mathcal O_K$. Subtract the $K$-conjugate congruence and use $D(w)\mid T_1$ to conclude $2(w-w')/D(w)\in\mathcal O_F$.

Choose a complex embedding of $K$ and its two extensions $\sigma_1,\sigma_2$ to $F$. The other two embeddings of $F$ are their complex conjugates. For $\Delta=|\sigma_1(w)-\sigma_2(w)|>0$, all four conjugates of $w-w'$ therefore have modulus $\Delta$. At least two of $k=0,1,2,3$ satisfy $|\sigma_i(w)-k|\ge 1/2$ for both $i=1,2$. For each of these two shifts the larger distance is at least $\Delta/2$, so $|\operatorname{Nm}_{F/\mathbb Q}(w-k)|=(|\sigma_1(w)-k||\sigma_2(w)-k|)^2\ge(\Delta/4)^2$. Every other factor has absolute norm at least one. Consequently
$$
 |\operatorname{Nm}_{F/\mathbb Q}D(w)|\ge 9^4\Delta^4/256
 > 16\Delta^4=|\operatorname{Nm}_{F/\mathbb Q}(2(w-w'))|.
$$
This would make $2(w-w')/D(w)$ a nonzero integral element of absolute norm less than one. Thus $w=w'$ and $w\in\mathcal O_K$.

To define $\mathbb Z$ uniformly over these $F$, take the formula of Lemma 5 with the new predicate imposed on its input and on every witness variable. Soundness forces all those variables into $\mathcal O_K$, where Lemma 5 holds. Completeness follows because Lemma 5 has integer witnesses and the new predicate accepts every integer over $F$. Apply Theorem 4 over $K$. Its integer test is empty at $K$, so the template remains negative there. $\square$

## 7. Questions and comparison

1. **All quadratic probes.** Is every uniformly c.e. monotone relation on the poset of all extensions $E/\mathbb Q$ of degree at most two the integral profile of one computable hypersurface template as in Theorem 1? Theorem 8 resolves all profiles with empty base-field language. Corollary 9 allows an arbitrary c.e. base-field language subject to monotonicity on the indicated countable subposet. A uniform $\mathbb Z$-definition over all real quadratic rings with integer witnesses would suffice for the full question, by conjunction with Lemma 5 and Theorem 4.
2. **Arbitrary fixed cutoff.** For every number field $K$ and $D$, is the c.e.-monotone condition sufficient on the category of all actual extensions of degree at most $D$? Theorem 4 reduces this to a uniform integer formula on that class and leaves open arithmetic constructions that bypass such a formula.
3. **Simultaneous field and integral smoothing.** Is there a uniform effective version of the earlier theorem preserving *both* exact field and integral witnesses up to a supplied cutoff, with explicit dimension and degree bounds, and with generic fiber of bounded genus in a suitable fibration? Theorem 1 replaces the earlier use of high-genus scarcity for the integral component by a polynomial unit test. Its principal-open model has abundant field points.

The cited arithmetic sources provide individual or uniform Diophantine definitions and the underlying rank calculation. The profile statements here use requested languages as independent data, check all off-target fields when isolation is asserted, and keep the local tests fixed. The earlier finite arithmetic-trace theorem and Poonen's smoothing construction provide comparative precedents for smoothing. Publication priority for the norm interpolation and the profile constructions remains unestablished. [Poonen, Lemma 4.1](https://math.mit.edu/~poonen/papers/automorphism.pdf#page=3)
