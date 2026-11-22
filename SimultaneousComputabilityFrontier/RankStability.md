# Rank-stability covers for quadratic profiles

Consider the probes $\mathbb Q$ and every quadratic number field, with embeddings from $\mathbb Q$ to the quadratic fields. A profile is a uniformly computably enumerable relation on the shared input and the field label, monotone along those embeddings. Real quadratic probes are ordered by the positive squarefree radicand $d$ of $\mathbb Q(\sqrt d)$. The arithmetic-profile construction uses a uniform integer formula that can recover signed squarefree field labels and arithmetic witnesses over these probes.

## 1. A fixed cover of density one

**Theorem 1.** There is a fixed set $\mathcal B$ of real quadratic fields of density zero with the following property. Every uniformly c.e. monotone profile on all probes of degree at most two is realized exactly at $\mathbb Q$, at all imaginary quadratic fields, and at all real quadratic fields outside $\mathcal B$ by one polynomial hypersurface template. All the prescribed positives are realized on the entire probe category. Each hypersurface is smooth over $\mathbb Z$, is a principal open of affine space, and admits integral points above every point of the input coordinate space over every finite completion.

*Proof.* Define $C_a:y^2=x^3-a^2x$. The rational points
$$
 (112/9,980/27)\in C_7(\mathbb Q),\qquad
 (-64/25,8184/125)\in C_{41}(\mathbb Q)
$$
are nontorsion by Nagell–Lutz. Hence both curves have positive rational rank. For a positive squarefree $d$, their rank increments in $\mathbb Q(\sqrt d)$ are the ranks of $C_{\operatorname{sf}(7d)}$ and $C_{\operatorname{sf}(41d)}$, respectively, where $\operatorname{sf}$ denotes the positive squarefree representative. This follows by taking the two eigenspaces of quadratic conjugation.

The function $[n]\mapsto w(C_n)$ on positive squarefree $n$ factors through the $2$-adic square class. Indeed the root number is $+1$ for $n\equiv1,2,3\bmod8$ and $-1$ for $n\equiv5,6,7\bmod8$. The $+1$ classes in $\mathbb Q_2^\times/\mathbb Q_2^{\times2}$ are represented by $1,3,2,10$. Multiplication by the class of $7$ carries this set to its complement, since it carries these representatives to the classes of $7,5,14,6$. The class of $41$ is $1$. Thus, for every $d$, exactly one of these two twists has positive root number. Smith proves that positive-rank congruent-number curves with positive root number are indexed by a density-zero set of positive squarefree integers. Each map $d\mapsto \operatorname{sf}(ad)$ for fixed positive squarefree $a$ is injective on positive squarefree integers, and maps $d\le X$ to $\operatorname{sf}(ad)\le aX$. It follows that the set $\mathcal B$ on which both curves have rank growth has $o(X)$ members of radicand at most $X$. [Birch–Stephens root number formula as used by Tian–Yuan–Zhang](https://web.math.princeton.edu/~shouwu/publications/cn.pdf#page=2) · [Smith, introduction](https://arxiv.org/html/1702.02325v2#S1)

For each of $C_7,C_{41}$, the rank-stability theorem of Mazur, Rubin and Shlapentokh gives a fixed existential integer formula for all real quadratic probes where that curve has no rank growth. Both formulas have rational integer witnesses on every integer input. Conjoin the two with the existential integer formula from the imaginary quadratic Pell construction, which has rational integer witnesses. The conjunction is sound for integer membership at $\mathbb Q$, every imaginary quadratic field, and every real quadratic outside $\mathcal B$, and admits all integers everywhere. [Mazur–Rubin–Shlapentokh, Theorem 3.1 and Remarks 3.2, 3.6](https://arxiv.org/html/2208.09963#S3) · [Mazur–Rubin–Shlapentokh, Lemma 4.1 and Remark 4.6](https://arxiv.org/html/2303.02521#S4)

Let $m$ range over the signed, nonzero squarefree radicands, with $m=1$ labelling $\mathbb Q$. Use MRDP to express the prescribed relation $R(e,m)$. Constrain every arithmetic witness and $m$ by the conjunction above, and add $t^2=m$. An intended positive always has witnesses from the integer solutions to the MRDP equation and any square root of the field label in the chosen probe. At a probe where the integer formulas are sound, the square-root gate identifies that very quadratic field or $\mathbb Q$. Such a $\mathbb Q$-positive is permitted to propagate by monotonicity. Apply effective integral trace smoothing with $K=\mathbb Q$ and $D=2$, using norm interpolation to preserve the integral witnesses. Its coefficients and number of variables are fixed except for the distinguished input parameter. This proves all assertions. $\square$

## 2. Effective finite patches and pointwise finite errors

**Lemma 2.** For a supplied positive squarefree $d>1$, an existential polynomial formula computed from $d$ defines $\mathbb Z$ over $\mathcal O_{\mathbb Q(\sqrt d)}$ with rational integer witnesses. The integer witnesses work in every ring of algebraic integers.

*Proof.* Over a test ring $R$, use formal coefficient pairs in $R[X]/(X^2-d)$. For $i=1,2,3$, require $a_i^2-db_i^2=1$, put $\gamma_i=a_i+b_iX$, and set
$$
 T_i=\gamma_i^2+\gamma_i^{-2}-2=2(a_i^2+db_i^2)-2\in R.
$$
These expressions are polynomial, since $\gamma_i^{-1}=a_i-b_iX$. At $R=\mathcal O_F$ for $F=\mathbb Q(\sqrt d)$, evaluation $X\mapsto\sqrt d$ takes $\gamma_i$ to an actual unit of $\mathcal O_F$. Its square has absolute norm one, and the formal expression for $T_i$ evaluates to the trace of this square minus $2$. Thus $T_i\in\mathbb Z$.

Require $T_1\ne0$, and with this requirement accept $w=0,1,2,3$ in four separate branches. Otherwise put $D(w)=9\prod_{k=0}^3(w-k)$, and require $D(w)\mid T_1$ and
$$
 T_2\equiv w^2T_1\bmod T_1^2,\qquad
 T_3\equiv(w+1)^2T_1\bmod T_1^2.
$$
Nonzero is existentially expressible over any ring of algebraic integers by $\exists p,q\colon T_1q=(2p+1)(3p+1)$. At nonzero $T_1$, use the Chinese remainder theorem modulo its absolute norm, which is a multiple of $T_1$ in the ring of integers. At zero neither rational root $-1/2,-1/3$ is integral. [Sun, Lemma 2.1 for the predicate over the rational integers](https://arxiv.org/html/2608.03992v1#S2)

At $F$ divide both congruences by $T_1$. The quotients $T_i/T_1$ are integral by the congruences and rational by their construction. Subtract the divided congruences and their conjugates to conclude $2(w-w')\in T_1\mathcal O_F$, where $w'$ is the nontrivial conjugate. If $\Delta=|w-w'|>0$, at least two of the shifts $k=0,1,2,3$ have both $|w-k|,|w'-k|\ge1/2$, since either embedding can violate this for at most one shift. For each good shift the larger distance is at least $\Delta/2$, so $|\operatorname{Nm}(w-k)|\ge\Delta/4$. All other factor norms have absolute value at least one. Then $|\operatorname{Nm} D(w)|\ge81\Delta^2/16>4\Delta^2$, whereas $|\operatorname{Nm}(2(w-w'))|=4\Delta^2$. This contradicts the integrality of $2(w-w')/D(w)$. Thus $w=w'\in\mathbb Z$.

For integer inputs, ordinary Pell's equation gives an infinite-order unit of formal norm one with integer coefficients. Take $\gamma_1$ to be a nontrivial power congruent to one modulo $D(w)$ in $\mathbb Z[X]/(X^2-d)$ when $D(w)\ne0$. This ensures $T_1\ne0$ and $D(w)\mid T_1$ in $\mathbb Z$. Then take $\gamma_2=\gamma_1^w,\ \gamma_3=\gamma_1^{w+1}$. The identity
$$
 z^m+z^{-m}-2\equiv m^2(z+z^{-1}-2)\pmod{(z+z^{-1}-2)^2}
$$
holds in $\mathbb Z[z,z^{-1}]$ for every integer $m$, as follows by expanding the Chebyshev recurrence for $z^m+z^{-m}$ at $z+z^{-1}=2$. This gives the required congruences with integer quotients. All variables in all branches admit rational integer witnesses for the intended integer inputs. $\square$

**Corollary 3.** For any finite set $\mathcal T$ of specified real quadratic fields, Theorem 1 can make those tests exact as well, still with one fixed hypersurface template. In the class of computable hypersurface families with variable format, one can simultaneously guarantee every desired positive, exactness at $\mathbb Q$ and all imaginary quadratic fields, and the following two error bounds.

- For each input $e$, the only possible erroneous real quadratic probes belong to $\mathcal B$ and have radicand greater than $e$.
- For each fixed real quadratic probe, its realized and prescribed languages differ on at most finitely many inputs.

*Proof.* Conjoin the integer predicates of Lemma 2 for the selected radicands to the formula in Theorem 1. They all admit integer witnesses, and on each selected field the associated predicate restricts the arithmetic variables to rational integers. For the variable-format family at input $e$, adjoin the formulas for every positive squarefree $d\le e$ with $d>1$. This is a finite effective calculation from $e$. Apply the same integral smoothing uniformly to the resulting finite systems. The only possible errors are false positives on the claimed set of fields and inputs. $\square$

## 3. Infinitely many exceptions to this two-curve rank cover

**Proposition 4.** The two curves used in Theorem 1 both gain rank over infinitely many real quadratic fields. For example, they both gain rank over $\mathbb Q(\sqrt{10})$.

*Proof.* For the example, $C_{410}$ has the point $(-400,1800)$ and $C_{70}$ has $(-20,300)$. Their doubles have nonintegral $x$-coordinates, as the slopes are $3119/36$ and $-37/6$, respectively. Both points are nontorsion.

For infinitude consider the genus-one curve
$$
 Y^2=(x^2-41^2)(x^2-7^2).
$$
Its smooth projective model has a rational point at infinity, used as the identity. The point $P=(57,2240)$ maps by $t=x^2,\ z=xY$ to $Q=(3249,127680)$ on $z^2=t(t-1681)(t-49)$. The map sends the identity to infinity and is a homomorphism. The doubling slope of $Q$ is $640901/7980$, which has negative $7$-adic valuation, so $t(2Q)$ has negative $7$-adic valuation too. Converting to an integral short Weierstrass model by replacing $t$ with $9t-5190$ and $z$ with $27z$ preserves this negative valuation of the doubled $x$-coordinate. By Nagell–Lutz, $Q$ and hence $P$ have infinite order.

The real points of the genus-one curve form a compact topological group. Differences of an infinite convergent subsequence of distinct multiples of $P$ give distinct multiples approaching the identity, after extracting infinitely many nonzero differences. Thus infinitely many rational points approach $P$. We can take them all with $x>41$, so $f_a(x)=x(x^2-a^2)>0$ for $a=7,41$. The curve equation implies $f_7(x)$ and $f_{41}(x)$ have the same square class, since their product is $(xY)^2$.

For each fixed square class $d>0$, the double cover obtained by adjoining a square root of $f_{41}(x)/d$ to this genus-one curve has four branch points. The two points over $x=0$ give simple zeros, the two points at infinity give poles of order three, and the zeros at $x=\pm41$ have order two. Riemann–Hurwitz gives genus three, so Faltings's theorem gives finitely many rational points on each such cover. Infinitely many distinct positive square classes $d$ therefore occur. The points $(x,\sqrt{f_a(x)})\in C_a(\mathbb Q(\sqrt d))$ are nontorsion after discarding finitely many $x$-coordinates. In fact each $C_a$ has only finitely many torsion points of degree at most two by uniform boundedness and finiteness of the torsion of bounded order. For every remaining nonsquare $d$, these points lie in the negative part for quadratic conjugation, which proves strict growth for both curves. $\square$

## 4. Scope of the remaining question

Theorem 1 proves an exact realization on a density-one set of real probes, with base-field positives included. Corollary 3 adds an arbitrary finite collection of further exact probes, and obtains pointwise finite errors when the format is allowed to grow. The failures in Proposition 4 concern rank stability, so their presence alone gives no claim about leakage of the corresponding formulas.

One sufficient route to exactness everywhere is a finite collection of positive-rank abelian varieties having at least one rank-stable member at each real quadratic field. Conjoining their integer predicates is sufficient because the known rank-stability formulas have integer witnesses. The pointwise arithmetic result of Alpöge, Bhargava, Ho and Shnidman chooses the abelian variety after the extension is given. Simultaneous positive twists work against coverage by a fixed small family, as in Proposition 4 and more generally in results on pairs of elliptic curves. The finite-cover existence claim remains open in this work. [Alpöge–Bhargava–Ho–Shnidman](https://link.springer.com/article/10.1007/s00222-025-01392-3) · [Wong, simultaneous quadratic twists of pairs](https://arxiv.org/abs/math/0606405)

The exact profile problem also has a weaker equivalent target. It suffices to realize a single c.e.-complete language $U$ identically at $\mathbb Q$ and every quadratic probe. Indeed reduce the prescribed base language to $U$ by one many-one reduction, and take the disjunction with the realization already available for arbitrary quadratic profiles that vanish at the base. Monotonicity absorbs the propagated base positives. The converse follows by prescribing $U$ at every probe. This argument is for computable hypersurface families, since the many-one reduction need not be polynomial as a map on numerical inputs. The construction in Sections 1–2 establishes approximations to this target. The manuscript proofs use established arithmetic and the claimed new content concerns simultaneous profiles and the patching construction. Priority and Lean verification remain unestablished.
