# Enumeration Degrees of Rational Subrings and a Cantor-Set Counterexample to Mazur

Both results below assume [Glazer's claimed Diophantine definition of the integers in the rationals](https://github.com/elliotglazer/diophantine-z-q). Write $P(a,\mathbf w)=0$ for a fixed integer polynomial whose rational solvability in $\mathbf w$ is equivalent to $a\in\mathbb Z$. Publication priority for the additional conclusions is unverified.

## 1. Hilbert's tenth problem on all subrings of the rationals

For a set $S$ of rational primes, write $R_S=\mathbb Z[S^{-1}]$ and let $\mathrm{HTP}(R_S)$ denote the set of integer-polynomial codes having a zero in $R_S$. This includes arbitrary $S$, with no effectiveness assumption. [Poonen's 2003 notes, §15](https://math.mit.edu/~poonen/papers/aws2003.pdf#page=15) ask about decidability over these rings and explain the reduction from rational solvability to solvability over each subring. [Miller, Theorem 6.5](https://arxiv.org/pdf/1907.03147#page=17) shows that an existential integer definition implies preservation of many-one reductions, and Theorems 6.7 and 6.9 encode finite prime supports by their products. The exact order classification below uses that encoding.

**Theorem.** For all sets $A,B$ of primes,
$$
 A\le_e B
 \quad\Longleftrightarrow\quad
 \mathrm{HTP}(R_A)\le_m\mathrm{HTP}(R_B)
 \quad\Longleftrightarrow\quad
 \mathrm{HTP}(R_A)\le_1\mathrm{HTP}(R_B).
$$
Here $\le_e$ is enumeration reducibility, $\le_m$ is computable many-one reducibility, and $\le_1$ additionally requires an injective map. In the forward direction, the output can always be chosen from one fixed one-integer-parameter family of geometrically integral smooth affine hypersurfaces of degree at most eight. The family works for every ring $R_B$ and every enumeration operator. With ordinary binary encodings and the operator index fixed, the reduction is polynomial-time.

Thus the many-one degrees of all $\mathrm{HTP}(R_S)$, ordered by many-one reducibility, form a copy of the entire partial order of enumeration degrees. In particular every $\mathrm{HTP}(R_S)$ is halting-hard. For computably enumerable $S$ it is halting-complete.

### Finite prime supports and a universal polynomial

An enumeration reduction can be described by a computably enumerable list of pairs $(x,F)$ with $F$ a finite set of primes. It outputs $x$ when $F\subseteq S$ for some listed pair. Choose a universal effective list of all such enumeration operators and write $e$ for its index. The relation
$$
C(e,x,m)\ \Longleftrightarrow\
m=\prod_{p\in F}p\text{ for a finite support }F\text{ listed for }x\text{ by operator }e
$$
on integer tuples is computably enumerable. The empty support has product $1$. Choose a standard computable injective pairing $t=\langle e,x,k\rangle$ with a freely chosen padding coordinate $k$. Regard $C$ as a relation in $(t,m)$ by decoding $t$ and ignoring $k$.

By the Matiyasevich–Robinson–Davis–Putnam theorem, this relation has a polynomial definition with integer witnesses. Enforce all the integer restrictions, including that on $m$, by adjoining copies of $P$. This gives a fixed system over $\mathbb Q$ that tests $C$ for rational $t,m$. Keep $t,m$ as inputs. Replace the other rational witness coordinates by $\mathbf a/b$, clear denominators and add
$$
b^2=1+u_1^2+u_2^2+u_3^2+u_4^2 .
$$
Over any $R_S$ this forces $b\ne0$. If $C(t,m)$ holds for integer $t,m$, choose a positive integer common denominator for the original rational witnesses. The guard is then solvable in integers by the four-square theorem. Thus the transformed equations admit integer witnesses on all true integer inputs and imply $C(t,m)$ on any rational solution.

Now add $m v=1$ with $v$ a native witness in $R_S$. Because $m$ is the product of its finite prime support, this holds over $R_S$ exactly when that support is contained in $S$. Consequently the new system over $R_S$ has a solution precisely when operator $e$ outputs $x$ from $S$. All steps so far are independent of $S$.

Compile the system into quadratic arithmetic-gate equations using $t$ as a variable pinned to its supplied value by one equation $s=t$. Gate values stay in the ring. Sum the squares of all equations and add the square of a fresh variable required to be zero. This yields a nonconstant polynomial $G_t$ of degree at most four. Each $R_S$ is contained in the ordered field $\mathbb Q$, so $G_t=0$ is equivalent to all the gate equations. The only varying term in $G_t$ is $(s-t)^2$. Its specialization at any input $t$ tests the chosen enumeration operator over every $R_S$.

### Transfer to a fixed smooth family

Use the family
$$
z^3+z=c^2G_t(\mathbf X)^2 .
$$
The elliptic curve $y^2=z^3+z$ has just one affine rational point, $(0,0)$. Indeed, if $z=a/b>0$ in lowest terms then the coprime factors $a,b,a^2+b^2$ have square product, which would give nonzero integers $A,B$ with $A^4+B^4$ square, contradicting [Fermat's descent](https://home.mathematik.uni-freiburg.de/arithgeom/lehre/ss20/algzt/TNT2.pdf). Negative $z$ is impossible by sign. Thus over every $R_S$ the new hypersurface has exactly the original witnesses with $z=0$ appended.

Over an algebraically closed field of characteristic zero the cubic is irreducible over the rational function field of $\mathbf X$. A root would yield a nonconstant rational map from affine space to the elliptic curve, which is impossible by restriction to a general line and Riemann–Hurwitz. This proves geometric integrality. For geometric smoothness a singular point must have $3z^2+1=0$, $G_t\ne0$ and $\nabla G_t=0$. A polynomial has finitely many critical values in characteristic zero because it is constant on every irreducible component of its critical locus. Over the algebraic closure of $\mathbb Q(t)$ only finitely many $c$ can therefore be bad. Choose a nonzero integer $c$ outside that set. The singular-parameter locus is constructible and excludes the generic point, so it contains only finitely many parameter values. The choices can be made using elimination, or fixed as finite constants. Taking a fixed $k$ larger than all excluded nonnegative integer parameters makes every $t=\langle e,x,k\rangle$ good, using a pairing with $t\ge k$.

The resulting polynomial codes are distinct for distinct $t$. The quartics differ by their linear coefficients in $s$, and their squares cannot become equal by a sign change because the coefficient of the fresh squared variable is $1$. A binary pairing and substitution in a fixed-degree polynomial use polynomial time in the bit length of $x$, with $e,k$ fixed. This establishes the smooth version of the universal encoding.

### Deduce the order classification

The operator taking $S$ to $\mathrm{HTP}(R_S)$ is an enumeration operator. Enumerate rational solutions to integer polynomials and attach to each solution the finite union of the prime supports of its reduced denominators. Thus if $A\le_e B$, composition gives an enumeration operator that outputs $\mathrm{HTP}(R_A)$ from $B$. The universal family gives an injective many-one reduction into $\mathrm{HTP}(R_B)$.

Conversely, the equation $p v-1=0$ reduces membership $p\in A$ to $\mathrm{HTP}(R_A)$. If $\mathrm{HTP}(R_A)\le_m\mathrm{HTP}(R_B)$, composing these maps with the enumeration operator for $\mathrm{HTP}(R_B)$ shows $A\le_e B$. This proves the equivalences. The halting set itself is the output of an operator using empty support, so it reduces to $\mathrm{HTP}(R_S)$ for every $S$. For c.e. $S$, the upper bound is immediate by enumerating all finite supports contained in $S$.

The same compiler shows that an effectively open upward-closed subset of the space of prime sets is exactly the solvability locus of some member of the fixed smooth family. Indeed, replace each basic cylinder in an effective open presentation by the condition that its positive bits are present. Upward closure puts this larger cylinder in the same set, since any extension of the positive bits contains a member of the original cylinder. For the converse, any integer-polynomial solution set gives a computably enumerable union of the cylinders requiring its finite denominator support. This formulation concerns the full solvability loci; Miller's construction already gives the prime-support encoding without the fixed smooth geometry.

## 2. A simultaneous Cantor-set strengthening of Mazur's 1992 conjecture

**Theorem.** There exist a smooth projective geometrically integral $\mathbb Q$-variety $X$ with Zariski-dense rational points, a morphism $f:X\to\mathbb P^1$, and one connected component $C$ of $X(\mathbb R)$ with the following property. Put $B=f(X(\mathbb Q)\cap C)$. The closure of $B$ in $\mathbb P^1(\mathbb R)$ is totally disconnected, and the set of its limit points contains a Cantor set. At every prime $p$ the closure of the same $B$ in $\mathbb P^1(\mathbb Q_p)$ also has a Cantor set of limit points. The local Cantor sets are parametrized by the same binary labels. In particular the closure of $X(\mathbb Q)\cap C$ in $C$ has exactly continuum many connected components.

[Mazur's 1992 conjecture](https://www.tandfonline.com/doi/abs/10.1080/10586458.1992.10504244) predicts finitely many components for the closure of rational points. The usual implication from an integer definition to its failure was already observed by Mazur and is recorded in [Poonen's account](https://math.mit.edu/~poonen/papers/mazur.pdf). The simultaneous conclusion and the continuum of components within one real component are the additions here.

### Build one rational set with matching limit codes at all places

Let $\mathcal C=\{0,1\}^{\mathbb N_{>0}}$. For a binary sequence $\epsilon$ set
$$
i_\infty(\epsilon)=\sum_{j\ge1}2\epsilon_j 3^{-j},
\qquad
i_p(\epsilon)=\sum_{j\ge1}\epsilon_j p^{2j}.
$$
Each $i_v$ is a continuous embedding of Cantor space into $\mathbb Q_v$. For the real embedding the contribution at the first differing digit exceeds the total possible tail. For the $p$-adic embedding it has strictly smaller valuation than the tail.

List the primes $p_1,p_2,\ldots$. For each finite binary word $w$ of length $n\ge1$, choose a rational number $a_w$ that is within $2^{-n}$ of $i_\infty(w0^\infty)$ and within $p_j^{-n}$ of $i_{p_j}(w0^\infty)$ for $j\le n$. Choose all $a_w$ distinct and choose them effectively. For example, take a common denominator coprime to the product $\prod_{j\le n}p_j^n$, impose the corresponding numerator congruences using the Chinese remainder theorem, and make the denominator large enough that the required real interval contains more candidates than have been used. Let $S$ be the set of these $a_w$.

For any subset $B'\subseteq S$, define $D(B')\subseteq\mathcal C$ by the condition that every prefix of a sequence is a prefix of infinitely many words whose $a_w$ belong to $B'$. This is a closed subset of Cantor space. The set of accumulation points of $B'$ in each $\mathbb P^1(\mathbb Q_v)$ is exactly $i_v(D(B'))$. In one direction, a convergent sequence of distinct members of $B'$ has lengths tending to infinity after discarding finitely many indices at each length. The corresponding zero-extended words have a convergent subsequence in $\mathcal C$. Its limit satisfies the prefix condition, and the approximation errors at $v$ tend to zero. Conversely, from the prefix condition select distinct words extending successively longer prefixes with lengths tending to infinity. The corresponding rationals converge to the specified limit at every place. The same argument works for the diagonal of $B'$ in the product of all the local projective lines.

For the full set $S$, every code lies in $D(S)$. Also $D$ takes finite unions to unions. For a code in $D(B'_1\cup\cdots\cup B'_r)$, if it failed the prefix test in every $B'_j$, a single prefix extending the finitely many failing prefixes would contradict the test for the union. Thus, for any finite cover of $S$ by subsets, some subset in the cover has $D$ containing a nonempty clopen cylinder. This follows because finitely many closed subsets with empty interior cannot cover Cantor space.

### Keep a Cantor cylinder on a single projective variety

The set $S$ is computably enumerable. By MRDP and the assumed integer definition its elements are exactly the rational projection of the zero set of a finite system. To see this, first describe the computably enumerable set of integer numerator–denominator pairs that the algorithm outputs, enforce all integer restrictions by copies of $P$, and tie the projection to the pair by $bt=a$. The output denominators are positive. Give the affine zero set the reduced scheme structure.

Close the graph of the projection in a product of projective spaces so it extends to a morphism to $\mathbb P^1$. By [Poonen's Theorem 1.3](https://math.mit.edu/~poonen/papers/chatelet.pdf), there exists a regular projective variety $Y$ mapping to this closure with rational-point image exactly the original affine graph's rational points. In particular the induced morphism $Y\to\mathbb P^1$ has rational image $S$.

There is a finite family of morphisms $X_j\to Y$ from smooth projective geometrically integral varieties with dense rational points whose rational images jointly cover $Y(\mathbb Q)$. For the construction take the reduced Zariski closure of $Y(\mathbb Q)$ and its irreducible components. The rational points of each component are dense, since its open part outside the other components is open in the full closure. Resolve each projectively. All rational points on the smooth open part lift, and the lifted points are dense. The remaining points lie in a finite union of closed subvarieties of smaller dimension, to which the construction applies by induction. Each smooth integral resolution with a rational point is geometrically integral, since its disjoint geometric components are permuted transitively by Galois and the component of a rational point is fixed. This step uses existence of the Zariski closures and does not assert an algorithm to compute them.

For each $j$, further split the rational image according to the finitely many connected components of $X_j(\mathbb R)$. The resulting finitely many subsets still cover $S$. The preceding Cantor argument selects one pair $(X,C)$ whose image $B$ has a clopen cylinder in $D(B)$. This proves the simultaneous limit-set assertion. In the real topology $\overline B$ is contained in the ordinary ternary Cantor set together with the countable set $B$. That union contains no real interval, so $\overline B$ is totally disconnected. The real component $C$ is compact, and the image of the closure of $X(\mathbb Q)\cap C$ is exactly $\overline B$ by continuity and compactness. Each connected component of this closure maps to a single point. Since $\overline B$ has continuum cardinality, there are at least continuum many components, and at most continuum because the ambient real variety has that cardinal bound.
