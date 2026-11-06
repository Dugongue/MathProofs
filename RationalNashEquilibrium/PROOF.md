# Rational Nash equilibrium in three-player zero-sum games

**Theorem.** For explicitly tabulated three-player games with binary-encoded rational payoffs whose sum is zero at every pure strategy profile, deciding whether some Nash equilibrium has rational probabilities is $\exists\mathbb Q$-complete under polynomial-time many-one reductions. Hardness also holds for integer payoffs.

Here $\exists\mathbb Q$ denotes the class of problems polynomial-time many-one reducible to truth of existential sentences over the ordered field of rationals. The main theorem is unconditional. Section 5 gives a separate conditional fixed-action result.

## 1. From arbitrary rational feasibility to bounded quadratic feasibility

An existential sentence over $\mathbb Q$ can be converted in polynomial time to a system of quadratic equations over $\mathbb Q$. To see this, put the quantifier-free formula in negation normal form, and use residuals that can vanish exactly when the corresponding atom holds. For $f=0$ use $f$, and for $f\ne 0$ use $fw-1$ with a fresh witness $w$. For $f\ge 0$ use $f-\sum_{i=1}^4 v_i^2$. A nonnegative rational $a/b$ with positive integer denominator is a sum of four rational squares by writing $ab$ as a sum of four integer squares and dividing by $b^2$. For $f>0$ use the conjunction of the residuals for $f\ge 0$ and $f\ne 0$. Reversing a sign handles the other comparisons.

Combine two residuals $A,B$ into $A^2+B^2$ for conjunction and $AB$ for disjunction. Fresh atom witnesses are separate, so a true branch can be made zero without placing requirements on the other branch. Conversely, a zero conjunction residual forces both children to vanish, and a zero disjunction residual forces at least one. Introduce a variable and a quadratic defining equation for each arithmetic gate and require the root residual to be zero. This avoids expanding expressions or distributing Boolean operations. Binary exponents in sparse input polynomials can be implemented by repeated squaring.

Now write an arbitrary quadratic system in $x\in\mathbb Q^m$ as $Q_i(x)+L_i(x)+c_i=0$, with $Q_i,L_i$ homogeneous of degree two and one. Produce the quadratic system in $(z,b,s)$
$$
b=8s^2-1,\qquad Q_i(z)+bL_i(z)+c_i b^2=0\quad\text{for every }i.
$$
In a rational solution $b$ cannot vanish since $s^2=1/8$ has no rational solution. Dividing by $b^2$ recovers the original system at $x=z/b$. Conversely, for any rational witness $x$ choose rational $s$ close enough to $1/\sqrt8$ that $|s|<1/2$ and $|8s^2-1|<1/(2\sqrt{1+\|x\|_2^2})$. Set $b=8s^2-1$ and $z=bx$. Then
$$
\|z\|_2^2+b^2+s^2=b^2(1+\|x\|_2^2)+s^2<1/2.
$$
Thus every yes-instance maps to a system with a rational witness in the unit ball, and every no-instance maps to a system with no rational witness anywhere. The reduction writes two extra variables and the displayed equations. Its construction requires no witness or bound on witness height.

## 2. Quadratic equations as bilinear equations on two simplexes

Let $y\in\mathbb Q^d$ denote the bounded system's variables. Put $M=d+1$. Introduce a probability vector $p$ on coordinates $0,i^+,i^-$ for $1\le i\le d$. Require $p_0=1/M$ and $p_i^++p_i^-=1/M$ and write $Y_i(p)=M(p_i^+-p_i^-)$.

Every vector $y\in[-1,1]^d$ has this encoding, with $p_i^\pm=(1\pm y_i)/(2M)$. Rationality is preserved in both directions. Let $q$ be a second probability vector on the same coordinates and let $S$ denote coordinate sum. Add equations $p_j S(q)-S(p)q_j=0$ so that $p=q$. Multiply the linear conditions on $p$ by $S(q)$ after replacing each constant $c$ by $cS(p)$. In each system equation replace $y_i y_j$ by $Y_i(p)Y_j(q)$, $y_i$ by $Y_i(p)S(q)$, and constants $c$ by $cS(p)S(q)$. The result is a collection of rational bilinear forms
$$
B_k(p,q)=\sum_{i,j}a^k_{ij}p_iq_j
$$
that must all vanish. A rational simplex solution decodes to a rational solution of the quadratic system, and the unit-ball witness from Section 1 encodes a simplex solution. All dimensions, equation counts, and coefficient bit lengths grow polynomially.

## 3. The equilibrium gadget

This section spells out the zero-sum construction of [Berthelsen and Hansen, §§3.2 and 3.4](https://arxiv.org/html/2001.05196#S3.SS4). Start with a game $G_0$. Player 1 chooses $(k,\epsilon)$ with $\epsilon=\pm1$, and players 2 and 3 choose coordinates $i,j$. The payoff vector is
$$
(2\epsilon a^k_{ij},-\epsilon a^k_{ij},-\epsilon a^k_{ij}).
$$
For strategies $p,q$ of the last two players, player 1 can achieve payoff $2u$ where $u=\max_k |B_k(p,q)|$. At any equilibrium of $G_0$ the payoffs are therefore $(2u,-u,-u)$. If $B_k(p,q)=0$ for all $k$, player 1 can play uniformly over signed actions. Player 1 then has payoff zero and cannot improve. The two signs cancel for every choice by players 2 and 3, so they cannot improve either.

Add two fallback actions per player. Use $G$ for a main action and $F$ for a fallback action. The mixed-block payoffs depend only on the block pattern, in player order.

| Blocks | Payoffs |
|---|---|
| $GGF$ | $(1,-1,0)$ |
| $GFG$ | $(1,0,-1)$ |
| $GFF$ | $(-4,2,2)$ |
| $FGG$ | $(0,0,0)$ |
| $FGF$ | $(2,-3,1)$ |
| $FFG$ | $(2,1,-3)$ |

For three main actions use $G_0$. For three fallback actions use $(-2,1,1)+H/6$, where the entries of $H$ are payoff triples. The two matrices below correspond to player 1's first and second fallback actions respectively. Rows and columns are the fallback actions of players 2 and 3.

| First action | Column 1 | Column 2 |
|---|---|---|
| Row 1 | $(-4,2,2)$ | $(-2,1,1)$ |
| Row 2 | $(-2,1,1)$ | $(0,0,0)$ |

| Second action | Column 1 | Column 2 |
|---|---|---|
| Row 1 | $(0,0,0)$ | $(-2,1,1)$ |
| Row 2 | $(-2,1,1)$ | $(-6,3,3)$ |

Each payoff triple sums to zero. We check all possible support patterns.

Suppose a Nash equilibrium has all three players assigning positive probability to main actions. Conditional on choosing main actions, their strategies form an equilibrium of $G_0$. Indeed, any strictly better main deviation in $G_0$ would also be strictly better against the unconditional opponents, since both opponents play main with positive probability and the deviating main action's identity has no effect in the other cases.

Now whenever player 2 uses main actions with positive probability, compare her conditional main strategy to any single fallback action. The fallback payoff minus the conditional main payoff, conditional on the blocks of players 1 and 3, is

| Blocks of players 1 and 3 | Difference for player 2 |
|---|---|
| $GG$ | $u$ |
| $GF$ | $3$ |
| $FG$ | $1$ |
| $FF$ | At least $4$ |

The $GG$ row is used only if that event has positive probability, in which case all three players use main and the preceding conditional-equilibrium argument applies. By symmetry the same comparison holds for player 3. Any positive main mass for either player 2 or player 3 forces both opponents to use main with probability one. The other of players 2 and 3 then also uses main with positive probability and forces the remaining player to use main with probability one. This yields an all-main equilibrium and forces $u=0$. Conversely, the all-main profile from any bilinear solution is an equilibrium of the enlarged game. Every player's fallback deviation pays zero, as does the profile itself.

The only other possibility is that players 2 and 3 both use fallback with probability one. Then player 1 strictly prefers fallback, which pays at least $-3$, over main, which pays $-4$. An all-fallback equilibrium must use an equilibrium of $H$ because translation and positive scaling preserve comparisons within the fallback subgame. To verify its exact form, let $t,x,y$ be the probabilities of the first action of players 1, 2, and 3 in $H$. The gains from first action versus second are respectively
$$
6(1-x)(1-y)-4xy,\qquad (3-y)t+y-2,\qquad (3-x)t+x-2.
$$
If $t=0$, best responses force $x=y=0$, contradicting player 1's best response. If $t=1$, they force $x=y=1$, again contradicting it. Hence $0<t<1$ and the first gain vanishes. A boundary value of $x$ or $y$ then forces the pair to be $(0,1)$ or $(1,0)$. In either case the last two best-response conditions would require both $t\le 1/2$ and $t\ge 2/3$. Thus all players mix and all three gains vanish. Subtracting the last two gives $(1-t)(y-x)=0$. With $x=y$, the first gain gives $x=y=3-\sqrt6$ as the only root in $(0,1)$. The second gives $t=1-1/\sqrt6$. This profile indeed has zero gains and is the unique equilibrium of $H$. Its probabilities are irrational. It remains an equilibrium of the full game because when both opponents use fallback, every player's fallback payoff strictly beats main. For players 2 and 3 this follows from payoffs at least $1$ versus $-3$.

Thus a rational equilibrium exists exactly when the bilinear equations have a rational simplex solution. The full payoff table has polynomial size and rational entries of polynomial bit length. Multiplying all payoffs by the same product of positive denominators gives integer payoffs of polynomial bit length and leaves the equilibria unchanged.

## 4. Membership and relation to earlier work

For a proposed strategy profile, introduce rational probability variables and enforce each simplex constraint. For each player $i$ and pure action $a$, let $V_{ia}$ be the expected payoff of that action against the opponents' probability vectors. Require an existential rational variable $v_i$ satisfying
$$
V_{ia}\le v_i,\qquad p_{ia}(v_i-V_{ia})=0
$$
for every $a$. These conditions hold exactly when the positive-probability actions are best responses. The representation is polynomial in the game table. This proves membership in $\exists\mathbb Q$ and completes the theorem.

Berthelsen and Hansen explicitly ask about hardness for the unrestricted rational problem. Their Theorem 9 assumes a promise that every positive input has a rational quadratic witness in the unit ball. Section 1 supplies an explicit polynomial-time reduction to that promise, with Sections 2–3 including the subsequent game construction for completeness. Schaefer, Cardinal, and Miltzow already state the unrestricted hardness classification in GT14 and cite Berthelsen and Hansen. Christ, Yannakakis, and Vlatakis-Gkaragkounis also list a related project titled *Bounded-$\exists\mathbb Q$* in an author's publication list. The explicit compactification is the contribution documented here. Publication priority for removing the promise has not been established. [Berthelsen–Hansen, Theorem 9](https://arxiv.org/html/2001.05196#S3.SS4) · [Schaefer–Cardinal–Miltzow, GT14](https://arxiv.org/html/2407.18006v1) · [Vlatakis-Gkaragkounis publication list](https://www.cs.columbia.edu/~emvlatakis/dummies/Detailed_Publication_List_Emmanouil_Vasileios_Vlatakis_Gkaragkounis.pdf)

## 5. Conditional result with fixed action counts and two varying payoff vectors

Assume that the embedded integers are Diophantine in the rationals, as asserted by [Glazer's manuscript](https://github.com/elliotglazer/diophantine-z-q). Then a family of three-player zero-sum games with fixed action sets and all but two pure payoff vectors fixed has a halting-complete rational equilibrium existence problem. The two payoff vectors depend affinely on a single rational parameter.

To see this, fix a polynomial relation for the halting set by the Davis–Putnam–Robinson–Matiyasevich theorem. Replace integrality of each existential witness variable by the fixed rational Diophantine definition of $\mathbb Z$. Combine all equations by a sum of squares. The result is one fixed polynomial $U(N,w)$ with a rational witness $w$ exactly when the machine coded by $N\ge0$ halts. For the input $N$ put $\lambda=1/(N+2)$, and impose the equations
$$
s=\lambda,\qquad b=8v^2-1,\qquad
P(s,b,z)=0,
$$
where $P$ is the fixed polynomial obtained by expanding
$$
s^E b^D U((1-2s)/s,z/b).
$$
Take $E$ at least the degree in $N$ and $D$ at least the total degree in $w$, so all exponents after expansion are nonnegative. Since $s>0$ and $b\ne0$ over $\mathbb Q$, every rational solution recovers a witness $w=z/b$ for input $N$. Conversely a rational witness can be scaled to $z=bw$ with $|v|<1/2$ and all coordinates of $z$ and $b$ bounded by one, using rational $v$ sufficiently near $1/\sqrt8$.

Use fixed arithmetic gates to quadratize $b=8v^2-1$ and $P=0$. Every gate on the cube of base variables is uniformly bounded, for example by an integer obtained recursively from the constants and gate operations. Fixed rational rescalings put all auxiliary gate variables in $[-1,1]$ for the constructed witness. Leave $s$ unscaled and keep its pinning equation separate. Now apply Section 2, encoding the pin as
$$
Y_s(p)q_0 - M\lambda p_0q_0=0.
$$
Because $p_0=q_0=1/M$, this is equivalent to $s=\lambda$. Only the $(0,0)$ coefficient of this bilinear form varies. In Section 3 it appears in precisely the two signed pure action profiles for this form and these two coordinates. The construction uses rational payoffs, with no input-dependent global scaling. Finally, rational equilibrium existence in this family is computably enumerable by enumerating rational profiles and verifying best-response inequalities exactly. The reduction from halting therefore proves completeness under computable many-one reductions.

*AI-assisted informal proof with independent internal audits. The main theorem does not depend on the Diophantine definition in Section 5.*
