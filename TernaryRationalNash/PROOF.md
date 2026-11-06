# Rational Nash equilibria at the boundary between pairwise and three-player interactions

**Theorem.** In games given as sums of zero-sum payoff tables on at most three players, rational Nash equilibrium existence is $\exists\mathbb Q$-complete. This holds with two actions per player, maximum degree at most seven in the interaction graph, and local integer payoffs from a single fixed finite alphabet. Finding an exact Nash equilibrium is also FIXP-complete under the same restrictions. In the pairwise case every such game has a rational Nash equilibrium.

**Conditional strengthening.** If the embedded integers are Diophantine in $\mathbb Q$, the decision problem above is halting-complete even on a single family obtained from one fixed game by attaching a chain of identical gadgets of varying length. The interaction graphs in that family have uniformly bounded pathwidth. Another family has a fixed interaction graph, with all but one local payoff vector fixed, and uses integer payoffs.

An interaction graph joins two players if they occur together in a local table. Each table has a payoff for each of its participants, and each player's total payoff is the sum of their local payoffs. Zero-sum here holds within each local table on every pure profile. The input explicitly lists the local tables.

## 1. Bounded quadratic feasibility with a fixed coefficient alphabet

Start from any existential sentence over the ordered field $\mathbb Q$. Put its quantifier-free part in negation normal form. An atom $f=0$ is represented by residual $f$. Use $fw-1$ for $f\ne 0$, and $f-\sum_{j=1}^4 w_j^2$ for $f\ge 0$. Witnesses in different atom occurrences are fresh. The four-square characterization follows from the integer four-square theorem applied to $ab$ for a nonnegative rational $a/b$ with $b>0$. Strict positivity is the conjunction of nonnegativity and nonvanishing. Conjunction of residuals $A,B$ is represented by $A^2+B^2$, and disjunction by $AB$. The root residual can vanish exactly when the formula is true. Inactive disjuncts place no requirement on their witness values.

Give each arithmetic gate a variable and a defining equation. Rational constants with binary numerator and denominator can be built as two integers by successive doubling and addition of $0$ or $1$, and a gate equation $dz=n$. Use repeated squaring for powers specified by binary exponents. With gates of fan-in at most two, the resulting quadratic equations have a fixed bound on their number of terms and on their integer coefficients. Introducing these variables and equations takes polynomial time.

Write the equations as $Q_j(x)+L_j(x)+c_j=0$ by degree. Introduce $z,b,s$ and replace them by
$$
Q_j(z)+bL_j(z)+c_j b^2=0,\qquad b=8s^2-1.
$$
A rational solution has $b\ne0$, so division by $b^2$ recovers the original solution $x=z/b$. Given any rational solution $x$, rational choices of $s$ arbitrarily near $1/\sqrt8$ give $b$ arbitrarily close to zero with $|s|<1/2$. Taking $z=bx$ places all the variables in $[-1,1]$. Thus unrestricted rational feasibility reduces to feasibility in this cube. Each output equation still has uniformly bounded sparsity and coefficients. The reduction does not have to find a bounded witness.

## 2. Convert feasibility into rational solvability of bounded arithmetic gates

Every wire takes values in $[0,1]$. Use gates with the following operations, along with unconstrained input wires.

- A clamped affine function of at most two inputs. Clamping sends $t$ to $\min(1,\max(0,t))$.
- The ordinary product $ab$ and the signed product $ab+(1-a)(1-b)$.

Only a fixed finite list of affine functions will be needed. A variable in $[-1,1]$ is represented by the signed value $2p-1$ of a wire $p$. Complement $1-p$ negates that value. Signed product multiplies signed values. Binary averaging of wires averages their signed values. Constants $0$, $1/2$, and $1$ represent signed $-1,0,1$.

For each bounded quadratic equation, build a wire whose signed value is its left side divided by one fixed power of two. Compute its monomials by signed product, repeat terms for the absolute values of the bounded integer coefficients, negate terms with negative coefficients, and pad with zero signed values to the chosen power of two. A binary averaging tree performs the division. The power of two is a fixed constant since the coefficient and sparsity bounds are fixed. Square each signed residual using signed product and average the squared signed values, padding with zeros to a power of two if needed. The output wire $T$ has signed value equal to this nonnegative mean. An affine gate $R=\operatorname{clamp}(2T-1)$ therefore produces $R\in[0,1]$ with $R=0$ exactly when all equations hold.

Introduce a feedback wire $v$ satisfying
$$
v=(1-R)v+R\left(v+\frac{1/2-v^2}{2}\right).
$$
This is a circuit of the prescribed gates. Compute $v^2$ by product, compute the inner parenthesis by a clamped affine gate, and combine the two product terms with clamped addition. The inner parenthesis lies in $[1/4,3/4]$ for $v\in[0,1]$, and the outer expression is a convex combination, so those clamps are inactive in any solution of the intervening gates. Use distinct intermediate output wires, with the final addition defining $v$. When $R=0$ every value of $v$ solves the feedback equation. When $R>0$ its unique solution in the unit interval is $1/\sqrt2$. In particular the gates have a rational assignment exactly when the original equations have a rational cube solution. This use of feedback is solely a test for rational solutions and permits real solutions on either outcome.

Replace excessive fan-out by binary trees of identity gates, counting individual input slots. Thus each logical wire is used in at most two slots. The circuit still has polynomial size. A gate's own output is distinct from all its inputs, and the two slots of a product will use distinct physical copies, even if the logical input is repeated.

## 3. Compile the gates into two-action zero-sum games

For each logical wire use a player with pure actions $0,1$ and identify its probability of $1$ with the wire value. Add one comparator player for each gate. Write $a_i\in\{0,1\}$ for a pure action, and use lower-case $i$ or its associated wire name for the probability of $1$. Payoffs below are local. The instruction to pay a term to one player and charge it to another means the two local entries are exact negatives, with all other entries zero.

### Affine gate

Consider an output $z$ with comparator $y$ and affine target $f=c+\sum_i d_i p_i$. On the pair $\{y,z\}$ pay $(a_y-1/2)(c-a_z)$ to $y$ and charge it to $z$. For each input $i$, on $\{y,z,i\}$ pay $d_i(a_y-1/2)a_i$ to $y$ and charge it to $z$. The latter charge does not depend on $a_z$, so it contributes zero to the output player's action gain. Inputs have zero payoff in these factors. At any profile the two action-1-minus-action-0 gains are
$$
\Delta_y=f-z,\qquad \Delta_z=y-\tfrac12.
$$
If $0<z<1$, then $y=1/2$ and $z=f$ at equilibrium. If $z=0$, the output best-response condition forces $y\le1/2$, and the comparator condition then forces $f\le0$. Likewise $z=1$ forces $f\ge1$. Thus $z=\operatorname{clamp}(f)$ at equilibrium. Conversely choose $y=1/2$ when $z=f$, $y=0$ when $f<0$, and $y=1$ when $f>1$. These choices are rational whenever the wire assignment is rational.

### Product gate

Use two private attenuated copies $c_1,c_2$ of the logical inputs $p_1,p_2$, with affine targets $c_i=1/4+p_i/2$. Give each copy its own comparator and multiply all its affine-gate factors by $K=16$. The input players remain payoff-neutral in these factors. Write $F(u,w)$ for either $uw$ or $uw+(1-u)(1-w)$, and set
$$
\widetilde F(c_1,c_2)=F(2c_1-1/2,2c_2-1/2).
$$
For the product comparator $y$ and output $z$, on the pair $\{y,z\}$ pay $-(a_y-1/2)a_z$ to $y$ and charge it to $z$. On the triple $\{y,c_1,c_2\}$ pay $(a_y-1/2)\widetilde F(a_{c_1},a_{c_2})$ to $y$ and charge it to $c_1$. These are the only additional payoffs to the two copies. In particular the comparator of a copy is unaffected. Multilinearity in the distinct players' actions gives $\Delta_y=\widetilde F(c_1,c_2)-z$ and $\Delta_z=y-1/2$.

The extra charge on $c_1$ changes its action gain by at most $5/2$ in absolute value. Indeed each pure value of $\widetilde F$ has absolute value at most $5/2$, and $|a_y-1/2|=1/2$. If $c_1=0$ at equilibrium, its comparator strictly prefers action $1$ because its target is at least $1/4$. The copy's own gain is then at least $K/2-5/2>0$, a contradiction. If $c_1=1$, the comparator strictly prefers action $0$ and the copy's gain is strictly negative. Thus $c_1$ is interior. Indifference of the copy forces its comparator's probability to differ from $1/2$ by at most $(5/2)/K<1/2$. The comparator is therefore interior too, so its gain is zero and the copy equals its affine target. The same argument applies to $c_2$, whose extra charge is zero.

Consequently the product comparator sees the exact legal target $F(p_1,p_2)\in[0,1]$. The same two-gain argument as for the affine gate gives $z=F(p_1,p_2)$. Conversely, for any legal product wire assignment choose its comparator at $1/2$. The extra charge then has zero expected action gain on the copy, so both copies and both copy comparators can use their exact target values and $1/2$, respectively.

### Composition and size

An input wire receives no action-dependent payoff when read by another logical gate. A product reads its logical input through a private copy. Thus no downstream use alters the action gains of any logical wire. The only nonzero cross-gate disturbance to a gate output is the explicitly bounded charge on a private product copy. The arguments apply simultaneously, including on the feedback cycle. At any equilibrium the logical wire values solve all gates. Every rational gate assignment lifts to a rational equilibrium by the local choices just given, with unconstrained input players indifferent. This proves both directions without any search for an equilibrium.

Each table is pointwise zero-sum and has at most three participants. All entries lie in a fixed finite rational set because the affine library, the product library, and $K$ are fixed. A single fixed positive integer clears all denominators. A logical wire has at most three neighbors in its own gate (its comparator and at most two inputs), and at most two neighbors for each of its at most two uses. The affine comparators have at most three neighbors, the product comparators at most three, and a private copy at most four. The graph degree is thus at most seven. The number of players and tables is polynomial in the formula length.

## 4. Membership and the pairwise boundary

For membership in $\exists\mathbb Q$, give each player a rational variable $p_i\in[0,1]$ and form the polynomial $D_i$ for the expected gain of action $1$ over $0$. It is a sum of degree-at-most-two contributions from the listed local tables. The two inequalities
$$
p_i D_i\ge0,\qquad (1-p_i)D_i\le0
$$
are exactly the best-response condition. The resulting existential formula has polynomial size.

For pairwise tables, choose the support of each player in any real Nash equilibrium. Restrict probabilities outside those supports to zero, and impose that each action in a chosen support is a best response. Expected pure-action payoffs are affine in the other players' probabilities. The resulting nonempty rational polyhedron contains a rational point, which is still a Nash equilibrium. This observation works even without zero-sum. For the zero-sum pairwise case an efficient linear programming algorithm is known. [Cai, Candogan, Daskalakis, and Papadimitriou](https://pubsonline.informs.org/doi/abs/10.1287/moor.2015.0745)

## 5. Exact Nash search is FIXP-complete in the same class

For hardness use the exact generalized circuit problem with complement, clipped addition, and square, proved FIXP-complete by Filos-Ratsikas, Giannakopoulos, Hollender, Lazos, and Poças. Those gates are already in Sections 2–3, with an ordinary product on two slots reading the same logical input for a square. Thus the compilation maps every equilibrium to an exact generalized circuit solution by coordinate projection. The fan-out reduction and private copies preserve the degree bound. [First-price auctions, Proposition 5.4](https://eprints.gla.ac.uk/300743/1/300743.pdf)

For membership, the polynomial-size algebraic circuit with coordinates $p_i\mapsto \operatorname{clamp}(p_i+D_i(p))$ maps the cube to itself. In the interior a fixed point forces $D_i=0$. At $p_i=0$ it forces $D_i\le0$, and at $p_i=1$ it forces $D_i\ge0$. These are exactly the best-response conditions. This proves FIXP-completeness under separable-linear reductions. [Etessami–Yannakakis](https://epubs.siam.org/doi/abs/10.1137/080720826)

## 6. Conditional fixed-family consequences

Assume the claim of [Glazer's manuscript](https://github.com/elliotglazer/diophantine-z-q) that the embedded integers have a Diophantine definition in $\mathbb Q$. Then every computably enumerable set of rationals has a fixed rational Diophantine definition. In detail, its integer numerator-denominator codes form a computably enumerable set of integer pairs with nonzero denominators. Apply Davis–Putnam–Robinson–Matiyasevich and impose the integrality of every integer variable with the assumed definition. Link the pair $(a,d)$ to the rational parameter $u$ by $du=a$ and require $d\ne0$. Conjunctions can be combined by a sum of squares.

Apply this to $\{2^{-n}:n\text{ codes a halting computation}\}$, where the halting predicate uses a fixed effective indexing of programs on empty input. Fix a defining polynomial $U(u,w)$ for this set. Quadratize $U=0$, and compactify as in Section 1, including the original parameter among the homogenized variables as $z_u$. Impose one additional equation $z_u=b u$, with $u$ now an external bounded variable. For every fixed rational $u\in[0,1]$, the combined quadratic system has a rational cube solution exactly when $U(u,w)=0$ has a rational witness. Compile this single fixed system using Sections 2–3, leaving its $u$ input wire to be supplied externally. That wire has probability $p=(1+u)/2$.

Start a chain at probability $1$ and repeat the affine gate $p\mapsto 1/4+p/2$ exactly $n$ times. The final signed value is $2^{-n}$, so attach the chain to the fixed core input. The last chain wire can be used twice in the core after the same fan-out treatment. Every stage uses the same local tables. The graph has a path decomposition consisting of constant-size bags along the chain and one final bag containing the fixed core and its attachment. This yields a computable many-one reduction from halting with a fixed payoff alphabet and bounded pathwidth. Rational equilibria are computably enumerable by enumerating rational profiles and checking all payoff gains. This proves halting-completeness.

The varying chain can also be made logarithmic in the program code, with two allowed transition types. For an integer $n$ of binary length $\ell$ (take $\ell=1$ for zero), set $u_n=(2n+1)/2^{\ell+1}$. Its numerator is odd, so it determines $n$ uniquely. Use the computably enumerable set of these $u_n$ for halting $n$ in the same fixed-core construction. Start the signed value at $1/2$ and read the $\ell$ bits of $n$ from least to most significant, applying $u\mapsto (u+d)/2$ for each bit $d$. In probability coordinates each step is the fixed affine gate $p\mapsto p/2+(d+1)/4$. This yields the same undecidability statement with a polynomial-time reduction from binary-coded halting.

For a separate fixed-graph version, use the same argument with the computably enumerable rational set $\{1/(n+2):n\text{ codes a halting computation}\}$. A two-player zero-sum table with row payoffs $\operatorname{diag}(1,n+1)$ and zero off-diagonal entries has a unique equilibrium with both players using their second action with probability $1/(n+2)$. This follows by the two equal-payoff equations, since neither player can be pure at equilibrium. Use the column probability as the first wire of a fixed affine gate that outputs $(1+1/(n+2))/2$ for the core. As a logical input, the column player receives zero payoff from the affine gate. The entire family then has fixed graph and fixed integer tables except for one vector in the matching-pennies table. Use one fixed positive scaling factor for the entire family to clear denominators. This variant has unbounded integer payoffs in that one vector.

## Relation to prior work

The bounded-witness step is the same quadratic compactification used in the companion rational Nash proof. Berthelsen and Hansen study rational equilibrium existence in explicitly tabulated three-player games, and Schaefer, Cardinal, and Miltzow already state its unrestricted hardness classification. Classical arithmetic-gate reductions to graphical games and FIXP establish hardness for equilibrium search. The result here concerns the exact rational-existence decision problem with pointwise zero-sum local tables, a fixed finite alphabet, and the pairwise versus ternary boundary. A targeted literature search found no proof of this combination. Publication priority has not been established. [Berthelsen–Hansen, Theorem 9](https://arxiv.org/html/2001.05196#S3.SS4) · [Compendium, GT14](https://arxiv.org/html/2407.18006v1) · [Daskalakis–Goldberg–Papadimitriou](https://epubs.siam.org/doi/10.1137/070699652) · [Etessami–Yannakakis](https://epubs.siam.org/doi/abs/10.1137/080720826) · [Exact generalized circuits in recent anonymous-game work](https://arxiv.org/abs/2610.16848)

*AI-assisted informal proof. The unconditional classification is independent of the Diophantine hypothesis in Section 6.*
