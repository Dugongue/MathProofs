# Exact sample-size spectra from fair binary observations

An exact observation can describe the same convex response family over all real probabilities while its witnesses change dramatically with the permitted empirical sample size. Here a single finite experiment realizes any prescribed additive spectrum of sample sizes, with an exact correspondence of witnesses. The same construction can make regional phase concavity express arbitrary rational linear inequalities on those witnesses.

[Geometry of partially observed laws](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/FourFieldProposals/PartiallyObservedLaws.md) · [Simultaneous computability](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/FourFieldProposals/SimultaneousComputability.md)

## 1. Observations, worlds and witnesses

A finite experiment has a known finite state set $A$, given as a subset of a binary cube, and observes every one-coordinate marginal of the state. The chosen trace is that every observed bit is fair. An empirical witness at size $N\ge1$ is an unordered dataset on $A$, given by nonnegative integer multiplicities $w_a$ of sum $N$, with exactly half of every bit in each value. The list of states is explicit. It may be a proper subset of the binary cube.

Use the divisibility poset of positive integers as the environment category. An arrow $N\to kN$ duplicates each observation $k$ times, which preserves the trace. Concatenating two datasets gives addition of witnesses at the sum of their sizes. To observe the joint response of some phase variables, a fixed phase distribution can be assigned to each state: the empirical witness then induces the mixture of those phase distributions with weights $w_a/N$. This defines the response kernel of the experiment. The empirical witness concerns the binary states.

## 2. An exact compiler for fair probes

**Lemma 1.** Let $B$ be any matrix with entries $0,1,-1$ and $t$ columns. There is a binary experiment on $2t$ states with at most $1+t+\operatorname{rows}(B)$ observed bits whose fair empirical witnesses at size $N$ are naturally bijective to
$$
 \left\{z\in\mathbb Z_{\ge0}^t:Bz=0,\quad 2\sum_i z_i=N\right\}.
\tag{1}
$$
The same formulas apply to real probabilities, with $\sum_i z_i=1/2$. The bijections preserve replication and addition before normalization.

*Proof.* For each column $i$ make two states $i,+$ and $i,-$. Interpret each binary bit as a sign. Begin with a bit that is $+1$ on every $i,+$ and $-1$ on every $i,-$. For every $i$ add a bit obtained from this baseline by reversing the two signs on column $i$. Fairness of the baseline and that one flipped bit gives the equality of the two multiplicities in the column. This is the subtraction of $r+w_{i,+}-w_{i,-}=0$ and $r-w_{i,+}+w_{i,-}=0$, where $r$ counts the unchanged contribution. Call the common count $z_i$. These baseline and flip bits distinguish every state from every other state.

For each row $b$ of $B$ add another bit. On column $i$, with $b_i=1$ or $-1$, make both signs $b_i$. With $b_i=0$, keep the baseline signs. Its signed total becomes $2\sum_i b_i z_i$. Thus fairness imposes exactly $Bz=0$. The total size gives the remaining equation of (1). Conversely duplicate the count $z_i$ on the two states for each $i$; all fair constraints then hold. These formulas are coordinate projections and duplications and therefore commute with replication, addition, and taking probabilities. $\square$

## 3. All additive spectra, with a logarithmic construction

Write $\langle d_1,\ldots,d_s\rangle$ for $\{\sum_i d_i u_i:u_i\in\mathbb Z_{\ge0}\}$, including zero.

**Theorem 2.** Given any positive integers $d_1,\ldots,d_s$, construct a single fair binary experiment, using $O(\sum_i\log(2d_i))$ states and bits, whose size-$N$ empirical witnesses are naturally bijective to
$$
 \left\{u\in\mathbb Z_{\ge0}^s:2\sum_i d_i u_i=N\right\}.
\tag{2}
$$
In particular the positive accepting sizes are exactly the positive elements of $2\langle d_1,\ldots,d_s\rangle$. Every spectrum of a fair binary experiment is of this form, allowing the empty positive spectrum. Its associated size-normalized response vector is exactly $(2d_i u_i/N)_i$. Over real probabilities the corresponding vector fills the entire simplex.

*Proof.* It suffices, for each $d$, to choose a positive integer list of length $O(\log(2d))$ summing to $d$ and a homogeneous $0,1,-1$ system whose nonnegative integer solutions are exactly the multiples of that list. At $d=1$ use one free coordinate. For $d\ge2$, choose $k\ge1$ with
$$
 2^{k+1}-2\le d<2^{k+2}-2.
$$
First use two coordinates of weight $2^j$ for each $0\le j<k$. Their sum of weights is $2^{k+1}-2$. Enforce that the two coordinates at each level agree. At level $j+1$ set one coordinate equal to the sum of both coordinates at $j$. All coefficients in these equations are $0,1,-1$, since the two lower coordinates are distinct. The free first coordinate is $u$, and every level is forced to be $2^j u$.

The deficit between $d$ and the current total is between 0 and $2^{k+1}-1$. Add at most three extra copies of each level weight. Every integer from 0 to $3(2^k-1)$ is a sum of powers $2^j$ with at most three copies of each. This follows by induction, since the intervals starting at $0,2^{k-1},2\cdot 2^{k-1},3\cdot 2^{k-1}$ with the lower-digit span $3(2^{k-1}-1)$ have no gaps; at $k=1$ it is the list $0,1,2,3$. The latter total covers the deficit because $3(2^k-1)\ge2^{k+1}-1$. Equate each added coordinate to the corresponding level's coordinate. This makes the positive weight list sum exactly to $d$ and adds only $O(k)$ equations.

Take the independent systems for all $d_i$, and apply Lemma 1 to their combined matrix. The two states from each column each have its assigned list value times $u_i$. This proves (2), the size bound, and the exact formulas for replication and addition. In the real setting arbitrary nonnegative $u_i$ satisfying $2\sum_i d_i u_i=1$ give all simplex weights.

For the converse, the positive accepting sizes are even when at least one bit is observed. Add zero and divide the sizes by two. This is an additive submonoid of the nonnegative integers since datasets can be concatenated. Any nonzero additive submonoid has a positive least element $a$. In each residue class modulo $a$ that meets it, retain the least element. Those finitely many elements, with $a$, generate the whole monoid. A system with one state whose only bit is $+1$ realizes the empty positive spectrum. A system with no observed bits instead accepts every positive size when its state set is nonempty. $\square$

This theorem concerns acceptance of exact empirical witnesses with all observations specified. Normality of marginal semigroups concerns membership of integer tables in their cone and lattice, and is the closest established geometric framework. Here a single fixed fair trace along the sample-size ray can realize arbitrary numerical semigroups, together with the explicit witness counts and transport, at logarithmic size in the generators. [Sullivant, normal binary graph models](https://arxiv.org/abs/0906.1784)

**Proposition 3 (a general lower bound on compression).** For a fair binary experiment with $t$ states, if a real probability vector is feasible, then an empirical witness exists at some size at most $t^{t/2}$. Thus an experiment whose first accepting size is $2d$ needs $\Omega(\log d/\log\log(3d))$ states. Theorem 2 realizes it using $O(\log(2d))$ states.

*Proof.* The real feasible set is a compact polytope given by nonnegative probabilities, homogeneous fair equations with sign coefficient rows, and the all-ones normalization row. At a vertex, the columns corresponding to its positive entries are independent for the equality matrix. Otherwise a kernel vector supported there would permit a small perturbation of each sign and contradict extremality. Select independent rows to get a square invertible subsystem of size $j\le t$. All its entries are $+1$ or $-1$, including the normalization row. Cramer's rule shows that multiplying the probabilities by the absolute determinant gives integer counts. Hadamard's inequality bounds that determinant by $j^{j/2}\le t^{t/2}$. Taking logarithms gives the lower bound. $\square$

## 4. The same experiment represents joint phase-law witnesses

**Theorem 4.** Fix a moment order $2m$ with $m\ge2$. In the fair experiment of Theorem 2, any finite collection of rational homogeneous linear inequalities in its witness coordinates $u_1,\ldots,u_s$ can be represented exactly by concavity on designated coordinate faces of a single phase response. Every witness, over real or empirical probabilities, has product Haar $(2m-1)$-marginals and all lower independent even moments. The correspondence holds simultaneously for every size $N$, every subcollection of the inequalities, and under every replication arrow.

*Proof.* Write the inequalities as $\sum_i a_{ji}u_i\ge0$ for $1\le j\le h$. Take $h$ disjoint sets $J_j$ of $2m$ phase coordinates, and a balanced charge $\chi_j(\theta)$ on each with $m$ positive entries $+1$ and $m$ negative entries $-1$. On every binary state belonging to group $i$, use the same conditional phase density
$$
 1+\eta\sum_{j=1}^h\frac{a_{ji}}{d_i}\cos(\chi_j(\theta))
$$
against product Haar on the whole phase cube. A single positive rational $\eta$ sufficiently small gives positive smooth densities for all groups. Each nonconstant charge is supported on $2m$ coordinates, so all lower marginals and moments are independent. The known weights of groups in a size-$N$ empirical law are $2d_i u_i/N$. Mixing the densities cancels the $d_i$ factors. The coefficient of $\prod_{\ell\in J_j} x_\ell^{1/(2m)}$ in the response is therefore
$$
 \frac{2\eta(m!)^2}{N}\sum_i a_{ji}u_i .
$$
The prefactor is positive. The independent part is concave, and the only non-independent term on this face has the displayed coefficient. The uniform phase obstruction theorem says that this face is concave exactly when the coefficient is nonnegative; its proof uses the dominating fractional exponent on a boundary line when the coefficient is negative. Hence the correspondence holds for every desired pattern of tests. The real proof is the same with real unnormalized counts $u_i$ and total one. Replication rescales $u_i$ and $N$ by the same integer, so every regional verdict is preserved. $\square$ [Original phase obstruction and coefficient calculation](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/FourFieldProposals/PartiallyObservedLaws.md)

For instance impose the law that $u_i=0$ for $i\notin T$, using the one inequality $-\sum_{i\notin T}u_i\ge0$. At every feasible size $N$, the satisfying witnesses exist exactly when $N/2\in\langle d_i:i\in T\rangle$. The violating witnesses exist exactly when $N/2-d_i\in\langle d_1,\ldots,d_s\rangle$ for some $i\notin T$. These two simultaneously computed spectra determine the three-valued law status. At the continuous response level every nonempty proper $T$ yields an undetermined law, because the complete simplex is available. At empirical sizes it can be forced, excluded, or undetermined depending on $N$.

For a concrete example take $d_1=2,d_2=3$, and let concavity mean $u_2=0$. The size-$4$ trace forces this law, the size-$6$ trace excludes it, and the size-$12$ trace leaves it undetermined because both $(u_1,u_2)=(3,0)$ and $(0,2)$ work. All three traces report fair marginals of the identical experiment. The phase response is built from one fixed conditional kernel. These are genuinely different experiment worlds for the same structural input.

## 5. Approximate traces

**Proposition 5.** A tolerance below $1/N$ in each observed sign expectation imposes exact fairness at size $N$. Conversely, if the exact real trace is feasible on $t$ states, every $N\ge1$ has a size-$N$ empirical witness within $t/N$ of every fair sign expectation.

*Proof.* A sign total in an empirical dataset is an integer, so a nonzero normalized value has absolute value at least $1/N$. For the converse, round the coordinates of $N$ times a feasible probability vector first down and then round up enough entries with nonzero fractional parts to make the count sum $N$. The error in each entry is less than one, so every signed linear total changes by at most $t$. $\square$


## 6. Joint verdict profiles stabilize effectively

**Corollary 6.** Fix a set of regional concavity tests in Theorem 4 and a specified pattern of passes and failures. Replace the strict linear inequalities corresponding to failures by their weak versions, and let $C$ be the resulting closed rational cone of witness coordinates including $u_i\ge0$. Put
$$
 S_C=\{\,2\textstyle\sum_i d_i u_i:u\in C\cap\mathbb Z^s\,\}.
$$
If there is any positive-size witness for the specified pattern, then that pattern occurs at every sufficiently large multiple of $\gcd(S_C)$, and at no size outside its multiples. There is a computable threshold. Consequently the full three-valued verdict across all empirical sizes is eventually periodic for any finite collection of the laws, and its finite exceptions can also be computed.

*Proof.* Integers in a closed rational polyhedral cone have a computable finite generating set. One construction takes finitely many rational generating rays, triangulates into rational simplicial cones and multiplies the rays by positive integers to obtain integral generators. For each simplicial cone, express an integral point in the generators with nonnegative real coefficients. Subtract the integral part of each coefficient. The remaining integral point lies in the bounded half-open fundamental parallelepiped, whose finite lattice points can be enumerated. This gives a finite generating set of all integer points in the original union. Apply the positive size functional to the generating set to get generators for $S_C$. [Polytopal semigroups](https://page.mi.fu-berlin.de/lapinou/lehre/bgt.pdf)

If a strict witness $u_*$ exists, adding any weak witness preserves the strict tests. Writing $N_*=2\sum_i d_i(u_*)_i$, the size spectrum of the specified pattern therefore contains $N_*+S_C$ and is contained in $S_C$. Every nonzero finitely generated additive submonoid of $\mathbb Z_{\ge0}$ contains all sufficiently large multiples of its gcd. To see this, divide out the gcd and take the smallest positive generator $b$. The reachable residues modulo $b$ form a subgroup because they are an addition-closed set in a finite group. Gcd one gives every residue. Choose any attainable element in each residue and add arbitrary multiples of $b$. These choices can be computed by searching residues using the finite generators. Since $N_*\in S_C$, translation leaves the eventual multiples unchanged.

Existence of a positive-size pattern can be tested over the rationals by normalizing the size to one and maximizing an auxiliary common slack in the strict inequalities. A feasible positive slack gives a rational witness and scaling gives $u_*$. With no strict inequality one just tests normalized rational feasibility. All smaller sample sizes can be checked by enumerating the finitely many nonnegative counts with that total. Finally there are finitely many patterns. Taking a common period and maximum threshold gives the full verdict sequence, with each of its three outcomes determined by the simultaneous existence or absence of compliant and violating completions. $\square$

The exact sample-size classification, its logarithmic construction, and the joint phase test representation are written proofs. The [integer balance step](FairBalance.lean) was checked independently in Lean. This does not formalize the probability or phase response calculations.
