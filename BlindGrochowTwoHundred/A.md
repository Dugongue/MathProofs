# Reconstruction from weighted and modular observation panels

These 50 universal Lean statements develop five kinds of reconstruction certificate. The formulas apply to the indicated arithmetic models as well as to the examples involving cycle profiles. The applications to Frobenius use the correspondence between finite étale objects and finite Galois sets. [Finite étale schemes and Galois sets](https://stacks.math.columbia.edu/tag/04JI)

## A paired suite has one exact exponent

For a positive length $d$, write $P_k(d)=d/\gcd(d,k)$. For a finite set $S$ of exponents put $g=\gcd S$. The suite of paired observations $P_k(d)$ for $k\in S$ recovers $P_g(d)$ by taking their least common multiple. Each observation can be regenerated from $P_g(d)$ by applying the further power $k/g$. The empty suite has $g=0$ and gives the constant period 1.

On the positive divisors of a known bound $B>0$, this suite is injective exactly when $\gcd(B,g)=1$. If the condition fails, lengths $1$ and $\gcd(B,g)$ yield the same paired labels. This gives both a criterion for exact retention under erasure and a way to choose one auxiliary exponent that restores recovery. Pairing here supplies the descendant lengths associated with a single original cycle. Ordinary scalar-extension observations of an algebra supply separate cycle multisets.

## The first weighted modular collision

Let $z$ be an integer perturbation on a finite set of coordinates, with positive integer weights $w_i$ and signed signal coefficients $c_i$ satisfying $|c_i|\le w_i$. Its mass is $\sum_i w_i|z_i|$ and its observed residue is $\sum_i c_i z_i\bmod m$, where $m>0$. Suppose one anchor $a$ has $w_a=c_a=1$. The first nonzero perturbation invisible to the residue, measured by mass, is exactly
$$
\min \left(m,\ \min_{i\ne a} (w_i+|c_i|)\right).
$$
The second minimum is infinity if there is no other coordinate. In the nonzero-signal case, divisibility by $m$ forces mass at least $m$, attained by changing only the anchor. In the zero-signal case, an occupied coordinate $i$ forces compensating mass at least $|c_i z_i|$ elsewhere. Its lower bound is achieved with the anchor as the compensator. The Lean file verifies the lower bound and both witness constructions.

This measures the exact information supplied by a modular row before any choice of search heuristic. For example, take the coordinates to be pairs $(u,pu)$ of cycle lengths exposed by a prime-$p$ power. The paired difference takes the form $(-p z_u,z_u)$, so the common dimension of the two reduced profiles is $p\sum_u u|z_u|$. Integer fixed-point or nullity tests supply coefficients in that weighted model.

## Weighted marginals beyond nonnegative tables

On the determinantal rank-one locus over an integral domain, let $R_i=\sum_j b_j M_{ij}$ and $C_j=\sum_i a_i M_{ij}$ for arbitrary weights $a_i,b_j$. Their common contraction $T=\sum_i a_iR_i$ satisfies $T M_{ij}=R_iC_j$. Thus equality of weighted marginals recovers every entry when the contraction is nonzero. This allows signed tables whose ordinary total vanishes. Related exact statements handle unit pivots, completion from a crossing row and column, and contraction along one dimension. [Drton, Sturmfels, and Sullivant on determinantal independence models](https://math.berkeley.edu/~bernd/owl.pdf)

## Recovery with erasures and imperfect measurements

A signed fibre panel recovers every difference when the available rows can isolate a singleton on any nonempty disagreement support, and the fibre readings are known with error smaller than the integer divisibility quantum. Coprime modular residues can be combined with that quantum. The signed cancellations are also certified by a label-preserving permutation that negates weights in each fibre.

Another block gives decoder contracts for finite linear probes. A certified diagonal decoder allows recovery on a known support even if some gains vanish. An integer decoder tolerates channelwise errors whenever their absolute weighted sum is smaller than the gain at every recovered coordinate. A separate ordered elimination theorem handles triangular probes with nonunit diagonal coefficients. It gives the exact effective modulus after common-factor cancellation, allows separately observed coprime residues, and covers strictly bounded observation intervals.

## Structure and scope

The frozen first worker queue contributed the permutation cycle producer 74081 at positions 4 and 45, the signed divisor consumer 299627 at position 29, the normalization consumer 46428 with the divisibility producer 61474 at position 84, the signed-measure consumer 125716 at position 93, and the divisibility and coprimality combination at position 122. The nodes led to cycle-index, weighted-fibre and sharp-divisibility representations after reveal. The proofs establish the stated reconstruction and ambiguity thresholds in their model. Several ingredients are classical algebra, and bibliographic priority for the combined applications remains open. [Sources and exact Lean statements](A.lean)
