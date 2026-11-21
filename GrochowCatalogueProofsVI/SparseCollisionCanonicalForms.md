# Canonical forms for two-member equivalence classes and one-way permutations

## GP-0821

For every polynomial-time computable length-preserving permutation $f$ on binary strings, there is a deterministic polynomial-time equivalence relation, with all classes of size exactly two, that has a polynomial-time complete invariant. A polynomial-time randomized canonical form for this one relation gives a polynomial-time inverter for $f$ that succeeds with probability at least $1/3$ on a uniform challenge of each length. Conversely, if $f$ has a polynomial-time randomized inverse with a worst-case success probability of at least $2/3$, this relation has a polynomial-time randomized canonical form with that probability. Thus any one-way permutation rules out universal randomized conversion even for two-member classes.

Use records $(a,b,x)$, where $a,x\in\{0,1\}^n$ and $b\in\{0,1\}$. Their complete invariant is
$$
I(a,b,x)=(a,f(x)\mathbin{\oplus}b a).
$$
Two records are equivalent when their invariants agree. Each class has exactly one member with each tag $b$, since $f$ is bijective. The inverse direction takes the representative with tag zero, using $f^{-1}$ to compute its final coordinate when necessary.

For the other direction, let $C$ be a randomized procedure that returns the chosen canonical representative of each class with probability at least $2/3$ on every input. The success guarantee concerns a single fixed choice for each class. On a challenge $y=f(w)$ with $w$ uniform, sample independent uniform $x$ and tag $b$. Set $a=f(x)\oplus y$, and call $C$ on $(a,b,x)$. The opposite-tag member of its class is $(a,1-b,w)$. If the output has the opposite tag and invariant, verify its last coordinate by applying $f$, then output it.

Indeed $a$ is uniform and independent of $x,b$. Conditional on $a$ and either tag, $f(x)\oplus b a$ is uniform. Thus conditional on the class, the input tag is still a fair bit. With probability $1/2$ it differs from the tag of the fixed canonical representative. On every record where that happens, the call succeeds with probability at least $2/3$, yielding the stated inversion probability. Verification ensures the inverter only accepts a genuine preimage. If desired, repetition of the randomized canonizer on the same record followed by a majority vote makes the lower bound on average inversion success arbitrarily close to $1/2$. An inversion lower bound for one-way permutations therefore applies to this explicit relation without any oracle separation assumptions.

The construction distinguishes efficient computation of an invariant from efficient selection inside its fiber. For a polynomial-time arbitrary relation, the universal randomized conversion question remains conditional on the computational assumptions. [Complete invariants and canonical forms](https://arxiv.org/html/0907.4775v2#S6)
