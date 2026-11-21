# Graph orbit invariants over a fixed finite field

## GP-0888

Fix a finite field $\mathbb F_q$, put $m=\binom n2$, and let $S_n$ permute the $m$ edge coordinates. The following are equivalent.

1. Boolean graphs have a uniform polynomial-time complete invariant with polynomial-length output.
2. There is a uniform family of polynomially many $S_n$-invariant polynomials over $\mathbb F_q$, each of degree at most $(q-1)m$, whose evaluations on $\mathbb F_q^m$ take polynomial time and whose joint values distinguish Boolean graph isomorphism classes.

The second condition concerns evaluation over the fixed base field. Its nonuniform version, with evaluators given by polynomial-size arithmetic circuits that agree with the polynomials on all base-field inputs, is equivalent to polynomial-size Boolean circuits for a complete invariant. The equivalence applies when the field characteristic divides $n!$.

The implication from 2 to 1 uses the list of values as the complete invariant. Encode field elements by a fixed number of bits, and evaluate the listed polynomials on the adjacency vector.

For the converse normalize the complete invariant to a fixed polynomial number $L$ of output bits, including a length marker if necessary. Define a Boolean graph from $a\in\mathbb F_q^m$ by making edge $e$ present precisely when $a_e\ne0$. For each invariant output bit $j$, let $h_j(a)\in\{0,1\}\subseteq\mathbb F_q$ be that bit on this graph. Evaluating every $h_j$ has the same polynomial-time bound. The permutation action commutes with this graph construction, so every $h_j$ is invariant as a function.

Every function from $\mathbb F_q^m$ to $\mathbb F_q$ is represented by a unique polynomial of individual degrees at most $q-1$. Existence follows from the indicator product
$$
P_j(X)=\sum_{a\in\mathbb F_q^m}h_j(a)
\prod_{e=1}^{m}\bigl(1-(X_e-a_e)^{q-1}\bigr).
$$
For uniqueness, a nonzero univariate polynomial of degree at most $q-1$ cannot vanish on the whole field. Induction on $m$, expanding in the last variable, proves the claim. The coordinate permutations preserve the individual degree bound, so by uniqueness they preserve $P_j$ as a formal polynomial. The total degree bound follows, while its evaluation algorithm is the already specified algorithm for $h_j$. The Boolean adjacency vectors remain unchanged by the threshold. Thus the polynomials separate the Boolean graph orbits.

For the circuit version, replace zero testing by $X_e^{q-1}$ and each Boolean gate by its constant-size arithmetic implementation on $\{0,1\}$, for example $\operatorname{NOT}(x)=1-x$ and $\operatorname{AND}(x,y)=xy$. This gives base-field evaluators for the canonical bounded-degree representatives. Conversely each arithmetic operation of the fixed finite field has a constant-size Boolean simulation. This proof makes no claim about circuit size for evaluating the formal $P_j$ at extension-field points. The argument needs no division by the permutation-group order and specifies the exact complete-invariant problem on which the finite-field evaluator question depends. [Graph invariant context](https://arxiv.org/abs/2604.16567) · [Earlier homomorphism separation](https://github.com/Dugongue/MathProofs/blob/a32630798eebd129ef621986ca4e0b8ce5edfcf3/GrochowCatalogueProofsII/HomomorphismSeparation.md)
