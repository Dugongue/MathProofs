# Deciding pre-injectivity of group cellular automata

**Theorem.** Given a finite group $G$, a group subshift $X\subseteq G^{\mathbb Z^d}$ specified by finite forbidden patterns, and a group cellular automaton $F:X\to X$ specified by a local rule, pre-injectivity of $F$ is decidable. The algorithm reduces to finitely many rank tests over rational function fields. This gives a decision procedure for the group-subshift case of Béaur and Kari's Question 1.

The argument below is an AI-assisted written proof.

## Reduction to elementary abelian subgroups

For a group shift $K$, let $\Delta(K)$ be its subgroup of finitely supported configurations, with support measured against the identity configuration. Two configurations $a,b\in X$ differ in finitely many positions exactly when $ab^{-1}\in\Delta(X)$. Since $F$ is a homomorphism, $F$ fails pre-injectivity exactly when $\Delta(\ker F)$ contains a nonidentity element.

Suppose $K$ is any group shift with such an element. Choose $c\in\Delta(K)$ with nonempty support $S$ of smallest cardinality. For a nonzero translation vector $w$, the commutator $[c,\sigma_w c]$ belongs to $\Delta(K)$ and has support contained in $S\cap(S+w)$. This intersection has fewer elements than $S$, because a finite nonempty set in $\mathbb Z^d$ cannot equal a nontrivial translate of itself. Minimality therefore gives $[c,\sigma_w c]=1$. Varying $w$ shows that all values of $c$ commute. They generate an abelian subgroup $B\le G$.

If $m$ is the order of $c$ and $p\mid m$ is prime, $c^{m/p}$ is a nonidentity finitely supported point whose values lie in the elementary abelian $p$-group $B[p]$. Consequently $\Delta(K)$ is nontrivial exactly when $\Delta(K\cap E^{\mathbb Z^d})$ is nontrivial for some elementary abelian subgroup $E\le G$.

## Laurent polynomial rank test

Fix $E\cong\mathbb F_p^r$ and put $K_E=K\cap E^{\mathbb Z^d}$. For $K=\ker F$, a finite description of $K_E$ is obtained by adjoining the local constraints that the image under $F$ is the identity and every value lies in $E$. Choose a finite window $W$ containing translates of the supports of all forbidden patterns. The global language $L_W(K_E)$ of $W$-patterns that occur in $K_E$ is computable by Béaur and Kari's group-shift language algorithm. Membership in $K_E$ is equivalent to membership in $L_W(K_E)$ at every translated window. In one direction this holds by definition. In the other, a forbidden pattern would sit in a translated window whose pattern could never occur in $K_E$.

As a subgroup of $(\mathbb F_p^r)^W$, $L_W(K_E)$ is a vector space. Write it as the kernel of the linear map with block matrices $\Phi_w\in\mathbb F_p^{s\times r}$ for $w\in W$. For indeterminates $u=(u_1,\dots,u_d)$ define

$$
H(u)=\sum_{w\in W}\Phi_w u^{-w},\qquad u^w=\prod_{i=1}^d u_i^{w_i}.
$$

A finitely supported configuration $c$ corresponds to the Laurent polynomial vector $c(u)=\sum_v c_vu^v$. The coefficient of $u^v$ in $H(u)c(u)$ is $\sum_w\Phi_wc_{v+w}$. Thus $\Delta(K_E)$ is nontrivial exactly when $H(u)$ has a nonzero Laurent polynomial kernel vector. A nonzero kernel vector over $\mathbb F_p(u_1,\dots,u_d)$ can be cleared of denominators, so the test is precisely $\operatorname{rank} H(u)<r$ over that field. Enumerating the elementary abelian subgroups of $G$ and computing these ranks decides the theorem.

On the full shift with local rule $f:G^W\to G$, the local subspace $\ker(f|_{E^W})$ can be used directly in place of the global language. The rule is a group homomorphism because arbitrary local patterns can be extended to global configurations. This yields a direct rank criterion in the full-shift case, where decidability also follows from Garden of Eden and the known surjectivity algorithm.

## Reference

- Pierre Béaur and Jarkko Kari, *Effective projections on group shifts to decide properties of group cellular automata*, especially Question 1 and the effective language result. [Journal article](https://doi.org/10.1142/S0129054123480040) · [Preprint](https://arxiv.org/abs/2301.11133)
