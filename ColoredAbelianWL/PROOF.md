# An unbounded counting Weisfeiler–Leman dimension for two-colored elementary abelian groups

**Theorem.** For every positive integer $k$, there exist two nonisomorphic two-colored elementary abelian $2$-groups of the same order that $k$-dimensional counting Weisfeiler–Leman fails to distinguish. This holds even when a tuple's initial color records the full colored isomorphism type of its marked generated subgroup. Consequently Grochow–Levet Question 8.3 has a negative answer. [Original question and colored-group definition](https://arxiv.org/html/2112.11487v7#S8)

We work throughout over $\mathbb F_2$. The argument constructs a bijection compatible with every possible one-element extension of a retained tuple. It also proves the claim directly for the joint tuple-replacement refinement.

## 1. The colorings are nonisomorphic

Fix an integer $s\ge 1$, to be the largest number of elements that the strategy must hold at a time. Let $X=\mathbb F_2^{s+2}$. Index the coordinates of $Y$ by the nonempty subsets $I\subseteq [s+2]$ of size at most $s$ and set

$$
\Phi(x)_I=\prod_{i\in I}x_i,\qquad d(x)=\prod_{i=1}^{s+2}x_i .
$$

The underlying additive group in each structure is $V=X\oplus Y$. Define

$$
c_0(x,y)=\langle y,\Phi(x)\rangle,\qquad
c_1(x,y)=\langle y,\Phi(x)\rangle+d(x).
$$

Both color values occur, since $\Phi(e_1)\ne 0$ and the $Y$ coordinate can vary. In the squarefree polynomial representation of Boolean functions, $c_0$ has degree $s+1$ and $c_1$ has degree $s+2$. Every group isomorphism between the underlying elementary abelian groups is linear. An invertible linear substitution preserves Boolean degree, because substitution followed by $z_i^2=z_i$ cannot increase degree, and its inverse gives the reverse inequality. The two colored groups are therefore nonisomorphic.

## 2. Interpolate on a small affine coset

Let $U\le X$ have dimension $r\le s-1$, and let $x\notin U$. The linear map

$$
Y\longrightarrow \mathbb F_2^{x+U},\qquad
u\longmapsto \bigl(\langle u,\Phi(z)\rangle\bigr)_{z\in x+U}
$$

is onto. To see this, choose affine linear functions on $X$ whose restrictions give coordinates on the affine space $x+U$. For each $z_0\in x+U$, the product of the $r$ coordinate-equality indicators is a polynomial of degree at most $r$ whose restriction is the indicator of $z_0$. Multiply by a linear form that vanishes on $U$ and equals one at $x$ to make its value at $0$ equal to zero. Its values on $x+U$ are unchanged. Its squarefree form now has degree at most $s$ and zero constant term, so is a linear combination of the coordinates of $\Phi$. We have realized all point indicators.

## 3. A single bijection for a round

Relate two tuples if, writing the first tuple as $(x_i,y_i)_{i=1}^\ell$, the second is $(x_i,y_i+Lx_i)_{i=1}^\ell$ for some linear map $L:U\to Y$, where $U=\operatorname{span}\{x_1,\ldots,x_\ell\}$, such that

$$
\langle La,\Phi(a)\rangle=d(a)\quad\text{for every }a\in U. \tag{1}
$$

This relation holds on empty tuples and survives deletion of any entries by restricting $L$. The shear $(a,b)\mapsto(a,b+La)$ preserves the two colorings on all of $U\oplus Y$ by (1). In particular it restricts to a color-preserving isomorphism of the generated subgroups carrying each tuple entry to its matched entry.

Suppose related tuples have at most $s-1$ entries. We construct a bijection between the entire domains making every possible appended pair related, without foreknowledge of the appended element. For each $x\in X$ choose a translation $u_x$ of the fiber at $x$. If $x\in U$, take $u_x=Lx$. Otherwise use Section 2 to solve the equations

$$
\langle u_x,\Phi(x+a)\rangle
=d(x+a)+\langle La,\Phi(x+a)\rangle
\quad (a\in U).
$$

Choices for distinct $x$ are independent. The map

$$
f(x,y)=(x,y+u_x)
$$

is a bijection on the entire domain. For an appended element with $x\in U$, the old $L$ still works. For an appended element with $x\notin U$, extend $L$ linearly to $U+\mathbb F_2x$ by setting $Lx=u_x$. Condition (1) on $U$ remains valid. On the other coset it is exactly the interpolation system. The resulting tuples are related regardless of which element was appended. The map also serves as its own inverse on the underlying coordinates, so a choice specified on the second domain causes no change to the argument.

## 4. Consequences for counting refinement

In the $s$-pebble bijective game, Duplicator restricts the relation after a pebble is picked up and uses the bijection of Section 3 before Spoiler chooses the new element. The result gives arbitrarily many rounds even with the strengthened winning condition requiring preservation of the colors on the full generated subgroup. The usual Version II condition asks for a marked isomorphism of the generated subgroups, with the colors of the pebbled elements included. The strengthened condition suffices for that version and also for Version I. [Grochow–Levet group pebble-game definitions](https://arxiv.org/html/2112.11487v7#S2)

For completeness, set $s=k+1$ and consider the joint $k$-tuple-update rule directly. Related $k$-tuples have the same initial color even under the strengthened initialization. Assume related $k$-tuples still have the same color at a given round. To compare the joint replacement multisets, use Section 3 on the entire current $k$-tuple. For every $z\in V$, appending $z$ on one side and $f(z)$ on the other gives related $(k+1)$-tuples. Replacing any old entry by the appended entry preserves relatedness by deletion and reordering. The bijection $f$ thus matches the whole list of $k$ replacement colors simultaneously. The new tuple colors agree. Finally, the same extension rule builds a bijection of the two spaces of $k$-tuples, by matching each appended coordinate using a bijection conditional on its already matched prefix. It matches related tuples, so the multisets of tuple colors agree at every round. Separate coordinate replacement is weaker, and is covered by the same bijection.

The rank of $V$ is $2^{s+2}-2$. Appending unused coordinates to $Y$ works as well, by including zero coordinates in $\Phi$ and choosing translation zero in those coordinates. In particular, for every sufficiently large rank $R$, there are examples on the group of order $2^R$ whose counting WL dimension is at least $\log_2 R-O(1)=\log_2\log_2 |V|-O(1)$.

This lower bound concerns the WL method. The two examples in this proof can be distinguished by another invariant, their Boolean algebraic degree.
