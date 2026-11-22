# Smallest finite conjugacy separators in class two

## Exact scalar optimization

Let $\Gamma$ be a finitely generated group with a central free abelian subgroup $W$ and free abelian quotient $V=\Gamma/W$. This includes every finitely generated torsion-free nilpotent group of class at most two by taking $W=Z(\Gamma)$. Indeed, if a power $x^k$ is central, then $[x,y]^k=1$ for every $y$ by the class-two commutator identity. Torsion-freeness implies that $x$ is central, so $\Gamma/Z(\Gamma)$ is torsion-free. Write $\beta:\bigwedge^2V\to W$ for the commutator tensor. Fix $g\in\Gamma$ and $z\in W$, and set $h=gz$ and $v=gW$.

**Theorem.** Suppose $g,h$ are nonconjugate. For a surjective character $\lambda:W\to \mathbb Z/p^\ell$, where $p$ is prime and $\ell\ge 1$, define
$$
T_\lambda:V\longrightarrow \operatorname{Hom}(V,\mathbb Z/p^\ell),\qquad
T_\lambda(u)(w)=\lambda(\beta(u,w)).
$$
Call $\lambda$ admissible if $T_\lambda(v)=0$ and $\lambda(z)\ne 0$. The least order of a finite quotient separating $g$ and $h$ is
$$
\min_{\lambda\ \mathrm{admissible}} p^\ell\,|\operatorname{im} T_\lambda|.
\tag{1}
$$
For every admissible $\lambda$, the term in (1) is realized by a separating $p$-group with cyclic center of order $p^\ell$. The formula uses the minimum over all finite quotients.

**Proof.** In $\Gamma$ the conjugacy class of $g$ is $g\,\beta(v,V)$. Hence $z$ survives in the finitely generated abelian group $W/\beta(v,V)$. Any nonzero element of a finitely generated abelian group survives in a finite cyclic quotient of prime-power order, as follows by its invariant-factor decomposition and reduction of any free coordinate modulo a suitable prime power. Thus there is an admissible character.

For the lower bound, take a separating finite quotient $Q$. It is nilpotent and is the direct product of its Sylow subgroups. Conjugacy in the product is coordinatewise, so at least one Sylow factor $Q_p$ separates. Let $W'$ be the image of $W$ in $Q_p$. The commutators $[\bar g,Q_p]$ form a subgroup of $W'$ since $Q_p$ has class at most two. As $\bar z$ survives in $W'/[\bar g,Q_p]$, a cyclic coordinate of that finite abelian $p$-group detects it. Compose the projection onto this coordinate with $W\to W'$ to get an admissible $\lambda:W\to R=\mathbb Z/p^\ell$. The kernel of the surjection $V\to Q_p/Z(Q_p)$ is contained in $\Lambda_\lambda=\ker T_\lambda$, because any lift of an element of that kernel commutes with every image of $\Gamma$. Moreover, $W'\le Z(Q_p)$ and $W'$ surjects onto $R$. Consequently
$$
|Q|\ \ge\ |Q_p|\ \ge\ |R|\,[V: \Lambda_\lambda]
     \ =\ |R|\,|\operatorname{im} T_\lambda|.
$$

For attainment, fix an admissible $\lambda$. Pass to $\overline\Gamma=\Gamma/\ker\lambda$, with central subgroup $R=W/\ker\lambda$. The preimage $E_\lambda$ of $\Lambda_\lambda$ is the center of $\overline\Gamma$, since commutation of a lift of $u$ with every lift from $V$ is exactly $T_\lambda(u)=0$. The sequence
$$
0\longrightarrow R\longrightarrow E_\lambda\longrightarrow\Lambda_\lambda\longrightarrow 0
$$
is an extension of abelian groups and splits because $\Lambda_\lambda$ is free abelian. Choose a complement $L$ to $R$ in $E_\lambda$. It is central, and $\overline\Gamma/L$ has order $|R|[V: \Lambda_\lambda]$. Its center is exactly the image of $R$, because commutators in $R$ retain their values in the quotient and the commutator matrix on $V/\Lambda_\lambda$ has zero radical. Admissibility gives $v\in\Lambda_\lambda$ and $\lambda(z)\ne0$, so the images of $g,h$ are distinct central elements. This works at the prime $2$ as well. $\square$

## Counting all minimum-index kernels

For each minimizing character $\lambda$, the set of complements in $E_\lambda$ is parametrized by $\operatorname{Hom}(\Lambda_\lambda,R)$ after choosing a splitting. There are $p^{\ell\,\operatorname{rank}V}$ such complements, since $\Lambda_\lambda$ has finite index in $V$.

These complements account for every minimum-index normal kernel. For a separator of minimum order, equality throughout the lower bound forces $Q=Q_p$, $Z(Q)=W'$ cyclic of order $p^\ell$, and $\ker(V\to Q/Z(Q))=\Lambda_\lambda$. The intersection of its kernel with $W$ is then $\ker\lambda$, and its image in $\overline\Gamma$ is a subgroup of $E_\lambda$ mapping isomorphically onto $\Lambda_\lambda$. Thus it is one of the complements. Two surjective characters to the same cyclic group have the same kernel in $W$ precisely when they differ by multiplication by a unit. Therefore the total count is
$$
\sum_{[\lambda]\ \mathrm{minimizing}} p^{\ell\,\operatorname{rank}V},
$$
where the sum takes one representative per unit orbit for each $p^\ell$.

## Complexity on explicit lattice inputs

Given $\beta,v,z$ in lattice coordinates and a positive bound $B$ in binary, existence of a separating quotient of order at most $B$ belongs to $\mathsf{NP}$ for all such inputs. A certificate consists of a modulus $n$, with $2\le n\le B$, and residues specifying $\lambda:W\to\mathbb Z/n$. Verify surjectivity by a gcd, test $T_\lambda(v)=0$ and $\lambda(z)\ne0$ modulo $n$, and use integer Smith normal form to compute the image size. Explicitly, for an integer lift of the matrix of $T_\lambda$ with nonzero Smith entries $d_1,\ldots,d_k$, the order is $\prod_{j=1}^k n/\gcd(n,d_j)$. Multiplying by $n$ and comparing with $B$ takes time polynomial in the input length. A prime-power restriction on the certificate is unnecessary because the complement construction works over any cyclic modulus $n$, and a minimum-order separator always gives a prime-power certificate. The affine pencil construction supplies hardness on a subfamily, yielding $\mathsf{NP}$-completeness on the full explicit same-projection lattice input class. [Kannan–Bachem, polynomial-time Smith normal form](https://doi.org/10.1137/0208040)

When $\Gamma$ is realized as the lattice of a compact class-two nilmanifold, the formula computes the smallest finite target group whose classifying space distinguishes the two free-loop classes. This is an instance-sensitive formula. Effective conjugacy separability usually considers worst-case growth over bounded-length words in a fixed group. [Pengitore, effective separability](https://arxiv.org/abs/1502.05445)

[Exact affine-pencil formula and counting reduction](MinimalFiniteLoopQuotients.md)
