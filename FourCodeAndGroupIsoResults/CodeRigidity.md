# Sharp automorphism threshold for random linear codes

## Statement

Fix a prime power $q$. Let $C$ be a uniformly random $k$-dimensional subspace of $\mathbb F_q^n$, with $0<k<n$. Write $m=\min(k,n-k)$, $M=(q^m-1)/(q-1)$, and $\lambda_n=\binom n2/M$. Let $Z=\mathbb F_q^\times I$. For either the monomial or the semilinear monomial automorphism group $A(C)$,
$$
  \Pr[A(C)=Z]=e^{-\lambda_n}+o(1),
$$
uniformly in $k$ as $n\to\infty$. In particular, for $m=2\log_q n+c_n$ with $c_n$ bounded, the probability is
$$
  \exp\!\left(-\tfrac{q-1}{2}q^{-c_n}\right)+o(1).
$$
It tends to one exactly when $m-2\log_q n\to+\infty$, and to zero exactly when $m-2\log_q n\to-\infty$.

In the bounded window, let $X$ count the equal projective-column pairs of a generator matrix of whichever of $C,C^\perp$ has dimension $m$. Ignore zero columns in this definition. With probability $1-o(1)$, both quotients $A(C)/Z$ are elementary abelian 2-groups of rank $X$. The law of $X$ is within $o(1)$ in total variation of $\mathrm{Poisson}(\lambda_n)$.

Li, Wang and Zhou prove scalar rigidity for $m\ge (2+\varepsilon)\log_q n$ for fixed $\varepsilon>0$ and a nonrigidity bound at a specified constant offset in their Theorem III.1. In Section V they identify narrowing the gap as future work. The theorem here determines the transition probability in that gap and the group law in the window. Its high-dimensional monomial case uses their Theorem IV.1. [Li–Wang–Zhou, *The automorphism groups of random linear codes*, v2](https://arxiv.org/abs/2607.23936)

## Reduction to projective occupancy

Duality preserves both groups up to isomorphism and carries the scalar subgroup onto itself. Write an ambient semilinear map in column coordinates as $B\sigma$, with $B$ monomial and $\sigma$ a field automorphism applied entrywise. The map $B\sigma\mapsto B^{-T}\sigma$ is a group isomorphism and satisfies $\langle B\sigma x,B^{-T}\sigma y\rangle=\sigma\langle x,y\rangle$. Thus we may take $k=m\le n/2$. A matrix $G$ of size $m\times n$ with independent uniform entries fails full row rank with probability at most $(q^m-1)q^{-n}$, by a union bound on nonzero left annihilators. Conditioned on full rank, its row space is a uniform code because every code has the same number of ordered bases. Conditioning changes event probabilities by $o(1)$ uniformly. Conditioned on the zero-column locations, the nonzero columns have independent uniform classes in $\mathrm{PG}(m-1,q)$.

Two proportional nonzero columns give a monomial automorphism by swapping the coordinates and rescaling by reciprocal ratios. Two zero columns can be swapped directly. For $m\le \tfrac74\log_q n$, scalar rigidity in either group therefore requires at least $n-1$ nonzero columns and no repeated projective class. The conditional probability is zero if the number $r$ of nonzero columns exceeds $M$, and otherwise at most $\exp[-r(r-1)/(2M)]$. This is uniformly $o(1)$ because $M=O_q(n^{7/4})$, and $e^{-\lambda_n}=o(1)$ in this range.

Suppose all columns are nonzero and $G$ has full rank. An ambient semilinear monomial automorphism has an equation $S\sigma(G)DP=G$, where $S\in GL_m(q)$, $D$ is diagonal invertible, and $P$ is a permutation matrix. Thus $[S\sigma]\in P\Gamma L_m(q)$ preserves the projective multiset of columns, in particular its support. If the support has trivial stabilizer in $P\Gamma L_m(q)$, then $\sigma=1$ and $S$ is scalar. The remaining coordinate permutations are precisely those permuting indices within each projective class. For any such permutation and any scalar $S$, there is a unique choice of the diagonal entries to satisfy the equation. Taking the coordinate permutation therefore gives a surjective homomorphism from either automorphism group onto the direct product of symmetric groups on the classes, with kernel $Z$.

## The logarithmic dimension range

Work in $\tfrac74\log_q n<m\le 3\log_q n$. By a union bound the probability of a zero column is at most $nq^{-m}=o(1)$. A uniform $h$-element subset of $\mathrm{PG}(m-1,q)$, for $n/2\le h\le n$, has trivial stabilizer in $P\Gamma L_m(q)$ with probability $1-o(1)$ uniformly. To see this, first bound the number of fixed points of each nonidentity projective semilinear map.

For a nonscalar linear map, the fixed projective points are eigenlines. Eigenspace dimensions are positive, sum to at most $m$, and are each at most $m-1$. If these dimensions are $d_i$, then $\sum_i(q^{d_i}-1)\le q^{m-1}+q-2$. Indeed, merging two positive parts increases this sum, and if there are three or more parts then any two can merge without exceeding $m-1$. With one or two parts, increasing the larger part up to the cap maximizes the sum. Thus the fraction fixed is at most $1/q+o(1)$.

For a map with nonidentity field automorphism $\sigma$, let $q_0$ be the size of the fixed field. If the fixed projective lines span a proper subspace, their count is at most that of a hyperplane. Otherwise choose a basis of fixed lines, in which the map is $(x_i)\mapsto(a_i\sigma(x_i))$. In a fixed line normalize the first nonzero coordinate, say coordinate $i$, to one. Every later coordinate satisfies $a_j\sigma(x_j)=a_i x_j$ and has at most $q_0$ choices, since the ratio of two nonzero solutions is fixed by $\sigma$. The number of fixed projective lines is at most $\sum_{i=1}^m q_0^{m-i}=o(M)$, since $q_0\le\sqrt q$. Both cases move at least $M/3$ points for large $n$.

Include each of the $M$ points independently with probability $t=h/M\le 1/2$. Invariance requires each nontrivial cycle to be entirely present or absent. For length $\ell\ge2$, this has probability
$$
 t^\ell+(1-t)^\ell \le [t^2+(1-t)^2]^{\ell/2}\le e^{-t\ell/2}.
$$
The probability of invariance for a given nonidentity element is therefore at most $e^{-h/6}$. Conditioning the subset to have size $h$ costs a factor at most $M+1$, because $h$ is a mode of the binomial size distribution. The group has at most $[\mathbb F_q\colon\mathbb F_p]q^{m^2}$ elements, where $p$ is the characteristic. The union bound is $e^{-\Omega_q(n)}$ in the stated range.

Conditional on all $n$ projective classes being distinct, their support is a uniform $n$-subset. Hence scalar rigidity differs from the no-collision event in probability by $o(1)$, including the zero-column and rank-failure probabilities. Since $n/M=o(1)$ uniformly, the classical occupancy product gives
$$
 \log\Pr[\text{no collision}\mid\text{no zero column}]
 =\sum_{j=0}^{n-1}\log(1-j/M)=-\lambda_n+O(n^3/M^2).
$$
The error is $o(1)$ even at the lower end of this range. This proves the probability formula here for both groups.

## Higher dimensions and semilinear automorphisms

For $m>3\log_q n$, Li–Wang–Zhou Theorem IV.1 with $\varepsilon=1$ gives monomial rigidity with probability $1-o(1)$. This is uniform in this range, since the theorem applies to every sequence of allowed dimensions. Also $e^{-\lambda_n}=1-o(1)$ uniformly.

On the event of monomial rigidity, a nonscalar semilinear automorphism gives a nontrivial image of the automorphism group in the cyclic field Galois group. Choose an element $g$ mapping to a field automorphism $\sigma$ of prime order $s$. Then $g^s=\alpha I$ is scalar. Since $g$ commutes with $g^s$, $\sigma(\alpha)=\alpha$. Finite-field norm surjectivity lets us rescale $g$ to arrange $g^s=I$, using $(ug)^s=N_{q/q_0}(u)g^s$ for $q_0=q^{1/s}$. The rescaled operator still fixes $C$.

Such an operator has exactly ${n\brack m}_{q_0}$ invariant $m$-subspaces, by Galois descent. For an elementary verification, for each vector $v$ and $a\in\mathbb F_q$, the vector $\sum_{i=0}^{s-1}\sigma^i(a)g^i(v)$ is fixed by $g$. If the fixed vectors failed to span, a nonzero linear functional $\ell$ would annihilate all of them, so $\sum_i\sigma^i(a)\ell(g^i(v))=0$ for all $a,v$. The distinct field automorphisms are linearly independent as functions over $\mathbb F_q$. Indeed, in a shortest nonzero linear relation, evaluating at $ab$ and subtracting one automorphism's value at $b$ times the evaluation at $a$ contradicts minimality for a suitable $b$. Independence would force $\ell(v)=0$ for all $v$. Thus the fixed vectors contain an $\mathbb F_q$-basis, and the fixed vectors in those coordinates have coefficients in $\mathbb F_{q_0}$. Apply the same argument inside any invariant subspace to get the asserted bijection.

Gaussian binomial products give ${n\brack m}_{q_0}/{n\brack m}_q\le C_q q^{-(1-1/s)m(n-m)}$, since after extracting the leading powers the residual factors are bounded above and below by positive constants for fixed $q$. The total number of ambient semilinear monomial maps is $[\mathbb F_q\colon\mathbb F_p]n!(q-1)^n$. Because $m(n-m)$ increases up to $n/2$, the union bound is at most
$$
 q^{n\log_q n+O_q(n)-\tfrac32\log_q n\,(n-3\log_q n)}=o(1).
$$
Together with Theorem IV.1 this proves semilinear rigidity in higher dimensions. For prime $q$ the semilinear group is already monomial. These three ranges also establish the two asserted threshold equivalences.

## The group in the critical window

Condition on no zero columns and initially draw the $n$ i.i.d. classes before conditioning on full rank. In the bounded window, $M=\Theta_q(n^2)$, so $\mathbb E X=\lambda_n=O_q(1)$. With probability $1-o(1)$ the support has at least $n/2$ points and no class has three occupants, by Markov's inequality and the bound $\binom n3/M^2=o(1)$. Given its size, the support is uniform by exchangeability of the projective classes. The logarithmic-range estimate applies to this support. On these events, the automorphism quotients are products of $X$ two-element swap groups by the projective description. Conditioning on full rank and dropping the no-zero conditioning costs $o(1)$ in probability.

For each fixed positive integer $r$, expand the factorial moment $\mathbb E(X)_r$ as a sum over ordered $r$-tuples of distinct unordered column pairs. The disjoint pairs contribute $(n)_{2r}/(2^r M^r)=\lambda_n^r+o(1)$. An overlap graph with $v$ occupied vertices and $c$ connected components contributes $O(n^v M^{-(v-c)})=O(n^{2c-v})$. In an overlapping graph, all components have size at least two and at least one has size at least three, giving $2c-v\le-1$. There are finitely many graph types for fixed $r$. Thus $\mathbb E(X)_r=\lambda_n^r+o(1)$. On every subsequence with $\lambda_n\to\lambda$, the Poisson method of moments and tightness give convergence in total variation to $\mathrm{Poisson}(\lambda)$. Since the parameters stay in a compact positive interval and the Poisson distribution depends continuously on its parameter in total variation, the claimed approximation holds for the full sequence. The rank and zero conditioning change total variation by $o(1)$.
