# Deciding rational points on $n$-folds via smooth projective $(n+2)$-folds

**Theorem.** Fix a number field $k$ and an integer $n\ge 0$. An oracle that decides whether a smooth projective geometrically integral $k$-variety of dimension exactly $n+2$ has a $k$-point gives an algorithm that decides whether $X(k)$ is nonempty for every $k$-variety $X$ of dimension at most $n$. The same oracle gives an algorithm that computes $X(k)$ whenever it is finite.

Here a $k$-variety is a separated finite-type $k$-scheme, specified by finitely many affine charts with gluing data. The theorem answers question (i) in §12 of Bjorn Poonen's 2009 paper. Its dimension bound comes from pulling back a single Châtelet surface bundle along a norm-form pencil. Poonen's construction in Lemma 8.1 uses a product of surface bundles whose relative dimension grows with the number of affine coordinates. [Poonen, *Existence of rational points on smooth projective varieties*, JEMS 11 (2009), 529–543](https://math.mit.edu/~poonen/papers/chatelet.pdf)

## The Châtelet bundles

By Poonen's Proposition 7.2, there is a projective family of Châtelet surfaces $\mu\colon W\to\mathbb P^1_k$ that is smooth above every $k$-point of $\mathbb P^1_k$ and satisfies $\mu(W(k))=\mathbb A^1(k)$. The fibre above infinity has no $k$-point. The construction has fibres of dimension two, including at geometric parameters where a fibre can be singular.

For computation use the finite collection $\mu_c\colon W_c\to\mathbb P^1_k$ furnished by Poonen's §9. Each is smooth above the $k$-points of the base and has a pointless fibre above infinity. At least one satisfies $\mu_c(W_c(k))=\mathbb A^1(k)$. The reduction below applies to all the members of the collection, so the algorithm needs no test to identify a member with this equality. [Poonen, Proposition 7.2 and §9](https://math.mit.edu/~poonen/papers/chatelet.pdf)

## The norm-form pencil

Let $m\ge 1$. Choose a field extension $L/k$ of degree $m$ with basis $\omega_1,\ldots,\omega_m$. For example, one can find $L$ by using a polynomial that is Eisenstein at a finite prime of $k$. Define
$$
N(t_1,\ldots,t_m)=N_{L/k}\!\left(\sum_{i=1}^m t_i\omega_i\right).
$$
This homogeneous polynomial of degree $m$ vanishes on $k^m$ only at the zero vector. In coordinates $[t_0:\cdots:t_m]$ on $\mathbb P^m_k$, consider the pencil
$$
\psi\colon\mathbb P^m_k\dashrightarrow\mathbb P^1_k,\qquad
[t_0:\cdots:t_m]\longmapsto[N(t_1,\ldots,t_m):t_0^m].
$$
Let $H=\{t_0=0\}$ be the hyperplane at infinity and let $\Lambda=\{t_0=N=0\}$ be the base locus. Then $\Lambda(k)=\varnothing$. The pencil sends $\mathbb A^m(k)$ into $\mathbb A^1(k)$ and sends $H(k)$ to infinity.

Let $B$ be the closure of the graph of $\psi$ in $\mathbb P^m_k\times\mathbb P^1_k$, with projections $\beta$ and $\pi_1$. Over $\mathbb P^m_k\setminus\Lambda$, the first projection $\beta$ is an isomorphism. Its fibres above $\Lambda$ have dimension at most one because each is a closed subscheme of a copy of $\mathbb P^1_k$. In particular $\beta$ is bijective on $k$-points.

For each $\mu_c$ set
$$
Z_c=B\times_{\mathbb P^1_k} W_c,\qquad
\eta_c=\beta\circ\operatorname{pr}_B\colon Z_c\longrightarrow\mathbb P^m_k.
$$
The morphism $\eta_c$ is projective. Its fibres have dimension two off $\Lambda$ and dimension at most three on $\Lambda$. Above each $t\in\mathbb A^m(k)$, the pencil is defined and $\eta_c$ is a base change of $\mu_c$ in a neighbourhood of $t$. Since $\mu_c$ is proper and smooth along its fibre over $\psi(t)$, it is smooth above a neighbourhood of $\psi(t)$. Thus $\eta_c$ is smooth above a neighbourhood of $t$.

Any $z\in Z_c(k)$ maps to a point $t\in\mathbb P^m(k)$ for which the fibre of $W_c$ over $\psi(t)$ has a $k$-point. Since its infinity fibre has no such point, $t\in\mathbb A^m(k)$. For a good member of the collection, every $t\in\mathbb A^m(k)$ has a $k$-point in its fibre. Therefore
$$
\eta_c(Z_c(k))\subseteq\mathbb A^m(k)\quad\text{for all }c,
\qquad
\bigcup_c\eta_c(Z_c(k))=\mathbb A^m(k).
$$

## The dimension bound

First let $U$ be a nonempty smooth integral affine $k$-variety of dimension $d\le n$. Choose a closed embedding $U\hookrightarrow\mathbb A^m_k$ with $m\ge1$ and let $\overline U\subseteq\mathbb P^m_k$ be its projective closure, so $U=\overline U\cap\mathbb A^m_k$. For each $c$ put
$$
Y_c^0=Z_c\times_{\mathbb P^m_k}\overline U .
$$
Over $\overline U\setminus\Lambda$ its fibres have dimension two. The part over $\overline U\cap\Lambda$ has dimension at most $\dim(\overline U\cap\Lambda)+3$. Since the integral variety $\overline U$ meets $\mathbb A^m_k$, its intersection with the hyperplane $H$ has dimension at most $d-1$. As $\Lambda\subseteq H$, the whole of $Y_c^0$ has dimension at most $d+2$.

Resolve the reduced projective scheme underlying $Y_c^0$ by projective resolutions of its irreducible components, choosing each resolution to be an isomorphism over the regular locus of its component. Take their disjoint union, denoted $Y_c$. Constructive resolution in characteristic zero gives $Y_c$ effectively. Each component has dimension at most $d+2$. Every $k$-point of $Y_c$ maps to a $k$-point of $U$, by the property of $\eta_c$ just proved. Conversely, let $u\in U(k)$ and choose $c$ for which $\eta_c^{-1}(u)$ has a $k$-point $z$. Since $U$ is smooth and $\eta_c$ is smooth above a neighbourhood of $u$, the scheme $Y_c^0$ is regular at $z$. At a regular point there is only one irreducible component, and the chosen resolution of that component is an isomorphism there. Thus $z$ lifts to $Y_c(k)$. In particular,
$$
U(k)\ne\varnothing \quad\Longleftrightarrow\quad
Y_c(k)\ne\varnothing\text{ for some }c .
$$
The construction uses the same resolution input as Poonen's Theorem 1.3. [Poonen, Theorem 1.3 and §9](https://math.mit.edu/~poonen/papers/chatelet.pdf)

For a general $X$, take the reductions of its affine charts. For each chart take its integral components, cover their smooth loci by finitely many affine opens, and recurse on their singular loci. Dimension drops at each recursion, by generic smoothness in characteristic zero. This gives a finite collection of smooth integral affine pieces of dimension at most $n$ whose $k$-points cover $X(k)$. All the chart, component, singular-locus, graph-closure and fibre-product operations are effective over a number field. Applying the preceding construction to each piece gives finitely many smooth projective $k$-varieties of dimension at most $n+2$, one of which has a $k$-point exactly when $X$ does.

## Queries of dimension exactly $n+2$

Compute the connected components of these smooth projective outputs. Every such component $C$ is integral. If $C(k)\ne\varnothing$, Poonen's Lemma 10.1 gives geometric integrality. The geometric integrality test is effective, so discard all components that fail it. For each remaining $C$ query the oracle on
$$
C\times_k\mathbb P^{\,n+2-\dim C}_k.
$$
This is smooth, projective and geometrically integral of dimension exactly $n+2$, and it has a $k$-point exactly when $C$ does. The disjunction of the oracle answers decides whether $X(k)\ne\varnothing$. [Poonen, Lemma 10.1 and §10](https://math.mit.edu/~poonen/papers/chatelet.pdf)

To list $X(k)$ when it is finite, start with $F=\varnothing$ and apply the decision procedure to $X\setminus F$. A positive answer permits enumeration of the affine charts over the computable field $k$ until a point outside $F$ is found. Add it to $F$ and repeat. A negative answer returns the full set $F$. Each query stays within dimension $n$, and the process terminates under the finiteness promise.

This is a written proof. The inputs are the Châtelet bundle construction and effectivity from Poonen, and constructive resolution of singularities in characteristic zero. Publication priority for the dimension bound remains unestablished.
