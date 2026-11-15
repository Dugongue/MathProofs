# A local–global failure for absolutely simple evolution algebras

Informal proof. There are explicit absolutely simple perfect evolution algebras of dimension $12$ over $K=\mathbb Q(\omega)=\mathbb Q(\sqrt{-3})$ that are isomorphic over every completion of $K$ and are not isomorphic over $K$. Both algebras have the same directed cycle as support. The proof exhausts the local alternatives. Each local alternative permits one of two cycle rotations, while the two global requirements on a rotation are incompatible.

Liu proves a positive local–global theorem for perfect evolution algebras over number fields with a real place, including $\mathbb Q$. The example below uses the imaginary quadratic field $\mathbb Q(\sqrt{-3})$ and shows that one cannot omit that hypothesis from a theorem covering all number fields. In particular it does not give the specific pair over $\mathbb Q$ proposed in the evolution-algebra survey's Conjecture 7. [Liu, *The Hasse Principle for Perfect Evolution Algebras*](https://zenodo.org/records/23631176), [Kaygorodov–Martín González–Viruel, Conjecture 7](https://arxiv.org/html/2610.22248v1#S2.SS3)

## 1. Isomorphisms of a weighted cycle

For a field $E$, $\ell\ge 2$, and $a\in E^\times$, define $C_\ell(a)$ on a natural basis $e_0,\ldots,e_{\ell-1}$ by
$$
 e_i^2=e_{i+1}\quad(0\le i<\ell-1),\qquad
 e_{\ell-1}^2=a e_0,\qquad e_i e_j=0\quad(i\ne j).
$$
The squares are a basis, so the algebra is perfect. It is also absolutely simple. Given a nonzero vector in an ideal over any field extension, multiplying by a basis vector of nonzero coordinate gives a nonzero multiple of its successor basis vector. Repeated squaring or multiplication along the cycle gives every basis vector.

Every isomorphism of perfect evolution algebras is monomial in natural bases. Indeed mixed products vanish in both bases and the squares on the target side are independent, which forces at most one nonzero entry per row in a basis-change matrix. The nonzero support must therefore be preserved. For these cycles the basis permutation is a rotation by some $s\in\{0,\ldots,\ell-1\}$. Write the isomorphism as $e_i\mapsto\lambda_i f_{i+s}$, with subscripts taken modulo $\ell$. If $a_i,b_i$ are the edge weights on the source and target, the condition is
$$
 a_i\lambda_{i+1}=b_{i+s}\lambda_i^2.
$$
Solving these equations in succession gives $\lambda_0^{2^\ell-1}=a/b^{2^s}$. The converse follows by choosing such a $\lambda_0$ and defining the successive $\lambda_i$ by the same equations. Thus, writing $N=2^\ell-1$ and $[a]$ for the class modulo $E^{\times N}$,
$$
 C_\ell(a)\cong_E C_\ell(b)
 \quad\Longleftrightarrow\quad [a]=[b]^{\,2^s}\text{ for some }s.
$$
This is the multiplicative rotation action for a single weighted cycle.

## 2. Two global power classes

Set $\ell=12$, $N=4095=3^2\cdot5\cdot7\cdot13$, $K=\mathbb Q(\omega)$ where $\omega$ is a primitive cube root of unity, and $L=K(\zeta_{13})$. The cyclotomic fields $\mathbb Q(\omega)$ and $\mathbb Q(\zeta_{13})$ have degree product $2\cdot12=\varphi(39)$, hence are linearly disjoint. In particular $L/K$ is cyclic of degree twelve. The element $2$ generates $(\mathbb Z/13)^\times$, since $2^6=-1$ and $2^4\ne1$ modulo 13. Put
$$
 \theta_i=\sum_{j=0}^3\zeta_{13}^{\,2^{\,i+3j}}\quad(i=0,1,2),
 \qquad \rho=\theta_0+\omega^2\theta_1+\omega\theta_2 .
$$
The generator $\sigma$ of $L/K$ acting by $\zeta_{13}\mapsto\zeta_{13}^2$ sends $\rho$ to $\omega\rho$. An explicit expansion gives
$$
 t=\rho^3=13(-1+3\omega).
$$
Here is a finite computation of this identity. Write $U_0=\{1,5,8,12\}$, $U_1=\{4,6,7,9\}$, $U_2=\{2,3,10,11\}$. In $\mathbb Z[X,Y]/(X^{13}-1,Y^3-1)$, lift $\rho$ to $P=\sum_{j=0}^2Y^j\sum_{x\in U_j}X^x$. For $j=0,1,2$, the coefficient of $Y^j X^s$ in $P^3$ is
$$
 \sum_{u=0}^2\sum_{v=0}^2\sum_{x\in U_u}\sum_{y\in U_v}
 {\bf 1}_{U_{j-u-v\bmod3}}(s-x-y\bmod13).
$$
Substitution gives the following rows. Each row for nonzero $s$ is checked within its four-element set $U_i$, since $P$ is invariant under $X\mapsto X^{8}$.

| $s$ | $Y^0$ coefficient | $Y^1$ coefficient | $Y^2$ coefficient |
|---|---:|---:|---:|
| $0$ | 24 | 72 | 36 |
| $1$ | 46 | 42 | 45 |
| $2$ | 46 | 42 | 45 |
| $4$ | 46 | 42 | 45 |

Now evaluate at $X=\zeta_{13}$, $Y=\omega$. The nonzero powers of $\zeta_{13}$ sum to $-1$, so $P^3=-22+30\omega-9\omega^2=-13+39\omega$, as claimed.

Define
$$
 \alpha=t^{1365}=\rho^N,\qquad
 p=13183=1+6\cdot13^3,\qquad
 \beta=p^{315}.
$$
The displayed $p$ is prime by trial division through $114$. The class $[\alpha]\in K^\times/K^{\times N}$ has exact order three. Its cube is $t^N$. The two primes above 13 correspond to reducing $\omega$ to the distinct roots 3 and 9 of $X^2+X+1$ modulo 13. Both have ramification index one. At the prime where $\omega$ reduces to 3, the element $-1+3\omega$ is a unit, so the normalized valuation of $t$ is one and that of $\alpha$ is 1365. The latter is not divisible by $N=4095$.
The class $[\beta]$ has exact order thirteen. Its thirteenth power is $p^N$, and at any place above $p$ its normalized valuation is $315e$ where the ramification index $e\le2$. It is not divisible by $N=315\cdot13$, which rules out an $N$-th power in $K$. The two classes therefore generate independent cyclic subgroups of coprime orders.

## 3. The exhaustive local alternatives

Fix a place $v$ of $K$. We show that $\alpha$ or $\beta$ is an $N$-th power in $K_v$.

- At a complex place both are $N$-th powers.
- At a finite place where $K_v$ contains $\mu_{13}$, an embedding $K(\zeta_{13})\hookrightarrow K_v$ over $K$ sends $\rho$ to an $N$-th root of $\alpha$. This includes every $v$ above $p=13183$, since $\mathbb Q_p$ contains $\mu_{13}$ when $p\equiv1\pmod {13}$.
- At a place above 13, the rational number $p\equiv1\pmod{13^3}$ is a thirteenth power in $\mathbb Q_{13}$. Apply Hensel's lemma to $X^{13}-p$ at 1, using $v_{13}(1-p)>2v_{13}(13)$. Thus $\beta=p^{N/13}$ is an $N$-th power in $K_v$.
- At every remaining finite place, $p$ is a unit, the residue characteristic is not 13, and $K_v$ does not contain $\mu_{13}$. The residue field also lacks $\mu_{13}$, since a primitive thirteenth root in it would lift by Hensel's lemma. Taking thirteenth powers is therefore a bijection of the residue multiplicative group. Every unit has a thirteenth root in $K_v$, by taking its residue root and applying Hensel again with unit derivative. Once more $\beta$ is an $N$-th power.

Now set $A=C_{12}(\alpha\beta)$ and $B=C_{12}(\alpha^2\beta)$. If $\alpha$ is locally an $N$-th power, the two local classes coincide. If $\beta$ is locally an $N$-th power, one local class is the square of the other, which is implemented by a cyclic rotation. Section 1 gives isomorphism over every completion.

## 4. The attempted global rotation

A global isomorphism would require
$$
 [\alpha][\beta]=([\alpha]^2[\beta])^{2^s}.
$$
The order-three part requires $2^{s+1}=1\bmod3$, so $s$ is odd. The order-thirteen part requires $2^s=1\bmod13$. The multiplicative order of 2 modulo 13 is twelve, so $s$ is divisible by twelve. These two requirements are incompatible. This proves global nonisomorphism.

The same argument yields examples with distinct pairs of local match types. For instance, one may vary the rational prime $p\equiv1\bmod13^3$. Each $\beta$ then has a different nontrivial valuation class at primes above $p$.

## 5. Finite reductions and transfer to a tensor-system question

All coefficients above are algebraic integers, since the Gaussian periods and their linear combinations defining $\rho$ are algebraic integers. At every prime where $\alpha,\beta$ are units, the local cycle isomorphism reduces to an isomorphism over its finite residue field. Indeed the recurrence in Section 1 gives $\lambda_0$ as the root of a unit, and all subsequent $\lambda_i$ are products of units. The reductions remain absolutely simple and perfect, because their cycle weights are still nonzero. Thus the same explicit globally inequivalent pair is locally equivalent and equivalent at every prime of good reduction.

There is also a transfer to ordinary tensor isomorphism over $\mathbb Q$ through tensor systems. Regard $V_A,V_B$ as rational vector spaces and include their multiplication as a bilinear map whose two inputs and output share the same linear action. Also include ordered linear endomorphisms given by multiplication by a fixed rational basis of $K$ on these spaces. An isomorphism of the resulting systems is precisely a $K$-linear algebra isomorphism. After extension to $\mathbb Q_p$, the marked scalar algebra becomes $K\otimes_{\mathbb Q}\mathbb Q_p=\prod_{v\mid p}K_v$, so the independently constructed local isomorphisms combine into a rational-local witness for the system. The analogous argument applies over $\mathbb R$. The constant-free fixed-signature tensor-system compiler transfers this pair to a single rational ordinary 3-TI pair and preserves the same field extensions. The isomorphism failure here uses the full marked multiplication and scalar maps. [Tensor-system reduction, Chen–Grochow–Qiao–Tang–Zhang](https://arxiv.org/html/2306.03135v2#S4)

The closest source found on the local–global statement was Liu's positive real-place result. Earlier evolution-algebra work describes natural-basis monomial maps and weights via the support graph. This note gives the explicit complementary construction over a field without a real place. The derivation is informal, and the literature screen does not assert exhaustive priority. [Elduque–Labra, evolution algebras and graphs](https://www.math.uci.edu/~brusso/ElduqueAutoGraph.pdf)
