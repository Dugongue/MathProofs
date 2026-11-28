# Unique products in virtually nilpotent groups of Hirsch length at most three

**Theorem.** Let $\Gamma$ be a finitely generated torsion-free virtually nilpotent group of Hirsch length $h\leq3$. Then the following are equivalent.

- $\Gamma$ has the unique product property.
- $\Gamma$ is diffuse.
- $\Gamma$ is locally indicable.
- $\Gamma$ is left-orderable.
- Either $h\leq2$ or $b_1(\Gamma)=\dim_{\mathbb Q} H_1(\Gamma;\mathbb Q)>0$.

This AI-assisted written proof uses six finite certificates. An independent exact checker verifies the certificates using only Python's standard library. A single certificate proves a whole range of integer parameters. The covering argument in the last section then removes the lower bound on the parameter.

## The endpoint criterion for cyclic extensions

A group has the unique product property if for every two nonempty finite subsets $A,B$, some element of $AB$ has exactly one ordered representation $ab$ with $a\in A$ and $b\in B$. Suppose $G$ has a normal infinite cyclic subgroup $\langle z\rangle$, with quotient $Q$. Choose representatives $s_x$ for $x\in Q$ and define $\gamma(x,y)$ by $s_xs_y=s_{xy}z^{\gamma(x,y)}$. Conjugation of $z$ by a lift of $y$ is $z\mapsto z^{\chi(y)}$, where $\chi(y)\in\{1,-1\}$. Thus

$$
(s_xz^i)(s_yz^j)=s_{xy}z^{\gamma(x,y)+\chi(y)i+j}.
$$

Let $\bar A,\bar B\subset Q$ be nonempty finite sets. Choose integers $P(x),P'(x)$ on $\bar A$ and $V(y),V'(y)$ on $\bar B$. For each pair $(x,y)$ set

$$
\begin{aligned}
U(x,y)&=\begin{cases}P(x)&\chi(y)=1\\P'(x)&\chi(y)=-1\end{cases}+V(y)+\gamma(x,y),\\
L(x,y)&=\begin{cases}P'(x)&\chi(y)=1\\P(x)&\chi(y)=-1\end{cases}+V'(y)-\gamma(x,y).
\end{aligned}
$$

**Criterion.** The group fails unique products if and only if some such data make each of $U$ and $L$ attain its maximum at least twice in every product class $xy=c$.

For necessity, take a witness $A,B$ and use its images in $Q$. Take $P$ to be the largest exponent in an $A$-fiber and $-P'$ the smallest, with $V,V'$ defined the same way for $B$. If the upper or lower endpoint in a product class were realized by just one quotient pair, its representation in that pair's two fibers would also be unique. Hence each endpoint ties.

Conversely, choose an integer $C$ large enough that the two fiber intervals $[-C-P',C+P]$ and $[-C-V',C+V]$ each contain at least two integers. Use them as the $A$- and $B$-fibers. Within each pair of fibers their sum, with the possible sign reversal, contributes the interval $[-2C-L,2C+U]$, with at least two representations at each interior integer. Choose $C$ large enough that every such interval contains zero in its interior. Every interior integer of the union in a product class is then interior to some interval, and the two extreme integers are each realized by at least two pairs by hypothesis. This gives a witness.

## Reduction to two central families

A torsion-free group of Hirsch length at most two in the theorem is trivial, infinite cyclic, free abelian of rank two, or the Klein bottle group, by the low-dimensional Bieberbach classification. These groups are locally indicable. If $h=3$ and $b_1(\Gamma)>0$, an epimorphism to $\mathbb Z$ has torsion-free virtually nilpotent kernel of Hirsch length two. The kernel and quotient are locally indicable, so $\Gamma$ is locally indicable. For the ambient elementary amenable groups, left-orderability, local indicability, and diffuseness are equivalent. Diffuseness implies unique products. See [Kionke–Raimbault, §§2 and 3, and Dunfield's Appendix B](https://arxiv.org/abs/1411.6449).

Assume $h=3$ and $b_1(\Gamma)=0$. A virtually abelian $\Gamma$ is the Hantzsche–Wendt group, the only flat three-manifold group with this first Betti number. Its failure of unique products is the example of Promislow. See [Kionke–Raimbault, §3.4](https://arxiv.org/abs/1411.6449) and [Del Valle, Linton and Nyberg-Brodda, §1](https://arxiv.org/abs/2603.22640).

Otherwise realize $\Gamma$ as an almost-Bieberbach group in the affine group of the real Heisenberg group $N$. Its subgroup of pure translations $J=\Gamma\cap N$ is a cocompact lattice, and its holonomy is finite. This uses the generalized Bieberbach theorem and the torsion-free virtually nilpotent characterization. The dimension equals the Hirsch length of the lattice, and the nonabelian nilpotent Lie algebra of dimension three is the Heisenberg algebra. [Dekimpe, Theorem 3.4 and Corollary 4.3](https://arxiv.org/abs/1603.07654)

Project to the affine group of the plane $N/Z(N)$. The image of $J$ is a rank-two lattice $\Lambda$. To see discreteness, fix two elements of $J$ with independent projected directions, which exist by cocompactness. Commutators with those two elements give two independent linear forms on $N/Z(N)$, taking the projection of $J$ into the discrete subgroup $J\cap Z(N)$ of the center. That intersection is infinite cyclic since it contains the nonidentity commutator of the chosen two elements. A finite-order automorphism of $N$ acting trivially on $N/Z(N)$ acts trivially on its center by the bracket, and any remaining central shear is unipotent and hence trivial. Thus the kernel of the affine projection on $\Gamma$ is exactly $\langle z\rangle=J\cap Z(N)$, with quotient $W$ a planar crystallographic group with translation lattice $\Lambda$.

Give the plane a holonomy-invariant inner product by averaging. If its finite group of linear parts contained no nonidentity rotation, it would be trivial or generated by one reflection. A nonzero invariant linear functional would then give a homomorphism $W\to\mathbb R$ by evaluating translation parts. It would be nonzero on $\Lambda$, contradicting $b_1(\Gamma)=0$. A nonidentity rotation in $\mathrm{GL}_2(\mathbb Z)$ has order $2,3,4,$ or $6$, by its trace and determinant. Therefore the holonomy contains a rotation of order $d\in\{2,3\}$.

Restrict to the inverse image in $\Gamma$ of the subgroup of $W$ with these rotational linear parts. Its quotient by $\langle z\rangle$ is $\Lambda\rtimes\langle M\rangle$. Indeed a lift of $M$ as an affine transformation has order $d$, since $M$ has no fixed vector and $1+M+\cdots+M^{d-1}=0$. The action on the center of $N$ is by the determinant of the action on the plane. On this subgroup $z$ is therefore central. When $d=2$ the rotation is $-I$. When $d=3$, $\Lambda$ is a rank-one lattice over the Euclidean Eisenstein integer ring, using $M$ as the action of a primitive cube root of unity. A module generator $e$ and $Me$ form a $\mathbb Z$-basis, with $M(p,q)=(-q,p-q)$.

## Exact normal forms

Fix lifts $a,b$ of a basis of $\Lambda$, and a lift $t$ of a generator of the rotation group. Write $bab^{-1}a^{-1}=z^K$ with $K\ne0$. Every group element has a unique form $a^p b^q z^s t^i$ with $p,q,s\in\mathbb Z$ and $0\leq i<d$, since its image determines $p,q,i$ and the kernel is infinite cyclic. The translation-triple law is

$$
(p,q,s)(p',q',s')=(p+p',q+q',s+s'+Kqp').
$$

For $d=2$, write $t^2=z^m$, $tat^{-1}=a^{-1}z^A$ and $tbt^{-1}=b^{-1}z^B$. The squares of $t,at,bt,abt$ have exponents $m,m+A,m+B,m+A+B-K$. Each exponent is odd, since an even exponent would give an involution by adjusting its lift by a power of $z$. Hence $A,B,K$ are even. Replace $a,b,t$ by central translates to arrange $A=B=0$ and $m=1$. The resulting conjugation law is $(p,q,s)\mapsto(-p,-q,s)$.

For $d=3$, write $t^3=z^m$, $tat^{-1}=bz^A$ and $tbt^{-1}=a^{-1}b^{-1}z^B$. The three conjugacy classes of order-three affine elements with linear part $M$ are indexed by $\Lambda/(I-M)\Lambda\cong\mathbb Z/3$. Indeed translation conjugation adds $(I-M)\Lambda$, and $M$ acts trivially on that quotient. The basis vector $e$ generates the quotient. For the representatives $t,at,a^{-1}t$ the cube exponents, computed with $a b a^{-1}b^{-1}=z^{-K}$, are

$$
m,\qquad m+2A+B-K,\qquad m-2A-B.
$$

Each is nonzero modulo three by torsion-freeness. At least two of the three residues thus agree. Choose the affine image of $t$ in one of the two equal-residue classes and choose either the basis $e,Me$ or $-e,-Me$ so $a^{-1}t$ represents the other class. This change leaves $M$ in the same matrix form. It gives $2A+B\equiv0\pmod3$. Multiplying $a,b$ by $z^u,z^v$ transforms $(A,B)$ to $(A+u-v,B+u+2v)$, so $u,v$ can be chosen to make both exponents zero. Translate $t$ centrally to get $m=1$ or $2$. Using the triple law on $b^p(a^{-1}b^{-1})^q$ gives conjugation

$$
(p,q,s)\longmapsto \left(-q,p-q,s+K\left(\binom q2-pq\right)\right).
$$

In both families multiply normal forms by applying this conjugation $i$ times to the second triple, multiplying the triples, and adding $m$ to the central exponent if $i+j\ge d$. These formulas apply to every subgroup obtained above from an actual group in the theorem. No enumeration of space groups or Seifert invariants is needed.

## Six finite checks and the covering argument

Using the section $s_{(p,q,i)}=a^p b^q t^i$, the cocycle $\gamma(x,y)$ computed by the normal-form multiplication is affine in $K$. Its constant and linear coefficient are found by evaluating the formulas at $K=0$ and $K=1$ and subtracting. For either sign of $K$, write $K=\varepsilon\lambda$ with $\lambda=|K|$. The files in [certificates](certificates/) give two finite quotient sets and four entries per point, recording the linear and constant coefficients of its upper and lower exponent functions. The central case of the endpoint criterion uses $U=P+V+\gamma$ and $L=P'+V'-\gamma$.

For each product class, the checker builds the ordered pairs of linear and constant coefficients for $U$ and $L$. It checks that the lexicographically greatest pair occurs at least twice in each case. If $S$ bounds the spread of constant terms in these comparisons, then for $\lambda\ge S+1$ a strictly larger integral linear coefficient outweighs any possible difference of constants. Thus lexicographic ties give actual ties for every such $K$. The six checks are as follows.

| Rotation order | Lift power $m$ | Sign of $K$ | Sizes of quotient sets | Product classes | Minimum $\lambda$ from check |
|---:|---:|---:|---:|---:|---:|
| 2 | 1 | + | 14, 16 | 42 | 5 |
| 2 | 1 | − | 16, 15 | 45 | 5 |
| 3 | 1 | + | 19, 22 | 63 | 5 |
| 3 | 1 | − | 19, 23 | 63 | 5 |
| 3 | 2 | + | 24, 16 | 60 | 5 |
| 3 | 2 | − | 19, 20 | 57 | 7 |

Run `python verify_certificates.py` from this directory. The check evaluates only integer formulas on the six supplied tables. It needs no search engine.

For any nonzero $K$, the base endomorphism $(v,M^i)\mapsto (uv,M^i)$ is injective for positive integer $u$. Its image has index $u^2$, and its preimage in the central extension has translation lifts $a^u,b^u$ with commutator exponent $u^2K$. The preimage is torsion-free and remains a central extension of the same planar rotation group. Normalize it by the argument above, which preserves the absolute commutator exponent. Taking $u$ large makes it satisfy the finite certificate threshold for its sign and lift power. It fails unique products, and failure passes to its overgroups. Hence the original $\Gamma$ fails unique products whenever $h=3$ and $b_1(\Gamma)=0$. This completes the equivalence.

Del Valle, Linton and Nyberg-Brodda prove failure of unique products for the particular virtually Heisenberg group $H_4$ in Proposition 7.1. The proof here covers all groups in the stated Hirsch-length range and uses a parameter-independent set of six finite checks. [Del Valle, Linton and Nyberg-Brodda](https://arxiv.org/abs/2603.22640)
