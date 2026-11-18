# Polynomial-time group epimorphism for bounded coefficient-field genus

**Status.** Informal proof of a deterministic algorithm for the coefficient-field case of Grochow–Srivastava–Thakkar Open Question 3(3). The algorithm allows an arbitrary class-two target of the same odd prime exponent. Definition 3.2 of Brooksbank–Maglione–Wilson also allows nonreduced local centroids with larger coefficient-field dimension. For that broader setting, we prove that restricting to exact genus two gives a problem polynomial-time equivalent to unrestricted epimorphism for class-two groups of odd prime exponent. See Theorem 4.

## 1. The algorithm

**Theorem 1.** Fix a positive integer $r$. Let $G,H$ be given by Cayley tables and have class at most two and exponent dividing the same odd prime $p$. For each directly indecomposable factor of the commutator bimap of $G$, let $C$ denote its local centroid, $k$ its coefficient field and $W$ its commutator space. Assume $\dim_k W\le r$ in every such factor. There is a deterministic algorithm, polynomial in the sum of the table lengths for fixed $r$, that decides whether $G$ surjects onto $H$ and produces a surjection on yes instances.

Here the coefficient field is the unique subfield of $C$ mapping isomorphically to $C/J(C)$, where $J(C)$ is the Jacobson radical. In particular, Theorem 1 with $r=2$ applies when the source is of genus at most two in the sense of BMW Definition 3.2 and each of its local centroids is a field. It also applies directly to the coefficient-field dimension test used in BMW §7, with no field or genus promise on the target. [Statement of Open Question 3(3)](https://arxiv.org/html/2609.07429v1#S7). [BMW, Definition 3.2 and §7](https://joshmaglione.com/papers/Genus2.pdf).

### 1.1 From groups to commutator maps

Put $F=\mathbb F_p$. In a group of class at most two and exponent dividing $p$, the operation $x+y=xy[x,y]^{-1/2}$ is abelian, with $[x,y]=xyx^{-1}y^{-1}$ and the exponent $-1/2$ taken modulo $p$. The class-two commutator identities give associativity of this addition and bilinearity of the bracket. The original product is recoverable from the addition and half the bracket. Consequently group homomorphisms are exactly the $F$-linear bracket-preserving maps for these coordinates. Bases, centers, and commutator spaces can all be computed by scanning the tables and performing linear algebra with this addition. The nontrivial group orders identify the prime, and the trivial groups are immediate.

Write $V_X=X/Z(X)$, $W_X=[X,X]$, $c_X=\dim_F(Z(X)/W_X)$, and $b_X:V_X\times V_X\to W_X$ for the commutator map. Its values span $W_X$ and its common radical is zero. An epimorphism induces surjective $F$-linear maps $A:V_G\to V_H$, $B:W_G\to W_H$ with
$$
b_H(Ax,Ay)=B b_G(x,y).
\tag{1}
$$
It also induces a surjection of abelianizations. Conversely, given (1) with $A,B$ surjective, the abelianization rank inequality
$$
\dim V_G+c_G\ \ge\ \dim V_H+c_H
\tag{2}
$$
suffices. Split the two linearized groups as $V_X\oplus W_X\oplus F^{c_X}$. The inequality gives a surjection from $\ker A\oplus F^{c_G}$ onto $F^{c_H}$. Extend it to a linear map on $V_G\oplus F^{c_G}$, and use $A,B$ on the other two output coordinates. The resulting map preserves brackets and is surjective. In particular (2) settles abelian targets. An abelian source cannot surject onto a nonabelian target.

For any such full, common-radical-zero bimap $b$, its centroid consists of $(s,t)$ with $b(sx,y)=b(x,sy)=t b(x,y)$ for all $x,y$. These equations are linear and the projection to the $s$ coordinate is faithful. For two centroid elements, computing $b(sx,s'y)$ in either order shows that $t,t'$ commute on all values of $b$, and then nondegeneracy forces the $s$'s to commute as well. The primitive idempotents of this commutative algebra give the direct decomposition
$$
V_G=\bigoplus_i V_i,\qquad W_G=\bigoplus_i W_i,\qquad b_G=\bigoplus_i b_i.
\tag{3}
$$
In particular the output spaces in (3) form a direct sum. Conversely any simultaneous direct decomposition gives these centroid idempotents, so the local factors are intrinsic. A finite commutative local $F$-algebra of residue size $q$ has its unique coefficient field as the roots of $x^q=x$: each root in the residue field lifts uniquely by the nilpotent-ideal lifting argument below, and the roots form a field because the ring is commutative of characteristic $p$.

### 1.2 Finite-algebra computations and lifting

For a nonzero full, common-radical-zero alternating bimap $b:U\times U\to W$, set $D=\operatorname{Adj}(b)\subseteq\operatorname{End}_F(U)$, where $a\in D$ if $b(ax,y)=b(x,a^*y)$ for an $a^*$. The adjoint is unique, and skew symmetry makes it an involution. Isometries fixing $W$ pointwise are the units $u$ of $D$ with $u^*u=1$. The radical $J=J(D)$ is stable under $*$.

We use the following raw-size bound for finite-algebra computations. A faithful action on a vector space of dimension $v$ meets every simple factor of the semisimple quotient. In fact, compute a composition series by testing every vector in each successive quotient and choosing a nonzero cyclic submodule of least dimension. Its dimension is least among nonzero submodules, so it is simple. The kernel of the action on all composition factors is a nilpotent ideal, because each element in the kernel lowers the series. Conversely the Jacobson radical kills all those factors. Thus that kernel equals the radical. Identify isomorphic simple factors of the module by solving the linear equations for intertwiners. For one representative $S_j$ of each isomorphism class, compute the field $K_j=\operatorname{End}_D(S_j)$ by linear equations and Wedderburn's theorem on finite division rings. Semisimple algebra structure identifies the image of $D$ on these representatives with $\prod_j M_{m_j}(K_j)$, with $m_j=\dim_{K_j}S_j$. Choose $K_j$-bases to realize this product explicitly, and factor the involution through the computed quotient. This takes $p^{O(v)}$ time times a polynomial in the matrix presentation size, since the cyclic-submodule search uses at most $v p^v$ vectors. In particular
$$
\sum_j m_j[K_j:F]\ \le\ v .
\tag{4}
$$
The same procedure on a source centroid acting faithfully on $V_G$, followed by lifting its quotient idempotents, computes (3). Polynomial algorithms in the characteristic also suffice for these algebra computations. [Wilson, Finding central decompositions of p-groups, §5](https://arxiv.org/abs/0801.3434). [Ivanyos–Qiao, Algorithms based on *-algebras, Theorem 18](https://arxiv.org/abs/1708.03495).

Here are the lifts we need. For a simple root of a polynomial $f$ over $F$ in $D/J$, lift the root to $x$ and apply $x\gets x-f(x)f'(x)^{-1}$. The derivative is a unit because its residue is. Its inverse belongs to the commutative algebra generated by $x$, by the minimal polynomial of the invertible derivative. The error doubles in radical order at each step, so the iteration terminates. A self-adjoint residue root lifts self-adjointly by first replacing $x$ by $(x+x^*)/2$. For idempotents use $f(X)=X^2-X$. For a frame of orthogonal idempotents, lift them successively in complementary corners. The same procedures apply to the source centroid.

If $g$ lifts a unitary of $D/J$, then $g^*g=1+z$ with $z\in J$. The truncated inverse-square-root series in $z$ has coefficients $(-1)^i\binom{2i}{i}/4^i$, requiring only the inverse of $2$, and gives a unitary lift $g(g^*g)^{-1/2}$. If $g$ intertwines two lists of self-adjoint elements, $g^*g$ centralizes the first list, so this correction preserves the intertwining relations.

### 1.3 Enumerating target decompositions

An orthogonal decomposition of $U$ corresponds to a set of orthogonal self-adjoint idempotents summing to 1 in $D$. Fully refined decompositions correspond to such frames whose members cannot themselves split into two nonzero orthogonal self-adjoint idempotents. A frame is fully refined exactly when its residue frame is; use corner lifting in one direction and the absence of nonzero idempotents in $J$ in the other.

The involution of the semisimple quotient either pairs two simple factors or acts in a single matrix factor as adjoint for a symmetric, alternating, or Hermitian form. The matrix of that form can be obtained from the linear adjoint equations on matrix units. On the center the involution is either trivial or the order-two field automorphism. In the latter case scalar normalization to a Hermitian matrix amounts to solving a scalar equation of Hilbert 90 and can be done by enumerating field elements. For paired factors, a frame amounts to matched rank-one matrix idempotents. For alternating factors the summands are symplectic planes. For Hermitian and symmetric factors the summands are nondegenerate lines. The symmetric case has one conjugacy type for each possible number of nonsquare lines, with the parity constrained by the discriminant. Each of the other cases has one type. This follows by mapping paired bases or fixed-type orthogonal bases summand by summand. For the symmetric case use a diagonal model with the desired numbers of entries $1$ and $\nu$ for a fixed nonsquare $\nu$. When its dimension and discriminant agree with the ambient form, ordinary finite-field Gram reduction supplies a change of basis. The same Gram procedures handle alternating and Hermitian forms. All needed square or norm searches take time polynomial in the relevant field size. [Wilson, Decomposing p-groups via Jordan algebras, §5](https://arxiv.org/abs/0711.0201).

By (4) the number of choices across all symmetric factors is at most $\prod_j(m_j+1)\le 2^v$, where $v=\dim_F U$. Lift one frame for each choice. To verify that these suffice upstairs, first lift any residue unitary identifying two residue frames. For two matched lifts $e_i,f_i$ of the same frame, $g=\sum_i f_i e_i$ satisfies $g\equiv 1\bmod J$ and $g e_i=f_i g$. The inverse-square-root correction from §1.2 makes this intertwiner unitary. Thus every fully refined orthogonal decomposition is isometric, fixing $W$ pointwise, to one of the enumerated decompositions. The total cost is $p^{O(v)}$, and each decomposition has at most $v$ summands.

### 1.4 Enumerating field actions on a target restriction

Given a finite field $k/F$, a full nonzero common-radical-zero alternating bimap on $U$ admits a list of representatives for all unital embeddings $k\hookrightarrow D=\operatorname{Adj}(b)$ with self-adjoint image, taken up to conjugation by a unitary of $D$. We construct this list in time polynomial in $|U|+|k|$.

In a single stable factor $M_m(K)$ of $D/J$, giving a $k$-action is equivalent to making $K^m$ a module over
$$
R=K\otimes_F k=\prod_{\ell=1}^g E_\ell,\qquad
g=\gcd([K:F],[k:F]).
$$
The involution on $K$ extends to $R$ by acting trivially on $k$. Self-adjointness of the action means the ambient classical form $\eta$ is balanced for that involution. The summands belonging to the field factors of $R$ are orthogonal except when those factors are exchanged by the involution.

For a fixed factor $E/K$, the balanced form is a trace of an $E$-valued form $h$. This follows by defining $h(x,y)$ using $\operatorname{Tr}_{E/K}(a h(x,y))=\eta(ax,y)$ for all $a\in E$, using the nondegenerate trace pairing. The balance identity gives $E$-linearity in the first variable and semilinearity in the second for the induced involution of $E$. Compatibility of trace with that involution gives the symmetry type. Nondegeneracy holds in both directions because the trace identity tests every multiple of a vector. If the involution of $K$ is trivial then the induced involution is trivial, since it fixes both $K$ and $k$. Thus the fixed factors give symmetric, alternating, or Hermitian forms as appropriate. For two exchanged fields their summands must have equal ranks, and a perfect pairing between these summands is unique up to module isomorphism, by choosing dual bases and taking traces. For a paired orbit of two simple **matrix** factors in $D/J$, the action in one is arbitrary, with the action in the other given by the adjoint. Ordinary $R$-module multiplicities classify actions in the first factor.

Enumerate multiplicities $(n_\ell)$ with $\sum_\ell [E_\ell:K]n_\ell=m$, as well as the permitted discriminants for each positive-rank symmetric fixed summand. Construct the balanced forms just described, compare their underlying $K$-forms with the actual ambient $K$-form, and transport each compatible model's action by a computed isometry. The resulting list covers all residue embeddings up to residue unitaries, because an isomorphism of the modules with their balanced forms is exactly a unitary intertwiner. There are at most $2^{m+2g}$ trials in a matrix factor, and $g\le[K:F]$, so the product is $2^{O(\dim_F U)}$ by (4). If the common extension degree $a=[E_\ell:K]$ exceeds $m$, no unital action exists on this factor. Otherwise the fields used have size at most $p^{m[K:F]}\le |U|$. For example, factor the separable minimal polynomial of a generator of $k$ over $K$ by constructing a degree-$a$ finite field extension of $K$, enumerating its roots and grouping roots into $K$-Frobenius orbits. Constructing the extension by testing monic degree-$a$ polynomials and selecting an irreducible is also polynomial in $|U|$. A generator of $k/F$ can be found by enumerating $k$.

To lift a residue embedding, lift the self-adjoint image of a field generator by its separable minimal polynomial and §1.2. Two lifts $\rho_1,\rho_2$ of the same residue embedding have intertwiner
$$
g=\frac{1}{|k^\times|}\sum_{s\in k^\times}\rho_2(s)\rho_1(s)^{-1}.
$$
The denominator is invertible in $F$. This element is congruent to 1 modulo $J$, and reindexing shows it intertwines the two multiplicative actions, hence also the fields. Its unitary correction still intertwines. As every residue unitary lifts, the list contains a representative of every required conjugacy class.

### 1.5 One source factor

Let $b_i$ be one source factor, with coefficient field $k$ and $\dim_k W_i=d\le r$. Pick commutator values $w_j=b_i(x_j,y_j)$ forming a $k$-basis of $W_i$. Greedy linear independence succeeds because the commutator values span the output. For a nonzero target restriction $b:U\times U\to W$, a surjective pair $(A,B)$ satisfying (1) obeys
$$
\ker A=\operatorname{rad}(B b_i).
$$
Indeed surjectivity of $A$ lets one test against all vectors of $U$, and $b$ has common radical zero. The centroid identities show that each scalar in $k$ preserves $\ker A$. Thus the scalar action descends to a self-adjoint unital embedding $\rho:k\hookrightarrow\operatorname{Adj}(b)$.

Run the enumeration in §1.4. For each listed action, guess the at most $2r$ images $u_j=A x_j$, $v_j=A y_j$ in $U$. This determines $B$ on an $F$-basis of $W_i$ by
$$
 B(c_\ell w_j)=b(\rho(c_\ell)u_j,v_j),
$$
where the $c_\ell$ form an $F$-basis of $k$. This identity tests every candidate $B$ that can arise: conjugating $A$ by a target isometry leaves $B$ unchanged. In particular no action on $W$, or stability of $\ker B$ under scalars, is needed. Reject a guess if $B$ is nonsurjective. Pass $B b_i$ to its quotient by its common radical, and compare the resulting bimap with $b$ by simultaneous isometry of the ordered alternating matrix tuples in the same basis of $W$. Ivanyos–Qiao Theorem 7(1) provides the decision and a witness deterministically in time polynomial in the matrix sizes and $p$. The resulting quotient and isometry produce an actual map $A$. Its values on the guessed vectors need not be tested again, since checking (1) directly suffices. The zero target is served by the zero maps. The runtime is polynomial in the table sizes because there are at most $|U|^{2r}$ guesses. [Ivanyos–Qiao, Algorithms based on *-algebras, Theorem 7(1)](https://arxiv.org/pdf/1708.03495#page=6).

### 1.6 Assembly and runtime

The images of different $V_i$ in a surjective bimap morphism are mutually orthogonal by (3) and span $V_H$. Their sum is direct: an element of one summand that is in the sum of the others pairs to zero with each image and thus with all of $V_H$. Each nonzero image has zero common radical, so refine the decomposition into a fully refined orthogonal decomposition. Section 1.3 brings it by a fixed-output isometry to one of the enumerated frames.

For each enumerated target frame with $t$ summands, test each source factor against every subset of these summands by §1.5. The target subspace is their sum, with output space the span of its own commutators. These restrictions are full and common-radical-zero, since the ambient decomposition is orthogonal. Use a subset dynamic program that assigns each source factor a successful subset, disjoint from the subsets already used, and accepts when their union is the entire frame. Empty subsets are allowed. Each source factor requires at most $3^t$ transitions. A true surjection supplies such a partition by the preceding argument. Conversely an accepted partition gives maps $A_i:V_i\to U_i$ and $B_i:W_i\to \operatorname{span} b_H(U_i,U_i)$. They assemble to a surjective $A$ by the target decomposition and to a single $B$ by the independent source spaces $W_i$. The target output spaces may overlap, but together they span $W_H$, so $B$ is surjective. Orthogonality gives (1) and (2) gives the group map.

The size of $k$ is at most $|G|$ because it acts faithfully on a nonzero source space, and $p^v\le |H|$ for $v=\dim_F V_H$. There are at most $2^v$ target frame types, at most $2^v$ subsets per source factor, and $t\le v$. The local costs and the $3^t$ dynamic program are therefore bounded by $(|G|+|H|)^{O(r+1)}$. Every finite-field operation and table computation fits the same deterministic bit-time bound. This completes Theorem 1.

## 2. Exact genus two and finite local algebra quotients

**Theorem 2.** Fix an odd prime $p$. For every finite nonzero commutative local $F=\mathbb F_p$-algebra $R$ there is a stem class-two exponent-$p$ group $P(R)$ of exact BMW genus two, with $|P(R)|=|R|^5$. For all such $R,S$,
$$
P(R)\twoheadrightarrow P(S)
\quad\Longleftrightarrow\quad
R\twoheadrightarrow S\ \text{as unital }F\text{-algebras}.
$$
The construction is polynomial in the ring-table lengths. On this group family, the ring can also be recovered in time polynomial in the group table length.

Use the bimap
$$
b_R((x,y,z),(x',y',z'))=(xy'-yx',xz'-zx')
$$
from $R^3\times R^3$ into $R^2$. As a bimap over $F$ it is full and has common radical zero, by testing against the three coordinate vectors. Define $P(R)$ on $R^3\oplus R^2$ by adding inputs and placing $\tfrac12 b_R$ in the central product coordinate. Bilinearity gives the group law, the bracket is $b_R$, and the center equals the derived subgroup.

Every self-adjoint $F$-endomorphism $T$ of $b_R$ is $R$-linear. Indeed $b_R(T(rx),y)=b_R(rx,Ty)=r b_R(Tx,y)$ for all $y$, so the common radical condition gives $T(rx)=rT(x)$. If $e_1,e_2,e_3$ are the usual basis, then $b_R(Te_i,e_i)=0$ since $2$ is invertible. These identities force $Te_1=a e_1$ and the other two images to have zero first entry. Comparing $b_R(Te_1,e_j)=b_R(e_1,Te_j)$ for $j=2,3$ then gives $Te_j=a e_j$. Conversely scalar $a$ is self-adjoint and induces multiplication by $a$ on the output. The centroid is therefore precisely $R$, a local ring, and $\dim_{R/J(R)}R^2/J(R)R^2=2$. There is one directly indecomposable commutator factor.

A unital ring epi gives a group epi entrywise. Conversely a group epi gives surjective $A,B$ between the bimaps. The scalar action of $R$ descends through $\ker A=\operatorname{rad}(B b_R)$, by the centroid identity, to a self-adjoint unital $F$-algebra action on the target. The computation above identifies this action with a homomorphism $\alpha:R\to S$. For the two standard basis vectors $f_i$ in $R^2$, balancing gives $B(r f_i)=\alpha(r)B(f_i)$. Hence $S^2=B(R^2)$ has at most $|\alpha(R)|^2$ elements, forcing $\alpha(R)=S$. The ring is recoverable by solving the centroid equations and enumerating their solutions on the promised family. This uses $|R|=|P(R)|^{1/5}$ solutions, with addition and multiplication inherited from the representing matrices.

For example $R=F[\epsilon]/(\epsilon^2)$ has genus two by Definition 3.2, yet its commutator space has dimension four over its coefficient field. The two parameter bounds thus differ even for stem groups of prime exponent.

### Polynomial cases within this nonreduced family

Two unrestricted-in-dimension cases of the ring reduction can be decided directly.

1. **Bounded number of radical generators in the source.** For $R$ with maximal ideal $\mathfrak m$, lift a coefficient-field basis of $\mathfrak m/\mathfrak m^2$. The lifts generate $R$ over its coefficient field, since their degree-$j$ monomials span $\mathfrak m^j/\mathfrak m^{j+1}$ and the radical is nilpotent. Enumerate the image of one field generator and the images of the lifted radical generators in $S$. For each choice extend by evaluating representatives for a basis of $R$ expressed as monomials and verify multiplication on basis pairs, the unit and surjectivity. This takes polynomial time in the table lengths when the number of radical generators is bounded. It includes all finite commutative equicharacteristic local principal ideal rings, with no bound on nilpotence length.

2. **Square-zero radical in the target.** Any unital surjection $R\to S$ sends Jacobson radical onto Jacobson radical and induces an isomorphism of residue fields. If $J(S)^2=0$, the map factors through $R/J(R)^2$. The two resulting local rings are square-zero extensions of their coefficient fields. They admit a surjection exactly when these fields are isomorphic and the radical dimension of the source is at least the radical dimension of the target, after identifying the fields. A surjective linear map on radicals and a field isomorphism then give the epimorphism.

## 3. A nonreduced-source case with arbitrary centroid generator rank bound

**Corollary 3.** Fix $r$. In the setting of Theorem 1, suppose instead that each source factor has $W_i/J(C_i)W_i$ of dimension at most $r$ over $C_i/J(C_i)$. If the target adjoint algebra has no nonzero self-adjoint nilpotent, there is a deterministic polynomial-time epimorphism algorithm, even when the coefficient-field dimensions of the source factors are unbounded. The target condition is recognizable within the same time bound.

For any surjective bimap morphism, the source centroid action descends to the target restriction of each source factor as in §1.5. Any nilpotent in $C_i$ acts there by a self-adjoint nilpotent. Each restriction admits extension of its adjoints by zero to the whole target, because the images of the source factors form an orthogonal decomposition. The target hypothesis forces the descended action of $J(C_i)$ to vanish. Then $B_i(J(C_i)W_i)=0$, since elements of $W_i$ are sums of commutator values and scalar multiplication on these values can be carried to either input. Thus every relevant $B_i$ factors through $W_i/J(C_i)W_i$.

Replace each $b_i$ by its projection to $W_i/J(C_i)W_i$, compressed by the common radical. This radical is stable under the action of the coefficient field, so its quotient still has this field action. Zero factors can be omitted. The argument of §1.5 only needs the known field action on a source factor, so it applies to these compressed bimaps even if their full centroids change. Any solution on the compressed bimaps lifts to a solution on the given source by the quotient maps. Use (2) for the original groups, since vectors killed in the compression are still available for the map to the extra center. The subset algorithm of §1.6 completes the test.

To decide the target condition, first compute the self-adjoint subspace $J^+$ of its adjoint radical by linear equations. Every member of that subspace is nilpotent. If $J^+=0$, it remains to test the semisimple quotient, since a self-adjoint residue element can be lifted by averaging, and a lift of a nilpotent is nilpotent. In a paired orbit of two matrix factors, there is a nonzero self-adjoint nilpotent exactly when the matrix size exceeds one. One may pair any nonzero nilpotent with its adjoint. In a symmetric or Hermitian factor, a nonzero self-adjoint nilpotent exists exactly when the form has a nonzero isotropic vector. Such a vector $u$ produces the nilpotent $x\mapsto h(x,u)u$; conversely for a self-adjoint nilpotent $N$ of index $m\ge2$, a nonzero $N^{m-1}x$ is isotropic by adjointness. In a symplectic factor, in dimension two the self-adjoint subspace consists of scalars. In higher dimension an independent isotropic pair $u,v$ gives $x\mapsto h(x,u)v-h(x,v)u$, a nonzero self-adjoint endomorphism with square zero. These tests can enumerate vectors in one simple module at a time, whose size is at most $|V_H|$ by (4).

## 4. The literal genus-two promise encodes unrestricted epimorphism

**Theorem 4.** Fix an odd prime $p$ and a positive integer $r$. For groups given by Cayley tables, the epimorphism problem for class-at-most-two groups of exponent dividing $p$ is polynomial-time many-one equivalent to the restriction in which both groups are stem and have exact genus $r$ as defined in BMW Definition 3.2. The reduction is uniform in $p$ for fixed $r$. In particular, $r=2$ gives the problem in Open Question 3(3) on its odd prime-exponent subclass. The same phenomenon already occurs at $r=1$.

Let $b:V\times V\to W$ be a full alternating bimap over $F=\mathbb F_p$ with common radical zero. Allow $V=W=0$. Form the commutative local ring $C=F\oplus W$ with square-zero ideal $J=0\oplus W$ and multiplication
$$
(a,w)(a',w')=(aa',aw'+a'w).
$$
Write $t=(x,y_1,\ldots,y_r)\in C^{r+1}$. Give $C^{r+1}\oplus V$ the alternating bimap $\widehat b$ with output $C^r$ defined by
$$
\widehat b((t,v),(t',v'))=(xy'_j-y_jx')_{j=1}^r+(b(v,v'),0,\ldots,0).
\tag{5}
$$
The last term uses $W=J\subset C$. The first term spans $C^r$ and has zero common radical on the marker coordinates $C^{r+1}$. The second term has zero common radical on $V$, and the cross terms vanish. Hence $\widehat b$ is full and has common radical zero. Scalar $C$ acts on $V$ through the residue $C\to F$, and gives a centroid action on all of (5).

The centroid is exactly that copy of $C$. To see this, compress the input endomorphism of a centroid element to the marker summand $C^{r+1}$. On the marker the resulting map is self-adjoint because marker and $V$ are orthogonal. The basis argument in Theorem 2 works with all $r+1$ coordinate vectors: each self-adjoint map is $C$-linear; its first column is a scalar multiple of the first basis vector; all other columns have zero first entry, and pairing them with the first basis vector forces the remaining block to be the same scalar matrix. This covers $r=1$ as well. The marker spans all $C^r$, so the output component of the original centroid element is multiplication by that scalar. The zero common radical of the entire bimap forces its input component to be the scalar action already constructed. The maximal ideal is $J$ and the output module is $C^r$. Thus there is one directly indecomposable factor and its genus is precisely $r$. The group built from (5) by the half-bracket formula is stem and has exponent $p$.

Here is how to recover the original bimap from (5) in a way that works through surjections. For an $F$-linear functional $\lambda$ on $C^r$, the scalar alternating form $\lambda\widehat b$ has rank at most two exactly when $\lambda$ annihilates $J^r$, with $J^r$ here denoting the direct product of $r$ copies of the ideal $J$. One implication follows by reducing the marker coordinates modulo $J$: the resulting form is the wedge of the $x$ coordinate with a single linear combination of the $y_j$'s. For the converse, choose a coordinate $j$ and $w\in J$ with $\lambda_j(w)\ne0$ if $\lambda$ does not annihilate those radical coordinates. The scalar form on the span of $1,w$ in each of the $x,y_j$ coordinates has an off-diagonal block
$$
\begin{pmatrix}\lambda_j(1)&\lambda_j(w)\\
\lambda_j(w)&0\end{pmatrix},
$$
which is invertible. The alternating form has rank at least four. Consequently the rank-at-most-two locus is exactly an $r$-dimensional subspace of the output dual. Its common radical in the input is $J^{r+1}\oplus V$, where the power likewise denotes a direct product. Restrict (5) to that common radical. The bracket then spans precisely $W$ in the first output coordinate, since all products of two elements of $J$ vanish. The common radical of the restriction is exactly $J^{r+1}$. Quotienting by this space gives back $b$.

Suppose a surjective pair $(\widehat A,\widehat B)$ maps $\widehat b$ onto $\widehat b'$. The injective dual map $\widehat B^*$ preserves the rank of scalar forms, because $\widehat A$ is surjective. Therefore it takes the distinguished $r$-dimensional subspace of the target dual onto the corresponding subspace of the source dual. Consequently the preimage under $\widehat A$ of the target common radical of those forms is the source common radical. The restriction of $\widehat A$ between these two subspaces is surjective. This restricted surjection preserves the bracket via the restriction of $\widehat B$, which is onto the span of the restricted brackets. It maps the radical of the restricted source bracket into the radical of the restricted target bracket. We obtain the required pair of surjections on the recovered original bimaps. Conversely, a surjective $A:V\to V'$, $B:W\to W'$ preserving the original brackets extends on the marker coordinates by the surjective algebra map $(a,w)\mapsto(a,Bw)$. It extends on $V$ by $A$, so it gives a surjective pair for (5).

For input groups $G,H$, first perform the abelianization test (2). If it fails, return any explicit no instance of exact genus $r$, for example the marker group with input ring $F$ followed by the larger marker group with ring $F[\epsilon]/(\epsilon^2)$. Otherwise build (5) for $b_G,b_H$. The stem groups of their new bimaps admit an epimorphism exactly when the bimaps admit one, and the preceding paragraph together with (2) proves the many-one reduction. The new group has order $|C|^{2r+1}|V|$ with $|C|=p|W|$, polynomial in the original group order for fixed $r$, and its entire Cayley table can be produced within that budget up to a fixed polynomial factor. The reverse reduction simply treats the restricted instances as unrestricted instances. This proves Theorem 4.

The same construction transfers unrestricted isomorphism of these exponent-$p$ groups to exact genus $r$ isomorphism. First check that orders, center orders and derived orders agree. The marker groups then have equal order, so their epimorphisms are exactly their isomorphisms. Treat a failed preliminary test by returning a fixed nonisomorphic pair in the promised class.

## 5. The same reduction retains power maps in special groups

**Corollary 5.** Fix $r\ge1$ and a prime $p$, including $p=2$. On finite class-two $p$-groups $X$ with $Z(X)=X'$, and with both $X'$ and $X/Z(X)$ elementary abelian, epimorphism reduces in polynomial Cayley-table time to the exact-genus-$r$ restriction of the same class. In odd characteristic these groups may have exponent $p^2$. In characteristic two they may have exponent four.

Write $q_X:V_X\to W_X$ for the $p$-th power of a lift of each vector. It is well defined because $W_X$ is central of exponent dividing $p$. For odd $p$ it is linear by the class-two power identity. For $p=2$ its polar form is $b_X$. A group epimorphism gives surjective maps $A,B$ preserving both brackets and powers. Conversely such maps give a group epimorphism. To see this choose basis lifts for $V_X$, send them to lifts of their prescribed images, and map the center by $B$. The power and commutator relations on basis lifts, with the relations of $W_X$, present the group: collecting these relations leaves at most $|V_X||W_X|$ words, and they already give a surjection onto a group of that order.

Use the same bimap (5). At $p=2$ the centroid calculation uses $b(Te_i,e_i)=0$ for the full centroid identity: a centroid element sends $b(e_i,e_i)=0$ to $b(Te_i,e_i)$. Its compression to the marker is therefore scalar by the same coordinate argument, without dividing by two. The rank-marker argument is valid in every characteristic. Prescribe powers on the new domain by
$$
\widehat q((x,y_1,\dots,y_r),v)=
\begin{cases}
 (q_X(v),0,\ldots,0), & p\ \text{odd},\\
 (xy_j)_{j=1}^r+(q_X(v),0,\ldots,0), & p=2 .
\end{cases}
$$
The even-characteristic expression is quadratic with polar form (5). On the distinguished subspace $J^{r+1}\oplus V_X$ its marker term vanishes, since the ideal $J$ is square-zero. Thus, in both cases, restricting to that subspace and taking its common-radical quotient recovers $q_X$. The recovery under an epimorphism in Theorem 4 now also recovers a pair preserving powers. Conversely the extension by $(a,w)\mapsto(a,Bw)$ preserves the displayed power map. The bracket and power characterization then gives the two directions of the group reduction.

For explicit tables, one can construct any bracket and compatible power data above as follows. For an ordered basis $e_i$ of the input space, and vectors $x,y$ in basis coordinates, form the central cocycle
$$
c(x,y)=\sum_i\left\lfloor\frac{\widetilde x_i+\widetilde y_i}{p}\right\rfloor q(e_i)
           +\sum_{i>j}x_i y_j b(e_i,e_j),
$$
where tildes denote representatives in $\{0,\ldots,p-1\}$. The first term consists of the usual addition carries for $\mathbb Z/p\mathbb Z$, and the second is bilinear. Both satisfy the additive cocycle identity. Use multiplication $(x,z)(y,w)=(x+y,z+w+c(x,y))$. The commutator is $b$ and the basis powers are $q(e_i)$, which determine all powers by linearity or polarization. Fullness and zero common radical give center equal to the derived subgroup and the stated element count. This makes the table construction polynomial for fixed $r$.

## Relation to the literature

Brooksbank–Maglione–Wilson solve isomorphism in the field-based genus-two setting. Schrock studies isomorphism **among** quotients of genus-two groups, including field recovery from a raw quotient and descent to genus-one quotients for certain kernels. Theorem 1 addresses the two-input search problem of finding an epimorphism from a specified source. It keeps the fixed-output isometry test of the earlier [MathProofs epimorphism counting proof](../GroupEpimorphismCounting/PROOF.md) and replaces exhaustive search over output maps by a complete list of field actions in the target adjoint algebra. Recent finite-ring isomorphism algorithms also address isomorphism, which alone supplies no algorithm for locating a kernel with a specified quotient. Theorem 2 transfers finite local ring epimorphism to the literal genus-two question even with both groups stem. General groups of literal genus two, including nonreduced centroids of unbounded coefficient-field dimension, remain outside the proof of Theorem 1. [Schrock, On the Complexity of Isomorphism in Finite Group Theory, chapter 4](https://math.colorado.edu/~tysc3584/Tyler_Schrock-PhD_Thesis.pdf). [On Applications of Polynomial-Time Group Isomorphism Algorithm](https://arxiv.org/abs/2611.18084).

The rank marker uses only scalar form rank and common radicals. This gives the equivalence in Theorem 4 without relying on a group or ring isomorphism runtime claim. These arguments are informal. See also the [power-map and nonreduced-centroid extensions](POWER-MAPS.md), the [Heisenberg quotient algorithm](HEISENBERG.md), and the [local-ring quotient algorithm](LOCAL-RINGS.md).
