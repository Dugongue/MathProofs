# Exponential dimension lower bounds for coherent determinant markers

Fix a finite field $F=\mathbb F_q$ with $q>2$, a tensor order bound $d\ge3$, and integers $n_1,\ldots,n_k$ with $n_i>d$ and $n_i\ge5$. Put $V_i=F^{n_i}$ and $r_i=\lceil n_i/d\rceil$. The following is a lower bound on fixed, coherent marker constructions. The three determinant tier comparisons are among its applications. All assertions are informal.

A marker consists of a finite list of spaces $W_\ell$ and fixed tensors of order at most $d$ in their mixed tensor products. Dual factors are allowed, as are any number of fixed tensors and any number of spaces. An automorphism is a tuple of invertible linear maps on the $W_\ell$ preserving the tensors. Each original mode $V_i$ is a distinguished space or a distinguished subquotient of one of the spaces, preserved by the automorphisms under consideration. Assume a homomorphism from $\prod_i\mathrm{SL}(V_i)$ into the marker automorphism group induces its usual independent standard maps on the $V_i$. This is the coherent-lift hypothesis.

Impose $s<k$ determinant-one restrictions on physical spaces or invariant subquotients of the marker. If the resulting automorphisms project onto exactly $\prod_i\mathrm{SL}(V_i)$ on the original modes, then some marker space has dimension at least
$$
\min_i\frac{1}{q-1}\binom{n_i}{\lceil n_i/d\rceil}.
$$
Here invariant subquotients must be preserved by the full marker automorphism group, or may simply be specified by a marked invariant flag. At fixed $q,d$ the bound is exponential in the smallest protected dimension. It applies to dropping one determinant test from one, two, or three in this model, including over $F_3$. It requires neither semisimplicity for the special linear group nor an a priori lift of the ordinary general linear action.

## 1. Low-dimensional representations extend across the determinant

First consider one mode of dimension $n$. Write $r=\lceil n/d\rceil$ and $m=q-1$. Write $D=(F^\times)^n$ for the full diagonal group and $D_0$ for its determinant-one subgroup. Since $D_0$ is abelian of order prime to the characteristic and all its character values lie in $F$, its action on any $F$-linear representation has a decomposition into simultaneous weight spaces. Its characters are represented by vectors of exponents in $(\mathbb Z/m)^n$, modulo adding a common exponent to all coordinates.

We show that any character occurring in a representation of $\mathrm{SL}_n(F)$ of dimension less than $\binom nr/m$ has a unique representative with fewer than $r$ nonzero coordinates. Every coordinate permutation acts on the $D_0$ weights, since a permutation matrix can be multiplied by a diagonal matrix to give determinant one without changing its conjugation action on $D_0$. Hence the orbit of each occurring weight consists entirely of occurring weights, and its cardinality is at most the representation dimension.

Suppose no exponent value occurs more than $n-r$ times in some exponent representative. The coordinates can be grouped into its exponent classes. Some union of classes has size $a$ with $r\le a\le n-r$. Indeed, if one class is in that interval it suffices. Otherwise all classes have size below $r$, and adding classes until the size first reaches $r$ gives size at most $2r-2\le n-r$. In the full permutation orbit of the exponent vector, the union can be sent to every $a$-subset, and distinct positions of the selected exponent values give distinct vectors. Thus the orbit has at least $\binom{n}{a}\ge\binom nr$ vectors. Quotienting by common shifts identifies at most $m$ such vectors, a contradiction. There is therefore a unique exponent value of multiplicity greater than $n-r$, since $r\le n/2$. Subtract that value to obtain the required representative. Call this the normalized weight.

On the weight space of normalized weight $\chi$ define the action of $u\in D$ to be multiplication by $\chi(u)$. The resulting $D$ action extends the old diagonal action. To see it is compatible with the $\mathrm{SL}_n(F)$ action, take $x_{ij}(a)=I+aE_{ij}$. It commutes with every member of $D_0$ whose $i$-th and $j$-th entries agree. Therefore any nonzero matrix block of $x_{ij}(a)$ between weights $\chi,\psi$ has weight difference, modulo common shifts, a multiple of $e_i-e_j$. Indeed the map taking the ratio of those two entries is onto $F^\times$ on $D_0$ for $n\ge3$, and the difference character is trivial on its kernel.

Both normalized weights have fewer than $r$ nonzero coordinates. Thus the representative difference has at most $2r-2<n-2$ nonzero coordinates, the last inequality holding for $n\ge5,d\ge3$. There is a zero outside $i,j$, so the common shift in the difference must vanish. It follows that the full-diagonal character quotient of every nonzero block depends only on the ratio of the $i$-th and $j$-th diagonal entries. Given $u\in D$, choose $v\in D_0$ with that same ratio. The new action of $u v^{-1}$ commutes with $x_{ij}(a)$ because the weight quotient on each nonzero block is one. Consequently conjugating the representation of $x_{ij}(a)$ by the new action of $u$ has exactly the same effect as the original conjugation by $v$, namely replacing $a$ by $(u_i/u_j)a$.

The elementary transvections generate $\mathrm{SL}_n(F)$. Let $\zeta$ generate $F^\times$ and take $u=\operatorname{diag}(\zeta,1,\ldots,1)$. Its new action has order dividing $m$ and implements the correct conjugation on the entire special linear group by the transvection calculation. Since $\mathrm{GL}_n(F)=\mathrm{SL}_n(F)\rtimes\langle u\rangle$, this defines an extension to a representation of $\mathrm{GL}_n(F)$. Every $\mathrm{SL}_n(F)$-invariant subspace and quotient is preserved by the new action: it is preserved by each $D_0$ weight projector, and the new diagonal is scalar on each projected space. The action on any distinguished standard subquotient is the standard $\mathrm{GL}_n(F)$ action because its normalized weights are exactly the coordinate weights. The same assertion for a distinguished space treated independently of the size bound follows directly from its standard action. Trivial actions of other factors likewise extend trivially.

## 2. Bounded-order invariants survive the extension

Consider a tensor product with at most $d$ ordinary or dual factors, each carrying the preceding extended action. Each weight of its full diagonal action is a sum of at most $d$ normalized weights or their negatives. Thus it has at most $d(r-1)<n$ nonzero coordinates. A tensor fixed by the original $\mathrm{SL}_n(F)$ action can have components only in the weights trivial on $D_0$. An exponent vector trivial on $D_0$ has all entries equal. Since the support is proper, these entries are all zero. The extra diagonal therefore fixes the tensor. The special linear group together with that diagonal generates the full general linear group, so every fixed marker tensor continues to be fixed.

Apply this argument to every protected factor $i$. The resulting general linear actions commute. Each extra diagonal is a combination of the weight projectors for its own $D_{0,i}$, so it commutes with the original actions of all other special linear factors and their diagonal weight projectors. The full product $\prod_i\mathrm{GL}(V_i)$ therefore acts inside the automorphism group and acts naturally on the distinguished subquotients.

## 3. Fewer output determinants cannot enforce all the source determinants

Each surviving determinant test on a physical marker space or invariant subquotient gives a homomorphism from the extended product group to $F^\times$. It is trivial on the product of special linear groups. Indeed each special linear factor is generated by elementary transvections whose order equals the characteristic, and that prime does not divide $q-1$. Those determinant tests jointly factor through a homomorphism
$$
(F^\times)^k\longrightarrow(F^\times)^s.
$$
Since $s<k$ and $q>2$, its kernel contains a nonidentity element. A product of general linear maps with that source determinant vector thus preserves every marker and obeys every surviving determinant-one test, yet is forbidden by the original restriction. This proves the lower bound. There is no involvement of tensor orbit counting or a semisimplicity assumption for the special linear group itself.

## 4. Matching size in the single-mode marker model

The lower bound for one source mode is sharp up to the factor $q-1$. Set $r=\lceil n/d\rceil$. Use typed spaces $\Lambda^j V$ for $1\le j\le r$ and the wedge maps
$$
V\otimes\Lambda^{j-1}V\longrightarrow\Lambda^jV,\qquad 2\le j\le r.
$$
Their images span every exterior grade, so any automorphism on the system is induced by its standard-space map $g$ through the exterior powers. Choose nonnegative integers $a_1,\ldots,a_d\le r$ summing to $n$. Mark the nonzero $d$-ary volume obtained by wedging grades $a_1,\ldots,a_d$ against the chosen coordinate volume. A factor of grade zero means a fixed scalar factor and can be omitted. The volume survives precisely for $\det(g)=1$. The largest space dimension is $\binom nr$. Every determinant-one map extends by its exterior powers. This is a size comparison for the stated tensor-system marker model.

These results quantify why attaching a fixed bounded-order marker with compatible witness extensions cannot give any of the three polynomial-time collapses. A general polynomial-time many-one reduction can use both tensors jointly, change the underlying spaces with the entries, and avoid lifting witnesses altogether. The result leaves those reductions unresolved. A previous project proof used characteristic-zero central characters for a related marker barrier. The argument here uses only finite-field diagonal weights and elementary matrices.
