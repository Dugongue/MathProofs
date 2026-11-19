# All attainable modular Hom-count profiles for modules and graphs

Fix a finite field of order $q=p^e$. Let $M,N$ be finite-dimensional modules over one associative unital algebra over this field. For every positive integer $m$, write $E_m(M,N)$ when all finite-dimensional probe modules $X$ have the same number of maps to $M$ and to $N$ modulo $m$. The maps are module homomorphisms. Matrix tuples under simultaneous similarity are included by using the free algebra on the tuple indices. Representations of a quiver with relations and representations of a fixed finite group are also included.

**Classification.** For isomorphic targets all propositions $E_m$ hold. For every other pair there are integers $a\ge0$ and $b\ge1$ such that, simultaneously for every $m$,
\[
 E_m(M,N)\quad\Longleftrightarrow\quad m\mid q^a(q^b-1).
\]
Every such pair of parameters is attained by two equal-dimensional diagonalizable single matrices with eigenvalues in $\{0,1\}$. If $n=\dim M+\dim N$, probes of dimension at most $(n^4+1)n$ already determine all the propositions.

Here is the structural information in the exponent $b$. For each isomorphism type $U$ of indecomposable summand, let $r_U(Y)$ be its multiplicity in $Y$ and let $d_U$ be the dimension of the residue division algebra of $\operatorname{End}(U)$ over the ground field. Then
\[
 b=\gcd_U |d_U(r_U(M)-r_U(N))|.
\]
For $m$ coprime to $q$, one can read a particular $E_m$ directly from the decompositions. Each multiplicity difference must vanish modulo $\operatorname{ord}_m(q)/\gcd(\operatorname{ord}_m(q),d_U)$. The convention is $\operatorname{ord}_1(q)=1$.

### Extracting the integer gcd from a finite set of probes

Write $h_X(Y)=\dim\operatorname{Hom}(X,Y)$ and $D_X=h_X(M)-h_X(N)$. Krull–Schmidt gives the finite list of indecomposable types in $M\oplus N$. The endomorphism algebra of an indecomposable is local. Its sole simple module has ground-field dimension $d_U$. By postcomposition, $\operatorname{Hom}(X,U)$ is a finite-dimensional module over that algebra, so its dimension is divisible by $d_U$. Additivity over the target decomposition now proves $b\mid D_X$ for every $X$.

For the converse, fix a type $U$ in the list. For each listed type $V$ take a ground-field basis of the radical maps $U\to V$. For $V\not\simeq U$ this space is all maps. For $V=U$ it is the Jacobson radical of $\operatorname{End}(U)$. Assemble these maps as the coordinates of a single map $s:U\to B$, with one copy of $V$ in $B$ per basis vector. Put $C=\operatorname{coker}(s)$.

For $Y=M,N$, precomposing maps $B\to Y$ with $s$ realizes exactly the radical maps $U\to Y$. In each indecomposable coordinate of $Y$, every radical map is a linear combination of the chosen basis and extends using the matching summands of $B$. Conversely compositions of these maps stay radical. In particular, a composition $U\to V\to U$ with nonisomorphic indecomposables cannot be invertible, since invertibility would split off $U$ from $V$. Thus the cokernel of precomposition has dimension $d_U r_U(Y)$. Its kernel is $\operatorname{Hom}(C,Y)$ by the cokernel property. Taking dimensions and subtracting gives
\[
 d_U(r_U(M)-r_U(N))=D_U-D_B+D_C.
\]
The targets are nonisomorphic, so some such expression is nonzero. This proves $b=\gcd_X |D_X|$ and shows that finitely many probes already attain that gcd collectively. Each $B$ has dimension at most $\dim U\sum_V (\dim V)^2\le n^3$, and $C$ is a quotient of $B$. The argument works also when the original acting algebra has infinite dimension, because it uses only Hom spaces and the displayed finite list of summands.

### Recovering the entire integer profile

Define $a$ to be the smallest $\min(h_X(M),h_X(N))$ over probes with $D_X\ne0$. For each such probe the absolute difference of the two cardinalities is
\[
 q^{\min(h_X(M),h_X(N))}(q^{|D_X|}-1).
\]
The second factor is coprime to $p$. Thus the $p$-primary part of the gcd of all cardinality differences is $q^a$. Its prime-to-$p$ part is $q^b-1$ by the Euclidean identity $\gcd(q^i-1,q^j-1)=q^{\gcd(i,j)}-1$. This proves the classification.

For the probe bound, the preceding probes of dimension at most $n^3$ give at least one nonzero difference, hence $a\le n^4$. In a minimizing probe $X$, interchange targets to make $h_X(M)=a<h_X(N)$. Map $X$ to the direct sum $M^a\oplus N^{a+1}$ by a basis of maps to $M$ and any $a+1$ independent maps to $N$. Use its image as a new probe $X'$. Pullback along $X\twoheadrightarrow X'$ is injective on maps to either target. Its image contains the chosen maps, so $h_{X'}(M)=a$ and $h_{X'}(N)\ge a+1$. This realizes the minimum in the asserted dimension. This witness-size bound does not bound the number of probes one might try to find it.

### Realizability and exact implication tests

For any $a,b$ use one linear operator on each target. In $M$ the multiplicities of the eigenvalues $0,1$ are $a,a+b$. Swap the multiplicities in $N$. For any probe the dimensions of maps to the two one-dimensional eigenspaces are two nonnegative integers $u,v$. The target Hom dimensions are $a(u+v)+bv$ and $a(u+v)+bu$. Hence every nonzero difference has smaller dimension at least $a$ and exponent difference divisible by $b$. The one-dimensional zero-operator probe gives $u=1,v=0$ and attains both bounds. This proves realizability in equal dimension.

For each modulus split $m=p^{v_p(m)}m'$ with $p\nmid m'$. For a finite set $S$ of positive assumptions $E_m$, let
\[
 A=\max_{m\in S}\lceil v_p(m)/e\rceil,\qquad
 B=\operatorname{lcm}_{m\in S}\operatorname{ord}_{m'}(q),
\]
using $A=0,B=1$ for the empty set. The implications valid over *all* module pairs are exactly
\[
 \bigwedge_{m\in S}E_m\ \Longrightarrow\ E_r
 \quad\Longleftrightarrow\quad r\mid q^A(q^B-1).
\]
The pair realizing $(A,B)$ proves the converse and simultaneously falsifies every conclusion outside this list. Thus any finite pattern of required agreements and disagreements is realizable precisely when none of its required disagreements divides the displayed integer. This proves actual mathematical realizability of the surviving patterns.

For example over the binary field, agreements modulo $3$ and $7$ together force agreement modulo $9$, in fact modulo $63$. The orders of $2$ modulo $3,7,9$ are $2,3,6$. Neither premise alone forces the conclusion. Over the field with four elements, universal agreement modulo $2$ is equivalent to agreement modulo $4$ because the characteristic-primary exponent changes in steps of two. Also on inputs of dimension at most $n$ per target, any $m$ coprime to $q$ with $\operatorname{ord}_m(q)>n$ gives a complete isomorphism test when *all probes* are available: $d_Ur_U(Y)\le\dim Y$ follows by applying the endomorphism action to $U$ itself. The two-eigenvalue examples with $a=0$ show this threshold is sharp across algebras.

### Sharp precision for full isomorphism detection

For each fixed $q$, a single modulus of numerical size $O_q(n)$ suffices to distinguish every pair of nonisomorphic targets of dimension at most $n$ by a polynomial-dimensional probe. Conversely, any single modulus with this universal property has size $\Omega(n)$, already for single matrices of equal dimension. Thus the optimal number of bits per returned count is $\log_2 n+O_q(1)$.

For the upper bound, fix any odd prime $\ell$ not dividing $q$, let $u=\operatorname{ord}_\ell(q)$ and $c=v_\ell(q^u-1)$. The binomial expansion gives $v_\ell((1+z)^\ell-1)=1+v_\ell(z)$ when $z$ is divisible by $\ell$; raising $1+z$ to a power prime to $\ell$ preserves that valuation. Consequently $\operatorname{ord}_{\ell^{c+j}}(q)=u\ell^j$ for $j\ge0$. Choose the first $j$ giving order greater than $n$. The resulting modulus is $O_q(n)$ and the preceding multiplicity test is complete. For this coprime modulus the three-probe construction needs dimension only $O(n^3)$.

For the lower bound, write an arbitrary candidate modulus $m=p^v m'$ with $p\nmid m'$. The diagonal pair realizing $a=\lceil v/e\rceil$ and $b=\operatorname{ord}_{m'}(q)$ agrees at modulus $m$. Its targets are nonisomorphic and have equal dimension $2a+b\le 2\log_2(m)+m$ for $m\ge2$, since $\lceil v/e\rceil\le v\le\log_2 m$. The modulus $1$ distinguishes nothing. Hence a modulus $o(n)$ cannot have the universal property. The number of possible probes may be large; this precision bound measures the number of bits needed in each answer.
### A deterministic raw-input algorithm for the first characteristic precision

For $m=p$ a Hom count is one or zero modulo $p$ according as its dimension is zero or positive. On matrix tuples the universal comparison can be decided in deterministic polynomial time and an explicit distinguishing probe returned on failure. The same holds for every $m=p^j$ with $1\le j\le e$.

Starting with $R=N$, compute the simultaneous intertwiner space $\operatorname{Hom}(R,M)$ by linear equations. Replace $R$ with the intersection of the kernels of a basis of this space and repeat. If a nonzero $R$ fails to shrink, it has zero Hom space to $M$, and its inclusion in $N$ supplies a nonzero map to $N$. This witnesses disagreement. If the iteration reaches zero, it supplies a filtration of $N$ in which each successive quotient embeds into a direct sum of copies of $M$ by the coordinate basis maps. For any nonzero map $X\to N$, choose the last filtration term containing its image. Composing to that successive quotient and then to an appropriate copy of $M$ gives a nonzero map $X\to M$. Thus the zero outcome certifies one implication on all probes. Interchanging $M,N$ gives the other. The residuals are invariant subspaces obtained in at most $\dim M+\dim N+2$ passes across the two runs. Basis changes, restrictions of the named matrices, intersections of kernels, and Hom-space bases all use ordinary polynomial-size linear algebra. This computation is an effective version of the standard Hom-orthogonality characterization of torsion-free classes in finite-length module categories.
**Relation to earlier results.** Recovering multiplicities from Hom dimensions is established representation theory. Dowbor and Mróz give the pertinent weighted multiplicity formula using Auslander–Reiten theory. The proof here supplies pair-dependent finite probes by elementary linear algebra and derives the cardinality gcd, complete modular implication test, and equal-dimensional realizations. Publication priority for these modular consequences remains unverified. The theorem applies to linear representations with their usual morphisms. Arbitrary three-tensor isomorphism remains outside the proved scope. The proof is informal. [Dowbor and Mróz, Colloquium Mathematicum 107 (2007)](https://doi.org/10.4064/cm107-2-4)

### Graphs realize the ordinary divisibility lattice

For finite simple graphs interpret $E_m$ using graph homomorphisms from all finite simple source graphs. Every positive integer $L$ occurs as the exact gcd of the cardinality differences, even for targets on the same $7L+1$ vertices that are connected, have diameter two, and become forests when one vertex is removed. Consequently the only universal joint implications for these graphs are $\bigwedge_{m\in S}E_m\Rightarrow E_r$ with $r\mid\operatorname{lcm}(S)$. This differs from the binary-module implication from $3,7$ to $9$.

Take the seven-vertex tree $T$ with one central vertex and three branches of lengths $1,2,3$. Let $H$ be obtained by deleting one edge and keeping all vertices. The difference in homomorphism counts from a single edge is two. There is exactly one injective endomorphism of $T$, since the central vertex and the three length-distinguished branches are fixed. There is no injective homomorphism from $T$ to $H$, which has too few edges. By inclusion-exclusion on equalities of source vertices, each injective homomorphism count is an integral linear combination of homomorphism counts from quotients of the same source. Loop-containing quotients give zero and parallel edges can be merged. The gcd for $T,H$ therefore divides one.

Take the disjoint union of $L$ copies of each target. For each nonempty connected probe its count scales by $L$. The gcd over connected probes already equals the gcd over all probes, since counts for a disconnected probe are products over its connected components and the difference of products is an integer combination of differences of factors. The gcd after this operation is exactly $L$.

Finally adjoin one new universal vertex to each target. For any probe $F$ and any target $Y$,
\[
 \operatorname{hom}(F,\operatorname{cone}(Y))
 =\sum_{I\subseteq V(F)\text{ independent}}\operatorname{hom}(F-I,Y).
\]
Here $I$ is the full preimage of the new vertex. The term for $I=\varnothing$ is the original count, and all other probes have fewer vertices. Integer induction in both directions shows this operation preserves the gcd. Both resulting graphs have the stated size, diameter and feedback-vertex property. The pair realizing $L=\operatorname{lcm}(S)$ simultaneously rules out all further conclusions. The source quotient identity and prime-modulus homomorphism profiles are classical; priority for the realization within this restricted target family has not been established. [Faben and Jerrum, modular Lovász vectors](https://arxiv.org/abs/1309.4033)