# From Pauli mutually unbiased bases to ordinary class-two group isomorphism

**Theorem.** For every odd prime $p$, unitary equivalence of complete Pauli mutually unbiased bases in dimension $d=p^n$ reduces to ordinary isomorphism of explicitly presented special class-two, exponent-$p$ groups. The construction accepts exact orthoframes of the promised Pauli type without supplied spread or group labels. One group automorphism count also gives the number of projective unitary automorphisms of the input family by an explicit normalization. The output is a polynomial-size commutator tensor or power-commutator presentation.

The proof combines two reductions. A pair of orthoframes recovers the underlying symplectic spread. A central extension remembers that unordered configuration through its intrinsic contraction ranks. Three auxiliary lines force the exact projective square class needed for unitary equivalence. The proofs are informal. The finite checks below are independent of the proofs.

## 1. Recover the spread from the given rays

Use the following input model. The bases are unordered orthoframes, each an unordered set of one-dimensional complex subspaces, with exact vector representatives over a common explicitly represented number field containing a specified complex primitive $p$th root $\zeta$. Assume a promise of Pauli type. This means there is a projective Weyl group $P\cong\mathbb F_p^{2n}$ with representatives satisfying the central commutator law
$$
D_xD_yD_x^{-1}D_y^{-1}=\zeta^{\omega(x,y)}I
$$
for a nondegenerate alternating form $\omega$, and the frames are the simultaneous eigenrays of the preimages of the members of a symplectic spread $\mathcal S$. A spread has $m=p^n+1$ pairwise complementary Lagrangians and partitions the nonzero symplectic vectors. The same complex root $\zeta$ is used for both input families. [Kantor, Theorem 2.3 and Section III](https://arxiv.org/abs/1104.3370), [Abdukhalikov, Sections 2–3](https://arxiv.org/abs/1306.3478).

Choose two frames $A,B$ and one $B$-ray $b_0$. Write representatives of all $B$-rays in $A$-coordinates. Every coordinate is nonzero by mutual unbiasedness. For each $B$-ray $b_j$, take the diagonal matrix with entries $(b_j)_i/(b_0)_i$. Its projective class is the unique diagonal projective operator in $A$-coordinates carrying $b_0$ to $b_j$.

These classes are exactly the projective Weyl subgroup $L_A$ belonging to $A$. Indeed, for any $B$-ray $b$, if $D_x$ fixes it, the commutator law with each $D_y$ for $y\in L_B$ implies $\omega(x,y)=0$. Thus $x\in L_B^\perp=L_B$, and every $x\in L_B$ fixes the ray. The stabilizer of $b$ in $P$ is therefore $L_B$. Its intersection with $L_A$ is zero, so $L_A$ of size $d$ acts freely and transitively on the $d$ rays of $B$. Its elements are diagonal in $A$ and exhaust the prescribed diagonal classes. Reverse $A,B$ to obtain $L_B$. Their products give all $d^2$ classes of $P$, which is therefore independent of the chosen pair of frames.

Normalize a representative of each projective matrix by a nonzero entry to compare classes and compute their product table exactly. This recovers $P$ as an elementary abelian $p$-group. Choose a vector-space basis by growing the spans in that table. Commutators of matrix representatives recover $\omega$ by comparing their scalars to the powers of $\zeta$. For each frame use the set of projective operators fixing every ray in the frame. The same stabilizer argument recovers its Lagrangian. These operations take polynomially many exact arithmetic operations in the input dimensions. The bit-time assertion uses a common number field given by an explicit defining polynomial and exact coordinates, with its standard exact arithmetic. No numerical tolerance or recovery of arbitrary unknown phases is required.

Any unitary equivalence carries the recovered $P$ to $P'$ and fixes the scalar $\zeta I$, so induces a symplectic isometry of spreads. Conversely, a symplectic isometry lifts to a unitary between Weyl representations. To see the representation step, choose symplectic coordinates $(a,b)$ and ordered Weyl operators $X(a),Z(b)$ with $X(a)Z(b)=\zeta^{a\cdot b}Z(b)X(a)$. The commuting generators in each family can be rescaled to have order $p$. The lift $D_{(a,b)}=\zeta^{-a\cdot b/2}X(a)Z(b)$ then has multiplication cocycle $\zeta^{\omega(x,y)/2}$. For a noncentral element the character vanishes, since some Weyl operator conjugates it to a nontrivial scalar multiple of itself. Both representations agree on the center, so they have the same character and are unitarily equivalent. The resulting map sends simultaneous eigenrays to simultaneous eigenrays. The projective unitary kernel on $P$ is exactly $P$. Indeed, a kernel unitary sends $D_x$ to $\chi(x)D_x$ for a character $\chi$. Nondegeneracy realizes $\chi$ by conjugation by a Weyl operator. The remaining exact commutant consists of scalars, since the Weyl representation is irreducible. Consequently the projective unitary automorphism count of the frame family is $d^2|\operatorname{Sp}(V,\omega;\mathcal S)|$. This recovers finite group coordinates for the established symplectic classification of this MUB class. [Calderbank–Cameron–Kantor–Seidel](https://doi.org/10.1112/S0024611597000403), [Kantor, Proposition 2.8 and its odd-prime extension](https://pages.uoregon.edu/kantor/PAPERS/MUBS12.pdf).

## 2. Recover unordered subspaces from the commutator

Let $(X,\Omega)$ be a symplectic $\mathbb F_p$-space of dimension $2N$ and let $\mathcal L=(L_i)$ be distinct $N$-dimensional subspaces, with positive integer colors $a_i$. The color will be the dimension of an added tag space $T_i=\mathbb F_p^{a_i}$. Assume the explicit gap
$$
\sum_{i:x\notin L_i} a_i>N \qquad\text{for every }0\ne x\in X.
$$
Set $Q_i=X/L_i$ with quotient map $\pi_i$, and define
$$
T=\bigoplus_i T_i,\qquad U=X\oplus T,\qquad
W=\mathbb F_p z\oplus\bigoplus_i (T_i\otimes Q_i).
$$
Use the alternating bilinear map
$$
\beta((x,t),(y,s))=
\Omega(x,y)z+\bigoplus_i\bigl(t_i\otimes\pi_i(y)-s_i\otimes\pi_i(x)\bigr).
$$
On $U\times W$, set
$$
(u,w)(u',w')=(u+u',w+w'+\tfrac12\beta(u,u')).
$$
Bilinearity gives associativity. The ordinary commutator is $\beta$, and alternation gives exponent $p$. Every $T_i\otimes Q_i$ is spanned by commutators with $T_i$. Commutators between two elements of $X$ span the $z$-line. The next rank argument shows that the radical is zero. Hence both the center and the derived subgroup are $W$, as is the Frattini subgroup by the exponent condition. This is a special group of class two. Its multiplication extends the Heisenberg central cocycle by making the added commutators depend on quotient maps. [Grochow–Qiao on group extensions and cohomology](https://doi.org/10.1137/15M1009767), [Grochow–Qiao I on commutator tensors and alternating matrix-space isometry](https://doi.org/10.1137/21M1441110).

For $u=(x,t)$, let its contraction rank be $\operatorname{rank}\beta(u,-)$.

1. If $x\ne0$, restriction to $T$ gives independent contributions of dimension $a_i$ for each $i$ with $\pi_i(x)\ne0$. The gap gives rank greater than $N$.
2. For $x=0$ and $t\ne0$, the kernel of the contraction on $X$ is $\bigcap_{i:t_i\ne0}L_i$. One nonzero tag component gives rank $N$. Two or more give rank greater than $N$, since distinct equal-dimensional subspaces have smaller intersection.

The minimum nonzero rank therefore identifies exactly the union of the nonzero vectors of the $T_i$. Its maximal linear subspaces after adjoining zero are the individual $T_i$, since adding nonzero vectors from different blocks increases the rank. Thus their dimensions give the colors, and their span recovers $T$. This is a characterization inside the group structure, available through $G/Z(G)$ and its commutator map.

The bracket subspace $\beta(T,U)$ is the sum of the $T_i\otimes Q_i$. On $U/T$ the bracket modulo this subspace is $\Omega$ valued in a one-dimensional quotient. Each recovered $T_i$ identifies the subspace $L_i$ as the kernel of pairing with it on $U/T$. These are canonical under group isomorphism. Conversely, a color-preserving symplectic similitude $s:X\to X'$ sends each $L_i$ to $L'_j$ and induces $\bar s_i:Q_i\to Q'_j$. Extend it by any invertible $D_i:T_i\to T'_j$ and by $D_i\otimes\bar s_i$ on the associated central summand. Scale the central $z$ by the multiplier of $s$. The resulting pair of maps preserves the entire commutator and lifts by the displayed law to an ordinary group isomorphism.

This gives exact equivalence between the colored configuration and unmarked group isomorphism. The rank argument is analogous to Grochow and Qiao's rank individualization. Here the rank minimum recovers whole variable-dimensional tag spaces and their quotient kernels. The target remembers actual symplectic configurations. The Baer–Lovász–Tutte graph construction is a close precedent for encoding a discrete source as an ordinary class-two group. [Grochow–Qiao II, Section 3](https://drops.dagstuhl.de/storage/00lipics/lipics-vol200-ccc2021/LIPIcs.CCC.2021.16/LIPIcs.CCC.2021.16.pdf), [He–Qiao](https://doi.org/10.1016/j.ejc.2021.103404).

## 3. Three lines impose the unitary square class

For an input spread $\mathcal S$ in dimension $2n$, take a separate symplectic plane $E$ with fixed basis $e,f$ and form the orthogonal symplectic sum $X=V\perp E$, with $N=n+1$. In $E$ use three lines $\ell_1=\langle e\rangle$, $\ell_2=\langle f\rangle$, $\ell_3=\langle e+f\rangle$. For each $L\in\mathcal S$, include $L\oplus\ell_j$ of color $a=j$ for $j=1,2,3$. The configuration consists of distinct $N$-dimensional subspaces.

Check the gap without enumerating the input vectors. If $(v,w)$ has $v\ne0$, then $v$ lies in just one member of the spread and the active tag dimension is at least $6(m-1)>n+1$. If $v=0,w\ne0$, then $w$ lies in at most one of the three auxiliary lines. The active tag dimension is at least $3m>n+1$. Thus the construction of Section 2 applies with
$$
\dim U=2(n+1)+6m,\qquad \dim W=1+6m(n+1).
$$

The intersection of each color class is exactly its auxiliary line. Their span singles out $E$, and its symplectic perpendicular singles out $V$. A color-preserving similitude must send the three ordered auxiliary lines to their counterparts. Such a linear map on a plane is scalar in the chosen bases and has square multiplier. The restriction to $V$ has the same multiplier and can be rescaled to a symplectic isometry without changing any spread member. Conversely, a symplectic isometry of the spread extends by the identity on $E$. Combining Sections 1–3 proves the unitary equivalence theorem for all odd $p$.

Output dimensions are linear in $m(n+1)$, and the structure constants can be computed by matrix elimination and tensor products. This is a polynomial construction in the exact frames or explicit spread data. The group order is exponential in the commutator dimensions. A bound stated for Cayley-table input does not yield a polynomial algorithm on the compact data here. The target is the class-two, exponent-$p$ commutator-tensor setting of Grochow and Qiao's tensor and group-isomorphism results. [Grochow–Qiao IV](https://arxiv.org/abs/2306.16317).

## 4. Exact automorphism count

For the augmented configuration all $L_i$ are Lagrangian and $N\ge2$. A pseudo-isometry of the commutator, meaning a pair of invertible linear maps on $U,W$ preserving $\beta$, has on $U$ the form
$$
(x,t)\longmapsto (sx,a(x)+Dt),
$$
where $s$ is a color-preserving similitude and $D$ permutes the tag blocks by invertible maps. Its action on the $T_i\otimes Q_i$ is already fixed by these maps. A possible additional central component of the image of $z$ is a vector $b=(b_i)$ in that sum. Composing with the inverse of the lift of $(s,D)$, it suffices to test $s=D=I$. The equation on pairs in $X$ is then
$$
a_i(x)\otimes\pi_i(y)-a_i(y)\otimes\pi_i(x)=\Omega(x,y)b_i.
$$
Take $0\ne u\in L_i$. The functional $\Omega(u,-)$ is nonzero on $Q_i$ by nondegeneracy and isotropy. Since $\dim Q_i=N\ge2$, choose a nonzero $q$ in its kernel and a preimage $y$. In the equation with $x=u$ this gives $a_i(u)\otimes q=0$, hence $a_i(u)=0$. Taking $q$ outside the kernel then gives $b_i=0$. This reasoning gives $a_i|_{L_i}=0$, so $a_i$ descends to $Q_i$. Choose two independent quotient vectors in the remaining tensor equation and apply suitable linear functionals to their tensor factors. Their coefficients must vanish, so the descended map is zero. This proves the asserted rigidity of the lift.

An abstract group automorphism induces a pseudo-isometry and can differ from its displayed lift by precisely an additive central map $U\to W$. This follows by substituting a map $(u,w)\mapsto(u,w+h(u))$ into the group law. Thus for this construction
$$
|\operatorname{Aut}G|=p^{(\dim U)(\dim W)}
  \left(\prod_{j=1}^3 |\operatorname{GL}(j,p)|^{m}\right)
  (p-1)|\operatorname{Sp}(V,\omega;\mathcal S)|.
$$
The last factor follows directly from the auxiliary restriction. For every $c\in\mathbb F_p^\times$, an automorphism acting by $cI$ on $E$ must act on $V$ by $c$ times a symplectic spread stabilizer, and every such choice works. Multiplying the normalized count by $d^2$ recovers the projective unitary automorphism count by Section 1. For equivalent objects, the number of transporters is the corresponding automorphism count in either model, so the same normalization applies.

## 5. Exact finite control and priority

For $p=5,n=1$, use all six projective lines in $V=\mathbb F_5^2$ as the spread. An exact phase calculation on the coordinate and Fourier frames recovered five diagonal classes and five shifts, with $25$ distinct projective products. Testing those products on each of the six frames recovered a stabilizer of size five in every case. The augmented configuration has $18$ subspaces, with two-dimensional quotients and total tag dimension $36$. A finite enumeration evaluated the quotient tests for all $624$ nonzero vectors in $V\perp E$. The minimum restricted contraction rank into the tag summands was $18$, above the pure single-block tag rank $2$. Enumeration of the $480$ invertible $2$-by-$2$ matrices over $\mathbb F_5$ found four scalar matrices preserving all three marked lines. Their multipliers were $1,1,4,4$. There were $480$ compatible ordered pairs of actions on $V,E$ and $120$ symplectic spread stabilizers on $V$, agreeing with the factor $p-1=4$ and giving $3000$ projective unitary symmetries by the theorem.

The finite Heisenberg and spread descriptions of Pauli MUBs are established. The individual ingredients of alternating commutator tensors and rank individualization are also established. The proposed bridge is the direct intrinsic recovery of colored subspace kernels together with the auxiliary square-class test and exact count in an ordinary class-two group. The scope is the promised Pauli class with exact coordinates and the stated concise format. No priority claim is made for the combined construction.
