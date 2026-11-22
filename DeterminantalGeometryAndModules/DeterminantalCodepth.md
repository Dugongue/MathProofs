# Exact codepth for square-to-rectangular determinantal flags

Let $k$ be an algebraically closed field of characteristic zero and $2\le r<t$. For a homogeneous $t\times(t+1)$ matrix $\mathcal A$ over a polynomial ring $R$, let $\mathcal B$ be obtained by deleting its last column. Put $q=t-r$, $I_A=I_{q+1}(\mathcal A)$, $I_B=I_{q+1}(\mathcal B)$, $A=R/I_A$, and $B=R/I_B$. All codepths below are dimension of support minus depth at the homogeneous maximal ideal.

**Theorem.** If the $t(t+1)$ entries of $\mathcal A$ are a homogeneous regular sequence of positive degrees in $R$, then
$$
\operatorname{codepth}\operatorname{Hom}_R(I_B,I_A/I_B)=r.
$$
The same equality holds for a general matrix of every positive degree pattern $a_j-b_i$ when the determinantal quotient $A$ has dimension at least three. For the universal matrix, on the rank-$q$ locus of $\mathcal A$, the rank-$(q-1)$ locus of $\mathcal B$ has ideal sheaf $\mathcal J$, and
$$
\operatorname{Fitt}_{r^2}(\operatorname{Hom}_R(I_B,A))=\mathcal J^r.
$$
Here Fitting ideals and the rank loci are taken on the same open subscheme of $\operatorname{Spec} A$.

This proves the $c=2$ conclusion for minors of size at least two in Kleppe and Miró-Roig's Conjecture 10.7(ii) for the universal matrix and for general forms of every permitted positive degree pattern for every allowed ambient dimension. Proposition 7.18 supplies only the upper bound in the universal case. The paper tests some instances, including powers of entries, in Example 7.20. [Kleppe–Miró-Roig, Proposition 7.18, Example 7.20 and Conjecture 10.7](https://arxiv.org/pdf/2007.12119). [Published memoir](https://doi.org/10.1090/memo/1418).

## Proof

### Universal matrix and the exact sequences

First let $R=k[x_{ij}]$ and take the matrix of independent indeterminates. Write
$$
H_1=\operatorname{Hom}_R(I_B,I_A/I_B),\qquad
H_2=\operatorname{Hom}_R(I_B,A),\qquad
H_3=\operatorname{Hom}_R(I_A/I_B,A),
$$
and $N_A=\operatorname{Hom}_R(I_A,A)$, $N_B=\operatorname{Hom}_R(I_B,B)$. Proposition 7.18 gives its exact sequences (7.4) and (7.6)
$$
0\longrightarrow H_3\longrightarrow N_A\longrightarrow H_2\longrightarrow0,\qquad
0\longrightarrow H_1\longrightarrow N_B\longrightarrow H_2\longrightarrow0.
$$
The first map $H_3\to N_A$ is precomposition with $I_A\to I_A/I_B$. Set $\ell=r(r+1)$, the codimension of $A$. The $c=2$ row of that proposition gives the input
$$
\operatorname{pd}_R H_3=\operatorname{pd}_R N_A=\ell,\qquad
\operatorname{pd}_R N_B=\ell-r+2.
$$
These projective dimensions can be taken at the homogeneous maximal ideal, since minimal graded free resolutions of finite graded modules over $R$ localize to minimal resolutions there. [Kleppe–Miró-Roig, equations (7.4) and (7.6) and the table in Proposition 7.18](https://arxiv.org/pdf/2007.12119#page=67).

### The local restriction map

Invert a $q\times q$ pivot on any $q$ rows and $q$ columns that include the last column of $\mathcal A$. Call this matrix $P$, and let $Q$ be the matrix of entries below $P$ in its chosen columns. List the last column last among the pivot columns. An invertible row operation normalizes these columns to $\binom{1_q}{0}$. If $Z_0,W_0$ are the upper and lower blocks in the $r+1$ nonpivot columns, the new blocks are $Z=P^{-1}Z_0$ and $W=W_0-QP^{-1}Z_0$. They are independent variables over $k[P,Q,\det(P)^{-1}]$, as one sees from the inverse coordinate change.

Use the first $q-1$ normalized pivot columns to clear the first $q-1$ coordinates in each nonpivot column. This is a column operation on $\mathcal B$ as well as on $\mathcal A$. Let $z=(z_1,\ldots,z_{r+1})$ be the remaining row of $Z$ and $w_{ij}$ the entries of $W$, with $1\le i\le r$. Cancelling the identity pivots gives
$$
I_A=(w_{ij}),\qquad I_B=I_2\left(\begin{matrix}z\\W\end{matrix}\right).
$$
For the second equality, $\mathcal B$ retains $q-1$ pivot columns and the residual matrix has rows $z,W$. For the first, the last pivot removes the row $z$ as well, leaving $W$. Write $S$ for $A$ on this chart. It is a polynomial ring over $k[P,Q,\det(P)^{-1}]$ in the entries of $Z$, so the $z_j$ are distinct prime variables.

The conormal module $I_A/I_A^2$ is free over $S$ on the $w_{ij}$, since these are coordinate variables. Identify $N_A$ on this chart with $S^{r(r+1)}$ by the images $F_{ij}$ of these generators. A tuple lies in $H_3$ precisely when it vanishes on $I_B$. Minors involving two rows of $W$ lie in $I_A^2$. The minors involving $z$ impose exactly
$$
z_jF_{ik}=z_kF_{ij}\qquad (1\le i\le r,\ 1\le j<k\le r+1).
$$
For each row, primality of $z_1$ and $z_1\nmid z_2$ give $F_{i1}=u_i z_1$. The remaining equations with $j=1$ then give $F_{ik}=u_i z_k$. Thus
$$
H_2|_{\operatorname{Spec} S}\cong\bigoplus_{i=1}^{r}\operatorname{coker}\big(S\xrightarrow{\,1\mapsto z\,}S^{r+1}\big).
$$

On the chart, the rank-$(q-1)$ locus of $\mathcal B$ on $A$ is cut out by the entries of $z$, so $\mathcal J=(z)$. In the displayed presentation the inclusion $S^r\to S^{r(r+1)}$ has one $z$ block per column. Its maximal minors generate precisely the degree-$r$ monomials in the $z_i$, since a nonzero minor chooses one entry from each block and every such selection is possible. These maximal minors generate $\operatorname{Fitt}_{r^2}(H_2)$. At a point with some nonzero $q$-minor of $\mathcal B$, normalize pivots entirely in $\mathcal B$ instead. Then $I_B$ is generated by $r^2$ coordinate variables, and their conormal module over $B$ is free, so $H_2$ is free of rank $r^2$ over $A$ there and $\mathcal J$ is the unit ideal. These two types of charts cover the rank-$q$ locus of $\mathcal A$, proving the Fitting-ideal formula.

### Computing the depth

Localize at the prime $(w_{ij},z_j)$ of the ambient pivot chart, which exists by the coordinate description. The base $S$ there is regular local, and each copy of the $H_2$ presentation is a minimal free resolution of length one. Indeed the vector $z$ gives an injection with entries in the maximal ideal. Over the ambient regular localization $I_A$ cuts out $\ell$ independent variables. Depth of an $A$-module is the same over the ambient regular local ring and its quotient $A$, since elements act through their images. By Auslander–Buchsbaum, the local ambient projective dimension of $H_2$ is $\ell+1$.

The first exact sequence gives the upper bound $\ell+1$ globally, so $\operatorname{pd}_R H_2=\ell+1$. In the second short exact sequence, $\operatorname{pd}_R N_B=\ell-r+2\le\ell$. The nonzero $\operatorname{Tor}_{\ell+1}^R(k,H_2)$ injects into $\operatorname{Tor}_{\ell}^R(k,H_1)$. The same long exact sequence gives zero in all higher degrees for $H_1$. Hence $\operatorname{pd}_R H_1=\ell$.

The determinantal domain $B$ has codimension $r^2$, and $I_A/I_B$ is a nonzero ideal of $B$. At the fraction field of $B$, $I_B/I_B^2$ has dimension $r^2$, as the rank-$q$ chart of $\mathcal B$ is a complete intersection of that codimension. Thus $H_1=\operatorname{Hom}_B(I_B/I_B^2,I_A/I_B)$ has positive generic rank and dimension of support $\dim B$. Auslander–Buchsbaum now gives
$$
\operatorname{codepth}H_1=(\dim R-r^2)-(\dim R-\ell)=r.
$$

### Specialization to a regular sequence of forms

Suppose the entries of a homogeneous matrix are a regular sequence $f_{ij}$ of positive degrees in a polynomial ring $T=k[y_1,\ldots,y_N]$. Give the universal variables $x_{ij}$ the weights $\deg f_{ij}=a_j-b_i$ and use the graded map $R\to T$, $x_{ij}\mapsto f_{ij}$. The weighted grading does not change projective dimensions at the ideal generated by the $x_{ij}$.

The map makes $T$ a free $R$-module. To see this, choose a homogeneous $k$-linear complement $V$ of $(f_{ij})$ in $T$. The multiplication map $R\otimes_k V\to T$ is onto by induction on degree. The regular sequence gives
$$
\operatorname{Hilb}_{V}(u)=\operatorname{Hilb}_{T}(u)\prod_{i,j}(1-u^{\deg f_{ij}}).
$$
The Hilbert series of $R\otimes_k V$ thus equals that of $T$, showing the surjection is an isomorphism degree by degree. This also shows that the map is faithfully flat.

Flatness carries the determinantal ideals, the quotient $I_A/I_B$, and $H_1$ to their versions over $T$. For the assertion about $H_1$, take a finite presentation of $I_B$, apply $\operatorname{Hom}_R(-,I_A/I_B)$ and use flatness to preserve the resulting kernel. A minimal graded free resolution of $H_1$ remains minimal after tensoring with $T$, since the $f_{ij}$ have positive degrees. Its projective dimension is still $\ell$. As a graded vector space the new $H_1$ is isomorphic to the old $H_1\otimes_k V$. The pole order of its Hilbert series at $u=1$ is therefore $(t(t+1)-r^2)+(N-t(t+1))=N-r^2$, proving that its dimension of support is $N-r^2$. Auslander–Buchsbaum gives the same codepth $r$.

For every allowed positive degree pattern and $N\ge t(t+1)$, the entries can be chosen as powers of distinct variables. They form a regular sequence. The locus of tuples whose common projective zero locus has the expected dimension or is empty when $N=t(t+1)$ is open by upper semicontinuity of fiber dimension for the projective incidence family. On this nonempty open set the ideal of entries has the required height $t(t+1)$, so these entries are a regular sequence in the polynomial ring.

### Specialization to general forms in every allowed ambient dimension

Fix positive weights $d_{ij}=a_j-b_i$ and $N\ge\ell+3$. Let $P$ be the polynomial ring over $k$ on the coefficients of all entries, let $K$ be its fraction field, and let $T=K[y_1,\ldots,y_N]$ with homogeneous maximal ideal $\mathfrak m=(y_1,\ldots,y_N)$. Substitute the polynomials having these coefficients for the $x_{ij}$.

For each $j$, the substitution on the localization $P[y_1,\ldots,y_N,y_j^{-1}]$ makes that ring a polynomial and Laurent polynomial extension of $R$. Indeed the coefficient of the monomial $y_j^{d_{ab}}$ in each entry $f_{ab}$ can be eliminated by solving $x_{ab}=f_{ab}$, because $y_j$ is invertible. These eliminated coefficients are distinct. After further localization at $P\setminus\{0\}$, the resulting map $R\to T[y_j^{-1}]$ is still flat.

Let $U$ be any of the universal modules $A,B,H_1$, and take its minimal weighted graded free resolution over $R$. Its length $s$ is at most $\ell$. For $A$ and $B$ this follows from the Cohen–Macaulay property of universal determinantal rings, and for $H_1$ it was proved above. The complex obtained by tensoring with $T$ has higher homology supported at $\mathfrak m$, by flatness on every $D(y_j)$. That homology vanishes by Peskine–Szpiro acyclicity. In this situation, one can see this directly as follows. Localize at $\mathfrak m$ and suppose $i>0$ is the highest nonzero homology degree. If the boundary module in degree $i$ is nonzero, the exact higher tail resolves it in length at most $s-i-1$, so its depth is at least $N-s+i+1\ge2$. The cycle module is a submodule of a free module and has no local cohomology in degree zero. The sequence from boundaries to cycles to homology, and the vanishing of the first local cohomology of the boundary module, contradict the existence of nonzero finite-length homology. A zero boundary module also makes nonzero finite-length homology impossible, since the homology would then be a submodule of a free module. [Peskine–Szpiro, Lemme d’acyclicité](https://numdam.org/item/PMIHES_1973__42__47_0/).

The tensor complexes therefore resolve $A_T,B_T,M=H_1\otimes_R T$. Their matrices still have entries in $\mathfrak m$, so they remain minimal and their projective dimensions are $\ell,r^2,\ell$, respectively. Their Hilbert numerators are unchanged under positive homogeneous substitution, and their Hilbert series now have denominator $(1-u)^N$ in place of $\prod_{i,j}(1-u^{d_{ij}})$. The dimensions of $A_T,B_T,M$ are therefore $N-\ell,N-r^2,N-r^2$. Transport of ideals through the substitution follows from $\operatorname{Tor}_1^R(A,T)=\operatorname{Tor}_1^R(B,T)=0$. In particular $A_T$ and $B_T$ are the ordinary determinantal quotients of $T$, and they are Cohen–Macaulay by Auslander–Buchsbaum.

Write $J_T=I_{A,T}/I_{B,T}$, and $M'=\operatorname{Hom}_T(I_{B,T},J_T)$. The comparison map $M\to M'$ is an isomorphism off $\mathfrak m$, by the flat maps on the $D(y_j)$. Its source has depth $N-\ell\ge3$. The depth lemma applied to $0\to J_T\to B_T\to A_T\to0$ gives $\operatorname{depth}J_T\ge2$. Presenting $I_{B,T}$ by finite free modules shows that $M'$ is a kernel of a map between finite sums of $J_T$. Its image in the target has depth at least one if nonzero, since any $J_T$-regular element acts injectively there. Thus the depth lemma gives $\operatorname{depth} M'\ge2$. A finite $T$-module of depth at least two at $\mathfrak m$ identifies with its sections on the punctured spectrum by the local cohomology exact sequence. Applying this to both $M$ and $M'$ proves that the comparison map is an isomorphism.

These conclusions hold on a nonempty open set of $k$-valued coefficients. For clarity, all three finite complexes and the comparison map are defined over $P[y_1,\ldots,y_N]$ after localization at one nonzero element of $P$. The higher homology of the complexes vanishes over $K$, so further localization makes those finite modules zero. Generic freeness applied to each zeroth homology then ensures exactness persists in all coefficient fibers. The comparison map to the module defined by the finite presentation of $I_{B,T}$ is likewise an isomorphism after localization, since its kernel and cokernel vanish over $K$. To ensure this presented Hom commutes with coefficient fibers, apply generic freeness also to the image and cokernel of the presentation map between finite sums of $J_T$. These finitely many localizations define the required nonempty open set. Thus the equality holds for general homogeneous matrices for every $\dim A\ge3$ in the $c=2$ part of Conjecture 10.7(ii).


## Status

Written proof using the cited exact sequences and projective dimensions. No Lean formalization. The calculation and specialization prove a scoped case of the conjecture. Priority for that case has not been established beyond comparison with the cited memoir and a targeted literature search.
