# Presented-module tensor isomorphism reduces to free tensor isomorphism

## GP-0095

For every fixed finite commutative ring $R$, tensor isomorphism for three finitely presented $R$-modules is polynomial-time many-one equivalent to ordinary three-tensor isomorphism on free $R$-modules. The input uses dense presentation matrices and representatives of the tensors in the free covers. The construction is also uniform when the ring is given by its full arithmetic tables. The reduction outputs a single pair of free three-tensors and works for rings with nilpotents or several local factors. The reverse reduction takes free presentations with zero relations. This extends the use of free and arbitrary module classes in [Grochow–Qiao–Stange–Sun, Part V](https://arxiv.org/html/2611.00735v1), where the diagonal-full property is needed for their free-module gadgets and can fail for local rings.

### Free presentations and a cyclic submodule

First, two surjections from free modules of the same rank to the same finite $R$-module $M$ differ by an invertible change in the source. Reduce to each local factor of the finite ring. Over a local ring with maximal ideal $\mathfrak m$, choose a source basis whose first $r=\dim_{R/\mathfrak m}M/\mathfrak m M$ images form a basis modulo $\mathfrak m M$. A basis modulo $\mathfrak m$ lifts to a basis of the source, and Nakayama gives generation of $M$ by the first $r$ images. Subtract combinations of these first basis elements from the remaining source basis elements to give them zero image. The resulting two minimal surjections $R^r\to M$ differ by a source change of basis: lift the generators of one along the other and use invertibility modulo $\mathfrak m$. Extend to the other source coordinates and combine over the local factors. The argument also lifts an isomorphism between different targets after identifying them.

In each input, let $F_i$ be the free cover of module $M_i$, with $D_i:H_i\to F_i$ the presentation matrix. For the two instances equalize the cover ranks by padding covers with additional generators mapping to zero and adding their coordinate vectors to the relations. Equalize each relation-source rank by appending zero columns. These steps preserve the modules and input tensors. Put $E=F_1\otimes F_2$ and $F=E\otimes F_3$. Write $K=\sum_i F_1\otimes\cdots\otimes\operatorname{im}D_i\otimes\cdots\otimes F_3$ for the sum of the images of those induced maps in $F$. Tensor product right exactness identifies $F/K$ with $M_1\otimes M_2\otimes M_3$.

If $\tilde t\in F$ represents the supplied tensor, take $D_4:H_4\to F$ to have columns $\tilde t$ and the images of each presentation column tensored with basis vectors of the other free covers. Its image is $K+R\tilde t$. The following diagram has a constant number of objects and maps, all free:

* The four linear maps $D_1,D_2,D_3,D_4$.
* The two bilinear tensor product maps $F_1\times F_2\to E$ and $E\times F_3\to F$.

Diagram isomorphisms mean invertible maps on each named object, intertwining all the named maps. An isomorphism on the original tensors lifts to cover isomorphisms by the surjection fact. These preserve the relation submodules and their tensor-product sum, and send $K+R\tilde t$ to $K'+R\tilde t'$. Apply the surjection fact again to lift the induced isomorphisms on each relation image to $H_1,H_2,H_3,H_4$. The tensor-product cover maps give the diagram isomorphism.

Conversely, the two product maps force the action on $F$ to be the tensor product of the three cover maps, and the linear maps ensure it passes to the quotients and sends $R t$ to $R t'$. Two elements generating the same cyclic submodule over a finite commutative ring differ by a unit. In each local factor, if the submodule is nonzero a generator has nonzero image in its quotient by the maximal ideal, by Nakayama. Hence a coefficient expressing one generator in terms of the other must be a unit. For zero factors take the coefficient one, then combine by the product decomposition. Absorbing the inverse of that unit in the first module isomorphism transports $t$ to $t'$ exactly.

### Encoding the diagram in one block-preserving bilinear map

For every diagram object $V$, introduce free copies $V_L,V_R,V_O$ in a left, right and output sum, respectively. The three sums also have scalar lines $R a$, $R b$ and $R c$, respectively. For each linear map $D$ introduce another marked right scalar line $R b_D$. Use these nonzero or potentially nonzero blocks of a single bilinear map, with distinct named blocks in each mode:

* $a\times b\mapsto c$ and $a\times b_D\mapsto c$.
* $a\times V_R\to V_O$ and $V_L\times b\to V_O$ by the identity copies.
* For a named linear map $D:V\to W$, $V_L\times b_D\to W_O$ by $D$.
* For a named bilinear map $B:V\times W\to Z$, $V_L\times W_R\to Z_O$ by $B$.

All remaining blocks are zero. The two product maps have distinct pairs of block indices. Under any block-preserving equivalence, let the scalars of $a,b$ be $\alpha,\beta\in R^\times$. The bridge to $c$ forces every $b_D$ to have scalar $\beta$. If $Q_V$ is the action on $V_O$, the identity bridges force the actions on $V_L$ and $V_R$ to be $Q_V/\beta$ and $Q_V/\alpha$, respectively. Consequently $Q_V/(\alpha\beta)$ gives simultaneous object isomorphisms intertwining the original linear and bilinear maps. Conversely a diagram isomorphism extends by setting $\alpha=\beta=1$ and applying each given object map to all its copies. Every output summand is the image of a specified bridge between a left and a right summand.

### Removing the block restriction over finite rings

Here is a guard construction for such a block map $f:A\times B\to C$, which uses cardinalities and therefore detects nonzero nilpotent coefficients. There are a constant number of left and right blocks. Add two right guard lines per left block and two left guard lines per right block. Number the guards on each side from zero. A guard numbered $j$ also receives a private free space of dimension $M L^j$ on the opposite side, where $M,L$ will be chosen below. The new left and right spaces are $\widehat A=A\oplus X\oplus S$, $\widehat B=B\oplus Y\oplus T$, where $S,T$ are the guard sums and $X,Y$ the respective sums of private spaces. In the output, retain $C$ and add an independent copy of each guard's paired data block and of its private space. With $u\in A$, $v\in B$, guard coordinates $s_i,t_j$, and private coordinates $x_j,y_i$, use the bilinear map
$$
\widehat f((u,x,s),(v,y,t))
=f(u,v)
 +\bigoplus_j t_j(u_{\tau(j)},x_j)
 +\bigoplus_i s_i(v_{\tau(i)},y_i).
$$
Here $\tau$ identifies the original opposite block paired with each guard.

For any linear map of finite modules, use the number $\log_2|\operatorname{im}|$ to measure the image. Write $c_R=\log_2 |R|$, and assume $R$ is nonzero. A vector without a guard component has contraction image measure at most $c_R(\operatorname{rank}_R C+\max(\dim S,\dim T))$, because its image is the sum of a submodule of $C$ and a linear image of the opposite guard sum. A vector with a nonzero $j$th guard component has measure at least $ML^j$, by contracting on opposite private coordinates, since a nonzero ideal has at least two elements. With $M$ exceeding the low bound, the submodules $A\oplus X$ and $B\oplus Y$ are intrinsic. Their pairing spans $C$ by the bridges, so the original output $C$ is intrinsic.

Work modulo $C$. The pairing $(A\oplus X)\times(\widehat B/(B\oplus Y))$ is well-defined with values in $\widehat C/C$, and likewise on the other side. For a guard combination $(t_j)$, its contraction against $A\oplus X$ has measure
$$
\sum_j ML^j\log_2|t_j R|+\epsilon,\qquad
0\le\epsilon\le c_R\operatorname{rank}_R A.
$$
The private coordinates contribute direct factors and the remaining image is a linear image of $A$. Let $\delta>0$ be the smallest positive difference between the finitely many distinct values of $\log_2|aR|$ for $a\in R$. Choose $L$ so that $c_R/(L-1)<\delta/4$ and make $M$ large enough that $c_R\max(\operatorname{rank}_R A,\operatorname{rank}_R B)/M<\delta/4$. The measure then determines the sequence of the values $\log_2|t_j R|$: two different sequences with highest differing index $k$ have leading terms differing by at least $ML^k\delta$, lower terms by less than $ML^k\delta/4$ in aggregate, and error terms by less than $ML^k\delta/4$. In particular the support of the guard combination is determined even if some guard coefficients are zero divisors. Each named guard line is the set with support contained in its index.

Contracting with a generator of a recovered guard line gives a kernel independent of the chosen generator, since generators differ by a unit. In either unguarded submodule the $j$th private space is exactly the intersection of all guard kernels on the opposite side except the $j$th: every original block is still hit by another copy of its guard and every other private space is hit by its own guard. Quotient out these private spaces. The kernel of each guard now induces the direct sum of all original blocks except its paired one. Intersecting the kernels for guards of all other blocks recovers each original block. The data pairing factors through these quotients and recovers $f$. Its bridges recover each individual output block by taking their images. Any ordinary isomorphism of $\widehat f$ therefore induces an isomorphism of $f$ with the required named blocks. Conversely, each block-preserving isomorphism extends to $\widehat f$ by the same action on paired copies and identity on guards and private spaces.

Choose the guard dimensions using integer bounds. For $s=|R|\ge 2$, distinct cardinalities $v<w$ satisfy
$$
\log_2(w)-\log_2(v)\ge \log_2(1+1/v)\ge \frac{1}{(v+1)\ln 2}>\frac{1}{s}.
$$
The middle inequality uses $\ln(1+x)\ge x/(1+x)$. Also $c_R\le s$. Thus $L=16(s+1)^2$ works, and so does $M=L(1+d_A+d_B+d_C+n_S+n_T)$, where $d_A,d_B,d_C$ are the free ranks before adding the guards and $n_S,n_T$ count the left and right guard lines. This selection avoids any logarithmic computation. There are only a constant number of guards, so the tensor dimensions and coefficient array are polynomial in the diagram size for fixed $R$ and also polynomial in the total input length if the arithmetic tables of $R$ are supplied. Bilinear-map isomorphism of the free input and output spaces is ordinary free three-tensor isomorphism after dualizing the two input factors. The zero-ring case is immediate because all modules and tensor spaces are zero.
