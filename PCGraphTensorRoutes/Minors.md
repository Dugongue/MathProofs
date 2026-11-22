# Reversing the two-private-row tensor for monomial code equivalence

Let $F$ be any field and let $M,N$ be $k\times n$ matrices, allowing zero or redundant rows and zero columns. The ordinary tensor equations for the exact Grochow–Qiao construction in Galesi–Grochow–Pitassi–She Proposition 5.5 give substitutions for every equation of monomial code equivalence in constant-degree ordinary Polynomial Calculus over $F$. The substitution uses two-sided witnessed inverses. No field equations are required. The published direction goes from the code equations to the tensor equations. [Galesi, Grochow, Pitassi and She, §5](https://arxiv.org/html/2305.19320#S5)

## Conventions

Index slices by $0$ and by $(j,b)$ with $1\le j\le n$ and $1\le b\le 2$. In the pencil $D_M(z)$ the top $k$ rows are $z_0M$. The private row $(j,b)$ has the single entry $z_{jb}$ in column $j$. Mode maps and their two-sided inverses are independent. Write the tensor equations as
$$
 X D_M(z)Y^{\mathsf T}=D_N(Kz).
$$
For a raw action multiplying all three tensor indices by $X,Y,Z$, the convention is $K=Z^{-\mathsf T}$. The two equation lists interconvert by multiplying by one witnessed inverse. Reversing all maps gives the inverse pencil identities. Set $W=Y^{-\mathsf T}$ and $W'=Y^{\mathsf T}$. The other slicing $B_M(y)$ is defined by $B_M(y)z=D_M(z)y$. Its column zero has top vector $My$ and all private entries zero. Its remaining columns are the diagonal private block with entries $y_1,y_1,\dots,y_n,y_n$. Thus
$$
 X B_M(y)=B_N(Wy)K .
$$

## Every column of the coordinate map is monomial in ordinary PC

Fix a source coordinate $c$, put $y=We_c$, and let $d=\operatorname{rank} B_M(e_c)$, equal to two when $M_{*,c}=0$ and three otherwise. Every $(d+1)$-minor of $B_N(y)$ vanishes in bounded degree. Indeed $B_N(y)=XB_M(e_c)K'$ factors through a constant $d$-dimensional space. Cauchy–Binet at order at most four is a polynomial identity in the two factors, and replacement by the slice equality on each entry gives the derivation. Moreover the $d$-minors of $B_N(y)$ have an explicit unit combination. Start with a nonzero constant $d$-minor of $B_M(e_c)$, use $B_M(e_c)=X' B_N(y)K$, and expand by Cauchy–Binet. Divide by the nonzero constant. This provides a certificate of $1$ using only determinants of order at most three in the witnessed matrices. Each expression here has polynomially many terms, since the minor orders are fixed.

Fix distinct $i,j$. For $d=2$ the three-private minors give $y_i y_j y_h=0$ for **every** $h$. If an index repeats, take the two different private copies belonging to that index. Multiplying the column identity $(W'W)_{cc}=1$ by $y_i y_j$ gives $y_i y_j=0$.

For $d=3$ the four-private minors kill every degree-four monomial in which no coordinate occurs more than twice. There is a second identity for each nonzero target column $N_{*,i}$. Choose $a$ with $N_{ai}\ne0$. The minor using one top row $a$, the two private indices of $i$, and one private index of $j$, together with column zero and the three matching private columns, is
$$
 \pm (Ny)_a y_i^2 y_j=0.
$$
All terms in the expansion with a fourth factor $y_h$ for $h\ne i$ vanish by four-private minors. Dividing by $N_{ai}$ gives $y_i^3 y_j=0$ for every $j\ne i$.

Now let $m(y)$ be any three-minor of $B_N(y)$. It is a homogeneous cubic. Its coefficient of $y_h^3$ is $m(e_h)$, which vanishes whenever $N_{*,h}=0$ since $B_N(e_h)$ then has rank two. We claim $y_i y_j m(y)=0$. A degree-five term containing both $i,j$ has a degree-four divisor with all multiplicities at most two unless the full exponent pattern is $(4,1)$. In that exception the cubic term in $m(y)$ must have been a pure cube on the index occurring four times. A nonzero coefficient implies that column of $N$ is nonzero. The preceding mixed quartic identity then kills the term. Multiplying the unit combination of the three-minors by $y_i y_j$ proves $y_i y_j=0$ in the remaining case.

Apply the same argument to $W'$ with $M,N$ reversed. Both matrices now have column collisions. The polynomials $p_{ic}=W_{ic}W'_{ci}$ give Boolean permutation entries. In fact multiplying $(W'W)_{cc}=1$ by $W_{ic}$ and using the column collisions gives $W_{ic}=W_{ic}p_{ic}$. Reversing gives $W'_{ci}=W'_{ci}p_{ic}$, which also yields $p_{ic}^2=p_{ic}$. Column and row collisions for $p$ follow from those for $W$ and $W'$ respectively. Both sums follow from the diagonal inverse equations. The support identity transfers those collisions back to both rows and columns of $W,W'$ and hence of $Y,Y'$. In particular this proves the required monomial axioms for both witnesses. This argument applies to every input column, including zero columns, before any information about the data slice map is used.

## Quotienting the private rows when at least one rank is at least two

Suppose first $N$ has rank at least two. Fix a private slice $s$ and write $w=K e_s$. The matrix $D_N(w)$ factors through the fixed rank-one source slice, so all its two-minors vanish. A nonsingular constant two-minor of $N$ gives $w_0^2=0$. For a private index $t=(j,b)$, choose any $a,l$ with $l\ne j$ and $N_{al}\ne0$. Such a column exists because $N$ has rank at least two. The minor on rows $a,t$ and columns $l,j$ is $N_{al}w_0 w_t$ up to sign. Consequently $w_0w_t=0$ for every $t$, including $t=0$. Multiplying $(K'K)_{ss}=1$ by $w_0$ yields $K_{0s}=0$. Write $\lambda=K_{00}$ and $\mu=K'_{00}$. The top row of $KK'=I$ gives $\lambda\mu=1$ and $\lambda K'_{0s}=0$, whence $K'_{0s}=0$ by multiplication by $\mu$. This uses no rank hypothesis on $M$. If only $M$ has rank at least two, apply this calculation with the roles reversed to obtain the identical pair of conclusions.

Each private target slice has zero top rows. In the equation for source private slice $s=(j,b)$ the top rows therefore vanish after suppressing $K_{0s}$. Multiplying by $Y^{-\mathsf T}$ shows the top part of $X e_{k+s}$ is zero, where $e_{k+s}$ denotes its private row basis vector. Apply the inverse argument as well. Thus the top quotient blocks $A_0$ of $X$ and $A'_0$ of $X'$ satisfy both inverse identities. The top rows of the slice-zero equation say $A_0 M Y^{\mathsf T}=\lambda N$. The code substitutions are
$$
 A=\mu A_0,\qquad A'=\lambda A'_0,\qquad B=Y,\qquad B'=Y'.
$$
They have degree at most two in the original witnessed tensor variables. The preceding equations give $A M B^{\mathsf T}=N$ and all four inverse identities directly.

## Generator ranks zero and one

When both matrices are zero the identity witnesses suffice. In general $p_{ic}$ vanishes for every zero/nonzero column mismatch. To see this when $M_{*,c}=0$ and $N_{*,i}\ne0$, choose a row $a$ with $N_{ai}\ne0$. The three-minors for $d=2$ include $(Ny)_a y_i^2$. Multiply by $p_{ic}$; column collisions and idempotence reduce this to $N_{ai}p_{ic}y_i^3=0$. Multiplying by $(W'_{ci})^3$ gives $p_{ic}=0$. The inverse argument gives the other mismatch. Thus when exactly one matrix is zero and the other has rank one, a row or column sum of $p$ gives a constant contradiction, which derives every substituted equation at constant degree.

For two rank-one matrices, factor $M=u(m_c)_c$, $N=v(n_i)_i$ with nonzero constant column vectors $u,v$. Choose a constant invertible $A$ sending $u$ to $v$, by completing each to a basis, and let $A'=A^{-1}$. For every pair with both coefficients nonzero put $b_{ic}=(n_i/m_c)p_{ic}$, $b'_{ci}=(m_c/n_i)p_{ic}$. For two zeros set both entries to $p_{ic}$ and on mismatched pairs set both to zero. The Boolean permutation identities imply the two matrix inverse equations, monomiality and $A M B^{\mathsf T}=N$. This uses only inverses of explicit nonzero field constants. The degree of the substitution remains at most two.

All determinant manipulations above are coordinate polynomial identities with bounded orders. The multipliers in the unit certificate are minors of witnessed inverse maps and hence have bounded degree too. An equality multiplied by a polynomial with a bounded number of variable factors per term is obtained by variable multiplication and linear combination. Thus all substituted code axioms have polynomial-size, absolute constant-degree ordinary PC derivations. This proof concerns exactly the rank-one private slices in Proposition 5.5, independently of Part IV rank-marker gadgets used for other tensor compilers.
