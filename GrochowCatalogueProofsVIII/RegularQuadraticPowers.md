# Regular determinants for powers of nondegenerate quadratics

## GP-0581

Write $m(N,a)$ for the smallest order of a complex affine matrix of determinant $q^a$ and corank one at zero, where $q$ is any nondegenerate quadratic in $N\ge1$ variables and $a\ge1$. Put $h=2^{\lfloor(N-1)/2\rfloor}$, $b=\lceil N/2\rceil$, and write $a=uh+v$ with $0\le v<h$. Then
$$
 \max(2a,1+b)\ \le\ m(N,a)\
 \le\ a+uh+\min(h,vb),
$$
where the last minimum is zero for $v=0$. In particular $m(N,1)=1+b$ and $m(N,a)=2a$ for all powers divisible by $h$. At fixed $N$ this gives the exact leading constant two with a bounded additive error for every power, and an infinite exact subsequence. The new lower bound is independent of the power, and the chiral construction reduces the intermediate dimension at even $N$. [Published regular constructions and the quadratic-power question](https://arxiv.org/html/2611.03554#S18.SS1)

### The two lower bounds

The degree of an order-$m$ affine determinant is at most $m$, so $m\ge 2a$. For the other bound choose a vector $v_0$ with $q(v_0)=1$, write $x=t v_0+y$, and let $B$ be the polar pairing normalized by $q(v+w)=q(v)+2B(v,w)+q(w)$. The coefficients of degrees one and two in $y$ are
$$
 2a\,t^{2a-1}B(v_0,y),\qquad
 a\,t^{2a-2}\big(q(y)+2(a-1)B(v_0,y)^2\big).
$$
After division by $t^{2a-2}$ the second coefficient is a quadratic of rank $N$. On the $B$-orthogonal complement of $v_0$ it is a multiple of $q$, and on the line of $v_0$ it is nonzero because $2a-1\ne0$.

Over $\mathbb C[t]_{(t)}$ the base matrix at $y=0$ has determinant $t^{2a}$ and corank one at $t=0$. Unit row and column operations independent of $y$ change the base matrix to $\operatorname{diag}(t^{2a},I_{m-1})$. Write the perturbation in blocks as $(\ell,B_1;C_1,W)$. The linear term of the determinant is $\ell+t^{2a}\operatorname{tr}W$. Its divisibility by $t^{2a-1}$ forces the same divisibility on $\ell$. The quadratic term is $t^{2a} e_2(W)+\ell\operatorname{tr}W-B_1C_1$. Up to a unit, its specialization after dividing by $t^{2a-2}$ is the residue quadratic above. The first two terms vanish after division and specialization, and the third is divisible by $t^{2a-2}$. Over the fraction field $B_1C_1$ has quadratic rank at most $2(m-1)$, being a sum of $m-1$ products of linear forms. Scaling by a power of $t$ preserves rank over that field, and its regular coefficient matrix cannot gain rank on specialization. Therefore $N\le2(m-1)$, as required.

### Regular pencils from rectangular linear factorizations

If $L(x)R(x)=q(x)I_a$ for linear pencils of sizes $a\times w$ and $w\times a$, use
$$
 \begin{pmatrix}-J_a&L(x)\\ -R(x)&I_w\end{pmatrix},
$$
where $J_a$ is a nilpotent Jordan block. Its determinant is $\det(q(x)I_a-J_a)=q(x)^a$ by the Schur complement, and its corank at zero is one. Thus it is enough to construct a linear factorization with a small intermediate width $w$.

Over $\mathbb C$, use coordinates $q=\sum_{i=1}^s x_i y_i$ for $N=2s$, and $q=z^2+\sum_{i=1}^s x_i y_i$ for $N=2s+1$. On the exterior algebra of an $s$-dimensional space, let $E_i$ be wedging by basis vector $i$ and $I_i$ contraction by its dual. The operator $\gamma=\sum_i(x_iE_i+y_iI_i)$ satisfies $\gamma^2=(\sum_i x_i y_i)I$, since the two types anticommute internally and $E_iI_j+I_jE_i=\delta_{ij}I$. It switches the even and odd parts. For $N=2s$ these parts have dimension $h=2^{s-1}$, so the two off-diagonal blocks of $\gamma$ are square $h\times h$ factors of $qI_h$. For $N=2s+1$ use $zI+\sqrt{-1}\gamma$ and $zI-\sqrt{-1}\gamma$ on the full exterior space of dimension $h=2^s$. Their product is $qI_h$.

Take $u$ copies of the corresponding factorization. For the residual $v>0$, restricting the outer rows and columns of one $h$-block to a coordinate $v$-space gives a linear factorization of $qI_v$ with intermediate width $h$. Alternatively $q$ is a sum of $b$ products of linear forms, so independent copies for each of the $v$ residual coordinates give width $vb$. Taking the smaller choice and adjoining the full blocks gives the upper bound. For $a=1$ the direct $b$-product representation always yields size $1+b$; for $h\mid a$ the degree lower bound is met.
