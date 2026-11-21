# Counting the extra lifts in higher-degree anchored algebras

Fix $n\ge2$ and $d\ge3$. Let $V_R$ be free of rank $n$ over a commutative ring $R$, write $S_j=\operatorname{Sym}^j(V_R)$, and take a formal degree-$d$ form $f\in S_d$. Give the unmarked algebra
$$
A_f=R[V_R,z]/\bigl((V_R,z)^{d+1},\, zV_R,\, f-z^d\bigr)
$$
its usual grading. Write $D_j=\binom{n+j-1}{j}$ and
$$
K_f=\{(B,\ell)\in S_{d-1}\oplus V_R^*:xB+\ell(x)f=0\text{ for all }x\in V_R\}.
$$

**Theorem.** For every finite commutative $R$, each allowable graded algebra transporter lifts to exactly
$$
|R|^{\,n\sum_{j=2}^{d}D_j+D_d+d-2}\,|K_f|
\tag{1}
$$
ungraded transporters. For finite local rings with residue field $k$ and $\mathfrak m^3=0$, the contribution $K_f$ has an exact formula in terms of the first prolongation of a linear space. For rings with one-dimensional $\mathfrak m^2$ and a nondegenerate multiplication pairing, the resulting maximum of extra lifts at any fixed leading coefficient rank is attained and given by Macaulay growth.

Over the universal coefficient ring, the mixed equations have a square-zero defect supported at the intersection of the zero-form and zero-shear spaces. Its rank over the ground ring is $\binom{n+d-1}{d-1}$. These conclusions include every characteristic. The proofs are informal.

## 1. All degrees have the same mixed lifting equations

The underlying free algebra pieces are $R$ in degree zero, $S_j\oplus Rz^j$ for $1\le j<d$, and $S_d$ in degree $d$. The top relation eliminates $z^d$ with coefficient $1$. Its positive ideal $\mathfrak m_A$ is nilpotent, and the powers $\mathfrak m_A^i$ are the sums of the pieces of degree at least $i$.

Here is the intrinsic argument needed for arbitrary base rings. Over a field, an isomorphism preserves the unique maximal ideal and its grading filtration. On the first quotient, multiplication by $v+az$ into degree two has rank $n\mathbf 1_{v\ne0}+\mathbf 1_{a\ne0}$. Thus the line $Rz$ and its annihilator $V_R$ in degree one are intrinsic over every residue field. Over the original ring, write the images of the generators as a constant, a linear term, and higher-degree terms. The linear terms form a basis since their determinant is a unit in every residue field. The degree-one component of each mixed relation is a linear combination of the two corresponding independent linear terms with coefficients equal to the constants on those generators. The constants vanish. The inverse satisfies the same argument, so the isomorphism preserves $\mathfrak m_A$ and its powers. If the linear terms are $Sv+c(v)z$ and $w+az$, the residue-field result shows that $S$ and $a$ are invertible. The degree-two relation is $(Sv)w+c(v)az^2=0$. The summands are independent, hence $c=0$. Multiplication in the symmetric algebra by a basis vector of $V_R$ is injective even over $R$, so $w=0$ as well. The top relation now gives $\operatorname{Sym}^d(S)f=a^dg$ for a transporter from $A_f$ to $A_g$. Thus the graded transporters are exactly the exact form transporters $a^{-1}S$ together with a freely chosen unit $a$, and all lift homogeneously.

To count the kernel on the associated graded, write a graded-identity automorphism on generators as
$$
x_i\mapsto u_i(x)+p_i(z),\qquad z\mapsto v(x)+q(z),
$$
with $u_i=x_i+\cdots$, $q=z+\cdots$, and $v,p_i$ of order at least two. Pure $z$ parts stop at $z^{d-1}$ because $z^d$ was eliminated. The mixed equations are $u_i v+p_iq=0$. In each degree from $3$ through $d-1$ the two branches are separate. Induction using the leading coefficient of $q$ forces $p_i$ to have order at least $d-1$. On the $x$ branch, induction and injectivity of multiplication by $x_i$ force $v$ to have order at least $d-1$. When $d=3$ there are no intermediate equations. Write the two first possible cross terms as $p_i=\ell(x_i)z^{d-1}$ and $v=B+T$, where $B$ has degree $d-1$ and $T$ has degree $d$. The remaining mixed equations are exactly the definition of $K_f$.

Every other coordinate is free. These are the degree-$2$ through degree-$d$ coefficients of the $u_i$, the $d-2$ coefficients in the pure $z$ part of $q$ after its linear term, and the $D_d$ coefficients of $T$. Substitution preserves the top relation since every correction raises total degree. The maps are invertible by the finite filtration and identity associated graded. The description is functorial in $R$ and gives an isomorphism of underlying parameter schemes with an affine space times $K_f$, where $K_f$ is viewed as a scheme of linear equations. The parameter-space product suffices for (1).

In particular
$$
|\operatorname{Aut}_{R}(A_f)|=
|R^\times|\,|\operatorname{Stab}_{\operatorname{GL}(V_R)}(f)|
\,|R|^{\,n\sum_{j=2}^{d}D_j+D_d+d-2}|K_f|.
$$
For nonempty transporter sets on pairs, the same lift factor applies. The formula reduces the new counting question to the mixed kernel.

For any ring the projection to $B$ gives an exact sequence of $R$-modules
$$
0\longrightarrow\operatorname{Ann}_R(f)^{\,n}\longrightarrow K_f
\longrightarrow \{B\in S_{d-1}:V_R B\subseteq Rf\}
\longrightarrow0.
\tag{2}
$$
Indeed each $x_iB$ in $Rf$ admits a coefficient $\ell(x_i)$ independently. This makes the number of hidden lifts a first colon-space problem. The square-zero computation below also shows that all coefficients of $B$ lie in $I_f\cap\operatorname{Ann}_R(I_f)$, where $I_f$ is the coefficient ideal of $f$. Over a reduced ring this intersection vanishes.

## 2. Exact counts over finite local rings with $\mathfrak m^3=0$

Let $R$ have residue field $k$ and maximal ideal $\mathfrak m$ with $\mathfrak m^3=0$. The proof applies in mixed characteristic as well. Put $E=\mathfrak m/\mathfrak m^2$, $Z=\mathfrak m^2$, and let $\mu:E\times E\to Z$ be the multiplication pairing. Use $V_k$ for the variable space over $k$ and write $S_j(k)$ for its symmetric degree $j$.

Suppose first that $f\in\mathfrak m S_d$ has nonzero leading part $f_1\in E\otimes S_d(k)$. Define
$$
L:E\to Z\otimes S_d(k),\qquad w\mapsto \mu(w,f_1),\qquad W=\operatorname{im}(L).
$$
Here the pairing is applied coefficient by coefficient. Put
$$
\mathcal P(W)=
\{b\in Z\otimes S_{d-1}(k):V_k b\subseteq W\}.
$$
Write $H\subseteq\mathfrak m$ for the preimage of $\ker L$ in $E$. Then there is an exact sequence of $R$-modules
$$
0\longrightarrow H^n
\longrightarrow K_f\longrightarrow\mathcal P(W)\longrightarrow0,
\tag{3}
$$
where the right term is an $R$-module via $k$. The map sends $(B,\ell)$ to $B$, which lies in $Z\otimes S_{d-1}(k)$. The additive group $H$ has order $q^{\dim Z+\dim\ker L}$ when $k=\mathbb F_q$, giving
$$
|K_f|=q^{\,n(\dim Z+\dim\ker L)+\dim\mathcal P(W)}.
\tag{4}
$$

To prove this, reduce each mixed equation modulo $\mathfrak m$. It gives $x_i\overline B=0$ and hence $B\in\mathfrak m S_{d-1}$. Next reduce the coefficients in $\mathfrak m/\mathfrak m^2$. The equations are $x_i B_1=-\bar\ell_i f_1$. If $B_1\ne0$, the $n$ vectors $x_iB_1$ are linearly independent over $k$. Indeed a nonzero coordinate functional of $E$ sends $B_1$ to a nonzero polynomial, and multiplication by it is injective over the field. The right sides lie in a common line, so $B_1=0$ and then every $\bar\ell_i=0$. The equations now lie wholly in $Z$ and are $x_iB=-L(\ell_{i,1})$. Thus $B$ can be any element of $\mathcal P(W)$. For each $B$, each leading $\ell_{i,1}$ has an affine fiber for $L$, and its $Z$ part is unconstrained. This proves (3) and (4) and gives a coefficient algorithm for every lift.

The other cases have exact formulas as well. If $f$ has a unit coefficient then $K_f=0$ as a module. This follows from injectivity of the defining coefficient matrix modulo $\mathfrak m$ by the same field independence argument and a unit maximal minor. If $0\ne f\in Z\otimes S_d(k)$, reduction modulo $\mathfrak m^2$ puts $B$ in $Z$ and the same argument there gives $B=0$ and $\ell_i\in\mathfrak m$ arbitrary. If $f=0$, then $B=0$ and $\ell_i\in R$ arbitrary. In particular the last two cases over $k=\mathbb F_q$ give $q^{n(\dim E+\dim Z)}$ and $q^{n(1+\dim E+\dim Z)}$ lifts, respectively.

For example, over $R=\mathbb F_3[\epsilon,\eta]/(\epsilon^2,\eta^2)$ the two cubics
$$
f_0=\epsilon x^3+\eta y^3,\qquad
f_1=\epsilon x^3+\eta x^2y
$$
have the same coefficient ideal and the same leading map rank two. Their images $W$ are generated by the indicated two monomials after identifying $Z$ with $k$ via $\epsilon\eta$. For $f_0$ the prolongation is zero. For $f_1$ it is $kx^2$. The mixed kernel counts are respectively $9$ and $27$. Equation (2) gives the same number of choices for a fixed $B$ in these examples. The factor of three comes from allowed nonzero cross terms.

The counts $9$ and $27$ also occur in mixed characteristic. Take $R=(\mathbb Z/27)[\epsilon]/(3\epsilon,\epsilon^2-9)$ and use the same two forms with $3$ in place of the first coefficient $\epsilon$ and the new $\epsilon$ in place of $\eta$. This ring has residue field $\mathbb F_3$, with $\mathfrak m=(3,\epsilon)$, $\mathfrak m^2=(9)$ and $\mathfrak m^3=0$. Its multiplication pairing on the classes of $3,\epsilon$ is diagonal with both entries $9$. The images $W$ and the two prolongations are therefore the same as above.

## 3. Sharp maximum at fixed leading coefficient rank

Suppose now $Z=k\omega$ is one-dimensional and $\mu$ gives a nondegenerate pairing on $E$. This includes split short local Gorenstein rings with nondegenerate degree-one pairing. Fix a leading rank $w>0$ with $w\le\min(\dim E,D_d)$. Every $w$-dimensional $W\subseteq S_d(k)$ is realized as the image of $L$ by a suitable $f_1$. Choose any surjective map $E\to W$ and use the pairing to identify it with an element of $E\otimes W$.

Let $t=d-1$ and let $h^{\langle t\rangle}$ denote the Macaulay growth of a nonnegative integer $h$. If $h=\sum_i\binom{a_i}{i}$ is its decreasing $t$-binomial expansion, $h^{\langle t\rangle}=\sum_i\binom{a_i+1}{i+1}$, and $0^{\langle t\rangle}=0$. The sharp maximum of $\dim\mathcal P(W)$ at rank $w$ is
$$
b_{\max}(w)=
\max\left\{b:0\le b\le D_t,\quad
  D_{t+1}-(D_t-b)^{\langle t\rangle}\le w\right\}.
\tag{5}
$$
Indeed for any $b$-dimensional subspace $B_0\subseteq S_t(k)$, the quotient by the homogeneous ideal generated by $B_0$ has dimension $D_t-b$ in degree $t$ and dimension $D_{t+1}-\dim(V_k B_0)$ in degree $t+1$. Macaulay's theorem bounds the latter dimension by $(D_t-b)^{\langle t\rangle}$. Applied to $B_0=\mathcal P(W)$, this gives the upper bound. For any $b$ satisfying the inequality, a lex-segment space $B_0$ of that dimension attains the minimum possible $\dim(V_k B_0)$. Extend $V_k B_0$ to a $w$-dimensional $W$. Its prolongation contains $B_0$, so taking the maximal feasible $b$ attains (5). This holds over every field. [Macaulay](https://doi.org/10.1112/plms/s2-26.1.531) · [Boij–Conca, Section 2.1](https://rendiconti.dmi.units.it/volumi/50/009.pdf)

Combining (4) and (5), the sharp maximum of the mixed kernel size over $\mathbb F_q$ at that rank is
$$
q^{\,n(1+\dim E-w)+b_{\max}(w)}.
$$
This bounds the exact number of ungraded lifts of each fixed graded witness by multiplication by the free factor in (1).

## 4. The universal mixed scheme is an explicit square-zero extension

Work over any ground ring $R_0$ and write $f=\sum_{|\alpha|=d}c_\alpha x^\alpha$ with independent coefficients. Let $B_\beta$ be the coefficients of $B$ for $|\beta|=d-1$, and write $\ell_i=\ell(x_i)$. Let $C$ be the coordinate ring of the mixed scheme, with generators $c_\alpha,\ell_i,B_\beta$ and equations
$$
\ell_i c_\alpha=
\begin{cases}
-B_{\alpha-e_i},&\alpha_i>0,\\
0,&\alpha_i=0.
\end{cases}
\tag{6}
$$
Here $e_i$ is the multi-index of $x_i$. Every $B_\beta$ can be eliminated using any row of these equations. Assign bidegrees $(1,0),(0,1),(1,1)$ to $c_\alpha,\ell_i,B_\beta$, respectively.

Let $N$ be the ideal generated by the mixed products $\ell_i c_\alpha$, equivalently by all $B_\beta$. Then $C/N=R_0[c,\ell]/(c_\alpha\ell_i)$, the coordinate algebra of the union of the zero-form and zero-shear spaces. There is an exact module description
$$
N\simeq\operatorname{Hom}_{R_0}\!\left(\bigoplus_{t=0}^{d-1}S_t(R_0),R_0\right),
\tag{7}
$$
where $\ell_i$ acts on the right by the transpose of multiplication by $x_i$ truncated above degree $d-1$. Each $c_\alpha$ kills $N$. The dual degree-$t$ factor has bidegree $(1,d-t)$. In particular $N^2=0$ and $N$ is free of rank $\binom{n+d-1}{d-1}$ over $R_0$. If $R_0$ is reduced, $N$ is exactly the nilradical of $C$, since the quotient injects into the product of the two reduced affine coordinate algebras. Its support lies at the intersection of the two spaces.

First show that every $B_\beta c_\alpha$ vanishes. If $\alpha_i=0$ for some $i$, substitute $B_\beta=-\ell_i c_{\beta+e_i}$ and invoke (6). Otherwise for any $i$ with $\alpha_i>0$ equation (6) gives the transfer
$$
B_\beta c_\alpha=B_{\alpha-e_i}\,c_{\beta+e_i}.
$$
Two successive transfers can swap one unit of $\alpha_i$ with one unit of $\beta_j$ for $j\ne i$, preserving the sum $\alpha+\beta$. Since that sum has degree $2d-1$ and there are at least two variables, choose $i$ with $(\alpha+\beta)_i\le d-1$. As long as $\alpha_i>0$, there is a positive $\beta_j$ for some $j\ne i$, so the two transfers reduce $\alpha_i$ by one. After finitely many steps the coefficient factor misses $x_i$, proving the vanishing. This also proves the coefficient annihilator assertion in Section 1 after arbitrary specialization.

Next (6) gives
$$
\ell_i B_\beta=0\quad\text{if }\beta_i=0,\qquad
\ell_i B_\beta=\ell_j B_{\beta-e_i+e_j}\quad\text{if }\beta_i>0.
$$
For the first statement choose $j\ne i$ in the representation $B_\beta=-\ell_j c_{\beta+e_j}$. The same representation proves the second. Thus $\ell^\delta B_\beta$ vanishes if any $\delta_i>\beta_i$, by transferring $\beta_i$ occurrences of $\ell_i$ to another coordinate and then using the first identity. Otherwise it depends only on $\beta-\delta$: transfer individual occurrences in $\delta$ to compare any two expressions with that difference. This proves that the proposed dual monomial elements span $N$, with the indicated lowering action.

For independence, the component of $C$ of coefficient degree one is presented as an $R_0[\ell]$-module by the $c_\alpha,B_\beta$ and the relations (6). No higher coefficient-degree multiplication contributes a new relation in this piece. Map it to the free module with basis $w_\gamma$ for $|\gamma|\le d$, on which $\ell_i$ lowers the index by $e_i$, giving zero when that is impossible. The map $c_\alpha\mapsto w_\alpha$, $B_\beta\mapsto-w_\beta$ respects (6). On the proposed basis it gives the distinct basis vectors $-w_{\beta-\delta}$. This proves independence over the ground ring and completes (7).

## 5. Relation to the literature

Agrawal and Saxena use truncated quotients by forms in their algebra-isomorphism reduction, with scalar-root hypotheses. Grochow and Qiao give broader isomorphism reductions between tensors and algebras. The anchored relation keeps the graded scalar in the input ring. Here the new calculations concern all higher-degree ungraded lifts, the exact counts over short local rings, and the sharp extremal count via Macaulay growth. The universal square-zero calculation describes the extra scheme structure that field-point counts cannot record. The stated results are informal, and publication priority remains unverified. [Agrawal–Saxena, Theorem 2.3 and Section 6](https://www.cse.iitk.ac.in/%75sers/nitin/papers/cubic-forms.pdf) · [Grochow–Qiao, Part I](https://doi.org/10.1137/21M1441110) · [Grochow–Qiao, Part IV](https://arxiv.org/abs/2306.16317)

The companion [Tensor.py](Tensor.py) checks the mixed counts $9,27$ in equal and mixed characteristic, enumerates all $212$ subspaces of the binary cubics over $\mathbb F_3$ to check the sharp extremal values, and verifies the listed universal module bidegrees for $(n,d)=(2,3),(2,4),(3,4)$ by exact linear algebra.
