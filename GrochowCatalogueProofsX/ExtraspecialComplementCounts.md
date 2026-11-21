# Exact complement counts with an extraspecial kernel

## GP-0427

Let $G$ be a finite group of class at most two and odd prime exponent $p$, and let $K\lhd G$ be extraspecial of order $p^{2m+1}$. Assume $Q=G/K$ is elementary abelian of dimension $d$. One can count complements to $K$ and their conjugacy classes exactly in polynomial bit time, and produce a complement when one exists. The algorithm uses alternating Lie coordinates, which can be constructed from compact permutation generators for $G,K$.

In the class-two Lie coordinates over $\mathbb F_p$ the product is $x*y=x+y+\tfrac12[x,y]$. Write $Z=K'=\mathbb F_p z$, so $V=K/Z$ carries its nondegenerate scalar alternating form $\omega$. The line $Z$ is central in $G$. For $g\in G$, the commutators $[g,K]$ lie in $K\cap Z(G)\subseteq Z$, so they define a linear functional on $V$, represented by a unique $v\in V$ via $\omega$. Subtracting a lift of $v$ from $g$ gives a vector of $C_G(K)$. Therefore $G=K+C_G(K)$ in Lie coordinates, with intersection $Z$.

Choose a linear section $s:Q\to C_G(K)$. Because $Q$ is abelian, $[s(x),s(y)]$ lies in $K\cap C_G(K)=Z$. View it as a scalar alternating form $\eta(x,y)$. Choose a linear lift from $V$ back to $K$. Each linear section of $G\to Q$ is then specified by a map $f:Q\to V$ and a functional $h:Q\to\mathbb F_p$. The section image is a group complement precisely when
$$
f^*\omega=-\eta .
$$
Indeed the bracket of any pair of lifted coordinates is $\eta(x,y)+\omega(f(x),f(y))$. Conversely a group complement is elementary abelian and, as a subgroup of a class-two Lie group of odd exponent, is an additive subspace.

For fixed $f$, conjugating by an element of $K$ preserves $f$ and translates $h$ by $x\mapsto\omega(v,f(x))$, where $v$ is the corresponding vector of $V$. These translations have dimension $\operatorname{rank}(f)$, since every functional on the image of $f$ extends to $V$ and is represented by $\omega$. Thus $f$ contributes $p^d$ complements and $p^{d-\operatorname{rank}(f)}$ conjugacy classes. Conjugacy under $G$ gives the same count, since $G=K L$ for any complement $L$ and $L$ normalizes itself.

### Evaluating the formula

Write $2s_0=\operatorname{rank}(\eta)$ and $t=d-2s_0$. If $s_0>m$ there is no complement. Otherwise choose an ordered symplectic basis of a nonsingular summand of $Q$ for $-\eta$. Its images are a symplectic sequence in $V$. Their number is
$$
E=\prod_{i=0}^{s_0-1}(p^{2(m-i)}-1)p^{2(m-i)-1}.
$$
At each step choose a nonzero first vector in the current symplectic complement and a partner with pairing one, in an affine hyperplane. The radical of $\eta$ maps into the $2M$-dimensional orthogonal complement of that image, where $M=m-s_0$, with totally isotropic image. For image dimension $j$ the number of choices for the image and the onto map to it is
$$
I_j=
\left(\prod_{i=0}^{j-1}\frac{p^{2M-i}-p^i}{p^j-p^i}\right)
\left(\prod_{i=0}^{j-1}(p^t-p^i)\right).
$$
The first product counts ordered isotropic bases, divided by the number of ordered bases of a fixed $j$-space. The second counts onto maps by dualizing and choosing independent images. The range is $0\le j\le\min(t,M)$ and $\operatorname{rank}(f)=2s_0+j$. The two answers are therefore
$$
p^d E\sum_j I_j
\qquad\text{and}\qquad
E\sum_j p^{t-j}I_j .
$$
The products may be evaluated by multiplying numerators and denominators before exact division. To construct a complement, use symplectic basis extension and send the radical to zero. These computations use polynomially many operations on integers whose bit length is polynomial in the Lie dimensions and $\log p$. In compact permutation input, the Lie coordinates and bracket follow from the preceding class-two coordinate algorithm. [Compact class-two coordinates](https://github.com/Dugongue/MathProofs/blob/cbce8131e2cb46db9fcc20e31490cb13eb850e95/GrochowCatalogueProofsIX/ParallelClassTwoIntersection.md)
