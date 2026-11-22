# An unrestricted reduction to matrix subgroup conjugacy

Let $k=\mathbb F_q$ with $q=3^e$. From a formal cubic in $n$ variables one can construct generators of a matrix group over $k$ in deterministic polynomial bit time. Two such groups are conjugate in the full general linear group exactly when the cubics are linearly equivalent over $k$. A conjugator yields an explicit cubic transporter in polynomial time. The matrix degree is $2n+2$ for $q\ge9$ and at most $4n+4$ for $q=3$. For fixed $n\ge2$ and $q$, **all output groups are abstractly isomorphic**. The cubic is encoded by their representations. The target permits an arbitrary change of generators when comparing the subgroups.

## Exponentiating the cubic

Let $P(x,y,z)$ be the coefficient of $uvw$ in $f(ux+vy+wz)$. Take the graded commutative algebra
$$
 B_f=k1\oplus V\oplus V^*\oplus ks .
$$
Besides the unit, its products are $xy=P(x,y,-)$ and $x\phi=\phi(x)s$. Products of other positive-degree types are zero. These rules are associative because the only potentially nonzero triple product of positive-degree elements is $xyz=P(x,y,z)s$, which is symmetric. For $x\in V$ set
$$
 u_f(x)=1+x+\tfrac12 x^2+f(x)s,\qquad U_f(x)=L_{u_f(x)}\in\mathrm{GL}(B_f).
$$
The degree-three part of $u_f(x)u_f(y)$ uses $f(x+y)-f(x)-f(y)=(P(x,x,y)+P(x,y,y))/2$. Thus $U_f(x)U_f(y)=U_f(x+y)$. Degree one in $U_f(x)1$ recovers $x$, so the matrices form an elementary abelian group $G_f$ of order $q^n$. A prime-field basis of $V$ supplies its $en$ generators. The degree-three component retains the pure-cube coefficients. A graded map induced by an exact cubic transporter $h$ acts on these grades as $1,h,h^{-*},1$, is an algebra isomorphism, and takes $U_f(x)$ to $U_g(hx)$ by conjugation.

One elementary fact used below is that values on $k^n$ determine a *formal homogeneous cubic* in characteristic three. For $q>3$ all individual degrees are less than $q$. For $q=3$, reduction by $X_i^3-X_i$ changes the pure cubes into distinct linear monomials and leaves all mixed cubics unchanged. These reduced monomials are independent as functions, by univariate interpolation successively in each variable. Hence comparing these functions proves formal polynomial equality.

## Unmarked groups over fields of size at least nine

Choose once per field $a\in k^\times$ of order $m\ge7$. For $q=9$, take an element of order eight by trying the nonzero elements. For $q\ge27$, among any 22 distinct nonzero elements at least one avoids the roots of every $X^i-1$ for $1\le i\le6$. These choices use polynomially many bit operations and require no factorization of $q-1$. Let $D$ act on grade $i$ by $a^i$, $0\le i\le3$. It is an algebra automorphism, and $D U_f(x)D^{-1}=U_f(ax)$. Output
$$
 H_f=\langle G_f,D\rangle=G_f\rtimes\langle D\rangle .
$$
An exact transporter extends as above fixing $D$. Conversely, a conjugator $T:H_f\to H_g$ carries the unique Sylow $3$-subgroup $G_f$ to $G_g$ and takes $D$ to $U_g(v)D^j$ for a unit $j\bmod m$. Multiplying $T$ on the left by a suitable $U_g(z)$ removes $v$, since $1-a^j$ is invertible. The spectrum of $D$ is $\{1,a,a^2,a^3\}$. Equality with the spectrum of $D^j$ gives $j\in\{1,2,3\}$ in this range of representatives. If $j=2$ then $2j=4$ is absent, and if $j=3$ then $2j=6$ is absent. Thus $j=1$ and the adjusted conjugator preserves the four grades.

Write $T1=b1$, $Ts=cs$ and $T|_V=M$. Evaluating $TU_f(x)1=U_g(y)T1$ shows $y=b^{-1}Mx$ and $g(b^{-1}Mx)=(c/b)f(x)$. Cubing is bijective, so $(b/c)^{1/3}b^{-1}M$ is the required exact transporter. To remove the shift algorithmically, read $v$ from the grade-one part of $TDT^{-1}1$. The diagonal grade-one block reveals $a^j$. No discrete logarithm is needed.

## Descent over the prime field

Suppose $k=\mathbb F_3$ and $n\ge2$. Work temporarily over $K=\mathbb F_9$, choose $a$ of order eight, and extend the coefficients of $f$ to $K$. Use the previous algebra over $K$, but output matrices on its underlying $k$-vector space. In addition to $D$ and $G=U_f(K^n)$ include $C=aI$ on the entire algebra and $\sigma$, the coordinate Frobenius $x\mapsto x^3$ in the bases over $k$. All are $k$-linear. The output has degree $4n+4$ and $2n+3$ supplied generators. An exact base-field transporter extends to a graded $K$-linear conjugator commuting with $C,D,\sigma$.

Every element has a unique expression $U_f(v) C^bD^j\sigma^t$, with $b,j\bmod8$ and $t\bmod2$. Indeed $C,D$ act diagonally and independently, $\sigma$ acts semilinearly, and $G$ meets their generated group trivially, as can be seen on the unit and graded pieces. The quotient by $G$ is a group of order $128$, so $G$ is the unique Sylow $3$-subgroup. An element acts on $G\cong(K^n,+)$ by $x\mapsto a^j x^{3^t}$. The only such identity action has $j=t=0$. Consequently the centralizer of $G$ inside the output group is $G\times\langle C\rangle$ and its elements of order prime to three form precisely $\langle C\rangle$.

A conjugator $T$ therefore normalizes $\langle C\rangle$ as a scalar group. Since $C$ generates $K$ as a $k$-algebra, $T$ is $K$-semilinear. Composing with the target $\sigma$ if necessary makes it $K$-linear. Among the $K$-linear elements of the group the quotient by $G\times\langle C\rangle$ is cyclic of order eight generated by $D$. Thus $TDT^{-1}=U_g(v)C^bD^j$ with $j$ odd. Adjust by $U_g(z)$ to remove $v$ as before. In the comparison of $D$ with $C^bD^j$ all four eigenvalues are distinct. On the source the eigenvalue one has a one-dimensional eigenspace on which $G_f$ acts nontrivially in the sense that it does not fix its vectors pointwise. On the target the only one-dimensional candidate with this property is grade zero. Grade three is fixed pointwise and grades one and two each have dimension $n\ge2$. Thus $a^b=1$, and the preceding spectrum argument gives $j=1$. The adjusted $T$ preserves the grades.

Since $T\sigma T^{-1}$ preserves the grading and acts semilinearly, it equals $C^uD^t\sigma$ for some $u,t$. A nonidentity $U_g(v)$ would add a grade-one component to the image of $1$. On grade one the identity $T\sigma=C^uD^t\sigma T$ gives $M=a^{u+t}M^{[3]}$, where the exponent acts on entries. Dividing by one nonzero entry gives an invertible matrix $M_0$ with all entries in $k$. The unit and top comparisons now yield $f=d\,g(M_0x)$ over $K$ for some $d\ne0$. For nonzero cubics, comparing any nonzero coefficient shows $d\in k$. For two zero cubics the identity works. Multiplying $M_0$ by the cube root of $d$ gives an exact $k$-transporter. It is enough to read the scalar and grading blocks in these formulas. Alternatively the adjustment removing $v$ can try all eight options for each scalar exponent and read $v$ from the image of $1$, so its cost is polynomial.

For $n=1$ over $k$ there are two orbits, zero and nonzero. Output the trivial group or $\langle-I_2\rangle$, respectively, and obtain a transporter from the input coefficient ratio. If identical abstract groups are desired for these two inputs as well, use the two order-two subgroups generated by $-I_2$ and $\mathrm{diag}(1,-1)$ instead. The abstract-isomorphism assertion above concerns $n\ge2$.

Plain scalar extension would give false positives. The binary cubics $x^2y+y^3$ and $x^2y-y^3$ have one and three rational projective roots over $\mathbb F_3$, respectively. They become equivalent over $\mathbb F_9$ by the substitution $(x,y)\mapsto(-ix,-y)$ with $i^2=-1$. The Frobenius generator in the construction enforces descent and distinguishes these inputs.

This is a reduction to one **unmarked matrix subgroup conjugacy** instance for every input. A linear-side passage from these generator-defined groups to ordinary three-tensor isomorphism has not been established. The two target problems have different witness equations. The proof is mathematical prose; implementation checks cover the group law, formal transporters and the descent example.
