# The noncommutative IPS zero ideal

The proof follows the external ChatGPT research bundle supplied by the user. The arguments refer to the two-sided ideal of polynomials vanishing at both substitutions and are independent of the wording of the original open question.

Let $A=k\langle x_1,\ldots,x_n\rangle$, $R=A\langle y_1,\ldots,y_m\rangle$, and $F_j\in A$. Write $\epsilon_0,\epsilon_F:R\to A$ for evaluation at $y=0$ and $y=F$, respectively. The zero ideal is $I=\ker\epsilon_0\cap\ker\epsilon_F$.

If there is a certificate $E$ with $\epsilon_0(E)=0$ and $\epsilon_F(E)=1$, the elements

$$
E^2-E,\qquad [E,x_i],\qquad y_j-EF_j
$$

generate $I$ as a two-sided ideal. They all belong to $I$. In their quotient $E$ is a central idempotent because the $y_j$ are $EF_j$. Each word, and hence every polynomial $P$, then has the form $(1-E)\epsilon_0(P)+E\epsilon_F(P)$. This expression vanishes when $P\in I$. The two evaluations together identify the quotient with $A\times A$.

Finite generation can fail for a satisfiable input. Take $R=k\langle x,z,y\rangle$ and $F=x$. The linear substitution $u=y,\ v=x-y$ turns the ideals into $(u)$ and $(v)$ inside $k\langle u,v,z\rangle$. Their intersection has word basis consisting of words containing both $u$ and $v$. The words $uz^jv$ for $j\ge0$ are pairwise distinct and minimal under taking contiguous factors in this intersection. A finite set of polynomials in the intersection has only finitely many such minimal words in its supports. Left and right multiplication cannot contribute a missing minimal word. Thus the intersection is not finitely generated.

If there is only one input variable $x$ and some $F_j\ne0$, take $g=\gcd(F_1,\ldots,F_m)\ne0$ and polynomials $a_j(x)$ with $\sum_j a_jF_j=g$. Set $E=\sum_j a_j y_j$. The $m+2$ elements $[E,x]$, $E^2-gE$ and $y_j-(F_j/g)E$ vanish under both substitutions. In their quotient every element can be written $a(x)+b(x)E$. For an element of $I$, evaluation at zero gives $a=0$ and the other evaluation gives $bg=0$. The polynomial domain gives $b=0$. If every $F_j=0$, the $y_j$ already generate the ideal.
