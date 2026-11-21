# GP-0743 · Geometric IPS for bounded-incidence-treewidth Boolean CSPs

**Theorem.** Let the local constraint polynomials $F_a(X_{S_a})$ have arity at most $r$, with the Boolean axioms $X_i^2-X_i=0$ included. An instance over any field $K$ with no Boolean solution and incidence treewidth $k$ has a division-free Geometric IPS certificate with $4^{O(r(k+1))}\operatorname{poly}(L)$ arithmetic gates, where $L$ is the input description length. For the usual $0/1$ violation-indicator encoding the construction uses only the input constants and $0,1,-1$.

Introduce placeholders $y_a,z_i$ for the local and Boolean axioms. In a bag $B$, work in the free algebra over $K[y,z]$
$$
R_B=K[y,z][u_i:i\in B]/(u_i^2-u_i-z_i:i\in B).
$$
The free basis consists of squarefree products of the bag variables. The involution $u_i\mapsto1-u_i$ is well defined. Write a bag element uniquely as $A+B'u_i$, with $A,B'$ independent of $u_i$. Its norm on forgetting $i$ is
$$
(A+B'u_i)(A+B'(1-u_i))=A^2+AB'-(B')^2z_i .
$$
This product is independent of $u_i$. At $z_i=0$, it is the product of evaluations at $u_i=0,1$. At $z_i=X_i^2-X_i$, substitution of $u_i=X_i$ or $1-X_i$ gives one factor at either root and the other at the complementary root.

Replace each constraint vertex in an incidence decomposition by its incident variables. A variable remains connected because its original bags meet the bags of each incident constraint. Each constraint support fits in one bag and the new bag size is at most $\max(1,r)(k+1)$. Use a rooted nice decomposition with empty root and leaves. Assign every local constraint to one bag containing its variables.

For constraint $a$, let $C_a$ be the set of nonzero values it takes on its Boolean inputs. Its local test is
$$
D_a=1-\prod_{c\in C_a}\left(1-(F_a(u)-y_a)/c\right).
$$
This vanishes whenever $F_a(u)=y_a$. If $y_a=0$ and $u$ is Boolean, it is exactly the $0/1$ violation flag. For $0/1$ violations one can directly use $F_a(u)-y_a$. All divisions in the general formula are by fixed nonzero field constants. If the constraint vanishes everywhere on its Boolean cube, the empty product gives the constant zero test.

Start at the leaves with zero. At an introduce-variable edge carry the child polynomial into the larger bag. At a forget-variable edge take the indicated norm. At joins and when adding local tests, combine values by $U+V-UV$. There are two inductive identities.

1. At $y=z=0$ and a fixed Boolean bag assignment, the value is the $0/1$ flag for there being no extension satisfying the subtree constraints. The join and local operation is OR. The forget operation is AND of the two failure flags, since either choice suffices to find a satisfying extension. Outside the bag the two child variable sets at a join are disjoint.
2. At $y_a=F_a(X)$, $z_i=X_i^2-X_i$ and $u_i=X_i$ for every bag variable, the value is identically zero in the indeterminates $X$. This holds for local tests. At forget nodes the product has the child evaluation at $X_i$ as a factor, and at joins the operation preserves two zeros. This is a formal substitution into $K[X]$, so it also works in finite characteristic.

The empty-root polynomial $P(y,z)$ therefore has $P(0)=1$ and $P(F(X),X^2-X)=0$, the Geometric IPS identities. No division by a circuit-computed expression is needed. Compute on coefficient vectors of length $2^{|B|}$; to multiply squarefree monomials use $u_i^2=u_i+z_i$ at common variables. Every ring operation costs $4^{O(|B|)}$ gates and may share earlier coefficient gates. Evaluate the input local circuits inside these algebras. A decomposition can be obtained in polynomial time for fixed $k$, or used directly if supplied. [Grochow–Pitassi, Geometric IPS definition and Boolean existence](https://www.cs.toronto.edu/~toni/Papers/jacm-gp.pdf)
