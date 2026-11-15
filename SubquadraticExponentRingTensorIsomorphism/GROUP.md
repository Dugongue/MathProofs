# A class-2 group encoding of tensor isomorphism modulo four

The linear alternating reduction in Section 1 of [the main proof](PROOF.md) gives a radical-free alternating bimap $b:V\times V\to W$ over $R=\mathbb Z/4\mathbb Z$, with $V=R^d,W=R^m$ and $d+m=O(n)$. There is also a direct reduction from these bimaps to class-2 groups of order $4^d8^m$. It gives a separate algorithm with time $2^{O(n^{51/26}\log(n+2))}$ by Sun's Theorem 1.1. [Sun, *Faster Isomorphism for Groups of Class 2*](https://arxiv.org/html/2611.05920)

Take $Z=(\mathbb Z/8\mathbb Z)^m$ and identify $W$ with $2Z$ via the canonical additive embedding $\iota$ that sends a coordinate $a$ to $2a$. For an ordered basis of $V$, put

$$
f(u,v)=\iota\!\left(\sum_{i<j}u_i v_j b(e_i,e_j)\right).
$$

On $V\times Z$ define $(u,z)(v,w)=(u+v,z+w+f(u,v))$. Biadditivity of $f$ gives associativity. The identity is $(0,0)$ and inverses follow from the displayed product. The commutator is $(0,\iota b(u,v))$, and the center is exactly $0\times Z$ by the zero radical. The center and its subgroup of doubles are characteristic. Thus a group isomorphism induces a bimap isometry on $G/Z(G)$ and $2Z(G)$.

For the converse, use the following presentation. The standard lifts $x_i=(e_i,0)$ satisfy $x_i^4=1$. The central basis elements $z_j$ have order eight. The commutators of the $x_i$'s are the prescribed products of $z_j$ corresponding to $\iota b(e_i,e_j)$. These relations are a presentation, since collecting central terms and ordering the $x_i$'s gives at most $4^d8^m$ normal words, and the explicit cocycle group attains that size.

Suppose $g:V\to V'$ and $q:W\to W'$ are an isometry. Any entrywise lift of $q$ to modulus eight is invertible by its odd determinant. It gives a center isomorphism inducing $q$ on doubles. For each basis vector choose the initial lift $(g(e_i),0)$. For any $v$,

$$
(v,z)^4=(0,4z+6f(v,v)).
$$

The term $6f(v,v)$ belongs to $4Z'$. Thus a central adjustment $z$ makes the fourth power trivial, and each basis lift can be adjusted independently. The adjusted lifts obey the required relations because central adjustments have no effect on commutators. The resulting map is an isomorphism since its center and quotient maps are isomorphisms. This is how the extra exponent in the center removes the fourth-power constraint.

The group multiplication is given explicitly and can be tabulated in time polynomial in the group order, which is $2^{O(n)}$. The Cayley-table algorithm from Sun then gives the stated time bound. The [exact finite check](check_group.py) verifies the cocycle computations and adjusted basis lifts on explicit small cases. This note was prepared with AI assistance. Both the proof and the finite checks are independent of the runtime analysis in the main proof.
