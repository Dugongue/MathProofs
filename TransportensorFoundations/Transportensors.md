# Transportensors, their isomorphisms and their automorphism groups

A Transportensor describes a tensor system at every vertex of a directed multigraph, together with linear transport along its edges. It allows a question that the two pieces alone cannot answer: can the *same* choices of local coordinates match the observed tensors and all their transports? This note fixes the meaning of the object. [Complexity](Complexity.md) and [variants](Variants.md) use the conventions below.

## 1. Field, signature and object

Fix a field $k$. A signature $\Sigma$ consists of a finite set $I$ of **named modes** and a finite set $A$ of **named operations**. Each operation $\alpha$ has an ordered input word $i_1\ldots i_s$ and output word $j_1\ldots j_t$ over $I$. Repeated modes are allowed and use the same local coordinate change. The empty word denotes $k$. Mode and operation names are fixed by default.

A finite **Transportensor** $X$ over $(k,\Sigma)$ consists of the following data.

1. A finite set $V_X$ of vertices, a finite set $E_X$ of edges, endpoint maps $s_X,t_X:E_X\to V_X$, and a threshold $\lambda_X:E_X\to\mathbb Q_{\ge0}$. Loops, isolated vertices, empty graphs and distinct edges with identical endpoints are allowed. An ordinary unweighted instance uses zero thresholds.
2. A finite-dimensional $k$-space $W^X_{v,i}$ for every vertex and mode. For a word $B$, write $W^X_{v,B}$ for the ordered tensor product, using the canonical unit convention.
3. For every vertex and operation, a linear map $T^X_{v,\alpha}:W^X_{v,\mathrm{in}(\alpha)}\to W^X_{v,\mathrm{out}(\alpha)}$.
4. For every edge and mode, a linear map $L^X_{e,i}:W^X_{s(e),i}\to W^X_{t(e),i}$.

The $L$ maps may be rectangular or singular. There is no axiom equating the tensor at the head to the tensor transported from the tail. Imposing that equation on every edge defines the separate **parallel** subclass. Transport along a path is the ordered composite, and the empty path has identity transport.

## 2. Homomorphism, isomorphism and automorphism

A **Transportensor homomorphism** $X\to Y$ is a triple $(p,a,g)$ satisfying all of the following.

- Functions $p:V_X\to V_Y$ and $a:E_X\to E_Y$ preserve the ordered endpoints, and $\lambda_Y(a(e))\le\lambda_X(e)$ for every edge.
- For every $v,i$ there is a linear map $g_{v,i}:W^X_{v,i}\to W^Y_{p(v),i}$. Write $g_{v,B}$ for its ordered tensor product on a word $B$, and use the identity of $k$ for the empty word.
- At every vertex and operation,
  $$g_{v,\mathrm{out}(\alpha)} T^X_{v,\alpha}
    =T^Y_{p(v),\alpha}g_{v,\mathrm{in}(\alpha)}.$$
- Along every edge and in every mode,
  $$g_{t_X(e),i} L^X_{e,i}=L^Y_{a(e),i} g_{s_X(e),i}.$$

The identity uses identity functions and identity linear maps. If $(p',a',h)$ follows $(p,a,g)$, their composite is $(p'p,a'a,(h_{p(v),i}g_{v,i})_{v,i})$. Substitution proves the two equations for the composite; associativity follows from ordinary composition. Thus these objects and maps form a category for each fixed field and signature.

A **Transportensor isomorphism** is an invertible homomorphism. Equivalently, $p,a$ are bijections, all $g_{v,i}$ are linear isomorphisms and thresholds agree exactly. Necessity follows by composing with the inverse. Conversely the inverse bijections and inverse matrices satisfy the same equations in reverse. Write $X\cong Y$ when there exists such a triple. Arbitrary vertex and edge identifiers in an input are not labels to be preserved.

A **Transportensor automorphism** is an isomorphism $X\to X$. Its group under the displayed composition is $\operatorname{Aut}(X)$. The identity means *all three* components are identity. Permuting identical parallel edges is a legitimate nonidentity automorphism. The set $\operatorname{Iso}(X,Y)$ carries commuting left and right actions by $\operatorname{Aut}(Y)$ and $\operatorname{Aut}(X)$. Once one witness is fixed, either action parametrizes all witnesses uniquely. Over finite fields this gives zero isomorphisms for a no-instance and exactly $|\operatorname{Aut}(X)|$ for a yes-instance.

## 3. What the automorphism group remembers

Write $Q$ for the directed thresholded multigraph of $X$. Projection of an automorphism onto $(p,a)$ is a group homomorphism. Let $H_X$ be its image in $\operatorname{Aut}(Q)$, and let $K_X$ consist of the field-linear coordinate changes with identity vertex and edge functions satisfying every tensor and edge equation. Then
$$1\longrightarrow K_X\longrightarrow\operatorname{Aut}(X)\longrightarrow H_X\longrightarrow1.$$
The image consists exactly of graph symmetries that lift. Each liftable graph symmetry has a coset of possible linear lifts.

This extension can be nonsplit. Over $\mathbb F_3$ take two vertices and one edge in each direction, both of threshold zero. Use one one-dimensional mode and no vertex operations. Put transport $1$ on the first edge and $-1$ on the return edge. An automorphism fixing the graph uses the same scalar at both vertices, giving $K_X=C_2$. The graph swap lifts with local scalars $(1,-1)$ or $(-1,1)$. Either lift squares to the global scalar $-1$. Hence $\operatorname{Aut}(X)=C_4$ and $H_X=C_2$. There is no choice of lift of the swap having order two.

For a disjoint union, take the weakly connected components of the underlying graph. Isomorphisms permute components of the same Transportensor isomorphism type. Thus if $C_j$ are pairwise nonisomorphic connected types with multiplicities $m_j$, then, up to isomorphism,
$$\operatorname{Aut}(X)\cong\prod_j\bigl(\operatorname{Aut}(C_j)^{m_j}\rtimes S_{m_j}\bigr),$$
where the symmetric group permutes the copies. Choose identifications with a representative in each type to obtain the decomposition. This formula concerns disconnected components and is compatible with nonsplitting *within* a component.

## 4. Examples and invariants

- An ordinary covariant tensor is one vertex, no edges, one nullary operation with the tensor modes as output. Use distinct mode names for independent factor maps. Ordinary tensor restrictions and ordinary tensor isomorphisms are recovered exactly.
- Graphs embed by zero spaces and zero operations (including a zero scalar operation if needed). Simple undirected graphs use the two opposite arcs for each edge. Between such simple graph inputs the vertex map uniquely determines the edge map.
- With one mode, no vertex operations and a specified quiver taken over its identity, one obtains the usual category of quiver representations. Allowing permutations of the quiver defines a different decision problem.
- For an example of coupling, put the named vector $1$ at both ends of a single arrow over $\mathbb F_3$. Edge coefficients $1$ and $2$ give isomorphic undecorated quiver representations. The decorated objects are nonisomorphic because every local map fixing the vector $1$ is the identity.
- Every path yields an intertwining equation by composition. Therefore a closed path gives a similarity class of operators when its combinatorial path is matched. Dimensions, edge ranks and vertex tensor orbits also give necessary invariants. In general these separate tests do not suffice, as the single-arrow example shows.
- Given a *specified* graph identification, in each mode choose a forest of invertible edges common to both sides, traversing them backwards by inversion when necessary. A map at a root determines all maps in that tree by $g_v=P'_v g_r P_v^{-1}$. Substitute into the tensor equations and remaining edge equations, including rectangular edges between trees. This is an exact bijection of solutions since the chosen tree equations are then automatic. Different modes may use different forests.

These definitions preserve the earlier threshold and singular-edge conventions of the proposed seven-type framework. Quiver representations and tensor diagrams are established comparison theories. See [Derksen and Weyman on quiver representations](https://www.math.utah.edu/~ptrapa/math-library/knutson/derksen-weyman-quiver-JAMS.pdf) and [Turner on tensor diagrams](https://arxiv.org/abs/1705.03448). The working name and the complexity arguments here carry no claim of publication priority.
