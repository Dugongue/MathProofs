# Difference-family designs with identical intersection distributions

Two explicit ordinary $(256,4,124)$ difference families have nonisomorphic developments with identical block-intersection distributions. Their simple short developments give two nonisomorphic $2$-$(256,4,31)$ designs with the same distribution. This supplies a concrete instance of the phenomenon requested in Kaspers–Pott, §5, third item, using the vanishing-flat construction from the project notes. The base families overlap, so a requirement that the families be disjoint would impose an additional condition. [Kaspers–Pott, §5](https://arxiv.org/html/1907.05848v2#S5) · [Boykett–Mayr, short difference families](https://arxiv.org/abs/math/0401239) · [Li, Meidl, Polujan, Pott, Riera and Stănică, vanishing flats](https://arxiv.org/abs/2006.01941)

## The two base families

Let $K=\mathbb F_2[t]/(t^4+t+1)$ and write $\alpha$ for the class of $t$. The polynomial has no root in $\mathbb F_2$ and is coprime to $t^2+t+1$, the only irreducible quadratic. Thus $K$ is the field of order 16. The element $\alpha$ has order 15. Its order divides 15, an order of 1 or 3 would contradict degree four, and an order of 5 would make it a root of $t^4+t^3+t^2+t+1$. Put $a_2=\alpha^5$ and $a_4=\alpha$, of degrees two and four over $\mathbb F_2$.

For $a\in\{a_2,a_4\}$ define $F_a\colon K^2\to\mathbb F_2^2$ by
$$
F_a(x,y)=(\operatorname{Tr}(xy),\operatorname{Tr}(a xy)),
$$
where $\operatorname{Tr}$ is the trace to $\mathbb F_2$. Its second derivatives are the two alternating bilinear pairings
$$
 Q(u,v)=\operatorname{Tr}(u_1v_2+u_2v_1),
 \qquad
 Q(au,v).
$$
Take as base blocks all 2-dimensional $\mathbb F_2$-subspaces of $V=K^2$ on which both pairings vanish. Write $D_a$ for the simple design obtained by taking all distinct translates of the base blocks. Its blocks are exactly the vanishing affine 2-flats of $F_a$.

The form $Q$ is nondegenerate by trace duality. For any nonzero $u\in V$, the functionals $Q(u,-)$ and $Q(au,-)$ are independent because $u,au$ are independent over $\mathbb F_2$. Their common kernel $K_u$ therefore contains 64 elements. The vectors $0,u$ are in $K_u$, while each $v\in K_u\setminus\{0,u\}$ spans a selected plane with $u$. Exactly two such vectors span each plane, namely $v$ and $v+u$. Thus each nonzero difference $u$ belongs to $(64-2)/2=31$ base blocks. Each such block contributes four ordered occurrences of difference $u$. This gives a $(256,4,124)$ ordinary difference family. The translation stabilizer of a base block is the block itself, of size four. Its short development is $D_a$, a $2$-$(256,4,31)$ design, because each selected plane containing a nonzero difference gives precisely one affine block through any given point pair with that difference.

## The intersection distribution

Two distinct affine 2-flats on a binary vector space can meet in 0, 1, or 2 points. In any design with these possible intersections and fixed parameters $v,k,\lambda$, the number of unordered distinct block pairs meeting in two points is $\binom v2\binom\lambda2$. The sum over all unordered block pairs of their intersection sizes equals $v\binom r2$, where $r$ is the number of blocks containing each point. Subtracting twice the number meeting in two points gives the number meeting in one point. All remaining pairs are disjoint. Here $r=2635$ and the number of blocks is 168,640. The counts for sizes $0,1,2$ are respectively $13{,}346{,}422{,}560$, $858{,}040{,}320$, and $15{,}177{,}600$ in both designs.

Under the full-development convention retaining multiplicity, each simple block occurs four times. Intersections between different underlying blocks therefore multiply the three counts by 16, and the pairs with the same underlying block contribute $6\cdot168640$ intersections of size four. The distributions agree under this convention as well.

## Why the designs are nonisomorphic

At any point, take the blocks through it, delete that point, and join two remaining points by an edge if some such block contains both. A design isomorphism carries this graph to the corresponding graph at the image point. Translations are automorphisms of each design, so it suffices to compare the graphs at zero. Their vertices are the nonzero vectors $u\in V$, and the closed neighborhood of $u$ is exactly $K_u\setminus\{0\}$. The kernel computation and trace duality give
$$
 K_u=K_v
 \quad\Longleftrightarrow\quad
 \operatorname{span}_{\mathbb F_2}\{u,au\}
 =
 \operatorname{span}_{\mathbb F_2}\{v,av\}.
$$
Let $S_a=\operatorname{span}_{\mathbb F_2}\{1,a\}$. For a fixed nonzero $u$, the equality holds exactly for $v=cu$ where $c\in K^\times$ satisfies $cS_a=S_a$. For $a=a_2$, this subspace is $\mathbb F_4$ and its multiplicative stabilizer has order three. For $a=a_4$, the stabilizer embeds in $\operatorname{GL}_2(\mathbb F_2)$ by multiplication, since it acts faithfully on 1. Its order divides both 15 and 6. If the order were three, it would contain a generator $c$ of $\mathbb F_4^\times$. Since $1\in S_{a_4}$ and $cS_{a_4}=S_{a_4}$, the subspace would be $\mathbb F_4$, contradicting the degree of $a_4$. Hence the stabilizer is trivial.

The relation of having equal closed neighborhoods is a graph invariant. Its classes all have size three for $a_2$ and all have size one for $a_4$. The graph pair and thus the two simple developments are nonisomorphic. An isomorphism of the full repeated-block developments would induce one on the distinct block supports, so those developments are nonisomorphic too.
