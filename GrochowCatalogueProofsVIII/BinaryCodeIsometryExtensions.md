# Extending all metric isometries of binary linear codes

## GP-0334

For a binary linear code, there is a polynomial-time checkable sufficient condition under which every Hamming isometry of the code, including a nonlinear map, extends to an isometry of the whole cube. In each multiplicity class of the nonzero coordinate functionals, require the sums of distinct unordered pairs to be all different. This includes the case of independent functionals within each multiplicity class. An explicit four-coordinate example shows that a general binary linear code need not have the extension property.

Let $C$ be a binary linear code, regarded as an additive group, and let $S$ be the set of its distinct nonzero coordinate functionals. For $a\in C^*$ write $\chi_a(x)=(-1)^{a(x)}$; let $m_a$ be the coordinate multiplicity of $a$. Coordinates identically zero do not contribute to distances. The matrix with entries $D_{x,y}=d_H(x,y)$ is convolution by
$$
 D_{0,x}=\frac12\sum_{a\in S}m_a(1-\chi_a(x)).
$$
Character orthogonality shows that its negative eigenspaces are exactly the spans of the characters of a fixed positive multiplicity. An arbitrary metric automorphism $f$ permutes the code points and commutes with this distance matrix, so composition by $f$ preserves each such real eigenspace.

In a multiplicity class $S_m$, let a function $g=\sum_{a\in S_m}u_a\chi_a$ take only values in $\{1,-1\}$. Then
$$
 g^2=\sum_a u_a^2+2\sum_{\{a,b\}\subset S_m}u_au_b\chi_{a+b}.
$$
All frequencies in the second sum are nonzero and, by the pair-sum condition, distinct. Since $g^2=1$, every product $u_au_b$ for $a\ne b$ is zero. Thus $g$ is one character times a sign. Apply this to $\chi_a\circ f$. First compose $f$ with translation by $f(0)$, a cube isometry preserving $C$, to arrange that $f(0)=0$. The sign is then positive. The visited characters are a permutation of each multiplicity class because composition by $f$ is invertible. Match the equally many ambient coordinates belonging to each functional with those of its image, and permute the identically zero coordinates arbitrarily. This coordinate permutation implements $f$ on $C$, and undoing the initial translation gives the extension. The multiplicity and pair-sum checks are performed on columns of a generator matrix with at most quadratically many pair sums.

For failure without the condition, take the even-weight subcode of length four. Its eight words form four complementary pairs at distance four; any two words from different pairs have distance two. Thus its metric automorphism group has order $2^4\cdot4!=384$. The stabilizer in the cube isometry group has order $8\cdot4!=192$, since the cube isometries consist of coordinate permutations and translations, and the translations preserving this subcode are exactly its eight even words. The cube isometry description follows by fixing zero and noting that distances to the unit vectors determine any word. Hence some metric automorphisms of the code have no ambient extension. This example gives a multiplicity class with repeated pair sums, as the four functionals add to zero. [Code equivalence and Hamming isometries](https://arxiv.org/html/2607.12870)
