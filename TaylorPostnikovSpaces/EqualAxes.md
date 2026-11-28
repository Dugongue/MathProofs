# Equal-axis operations give H-spaces without any finiteness hypothesis

All mathematical claims in this note are **PROVED, confidence 0.99**. The first theorem is a direct argument, and no novelty is claimed. Walter Taylor's *Spaces and equations* (2000), Section 11.5, records the classical mean-operation special case. The result below is stated for homotopy operations and spells out the fundamental-group argument.

Throughout, \(W\) is a pointed connected CW complex, \(k\ge2\), and all homotopies are pointed. Products are taken in compactly generated spaces, and the basepoint is chosen to be a zero-cell. No assumption is made about finite generation of homotopy groups, finite Postnikov height, or simplicity.

## Theorem E1: equal axes

**PROVED, confidence 0.99.** Suppose that \(t:W^k\to W\) is pointed and satisfies the following two requirements.

1. For the diagonal \(\Delta:W\to W^k\), the composite \(t\Delta\) is pointed homotopic to \(\operatorname{id}_W\).
2. If \(\iota_j:W\to W^k\) inserts its input in position \(j\) and the basepoint in every other position, then the maps \(\alpha_j=t\iota_j\) are all pointed homotopic.

Then \(W\) has a pointed H-space structure. Moreover, \(\pi_1(W)\) is abelian, every \(\alpha_j\) is a pointed homotopy equivalence, and multiplication by \(k\) is an automorphism of \(\pi_m(W)\) for every \(m\ge1\).

### Proof: the fundamental group

Write \(G=\pi_1(W)\), initially using multiplicative notation and without assuming that \(G\) is abelian. A based loop in a product is exactly a tuple of based loops; a based homotopy is exactly a tuple of based homotopies. Thus \(\pi_1(W^k)=G^k\), with coordinate inclusions induced by the \(\iota_j\). The map \(t\) induces a group homomorphism

\[
 T:G^k\longrightarrow G.
\]

Let \(a:G\to G\) be the common homomorphism induced by the homotopic maps \(\alpha_j\). Every tuple \((g_1,\ldots,g_k)\) is the product of its coordinate tuples, in coordinate order. Therefore

\[
 T(g_1,\ldots,g_k)=a(g_1)a(g_2)\cdots a(g_k).
\]

Elements in different coordinate subgroups of \(G^k\) commute. Since \(k\ge2\), placing \(g\) in the first coordinate and \(h\) in the second gives

\[
 a(g)a(h)=a(h)a(g)
 \qquad(g,h\in G).
\]

Thus the subgroup \(a(G)\) is abelian.

The normalization \(t\Delta\simeq\operatorname{id}_W\) implies

\[
 g=T(g,\ldots,g)=a(g)^k
 \qquad(g\in G).
\]

The element \(a(g)^k\) lies in \(a(G)\), because \(a\) is a group homomorphism and \(a(g)^k=a(g^k)\). Hence every \(g\) belongs to \(a(G)\), and \(a\) is surjective. Since \(a(G)\) is abelian, \(G\) itself is abelian.

We may now use additive notation. Write \([k]:G\to G\) for multiplication by \(k\). The normalization becomes \([k]a=\operatorname{id}_G\). Integer scalar multiplication commutes with every homomorphism of abelian groups, so

\[
 a[k]=[k]a=\operatorname{id}_G.
\]

Consequently \(a\) is an automorphism with inverse \([k]\), and \([k]\) is an automorphism with inverse \(a\).

### Proof: the higher homotopy groups

For \(m\ge2\), put \(A_m=\pi_m(W)\). These groups are abelian. The coordinatewise description of sphere maps and sphere homotopies identifies \(\pi_m(W^k)\) with \(A_m^k\). Let \(a_m\) be the homomorphism induced by any \(\alpha_j\). The induced homomorphism of \(t\) sends \((u_1,\ldots,u_k)\) to \(\sum_{j=1}^k a_m(u_j)\). Restricting to the diagonal and using normalization gives

\[
 [k]a_m=\operatorname{id}_{A_m}.
\]

Because integer scalar multiplication commutes with \(a_m\), we also have

\[
 a_m[k]=\operatorname{id}_{A_m}.
\]

Thus \(a_m\) is an automorphism with inverse multiplication by \(k\).

### Proof: construction of the multiplication

Choose \(\alpha=\alpha_1\). The preceding calculations show that \(\alpha\) induces an isomorphism on \(\pi_m\) for every \(m\ge1\). It is a pointed map between connected CW complexes. The pointed Whitehead theorem, Hatcher (2002, current Cornell online edition), Theorem 4.5, therefore gives a pointed homotopy inverse \(\beta:W\to W\), with pointed homotopies

\[
 \alpha\beta\simeq\operatorname{id}_W,
 \qquad
 \beta\alpha\simeq\operatorname{id}_W.
\]

Define

\[
 \begin{aligned}
 \mu:W\times W&\longrightarrow W,\\
 \mu(x,y)&=t\bigl(\beta(x),\beta(y),*,\ldots,*\bigr).
 \end{aligned}
\]

On the first coordinate axis this map is \(\alpha_1\beta\), which is pointed homotopic to the identity. On the second coordinate axis it is \(\alpha_2\beta\). Since \(\alpha_2\simeq\alpha_1\) by a pointed homotopy, composition with \(\beta\) gives

\[
 \alpha_2\beta\simeq\alpha_1\beta\simeq\operatorname{id}_W.
\]

Both axis homotopies remain at the basepoint when their input is the basepoint. They therefore agree on the intersection of the two axes. The pushout defining the wedge glues these two homotopies into a pointed homotopy from \(\mu|_{W\vee W}\) to the fold map. Thus \(\mu\) is the required H-space multiplication. \(\square\)

### Scope of the conclusion

The proof does not assert that a map inducing multiplication by \(k\) on all homotopy groups is uniquely determined by that effect. The map \(\beta\) is chosen as an actual homotopy inverse of \(\alpha\), using Whitehead's theorem. No absence of phantom maps is assumed.

The arithmetic condition that multiplication by \(k\) be an automorphism of every homotopy group is necessary for the operation in Theorem E1 to exist. The theorem does not assert that this arithmetic condition alone is sufficient to construct a normalized cyclic or weak near-unanimity operation on an arbitrary H-space.

## Corollary E2: normalized cyclic operations

**PROVED, confidence 0.99.** Suppose that \(t:W^k\to W\) satisfies \(t\Delta\simeq\operatorname{id}_W\) and

\[
 t(x_1,x_2,\ldots,x_k)
 \simeq
 t(x_2,\ldots,x_k,x_1)
\]

as pointed maps \(W^k\to W\). Then \(W\) is an H-space, and multiplication by \(k\) is an automorphism of every homotopy group.

**Proof.** Let \(\rho\) be the displayed cyclic permutation of \(W^k\). Each coordinate inclusion \(\iota_j\) is sent by \(\rho\) to another coordinate inclusion, and repeated applications of \(\rho\) pass through all \(k\) coordinate inclusions. Restrict the pointed homotopy \(t\rho\simeq t\) along each \(\iota_j\). This gives a pointed homotopy between the corresponding two axis restrictions. Concatenating these homotopies around the cycle proves that all axis restrictions are pointed homotopic. Theorem E1 applies. \(\square\)

## Corollary E3: normalized weak near-unanimity

**PROVED, confidence 0.99.** Suppose that \(t:W^k\to W\) is normalized and that the \(k\) maps

\[
 \begin{aligned}
 (x,y)&\longmapsto t(y,x,\ldots,x),\\
 (x,y)&\longmapsto t(x,y,x,\ldots,x),\\
 &\hspace{1.5em}\vdots\\
 (x,y)&\longmapsto t(x,\ldots,x,y)
 \end{aligned}
\]

from \(W\times W\) to \(W\) are pointed homotopic to one another. Then \(W\) is an H-space, and multiplication by \(k\) is an automorphism of every homotopy group.

**Proof.** Precompose every displayed map with

\[
 W\longrightarrow W\times W,
 \qquad z\longmapsto(*,z).
\]

The resulting maps are exactly \(\alpha_1,\ldots,\alpha_k\). Precomposing the given pointed homotopies proves that these axis maps are all pointed homotopic. Theorem E1 applies. \(\square\)

## Corollary E4: normalized means

**PROVED, confidence 0.99.** Suppose that \(t\) is normalized and invariant up to pointed homotopy under every coordinate permutation. Then the conclusions of Theorem E1 hold.

**Proof.** Full permutation symmetry includes the cyclic permutation from Corollary E2. That corollary gives the conclusion. \(\square\)

## Corollary E5: near-unanimity forces contractibility

**PROVED, confidence 0.99.** Suppose that \(k\ge3\) and that \(t\) satisfies the pointed homotopy identities

\[
 \begin{aligned}
 t(y,x,\ldots,x)&\simeq x,\\
 t(x,y,x,\ldots,x)&\simeq x,\\
 &\hspace{1.5em}\vdots\\
 t(x,\ldots,x,y)&\simeq x.
 \end{aligned}
\]

Then \(W\) is contractible.

**Proof.** Substitute \(y=x\) in any one of the identities. This gives \(t\Delta\simeq\operatorname{id}_W\). Substitute \(x=*\) and \(y=z\) in the identity whose exceptional entry is in position \(j\). This gives a pointed nullhomotopy of \(\alpha_j\), for every \(j\).

For the fundamental group, the homomorphism \(T:G^k\to G\) induced by \(t\) is trivial on every coordinate subgroup because every \(\alpha_j\) is nullhomotopic. Every element of \(G^k\) is a product of coordinate-subgroup elements, so \(T\) is the trivial homomorphism. Its restriction to the diagonal is therefore trivial. Normalization says that this restriction is \(\operatorname{id}_G\), so \(G\) is trivial.

For \(m\ge2\), the homomorphism

\[
 \pi_m(W)^k\longrightarrow\pi_m(W)
\]

induced by \(t\) is the sum of the homomorphisms induced by the coordinate-axis restrictions. Each is zero, so the total map is zero. Its restriction to the diagonal is both zero and the identity. Hence \(\pi_m(W)=0\) for every \(m\ge2\).

The unique map \(W\to *\) is an isomorphism on all homotopy groups and on components. Whitehead's theorem makes it a homotopy equivalence because \(W\) is a CW complex. Therefore \(W\) is contractible. \(\square\)

## Examples and limitations

### E6: H-spaces with no normalized cyclic operations

**PROVED, confidence 0.99.** If some \(\pi_m(W)\) is \(\mathbb Z\), or has a \(\mathbb Z\) direct summand, then \(W\) admits no normalized equal-axis operation of any arity \(k\ge2\).

**Proof.** Multiplication by \(k\) is not surjective on a \(\mathbb Z\) summand: its composite with the projection to that summand has image in \(k\mathbb Z\), which does not contain \(1\). Theorem E1 proves that this multiplication would have to be an automorphism if such an operation existed. \(\square\)

In particular, the circle \(S^1\) is an H-space under ordinary complex multiplication but has no normalized cyclic operation of arity \(k\ge2\). The same obstruction applies to each \(K(\mathbb Z,m)\), even though addition gives it an abelian H-space structure. Thus the existence of an H-space structure does not imply the existence of a normalized cyclic operation.

### E7: examples without finite generation

**PROVED, confidence 0.99.** Let \(A\) be an abelian group on which multiplication by \(k\) is an automorphism. In a strict abelian Eilenberg–MacLane model \(K(A,m)\), define

\[
 t(x_1,\ldots,x_k)=[k]^{-1}(x_1+\cdots+x_k),
\]

where \([k]^{-1}\) is induced by the inverse group homomorphism \(A\to A\). This operation is cyclic and satisfies \(t(x,\ldots,x)=x\).

**Proof.** Use the simplicial abelian model

\[
 \mathcal K(A,m)_q=Z^m(\Delta[q];A),
\]

where the right side denotes normalized simplicial cocycles and simplicial operators act by pullback. May (1967), Theorem 23.9, gives its simplicial homotopy groups; Theorems 16.1 and 16.6 identify them with those of its realization, and Theorem 14.1 makes that realization a CW complex. Addition and the coefficient homomorphisms \([k]\) and \([k]^{-1}\) act on the cocycles themselves. Their identities hold in each simplicial degree. Realization preserves finite products in compactly generated spaces, as specified by May (1967), Theorem 14.3 with the compactly generated interpretation recorded in the Bibliographical Notes to Chapter III. Thus these operations give continuous operations on the realization, and their identities remain exact. The sum \(x_1+\cdots+x_k\) is permutation invariant, proving cyclicity. Substituting \(x\) in every coordinate gives \([k]^{-1}[k]x=x\), proving normalization. \(\square\)

Taking \(A=\mathbb Q\) gives examples with homotopy groups that are not finitely generated. Taking \(A=\mathbb Z/q\) for a prime \(q\) not dividing \(k\) gives finite examples. These examples demonstrate the range of the theorem; they are not needed in its proof.

### E8: general normalized Taylor does not imply equal-axis normalization

**PROVED, confidence 0.99.** The circle \(S^1\), regarded as an abelian topological group, has the normalized Mal'cev operation

\[
 m(x,y,z)=xy^{-1}z.
\]

It satisfies

\[
 m(x,y,y)=x,
 \qquad m(y,y,x)=x,
 \qquad m(x,x,x)=x
\]

exactly. These identities include Taylor identities distinguishing every input position: the identity

\[
 m(x,y,y)=m(x,x,x)
\]

distinguishes positions \(2\) and \(3\), and the identity

\[
 m(y,y,x)=m(x,x,x)
\]

distinguishes positions \(1\) and \(2\). Thus \(m\) is a normalized Taylor operation.

However, \(\pi_1(S^1)=\mathbb Z\), so E6 excludes every normalized equal-axis operation of arity at least two on the same space, whether or not it is built as a term from \(m\). Therefore general normalized Taylor operations do not imply normalized cyclic or weak near-unanimity operations in this setting.

## A stronger obstruction to a single binary-term extraction argument

The following statement concerns algebraic term extraction. It supplies an explicit infinite-height example, with every homotopy group finitely generated, in which no binary term in the given Taylor operation and the basepoint has two axis maps that are homotopy equivalences. The underlying space nevertheless has an abelian H-space structure.

**Proposition E9 — PROVED, confidence 0.99.** There is a pointed connected CW topological abelian group \(W\), in compactly generated spaces, with

\[
 \pi_n(W)\cong\mathbb Z
 \qquad(n\ge1),
\]

and a continuous endomorphism \(T:W\to W\) that induces multiplication by \(n\) on \(\pi_n(W)\). On this space the operation

\[
 t(x_1,x_2,x_3,x_4)
  =(3T-I)x_1+Tx_2+(I-2T)x_3+(I-2T)x_4
 \tag{E9.1}
\]

is normalized and satisfies the Siggers identity

\[
 t(x,y,x,z)=t(y,x,z,y).
 \tag{E9.2}
\]

Nevertheless, no binary term \(\tau(x,y)\) built from \(t\), the two variables, and the zero constant has both restrictions \(\tau(x,0)\) and \(\tau(0,y)\) homotopy equivalences of \(W\).

### Proof: an explicit simplicial model for the space and the endomorphism

For every \(n\ge1\), let

\[
 \mathcal K_n=\mathcal K(\mathbb Z,n),
 \qquad
 (\mathcal K_n)_q=Z^n(\Delta[q];\mathbb Z),
\]

with the cocycle model used in E7. Define the simplicial abelian group

\[
 \mathcal G=\bigoplus_{n\ge1}\mathcal K_n,
 \qquad
 W=|\mathcal G|.
 \tag{E9.3}
\]

This direct sum is formed in each simplicial degree, with coordinatewise addition and coordinatewise face and degeneracy maps. If \(n>q\), there are no normalized \(n\)-cochains on \(\Delta[q]\), so \((\mathcal K_n)_q=0\). Consequently

\[
 \mathcal G_q=\bigoplus_{1\le n\le q}(\mathcal K_n)_q;
\]

only finitely many coordinates occur in each degree. The realization is a CW complex by May (1967), Theorem 14.1. In degree zero every factor is zero, so \(W\) has exactly one vertex and is connected. Realization preserves finite products in compactly generated spaces, by May (1967), Theorem 14.3 with the correction stated in the Bibliographical Notes to Chapter III. Realizing the addition, inverse, and zero of \(\mathcal G\) therefore equips \(W\) with a continuous strict abelian group structure. All group identities are identities of simplicial maps before realization, so they are exact identities afterwards.

For \(r\ge1\), put

\[
 \mathcal G^{(r)}=\bigoplus_{1\le n\le r}\mathcal K_n.
\]

This is a simplicial subgroup and a simplicial subset of \(\mathcal G\). Its realization is a CW subcomplex: its nondegenerate simplices are a subset of those of \(\mathcal G\), and their faces remain in the subgroup. Every simplex of \(\mathcal G\) belongs to some \(\mathcal G^{(r)}\). Hence the CW cells of \(W\) are exhausted by the subcomplexes \(|\mathcal G^{(r)}|\).

We verify explicitly the compactness fact needed to compute the homotopy groups. A compact subset of a CW complex is contained in a finite subcomplex. If this were false, the subset would meet infinitely many distinct open cells; choose one point in each of countably many such cells. The resulting point set, and each of its subsets, meets the closure of any fixed cell in a finite set, because a cell closure meets only finitely many open cells. A finite set in a Hausdorff space is closed. The weak topology of the CW complex therefore makes the chosen point set and each of its subsets closed in the CW complex. In particular the chosen set is a closed infinite discrete subspace of the compact subset. It would have to be compact, although its open cover by singletons has no finite subcover. This contradiction proves that the compact subset meets only finitely many cells. Closure finiteness then places it in a finite subcomplex.

Apply this fact to a continuous map from a sphere, or from a sphere times an interval, into \(W\). Its image lies in a finite subcomplex. Each of the finitely many cells of that subcomplex lies in some \(|\mathcal G^{(r)}|\). Taking the maximum of these finitely many values of \(r\) puts the whole map, or the whole homotopy, into one \(|\mathcal G^{(r)}|\). It follows that

\[
 \pi_m(W)
   \cong\varinjlim_r\pi_m\bigl(|\mathcal G^{(r)}|\bigr)
 \qquad(m\ge1).
 \tag{E9.4}
\]

Surjectivity of this comparison follows because a sphere map factors through one finite subcomplex. Injectivity follows because a nullhomotopy, or a homotopy between two representatives, also factors through one finite subcomplex.

The sum defining \(\mathcal G^{(r)}\) is finite, so it is also the product of its factors. Finite-product preservation under realization gives

\[
 |\mathcal G^{(r)}|
   \cong\prod_{1\le n\le r}|\mathcal K_n|
\]

in compactly generated spaces. May (1967), Theorems 23.9, 16.1, and 16.6, identify \(|\mathcal K_n|\) as \(K(\mathbb Z,n)\). Homotopy groups of a finite product are products of the homotopy groups of the factors, because sphere maps and their homotopies are specified coordinate by coordinate. Therefore

\[
 \pi_m\bigl(|\mathcal G^{(r)}|\bigr)
   \cong
   \begin{cases}
    \mathbb Z,&m\le r,\\
    0,&m>r.
   \end{cases}
\]

The map from stage \(r\) to stage \(r+1\) is the identity on each existing factor and inserts zero in the new factor. In every fixed degree \(m\), the displayed system is thus eventually the constant group \(\mathbb Z\) with identity maps. Equation (E9.4) proves \(\pi_m(W)\cong\mathbb Z\).

On \(\mathcal G\), define \(T\) to be multiplication by \(n\) on the summand \(\mathcal K_n\). This is a simplicial group endomorphism, so its realization is continuous. At finite stages it acts by multiplication by \(m\) on the unique summand contributing to \(\pi_m\). Passing through (E9.4), it acts by multiplication by \(m\) on \(\pi_m(W)\). Addition, subtraction, and composition of the endomorphisms \(T\) and \(I\) are continuous, so (E9.1) defines a continuous pointed operation.

### Proof: the normalization and every required Taylor identity

The four endomorphism coefficients in (E9.1) sum to \(I\):

\[
 (3T-I)+T+(I-2T)+(I-2T)=I.
\]

Therefore \(t(x,x,x,x)=x\) exactly. The coefficients of \(x,y,z\) on the left side of (E9.2) are, in order,

\[
 (3T-I)+(I-2T)=T,
 \qquad T,
 \qquad I-2T.
\]

The coefficients of \(x,y,z\) on the right side are

\[
 T,
 \qquad(3T-I)+(I-2T)=T,
 \qquad I-2T.
\]

The coefficients agree, so (E9.2) is an exact identity. To verify the specified two-variable Taylor requirement, substitute \(z=x\) and then \(z=y\). This gives

\[
 \begin{aligned}
 t(x,y,x,x)&=t(y,x,x,y),\\
 t(x,y,x,y)&=t(y,x,y,y).
 \end{aligned}
 \tag{E9.5}
\]

In the first identity, the two argument words differ in positions \(1\), \(2\), and \(4\). In the second identity, they differ in positions \(1\), \(2\), and \(3\). Every input position is therefore distinguished by one of these two-variable identities. Together with the normalization already proved, they are explicit normalized Taylor identities for \(t\).

### Proof: every binary term has polynomial coefficients

We prove by induction on the construction of a binary term that

\[
 \tau(x,y)=P(T)x+Q(T)y
 \tag{E9.6}
\]

for polynomials \(P,Q\in\mathbb Z[z]\). The term \(x\) has coefficients \((1,0)\), the term \(y\) has coefficients \((0,1)\), and the zero constant has coefficients \((0,0)\). These are the base cases.

Suppose that four terms \(\tau_j\), for \(1\le j\le4\), have coefficient pairs \((P_j,Q_j)\). Substituting them into \(t\) yields coefficients

\[
 \begin{aligned}
 P&=(3z-1)P_1+zP_2+(1-2z)P_3+(1-2z)P_4,\\
 Q&=(3z-1)Q_1+zQ_2+(1-2z)Q_3+(1-2z)Q_4.
 \end{aligned}
\]

These are integer polynomials, and distributivity in the topological abelian group gives (E9.6). This proves the induction.

### Proof: invertible axis maps would force impossible constant polynomials

The first restriction of (E9.6) is \(P(T)\). On \(\pi_n(W)\cong\mathbb Z\), it acts by multiplication by \(P(n)\), because \(T\) acts there by \(n\). If this axis restriction were a homotopy equivalence, then

\[
 P(n)\in\{1,-1\}
 \qquad(n\ge1).
\]

Thus \(P(z)^2-1\) would have infinitely many distinct integer roots. A nonzero polynomial of degree \(d\) over \(\mathbb Q\) has at most \(d\) roots: division by \(z-a\) lowers the degree by one at each distinct root, so more than \(d\) roots force the zero polynomial. Consequently \(P(z)^2-1=0\). Since \(\mathbb Z[z]\) is an integral domain,

\[
 (P-1)(P+1)=0
\]

implies that \(P\) is the constant polynomial \(1\) or the constant polynomial \(-1\).

The second restriction is \(Q(T)\). If it is a homotopy equivalence, it acts invertibly on each \(\pi_n(W)\), so \(Q(n)\in\{1,-1\}\) for every positive integer \(n\). Applying the root-counting argument to \(Q(z)^2-1\) proves that \(Q\) is also one of the constant polynomials \(1\) and \(-1\).

Now evaluate the formal operation at \(z=2/5\). Its four coefficients become

\[
 3\left(\frac25\right)-1=\frac15,
 \qquad \frac25,
 \qquad 1-2\left(\frac25\right)=\frac15,
 \qquad 1-2\left(\frac25\right)=\frac15.
\]

They are nonnegative and sum to one. For every binary term, its evaluated coefficient pair therefore satisfies

\[
 P(2/5)\ge0,
 \qquad Q(2/5)\ge0,
 \qquad P(2/5)+Q(2/5)\le1.
 \tag{E9.7}
\]

Here is the full induction establishing (E9.7). The initial pairs \((1,0)\), \((0,1)\), and \((0,0)\) all satisfy these three inequalities. At an operation node, the new pair is the convex combination of its four input pairs with weights \(1/5,2/5,1/5,1/5\). Each new coordinate is a sum of nonnegative terms. The sum of the two new coordinates is the same convex combination of the four input coordinate sums; each input sum is at most one, so the new sum is at most the sum of the weights, which is one. This completes the induction.

If both axis restrictions were homotopy equivalences, we proved that \(P\) and \(Q\) would be constant polynomials with values in \(\{1,-1\}\). Their nonnegativity in (E9.7) would force \(P=Q=1\). Their sum at \(2/5\) would then be \(2\), contradicting the last inequality in (E9.7). No binary term can have both axis restrictions homotopy equivalences. This proves Proposition E9. \(\square\)

This example does not contradict the proposed general implication from normalized Taylor operations to H-space structures: \(W\) itself is a topological abelian group. It proves that a strategy extracting a single binary term with invertible coordinate restrictions cannot succeed uniformly from the Taylor identities alone in infinite Postnikov height. The obstruction is already algebraic on the graded family \(\pi_n(W)=\mathbb Z\), with \(T\) acting in degree \(n\) by multiplication by \(n\); the explicit realization above verifies that this algebraic family occurs in the stated category of spaces.

## References and citation scope

* Allen Hatcher (2002), *Algebraic Topology*, current Cornell online edition, Theorem 4.5 (Whitehead). The theorem is invoked only after the induced homotopy-group isomorphisms have been proved explicitly.
* J. Peter May (1967), *Simplicial Objects in Algebraic Topology*, Theorem 14.1 (CW realization), Theorem 14.3 (realization and products, interpreted in compactly generated spaces as explained in the Bibliographical Notes to Chapter III), Theorems 16.1 and 16.6 (comparison with the homotopy groups of realization), and Theorem 23.9 (the simplicial Eilenberg–MacLane cocycle model). These results justify the strict abelian CW models and the explicit realization in Proposition E9.
* Walter Taylor (2000), *Spaces and equations*, *Fundamenta Mathematicae* **164**(3), 193–240, Section 11.5. This section records the mean-operation CW-complex special case and distinguishes it from the general H-space compatibility problem. Primary-author manuscript: <https://spot.colorado.edu/~wtaylor/main.pdf>. This reference supplies historical context; no proof step above is delegated to its unnumbered assertion.
