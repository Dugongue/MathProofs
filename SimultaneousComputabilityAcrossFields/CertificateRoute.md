# Polynomial Calculus certificates for matroid representability across fields

This chapter uses one quadratic Grassmann–Plücker encoding for each matroid, retaining the same variables and integer axioms across all field probes. It gives resource comparisons under minors, duality and direct sums, as well as sharp worst-case degrees at the binary and ternary probes. The classification of representability is classical. The claims about ordinary Polynomial Calculus (PC) concern the encoding specified below.

## 1. The presentation

Let $M$ be a finite matroid of rank $r$ with ordered ground set $E$. For each basis $I$ introduce a bracket $p_I$ and reciprocal $u_I$ and impose $p_Iu_I=1$. Interpret a bracket on an ordered $r$-tuple as its signed basis bracket, or as zero if the tuple repeats an entry or its set is a nonbasis. Use every full Grassmann–Plücker relation
$$
 \sum_{j=1}^{r+1}(-1)^{j-1}
       p_{(I,J_j)}p_{J\setminus J_j}=0
       \qquad (|I|=r-1,\ |J|=r+1).
$$
Over a field the bracket system has a solution exactly when $M$ is representable there. Indeed the full Plücker relations identify nonzero decomposable wedges, and the reciprocal constraints require support exactly the given bases. The rank-zero convention uses the single unconstrained unit bracket for the empty basis and no Plücker relations. [Baker–Bowler, Grassmann–Plücker functions over fields](https://arxiv.org/abs/1601.01204)

At a field probe $K$, we use either the raw system, which detects representability over an algebraic closure for refutations, or the system with all field equations $z^q-z=0$ when the probe is $K=\mathbb F_q$. Use ordinary PC, with binary linear combinations and multiplication by a single variable. Size is the total number of expanded monomial occurrences on all used lines. Let the minimum degree be $+\infty$ if there is no refutation. All statements about exact degree refer to this literal system and these inference rules.

## 2. Exact certificate transfer

**Theorem 1.** For each minor $N$ of $M$, there is one signed variable substitution lifting every PC refutation of $N$ to one of $M$. It preserves the degree and sparse size bounds, and the same substitution works at every field probe, with or without field equations. Duality preserves the exact minimum degree and size.

For the minor, write $N=(M/C)|S$ with $C$ independent. One may first replace any contraction set by a basis of it, since the remaining contracted elements have become loops and can be deleted. In $M/C$, extend a basis of the restriction to $S$ to a full basis using a fixed set $J$ outside $S$. A subset $I\subseteq S$ of size $r(N)$ is a basis of $N$ exactly when $C\cup J\cup I$ is a basis of $M$. For a basis of $N$ its closure in $M/C$ is the closure of $S$, so the same complement $J$ works. For a nonbasis the rank falls short even after adding $J$.

Prefix every bracket by $C,J$ in a fixed order, and send its reciprocal to the reciprocal with the same orientation sign. Every Plücker axiom of $N$ is an axiom of $M$ after prefixing both tuples. Extra summands have a repeated prefix entry and are zero. The reciprocal and field axioms are carried to the corresponding axioms, up to sign. For exact size, carry a sign on each translated line. At an axiom choose the sign of the actual input line, at a multiplication absorb the sign of the multiplier into the output line, and at a linear combination absorb the parents' signs into its scalar coefficients. Choose the sign of the final combination to obtain $1$. The resulting proof has no additional lines from sign corrections. This proves the simultaneous claim.

For duality send a bracket on $I$ to the bracket on $E\setminus I$ with the sign of the concatenation $(I,E\setminus I)$ relative to the ground-set order. Use the same sign on its reciprocal. In a Plücker relation with index sets $I,J$, complement exchanges their roles, giving the relation with index sets $E\setminus J,E\setminus I$. All surviving terms have the same overall sign change. For example, using 1-based labels, the sign of a subset $U$ is $(-1)^{\sum_{i\in U}i-|U|(|U|+1)/2}$, so the product of the two complement signs is independent of the summation index. The remaining permutation parity depends only on the two index sets. Reciprocity and field equations are again preserved. Dualizing twice gives the reverse signed substitution. $\square$

**Theorem 2.** Over every probe, the minimum degree of a direct sum is the minimum of the component degrees. The statement holds for the raw presentation and for the finite-field presentation.

The upper bound is Theorem 1. For the lower bound, order the components consecutively and substitute each bracket and reciprocal of the direct sum by the product of its local brackets and reciprocals. Products in the images of a degree-$D$ line have degree at most $D$ in each separate component. A nonzero term in a full Plücker relation must have its summation index in the unique component where the first index tuple is one short of the component rank and the second is one over. In all other components the bracket factors are fixed. Thus the displayed relation maps to a local Plücker relation times fixed products of local brackets, or to zero. The reciprocity and field axioms telescope to sums of multiples of local axioms. These multiples have degree at most the input axiom's degree in each component.

To account for degree falls, let $\mathcal P_i(D)$ be the degree-$D$ polynomial space in component $i$, and let $\mathcal C_i$ be the span of degree-at-most-$D$ derivable lines of that component's original system. In the tensor product of these polynomial spaces, let $W$ be the sum of the subspaces with at least one factor in $\mathcal C_i$. An image of a legal source axiom lies in $W$ by the preceding identities. Choose bases of the individual spaces simultaneously adapted to the degree filtration and to $\mathcal C_i$. The intersection of $W$ with the tensor product of the degree-at-most-$(D-1)$ spaces consists of the tensor basis elements that still have a consequence factor in that lower part. Multiplication by the image of a source variable multiplies each component by one local variable, and preserves consequence factors for these lower-degree lines. Since a source multiplication through degree $D$ has parent degree at most $D-1$, all legal steps preserve membership in $W$. If every component excludes $1$ from $\mathcal C_i$, choose the constant $1$ as a basis vector outside it in every component. Then $1\notin W$, so the direct sum has no degree-$D$ proof. $\square$

Thus a single minor map transports certificates throughout a list of probes, and direct sum realizes pointwise minima of certificate-degree profiles. This comparison includes the value $+\infty$. It does not require separate selection of a chart or pivot in each field.

## 3. The degree cost of the field axioms

**Theorem 3.** If $r>0$, $M$ is representable over $\overline{\mathbb F_q}$, and $M$ is not representable over $\mathbb F_q$, every PC refutation in the finite-field presentation has degree at least $q+1$.

Give $p_I$ weight $1_I\in\mathbb Z^E$ and its reciprocal weight $-1_I$. The raw axioms are homogeneous for this grading. Let $C$ be their degree-at-most-$q$ consequence space. It is graded: in every linear combination one may take its weight components, and the weight of a component shifts by the weight of the variable in a multiplication. This gives a derivation of each projected component without raising its degree. For each variable $z$, $z^q$ is the only monomial of degree at most $q$ with weight $q\,\mathrm{wt}(z)$. In fact this weight has $1$-norm $qr$. Equality in the triangle bound forces $q$ factors, all with the prescribed sign and with the same support $I$. The graded part of $C$ of that weight is zero, because a geometric solution has $z\ne0$. The pure powers $z^q$ for distinct variables also have distinct weights.

Now adjoin just the scalar span of the field axioms to $C$. A line of degree at most $q-1$ in this enlarged space already lies in $C$, since none of the added pure degree-$q$ monomials can cancel against $C$. The enlarged space is consequently closed under all legal degree-$q$ PC steps, and it still excludes $1$. This proves the bound. The same argument applies to other graded systems for which each field-tested variable is nonzero at a geometric solution and uniquely attains its exposed degree-$q$ weight. $\square$

## 4. Exact binary and ternary benchmarks

**Binary.** Every nonbinary matroid has minimum degree exactly $3$ over $\mathbb F_2$ in the finite-field presentation. By Tutte's theorem it contains $U_{2,4}$ as a minor. In its encoding derive $p_I-1$ for each of the six basis brackets in degree three, by first subtracting $u_I(p_I^2-p_I)$ from $p_I(p_Iu_I-1)$, then comparing with $p_Iu_I-1$. The identity after the first subtraction is $p_Iu_I-p_I=0$. Substitute $p_I=1$ in the three-term Plücker relation, using its individual linear multiples, to obtain $1-1+1=1$ in the field. Lift by Theorem 1. For any matroid, the degree-two span contains no nonzero line of degree less than two. The squared monomials occur only in field axioms, each mixed product $p_Iu_I$ occurs only in its reciprocal axiom, and the Plücker polynomials are homogeneous quadratics on distinct bracket factors. In each nonzero Plücker term the summation element occurs in one factor's tuple and not the other. Therefore there is no legal first multiplication step through degree two that can help produce a constant. [Tutte, Lectures on Matroids](https://nistdigitalarchives.contentdm.oclc.org/digital/api/collection/p16009coll6/id/88448/download)

**A single Fano certificate across characteristics.** The raw Fano and dual Fano systems have a degree-five refutation over $\mathbb Z[1/2]$, using the same signed integer operations and the scalar $1/2$ throughout. Use the seven Fano lines $124,135,236,456,167,257,347$ as zero brackets. Write
$$
 t=p_{123},\quad a=p_{234},\ b=-p_{134},\ c=p_{235},\ e=p_{125},
 \quad f=-p_{136},\ g=p_{126},\quad
 x=p_{237},\ y=-p_{137},\ z=p_{127}.
$$
Three-term Plücker relations with common index $3,2,1$ respectively give $ay-bx,\ cz-ex,\ fz-gy$ as zero lines. More precisely the four remaining indices for these are $(1,2,4,7),(1,3,5,7),(2,3,6,7)$. The three-term relations with common index $2,3$ and remaining sets $(1,3,4,5),(1,2,4,5)$ give $tp_{245}=-ae$ and $tp_{345}=-bc$. The full relation with tuples $(4,5),(1,2,3,6)$ gives $p_{245}f+p_{345}g=0$. Multiplying this by $t$ and substituting the two derived equalities gives $aef+bcg=0$ in degree three. On the other hand,
$$
 z(aef-bcg)=ae(fz-gy)+ge(ay-bx)+gb(ex-cz).
$$
This is a degree-four derivation. Cancel the unit bracket $z$ using its reciprocal, at degree five. Combining the two cubic lines and dividing by two gives $aef=0$, and the three reciprocal cancellations derive $1=0$ through degree four. Unit cancellation of a line $vP=0$ means multiply by the reciprocal $u$ and subtract $P(vu-1)$, using one additional degree. Theorem 1 gives the dual proof and lifts either certificate to any matroid with that minor.

In particular each binary matroid is either regular and has a representation over every field, or it has a binary representation and a degree-five raw certificate after inverting 2, valid over every field of other characteristic. This follows from Tutte's regular-matroid characterization. The certificate is the same over all rejecting probes. [Tutte, Lectures on Matroids](https://nistdigitalarchives.contentdm.oclc.org/digital/api/collection/p16009coll6/id/88448/download)

**Ternary.** Every nonternary matroid has a refutation of degree at most $5$ over $\mathbb F_3$ with field equations, and the bound is attained by $U_{2,5}$. By Seymour's excluded-minor theorem and duality, the upper bound needs only the Fano certificate above and one for $U_{2,5}$. For each basis bracket $p$ with reciprocal $u$, derive $p^2-1$ in degree four by combining $u(p^3-p)$, $-p^2(pu-1)$ and $pu-1$. For $i=3,4,5$, set $a_i=p_{1i}$, $b_i=p_{2i}$, $c_i=a_i b_i$. The three-term relation is $a_i b_j-a_j b_i=p_{12}p_{ij}$ when $i<j$. Multiply its difference by its sum and use the bracket-square identities to derive $c_i c_j+1=0$ in degree four. Indeed its two squared terms equal $1$ and the squared right side equals $1$, so the cross term forces $2c_i c_j=1$, that is $c_i c_j=-1$. The same bracket-square identities give $c_i^2=1$ in degree four. Multiply $c_3c_4+1$ and $c_3c_5+1$ separately by $a_3$, and use $a_3^2=1$ to obtain $b_3c_4+a_3=b_3c_5+a_3=0$ through degree five. Subtract and cancel $b_3$ using $b_3^2=1$, now in degree four since the subtracted line has degree three. This yields $c_4=c_5$, incompatible with $c_4^2=1$ and $c_4c_5=-1$ through degree four. [Seymour, Matroid representation over GF(3)](https://doi.org/10.1016/0095-8956(79)90055-8)

Here is the finite exact check excluding degree four for $U_{2,5}$. Substitute each reciprocal by its matching bracket and work in the quotient $p_I^2=1$. A hypothetical degree-four proof normalizes to one using the five quadratic relations and multiplication by a variable only when the parent representative has degree at most three. All other original axioms normalize to zero. Terms are edge subsets of the complete graph on five vertices and multiplication is symmetric difference of subsets. Let $V_D$ be the span of the five quadratic relations multiplied by all monomials of degree at most $D-2$, then normalized. The ranks of $V_D$ and of its projection to exactly degree $D$ are as follows.

| $D$ | Full rank | Top-degree rank |
|---|---:|---:|
| 2 | 5 | 5 |
| 3 | 50 | 45 |
| 4 | 225 | 175 |

In particular $V_4\cap\mathcal P(3)=V_3$, by inclusion and dimension. Multiplying a line from $V_3$ by one variable stays in $V_4$. So the supposed refutation stays in $V_4$. The same ranks give $V_3\cap\mathcal P(2)=V_2$, and $V_2$ excludes $1$. The following integer-only code reproduces the six ranks, specifying the entire finite calculation.

```python
from itertools import combinations

edges = list(combinations(range(5), 2))
bit = {edge: 1 << i for i, edge in enumerate(edges)}
gp = [
    [(bit[a,b] ^ bit[c,d], 1), (bit[a,c] ^ bit[b,d], 2),
     (bit[a,d] ^ bit[b,c], 1)]
    for a,b,c,d in combinations(range(5), 4)
]

def rank(degree, top_only):
    masks = range(1 << len(edges))
    monomials = [m for m in masks if m.bit_count() <= degree
                 and (not top_only or m.bit_count() == degree)]
    columns = {monomial: index for index, monomial in enumerate(monomials)}
    pivots = {}
    for multiplier in masks:
        if multiplier.bit_count() > degree - 2:
            continue
        for relation in gp:
            row = [0] * len(columns)
            for monomial, coefficient in relation:
                column = columns.get(multiplier ^ monomial)
                if column is not None:
                    row[column] = coefficient
            for column in range(len(row)):
                coefficient = row[column]
                if coefficient == 0:
                    continue
                if column not in pivots:
                    pivots[column] = [x * coefficient % 3 for x in row]
                    break
                pivot = pivots[column]
                row = [(x - coefficient*y) % 3 for x,y in zip(row, pivot)]
    return len(pivots)

assert [(rank(d, False), rank(d, True)) for d in (2,3,4)] == [
    (5,5), (50,45), (225,175)
]
```

## 5. Explicit bounds for larger fields

If a fixed minor $N$ has $b$ bases and is not representable over $\mathbb F_q$, it supplies a PC refutation of any matroid containing it in degree at most
$$
 \max\{q+1,\ 2,\ b(q-2)+1\}.
$$
Indeed for each unit bracket $p$, derive $p^{q-1}-1$ in degree at most $q+1$ using its reciprocal equation and $u(p^q-p)$. The quotient by these powers in the bracket variables alone is the algebra of functions on $(\mathbb F_q^\times)^b$, and each polynomial has a representative of degree at most $b(q-2)$. The Plücker axioms have no common zero there. They generate the unit ideal, which can be reached by successive linear combinations and variable multiplications in the quotient. Replay those operations and reduce after each step using the derived unit-power equations. The degree bound allows one multiplication above the quotient's representative degree. Finally lift by Theorem 1.

For $\mathbb F_4$, Geelen–Gerards–Kapoor give seven excluded minors with at most eight elements, so every nonquaternary matroid has a certificate of degree at most $141$ by this formula. For the named problem of the explicit $\mathbb F_5$ excluded-minor classification, the same result gives degree at most $757$ for any input with an excluded minor on at most ten elements, independent of its rank and ground-set size. It applies to the $2128$ ten-element exclusions enumerated by Brettell, in addition to the smaller ones. The classification beyond these ranges is a separate matroid problem, and the theorem does not extract an explicit bound for the unlisted exclusions. A proved finite bound on the sizes of those exclusions would immediately give an explicit rank-independent PC degree bound by the same formula. [Geelen–Gerards–Kapoor, Theorem 1.1](https://www.math.uwaterloo.ca/~jfgeelen/Publications/gf4.pdf) · [Brettell, Theorem 1.1 and Introduction](https://arxiv.org/html/2307.14614v2#S1) · [Geelen–Gerards–Whittle, Rota announcement](https://ir.cwi.nl/pub/22543)

For any fixed excluded minor and fixed field, the resulting proof has bounded sparse size independently of the parent matroid. The proof can be written using only the bracket names it touches. With a rank oracle, one rank query verifies the basis status of each touched bracket, so no enumeration of all parent brackets is needed to check this certificate. Short rank-query certificates were already studied by Geelen and Whittle, including their $O(n^2)$ bound for all prime fields. The new conclusion here concerns ordinary PC degree and monomial size in a fixed quadratic presentation. [Geelen–Whittle, certifying nonrepresentability](https://arxiv.org/abs/1101.4691)

The proofs are written, with the ternary sharpness calculation checked by the explicit finite rank computation. The bound for an individual field depends on the stated minor hypotheses. The argument uses no number-theoretic conjecture.
