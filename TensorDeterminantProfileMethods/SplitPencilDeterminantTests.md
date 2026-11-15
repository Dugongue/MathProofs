# Determinant tests for pencils with split determinant divisors

Informal proof. Fix a finite field $F=\mathbb F_q$. A matrix pencil is a linear map $M:V\to\operatorname{Hom}_F(X,Y)$ with $\dim X=\dim Y=n$. Write $P_M(x)=\det M(x)$ in the input bases. Use the transporter convention
$$
M_B(fx)=hM_A(x)g^{-1}.
$$
The two covariant characters of interest are $d_f=\det f$ and $\mu=\det h/\det g$. In particular the product of the three covariant determinants is $d_f^{-1}\mu$.

**Theorem 1.** Suppose $P_A$ is formally nonzero and splits into geometric linear factors, and the common kernel of the factors has dimension $w$. Suppose its Frobenius orbits of geometric factors have pairwise distinct pairs (orbit length, multiplicity). For any fixed exponents $a,b$ and $\eta\in F^\times$, there is a deterministic same-field many-one reduction, of cost polynomial in the dense input length and $2^w$, for the existence of a transporter with $d_f^a\mu^b=\eta$. It also handles any prescribed pair $(d_f,\mu)$ in one instance. The linear factors may overlap in their spans and use different fields of arbitrarily large degrees. The source alone needs the promise.

**Theorem 2.** Dropping the distinction between orbit types gives a deterministic polynomial-time ordinary TI Cook reduction for the entire attainable set of pairs $(d_f,\mu)$ whenever $w=O(\log L)$, where $L$ is the dense input length. No search-to-decision theorem for witnesses of arbitrary tensors is required.

Testing the prescribed pair $(1,1)$ decides SL-TI on its promise whenever $n$ is invertible modulo $q-1$, with no condition on $\dim V$. Indeed, one common scalar on $g,h$ corrects both of their equal determinants, leaving $f$ fixed. If only the single product character is tested, it suffices that $\dim V,n$ have the same unit residue modulo $q-1$. Under that condition the scalar triples of product one correct every determinant triple whose product is one. The statements specify the product or the two displayed characters for other dimensions. [Open Question 1.9](https://arxiv.org/html/2306.03135v2).

## 1. Separate Frobenius orbits

Recover the normalized absolute factor lines, multiplicities, and separate field representations using the degree-one case of the [geometric factor recovery appendix](GeometricPencilFactorRecovery.md). This computes each orbit in degree at most $n$, with no common splitting field. Its bounded-degree hitting curve chooses one affine line whose formal restrictions separate the distinct factors, and monic Hensel lifting recovers the complete linear forms with their multiplicities. Fixed-characteristic univariate factoring and compatible finite-field models have polynomial cost. [Shoup’s finite-field construction](https://www.shoup.net/papers/detirred.pdf).

For each matched orbit choose a normalized representative $\ell_{M,i}:V_M\to E_i$ for $M=A,B$, with $E_i/F$ of degree $d_i$, using the same explicit field model on both sides. Write $m_i$ for its multiplicity and
$$
P_M=c_M\prod_i N_{E_i/F}(\ell_{M,i})^{m_i},
\qquad c_M\in F^\times.
$$
Norms here are polynomial norms. The constants can be computed by evaluating along a full-degree restriction used by factor recovery, on a direction where no factor vanishes. Even if the direction is over an extension field $J/F$, compute the norm via the determinant of multiplication in the finite free $J$-algebra $E_i\otimes_F J$.

An actual transporter with the prescribed orbit matching satisfies
$$
\ell_{B,i}(f x)=\lambda_i\sigma_i(\ell_{A,i}(x)),
\qquad
\mu=\frac{c_B}{c_A}\prod_i N_{E_i/F}(\lambda_i)^{m_i},
$$
where $\lambda_i\in E_i^\times$ and $\sigma_i\in\operatorname{Gal}(E_i/F)$. The first equation follows from unique factorization and Frobenius compatibility. The second follows by applying norms to the first and using $P_B(fx)=\mu P_A(x)$. The orbit pairing is fixed by the theorem’s type assumption, or supplied by a complete branch in Theorem 2. Retain the first equations and the original pencil equation in the output system. If the unpromised target fails recovery, its image cannot be a genuine transporter of a promised source.

The first equations are tensor data. Use two copies of the $F$-space of $E_i$, one with field multiplication and one with its regular module action. Mark $\ell_{M,i}$ as a map into the module copy. The field copy may move by any field automorphism fixing $F$. The module map is precisely multiplication by $\lambda_i$ after applying this field automorphism. Attach a binary powering chain of one-dimensional $E_i$-modules to read $N_{E_i/F}(\lambda_i)$ via exponent $(q^{d_i}-1)/(q-1)$. On each multiplication link a semilinear input pair with common $\sigma_i$ forces the semilinear output with the product of their multiplier scalars. Coordinate generators fix the multiplication tables only. The final module’s $F$-line through its coordinate generator is carried into itself because its multiplier lies in $F^\times$. This gives a line of multiplier $N_{E_i/F}(\lambda_i)$.

## 2. Filter the label space by factor orbits

Order the matched orbits by their pairings and define
$$
V_{M,i}=\bigcap_{j\le i}\ker\ell_{M,j},
\qquad W_{M,i}=\ell_{M,i}(V_{M,i-1})\subseteq E_i
$$
with $V_{M,0}=V_M$. A genuine $f$ preserves the flags in its prescribed correspondence. On the grade $V_{M,i-1}/V_{M,i}$ its action is identified with $\lambda_i\sigma_i:W_{A,i}\to W_{B,i}$ under the linear maps induced by $\ell_{M,i}$. Compute these spaces and give the levels compatible recorded coordinate bases. Exact sequences express $\det f$ as the product of these grade determinants and the determinant on the last common kernel, multiplied by the known input-to-flag basis ratio. Attach the last kernel and its exterior algebra, of dimension $2^w$, if it is nonzero.

The remaining issue is to read the determinant on each $W_{M,i}$ when $\lambda_i,\sigma_i$ remain coupled to the original $f$. Each grade has the same shape, so omit $i$ in the next section.

## 3. Read the determinant of a partly defined semilinear map

Let $E/F$ be a finite field of degree $d$ and let $0\ne W_A,W_B\le E$ be $F$-subspaces of the same dimension. Define
$$
D_M=\{b\in E:bW_M\subseteq W_M\}.
$$
This is a subfield, because it is a finite unital subring of a field. Compute it by linear equations. A semilinear map $u=\lambda\sigma$ from $W_A$ onto $W_B$, with $\lambda\in E^\times$ and $\sigma\in\operatorname{Gal}(E/F)$, necessarily sends $D_A$ to $D_B$ by $\sigma$. Both are then the same unique subfield of $E$ of their degree, denoted $D$. Find one such reference $u_0$ by trying the $d$ Frobenius powers individually. For each power $\sigma$, solve $\lambda\sigma(W_A)\subseteq W_B$ as linear equations in $\lambda$. Any nonzero solution gives equality. Discard the whole instance if no reference exists, since that precludes a genuine transporter. A zero-dimensional grade contributes the identity multiplier.

Apply the same search with source and target both $W_A$. Under composition, the maps found in this form belong to the semilinear stabilizer
$$
H_A=\{(\lambda,\sigma):\lambda\sigma(W_A)=W_A\}.
$$
The projection to $\operatorname{Gal}(E/F)$ has kernel $D^\times$, so one reference per feasible Frobenius power represents all its cosets. This statement concerns pairs $(\lambda,\sigma)$ even in cases where two such pairs agree on $W_A$.

Choose an ordered $D$-basis of $W_A$ and use its ordered decomposition into $D$-lines. Apply the computed coset representatives to this frame. This gives an unordered set of at most $d$ distinct ordered frames, since each element of the kernel fixes every $D$-line. On $W_B$, use the image of the entire set under the single reference $u_0$. Every possible $u$ permutes these corresponding sets because $u_0^{-1}u\in H_A$. Consequently, marking the frame sets, with frame permutations allowed, places no new restriction on genuine transporters.

Choose a basis of $D/F$, and choose one generator of each line of each frame, on each side. The resulting ordered $F$-basis for a frame $\alpha$ on side $M$ has determinant $\omega_{M,\alpha}$ in the designated basis of $W_M$. Suppose the actual map carries a frame $\alpha$ to $\beta$. On its $j$-th line the map is $x\mapsto b_j\sigma(x)$ in the chosen $D$-coordinates. Its determinant over $F$ is
$$
N_{D/F}(b_j)\,\delta(\sigma),\qquad
\delta(\sigma)=\det_F(\sigma|_D).
$$
Read the norm via a $D$-module powering chain as in Section 1. If $s=[D:F]$ is odd, $\delta=1$ by the normal basis theorem. If $s$ is even, $\delta$ is the determinant of $\sigma$ on the unique quadratic subfield of $D$. In a normal basis Frobenius acts as an $s$-cycle, so its $k$-th power has sign $(-1)^k$ for even $s$. On the quadratic subfield it has exactly this sign. Attach that two-dimensional space and its exterior algebra to read $\delta$ from the actual $\sigma$. The automorphism on $D$ is linked to the same automorphism on $E$ by the inclusion of fields, with their $F$-algebra structures retained.

Multiply these signed norms in each frame’s slot order, attaching multiplication maps of $F$-lines. This gives a local frame volume line with multiplier
$$
\gamma_{\alpha,\beta}=\prod_j N_{D/F}(b_j)\delta(\sigma).
$$
On either side map every local frame volume line into one common grade line by multiplication by its known $\omega_{M,\alpha}$. Commutativity with these maps forces the common line multiplier to be
$$
\Delta=(\omega_{B,\beta}/\omega_{A,\alpha})\gamma_{\alpha,\beta}=\det_F u.
$$
The second equality is the determinant formula for a block-diagonal map in the two frame bases, followed by the two basis changes. It is independent of the frame. Thus every genuine $u$ extends simultaneously through every frame, including the ones it permutes. Conversely each isomorphism of the enlarged system reads the determinant of the same $u$ from the common line.

## 4. Assemble the one-instance test

Multiply the common grade lines and the last kernel’s exterior line from Section 2 to read $d_f$, including the input frame calibration. Multiply the lines from Section 1 with the stated multiplicities to read $\mu$, including the coefficient ratio. Use tensor products of lines and dual lines for powers and inverses. Pin the resulting coordinate to the requested character, or pin the two separate lines for a prescribed pair. Coordinate generators in all earlier lines are used for their multiplication tables. A prescribed value is imposed by a vector at the final line only.

All linear inclusions and projections, field actions, line multiplications and exterior multiplications participate in the same typed tensor system with the original tensor. Group the data by their fixed roles. A coordinate algebra $F^I$ encodes a finite set of indices by its primitive idempotents. Within an orbit, leave the frame-idempotent set unpinned but tag the slot positions in their given order. Incidence maps between index algebras are pullbacks along the projections from a frame slot or diagram edge to its parent indices. These maps enforce that a frame permutation simultaneously permutes its inclusions, field actions, line multiplications and volume calibration. Spaces of each role are direct sums with the indicated coordinate-algebra actions. The components of each family of maps combine into one block map on these sums. Padding chains of the same role, or tagging their lengths with the incidence indices, keeps the number of roles fixed. Thus the total system consists of fixed-arity linear and bilinear maps, together with the original tensor. The standard typed tensor-system compiler gives one ordinary TI instance over $F$. The only exponential-space term is the last kernel’s exterior algebra. Each other grade uses at most $d_i$ frames with at most $d_i$ slots of field degree at most $d_i$, plus polynomial-size norm and exterior-square data. [Tensor-system compiler](https://arxiv.org/html/2306.03135v2#S4).

The original pencil and its actual maps remain in the system. Therefore every output isomorphism proves the requested character equation for a genuine original transporter. Every original transporter with the character value has all the induced maps above. This proves Theorem 1 and proves the same one-instance result when an orbit correspondence is supplied.

## 5. Lift the factor permutation group without searching for tensor witnesses

The set $\Lambda_M$ of all geometric factor lines has size at most $n$. Each label is a specified Frobenius conjugate in one orbit’s own field model. A partial correspondence of labels can be marked in one ordinary TI query. A pin forces the specified pair of factor orbits to match by the first equation of Section 1 with the specified Frobenius power. Fix that power by linking the matching of two field bases according to it. Multipliers on the module copy stay free. Multiple pins in one orbit must prescribe the same field matching rule, a check performed before issuing a query. Each query retains the original tensor. Polynomially many labels and markers fit in the same fixed-type encoding as in Section 4.

For the automorphisms of $A$, let $H$ be the image of its automorphism group in $\operatorname{Sym}(\Lambda_A)$ and $K$ the kernel. Fix an ordering of the labels. For each pointwise-stabilizer level in its permutation chain, find the orbit of the next label by asking extension queries for every possible image. For each yes answer, greedily extend the prefix to one complete factor permutation feasible for $A$ against itself. These chosen permutations form transversals for the successive point stabilizers, so together they generate $H$. With a full permutation in hand, use Section 4 and the full pins to test the constantly many possible pairs $(d_f,\mu)$. This yields the character pair of some lift realizing that permutation. Apply the same pair enumeration to the identity permutation to read the full image of $K$. This works with no construction of matrix witnesses: every feasible character pair is certified by an isomorphism of the marked pencils. The selected lift images and the image of $K$ generate the full character image of the automorphism group. In fact the selected lifts generate modulo $K$, and the character map is a homomorphism.

For $A$ against $B$ find a feasible complete label permutation by the same prefix queries, starting with an ordinary TI test. On that permutation find one feasible character pair by Section 4. All transporter pairs constitute its coset of the automorphism character image just computed. This proves Theorem 2 using a polynomial number of ordinary TI queries on polynomial-size inputs. The order of the character codomain is constant at fixed $F$.

## 6. An unbounded family

Let $E_i=\mathbb F_{q^i}$ for $i=3,\ldots,r+2$ and set $W_i=\ker\operatorname{Tr}_{E_i/F}$. Take label space $\bigoplus_i W_i$ and matrix spaces $\bigoplus_i E_i$. The diagonal blocks of the pencil are regular multiplications $L_{x_i}$ on $E_i$ for $x_i\in W_i$. One may add arbitrary strictly upper triangular blocks linear in the labels. The determinant stays $\prod_i N_{E_i/F}(x_i)$.

Each factor orbit has length $i$. If the normalized coefficient ratios of its representative lay in a proper subfield of $E_i$, then the range $W_i$ would lie in a scalar multiple of that subfield and have dimension at most $i/2$, contrary to $\dim_F W_i=i-1$. The common kernel is zero and the orbit lengths are distinct. The scalar field preserving $W_i$ is exactly $F$, since its extension degree would divide both $i$ and $i-1$. Frame sizes on these grades grow. The product of possible independent Frobenius shifts $\prod_i i$ grows faster than any polynomial in the input length. In the block diagonal subfamily all those shifts are realized by applying the same Frobenius power on the label and two matrix spaces of each block. The construction handles them without enumerating their Cartesian product. The upper triangular off-diagonal blocks do not enter the proof of the determinant or the factor conditions and remain fully present in the output instance.

## 7. Relation to the published questions

Open Question 1.9 asks both containment and equality. The reverse inclusion has an elementary worst-case reduction over every field, by padding each mode with one zero direction and extending each ordinary transporter by the inverse determinant on that direction. For the converse, a padded transporter takes each intrinsic support to the corresponding support, and its restrictions extend to an ordinary transporter on the original spaces. This also answers the worst-case formulation of Joux and Narayanan’s Question 9. Their hyperdeterminant application involves a distributional issue: the padded tensor is singular because one can take a nonzero null covector in each mode, so the padding does not yield their proposed distinguisher. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2), [Joux–Narayanan, §5, Question 9](https://doi.org/10.4230/LIPIcs.ITCS.2025.62).

These determinant tests cover the stated split classes. General pencils can have identically zero determinants, nonlinear geometric factors or large common kernels. In particular the determinant of the regular multiplication pencil may depend only on semisimple quotient coordinates, leaving the whole radical in the common kernel. The tests neither supply a universal reduction for Open Question 1.9 nor establish publication priority for the restricted result.
