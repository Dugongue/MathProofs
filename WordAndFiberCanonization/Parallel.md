# Canonizing equal-length pairs captures group products and exact path counting

Two explicit equivalence relations below have classes of size exactly two. The first has an AC⁰ complete invariant and an NC¹ exact canonical form. Improving on one-half agreement with a canonical form on uniform inputs is already NC¹-hard under nonuniform constant-depth reductions. The second has a TC⁰ complete invariant and gives the corresponding equivalence for exact logspace path counting. Both results concern ordinary explicit binary strings. These proofs are informal.

## A counting observation

For a permutation D of a finite set X, label two sorts of records by

    F(0,u,v) = (D(u),v)
    F(1,u,v) = (u,D(v)).

Equality of labels defines the relation. Each label (a,b) has one preimage of each tag. A canonical form c selects one of those preimages and returns it for both. The identity function agrees with every c on exactly half the uniform records. For any circuit H, if its agreement with some c is at least 1/2 + ε, its probability of returning a **valid record of the opposite tag** is at least ε. Indeed, correctly returning a record of the same tag is possible at only one input per class. Every correctly returned opposite-tag record supplies the inverse of D on the challenge coordinate v of a tag-0 input or u of a tag-1 input. This reasoning imposes no computability assumption on the selector used to measure agreement.

When a randomized construction gives each fixed target an independently verifiable correct answer with probability δ, T independent parallel trials fail with probability at most exp(−δT). For a finite length with M possible targets, choose T larger than (log M + 1)/δ. Some fixed choice of all trial coins succeeds on every target. Validity checks followed by selection of the first valid answer add constant depth when the checks are in AC⁰, or constant threshold depth when they are in TC⁰. This step gives nonuniform circuits. A polynomial number of trials suffices when the advantage is inverse polynomial and log M is polynomial in the input length.

## Finite group words

Take the alternating group G on five letters. For a length-n vector u of group elements put u₀ = e, the identity, and define D(u) at i to be u at i−1 inverted, multiplied on the left of u at i. This is a bijection. Its inverse takes the ordered prefix products. Finite-group table lookups give a constant-locality invariant on the group alphabet. Computing all prefix products by balanced multiplication trees gives an NC¹ exact canonical form, by computing the label and returning its tag-0 preimage.

Given an arbitrary word b of n group elements, draw independent uniform r₁,…,rₙ in G, with r₀ = e. Form a masked challenge with entries

    b′ᵢ = rᵢ₋₁⁻¹ bᵢ rᵢ.

For fixed b the map r ↦ b′ is bijective, by solving for the rᵢ successively. Thus b′ is uniform on all group words. Its prefix through position i is the prefix of b through i multiplied on the right by rᵢ. Independently sample uniform s in Gⁿ and a fair tag. Supply (0,s,b′) or (1,b′,s) to H. In either case the input has exactly the uniform law. A valid tag switch gives D⁻¹(b′), and multiplication on the right by rᵢ⁻¹ recovers each prefix of b. Check the answer by taking consecutive differences and comparing with b. All operations surrounding H have constant depth. This masking is the standard random self-reduction for group products; the two-member selection argument transfers it to canonical forms. [Barrington's NC¹-completeness theorem](https://people.cs.umass.edu/~barring/publications/bwbp.pdf) · [Moitra, Mossel and Sandon, Proposition 18 and its random self-reduction](https://proceedings.mlr.press/v125/moitra20a/moitra20a.pdf)

### Uniform bits throughout

Here is an encoding that retains the claim for **uniform binary inputs** even though 60 does not divide a power of two. Use n positions with n six-bit slots per position. Each slot encodes an integer between 0 and 63. At a position, the first slot containing a value less than 60 holds its active group element. A binary vector is good if each position has an active slot. The chance that a uniform vector is bad is at most n·16^(−n). For good vectors the active elements are independent and uniform conditional on the locations of the active slots and on all inactive bits. Indeed, replacing any active group value by any of the other 59 possibilities preserves that auxiliary data.

On a good vector apply D to the active symbols and keep all auxiliary data. On a bad vector act identically. The resulting binary map is a permutation. Testing the first valid slot, selecting its bits, taking finite table lookups, and replacing the selected bits all have AC⁰ circuits of polynomial size. The full input length is 1 + 12n², including the tag. These are the formats on which average agreement is measured. At other lengths one may make strings singleton classes with separate labels. All pairs in the specified formats still consist of exactly two elements, including those containing bad vectors.

For the reduction, sample the challenge vector's auxiliary data according to the conditional law of a good vector, then fill its active slots with b′. Sample the second vector independently from uniform good vectors, and use the two possible input orders above. This produces exactly the uniform tagged law conditional on both vectors being good. Removing bad vectors from the original uniform law costs at most 2n·16^(−n) in event probability. Hence the success probability for a valid switch is at least ε − 2n·16^(−n). The random auxiliary data and masks can be fixed in the parallel circuit construction. Multiplying by a fixed mask at a position is a constant-size table lookup on the active symbol. Input verification remains in AC⁰. Padding input bits and hardwiring the symbol encoding increase sizes only polynomially.

**Conclusion.** For nonuniform ACC⁰, each of the following conditions is equivalent to the other two.

1. At every sufficiently large supported length, ACC⁰ circuits agree with some canonical selector on at least 1/2 plus an inverse polynomial fraction of uniform binary inputs, with a fixed advantage exponent and fixed circuit depth and modulus.
2. The matching has an exact ACC⁰ canonical form.
3. ACC⁰ = NC¹.

The random reduction followed by fixing coins gives the worst-case group product from the first condition. Barrington reduces every NC¹ language to that product. Conversely the group-prefix algorithm gives an exact form in NC¹. ACC⁰ is contained in NC¹. The same proof works for any nonuniform polynomial-size circuit class containing AC⁰ that is closed under these constant compositions and parallel repetitions, yielding NC¹ containment in that class as the criterion.

**Unconditional application.** For each fixed prime p, even quasipolynomial-size fixed-depth AC⁰[p] circuits have advantage at most negligible over one half. An inverse-polynomial advantage at infinitely many n would, at these lengths, give exact circuits for the G-word problem with only polynomially many parallel repetitions and a constant increase in depth. Choose a prime r among 2, 3 and 5 different from p and take an element h of G of order r. Substituting h or e at each position according to a bit gives an exact MOD-r circuit at those same lengths, contradicting Smolensky's exponential lower bound. This proves an average-case lower bound for one matching simultaneously for each fixed prime. Whether unrestricted ACC⁰ equals NC¹ remains open. [Smolensky's lower bound](https://people.cs.umass.edu/~immerman/cs601/Smolensky.pdf)

## Integer matrices and exact path counts

For m at least 2, let G be the group of upper unitriangular m-by-m matrices over the residues modulo 2^m. Record the m bits of each entry strictly above the diagonal in row-major order. Every string of the required length encodes one group element, and uniform bits give the uniform group measure exactly. Matrix multiplication lies in uniform TC⁰ by binary multiplication and iterated addition. It is also a deterministic logspace string function. [Hesse, Allender and Barrington](https://people.cs.rutgers.edu/~allender/papers/division.pdf)

On X = G² use the permutation D(a,b) = (a,ab). Its inverse sends (u,v) to (u,u⁻¹v). Form the tagged two-member relation above. Its invariant requires just one matrix multiplication. At each m, all records consist of a tag and four group elements of that fixed size. Measures and agreement statements concern exactly these supported lengths.

Given an arbitrary g in G, take independent uniform q and a in G. The pair B = (gq,a) is a uniform challenge in X, for every fixed g. With independent uniform S in X and a fair bit, feed (0,S,B) or (1,B,S) to H. A valid switch yields D⁻¹(B) and hence h = (gq)⁻¹a. Then g⁻¹ = q h a⁻¹. Test the answer by multiplying it by g. The factor a⁻¹ depends only on the trial coins and is supplied as a hardwired constant along with a. No algorithm for computing a random matrix inverse in low depth is assumed. Parallel repetition and fixed coins give worst-case nonuniform inversion from any inverse-polynomial advantage on uniform raw binary records. In the other direction, worst-case inversion gives an exact canonical form by decoding the tag-0 preimage of the label.

### Equivalence with counting paths

For a simple directed acyclic graph with m vertices in topological order, let A be its strictly upper triangular adjacency matrix. The entry (s,t) of

    (I − A)⁻¹ = I + A + ⋯ + A^(m−1)

counts paths from s to t, including the empty path when s = t. The number is less than 2^m since a path with fixed endpoints is determined by its subset of interior vertices. Thus the residue modulo 2^m gives its exact binary value. Topologically ordered acyclic path counting is #L-complete. Explicitly, unfold a polynomial-time nondeterministic logspace machine into a time-layered configuration graph. If two choices can lead to the same next configuration, give each choice its own intermediate vertex. Route accepts to a common sink with unique continuations. For a fixed input length, each configuration-transition bit tests at most a fixed input symbol after the machine configurations and layer numbers have been hardwired. The graph has polynomially many vertices in a fixed topological order, and its designated path count equals the number of accepting computations. This construction also supplies deterministic logspace reductions. [Allender, Beals and Ogihara on matrix complexity and counting classes](https://www.cs.rutgers.edu/~allender/papers/rank.pdf)

For the reverse reduction, given g in G write H = I − g. This is strictly upper triangular, with residues represented between 0 and 2^m−1. Each entry of g⁻¹ modulo 2^m is a sum of products of edge weights over increasing paths, including the empty path on the diagonal. The integer weighted count before reduction is a #L function. Choose each successive vertex in one fixed-length encoding and reject invalid or non-increasing choices. On traversing an edge of weight w, branch with precisely w accepting continuations by guessing m bits and continuing if the resulting word represents a number less than w. A streaming comparison uses one comparison flag and a logarithmic index. Stop exactly at the specified endpoint. Paths have at most m−1 edges, and this gives the product multiplicities with logarithmic work space. Taking the low m bits yields the required entry. Matrix-entry queries can be run for all output bits in parallel or replayed individually using logarithmic workspace.

Consequently, for each of the two models below all three capabilities are equivalent: weak canonization with inverse-polynomial advantage over one half on every sufficiently large supported length, exact canonization of this matching, and worst-case computation of every #L function in binary.

- Nonuniform polynomial-size TC⁰ circuits.
- Deterministic logspace transducers with polynomial advice depending only on the input length.

For the advice model the polynomial list of successful trials and their inverse constants are part of the advice. A logspace machine tries trial indices in sequence and replays intermediate output bits to check each candidate and emit the first verified answer. The number of nested logspace compositions is constant. The construction does not use a read-once random tape to simulate repeated accesses to a sampled matrix. The characterization gives no unconditional separation of #L from these models.

The source of the improvement across both constructions is the same: any advantage over one half requires producing a representative in the other encoding. Masking then makes the missing part of that representative useful on every worst-case input. The finite-group example transfers a known group-product theorem, and the matrix example transfers known counting properties of triangular inversion. Priority for their conclusions about average agreement with arbitrary canonical forms has not been established.
