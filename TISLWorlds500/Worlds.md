# Comparing conjecture worlds against strict ternary TI

Here \(H\) means deterministic polynomial-time many-one reducibility of signed ternary TI to ordinary ternary TI. The table conditions the encoded rule system on \(\neg H\). A zero count carries an implication chain ending in a contradiction. A positive count certifies truth assignments of the stated propositional system. It makes no claim that the corresponding mathematical hypotheses are jointly consistent or independent. “True” and “false” columns compare both branches of each premise while ranging over every other premise.

## Strongest intersections

- **Ordinary tractability does not erase orientation without another input.** Signed Cook access plus ordinary TI in P gives signed TI in P. A randomized one-output map plus ordinary TI in P needs P=BPP in the stated chain. Plain GI in P, even combined with ordinary TI reducing to GI, supplies ordinary tractability but does not supply signed Cook access.
- **Signed and ordinary completeness have different effects.** Ordinary TI NP-completeness forces \(H\). Signed TI NP-completeness forces a second-level PH collapse via the AM protocol for nonisomorphism. That latter implication alone has no edge to the ordinary target.
- **Algebraic circuit collapse hits the stronger strict branch.** Over \(\mathbb F_3\), formal VP=VNP implies NP in P/poly via Boolean witness counting plus isolation. It therefore rules out nonuniform strictness. With only deterministic strictness it forces the reduction to exist nonuniformly and puts PH at the second level.
- **Sparse oracle examples have a different quantifier.** A PSPACE join with a sparse oracle can have \(H\), P=BPP, no classical one-way functions, and a separation between P and UP∩coUP in the same oracle model. This is a construction about external access to fixed tensor languages. It supplies no consistency or independence proof for the unrelativized arithmetic axioms. [Proof and scope](Complexity.md)
- **Current fine-grained claims get an explicit branch.** The posted classical ETH refutation fixes the classical ETH axis to false in its scoped branch. Weak ETH excludes a different running-time regime. The table keeps the counterfactual classical true branch visible and records the additional pin separately. The posted finite-field and Cayley-table algorithms are used only with the theorem scopes and representation costs stated in the complexity chapter. [OpenAI ETH Lean scope](https://github.com/openai/math/blob/main/lean/docs/378.md) · [Weak ETH comparison](https://arxiv.org/abs/2611.02650) · [Qiao–Zhang working manuscript](https://group-iso.github.io/)
- **Arithmetic hypotheses can have sharp local consequences.** GRH has an explicit path to certain effective arithmetic and interactive algorithms. The rational Hasse statement for signed TI is false by a concrete tensor example. Other standard conjectures such as BSD, Hodge and abc do not acquire a TI implication merely because they appear as axes. [Arithmetic and geometry cases](Arithmetic.md)

## Both branches of every axis


| ID | Proposed premise | Strict and true | Strict and false | Equal and true | Equal and false |
| --- | --- | ---: | ---: | ---: | ---: |
| `HR` | Signed ternary TI has a one-output bounded-error randomized reduction to ordinary ternary TI | 10,796,544 | 15,489,792 | 1,182,154,752 | 0 |
| `HN` | Signed ternary TI has a polynomial-size circuit many-one reduction to ordinary ternary TI | 22,367,232 | 3,919,104 | 1,182,154,752 | 0 |
| `HC` | Signed ternary TI is decidable in deterministic polynomial time with an ordinary TI oracle | 9,300,096 | 16,986,240 | 1,182,154,752 | 0 |
| `AP` | Signed ternary TI is in P | 0 | 26,286,336 | 992,378,880 | 189,775,872 |
| `BP` | Ordinary ternary TI is in P | 7,686,144 | 18,600,192 | 559,841,280 | 622,313,472 |
| `AQP` | Signed ternary TI is in QP | 16,250,112 | 10,036,224 | 1,158,266,880 | 23,887,872 |
| `BQP_TIME` | Ordinary ternary TI is in QP | 18,641,664 | 7,644,672 | 917,962,752 | 264,192,000 |
| `AAP` | Signed ternary TI is in P/poly | 17,515,008 | 8,771,328 | 1,129,734,144 | 52,420,608 |
| `PNP` | P = NP | 0 | 26,286,336 | 1,474,560 | 1,180,680,192 |
| `PRP` | P = RP | 8,246,016 | 18,040,320 | 659,275,776 | 522,878,976 |
| `PBPP` | P = BPP | 5,239,296 | 21,047,040 | 440,008,704 | 742,146,048 |
| `PZPP` | P = ZPP | 14,259,456 | 12,026,880 | 899,629,056 | 282,525,696 |
| `PBQP` | P = BQP | 2,619,648 | 23,666,688 | 220,250,112 | 961,904,640 |
| `PPSPACE` | P = PSPACE | 0 | 26,286,336 | 491,520 | 1,181,663,232 |
| `PH2` | The polynomial hierarchy collapses to its second level | 20,860,416 | 5,425,920 | 1,091,469,312 | 90,685,440 |
| `AMNP` | AM = NP | 8,762,112 | 17,524,224 | 560,185,344 | 621,969,408 |
| `NPCONP` | P = NP ∩ coNP | 8,762,112 | 17,524,224 | 560,185,344 | 621,969,408 |
| `NPADVICE` | NP ⊆ P/poly | 10,008,576 | 16,277,760 | 699,826,176 | 482,328,576 |
| `NPQP` | NP ⊆ QP | 6,213,888 | 20,072,448 | 500,416,512 | 681,738,240 |
| `GIP` | Graph isomorphism is in P | 10,996,992 | 15,289,344 | 481,787,904 | 700,366,848 |
| `GINPC` | Graph isomorphism is NP-complete under deterministic Karp reductions | 0 | 26,286,336 | 81,690,624 | 1,100,464,128 |
| `AGI` | Signed ternary TI reduces to graph isomorphism under deterministic Karp reductions | 0 | 26,286,336 | 602,062,848 | 580,091,904 |
| `BGI` | Ordinary ternary TI reduces to graph isomorphism under deterministic Karp reductions | 7,174,656 | 19,111,680 | 436,764,672 | 745,390,080 |
| `ANPC` | Signed ternary TI is NP-complete under deterministic Karp reductions | 10,430,208 | 15,856,128 | 545,734,656 | 636,420,096 |
| `BNPC` | Ordinary ternary TI is NP-complete under deterministic Karp reductions | 0 | 26,286,336 | 545,734,656 | 636,420,096 |
| `ETH` | The Exponential Time Hypothesis for 3-SAT | 13,143,168 | 13,143,168 | 590,340,096 | 591,814,656 |
| `SETH` | The Strong Exponential Time Hypothesis | 6,571,584 | 19,714,752 | 295,170,048 | 886,984,704 |
| `OWF` | Classical uniform one-way functions exist | 13,143,168 | 13,143,168 | 590,340,096 | 591,814,656 |
| `VPVNP3` | Formal arithmetic VP = VNP over the fixed field F3 | 5,004,288 | 21,282,048 | 349,913,088 | 832,241,664 |
| `MCSPP` | The minimum circuit size problem is in P | 9,020,160 | 17,266,176 | 559,448,064 | 622,706,688 |
| `MKTPP` | The minimum KT problem is in P | 6,013,440 | 20,272,896 | 538,361,856 | 643,792,896 |
| `COB` | Complement ordinary ternary TI many-one reduces to ordinary ternary TI in P | 8,762,112 | 17,524,224 | 591,077,376 | 591,077,376 |
| `PLDEC` | Signed TI has a PL decoder on a polynomial, deterministically generated list of ordinary TI queries | 8,762,112 | 17,524,224 | 591,077,376 | 591,077,376 |
| `AXIS` | The oriented single-mode boundary test is in PromiseP on ordinary-positive inputs | 0 | 26,286,336 | 591,077,376 | 591,077,376 |
| `PROBES` | The quotient-volume marks cover an H-hard carrier, with an explicit polynomial equivariant extraction and complete sign repair | 0 | 26,286,336 | 591,077,376 | 591,077,376 |
| `POLYBACK` | The explicit ordinary free F3[t] tensor image of signed ternary TI reduces to ordinary ternary TI in P | 0 | 26,286,336 | 591,077,376 | 591,077,376 |
| `INTBACK` | The explicit ordinary free integral tensor image of signed ternary TI reduces to ordinary ternary TI in P | 0 | 26,286,336 | 591,077,376 | 591,077,376 |
| `DUAL` | Full signed-to-ordinary collapse over the ternary dual numbers | 0 | 26,286,336 | 1,182,154,752 | 0 |
| `SOCLE9` | Full signed-to-ordinary collapse on the socle-supported Z/9 carrier | 0 | 26,286,336 | 1,182,154,752 | 0 |
| `RH` | The Riemann hypothesis for the Riemann zeta function | 17,524,224 | 8,762,112 | 788,103,168 | 394,051,584 |
| `GRH` | The generalized Riemann hypothesis for all Dirichlet L-functions, including zeta | 8,762,112 | 17,524,224 | 394,051,584 | 788,103,168 |
| `BSD` | The Birch and Swinnerton-Dyer conjecture for all elliptic curves over Q | 13,143,168 | 13,143,168 | 591,077,376 | 591,077,376 |
| `HODGE` | The rational Hodge conjecture | 13,143,168 | 13,143,168 | 591,077,376 | 591,077,376 |
| `ABC` | The abc conjecture over Q | 13,143,168 | 13,143,168 | 591,077,376 | 591,077,376 |
| `H10Q` | Solvability of rational Diophantine equations is decidable | 13,143,168 | 13,143,168 | 591,077,376 | 591,077,376 |
| `HASSEQ` | Rational signed TI has a local-to-global principle at all places of Q | 0 | 26,286,336 | 0 | 1,182,154,752 |
| `WEAKETH` | No 3-SAT algorithm runs in 2^(O(n^(1−ε))) poly(input length) for any fixed ε>0 | 19,714,752 | 6,571,584 | 885,510,144 | 296,644,608 |

The strict branch has 26,286,336 assignments under the encoded rules. The equality branch has 1,182,154,752. Pinning classical ETH false leaves 13,143,168 in the strict branch. Pinning Weak ETH true instead leaves 19,714,752.

## All minimal positive incompatibilities of size at most three

| Assumed true together with strictness | Rule certificate |
| --- | --- |
| `AP` | [U03](#rule-u03) |
| `PNP` | [U03](#rule-u03), [C05](#rule-c05) |
| `PPSPACE` | [U03](#rule-u03), [C01](#rule-c01), [C05](#rule-c05) |
| `GINPC` | [G01](#rule-g01), [G05](#rule-g05) |
| `AGI` | [G01](#rule-g01) |
| `BNPC` | [G07](#rule-g07) |
| `AXIS` | [T02](#rule-t02) |
| `PROBES` | [T03](#rule-t03) |
| `POLYBACK` | [T04](#rule-t04) |
| `INTBACK` | [T05](#rule-t05) |
| `DUAL` | [T06](#rule-t06) |
| `SOCLE9` | [T08](#rule-t08) |
| `HASSEQ` | [M02](#rule-m02) |
| `HC` + `BP` | [U03](#rule-u03), [U05](#rule-u05) |
| `PRP` + `MCSPP` | [U03](#rule-u03), [C09](#rule-c09) |
| `PRP` + `MKTPP` | [U03](#rule-u03), [C04](#rule-c04), [C10](#rule-c10) |
| `PBPP` + `MCSPP` | [U03](#rule-u03), [C03](#rule-c03), [C09](#rule-c09) |
| `PBPP` + `MKTPP` | [U03](#rule-u03), [C03](#rule-c03), [C04](#rule-c04), [C10](#rule-c10) |
| `PZPP` + `MKTPP` | [U03](#rule-u03), [C10](#rule-c10) |
| `PBQP` + `MCSPP` | [U03](#rule-u03), [C02](#rule-c02), [C03](#rule-c03), [C09](#rule-c09) |
| `PBQP` + `MKTPP` | [U03](#rule-u03), [C02](#rule-c02), [C03](#rule-c03), [C04](#rule-c04), [C10](#rule-c10) |
| `AMNP` + `NPCONP` | [U03](#rule-u03), [C08](#rule-c08) |
| `COB` + `PLDEC` | [T01](#rule-t01) |
| `HR` + `BP` + `PBPP` | [U03](#rule-u03), [U06](#rule-u06) |
| `HR` + `BP` + `PBQP` | [U03](#rule-u03), [U06](#rule-u06), [C02](#rule-c02) |
| `HC` + `GIP` + `BGI` | [U03](#rule-u03), [U05](#rule-u05), [G04](#rule-g04) |

The local Hasse rule is the one unconditional positive conflict in this table. It holds on the equality side as well, because the explicit rational counterexample is independent of the ternary hypothesis.

## Cited implication rules

### Rule U01

**H ⇒ HR, HN, HC.** Simulate deterministically, compile into circuits, or make one oracle call. [Definitions and ordinary/signed transfers](prior/RESULTS.md)

### Rule U02

**HR ⇒ HN.** Amplify each length by independent repeated reductions and combine output instances via the ordinary majority compiler. Fix all repetitions for that length by the union bound over inputs. [Definitions and ordinary/signed transfers](prior/RESULTS.md) · [Complexity chapter](Complexity.md)

### Rule U03

**AP ⇒ H, AQP, AAP.** A decision bit selects fixed YES or NO output. Polynomial time gives both listed bounds. [Definitions and ordinary/signed transfers](prior/RESULTS.md)

### Rule U04

**AAP ⇒ HN.** A decision circuit chooses the fixed YES or NO output. [Definitions and ordinary/signed transfers](prior/RESULTS.md)

### Rule U05

**HC, BP ⇒ AP.** Answer all ordinary oracle calls deterministically. [Definitions and ordinary/signed transfers](prior/RESULTS.md)

### Rule U06

**HR, BP, PBPP ⇒ AP.** Simulate the one-output randomized reduction followed by ordinary decision, then derandomize BPP. [Definitions and ordinary/signed transfers](prior/RESULTS.md)

### Rule U07

**HN, BP ⇒ AAP.** Compose the advice reduction circuit with a circuit for ordinary polynomial-time decision. [Definitions and ordinary/signed transfers](prior/RESULTS.md)

### Rule U08

**H, BQP_TIME ⇒ AQP.** Compose a polynomial-size output map with quasipolynomial ordinary decision. [Definitions and ordinary/signed transfers](prior/RESULTS.md)

### Rule C01

**PPSPACE ⇒ PNP, PBQP.** Both NP and BQP are contained in PSPACE.

### Rule C02

**PBQP ⇒ PBPP.** BPP is contained in BQP.

### Rule C03

**PBPP ⇒ PRP.** RP is contained in BPP.

### Rule C04

**PRP ⇒ PZPP.** ZPP is contained in RP.

### Rule C05

**PNP ⇒ AP, BP, NPADVICE, NPQP, GIP, NPCONP, PH2, AMNP, PBPP.** The transporter relations are in NP. PH collapses to P and contains AM and BPP. [Earlier complexity atlas](prior/prior/earlier/baseline/expansion/Complexity.md)

### Rule C06

**NPADVICE ⇒ AAP, PH2.** Signed TI lies in NP and Karp–Lipton gives collapse to the second level. [Earlier complexity atlas](prior/prior/earlier/baseline/expansion/Complexity.md) · [Karp and Lipton](https://doi.org/10.5169/seals-52237)

### Rule C07

**NPQP ⇒ AQP, BQP_TIME.** Both transporter problems lie in NP. [Earlier complexity atlas](prior/prior/earlier/baseline/expansion/Complexity.md)

### Rule C08

**AMNP, NPCONP ⇒ AP.** Signed nonisomorphism lies in AM, so the two assumptions put signed decision in P. [Earlier complexity atlas](prior/prior/earlier/baseline/expansion/Complexity.md)

### Rule C09

**MCSPP, PRP ⇒ AP.** The MCSP-assisted witness inverter gives signed decision in RP with the MCSP oracle. [Allender and Das](https://www.cs.rutgers.edu/~allender/papers/szk.mcsp.pdf) · [Allender et al., Theorem 5.7](https://pages.cs.wisc.edu/~dieter/Papers/gi-mktp-sicomp.pdf) · [Earlier complexity atlas](prior/prior/earlier/baseline/expansion/Complexity.md)

### Rule C10

**MKTPP, PZPP ⇒ AP.** The group-orbit MKTP algorithm gives signed decision in ZPP with the MKTP oracle. [Allender and Das](https://www.cs.rutgers.edu/~allender/papers/szk.mcsp.pdf) · [Allender et al., Theorem 5.7](https://pages.cs.wisc.edu/~dieter/Papers/gi-mktp-sicomp.pdf) · [Earlier complexity atlas](prior/prior/earlier/baseline/expansion/Complexity.md)

### Rule C11

**VPVNP3 ⇒ NPADVICE.** Isolate Boolean witnesses, compute the formal VNP count modulo three, amplify and fix good randomness nonuniformly. [Valiant and Vazirani](https://ics.uci.edu/~vazirani/ValVaz.pdf) · [Earlier VP/VNP comparison](prior/RESULTS.md)

### Rule C12

**PNP ⇒ !ETH, !SETH, !OWF, !WEAKETH.** Polynomial SAT violates both exponential hypotheses, and NP search in P inverts every polynomial-time function on its range. [Impagliazzo and Paturi](https://doi.org/10.1006/jcss.2000.1727)

### Rule C13

**SETH ⇒ ETH.** Sparsification and linear-size reduction of each fixed-width sparse SAT to 3-SAT transfer arbitrarily small exponents. [Impagliazzo and Paturi](https://doi.org/10.1006/jcss.2000.1727)

### Rule C14

**ETH ⇒ WEAKETH.** A stretched-exponential 3-SAT running time has asymptotic exponential rate zero. [Comparison of classical and Weak ETH](https://arxiv.org/abs/2611.02650)

### Rule G01

**AGI ⇒ H, AQP.** Compose with graph-to-tensor or with Babai's graph algorithm. [Definitions and ordinary/signed transfers](prior/RESULTS.md) · [Babai, Graph Isomorphism in Quasipolynomial Time](https://arxiv.org/abs/1512.03547)

### Rule G02

**AGI, GIP ⇒ AP.** Compose signed-to-graph with graph decision. [Babai, Graph Isomorphism in Quasipolynomial Time](https://arxiv.org/abs/1512.03547)

### Rule G03

**BGI ⇒ BQP_TIME.** Compose ordinary-to-graph with Babai's graph algorithm. [Babai, Graph Isomorphism in Quasipolynomial Time](https://arxiv.org/abs/1512.03547)

### Rule G04

**BGI, GIP ⇒ BP.** Compose ordinary-to-graph with graph decision. [Babai, Graph Isomorphism in Quasipolynomial Time](https://arxiv.org/abs/1512.03547)

### Rule G05

**GINPC ⇒ AGI, BGI, PH2, NPQP.** Both languages are in NP. Graph nonisomorphism is in AM, and Babai supplies the quasipolynomial upper bound. [Boppana, Håstad and Zachos](https://www.sciencedirect.com/science/article/pii/0020019087902328) · [Babai, Graph Isomorphism in Quasipolynomial Time](https://arxiv.org/abs/1512.03547) · [Earlier complexity atlas](prior/prior/earlier/baseline/expansion/Complexity.md)

### Rule G06

**ANPC ⇒ PH2.** Signed nonisomorphism lies in AM, so signed NP-completeness collapses PH to its second level. [Boppana, Håstad and Zachos](https://www.sciencedirect.com/science/article/pii/0020019087902328) · [Earlier complexity atlas](prior/prior/earlier/baseline/expansion/Complexity.md)

### Rule G07

**BNPC ⇒ H, PH2.** Completeness gives the reduction, and ordinary nonisomorphism lies in AM. [Boppana, Håstad and Zachos](https://www.sciencedirect.com/science/article/pii/0020019087902328) · [Earlier complexity atlas](prior/prior/earlier/baseline/expansion/Complexity.md)

### Rule T01

**COB, PLDEC ⇒ H.** Complement rails and the single-query weighted branching-program compiler implement the PL decoder. [Complexity chapter](Complexity.md)

### Rule T02

**AXIS ⇒ H.** Reflect the sign cube, recover edge boundaries, and gate through the single original ordinary input. [Complexity chapter](Complexity.md) · [Quotient-volume chapter](Volumes.md)

### Rule T03

**PROBES ⇒ H.** Compile the sufficient explicit family of character measurements and repair all signs. [Quotient-volume chapter](Volumes.md)

### Rule T04

**POLYBACK ⇒ H.** Compose the uniform ternary polynomial-ring bridge with the stipulated back-transfer. [Arithmetic chapter](Arithmetic.md)

### Rule T05

**INTBACK ⇒ H.** Compose the integral bridge with the stipulated back-transfer. [Definitions and ordinary/signed transfers](prior/RESULTS.md)

### Rule T06

**DUAL ⇒ H.** Use the fixed dual-number ring to residue-field equivalence. [Definitions and ordinary/signed transfers](prior/RESULTS.md)

### Rule T07

**H ⇒ DUAL.** Use the residue-field to fixed dual-number ring equivalence. [Definitions and ordinary/signed transfers](prior/RESULTS.md)

### Rule T08

**SOCLE9 ⇒ H.** The signed and ordinary comparisons on this carrier reflect their residue-field counterparts. [Mixed-characteristic chapter](Algebra.md)

### Rule T09

**H ⇒ SOCLE9.** Encode and reflect the residue instance using a fixed socle line over Z/9. [Mixed-characteristic chapter](Algebra.md)

### Rule M01

**GRH ⇒ RH.** The trivial character includes the Riemann zeta function. [Arithmetic chapter](Arithmetic.md)

### Rule M02

**unconditional ⇒ !HASSEQ.** Explicit rational tensor pairs have local signed transporters everywhere and no rational signed transporter. [Arithmetic chapter](Arithmetic.md)


## Exact checking

The verifier is standard-library Python. Run it from the directory containing this atlas to regenerate the counts, or pass named premises as shown. A leading exclamation mark fixes the negative branch. Add `--equality` to fix \(H\) instead of \(\neg H\).

~~~powershell
py -3 .\world_count.py --report
py -3 .\world_count.py +PRP +MCSPP
py -3 .\world_count.py +GRH '!ETH'
~~~

The inference procedure takes the closure of positive heads of the recorded Horn rules and checks any implied negative heads. This is complete for satisfiability of **these Horn rules** under pinned premises. The separate model counter splits on variables and counts disappearing free coordinates exactly. An independent exhaustive computation checks a 14-axis projection. The full report also checks each individual premise by both model counting and propagation.

[Rule data and cited proof paths](world_rules.json) · [Verifier](world_count.py) · [Exact report](WorldCounts.json)
