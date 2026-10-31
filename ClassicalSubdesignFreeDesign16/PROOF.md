# A classical 16-point design without a Steiner subdesign

**Credit and status:** this is a resolution via prior work, **not a claim of a new MathProof discovery**. The construction family belongs to Martin Glen Oxenham's 1991 work on finite-geometric covers. MathProof, recorded by [Dugongue](https://github.com/Dugongue) with AI assistance, supplies the explicit witness, short explanatory proof, portable verification and connection to the later question. No first-recognition priority is claimed. This is an informal explanatory proof, not a Lean certificate.

## Statement

There is a simple 2-(16,4,3) design with no 2-(16,4,1) subdesign. The obstruction already occurs in the blocks through a single point and has a three-case hand proof. Thus no solver infeasibility claim is needed as a premise.

## Relation to the stated question
This supplies n=4,s=1,r=1 in the general-design existence clause of Meidl, Polujan and Pott, Linear codes and incidence structures of bent functions and their generalizations, concluding problem 4 (also Polujan thesis Open Problem 3.69, first part):
https://arxiv.org/html/2012.06866v2#S6
The existence clause asks for designs with these parameters without a smaller-index subdesign. The following realization clause separately concerns D contained in VF(F). We do NOT claim our design is VF(F), or that this solves any version imposing that additional restriction.

## Prior-art correction
A focused novelty search after finding the witness located Martin Glen Oxenham's November 1991 PhD thesis, On n-covers of PG(3,q) and related structures. Chapter III constructs proper 3-covers of PG(3,2); Chapter IV Construction 4.1.1 and Theorem 4.1.2 turn such covers into BIBDs with v=q^(4t),k=q^2,lambda equal to the cover multiplicity. For q=2,t=1 and multiplicity 3, these are the same 2-(16,4,3) parameters and construction framework. The following independently found witness is therefore not claimed as a new design-existence discovery. It is an explicit self-contained answer to the later general-design question and a connection to older finite geometry. The independent audit also identified this particular direction set as a classical long Singer orbit, with stabilizer order 30, matching the thesis construction family; its novelty is therefore not merely unconfirmed, but contradicted by that construction history.
Primary thesis:
https://digital.library.adelaide.edu.au/server/api/core/bitstreams/596d0da1-c3f5-4e73-bf69-73186a5c2fa9/content
The classical source is credited explicitly below; no thesis scan is redistributed.

## Construction
Identify the points with integers 0,...,15 under bitwise XOR, that is F2^4. Take the following 15 triples of nonzero points:

    L0={1,6,7}     L1={1,8,9}      L2={1,10,11}
    L3={2,4,6}     L4={2,12,14}    L5={2,13,15}
    L6={3,4,7}     L7={3,9,10}     L8={3,12,15}
    L9={4,10,14}   L10={5,8,13}    L11={5,9,12}
    L12={5,11,14}  L13={6,11,13}   L14={7,8,15}.

Each triple has XOR sum zero. Therefore Ui={0} union Li is a two-dimensional binary subspace. Include all affine cosets of each Ui as blocks, without duplication.

## Proof of the design parameters
Each nonzero point occurs in exactly three displayed triples, as direct inspection verifies. For any distinct x,y, put a=x XOR y. For each Ui containing a there is exactly one Ui-coset containing x,y, namely x+Ui. Distinct Ui give distinct cosets as their direction spaces differ. Thus each pair lies in exactly three blocks. There are 15 subspaces and four cosets of each, giving 60 distinct four-point blocks, as also required by b=3*16*15/(4*3)=60.

## Proof that no Steiner subdesign exists
A 2-(16,4,1) subdesign would have exactly five blocks through 0: every such block covers three of the 15 pairs {0,a}, and those pairs must each occur once. Its five direction triples would therefore partition {1,...,15}.

Point 1 belongs only to L0,L1,L2, so consider these three possible choices.

- If L0 is chosen, point 4 can only be covered by L9. Its alternatives L3 and L6 meet L0. But after choosing L0,L9, point 11 cannot be covered: its three triples L2,L12,L13 meet the chosen union at 1, 14, 6 respectively.
- If L1 is chosen, point 5 can only be covered by L12: L10,L11 meet L1. Then point 10 cannot be covered, because L2,L7,L9 meet the chosen union at 1, 9, 14 respectively.
- If L2 is chosen, point 6 can only be covered by L3: L0,L13 meet L2. Then point 14 cannot be covered, because L4,L9,L12 meet the chosen union at 2, 4, 11 respectively.

Every case is impossible. No five disjoint direction triples exist, so no Steiner subdesign exists. This completes the mathematical proof.

## Verification
witness.json contains all 60 blocks. The parent checked all 120 unordered pairs and found multiplicity 3. A separate worker independently verified the block parameters using ordinary sets, and proved absence of a subdesign with a different exact-cover implementation. More strongly, the worker checked that every point's local pencil has no partition, not just0. local-refutation.json records the seven-node three-case proof above. The research archive also retains a full-block exact-cover refutation. Neither computational search is needed once the explicit three-case proof is read.

## Scope and result classification
The general-design existence statement has an affirmative explicit witness with an elementary proof. The construction framework predates this work, so this is not evidence that we have newly solved a genuinely previously unresolved existence problem. Its useful output is the exact witness, short obstruction, independent audit and corrected source connection. It gives no new claim about bent-function non-extendability, covering radius, or VF-realizability. No Lean verification is claimed.


## Reproduce

Run `python verify.py` from this directory. It checks every design pair, every local pencil, the complete local refutation and an explicit Singer cycle; it writes `CHECKS.json`. Only the Python standard library is required.
