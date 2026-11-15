# Published inputs for crossed-flattening tensor isomorphism

This note describes two source collections and an independent exact coverage pass. Original-record counts refer to publisher records. Axis permutations, field reductions, and planted transporters are declared derivatives of those records. A crossed-flattening rejection concerns the method's scope and does not decide tensor nonisomorphism.

## MatTen crystal elasticity

Wen, Horton, Munro, Huck and Persson released full fourth-rank stiffness tensors for 10,276 crystals. These are published density functional theory calculations. Use the field named 'elastic_tensor' in 'crystal_elasticity_tensor.json', with its full four axes of size three. The data record declares CC BY 4.0. The source file's MD5 is '337c77550fbdb2b6c6d07b6f4e769920' and its SHA-256 is 'a954825ad3f38dc795a39f5958cc91eac64e9cfe83d2a4528a883e053ca2302a'. [Data release](https://doi.org/10.5281/zenodo.8190849) · [Introducing paper](https://doi.org/10.1039/D3DD00233K)

We run each of two specified axis orders on all records. The native order is $C_{ijkl}$. The regrouped order uses $T_{ijkl}=C_{ikjl}$ for every record. This exchanges the middle two axes before the same pair of cuts. The original flattening is singular because of exact minor symmetry in the files. Regrouping uses the other two balanced cuts and leaves the numerical entries intact. A change to the physical index order is disclosed for every regrouped result.

All decimal literals are exact rationals for the rational runs. Physical symmetries need not be exact in the stored decimals, particularly for rotations with irrational entries in the reported coordinates. The binary variants remove the least common decimal denominator, divide the resulting integer entries by their content, and reduce entrywise modulo two. These are binary instances derived from the data. They have no automatic claim to preserve the rational equivalence relation.

| Axis order and field | Original records tested | First cut singular | Second cut singular among the rest | Both invertible but non-scalar | Supported |
| --- | ---: | ---: | ---: | ---: | ---: |
| Native, rational literals | 10,276 | 10,276 | 0 | 0 | 0 |
| Regrouped, rational literals | 10,276 | 0 | 0 | 10,172 | 104 |
| Native, derived binary | 10,276 | 10,276 | 0 | 0 | 0 |
| Regrouped, derived binary | 10,276 | 9,361 | 0 | 912 | 3 |

The rational positives include 57 of 60 triclinic inputs and 47 of 756 trigonal inputs. All other crystal systems in this dataset had zero positives. The derived binary positives are publisher row numbers 7591 and 10198 (triclinic) and 7914 (trigonal). The material workflow here is a tensor-coordinate test on published numbers. Harness decisions do not certify physical equivalence under a common real rotation of all four modes.

Download the source file from the release page and run 'python data_elasticity.py crystal_elasticity_tensor.json output_directory'. This creates all four JSONL views and the companion coverage report. Use '--limit 100' for a prefix smoke test. The standard-library script verifies the publisher MD5 and checks each candidate by exact integer fraction-free elimination or bit-packed binary elimination. It keeps rational determinants and their adjugates integral by clearing denominators. [Normalization and exact coverage](data_elasticity.py) · [Coverage summary](data_elasticity_coverage.json)

## Sloane orthogonal-array catalogue

The source is N. J. A. Sloane's *A Library of Orthogonal Arrays*. The selection consists of all linked pure-level text entries with 3 to 9 levels, at least four columns, at most 256 runs and strength at least two. All 23 selected source files downloaded. The parser checked every pair marginal of their first four factors. Each normalized entry records the parity of the number of observations in a cell of that four-dimensional contingency table. One source, 'oa.9.4.3.2', is already four-way. The other 22 are first-four-factor projections. Source URLs and source-byte hashes are saved in the manifest. [Catalogue](https://neilsloane.com/oadir/index.html) · [Normalizer](data_sloane_oa.py) · [Source manifest](data_sloane_oa_manifest.json)

Sixteen normalized arrays had a singular first cut. The other seven had both cuts invertible and lacked scalar commutants, giving zero supported inputs among these 23. The latter are the index-one sources. Every two-column projection has each level pair once, so each balanced flattening is a permutation matrix. If $F$ and $\Gamma(F)$ are permutation matrices, $H=\Gamma(\Gamma(F)^{-1})=\Gamma(\Gamma(F)^{\mathsf T})=F^{\mathsf T}$, because transposition commutes with $\Gamma$. Hence $FH-I=0$ and all the power-trace covariants vanish. The same obstruction holds for exact complex multiunitary matrices with conjugate transposition. This is an intrinsic rejection under independent changes of the four mode bases.

The index-one subfamily includes canonical exact minimal-support four-party AME encodings. The nine rows of the published tetracode table are the unnormalized $\{0,1\}$ support coefficients of a four-qutrit AME state. The ordinary exact binary TI tests use those support entries. [Three- and higher-level orthogonal arrays](https://neilsloane.com/oadir/index.html) · [AME states and orthogonal arrays](https://arxiv.org/abs/1506.08857)

Run 'python data_sloane_oa.py output_directory' to download the selected sources and regenerate the normalized data. The normalized OA payload remains a local benchmark input. No explicit licence for redistribution was located.

## Native-format screen for FROSTT

All six entries explicitly listed at order four in the FROSTT catalogue have four distinct axis sizes. The dimensions are Chicago Crime $6186,24,77,32$, Delicious $532924,17262471,2480308,1443$, Enron $6066,5699,244268,1176$, Flickr $319686,28153045,1607191,731$, NIPS $2482,2862,14036,17$, and Uber Pickups $183,24,1140,1717$. Permuting their axes cannot make two matched pairs of dimensions. These are six format exclusions, separate from any rank or scalar-commutant rejection. [FROSTT catalogue](https://frostt.io/tensors/) · [FROSTT primary dimension metadata](https://github.com/frostt-tensor/frostt-tensor.github.io/tree/master/_tensors)

The small exact four-way classes catalogued in *Canonical Forms of Small Tensors over F2* have $2\times2\times2\times2$ and $3\times2\times2\times2$ formats. The first is outside the dimensions at least three contract and the second also lacks matched axes. The later fully symmetric $3\times3\times3\times3$ class has eligible shape but every balanced cut has duplicate rows and rank at most six, so the required cuts are singular. [Small tensor classifications](https://arxiv.org/abs/1206.5179) · [Symmetric tensor classification](https://arxiv.org/abs/1302.5005)
