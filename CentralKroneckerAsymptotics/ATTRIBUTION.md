# Attribution and reproducibility

The rectangular two-row Kronecker identity is classical Pak-Panova work.
The precise target is Open Problem 6.13 in Greta Panova's *Complexity and
asymptotics of structure constants*, arXiv:2305.02553. Related off-center
asymptotics are due to Stephen Melczer, Greta Panova and Robin Pemantle,
*Counting partitions inside a rectangle*, SIAM Journal on Discrete Mathematics
34 (2020), 2388-2410, arXiv:1805.08375. These ingredients are credited,
not claimed as new results. Full links are in PROOF.md.

The present MathProofs argument takes the adjacent difference before applying
Fourier asymptotics, retaining its exact parity-dependent quadratic weight.
It is an AI-assisted informal proof candidate with separate internal reviews;
human validation, publication priority and Lean formalization remain pending.

Run `python checks.py` with Python 3.10 or newer from this directory. It needs
only the standard library and rewrites CHECKS.json. Finite computations do
not establish the universal asymptotic or publication priority. No external
paper code or Lean library is bundled.
