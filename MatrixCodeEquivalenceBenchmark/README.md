# Matrix-code equivalence benchmark

This prototype decides left–right equivalence of matrix subspaces over prime fields when its exact search finishes. Given bases for two codes, it looks for invertible row and column operations that take one span to the other. A positive result includes those two operations and a change of code basis, verified on the original generators. A negative result follows from an exact invariant or a completed search. A search limit yields `unknown`.

The transfer from the balanced tensor solver uses contraction ranks to restrict the search for a coefficient map. Once that map is fixed, both matrix factors are recovered by linear algebra and a checked invertibility search. Projective incidence, two-dimensional coefficient planes in the binary backend, and trace duality improve coverage in different regimes. The mathematical argument was reviewed informally and the implementation was tested against exact controls. [Mathematical details](RankProfiles.md)

## Run

Install Python 3.11 or newer and NumPy. Compile the optional native kernel for the prime-field solver and the standalone binary backend from the same directory.

```powershell
python -m pip install numpy
g++ -std=c++20 -O3 -march=native -static -shared mce_kernels.cpp -o mce_kernels.dll
g++ -std=c++20 -O3 -march=native mce_backend.cpp -o mce_backend.exe
python mce.py dataset/oxford-meds-13-4-6-5.txt
python benchmark_mce.py --controls --repeats 7 --compare-python --out reproduced-oxford.json dataset/oxford-meds-13-4-6-5.txt
python mce_backend_controls.py --output reproduced-binary.json
```

On Linux, build the prime-field kernel with `g++ -std=c++20 -O3 -shared -fPIC mce_kernels.cpp -o libmce_kernels.so`. Without a native kernel the prime-field solver uses its NumPy path. The binary controls accept `--exe` for a different executable name.

Input is whitespace-delimited: `p m n k`, followed by the row-major entries of the first basis and then the second. Each basis contains `k` matrices of size `m × n`. The prime-field solver takes primes up to 65,521, matrix sides up to 128, and by default at most 100,000 projective coefficient directions after any trace-dual reduction. The binary backend has separate bounds documented with its benchmark.

- [End-to-end results and comparison scope](BENCHMARK.md)
- [Datasets, generation commands, and label audit](DATASETS.md)
- [Binary backend and ablations](mce_backend.md)
- [Reference solvers and reproduction](ref_notes.md)
