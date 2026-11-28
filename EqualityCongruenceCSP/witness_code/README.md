# Integer avoidance subroutine

The C++17 source uses GMP. On a system with GMP development libraries, build and run the 11 deterministic fixtures from this directory.

```sh
g++ -std=c++17 -O2 -Wall -Wextra -pedantic avoid.cpp -lgmpxx -lgmp -o avoid
python3 test_avoid.py
```

This program implements the exact avoidance step described in Chapter II. The `.in` and `.expected` files specify the fixtures and their expected standard output. The Python driver also verifies successful outputs by exact substitution.
