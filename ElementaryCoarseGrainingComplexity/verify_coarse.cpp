#include <array>
#include <cassert>
#include <cstdlib>
#include <iostream>
#include <vector>

struct Gate {
    int out, left, middle, right;
};

static int rule_value(int rule, int x, int y, int z) {
    return (rule >> (4 * x + 2 * y + z)) & 1;
}

static int simultaneous_update(int rule, int word, int width) {
    int result = 0;
    for (int i = width - 3; i >= 0; --i)
        result = (result << 1) | ((rule >> ((word >> i) & 7)) & 1);
    return result;
}

static std::vector<int> source_table(int rule, int block_length) {
    int m = 1 << block_length;
    std::vector<int> table;
    for (int a = 0; a < m; ++a)
        for (int b = 0; b < m; ++b)
            for (int c = 0; c < m; ++c) {
                int word = (a << (2 * block_length)) | (b << block_length) | c;
                for (int width = 3 * block_length; width > block_length; width -= 2)
                    word = simultaneous_update(rule, word, width);
                table.push_back(word);
            }
    return table;
}

static int affine_coefficients(int rule) {
    int constant = rule & 1;
    int coefficients = ((rule >> 1) & 1) ^ constant;
    coefficients |= (((rule >> 2) & 1) ^ constant) << 1;
    coefficients |= (((rule >> 4) & 1) ^ constant) << 2;
    for (int i = 0; i < 8; ++i)
        if (((rule >> i) & 1) != (constant ^ __builtin_parity(coefficients & i)))
            return -1;
    return coefficients;
}

struct Term { std::vector<Gate> steps; int final_mask = 8; };

static Term meet_term(int rule) {
    std::array<bool, 16> found{};
    found[0] = found[15] = found[12] = found[10] = true;
    std::vector<Gate> steps;
    while (!found[8] && !found[14]) {
        auto before = found;
        for (int a = 0; a < 16; ++a) if (before[a])
            for (int b = 0; b < 16; ++b) if (before[b])
                for (int c = 0; c < 16; ++c) if (before[c]) {
                    int value = 0;
                    for (int i = 0; i < 4; ++i)
                        value |= rule_value(rule, (a >> i) & 1, (b >> i) & 1, (c >> i) & 1) << i;
                    if (!found[value]) {
                        found[value] = true;
                        steps.push_back({value, a, b, c});
                    }
                }
        assert(before != found);
    }
    return {steps, found[8] ? 8 : 14};
}

static bool insert_row(std::vector<int> &pivots, int row, int m) {
    for (int i = 0; i < m; ++i) {
        if (!((row >> i) & 1)) continue;
        if (pivots[i]) row ^= pivots[i];
        else {
            pivots[i] = row;
            return true;
        }
    }
    return row == 0;
}

static bool affine_test(const std::vector<int> &table, int m, int rule, int coefficients) {
    std::vector<int> pivots(m);
    int at = 0;
    for (int a = 0; a < m; ++a)
        for (int b = 0; b < m; ++b)
            for (int c = 0; c < m; ++c) {
                int row = (rule & 1) << m;
                row ^= 1 << table[at++];
                if (coefficients & 4) row ^= 1 << a;
                if (coefficients & 2) row ^= 1 << b;
                if (coefficients & 1) row ^= 1 << c;
                if (!insert_row(pivots, row, m)) return false;
            }
    for (int zero = 0; zero < m; ++zero)
        for (int one = 0; one < m; ++one) if (one != zero) {
            auto candidate = pivots;
            if (insert_row(candidate, 1 << zero, m) &&
                insert_row(candidate, (1 << one) | (1 << m), m))
                return true;
        }
    return false;
}

static bool check(const std::vector<int> &table, int m, int rule, int map) {
    int at = 0;
    for (int a = 0; a < m; ++a)
        for (int b = 0; b < m; ++b)
            for (int c = 0; c < m; ++c)
                if (((map >> table[at++]) & 1) !=
                    rule_value(rule, (map >> a) & 1, (map >> b) & 1, (map >> c) & 1))
                    return false;
    return true;
}

static bool nonlinear_test(const std::vector<int> &table, int m, int rule, const Term &term) {
    std::vector<int> meet(m * m);
    for (int zero = 0; zero < m; ++zero)
        for (int one = 0; one < m; ++one) if (one != zero) {
            for (int a = 0; a < m; ++a)
                for (int b = 0; b < m; ++b) {
                    std::array<int, 16> values{};
                    values[0] = zero;
                    values[15] = one;
                    values[12] = a;
                    values[10] = b;
                    for (Gate gate : term.steps)
                        values[gate.out] = table[(m * values[gate.left] + values[gate.middle]) * m + values[gate.right]];
                    meet[a * m + b] = values[term.final_mask];
                }
            for (int seed = 0; seed < m; ++seed) {
                int must_include = term.final_mask == 8 ? one : zero;
                int must_exclude = term.final_mask == 8 ? zero : one;
                int map = (1 << seed) | (1 << must_include);
                for (int previous = -1; previous != map;) {
                    previous = map;
                    for (int a = 0; a < m; ++a)
                        for (int b = 0; b < m; ++b) {
                            int ab = (1 << a) | (1 << b);
                            int target = 1 << meet[a * m + b];
                            if ((map & ab) == ab) map |= target;
                            if (map & target) map |= ab;
                        }
                }
                int actual = term.final_mask == 8 ? map : (((1 << m) - 1) ^ map);
                if (!(map & (1 << must_exclude)) && check(table, m, rule, actual))
                    return true;
            }
        }
    return false;
}

int main() {
    std::array<int, 256> coefficients;
    std::array<Term, 256> terms;
    for (int target = 0; target < 256; ++target) {
        coefficients[target] = affine_coefficients(target);
        if (coefficients[target] < 0) terms[target] = meet_term(target);
    }
    for (int block_length : {1, 2, 3}) {
        int m = 1 << block_length;
        int yes = 0;
        for (int source = 0; source < 256; ++source) {
            auto table = source_table(source, block_length);
            for (int target = 0; target < 256; ++target) {
                bool brute = false;
                for (int map = 1; !brute && map < (1 << m) - 1; ++map)
                    brute = check(table, m, target, map);
                bool fast = coefficients[target] >= 0
                    ? affine_test(table, m, target, coefficients[target])
                    : nonlinear_test(table, m, target, terms[target]);
                if (fast != brute) {
                    std::cerr << "Mismatch " << block_length << " " << source << " " << target << "\n";
                    return EXIT_FAILURE;
                }
                yes += fast;
            }
        }
        std::cout << "PASS: all 65,536 ordered rule pairs at block length " << block_length
                  << ", with " << yes << " yes instances\n";
    }
}
