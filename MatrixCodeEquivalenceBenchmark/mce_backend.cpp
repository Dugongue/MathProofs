#include <algorithm>
#include <bit>
#include <chrono>
#include <cstdint>
#include <exception>
#include <iostream>
#include <map>
#include <numeric>
#include <optional>
#include <random>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Word = std::uint64_t;
using Bits = std::vector<Word>;
using Clock = std::chrono::steady_clock;

struct Deadline {
    Clock::time_point finish;
    struct Reached {};
    void check() const {
        if (Clock::now() >= finish) throw Reached{};
    }
};

struct Matrix {
    int rows, cols, width;
    std::vector<Word> data;
    Matrix(int nr, int nc) : rows(nr), cols(nc), width((nc + 63) / 64), data(nr * width) {}
    Word* row(int i) { return data.data() + i * width; }
    const Word* row(int i) const { return data.data() + i * width; }
    bool at(int i, int j) const { return (row(i)[j / 64] >> (j % 64)) & 1; }
    void flip(int i, int j) { row(i)[j / 64] ^= Word(1) << (j % 64); }
    void swap_rows(int i, int j) {
        for (int w = 0; w < width; ++w) std::swap(row(i)[w], row(j)[w]);
    }
    void add_row(int dst, int src, int start = 0) {
        for (int w = start; w < width; ++w) row(dst)[w] ^= row(src)[w];
    }
    void xor_with(const Matrix& b) {
        for (std::size_t i = 0; i < data.size(); ++i) data[i] ^= b.data[i];
    }
};

static Matrix identity(int n) {
    Matrix a(n, n);
    for (int i = 0; i < n; ++i) a.flip(i, i);
    return a;
}

static int rank(Matrix a) {
    int r = 0;
    for (int j = 0; j < a.cols && r < a.rows; ++j) {
        int pivot = r;
        while (pivot < a.rows && !a.at(pivot, j)) ++pivot;
        if (pivot == a.rows) continue;
        a.swap_rows(r, pivot);
        const int word = j / 64;
        const int pos = j % 64;
        const Word* const source = a.row(r);
        for (int i = r + 1; i < a.rows; ++i) {
            Word* const target = a.row(i);
            const Word mask = Word(0) - ((target[word] >> pos) & 1);
            for (int w = word; w < a.width; ++w) target[w] ^= source[w] & mask;
        }
        ++r;
    }
    return r;
}

static bool invert(Matrix a, Matrix& inv) {
    inv = identity(a.rows);
    for (int j = 0; j < a.rows; ++j) {
        int pivot = j;
        while (pivot < a.rows && !a.at(pivot, j)) ++pivot;
        if (pivot == a.rows) return false;
        a.swap_rows(j, pivot);
        inv.swap_rows(j, pivot);
        for (int i = 0; i < a.rows; ++i) {
            if (i != j && a.at(i, j)) {
                a.add_row(i, j, j / 64);
                inv.add_row(i, j);
            }
        }
    }
    return true;
}

static Matrix multiply(const Matrix& a, const Matrix& b) {
    Matrix c(a.rows, b.cols);
    for (int i = 0; i < a.rows; ++i) {
        auto* out = c.row(i);
        for (int w = 0; w < a.width; ++w) {
            Word bits = a.row(i)[w];
            while (bits) {
                int j = 64 * w + std::countr_zero(bits);
                for (int s = 0; s < b.width; ++s) out[s] ^= b.row(j)[s];
                bits &= bits - 1;
            }
        }
    }
    return c;
}

static bool bit(const Bits& v, int i) { return (v[i / 64] >> (i % 64)) & 1; }
static void toggle(Bits& v, int i) { v[i / 64] ^= Word(1) << (i % 64); }

static Bits matvec(const Matrix& a, const Bits& v) {
    Bits out((a.rows + 63) / 64);
    for (int i = 0; i < a.rows; ++i) {
        Word acc = 0;
        for (int w = 0; w < a.width; ++w) acc ^= a.row(i)[w] & v[w];
        if (std::popcount(acc) & 1) toggle(out, i);
    }
    return out;
}

struct LinearSystem {
    int vars, words, dimension;
    std::vector<Bits> pivots;
    explicit LinearSystem(int d) : vars(d), words((d + 63) / 64), dimension(d), pivots(d) {}
    bool add(Bits v) {
        for (int w = 0; w < words; ++w) {
            while (v[w]) {
                int p = 64 * w + std::countr_zero(v[w]);
                if (pivots[p].empty()) {
                    pivots[p] = std::move(v);
                    --dimension;
                    return true;
                }
                for (int j = w; j < words; ++j) v[j] ^= pivots[p][j];
            }
        }
        return false;
    }
    std::vector<Bits> kernel() const {
        std::vector<Bits> result;
        for (int p = 0; p < vars; ++p) {
            if (!pivots[p].empty()) continue;
            Bits v(words);
            toggle(v, p);
            for (int j = vars - 1; j >= 0; --j) {
                if (pivots[j].empty()) continue;
                Word acc = 0;
                for (int w = j / 64; w < words; ++w) acc ^= pivots[j][w] & v[w];
                if (std::popcount(acc) & 1) toggle(v, j);
            }
            result.push_back(std::move(v));
        }
        return result;
    }
};

static Matrix combination(const std::vector<Matrix>& a, unsigned point) {
    Matrix m(a.front().rows, a.front().cols);
    while (point) {
        m.xor_with(a[std::countr_zero(point)]);
        point &= point - 1;
    }
    return m;
}

static std::vector<int> all_ranks(const std::vector<Matrix>& a, const Deadline& deadline) {
    unsigned n = 1u << a.size();
    std::vector<int> ranks(n);
    Matrix current(a.front().rows, a.front().cols);
    for (unsigned i = 1; i < n; ++i) {
        if ((i & 127) == 1) deadline.check();
        current.xor_with(a[std::countr_zero(i)]);
        ranks[i ^ (i >> 1)] = rank(current);
    }
    return ranks;
}

static void walsh(std::vector<std::int64_t>& x) {
    for (std::size_t q = 1; q < x.size(); q <<= 1) {
        for (std::size_t i = 0; i < x.size(); i += 2 * q) {
            for (std::size_t j = i; j < i + q; ++j) {
                auto u = x[j], v = x[j + q];
                x[j] = u + v;
                x[j + q] = u - v;
            }
        }
    }
}

struct Colors {
    std::vector<int> source, target;
    std::vector<std::vector<unsigned>> target_class;
    bool same_histograms = false;
};

static Colors compare_colors(const std::vector<int>& ra, const std::vector<int>& rb,
                             bool rank_only, const Deadline& deadline) {
    int n = static_cast<int>(ra.size());
    int maxr = std::max(*std::max_element(ra.begin(), ra.end()),
                        *std::max_element(rb.begin(), rb.end()));
    std::vector<int> ha(maxr + 1), hb(maxr + 1);
    for (int x : ra) ++ha[x];
    for (int y : rb) ++hb[y];
    if (ha != hb) return {};
    // Enumerating all unordered pairs is helpful on dense square codes.
    // For many different ranks, the first eight nonzero rank colors suffice
    // as safe invariants. The cutoff depends only on the shared histogram.
    std::vector<int> selected;
    if (!rank_only)
        for (int r = 1; r <= maxr; ++r)
            if (ha[r] && selected.size() < 8) selected.push_back(r);
    auto signatures = [&](const std::vector<int>& ranks) {
        std::vector<std::vector<int>> result(n, std::vector<int>(
            1 + selected.size() * (selected.size() + 1) / 2));
        for (int p = 0; p < n; ++p) result[p][0] = ranks[p];
        std::vector<std::vector<std::int64_t>> transformed;
        for (int r : selected) {
            std::vector<std::int64_t> indicator(n);
            for (int p = 0; p < n; ++p) indicator[p] = ranks[p] == r;
            walsh(indicator);
            transformed.push_back(std::move(indicator));
        }
        std::vector<std::int64_t> conv(n);
        int pos = 1;
        for (std::size_t i = 0; i < selected.size(); ++i) {
            for (std::size_t j = i; j < selected.size(); ++j) {
                deadline.check();
                for (int p = 0; p < n; ++p) conv[p] = transformed[i][p] * transformed[j][p];
                walsh(conv);
                for (int p = 0; p < n; ++p) result[p][pos] = static_cast<int>(conv[p] / n);
                ++pos;
            }
        }
        return result;
    };
    auto a = signatures(ra);
    auto b = signatures(rb);
    std::map<std::vector<int>, int> ids;
    Colors out;
    out.source.resize(n);
    out.target.resize(n);
    for (int p = 0; p < n; ++p) {
        auto [it, inserted] = ids.try_emplace(std::move(a[p]), static_cast<int>(ids.size()));
        out.source[p] = it->second;
    }
    std::vector<int> counts(ids.size());
    for (int c : out.source) ++counts[c];
    out.target_class.resize(ids.size());
    for (int p = 0; p < n; ++p) {
        auto it = ids.find(b[p]);
        if (it == ids.end()) return {};
        out.target[p] = it->second;
        out.target_class[it->second].push_back(static_cast<unsigned>(p));
    }
    for (std::size_t c = 0; c < counts.size(); ++c)
        if (counts[c] != static_cast<int>(out.target_class[c].size())) return {};
    out.same_histograms = true;
    return out;
}

struct Stacks {
    unsigned n;
    std::vector<unsigned short> colors;
    unsigned short operator()(unsigned x, unsigned y) const { return colors[x * n + y]; }
};

static Stacks all_stacks(const std::vector<Matrix>& input, const Deadline& deadline) {
    auto a = input;
    if (a.front().rows > a.front().cols) {
        for (auto& m : a) {
            Matrix t(m.cols, m.rows);
            for (int i = 0; i < m.rows; ++i)
                for (int j = 0; j < m.cols; ++j) if (m.at(i, j)) t.flip(j, i);
            m = std::move(t);
        }
    }
    auto count = 1u << a.size();
    int m = a.front().rows, n = a.front().cols;
    std::vector<Matrix> matrices;
    for (unsigned x = 0; x < count; ++x) matrices.push_back(combination(a, x));
    Stacks result{count, std::vector<unsigned short>(count * count)};
    for (unsigned x = 1; x < count; ++x) {
        deadline.check();
        for (unsigned y = x + 1; y < count; ++y) {
            unsigned z = x ^ y;
            if (z <= y) continue;
            Matrix stack(2 * m, n);
            std::copy(matrices[x].data.begin(), matrices[x].data.end(), stack.row(0));
            std::copy(matrices[y].data.begin(), matrices[y].data.end(), stack.row(m));
            auto value = static_cast<unsigned short>(rank(std::move(stack)));
            result.colors[x * count + y] = result.colors[y * count + x] = value;
            result.colors[y * count + z] = result.colors[z * count + y] = value;
            result.colors[z * count + x] = result.colors[x * count + z] = value;
        }
    }
    return result;
}

static bool refine_by_stacks(Colors& points, const Stacks& a, const Stacks& b) {
    for (int pass = 0; pass < 3; ++pass) {
        std::map<std::vector<int>, int> palette;
        auto relabel = [&](const Stacks& stacks, const std::vector<int>& colors) {
            std::vector<int> new_colors(stacks.n);
            int nc = static_cast<int>(points.target_class.size());
            for (unsigned x = 0; x < stacks.n; ++x) {
                std::vector<int> key{colors[x]};
                for (unsigned y = 0; y < stacks.n; ++y) {
                    auto [u, v] = std::minmax(colors[y], colors[x ^ y]);
                    key.push_back((stacks(x, y) * nc + u) * nc + v);
                }
                std::sort(key.begin() + 1, key.end());
                auto it = palette.try_emplace(std::move(key), static_cast<int>(palette.size())).first;
                new_colors[x] = it->second;
            }
            return new_colors;
        };
        auto sa = relabel(a, points.source);
        auto sb = relabel(b, points.target);
        std::vector<unsigned> ha(palette.size()), hb(palette.size());
        for (int c : sa) ++ha[c];
        for (int c : sb) ++hb[c];
        if (ha != hb) return false;
        bool stable = palette.size() == points.target_class.size();
        points.source = std::move(sa);
        points.target = std::move(sb);
        points.target_class.assign(palette.size(), {});
        for (unsigned y = 0; y < b.n; ++y) points.target_class[points.target[y]].push_back(y);
        if (stable) break;
    }
    return true;
}

enum class Verdict { yes, no, unknown };

struct Witness {
    Matrix l, r;
    std::vector<unsigned> s;
    Witness(int m, int n) : l(m, m), r(n, n) {}
};

static bool verify(const std::vector<Matrix>& a, const std::vector<Matrix>& y,
                   Witness& witness, Matrix l, const Matrix& h) {
    if (rank(l) != l.rows || !invert(h, witness.r)) return false;
    for (std::size_t i = 0; i < a.size(); ++i)
        if (multiply(l, a[i]).data != multiply(y[i], h).data) return false;
    witness.l = std::move(l);
    return true;
}

static std::pair<Matrix, Matrix> rank_frames(Matrix a) {
    Matrix left = identity(a.rows), right = identity(a.cols);
    for (int j = 0; j < std::min(a.rows, a.cols); ++j) {
        int ri = j, ci = j;
        bool found = false;
        for (ri = j; ri < a.rows && !found; ++ri) {
            for (ci = j; ci < a.cols; ++ci) {
                if (a.at(ri, ci)) { found = true; break; }
            }
        }
        if (!found) break;
        --ri;
        a.swap_rows(ri, j);
        left.swap_rows(ri, j);
        if (ci != j) {
            for (int i = 0; i < a.rows; ++i) {
                if (a.at(i, ci) != a.at(i, j)) { a.flip(i, ci); a.flip(i, j); }
            }
            for (int i = 0; i < a.cols; ++i) {
                if (right.at(i, ci) != right.at(i, j)) { right.flip(i, ci); right.flip(i, j); }
            }
        }
        for (int i = 0; i < a.rows; ++i)
            if (i != j && a.at(i, j)) { a.add_row(i, j); left.add_row(i, j); }
        for (int c = j + 1; c < a.cols; ++c) {
            if (!a.at(j, c)) continue;
            for (int i = 0; i < a.rows; ++i) if (a.at(i, j)) a.flip(i, c);
            for (int i = 0; i < a.cols; ++i) if (right.at(i, j)) right.flip(i, c);
        }
    }
    return {std::move(left), std::move(right)};
}

static bool find_cyclic(const Matrix& a, Matrix& frame, const Deadline& deadline) {
    int n = a.rows;
    std::mt19937_64 rng(0x1d0cb0dd);
    for (int trial = 0; trial < std::min(n + 4, 12); ++trial) {
        deadline.check();
        Bits v(a.width);
        if (trial < 4 && trial < n) toggle(v, trial);
        else {
            for (auto& word : v) word = rng();
            if (n % 64) v.back() &= (Word(1) << (n % 64)) - 1;
        }
        LinearSystem span(n);
        Matrix f(n, n);
        for (int j = 0; j < n; ++j) {
            if (!span.add(v)) break;
            for (int i = 0; i < n; ++i) if (bit(v, i)) f.flip(i, j);
            if (j == n - 1) { frame = std::move(f); return true; }
            v = matvec(a, v);
        }
    }
    return false;
}

template <class F>
static Verdict search_kernel(const LinearSystem& system, int max_exact,
                             F&& check, const Deadline& deadline) {
    auto basis = system.kernel();
    if (basis.empty()) return Verdict::no;
    int d = static_cast<int>(basis.size());
    Bits v(system.words);
    if (d <= max_exact) {
        for (unsigned i = 1; i < (1u << d); ++i) {
            if ((i & 63) == 1) deadline.check();
            const Bits& b = basis[std::countr_zero(i)];
            for (int j = 0; j < system.words; ++j) v[j] ^= b[j];
            if (check(v)) return Verdict::yes;
        }
        return Verdict::no;
    }
    std::mt19937_64 rng(0x2f9dd126);
    for (int trial = 0; trial < 128; ++trial) {
        deadline.check();
        std::fill(v.begin(), v.end(), 0);
        if (trial < std::min(d, 8)) v = basis[trial];
        else
            for (const auto& b : basis)
                if (rng() & 1)
                    for (int j = 0; j < system.words; ++j) v[j] ^= b[j];
        if (check(v)) return Verdict::yes;
    }
    return Verdict::unknown;
}

template <class F>
static std::optional<Verdict> cyclic_lift(const std::vector<Matrix>& ts,
                                          const std::vector<Matrix>& us,
                                          F&& check, const Deadline& deadline) {
    const int n = ts.front().rows;
    Matrix frame(n, n), inv_frame(n, n);
    for (std::size_t j = 0; j < std::min<std::size_t>(4, ts.size()); ++j) {
        if (!find_cyclic(ts[j], frame, deadline)) continue;
        if (!invert(frame, inv_frame)) throw std::logic_error("invalid cyclic frame");
        std::vector<Matrix> powers;
        powers.push_back(identity(n));
        for (int e = 1; e < n; ++e) powers.push_back(multiply(us[j], powers.back()));
        auto candidate = [&](const Bits& w) {
            Matrix image(n, n);
            for (int e = 0; e < n; ++e) {
                Bits column = matvec(powers[e], w);
                for (int r = 0; r < n; ++r) if (bit(column, r)) image.flip(r, e);
            }
            auto l = multiply(image, inv_frame);
            return check(std::move(l));
        };
        LinearSystem sys(n);
        if (n <= 6) return search_kernel(sys, 6, candidate, deadline);
        for (std::size_t i = 0; i < ts.size(); ++i) {
            auto c = multiply(multiply(inv_frame, ts[i]), frame);
            for (int col = 0; col < n; ++col) {
                if ((col & 7) == 0) deadline.check();
                auto delta = multiply(us[i], powers[col]);
                for (int e = 0; e < n; ++e)
                    if (c.at(e, col)) delta.xor_with(powers[e]);
                for (int r = 0; r < n; ++r)
                    sys.add(Bits(delta.row(r), delta.row(r) + delta.width));
                // It is exact to check all surviving candidates early.
                // Each check verifies every original equation.
                if (sys.dimension <= 6) return search_kernel(sys, 6, candidate, deadline);
            }
        }
        return search_kernel(sys, 15, candidate, deadline);
    }
    return std::nullopt;
}

static Matrix transpose(const Matrix& a) {
    Matrix b(a.cols, a.rows);
    for (int i = 0; i < a.rows; ++i)
        for (int j = 0; j < a.cols; ++j)
            if (a.at(i, j)) b.flip(j, i);
    return b;
}

static Matrix row_stack(const Matrix& a, const Matrix& b) {
    Matrix result(a.rows + b.rows, a.cols);
    std::copy(a.data.begin(), a.data.end(), result.row(0));
    std::copy(b.data.begin(), b.data.end(), result.row(a.rows));
    return result;
}

static Matrix column_block(const Matrix& a, int block) {
    Matrix out(a.rows, a.rows);
    for (int i = 0; i < out.rows; ++i)
        for (int j = 0; j < out.cols; ++j)
            if (a.at(i, block * out.cols + j)) out.flip(i, j);
    return out;
}

static Matrix double_diagonal(const Matrix& a) {
    Matrix out(2 * a.rows, 2 * a.cols);
    for (int i = 0; i < a.rows; ++i)
        for (int j = 0; j < a.cols; ++j)
            if (a.at(i, j)) {
                out.flip(i, j);
                out.flip(i + a.rows, j + a.cols);
            }
    return out;
}

static Verdict lift_tuple(const std::vector<Matrix>& a, const std::vector<Matrix>& y,
                          Witness& witness, const Deadline& deadline) {
    const int m = a.front().rows, n = a.front().cols;
    if (a.size() == 1) {
        auto [la, ra] = rank_frames(a[0]);
        auto [lb, rb] = rank_frames(y[0]);
        Matrix ilb(m, m), h(n, n);
        if (!invert(lb, ilb)) throw std::logic_error("invalid row frame");
        Matrix ira(n, n);
        if (!invert(ra, ira)) throw std::logic_error("invalid column frame");
        // la * a * ra = lb * y * rb. Here h is inverse to ra * rb^{-1}.
        h = multiply(rb, ira);
        return verify(a, y, witness, multiply(ilb, la), h) ? Verdict::yes : Verdict::no;
    }

    if (m == 2 * n) {
        std::vector<Matrix> ta, ty;
        for (const auto& x : a) ta.push_back(transpose(x));
        for (const auto& x : y) ty.push_back(transpose(x));
        Witness swapped(n, m);
        auto result = lift_tuple(ta, ty, swapped, deadline);
        if (result == Verdict::yes) {
            witness.l = transpose(swapped.r);
            witness.r = transpose(swapped.l);
        }
        return result;
    }

    if (n == 2 * m) {
        Matrix ainv(n, n), yinv(n, n);
        for (std::size_t i = 0; i < a.size(); ++i) {
            for (std::size_t j = i + 1; j < a.size(); ++j) {
                deadline.check();
                auto a_stack = row_stack(a[i], a[j]);
                if (!invert(a_stack, ainv)) continue;
                if (!invert(row_stack(y[i], y[j]), yinv)) return Verdict::no;
                std::vector<Matrix> ts, us;
                for (std::size_t h = 0; h < a.size(); ++h) {
                    if (h == i || h == j) continue;
                    auto c = multiply(a[h], ainv);
                    auto d = multiply(y[h], yinv);
                    for (int block = 0; block < 2; ++block) {
                        ts.push_back(column_block(c, block));
                        us.push_back(column_block(d, block));
                    }
                }
                if (ts.empty()) {
                    auto l = identity(m);
                    auto h = multiply(yinv, a_stack);
                    return verify(a, y, witness, std::move(l), h)
                        ? Verdict::yes : Verdict::no;
                }
                auto lifted = cyclic_lift(ts, us, [&](Matrix l) {
                    auto h = multiply(multiply(yinv, double_diagonal(l)), a_stack);
                    return verify(a, y, witness, std::move(l), h);
                }, deadline);
                if (lifted) return *lifted;
                break;
            }
        }
    }

    if (m == n) {
        Matrix ainv(n, n), yinv(n, n);
        for (std::size_t base = 0; base < a.size(); ++base) {
            deadline.check();
            if (!invert(a[base], ainv)) continue;
            if (!invert(y[base], yinv)) return Verdict::no;
            std::vector<Matrix> ts, us;
            for (std::size_t i = 0; i < a.size(); ++i) {
                if (i == base) continue;
                ts.push_back(multiply(a[i], ainv));
                us.push_back(multiply(y[i], yinv));
            }
            auto lifted = cyclic_lift(ts, us, [&](Matrix l) {
                auto h = multiply(multiply(yinv, l), a[base]);
                return verify(a, y, witness, std::move(l), h);
            }, deadline);
            if (lifted) return *lifted;
            // The generic fallback below still applies. Try another full-rank
            // basis slice before expanding the complete m^2+n^2 system.
        }
    }

    int vars = m * m + n * n;
    if (vars > 3000) return Verdict::unknown;
    LinearSystem sys(vars);
    for (std::size_t i = 0; i < a.size(); ++i) {
        for (int r = 0; r < m; ++r) {
            deadline.check();
            for (int c = 0; c < n; ++c) {
                Bits eq(sys.words);
                for (int h = 0; h < m; ++h) if (a[i].at(h, c)) toggle(eq, r * m + h);
                for (int h = 0; h < n; ++h) if (y[i].at(r, h)) toggle(eq, m * m + h * n + c);
                sys.add(std::move(eq));
            }
        }
    }
    return search_kernel(sys, 15, [&](const Bits& point) {
        Matrix l(m, m), h(n, n);
        for (int i = 0; i < m; ++i)
            for (int j = 0; j < m; ++j) if (bit(point, i * m + j)) l.flip(i, j);
        for (int i = 0; i < n; ++i)
            for (int j = 0; j < n; ++j) if (bit(point, m * m + i * n + j)) h.flip(i, j);
        return verify(a, y, witness, std::move(l), h);
    }, deadline);
}

struct Search {
    const std::vector<Matrix>& a;
    const std::vector<Matrix>& b;
    const Colors& colors;
    const Deadline& deadline;
    Witness& witness;
    const Stacks* sa;
    const Stacks* sb;
    unsigned points;
    std::vector<unsigned> xs{0}, ys{0};
    std::vector<int> map, used;
    unsigned branches = 0, lifted = 0;
    bool incomplete = false;
    Search(const std::vector<Matrix>& in_a, const std::vector<Matrix>& in_b,
           const Colors& c, const Deadline& d, Witness& out,
           const Stacks* stacks_a = nullptr, const Stacks* stacks_b = nullptr)
        : a(in_a), b(in_b), colors(c), deadline(d), witness(out), sa(stacks_a), sb(stacks_b),
          points(1u << a.size()), map(points, -1), used(points, -1) { map[0] = used[0] = 0; }

    bool compatible(unsigned x, unsigned y) const {
        if (used[y] >= 0) return false;
        for (std::size_t i = 0; i < xs.size(); ++i)
            if (colors.source[x ^ xs[i]] != colors.target[y ^ ys[i]] ||
                (sa && (*sa)(x, xs[i]) != (*sb)(y, ys[i]))) return false;
        return true;
    }
    void add(unsigned x, unsigned y) {
        auto size = xs.size();
        for (std::size_t i = 0; i < size; ++i) {
            unsigned px = x ^ xs[i], py = y ^ ys[i];
            map[px] = static_cast<int>(py);
            used[py] = static_cast<int>(px);
            xs.push_back(px);
            ys.push_back(py);
        }
    }
    void remove() {
        auto half = xs.size() / 2;
        for (std::size_t i = half; i < xs.size(); ++i) {
            map[xs[i]] = -1;
            used[ys[i]] = -1;
        }
        xs.resize(half);
        ys.resize(half);
    }
    bool choose_forced() {
        for (unsigned x = 1; x < points; ++x) {
            const auto& cls = colors.target_class[colors.source[x]];
            if (cls.size() != 1) continue;
            unsigned y = cls.front();
            if (map[x] >= 0) {
                if (map[x] != static_cast<int>(y)) return false;
            } else {
                if (!compatible(x, y)) return false;
                add(x, y);
            }
        }
        return true;
    }
    bool visit() {
        deadline.check();
        ++branches;
        if (xs.size() == points) {
            ++lifted;
            std::vector<Matrix> images;
            witness.s.resize(a.size());
            for (std::size_t j = 0; j < a.size(); ++j) {
                witness.s[j] = static_cast<unsigned>(map[1u << j]);
                images.push_back(combination(b, witness.s[j]));
            }
            auto result = lift_tuple(a, images, witness, deadline);
            incomplete |= result == Verdict::unknown;
            return result == Verdict::yes;
        }
        unsigned pivot = 0, best = points + 1;
        for (unsigned x = 1; x < points; ++x) {
            if (map[x] >= 0) continue;
            unsigned count = static_cast<unsigned>(colors.target_class[colors.source[x]].size());
            if (count < best) { pivot = x; best = count; }
        }
        const auto& cls = colors.target_class[colors.source[pivot]];
        for (std::size_t i = 0; i < cls.size(); ++i) {
            if ((i & 127) == 0) deadline.check();
            unsigned y = cls[i];
            if (!compatible(pivot, y)) continue;
            add(pivot, y);
            if (visit()) return true;
            remove();
        }
        return false;
    }
};

static double millis(Clock::time_point begin) {
    return std::chrono::duration<double, std::milli>(Clock::now() - begin).count();
}

static void print_matrix(const Matrix& m) {
    std::cout << '[';
    for (int i = 0; i < m.rows; ++i) {
        if (i) std::cout << ',';
        std::cout << '[';
        for (int j = 0; j < m.cols; ++j) {
            if (j) std::cout << ',';
            std::cout << static_cast<int>(m.at(i, j));
        }
        std::cout << ']';
    }
    std::cout << ']';
}

int main(int argc, char** argv) {
    int budget_ms = 5000;
    bool rank_only = false, no_stacks = false;
    for (int i = 1; i < argc; ++i) {
        std::string flag(argv[i]);
        if (flag == "--rank-only") rank_only = true;
        else if (flag == "--no-stacks") no_stacks = true;
        else if (flag == "--budget-ms" && i + 1 < argc) budget_ms = std::stoi(argv[++i]);
        else { std::cerr << "usage: mce_backend [--rank-only] [--no-stacks] [--budget-ms N]\n"; return 2; }
    }
    if (budget_ms <= 0) { std::cerr << "expected positive budget\n"; return 2; }
    int p, m, n, k;
    while (std::cin >> p >> m >> n >> k) {
        auto start = Clock::now();
        if (p != 2 || m < 1 || n < 1 || m > 128 || n > 128 || k < 1 || k > 16) {
            std::cerr << "only p=2, dimensions 1..128 and code dimension 1..16 supported\n";
            return 2;
        }
        auto read = [&](std::vector<Matrix>& code) {
            for (int s = 0; s < k; ++s) {
                Matrix a(m, n);
                for (int i = 0; i < m; ++i) for (int j = 0; j < n; ++j) {
                    int x;
                    if (!(std::cin >> x) || (x != 0 && x != 1)) return false;
                    if (x) a.flip(i, j);
                }
                code.push_back(std::move(a));
            }
            return true;
        };
        std::vector<Matrix> a, b;
        if (!(read(a) && read(b))) { std::cerr << "invalid or incomplete matrix data\n"; return 2; }
        double input_ms = millis(start), rank_ms = 0, color_ms = 0, stack_ms = 0;
        unsigned branches = 0, lifted = 0, classes = 0, forced_dim = 0;
        Deadline d{Clock::now() + std::chrono::milliseconds(budget_ms)};
        std::string verdict = "unknown";
        Witness witness(m, n);
        try {
            auto phase = Clock::now();
            auto ra = all_ranks(a, d), rb = all_ranks(b, d);
            rank_ms = millis(phase);
            if (std::count(ra.begin(), ra.end(), 0) != 1 ||
                std::count(rb.begin(), rb.end(), 0) != 1) { verdict = "invalid-basis"; }
            else {
                phase = Clock::now();
                auto colors = compare_colors(ra, rb, rank_only, d);
                color_ms = millis(phase);
                std::optional<Stacks> sa, sb;
                if (colors.same_histograms && 2 * std::max(m, n) >= 3 * std::min(m, n) &&
                    k >= 2 && k <= 8 &&
                    !rank_only && !no_stacks) {
                    phase = Clock::now();
                    sa = all_stacks(a, d);
                    sb = all_stacks(b, d);
                    colors.same_histograms = refine_by_stacks(colors, *sa, *sb);
                    stack_ms = millis(phase);
                }
                if (!colors.same_histograms) verdict = "no";
                else {
                    classes = static_cast<unsigned>(colors.target_class.size());
                    Search search(a, b, colors, d, witness, sa ? &*sa : nullptr, sb ? &*sb : nullptr);
                    bool forced = search.choose_forced();
                    forced_dim = std::bit_width(search.xs.size()) - 1;
                    if (!forced) verdict = "no";
                    else {
                        try {
                            if (search.visit()) verdict = "yes";
                            else if (!search.incomplete) verdict = "no";
                        } catch (const Deadline::Reached&) {}
                    }
                    branches = search.branches;
                    lifted = search.lifted;
                }
            }
        } catch (const Deadline::Reached&) {}
        std::cout << "{\"result\":\"" << verdict << "\",\"input_ms\":" << input_ms
                  << ",\"rank_ms\":" << rank_ms << ",\"color_ms\":" << color_ms
                  << ",\"stack_ms\":" << stack_ms
                  << ",\"total_ms\":" << millis(start) << ",\"classes\":" << classes
                  << ",\"forced_dimension\":" << forced_dim << ",\"branches\":" << branches
                  << ",\"lifted\":" << lifted;
        if (verdict == "yes") {
            std::cout << ",\"L\":"; print_matrix(witness.l);
            std::cout << ",\"R\":"; print_matrix(witness.r);
            Matrix s(k, k);
            for (int i = 0; i < k; ++i)
                for (int j = 0; j < k; ++j) if ((witness.s[j] >> i) & 1) s.flip(i, j);
            std::cout << ",\"S\":"; print_matrix(s);
        }
        std::cout << "}" << std::endl;
    }
}
