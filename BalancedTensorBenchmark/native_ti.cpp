#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Clock = std::chrono::steady_clock;
using Tensor = std::vector<std::uint8_t>;
using Domains = std::vector<std::vector<int>>;

static double milliseconds(Clock::time_point begin) {
    return std::chrono::duration<double, std::milli>(Clock::now() - begin).count();
}

struct Matrix {
    std::array<unsigned, 3> rows{};
    std::array<unsigned, 8> pullback{};
};

static unsigned parity(unsigned x) {
    return std::popcount(x) & 1U;
}

static std::vector<Matrix> changes(int n) {
    std::vector<Matrix> result;
    for (unsigned word = 0; word < (1U << (n * n)); ++word) {
        Matrix matrix;
        for (int i = 0; i < n; ++i) {
            matrix.rows[i] = (word >> (i * n)) & ((1U << n) - 1);
        }
        bool invertible = true;
        for (unsigned bits = 1; bits < (1U << n); ++bits) {
            unsigned value = 0;
            for (int i = 0; i < n; ++i) {
                if (bits & (1U << i)) {
                    value ^= matrix.rows[i];
                }
            }
            matrix.pullback[bits] = value;
            invertible &= value != 0;
        }
        if (invertible) {
            result.push_back(matrix);
        }
    }
    return result;
}

struct Layout {
    std::vector<int> dims;
    std::vector<std::size_t> strides;
    std::size_t size = 1;

    explicit Layout(std::vector<int> sides) : dims(std::move(sides)), strides(dims.size()) {
        for (int i = static_cast<int>(dims.size()) - 1; i >= 0; --i) {
            if (dims[i] < 1 || dims[i] > 3) {
                throw std::runtime_error("Each local dimension must be in 1..3");
            }
            strides[i] = size;
            size *= dims[i];
            if (size > (1U << 20)) {
                throw std::runtime_error("Dense payload exceeds the experimental input cap");
            }
        }
    }

    std::vector<std::size_t> offsets(const std::vector<int>& modes) const {
        std::vector<std::size_t> result{0};
        for (int axis : modes) {
            std::vector<std::size_t> next;
            next.reserve(result.size() * dims[axis]);
            for (auto base : result) {
                for (int i = 0; i < dims[axis]; ++i) {
                    next.push_back(base + i * strides[axis]);
                }
            }
            result = std::move(next);
        }
        return result;
    }
};

static void apply(const Layout& l, int axis, const Matrix& m,
                  const Tensor& input, Tensor& output) {
    const auto stride = l.strides[axis];
    const int side = l.dims[axis];
    for (std::size_t block = 0; block < l.size; block += stride * side) {
        for (std::size_t j = block; j < block + stride; ++j) {
            unsigned bits = 0;
            for (int i = 0; i < side; ++i) {
                bits |= unsigned(input[j + i * stride]) << i;
            }
            for (int i = 0; i < side; ++i) {
                output[j + i * stride] = static_cast<std::uint8_t>(parity(bits & m.rows[i]));
            }
        }
    }
}

static bool match_last(const Layout& l, int axis, const Matrix& m,
                       const Tensor& input, const Tensor& goal) {
    const auto stride = l.strides[axis];
    const int side = l.dims[axis];
    for (std::size_t block = 0; block < l.size; block += stride * side) {
        for (std::size_t j = block; j < block + stride; ++j) {
            unsigned bits = 0;
            for (int i = 0; i < side; ++i) {
                bits |= unsigned(input[j + i * stride]) << i;
            }
            for (int i = 0; i < side; ++i) {
                if (goal[j + i * stride] != parity(bits & m.rows[i])) {
                    return false;
                }
            }
        }
    }
    return true;
}

static unsigned binary_rank(std::vector<std::uint64_t>& data, std::size_t rows,
                            std::size_t cols, std::size_t words) {
    std::size_t rank = 0;
    for (std::size_t c = 0; c < cols && rank < rows; ++c) {
        const auto word = c / 64;
        const auto bit = std::uint64_t{1} << (c % 64);
        auto pivot = rank;
        while (pivot < rows && !(data[pivot * words + word] & bit)) {
            ++pivot;
        }
        if (pivot == rows) {
            continue;
        }
        for (auto w = word; w < words; ++w) {
            std::swap(data[pivot * words + w], data[rank * words + w]);
        }
        for (auto r = rank + 1; r < rows; ++r) {
            if (data[r * words + word] & bit) {
                for (auto w = word; w < words; ++w) {
                    data[r * words + w] ^= data[rank * words + w];
                }
            }
        }
        ++rank;
    }
    return static_cast<unsigned>(rank);
}

struct Cut {
    std::vector<std::size_t> row_offsets;
    std::vector<std::size_t> col_offsets;
};

static Cut pair_cut(const Layout& l, int x, int y, int split) {
    std::array<std::vector<int>, 2> modes;
    std::array<std::size_t, 2> volume{1, 1};
    std::vector<int> active;
    for (int i = 0; i < static_cast<int>(l.dims.size()); ++i) {
        if (i != x && i != y) {
            active.push_back(i);
        }
    }
    std::stable_sort(active.begin(), active.end(), [&](int i, int j) {
        return l.dims[i] > l.dims[j];
    });
    if (split && active.size() >= 4) {
        std::swap(active[1], active[2]);
    }
    for (int i : active) {
        const int side = volume[0] <= volume[1] ? 0 : 1;
        modes[side].push_back(i);
        volume[side] *= l.dims[i];
    }
    if (volume[1] > volume[0]) {
        std::swap(modes[0], modes[1]);
    }
    return {l.offsets(modes[0]), l.offsets(modes[1])};
}

static std::vector<unsigned> rank_table(const Layout& l, int x, int y,
                                        const Cut& cut, const Tensor& input) {
    const unsigned nx = 1U << l.dims[x];
    const unsigned ny = 1U << l.dims[y];
    const auto rows = cut.row_offsets.size();
    const auto cols = cut.col_offsets.size();
    const auto words = (cols + 63) / 64;
    const auto plane_size = rows * words;
    const int plane_count = l.dims[x] * l.dims[y];
    std::vector<std::uint64_t> planes(plane_count * plane_size);
    for (int i = 0; i < l.dims[x]; ++i) {
        for (int j = 0; j < l.dims[y]; ++j) {
            auto* plane = planes.data() + (i * l.dims[y] + j) * plane_size;
            const auto rest = i * l.strides[x] + j * l.strides[y];
            for (std::size_t r = 0; r < rows; ++r) {
                const auto row = rest + cut.row_offsets[r];
                for (std::size_t c = 0; c < cols; ++c) {
                    plane[r * words + c / 64] |=
                        std::uint64_t{input[row + cut.col_offsets[c]]} << (c % 64);
                }
            }
        }
    }
    std::vector<std::uint64_t> matrix(rows * words);
    std::vector<unsigned> table((nx - 1) * (ny - 1));
    for (unsigned u = 1; u < nx; ++u) {
        for (unsigned v = 1; v < ny; ++v) {
            unsigned mask = 0;
            for (int i = 0; i < l.dims[x]; ++i) {
                if (u & (1U << i)) {
                    mask |= v << (i * l.dims[y]);
                }
            }
            const auto first_plane = std::countr_zero(mask);
            const auto* plane = planes.data() + first_plane * plane_size;
            std::copy_n(plane, plane_size, matrix.begin());
            mask &= mask - 1;
            while (mask) {
                plane = planes.data() + std::countr_zero(mask) * plane_size;
                for (std::size_t i = 0; i < plane_size; ++i) {
                    matrix[i] ^= plane[i];
                }
                mask &= mask - 1;
            }
            table[(u - 1) * (ny - 1) + v - 1] = binary_rank(matrix, rows, cols, words);
        }
    }
    return table;
}

struct Pair {
    int x;
    int y;
    std::size_t columns;
    std::vector<std::uint8_t> allowed;

    bool has(int i, int j) const {
        return allowed[i * columns + j] != 0;
    }
};

static Pair restrictions(const Layout& l, int x, int y, const Tensor& a,
                         const Tensor& b, const std::vector<std::vector<Matrix>>& groups,
                         const Domains& domains, int split) {
    const auto cut = pair_cut(l, x, y, split);
    const auto ra = rank_table(l, x, y, cut, a);
    const auto rb = rank_table(l, x, y, cut, b);
    const unsigned nx = (1U << l.dims[x]) - 1;
    const unsigned ny = (1U << l.dims[y]) - 1;
    const auto width = groups[y].size();
    Pair pair{x, y, width, std::vector<std::uint8_t>(groups[x].size() * width)};
    auto ha = ra;
    auto hb = rb;
    std::sort(ha.begin(), ha.end());
    std::sort(hb.begin(), hb.end());
    if (ha != hb) {
        return pair;
    }
    for (int i : domains[x]) {
        const auto& left = groups[x][i].pullback;
        for (int j : domains[y]) {
            const auto& right = groups[y][j].pullback;
            bool ok = true;
            for (unsigned u = 1; ok && u <= nx; ++u) {
                for (unsigned v = 1; v <= ny; ++v) {
                    if (ra[(left[u] - 1) * ny + right[v] - 1] != rb[(u - 1) * ny + v - 1]) {
                        ok = false;
                        break;
                    }
                }
            }
            pair.allowed[i * width + j] = ok;
        }
    }
    return pair;
}

static bool propagate(Domains& domains, const std::vector<Pair>& constraints) {
    bool changed;
    do {
        changed = false;
        for (const auto& pair : constraints) {
            auto& x = domains[pair.x];
            auto& y = domains[pair.y];
            const auto before = x.size() + y.size();
            std::erase_if(x, [&](int i) {
                return std::none_of(y.begin(), y.end(), [&](int j) { return pair.has(i, j); });
            });
            std::erase_if(y, [&](int j) {
                return std::none_of(x.begin(), x.end(), [&](int i) { return pair.has(i, j); });
            });
            if (x.empty() || y.empty()) {
                return false;
            }
            changed |= before != x.size() + y.size();
        }
    } while (changed);
    return true;
}

static int grouped_restrictions(const Layout& l, const Tensor& a, const Tensor& b,
                                 const std::vector<std::vector<Matrix>>& changes,
                                 Domains& domains, bool half, Clock::time_point stop) {
    const auto d = static_cast<int>(l.dims.size());
    const std::array<int, 3> counts = half
        ? std::array<int, 3>{d / 2, d - d / 2 - 1, 1}
        : std::array<int, 3>{d / 3, (d + 1) / 3, (d + 2) / 3};
    std::array<std::vector<int>, 3> axes;
    int next = 0;
    for (int group = 0; group < 3; ++group) {
        for (int i = 0; i < counts[group]; ++i) {
            axes[group].push_back(next++);
        }
    }
    for (int group = 0; group < 3; ++group) {
        const auto& active = axes[group];
        const auto row_offsets = l.offsets(axes[(group + 1) % 3]);
        const auto col_offsets = l.offsets(axes[(group + 2) % 3]);
        const auto rows = row_offsets.size();
        const auto cols = col_offsets.size();
        const auto words = (cols + 63) / 64;
        std::size_t points = 1;
        std::vector<unsigned> radix;
        for (int axis : active) {
            radix.push_back((1U << l.dims[axis]) - 1);
            points *= radix.back();
        }
        // Skip this optional invariant when its explicit evaluation would be large.
        if (points > 1000000 || points * rows * cols > 10000000) {
            continue;
        }
        const auto rank_count = std::min(rows, cols) + 1;
        std::array<std::vector<std::vector<unsigned>>, 2> counts_by_rank;
        for (auto& hist : counts_by_rank) {
            for (unsigned n : radix) {
                hist.emplace_back(n * rank_count, 0);
            }
        }
        std::vector<std::uint64_t> ma(rows * words), mb(rows * words);
        std::vector<unsigned> selected(active.size());
        std::vector<std::size_t> weights;
        std::vector<std::size_t> expanded;
        for (std::size_t point = 0; point < points; ++point) {
            if ((point & 63) == 0 && Clock::now() >= stop) {
                return -1;
            }
            std::size_t digits = point;
            weights.assign(1, 0);
            for (std::size_t j = 0; j < active.size(); ++j) {
                selected[j] = static_cast<unsigned>(digits % radix[j]);
                digits /= radix[j];
                const auto stride = l.strides[active[j]];
                expanded.clear();
                for (unsigned mask = selected[j] + 1; mask; mask &= mask - 1) {
                    const auto offset = std::countr_zero(mask) * stride;
                    for (auto weight : weights) {
                        expanded.push_back(weight + offset);
                    }
                }
                weights.swap(expanded);
            }
            std::fill(ma.begin(), ma.end(), 0);
            std::fill(mb.begin(), mb.end(), 0);
            for (std::size_t r = 0; r < rows; ++r) {
                for (std::size_t c = 0; c < cols; ++c) {
                    const auto base = row_offsets[r] + col_offsets[c];
                    std::uint64_t x = 0, y = 0;
                    for (auto offset : weights) {
                        x ^= a[base + offset];
                        y ^= b[base + offset];
                    }
                    ma[r * words + c / 64] |= x << (c % 64);
                    mb[r * words + c / 64] |= y << (c % 64);
                }
            }
            const auto ar = binary_rank(ma, rows, cols, words);
            const auto br = binary_rank(mb, rows, cols, words);
            for (std::size_t j = 0; j < active.size(); ++j) {
                const auto bin = rank_count * selected[j];
                ++counts_by_rank[0][j][bin + ar];
                ++counts_by_rank[1][j][bin + br];
            }
        }
        for (std::size_t j = 0; j < active.size(); ++j) {
            const int axis = active[j];
            const auto& ha = counts_by_rank[0][j];
            const auto& hb = counts_by_rank[1][j];
            std::erase_if(domains[axis], [&](int k) {
                const auto& g = changes[axis][k].pullback;
                for (unsigned u = 1; u <= radix[j]; ++u) {
                    auto src = ha.begin() + (g[u] - 1) * rank_count;
                    auto dst = hb.begin() + (u - 1) * rank_count;
                    if (!std::equal(src, src + rank_count, dst)) {
                        return true;
                    }
                }
                return false;
            });
            if (domains[axis].empty()) {
                return false;
            }
        }
    }
    return true;
}

struct Answer {
    const char* result = "no";
    double rank_ms = 0;
    double search_ms = 0;
    std::uint64_t nodes = 0;
    std::vector<int> witness;
    std::vector<std::size_t> domain_sizes;
};

static Answer solve(const Layout& l, const Tensor& a, const Tensor& b, bool prune,
                    int budget_ms, int grouping) {
    auto start = Clock::now();
    const auto stop = start + std::chrono::milliseconds(budget_ms);
    const auto d = static_cast<int>(l.dims.size());
    std::vector<std::vector<Matrix>> groups;
    Domains domains(d);
    for (int axis = 0; axis < d; ++axis) {
        groups.push_back(changes(l.dims[axis]));
        domains[axis].resize(groups.back().size());
        std::iota(domains[axis].begin(), domains[axis].end(), 0);
    }
    Answer answer;
    if (a == b) {
        answer.result = "yes";
        for (int axis = 0; axis < d; ++axis) {
            const auto& group = groups[axis];
            const auto found = std::find_if(group.begin(), group.end(), [&](const Matrix& m) {
                for (int i = 0; i < l.dims[axis]; ++i) {
                    if (m.rows[i] != (1U << i)) {
                        return false;
                    }
                }
                return true;
            });
            answer.witness.push_back(static_cast<int>(found - group.begin()));
        }
    }
    if (grouping && answer.witness.empty()) {
        int outcome = grouped_restrictions(l, a, b, groups, domains, grouping == 2, stop);
        if (outcome <= 0) {
            answer.result = outcome < 0 ? "timeout" : "no";
            answer.rank_ms = milliseconds(start);
            return answer;
        }
    }
    std::vector<Pair> constraints;
    if (prune && answer.witness.empty()) {
        bool determined = false;
        for (int split = 0; split < 2 && !determined; ++split) {
            for (int x = 0; x < d && !determined; ++x) {
                for (int y = x + 1; y < d && !determined; ++y) {
                    constraints.push_back(restrictions(l, x, y, a, b, groups, domains, split));
                    if (!propagate(domains, constraints)) {
                        answer.rank_ms = milliseconds(start);
                        return answer;
                    }
                    if (Clock::now() >= stop) {
                        answer.result = "timeout";
                        answer.rank_ms = milliseconds(start);
                        return answer;
                    }
                    determined = std::all_of(domains.begin(), domains.end(), [](const auto& x) {
                        return x.size() == 1;
                    });
                }
            }
        }
    }
    answer.rank_ms = milliseconds(start);
    for (const auto& domain : domains) {
        answer.domain_sizes.push_back(domain.size());
    }
    const auto search_start = Clock::now();
    if (answer.witness.empty()) {
        std::vector<int> chosen(d, -1);
        std::vector<int> order(d);
        std::iota(order.begin(), order.end(), 0);
        std::stable_sort(order.begin(), order.end(), [&](int x, int y) {
            return domains[x].size() < domains[y].size();
        });
        std::vector<Tensor> buffer(d, Tensor(l.size));
        buffer[0] = a;
        bool timeout = false;
        const auto visit = [&](auto&& self, int depth) -> bool {
            if ((answer.nodes++ & 127) == 0 && Clock::now() >= stop) {
                timeout = true;
                return false;
            }
            const int axis = order[depth];
            for (int i : domains[axis]) {
                bool compatible = true;
                for (const auto& pair : constraints) {
                    if (pair.x == axis && chosen[pair.y] >= 0 &&
                        !pair.has(i, chosen[pair.y])) {
                        compatible = false;
                        break;
                    }
                    if (pair.y == axis && chosen[pair.x] >= 0 &&
                        !pair.has(chosen[pair.x], i)) {
                        compatible = false;
                        break;
                    }
                }
                if (!compatible) {
                    continue;
                }
                chosen[axis] = i;
                const auto& matrix = groups[axis][i];
                if (depth + 1 == d) {
                    if (match_last(l, axis, matrix, buffer[depth], b)) {
                        return true;
                    }
                } else {
                    apply(l, axis, matrix, buffer[depth], buffer[depth + 1]);
                    if (self(self, depth + 1)) {
                        return true;
                    }
                    if (timeout) {
                        return false;
                    }
                }
                chosen[axis] = -1;
            }
            return false;
        };
        if (visit(visit, 0)) {
            answer.result = "yes";
            answer.witness = std::move(chosen);
        } else if (timeout) {
            answer.result = "timeout";
        }
    }
    for (int axis = 0; axis < static_cast<int>(answer.witness.size()); ++axis) {
        unsigned packed = 0;
        const auto& matrix = groups[axis][answer.witness[axis]];
        for (int i = 0; i < l.dims[axis]; ++i) {
            packed |= matrix.rows[i] << (i * l.dims[axis]);
        }
        answer.witness[axis] = static_cast<int>(packed);
    }
    answer.search_ms = milliseconds(search_start);
    return answer;
}

template <class Item>
static void array_json(const std::vector<Item>& values) {
    std::cout << '[';
    for (std::size_t i = 0; i < values.size(); ++i) {
        if (i) {
            std::cout << ',';
        }
        std::cout << values[i];
    }
    std::cout << ']';
}

int main(int argc, char* argv[]) try {
    bool prune = true;
    int budget_ms = 2000;
    int grouping = 0;
    for (int i = 1; i < argc; ++i) {
        const std::string arg = argv[i];
        if (arg == "--direct") {
            prune = false;
        } else if (arg == "--grouped" && i + 1 < argc) {
            const std::string layout = argv[++i];
            if (layout != "balanced" && layout != "half") {
                throw std::runtime_error("Expected grouped layout balanced or half");
            }
            grouping = layout == "balanced" ? 1 : 2;
            prune = false;
        } else if (arg == "--budget" && i + 1 < argc) {
            budget_ms = std::stoi(argv[++i]);
        } else {
            throw std::runtime_error("Usage: native_ti [--direct|--grouped balanced|--grouped half] [--budget milliseconds]");
        }
    }
    if (budget_ms < 1) {
        throw std::runtime_error("Budget must be positive");
    }
    int order;
    while (std::cin >> order) {
        int prime;
        if (!(std::cin >> prime) || prime != 2 || order < 3 || order > 20) {
            throw std::runtime_error("Expected order in 3..20 and prime 2");
        }
        std::vector<int> dims(order);
        for (auto& side : dims) {
            if (!(std::cin >> side)) {
                throw std::runtime_error("Missing side length");
            }
        }
        const Layout layout(dims);
        Tensor a(layout.size);
        Tensor b(layout.size);
        for (auto* tensor : {&a, &b}) {
            for (auto& value : *tensor) {
                int entry;
                if (!(std::cin >> entry) || (entry != 0 && entry != 1)) {
                    throw std::runtime_error("Missing or nonbinary input coefficient");
                }
                value = static_cast<std::uint8_t>(entry);
            }
        }
        const auto answer = solve(layout, a, b, prune, budget_ms, grouping);
        std::cout << "{\"result\":\"" << answer.result << "\",\"rank_ms\":" << answer.rank_ms
                  << ",\"search_ms\":" << answer.search_ms << ",\"nodes\":" << answer.nodes
                  << ",\"domains\":";
        array_json(answer.domain_sizes);
        std::cout << ",\"witness\":";
        array_json(answer.witness);
        std::cout << "}\n";
    }
    return 0;
} catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 1;
}
