// Equal-side binary grouped solver. The same exact fallback is used in both
// configurations, allowing the grouping's effect to be measured.
#define main original_native_ti_main
#include "native_ti.cpp"
#undef main

static std::vector<std::vector<unsigned>> covector_tuples(int size) {
    std::vector<std::vector<unsigned>> tuples{{}};
    for (int axis = 0; axis < size; ++axis) {
        std::vector<std::vector<unsigned>> extended;
        extended.reserve(3 * tuples.size());
        for (const auto& prefix : tuples) {
            for (unsigned digit = 1; digit < 4; ++digit) {
                auto next = prefix;
                next.push_back(digit);
                extended.push_back(std::move(next));
            }
        }
        tuples = std::move(extended);
    }
    return tuples;
}

static std::vector<unsigned> profile(
    const Tensor& t, const std::array<int, 3>& counts, int group,
    const std::vector<std::vector<unsigned>>& covectors) {
    const std::array<int, 3> sizes{1 << counts[0], 1 << counts[1], 1 << counts[2]};
    const std::array<int, 3> stride{sizes[1] * sizes[2], sizes[2], 1};
    std::array<int, 2> others{};
    int pointer = 0;
    for (int axis = 0; axis < 3; ++axis) if (axis != group) others[pointer++] = axis;
    const int rows = sizes[others[0]];
    const int cols = sizes[others[1]];
    std::vector<unsigned> result;
    result.reserve(covectors.size());
    std::vector<std::uint64_t> packed(rows);
    for (const auto& tuple : covectors) {
        std::vector<int> support{0};
        for (auto digit : tuple) {
            std::vector<int> extended;
            extended.reserve(2 * support.size());
            for (const auto index : support) {
                if (digit & 1U) extended.push_back(2 * index);
                if (digit & 2U) extended.push_back(2 * index + 1);
            }
            support = std::move(extended);
        }
        std::fill(packed.begin(), packed.end(), 0);
        for (int row = 0; row < rows; ++row) {
            const int row_offset = row * stride[others[0]];
            for (int col = 0; col < cols; ++col) {
                auto offset = row_offset + col * stride[others[1]];
                unsigned bit = 0;
                for (auto x : support) bit ^= t[offset + x * stride[group]];
                packed[row] |= std::uint64_t{bit} << col;
            }
        }
        result.push_back(binary_rank(packed, rows, cols, 1));
    }
    return result;
}

using Histogram = std::array<unsigned, 65>;

static std::vector<int> filter_tuple_maps(
    const std::vector<unsigned>& a, const std::vector<unsigned>& b,
    const std::vector<std::vector<unsigned>>& covectors, const std::vector<Matrix>& matrices,
    bool& multiple) {
    const int size = int(covectors.front().size());
    std::vector<std::array<Histogram, 3>> ha(size), hb(size);
    for (std::size_t p = 0; p < covectors.size(); ++p) {
        for (int local = 0; local < size; ++local) {
            ++ha[local][covectors[p][local] - 1][a[p]];
            ++hb[local][covectors[p][local] - 1][b[p]];
        }
    }
    Domains domains(size);
    for (int local = 0; local < size; ++local) {
        for (std::size_t j = 0; j < matrices.size(); ++j) {
            const auto& map = matrices[j].pullback;
            bool compatible = true;
            for (unsigned digit = 1; digit < 4; ++digit) {
                compatible &= ha[local][map[digit] - 1] == hb[local][digit - 1];
            }
            if (compatible) domains[local].push_back(int(j));
        }
        if (domains[local].empty()) return {};
    }
    std::vector<int> partial(size), first;
    const auto enumerate = [&](auto&& self, int local) -> void {
        if (multiple) return;
        if (local == size) {
            for (std::size_t p = 0; p < covectors.size(); ++p) {
                int mapped = 0;
                for (int k = 0; k < size; ++k) {
                    auto image = matrices[partial[k]].pullback[covectors[p][k]];
                    mapped = 3 * mapped + int(image) - 1;
                }
                if (a[mapped] != b[p]) return;
            }
            if (first.empty()) first = partial;
            else multiple = true;
            return;
        }
        for (int candidate : domains[local]) {
            partial[local] = candidate;
            self(self, local + 1);
            if (multiple) return;
        }
    };
    enumerate(enumerate, 0);
    return first;
}

static Answer solve_grouped(const Layout& l, const Tensor& a, const Tensor& b,
                            const std::array<int,3>& sizes, bool& fallback) {
    const auto start = Clock::now();
    Answer answer;
    const auto matrices = changes(2);
    if (a == b) {
        answer.result = "yes";
        answer.witness.assign(l.dims.size(), 9); // Binary identity packed by rows.
        answer.rank_ms = milliseconds(start);
        return answer;
    }
    std::vector<int> candidates;
    bool has_ambiguity = false;
    for (int pivot = 0; pivot < 3; ++pivot) {
        const auto tuples = covector_tuples(sizes[pivot]);
        const auto pa = profile(a, sizes, pivot, tuples);
        const auto pb = profile(b, sizes, pivot, tuples);
        bool ambiguous = false;
        auto found = filter_tuple_maps(pa, pb, tuples, matrices, ambiguous);
        if (found.empty()) {
            answer.rank_ms = milliseconds(start);
            return answer;
        }
        has_ambiguity |= ambiguous;
        candidates.insert(candidates.end(), found.begin(), found.end());
    }
    const double rank_ms = milliseconds(start);
    if (has_ambiguity) {
        fallback = true;
        auto result = solve(l, a, b, true, 2000, 0);
        result.rank_ms += rank_ms;
        return result;
    }
    answer.rank_ms = rank_ms;
    const auto verify = Clock::now();
    auto current = a;
    auto updated = b;
    for (std::size_t i = 0; i < candidates.size(); ++i) {
        const auto& matrix = matrices[candidates[i]];
        apply(l, int(i), matrix, current, updated);
        std::swap(current, updated);
    }
    if (current == b) {
        answer.result = "yes";
        for (int candidate : candidates) {
            const auto& matrix = matrices[candidate];
            answer.witness.push_back(int(matrix.rows[0] | (matrix.rows[1] << 2)));
        }
    }
    answer.search_ms = milliseconds(verify);
    return answer;
}

int main(int argc, char* argv[]) try {
    if (argc != 2 || (std::string(argv[1]) != "balanced" && std::string(argv[1]) != "half")) {
        throw std::runtime_error("Usage: baseline_group_rank balanced|half");
    }
    std::ios::sync_with_stdio(false);
    const bool balanced = std::string(argv[1]) == "balanced";
    int order, prime;
    while (std::cin >> order >> prime) {
        if (order < 3 || order > 12 || prime != 2) {
            throw std::runtime_error("Expected order 3..12 over GF(2)");
        }
        std::vector<int> dims(order);
        for (int& side : dims) {
            if (!(std::cin >> side) || side != 2) throw std::runtime_error("Expected all sides 2");
        }
        const Layout l(dims);
        Tensor a(l.size), b(l.size);
        for (auto* tensor : {&a, &b}) {
            for (auto& bit : *tensor) {
                int entry;
                if (!(std::cin >> entry) || (entry != 0 && entry != 1)) {
                    throw std::runtime_error("Expected binary coefficient");
                }
                bit = static_cast<std::uint8_t>(entry);
            }
        }
        const auto sizes = balanced ? std::array<int,3>{order/3,(order+1)/3,(order+2)/3}
                                    : std::array<int,3>{order/2,order-order/2-1,1};
        bool fallback = false;
        const auto start = Clock::now();
        auto answer = solve_grouped(l, a, b, sizes, fallback);
        const double wall = milliseconds(start);
        std::cout << "{\"result\":\"" << answer.result << "\",\"group_fallback\":"
                  << (fallback ? "true" : "false") << ",\"rank_ms\":" << answer.rank_ms
                  << ",\"search_ms\":" << answer.search_ms << ",\"backend_ms\":" << wall
                  << ",\"witness\":";
        array_json(answer.witness);
        std::cout << "}\n" << std::flush;
    }
    return 0;
} catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 1;
}
