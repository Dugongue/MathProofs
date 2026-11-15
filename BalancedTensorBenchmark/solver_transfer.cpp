#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

// Independent benchmark of the covariant-then-verify method over F_2.
using Bits = std::vector<std::uint64_t>;
using Choice = std::vector<int>;
using Domains = std::vector<Choice>;
using Clock = std::chrono::steady_clock;

constexpr std::array<std::array<int, 2>, 6> maps{{
    {1, 2}, {1, 3}, {2, 1}, {2, 3}, {3, 1}, {3, 2}
}};

int image(int map, int covector) {
    if (covector < 3) {
        return maps[map][covector - 1];
    }
    return maps[map][0] ^ maps[map][1];
}

int inverse(int map) {
    for (int candidate = 0; candidate < 6; ++candidate) {
        if (image(map, image(candidate, 1)) == 1 &&
            image(map, image(candidate, 2)) == 2) {
            return candidate;
        }
    }
    throw std::logic_error("Invalid local map");
}

struct LocalActions {
    int order;
    std::vector<std::uint64_t> masks;

    explicit LocalActions(int order) : order(order), masks(order, 0) {
        for (int axis = 0; axis < order; ++axis) {
            const auto stride = std::size_t{1} << (order - axis - 1);
            if (stride < 64) {
                for (std::size_t bit = 0; bit < 64; ++bit) {
                    if (!(bit & stride)) {
                        masks[axis] |= std::uint64_t{1} << bit;
                    }
                }
            }
        }
    }

    static std::uint64_t select(std::uint64_t low, std::uint64_t high, int which) {
        switch (which) {
            case 1: return low;
            case 2: return high;
            default: return low ^ high;
        }
    }

    void apply(const Bits& source, int axis, int map, Bits& target) const {
        const auto stride = std::size_t{1} << (order - axis - 1);
        const auto [choose_low, choose_high] = maps[map];
        if (stride < 64) {
            const std::uint64_t mask = masks[axis];
            for (std::size_t word = 0; word < source.size(); ++word) {
                const auto low = source[word] & mask;
                const auto high = (source[word] >> stride) & mask;
                target[word] = select(low, high, choose_low) |
                    (select(low, high, choose_high) << stride);
            }
        } else {
            const auto width = stride / 64;
            for (std::size_t block = 0; block < source.size(); block += 2 * width) {
                for (std::size_t j = block; j < block + width; ++j) {
                    const auto low = source[j];
                    const auto high = source[j + width];
                    target[j] = select(low, high, choose_low);
                    target[j + width] = select(low, high, choose_high);
                }
            }
        }
    }

    bool verifies(const Bits& source, const Bits& target, const Choice& witness) const {
        Bits current = source;
        Bits scratch(source.size());
        for (int axis = 0; axis < order; ++axis) {
            apply(current, axis, witness[axis], scratch);
            current.swap(scratch);
        }
        return current == target;
    }
};

std::vector<std::array<std::size_t, 3>> covector_counts(const Bits& tensor, int order) {
    std::vector<std::uint8_t> grid(std::size_t{1} << order);
    for (std::size_t i = 0; i < grid.size(); ++i) {
        grid[i] = (tensor[i / 64] >> (i % 64)) & 1;
    }
    std::vector<std::uint8_t> next;
    std::size_t stride = 1;
    // Along each axis, add the evaluation at the sum of its two basis covectors.
    for (int axis = order - 1; axis >= 0; --axis) {
        const std::size_t groups = grid.size() / (2 * stride);
        next.resize(3 * stride * groups);
        for (std::size_t group = 0; group < groups; ++group) {
            const auto from = group * 2 * stride;
            const auto to = group * 3 * stride;
            std::copy_n(grid.begin() + from, 2 * stride, next.begin() + to);
            for (std::size_t j = 0; j < stride; ++j) {
                next[to + 2 * stride + j] = grid[from + j] ^ grid[from + stride + j];
            }
        }
        grid.swap(next);
        stride *= 3;
    }
    std::vector<std::array<std::size_t, 3>> result(order);
    // Compute each marginal while summing away that axis. Every step sees a
    // third as many entries, and all remaining marginals are preserved.
    std::vector<std::uint32_t> sums(grid.size() / 3);
    auto& last = result.back();
    for (std::size_t i = 0; i < sums.size(); ++i) {
        const auto a = grid[3 * i];
        const auto b = grid[3 * i + 1];
        const auto c = grid[3 * i + 2];
        last[0] += a;
        last[1] += b;
        last[2] += c;
        sums[i] = a + b + c;
    }
    std::size_t size = sums.size();
    for (int axis = order - 2; axis >= 0; --axis) {
        size /= 3;
        auto& counts = result[axis];
        for (std::size_t i = 0; i < size; ++i) {
            const auto a = sums[3 * i];
            const auto b = sums[3 * i + 1];
            const auto c = sums[3 * i + 2];
            counts[0] += a;
            counts[1] += b;
            counts[2] += c;
            sums[i] = a + b + c;
        }
    }
    return result;
}

Domains allowed_maps(const Bits& source, const Bits& target, int order, bool signature) {
    Domains domains(order);
    if (!signature) {
        for (auto& domain : domains) {
            domain = {0, 1, 2, 3, 4, 5};
        }
        return domains;
    }
    const auto left = covector_counts(source, order);
    const auto right = covector_counts(target, order);
    for (int axis = 0; axis < order; ++axis) {
        for (int map = 0; map < 6; ++map) {
            bool matches = true;
            for (int covector = 1; covector <= 3; ++covector) {
                matches &= left[axis][image(map, covector) - 1] == right[axis][covector - 1];
            }
            if (matches) {
                domains[axis].push_back(map);
            }
        }
    }
    return domains;
}

struct BitHash {
    std::size_t operator()(const Bits& values) const {
        std::size_t hash = 0;
        for (auto word : values) {
            hash ^= std::hash<std::uint64_t>{}(word) + 0x9e3779b97f4a7c15ULL +
                (hash << 6) + (hash >> 2);
        }
        return hash;
    }
};

template<class Callback>
bool enumerate(
    const Bits& tensor, const Domains& domains, const std::vector<int>& axes,
    const LocalActions& action, bool invert, Callback&& callback
) {
    std::vector<Bits> states(axes.size() + 1, Bits(tensor.size()));
    states[0] = tensor;
    const auto walk = [&](const auto& recurse, std::size_t level, std::uint64_t code) -> bool {
        if (level == axes.size()) {
            return callback(states[level], code);
        }
        const int axis = axes[level];
        for (const int map : domains[axis]) {
            action.apply(states[level], axis, invert ? inverse(map) : map, states[level + 1]);
            if (recurse(recurse, level + 1, code * 6 + map)) {
                return true;
            }
        }
        return false;
    };
    return walk(walk, 0, 0);
}

void decode(std::uint64_t code, const std::vector<int>& axes, Choice& witness) {
    for (auto axis = axes.rbegin(); axis != axes.rend(); ++axis) {
        witness[*axis] = code % 6;
        code /= 6;
    }
}

struct Result {
    std::string status;
    Choice witness;
    std::size_t left_states = 0;
    std::size_t right_states = 0;
    std::vector<std::size_t> domain_sizes;
    long long feature_ns = 0;
};

Result solve(const Bits& source, const Bits& target, int order, bool signature, std::size_t table_limit) {
    const LocalActions action(order);
    Result result;
    if (source == target) {
        result.status = "yes";
        result.witness.assign(order, 0);
        return result;
    }
    result.status = "no";
    const auto feature_start = Clock::now();
    const auto domains = allowed_maps(source, target, order, signature);
    result.feature_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(
        Clock::now() - feature_start).count();
    for (auto& domain : domains) {
        result.domain_sizes.push_back(domain.size());
    }
    if (std::ranges::find(result.domain_sizes, 0) != result.domain_sizes.end()) {
        return result;
    }

    // Greedily balance the number of candidate maps across both sides.
    std::array<std::vector<int>, 2> halves;
    std::array<std::uint64_t, 2> count{1, 1};
    std::vector<int> axis_order(order);
    std::iota(axis_order.begin(), axis_order.end(), 0);
    std::stable_sort(axis_order.begin(), axis_order.end(), [&](int a, int b) {
        return domains[a].size() > domains[b].size();
    });
    for (const int axis : axis_order) {
        const int half = count[0] <= count[1] ? 0 : 1;
        halves[half].push_back(axis);
        count[half] *= domains[axis].size();
    }
    if (count[0] > count[1]) {
        std::swap(count[0], count[1]);
        std::swap(halves[0], halves[1]);
    }
    if (count[0] > table_limit / (source.size() * sizeof(std::uint64_t) + 128)) {
        result.status = "budget-exhausted";
        return result;
    }
    std::unordered_map<Bits, std::uint64_t, BitHash> left;
    left.reserve(count[0]);
    enumerate(source, domains, halves[0], action, false, [&](const Bits& value, std::uint64_t code) {
        ++result.left_states;
        left.try_emplace(value, code);
        return false;
    });
    enumerate(target, domains, halves[1], action, true, [&](const Bits& value, std::uint64_t code) {
        ++result.right_states;
        const auto match = left.find(value);
        if (match == left.end()) {
            return false;
        }
        result.witness.resize(order);
        decode(match->second, halves[0], result.witness);
        decode(code, halves[1], result.witness);
        if (!action.verifies(source, target, result.witness)) {
            throw std::logic_error("Packed witness verification failed");
        }
        result.status = "yes";
        return true;
    });
    return result;
}

Bits read_tensor(int order) {
    const auto coefficients = std::size_t{1} << order;
    Bits value((coefficients + 63) / 64);
    for (std::size_t i = 0; i < coefficients; ++i) {
        int coefficient;
        if (!(std::cin >> coefficient) || (coefficient != 0 && coefficient != 1)) {
            throw std::runtime_error("Expected 2^d coefficients in {0,1} for each tensor");
        }
        value[i / 64] |= static_cast<std::uint64_t>(coefficient) << (i % 64);
    }
    return value;
}

template<class T>
void print_array(const std::vector<T>& values) {
    std::cout << '[';
    bool comma = false;
    for (const T value : values) {
        if (comma) {
            std::cout << ',';
        }
        std::cout << value;
        comma = true;
    }
    std::cout << ']';
}

int main(int argc, char** argv) {
    try {
        std::ios::sync_with_stdio(false);
        std::cin.tie(nullptr);
        bool signature = true;
        int repeat = 1;
        std::size_t table_limit = 128 * 1024 * 1024;
        for (int i = 1; i < argc; ++i) {
            const std::string arg = argv[i];
            if (arg == "--signature") {
                signature = true;
            } else if (arg == "--mitm") {
                signature = false;
            } else if (arg == "--repeat" && i + 1 < argc) {
                repeat = std::stoi(argv[++i]);
            } else if (arg == "--max-table-mib" && i + 1 < argc) {
                table_limit = std::stoull(argv[++i]) * 1024 * 1024;
            } else {
                throw std::runtime_error("Expected --signature or --mitm, optional --repeat N and --max-table-mib N");
            }
        }
        int order;
        while (std::cin >> order) {
            int field;
            if (!(std::cin >> field) || order < 1 || repeat < 1) {
                throw std::runtime_error("Expected valid tensor order, field and repeat count");
            }
            if (field != 2 || order > 14) {
                std::cout << "{\"status\":\"unsupported\"}\n";
                return 0;
            }
            for (int axis = 0; axis < order; ++axis) {
                int side;
                if (!(std::cin >> side)) {
                    throw std::runtime_error("Expected a side length for each tensor mode");
                }
                if (side != 2) {
                    std::cout << "{\"status\":\"unsupported\"}\n";
                    return 0;
                }
            }
            const auto source = read_tensor(order);
            const auto target = read_tensor(order);
            std::vector<long long> solve_ns;
            std::vector<long long> feature_ns;
            Result result;
            for (int i = 0; i < repeat; ++i) {
                const auto start = Clock::now();
                result = solve(source, target, order, signature, table_limit);
                solve_ns.push_back(std::chrono::duration_cast<std::chrono::nanoseconds>(
                    Clock::now() - start).count());
                feature_ns.push_back(result.feature_ns);
            }
            std::cout << "{\"status\":\"" << result.status << "\",\"solve_ns\":";
            print_array(solve_ns);
            std::cout << ",\"feature_ns\":";
            print_array(feature_ns);
            std::cout << ",\"domains\":";
            print_array(result.domain_sizes);
            std::cout << ",\"witness\":";
            print_array(result.witness);
            std::cout << ",\"left_states\":" << result.left_states <<
                ",\"right_states\":" << result.right_states << "}" << std::endl;
        }
        return 0;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
