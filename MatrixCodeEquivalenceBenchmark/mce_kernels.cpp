#include <algorithm>
#include <cstdint>
#include <vector>

#ifdef _WIN32
#define MCE_API extern "C" __declspec(dllexport)
#else
#define MCE_API extern "C" __attribute__((visibility("default")))
#endif

static int invert(int x, int p) {
    std::int64_t a = x, y = 1;
    for (int j = p - 2; j; j >>= 1) {
        if (j & 1) y = y * a % p;
        a = a * a % p;
    }
    return static_cast<int>(y);
}

template<int Fixed>
static void rank_words(int p, int k, int m, int n, int count,
                       const std::int64_t* code, const std::int64_t* points,
                       std::int16_t* output) {
    if constexpr (Fixed != 0) p = Fixed;
    const int size = m * n;
    std::vector<int> a(size);
    std::vector<std::int64_t> raw(size);
    std::vector<int> inverses(p);
    for (int j = 1; j < p; ++j) inverses[j] = invert(j, p);
    for (int row = 0; row < count; ++row) {
        std::fill(raw.begin(), raw.end(), 0);
        const auto* vector = points + static_cast<std::size_t>(row) * k;
        for (int v = 0; v < k; ++v) {
            const auto coefficient = vector[v];
            if (!coefficient) continue;
            const auto* src = code + static_cast<std::size_t>(v) * size;
            for (int i = 0; i < size; ++i) raw[i] += coefficient * src[i];
        }
        for (int i = 0; i < size; ++i) a[i] = static_cast<int>(raw[i] % p);
        int r = 0;
        for (int c = 0; c < n && r < m; ++c) {
            int pivot = r;
            while (pivot < m && a[pivot * n + c] == 0) ++pivot;
            if (pivot == m) continue;
            auto* lead = a.data() + r * n;
            if (pivot != r) std::swap_ranges(lead + c, lead + n, a.data() + pivot * n + c);
            const auto inv = inverses[lead[c]];
            for (int i = r + 1; i < m; ++i) {
                auto* dest = a.data() + i * n;
                const int factor = static_cast<int>(std::int64_t{dest[c]} * inv % p);
                if (!factor) continue;
                for (int j = c; j < n; ++j) {
                    const auto value = dest[j] - std::int64_t{factor} * lead[j];
                    dest[j] = static_cast<int>((value + std::int64_t{p} * p) % p);
                }
            }
            ++r;
        }
        output[row] = static_cast<std::int16_t>(r);
    }
}

MCE_API void mce_rank_words(int p, int k, int m, int n, int count,
                             const std::int64_t* code, const std::int64_t* points,
                             std::int16_t* output) {
    switch (p) {
        case 2: rank_words<2>(p, k, m, n, count, code, points, output); break;
        case 3: rank_words<3>(p, k, m, n, count, code, points, output); break;
        case 5: rank_words<5>(p, k, m, n, count, code, points, output); break;
        case 7: rank_words<7>(p, k, m, n, count, code, points, output); break;
        case 13: rank_words<13>(p, k, m, n, count, code, points, output); break;
        default: rank_words<0>(p, k, m, n, count, code, points, output); break;
    }
}

template<int Fixed>
static int reduce(int p, int rows, int cols, int limit, std::int64_t* a, int* pivots) {
    if constexpr (Fixed != 0) p = Fixed;
    int rank = 0;
    const std::int64_t base = std::int64_t{p} * p;
    for (int j = 0; j < limit && rank < rows; ++j) {
        int q = rank;
        while (q < rows && a[static_cast<std::size_t>(q) * cols + j] == 0) ++q;
        if (q == rows) continue;
        auto* lead = a + static_cast<std::size_t>(rank) * cols;
        if (q != rank) std::swap_ranges(lead + j, lead + cols, a + static_cast<std::size_t>(q) * cols + j);
        const int inv = invert(static_cast<int>(lead[j]), p);
        if (inv != 1) {
            for (int c = j; c < cols; ++c) lead[c] = lead[c] * inv % p;
        }
        for (int r = 0; r < rows; ++r) {
            if (r == rank) continue;
            auto* dest = a + static_cast<std::size_t>(r) * cols;
            const auto scale = dest[j];
            if (!scale) continue;
            for (int c = j; c < cols; ++c) {
                if constexpr (Fixed == 2) dest[c] ^= lead[c];
                else dest[c] = (dest[c] - scale * lead[c] + base) % p;
            }
        }
        pivots[rank++] = j;
    }
    return rank;
}

MCE_API int mce_rref(int p, int rows, int cols, int limit, std::int64_t* a, int* pivots) {
    switch (p) {
        case 2: return reduce<2>(p, rows, cols, limit, a, pivots);
        case 3: return reduce<3>(p, rows, cols, limit, a, pivots);
        case 5: return reduce<5>(p, rows, cols, limit, a, pivots);
        case 7: return reduce<7>(p, rows, cols, limit, a, pivots);
        case 13: return reduce<13>(p, rows, cols, limit, a, pivots);
        default: return reduce<0>(p, rows, cols, limit, a, pivots);
    }
}
