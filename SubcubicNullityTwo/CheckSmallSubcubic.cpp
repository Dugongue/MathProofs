#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <numeric>
#include <stdexcept>
#include <vector>

using Mask = std::uint32_t;
struct Graph {
  int n;
  std::array<std::uint8_t, 8> adj{};
};

std::vector<std::array<int, 2>> edges_for(int n) {
  std::vector<std::array<int, 2>> edges;
  for (int u = 0; u < n; ++u)
    for (int v = u + 1; v < n; ++v) edges.push_back({u, v});
  return edges;
}

Graph decode(int n, Mask mask) {
  Graph g{n};
  const auto edges = edges_for(n);
  for (std::size_t j = 0; j < edges.size(); ++j) if ((mask >> j) & 1) {
    auto [u, v] = edges[j];
    g.adj[u] |= 1 << v;
    g.adj[v] |= 1 << u;
  }
  return g;
}

std::vector<Graph> representatives(int n, int split) {
  const auto edges = edges_for(n);
  std::vector<std::vector<std::array<int, 2>>> swaps;
  for (int a = 0; a + 1 < n; ++a) if (a + 1 != split) {
    const int b = a + 1;
    std::vector<std::array<int, 2>> bit_swaps;
    for (int i = 0; i < static_cast<int>(edges.size()); ++i) {
      auto e = edges[i];
      for (int &v : e) {
        if (v == a) v = b;
        else if (v == b) v = a;
      }
      if (e[0] > e[1]) std::swap(e[0], e[1]);
      const int j = std::find(edges.begin(), edges.end(), e) - edges.begin();
      if (j > i) bit_swaps.push_back({i, j});
    }
    swaps.push_back(bit_swaps);
  }
  const Mask count = Mask(1) << edges.size();
  std::vector<bool> seen(count);
  std::vector<Graph> result;
  for (Mask m = 0; m < count; ++m) if (!seen[m]) {
    result.push_back(decode(n, m));
    std::vector<Mask> pending{m};
    seen[m] = true;
    for (std::size_t k = 0; k < pending.size(); ++k) {
      for (const auto &bit_swaps : swaps) {
        Mask image = pending[k];
        for (auto [i, j] : bit_swaps) {
          Mask diff = ((image >> i) ^ (image >> j)) & 1;
          image ^= (diff << i) | (diff << j);
        }
        if (!seen[image]) {
          seen[image] = true;
          pending.push_back(image);
        }
      }
    }
  }
  return result;
}

std::vector<Graph> representatives_four_plus_four() {
  const auto internal = representatives(4, 0);
  const int n = 8;
  const int split = 4;
  std::vector<Graph> result;
  auto automorphisms = [&](const Graph &g) {
    std::vector<std::array<int, 4>> group;
    std::array<int, 4> p{0, 1, 2, 3};
    do {
      bool preserves = true;
      for (int i = 0; i < 4; ++i)
        for (int j = i + 1; j < 4; ++j)
          if (((g.adj[i] >> j) & 1) != ((g.adj[p[i]] >> p[j]) & 1))
            preserves = false;
      if (preserves) group.push_back(p);
    } while (std::next_permutation(p.begin(), p.end()));
    return group;
  };
  for (const auto &left : internal) for (const auto &right : internal) {
    const auto left_group = automorphisms(left);
    const auto right_group = automorphisms(right);
    std::vector<std::array<int, 16>> generators;
    const std::array<int, 4> identity{0, 1, 2, 3};
    auto add_generator = [&](const std::array<int, 4> &p,
                             const std::array<int, 4> &q) {
      if (p == identity && q == identity) return;
      std::array<int, 16> movement{};
      for (int i = 0; i < 4; ++i)
        for (int j = 0; j < 4; ++j)
          movement[4 * i + j] = 4 * p[i] + q[j];
      generators.push_back(movement);
    };
    for (const auto &p : left_group) add_generator(p, identity);
    for (const auto &q : right_group) add_generator(identity, q);
    std::vector<bool> seen(1 << 16);
    for (Mask m = 0; m < (1 << 16); ++m) if (!seen[m]) {
      Graph g{n};
      for (int i = 0; i < 4; ++i) {
        g.adj[i] = left.adj[i] | (((m >> (4 * i)) & 15) << split);
        g.adj[i + split] = right.adj[i] << split;
      }
      for (int i = 0; i < 4; ++i)
        for (int j = 0; j < 4; ++j)
          if ((m >> (4 * i + j)) & 1) g.adj[j + split] |= 1 << i;
      result.push_back(g);
      std::vector<Mask> pending{m};
      seen[m] = true;
      for (std::size_t k = 0; k < pending.size(); ++k) {
        for (const auto &movement : generators) {
          Mask image = 0;
          Mask bits = pending[k];
          while (bits) {
            image |= 1 << movement[__builtin_ctz(bits)];
            bits &= bits - 1;
          }
          if (!seen[image]) {
            seen[image] = true;
            pending.push_back(image);
          }
        }
      }
    }
  }
  return result;
}

bool connected_subcubic(const Graph &g) {
  std::uint8_t seen = 1;
  for (int u = 0; u < g.n; ++u) {
    if (__builtin_popcount(g.adj[u]) > 3) return false;
  }
  for (int step = 0; step < g.n; ++step)
    for (int u = 0; u < g.n; ++u)
      if ((seen >> u) & 1) seen |= g.adj[u];
  return seen == (1 << g.n) - 1;
}

std::uint64_t hom_count(const Graph &source, const Graph &target,
                       const std::array<int, 8> &order,
                       const std::array<Mask, 8> &allowed) {
  std::array<int, 8> image{};
  auto count = [&](auto self, int pos) -> std::uint64_t {
    if (pos == source.n) return 1;
    const int u = order.at(pos);
    Mask candidates = allowed[u];
    for (int k = 0; k < pos; ++k)
      if (source.adj[u] & (1 << order[k])) candidates &= target.adj[image[k]];
    std::uint64_t result = 0;
    while (candidates) {
      image.at(pos) = __builtin_ctz(candidates);
      candidates &= candidates - 1;
      result += self(self, pos + 1);
    }
    return result;
  };
  return count(count, 0);
}

int main() {
  std::vector<Graph> probes;
  for (int n = 1; n <= 7; ++n)
    for (const auto &g : representatives(n, 0))
      if (connected_subcubic(g)) probes.push_back(g);
  for (auto [n, split, fully_colored] : std::vector<std::array<int, 3>>{
           {1, 0, 0}, {2, 0, 0}, {3, 0, 0}, {4, 0, 0}, {5, 0, 0},
           {6, 0, 0}, {7, 0, 0}, {6, 3, 0}, {7, 3, 0}, {8, 4, 1}}) {
    const auto targets = n == 8 ? representatives_four_plus_four()
                                : representatives(n, split);
    const std::array<std::size_t, 8> uncolored_totals{0, 1, 2, 4, 11, 34, 156, 1044};
    const std::size_t expected_count = !split ? uncolored_totals.at(n)
        : n == 6 ? 1408 : n == 7 ? 20364 : 580656;
    if (targets.size() != expected_count) {
      throw std::runtime_error("Unexpected number of color-isomorphism representatives");
    }
    std::vector<std::vector<int>> unresolved(1);
    unresolved[0].resize(targets.size());
    std::iota(unresolved[0].begin(), unresolved[0].end(), 0);
    int used = 0;
    for (const auto &source : probes) {
      if (unresolved.empty()) break;
      std::array<int, 8> order{};
      std::iota(order.begin(), order.end(), 0);
      std::stable_sort(order.begin(), order.begin() + source.n,
                       [&](int u, int v) {
                        return __builtin_popcount(source.adj[u]) >
                               __builtin_popcount(source.adj[v]);
                       });
      const Mask any = (1 << n) - 1;
      const Mask first = (1 << split) - 1;
      std::array<Mask, 8> allowed;
      allowed.fill(any);
      auto test = [&]() {
        ++used;
        std::vector<std::vector<int>> next;
        for (const auto &same : unresolved) {
          std::map<std::uint64_t, std::vector<int>> parts;
          for (int idx : same)
            parts[hom_count(source, targets[idx], order, allowed)].push_back(idx);
          for (auto &[value, part] : parts)
            if (part.size() > 1) next.push_back(std::move(part));
        }
        unresolved = std::move(next);
      };
      auto color = [&](auto self, int u) -> void {
        if (unresolved.empty()) return;
        if (u == source.n) {
          test();
          return;
        }
        allowed[u] = any;
        self(self, u + 1);
        if (split && (fully_colored || __builtin_popcount(source.adj[u]) <= 2)) {
          allowed[u] = first;
          self(self, u + 1);
          allowed[u] = any ^ first;
          self(self, u + 1);
        }
      };
      color(color, 0);
    }
    std::cout << "n=" << n << " split=" << split
              << " representatives=" << targets.size()
              << " probes_checked=" << used
              << " unresolved_groups=" << unresolved.size() << std::endl;
    if (!unresolved.empty()) return 1;
  }
}
