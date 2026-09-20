#!/usr/bin/env python3

from dataclasses import dataclass
from math import log
from math import log2
from math import ceil
from math import comb
import re

@dataclass
class Param:
  digest_bytes: int
  pub_seed_bytes: int
  sec_seed_bytes: int
  st_seed_bytes: int
  st_salt_bytes: int
  q: int
  n: int
  m: int
  s: int
  t: int
  w: int
  k: int
  seed_tree: bool = True
  hash_opt: bool = False

  _name: str=None

  def __str__(self):
    if self._name:
      return self._name
    else:
      return f"MEDS-{self.pk_size}"

  def __repr__(self):
    return self.name

  @property
  def name(self):
    if self._name:
      return re.sub(r'\W+', '', self._name)
    else:
      return f"MEDS{self.pk_size}"

  @property
  def pk_size(self):
    pub_seed_bytes = self.pub_seed_bytes
    s = self.s
    k = self.k
    m = self.m
    n = self.n
    q = self.q

    q_bits = ceil(log2(q))

    return (s - 1) * ceil(((k-2) * (m*n - k) * ceil(log2(q))) / 8) + pub_seed_bytes

  @property
  def sk_size(self):
    sec_seed_bytes = self.sec_seed_bytes
    s = self.s
    k = self.k
    m = self.m
    n = self.n
    q = self.q

    q_bits = ceil(log2(q))

    def mat_bytes(i, j):
       return ceil(i*j*q_bits/8)

    #return (s-1)*(mat_bytes(m,m) + mat_bytes(n,n)) + sec_seed_bytes + self.pub_seed_bytes
    return (s-1)*(mat_bytes(m,m) + mat_bytes(n,n) + mat_bytes(k,k)) + sec_seed_bytes + self.pub_seed_bytes

  @property
  def fiat_shamir(self):
    return log2(comb(self.t, self.w) * (self.s - 1)**self.w)

  @property
  def seed_tree_cost(self):
    return self.seed_max_tree_len * self.st_seed_bytes

  @property
  def seed_max_tree_len(self):
    st_seed_bytes = self.st_seed_bytes
    t = self.t
    w = self.w

    if self.seed_tree:
      return (2**ceil(log2(w)) + w * (ceil(log2(t)) - ceil(log2(w)) - 1))
    else:
      return t - w


  @property
  def sig_size(self):
    digest_bytes = self.digest_bytes
    m = self.m
    n = self.n
    k = self.k
    q = self.q
    t = self.t
    w = self.w

    q_bits = ceil(log2(q))

    sig_size = digest_bytes + w*ceil(2*k*q_bits/8) + self.seed_tree_cost
    #sig_size = digest_bytes + w*(ceil(m*m*q_bits/8) + ceil(n*n*q_bits/8)) + self.seed_tree_cost

    sig_size += self.st_salt_bytes

    return sig_size

  def dump(self):
    print()

    print(f"digest_bytes   = {self.digest_bytes}")
    print(f"pub_seed_bytes = {self.pub_seed_bytes}")
    print(f"sec_seed_bytes = {self.sec_seed_bytes}")
    print(f"st_seed_bytes  = {self.st_seed_bytes}")
    print(f"st_salt_bytes  = {self.st_salt_bytes}")

    print()

    print(f"q = {self.q:>3}")
    print(f"n = {self.n:>3}")
    print(f"m = {self.m:>3}")
    print(f"s = {self.s:>3}")
    print(f"t = {self.t:>3}")
    print(f"w = {self.w:>3}")
    print(f"k = {self.k:>3}")

    print()

    print(f"seed tree: {self.seed_tree}")

    print()

    print(f"pk size:      {self.pk_size:7}")
    print(f"max sig size: {self.sig_size:7}")
    print(f"sum:          {self.pk_size + self.sig_size:7}")

    print()

    print(f"FS security:   {self.fiat_shamir:12.5f}")

    print()

  def opt_perf(self, max_t = 1024):
    pick = (999999999, 0, 0)

    for t in range(64, max_t, 16):
      for w in range(1, t):
        self.t = t
        self.w = w

        if self.fiat_shamir > (self.st_seed_bytes << 3):
          #print(t, w, self.sig_size)

          if self.sig_size < pick[0]:
            pick = self.sig_size, t, w

          break

      self.t = pick[1]
      self.w = pick[2]

    self.dump()


params = [
## old parameter sets
# old Level I
  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 128 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 14,
        n = 15,
        k = 14,
        s = 4,
        t = 1152,
        w = 14,
        seed_tree = True,
        _name = "oldlevel1-9923"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 128 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 15,
        n = 16,
        k = 15,
        s = 4,
        t = 1152,
        w = 14,
        seed_tree = True,
        _name = "oldlevel1-9923-1"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 128 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 15,
        n = 16,
        k = 15,
        s = 2,
        t = 256,
        w = 30,
        seed_tree = True,
        _name = "oldlevel1-9923-2"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 128 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 14,
        n = 15,
        k = 14,
        s = 5,
        t = 192,
        w = 20,
        seed_tree = True,
        _name = "oldlevel1-13220"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 128 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 15,
        n = 16,
        k = 15,
        s = 5,
        t = 192,
        w = 20,
        seed_tree = True,
        _name = "oldlevel1-13220-2"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 128 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 15,
        n = 16,
        k = 15,
        s = 2,
        t = 144,
        w = 48,
        seed_tree = True,
        _name = "oldlevel1-13220-3"),

# old Level III

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 192 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 22,
        n = 23,
        k = 22,
        s = 4,
        t = 608,
        w = 26,
        seed_tree = True,
        _name = "oldlevel3-41711"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 192 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 23,
        n = 24,
        k = 23,
        s = 4,
        t = 608,
        w = 26,
        seed_tree = True,
        _name = "oldlevel3-41711-1"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 192 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 23,
        n = 24,
        k = 23,
        s = 3,
        t = 480,
        w = 31,
        seed_tree = True,
        _name = "oldlevel3-41711-2"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 192 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 22,
        n = 23,
        k = 22,
        s = 5,
        t = 160,
        w = 36,
        seed_tree = True,
        _name = "oldlevel3-55604"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 192 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 23,
        n = 24,
        k = 23,
        s = 5,
        t = 160,
        w = 36,
        seed_tree = True,
        _name = "oldlevel3-55604-1"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 192 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 23,
        n = 24,
        k = 23,
        s = 3,
        t = 128,
        w = 69,
        seed_tree = True,
        _name = "oldlevel3-55604-2"),

# old Level V

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 256 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 2039,
        m = 30,
        n = 31,
        k = 30,
        s = 5,
        t = 192,
        w = 52,
        seed_tree = True,
        _name = "oldlevel5-134180"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 256 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 2039,
        m = 30,
        n = 31,
        k = 30,
        s = 4,
        t = 144,
        w = 74,
        seed_tree = True,
        _name = "oldlevel5-134180-1"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 256 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 2039,
        m = 30,
        n = 31,
        k = 30,
        s = 6,
        t = 112,
        w = 66,
        seed_tree = True,
        _name = "oldlevel5-167717"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 256 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 2039,
        m = 30,
        n = 31,
        k = 30,
        s = 5,
        t = 112,
        w = 86,
        seed_tree = True,
        _name = "oldlevel5-167717-1"),

## # new parameter sets
## # Test Level 1
##   Param(digest_bytes = 256 >> 3,
##         pub_seed_bytes = 256 >> 3,
##         sec_seed_bytes = 256 >> 3,
##         st_seed_bytes = 128 >> 3,
##         st_salt_bytes = 256 >> 3,
##         q = 8191,
##         m = 21,
##         n = 22,
##         k = 21,
##         s = 2,
##         t = 160,
##         w = 42,
##         seed_tree = False,
##         _name = "level1"),
## 
##   Param(digest_bytes = 256 >> 3,
##         pub_seed_bytes = 256 >> 3,
##         sec_seed_bytes = 256 >> 3,
##         st_seed_bytes = 128 >> 3,
##         st_salt_bytes = 256 >> 3,
##         q = 65521,
##         m = 18,
##         n = 19,
##         k = 18,
##         s = 2,
##         t = 160,
##         w = 42,
##         seed_tree = False,
##         _name = "level116"),
## 
##   Param(digest_bytes = 256 >> 3,
##         pub_seed_bytes = 256 >> 3,
##         sec_seed_bytes = 256 >> 3,
##         st_seed_bytes = 128 >> 3,
##         st_salt_bytes = 256 >> 3,
##         q = 4194301,
##         m = 14,
##         n = 15,
##         k = 14,
##         s = 2,
##         t = 160,
##         w = 42,
##         seed_tree = False,
##         _name = "level1alt"),
## 
##   Param(digest_bytes = 256 >> 3,
##         pub_seed_bytes = 256 >> 3,
##         sec_seed_bytes = 256 >> 3,
##         st_seed_bytes = 128 >> 3,
##         st_salt_bytes = 256 >> 3,
##         q = 4194301,
##         m = 14,
##         n = 15,
##         k = 14,
##         s = 3,
##         t = 240,
##         w = 23,
##         seed_tree = True,
##         _name = "level1alt2"),
## 
##   Param(digest_bytes = 256 >> 3,
##         pub_seed_bytes = 256 >> 3,
##         sec_seed_bytes = 256 >> 3,
##         st_seed_bytes = 128 >> 3,
##         st_salt_bytes = 256 >> 3,
##         q = 8191,
##         m = 21,
##         n = 22,
##         k = 21,
##         s = 2,
##         t = 256,
##         w = 30,
##         seed_tree = True,
##         _name = "level1st"),
## 
## #   Param(digest_bytes = 256 >> 3,
## #         pub_seed_bytes = 256 >> 3,
## #         sec_seed_bytes = 256 >> 3,
## #         st_seed_bytes = 128 >> 3,
## #         st_salt_bytes = 256 >> 3,
## #         q = 65521,
## #         m = 18,
## #         n = 19,
## #         k = 18,
## #         s = 2,
## #         t = 160,
## #         w = 42,
## #         seed_tree = False),
## # 
## #   Param(digest_bytes = 256 >> 3,
## #         pub_seed_bytes = 256 >> 3,
## #         sec_seed_bytes = 256 >> 3,
## #         st_seed_bytes = 128 >> 3,
## #         st_salt_bytes = 256 >> 3,
## #         q = 4194301,
## #         m = 14,
## #         n = 15,
## #         k = 14,
## #         s = 2,
## #         t = 240,
## #         w = 31),
## # #        _name = "MEDS-2084"),
## 
## # # Level I
## #   Param(digest_bytes = 256 >> 3,
## #         pub_seed_bytes = 256 >> 3,
## #         sec_seed_bytes = 256 >> 3,
## #         st_seed_bytes = 128 >> 3,
## #         st_salt_bytes = 256 >> 3,
## #         q = 4093,
## #         m = 14,
## #         n = 15,
## #         k = 14,
## #         s = 4,
## #         t = 1152,
## #         w = 14),
## # 
## #   Param(digest_bytes = 256 >> 3,
## #         pub_seed_bytes = 256 >> 3,
## #         sec_seed_bytes = 256 >> 3,
## #         st_seed_bytes = 128 >> 3,
## #         st_salt_bytes = 256 >> 3,
## #         q = 4093,
## #         m = 14,
## #         n = 15,
## #         k = 14,
## #         s = 5,
## #         t = 192,
## #         w = 20),
## 
## # Level III
## 
##   Param(digest_bytes = 256 >> 3,
##         pub_seed_bytes = 256 >> 3,
##         sec_seed_bytes = 256 >> 3,
##         st_seed_bytes = 192 >> 3,
##         st_salt_bytes = 256 >> 3,
##         q = 131071,
##         m = 25,
##         n = 26,
##         k = 25,
##         s = 2,
##         t = 240,
##         w = 61,
##         seed_tree = False,
##         _name = "level3"),
## 
##   Param(digest_bytes = 256 >> 3,
##         pub_seed_bytes = 256 >> 3,
##         sec_seed_bytes = 256 >> 3,
##         st_seed_bytes = 192 >> 3,
##         st_salt_bytes = 256 >> 3,
##         q = 65521,
##         m = 26,
##         n = 27,
##         k = 26,
##         s = 2,
##         t = 240,
##         w = 61,
##         seed_tree = False,
##         _name = "level16"),
## 
##   Param(digest_bytes = 256 >> 3,
##         pub_seed_bytes = 256 >> 3,
##         sec_seed_bytes = 256 >> 3,
##         st_seed_bytes = 192 >> 3,
##         st_salt_bytes = 256 >> 3,
##         q = 2097143,
##         m = 20,
##         n = 21,
##         k = 20,
##         s = 2,
##         t = 240,
##         w = 61,
##         seed_tree = False,
##         _name = "level3alt"),
## 
##   Param(digest_bytes = 256 >> 3,
##         pub_seed_bytes = 256 >> 3,
##         sec_seed_bytes = 256 >> 3,
##         st_seed_bytes = 192 >> 3,
##         st_salt_bytes = 256 >> 3,
##         q = 131071,
##         m = 25,
##         n = 26,
##         k = 25,
##         s = 2,
##         t = 464,
##         w = 40,
##         seed_tree = True,
##         _name = "level3st"),
## 
## #   Param(digest_bytes = 256 >> 3,
## #         pub_seed_bytes = 256 >> 3,
## #         sec_seed_bytes = 256 >> 3,
## #         st_seed_bytes = 192 >> 3,
## #         st_salt_bytes = 256 >> 3,
## #         q = 4093,
## #         m = 22,
## #         n = 23,
## #         k = 22,
## #         s = 4,
## #         t = 608,
## #         w = 26),
## # 
## #   Param(digest_bytes = 256 >> 3,
## #         pub_seed_bytes = 256 >> 3,
## #         sec_seed_bytes = 256 >> 3,
## #         st_seed_bytes = 192 >> 3,
## #         st_salt_bytes = 256 >> 3,
## #         q = 4093,
## #         m = 22,
## #         n = 23,
## #         k = 22,
## #         s = 5,
## #         t = 160,
## #         w = 36),
## 
## # Level V
## 
##   Param(digest_bytes = 256 >> 3,
##         pub_seed_bytes = 256 >> 3,
##         sec_seed_bytes = 256 >> 3,
##         st_seed_bytes = 256 >> 3,
##         st_salt_bytes = 256 >> 3,
##         q = 1048573,
##         m = 27,
##         n = 28,
##         k = 27,
##         s = 2,
##         t = 304,
##         w = 86,
##         seed_tree = False,
##         _name = "level5"),
## 
##   Param(digest_bytes = 256 >> 3,
##         pub_seed_bytes = 256 >> 3,
##         sec_seed_bytes = 256 >> 3,
##         st_seed_bytes = 256 >> 3,
##         st_salt_bytes = 256 >> 3,
##         q = 65521,
##         m = 34,
##         n = 35,
##         k = 34,
##         s = 2,
##         t = 304,
##         w = 86,
##         seed_tree = False,
##         _name = "level516"),
## 
##   Param(digest_bytes = 256 >> 3,
##         pub_seed_bytes = 256 >> 3,
##         sec_seed_bytes = 256 >> 3,
##         st_seed_bytes = 256 >> 3,
##         st_salt_bytes = 256 >> 3,
##         q = 1048573,
##         m = 27,
##         n = 28,
##         k = 27,
##         s = 2,
##         t = 512,
##         w = 58,
##         seed_tree = True,
##         _name = "level5st"),
## 
## 
## #  Param(digest_bytes = 256 >> 3,
## #        pub_seed_bytes = 256 >> 3,
## #        sec_seed_bytes = 256 >> 3,
## #        st_seed_bytes = 256 >> 3,
## #        st_salt_bytes = 256 >> 3,
## #        q = 2039,
## #        m = 30,
## #        n = 31,
## #        k = 30,
## #        s = 2,
## #        t = 288,
## #        w = 94,
## #        seed_tree = False),
## #
## #  Param(digest_bytes = 256 >> 3,
## #        pub_seed_bytes = 256 >> 3,
## #        sec_seed_bytes = 256 >> 3,
## #        st_seed_bytes = 256 >> 3,
## #        st_salt_bytes = 256 >> 3,
## #        q = 2039,
## #        m = 30,
## #        n = 31,
## #        k = 30,
## #        s = 4,
## #        t = 256,
## #        w = 50),
## 
## #   Param(digest_bytes = 256 >> 3,
## #         pub_seed_bytes = 256 >> 3,
## #         sec_seed_bytes = 256 >> 3,
## #         st_seed_bytes = 256 >> 3,
## #         st_salt_bytes = 256 >> 3,
## #         q = 2039,
## #         m = 30,
## #         n = 31,
## #         k = 30,
## #         s = 5,
## #         t = 192,
## #         w = 52),
## # 
## #   Param(digest_bytes = 256 >> 3,
## #         pub_seed_bytes = 256 >> 3,
## #         sec_seed_bytes = 256 >> 3,
## #         st_seed_bytes = 256 >> 3,
## #         st_salt_bytes = 256 >> 3,
## #         q = 2039,
## #         m = 30,
## #         n = 31,
## #         k = 30,
## #         s = 6,
## #         t = 112,
## #         w = 66),

# toy

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 128 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 25,
        n = 26,
        k = 25,
        s = 2,
        t = 144,
        w = 48,
        seed_tree = False,
        _name = "level1"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 192 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 34,
        n = 35,
        k = 34,
        s = 2,
        t = 208,
        w = 75,
        seed_tree = False,
        _name = "level3"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 256 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 44,
        n = 45,
        k = 44,
        s = 2,
        t = 272,
        w = 103,
        seed_tree = False,
        _name = "level5"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 128 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 25,
        n = 26,
        k = 25,
        s = 2,
        t = 144,
        w = 48,
        seed_tree = False,
        hash_opt = True,
        _name = "level1hopt"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 192 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 34,
        n = 35,
        k = 34,
        s = 2,
        t = 208,
        w = 75,
        seed_tree = False,
        hash_opt = True,
        _name = "level3hopt"),

  Param(digest_bytes = 256 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 256 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 4093,
        m = 44,
        n = 45,
        k = 44,
        s = 2,
        t = 272,
        w = 103,
        seed_tree = False,
        hash_opt = True,
        _name = "level5hopt"),

  Param(digest_bytes = 128 >> 3,
        pub_seed_bytes = 256 >> 3,
        sec_seed_bytes = 256 >> 3,
        st_seed_bytes = 128 >> 3,
        st_salt_bytes = 256 >> 3,
        q = 13, #4093,
        m = 4, #10,
        n = 5, #11,
        k = 4, #10,
        s = 2, #5,
        t = 4, #16,
        w = 2,
        _name = "toy"),
]

for i, p in enumerate(params):
  exec(f"{p.name} = params[i]")

par_list = {p.name : p for p in params}


def print_table():
  from tabulate import tabulate

  tab = []

  for param in params:
    fs = -param.fiat_shamir

    pk =  param.pk_size
    sk =  param.sk_size
    sig = param.sig_size

    tab.append([param, param.q, param.n, param.m, param.k, param.s, param.t, param.w, param.seed_tree, pk, sk, sig, fs])

  headers = ["set", "q", "n", "m", "k", "s", "t", "w", "st", "pk", "sk", "sig", "fs"]

  tab = tabulate(tab, headers, tablefmt="latex_booktabs")

  print(tab)

def print_list():
  for param in params:
    print(param.name)

def interactive():
  param = params[0]

  def inject_params(param):
    global digest_bytes, pub_seed_bytes, sec_seed_bytes, st_seed_bytes, st_salt_bytes, q, n, m, s, t, w, k

    digest_bytes = param.digest_bytes
    pub_seed_bytes = param.pub_seed_bytes
    sec_seed_bytes = param.sec_seed_bytes
    st_seed_bytes = param.st_seed_bytes
    st_salt_bytes = param.st_salt_bytes
    q = param.q
    n = param.n
    m = param.m
    s = param.s
    t = param.t
    w = param.w
    k = param.k

  inject_params(param)

  def opt_tw(s, range_t=range(1, 1024)):
    @dataclass
    class TMP:
      sig_size: int

    tmp = TMP(100000000000000)

    for t in range_t:
      for w in range(1, min(t, 100)):
        loc = Param(digest_bytes, pub_seed_bytes, sec_seed_bytes, st_seed_bytes, st_salt_bytes, q, n, m, s, t, w, k)

        if loc.fiat_shamir > st_seed_bytes*8:
          if loc.sig_size < tmp.sig_size:
            tmp = loc

    print(f"sig size: {tmp.sig_size}  pk size: {tmp.pk_size} -> t = {tmp.t}, w = {tmp.w}")

  def dump():
    Param(digest_bytes, pub_seed_bytes, sec_seed_bytes, st_seed_bytes, st_salt_bytes, q, n, m, s, t, w, k).dump()

  import code
  import readline
  import rlcompleter

  vars = globals()
  vars.update(locals())

  readline.set_completer(rlcompleter.Completer(vars).complete)
  readline.parse_and_bind("tab: complete")
  code.InteractiveConsole(vars).interact(banner="""

Explore paramter space interactively.

Local variables q, n, m, ... can be dumped via 'dump()'.

(Exit python prompt with Ctrl-D)
""")


def gen_api(par_set):
  if not par_set:
    par_set = "toy"

  par_set = par_list[par_set]

  print(f"""#ifndef API_H
#define API_H

#define CRYPTO_SECRETKEYBYTES {par_set.sk_size}
#define CRYPTO_PUBLICKEYBYTES {par_set.pk_size}
#define CRYPTO_BYTES {par_set.sig_size}

#define CRYPTO_ALGNAME "{par_set.name}"

int crypto_sign_keypair(
    unsigned char *pk,
    unsigned char *sk
  );

int crypto_sign(
    unsigned char *sm, unsigned long long *smlen,
    const unsigned char *m, unsigned long long mlen,
    const unsigned char *sk
  );

int crypto_sign_open(
    unsigned char *m, unsigned long long *mlen,
    const unsigned char *sm, unsigned long long smlen,
    const unsigned char *pk
  );

#endif
""")

def gen_param(parset):
  print("#ifndef PARAMS_H")
  print("#define PARAMS_H")
  print()

  if not parset:
    plist = params
  else:
    plist = [par_list[parset]]

  for param in plist:
    if not parset:
      print(f"#ifdef {param.name}")
      ind = "  "
    else:
     ind = ""

    print(f'{ind}#define MEDS_name "{param.name}"')

    print()

    print(f"{ind}#define MEDS_digest_bytes {param.digest_bytes}")
    print(f"{ind}#define MEDS_pub_seed_bytes {param.pub_seed_bytes}")
    print(f"{ind}#define MEDS_sec_seed_bytes {param.sec_seed_bytes}")
    print(f"{ind}#define MEDS_st_seed_bytes {param.st_seed_bytes}")

    print(f"{ind}#define MEDS_st_salt_bytes {param.st_salt_bytes}")

    print()

    bits = log(param.q, 2)

    if bits < 64:
      tbits = 64

    if bits < 32:
      tbits = 32

    if bits < 16:
      tbits = 16

    if bits < 8:
      tbits = 8

    print(f"{ind}#define MEDS_p {param.q}")
    print(f"{ind}#define GFq_t uint{tbits}_t")
    print(f"{ind}#define GFq_bits {ceil(log(param.q, 2))}")
    print(f"{ind}#define GFq_bytes {ceil(ceil(log(param.q, 2))/8)}")
    print(f"{ind}#define GFq_fmt \"%{ceil(log(param.q, 10))}u\"")

    print()

    print(f"{ind}#define MEDS_m {param.m}")
    print(f"{ind}#define MEDS_n {param.n}")
    print(f"{ind}#define MEDS_k {param.k}")

    print()

    print(f"{ind}#define MEDS_s {param.s}")
    print(f"{ind}#define MEDS_t {param.t}")
    print(f"{ind}#define MEDS_w {param.w}")

    print()

    if param.seed_tree:
      print(f"{ind}#define MEDS_seed_tree_height {ceil(log(param.t, 2))}")
      print(f"{ind}#define SEED_TREE_size {((1 << (ceil(log(param.t, 2)) + 1)) - 1)}")
      print(f"{ind}#define MEDS_max_path_len {param.seed_max_tree_len}")
    else:
      print(f"{ind}#define MEDS_no_seed_tree")
      print(f"{ind}#define MEDS_seed_tree_height 0")
      print(f"{ind}#define SEED_TREE_size {param.t}")
      print(f"{ind}#define MEDS_max_path_len {param.seed_max_tree_len}")

    print()

    if param.hash_opt:
      print(f"{ind}#define MEDS_hash_opt")
    
    print()

    print(f"{ind}#define MEDS_t_mask 0x{2**ceil(log(param.t, 2)) - 1:08X}")
    print(f"{ind}#define MEDS_t_bytes {ceil(log(param.t-1, 2)/8)}")
    print()
    print(f"{ind}#define MEDS_s_mask 0x{2**ceil(log(param.s, 2)) - 1:08X}")

    print()

    print(f"{ind}#define MEDS_PK_BYTES {param.pk_size}")
    print(f"{ind}#define MEDS_SK_BYTES {param.sk_size}")
    print(f"{ind}#define MEDS_SIG_BYTES {param.sig_size}")

    if not parset:
      print(f"#endif")
    print()

  print("#endif")
  print()



if __name__ == "__main__":
  import argparse

  parser = argparse.ArgumentParser()

  parser.add_argument("-t", "--table", action='store_true', help = "print Latex table")
  parser.add_argument("-l", "--list", action='store_true', help = "list param set names")
  parser.add_argument("-i", "--interactive", action='store_true', help = "interactive python console")
  parser.add_argument("-a", "--api", action='store_true', help = "generate api.h")
  parser.add_argument("-p", "--param", action='store_true', help = "generate param.h")
  parser.add_argument('parset', nargs='?', help = "parameter set", default=None)

  args = parser.parse_args()

  if args.table:
    print_table()
  elif args.list:
    print_list()
  elif args.interactive:
    interactive()
  elif args.api:
    gen_api(args.parset)
  elif args.param:
    gen_param(args.parset)
  else:
    print_table()

