import Lean

namespace ShotD

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Binary vectors of at most eight coordinates, encoded as natural numbers. -/
def parity8 (x : Nat) : Bool :=
  let a := x ^^^ (x >>> 4)
  let b := a ^^^ (a >>> 2)
  (b ^^^ (b >>> 1)).testBit 0

/-- A seed represents two scalar probes. The result encodes its two-bit image. -/
def project (seed : Nat × Nat) (v : Nat) : Nat :=
  (if parity8 (seed.1 &&& v) then 1 else 0) +
    (if parity8 (seed.2 &&& v) then 2 else 0)

/-- There is one record per plane, with its nonzero vectors x < y < x XOR y. -/
def planes (n : Nat) : List (Nat × Nat) :=
  let vectors := List.range (2 ^ n)
  vectors.flatMap fun x =>
    (vectors.filter fun y => 0 < x && x < y && y < (x ^^^ y)).map fun y => (x, y)

/-- Two nonzero distinct images are independent in the binary codomain. -/
def preserves (seed : Nat × Nat) (plane : Nat × Nat) : Bool :=
  let x := project seed plane.1
  let y := project seed plane.2
  x != 0 && y != 0 && x != y

/-- A row of binary survival indicators in plane order. -/
def hits (n : Nat) (seed : Nat × Nat) : List Nat :=
  (planes n).map fun plane => if preserves seed plane then 1 else 0

/-- Entry t counts planes on which exactly t of the supplied rows have a hit. -/
def histogram (size : Nat) (rows : List (List Nat)) : List Nat :=
  let counts := rows.foldl (List.zipWith (· + ·)) (List.replicate size 0)
  (List.range (rows.length + 1)).map fun t => counts.count t

def spectrum (n : Nat) (seeds : List (Nat × Nat)) : List Nat :=
  histogram (planes n).length (seeds.map (hits n))

private theorem layout4 : planes 4 = [(1, 2), (1, 4), (1, 6), (1, 8), (1, 10), (1, 12), (1, 14), (2, 4), (2, 5), (2, 8), (2, 9), (2, 12), (2, 13), (3, 4), (3, 5), (3, 8), (3, 9), (3, 12), (3, 13), (4, 8), (4, 9), (4, 10), (4, 11), (5, 8), (5, 9), (5, 10), (5, 11), (6, 8), (6, 9), (6, 10), (6, 11), (7, 8), (7, 9), (7, 10), (7, 11)] := by decide
private theorem count4 : (planes 4).length = 35 := by rw [layout4] <;> decide
private theorem row4_1_2 : hits 4 (1, 2) = [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0] := by rw [hits, layout4] <;> decide
private theorem row4_1_4 : hits 4 (1, 4) = [0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] := by rw [hits, layout4] <;> decide
private theorem row4_1_6 : hits 4 (1, 6) = [1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1] := by rw [hits, layout4] <;> decide
private theorem row4_1_8 : hits 4 (1, 8) = [0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1] := by rw [hits, layout4] <;> decide
private theorem row4_1_10 : hits 4 (1, 10) = [1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1] := by rw [hits, layout4] <;> decide
private theorem row4_1_12 : hits 4 (1, 12) = [0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0] := by rw [hits, layout4] <;> decide
private theorem row4_1_14 : hits 4 (1, 14) = [1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0] := by rw [hits, layout4] <;> decide
private theorem row4_2_4 : hits 4 (2, 4) = [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1] := by rw [hits, layout4] <;> decide
private theorem row4_2_5 : hits 4 (2, 5) = [1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1] := by rw [hits, layout4] <;> decide
private theorem row4_2_8 : hits 4 (2, 8) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1] := by rw [hits, layout4] <;> decide
private theorem row4_2_9 : hits 4 (2, 9) = [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1] := by rw [hits, layout4] <;> decide
private theorem row4_2_12 : hits 4 (2, 12) = [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0] := by rw [hits, layout4] <;> decide
private theorem row4_2_13 : hits 4 (2, 13) = [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0] := by rw [hits, layout4] <;> decide
private theorem row4_3_4 : hits 4 (3, 4) = [0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0] := by rw [hits, layout4] <;> decide
private theorem row4_3_5 : hits 4 (3, 5) = [1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0] := by rw [hits, layout4] <;> decide
private theorem row4_3_8 : hits 4 (3, 8) = [0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0] := by rw [hits, layout4] <;> decide
private theorem row4_3_9 : hits 4 (3, 9) = [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0] := by rw [hits, layout4] <;> decide
private theorem row4_3_12 : hits 4 (3, 12) = [0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0] := by rw [hits, layout4] <;> decide
private theorem row4_3_13 : hits 4 (3, 13) = [1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0] := by rw [hits, layout4] <;> decide
private theorem row4_4_8 : hits 4 (4, 8) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by rw [hits, layout4] <;> decide
private theorem row4_4_9 : hits 4 (4, 9) = [0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] := by rw [hits, layout4] <;> decide
private theorem row4_4_10 : hits 4 (4, 10) = [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0] := by rw [hits, layout4] <;> decide
private theorem row4_4_11 : hits 4 (4, 11) = [0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1] := by rw [hits, layout4] <;> decide
private theorem row4_5_8 : hits 4 (5, 8) = [0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0] := by rw [hits, layout4] <;> decide
private theorem row4_5_9 : hits 4 (5, 9) = [0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1] := by rw [hits, layout4] <;> decide
private theorem row4_5_10 : hits 4 (5, 10) = [1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1] := by rw [hits, layout4] <;> decide
private theorem row4_5_11 : hits 4 (5, 11) = [1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0] := by rw [hits, layout4] <;> decide
private theorem row4_6_8 : hits 4 (6, 8) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout4] <;> decide
private theorem row4_6_9 : hits 4 (6, 9) = [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1] := by rw [hits, layout4] <;> decide
private theorem row4_6_10 : hits 4 (6, 10) = [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1] := by rw [hits, layout4] <;> decide
private theorem row4_6_11 : hits 4 (6, 11) = [1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0] := by rw [hits, layout4] <;> decide
private theorem row4_7_8 : hits 4 (7, 8) = [0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1] := by rw [hits, layout4] <;> decide
private theorem row4_7_9 : hits 4 (7, 9) = [1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0] := by rw [hits, layout4] <;> decide
private theorem row4_7_10 : hits 4 (7, 10) = [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0] := by rw [hits, layout4] <;> decide
private theorem row4_7_11 : hits 4 (7, 11) = [0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] := by rw [hits, layout4] <;> decide
theorem n4_001 : spectrum 4 [(1, 2), (1, 8), (2, 8), (4, 11), (7, 8)] = [1, 8, 12, 8, 6, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (1, 8), hits 4 (2, 8), hits 4 (4, 11), hits 4 (7, 8)] = [1, 8, 12, 8, 6, 0]
  rw [count4, row4_1_2, row4_1_8, row4_2_8, row4_4_11, row4_7_8] <;> decide

theorem n4_002 : spectrum 4 [(2, 5), (3, 4), (3, 9), (4, 10), (7, 8), (7, 9), (7, 11)] = [3, 0, 4, 14, 10, 2, 2, 0] := by
  change histogram (planes 4).length [hits 4 (2, 5), hits 4 (3, 4), hits 4 (3, 9), hits 4 (4, 10), hits 4 (7, 8), hits 4 (7, 9), hits 4 (7, 11)] = [3, 0, 4, 14, 10, 2, 2, 0]
  rw [count4, row4_2_5, row4_3_4, row4_3_9, row4_4_10, row4_7_8, row4_7_9, row4_7_11] <;> decide

theorem n4_003 : spectrum 4 [(1, 10), (1, 14), (2, 5), (2, 12), (3, 4), (4, 10), (5, 9), (7, 11)] = [0, 2, 3, 12, 9, 6, 3, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 10), hits 4 (1, 14), hits 4 (2, 5), hits 4 (2, 12), hits 4 (3, 4), hits 4 (4, 10), hits 4 (5, 9), hits 4 (7, 11)] = [0, 2, 3, 12, 9, 6, 3, 0, 0]
  rw [count4, row4_1_10, row4_1_14, row4_2_5, row4_2_12, row4_3_4, row4_4_10, row4_5_9, row4_7_11] <;> decide

theorem n4_004 : spectrum 4 [(1, 14), (3, 4), (4, 10), (4, 11), (6, 8), (7, 8), (7, 9)] = [0, 4, 8, 10, 5, 6, 2, 0] := by
  change histogram (planes 4).length [hits 4 (1, 14), hits 4 (3, 4), hits 4 (4, 10), hits 4 (4, 11), hits 4 (6, 8), hits 4 (7, 8), hits 4 (7, 9)] = [0, 4, 8, 10, 5, 6, 2, 0]
  rw [count4, row4_1_14, row4_3_4, row4_4_10, row4_4_11, row4_6_8, row4_7_8, row4_7_9] <;> decide

theorem n4_005 : spectrum 4 [(1, 8), (1, 12), (2, 8), (4, 9), (4, 11), (5, 9), (6, 10)] = [1, 0, 10, 10, 8, 6, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 8), hits 4 (1, 12), hits 4 (2, 8), hits 4 (4, 9), hits 4 (4, 11), hits 4 (5, 9), hits 4 (6, 10)] = [1, 0, 10, 10, 8, 6, 0, 0]
  rw [count4, row4_1_8, row4_1_12, row4_2_8, row4_4_9, row4_4_11, row4_5_9, row4_6_10] <;> decide

theorem n4_006 : spectrum 4 [(1, 4), (2, 5), (3, 5), (3, 9), (3, 13), (4, 9), (5, 9), (5, 10), (6, 10)] = [0, 2, 3, 7, 7, 10, 5, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (2, 5), hits 4 (3, 5), hits 4 (3, 9), hits 4 (3, 13), hits 4 (4, 9), hits 4 (5, 9), hits 4 (5, 10), hits 4 (6, 10)] = [0, 2, 3, 7, 7, 10, 5, 1, 0, 0]
  rw [count4, row4_1_4, row4_2_5, row4_3_5, row4_3_9, row4_3_13, row4_4_9, row4_5_9, row4_5_10, row4_6_10] <;> decide

theorem n4_007 : spectrum 4 [(3, 9), (3, 12), (4, 11), (5, 10)] = [3, 12, 10, 8, 2] := by
  change histogram (planes 4).length [hits 4 (3, 9), hits 4 (3, 12), hits 4 (4, 11), hits 4 (5, 10)] = [3, 12, 10, 8, 2]
  rw [count4, row4_3_9, row4_3_12, row4_4_11, row4_5_10] <;> decide

theorem n4_008 : spectrum 4 [(1, 6), (1, 8), (2, 5), (2, 13), (3, 4), (3, 9), (7, 11)] = [0, 4, 4, 12, 11, 4, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (1, 8), hits 4 (2, 5), hits 4 (2, 13), hits 4 (3, 4), hits 4 (3, 9), hits 4 (7, 11)] = [0, 4, 4, 12, 11, 4, 0, 0]
  rw [count4, row4_1_6, row4_1_8, row4_2_5, row4_2_13, row4_3_4, row4_3_9, row4_7_11] <;> decide

theorem n4_009 : spectrum 4 [(1, 4), (2, 5), (2, 9), (2, 12), (2, 13), (3, 4), (3, 13), (5, 10), (5, 11), (6, 9)] = [0, 0, 1, 9, 7, 8, 7, 3, 0, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (2, 5), hits 4 (2, 9), hits 4 (2, 12), hits 4 (2, 13), hits 4 (3, 4), hits 4 (3, 13), hits 4 (5, 10), hits 4 (5, 11), hits 4 (6, 9)] = [0, 0, 1, 9, 7, 8, 7, 3, 0, 0, 0]
  rw [count4, row4_1_4, row4_2_5, row4_2_9, row4_2_12, row4_2_13, row4_3_4, row4_3_13, row4_5_10, row4_5_11, row4_6_9] <;> decide

theorem n4_010 : spectrum 4 [(1, 4), (1, 14), (3, 5), (6, 9)] = [2, 12, 14, 4, 3] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 14), hits 4 (3, 5), hits 4 (6, 9)] = [2, 12, 14, 4, 3]
  rw [count4, row4_1_4, row4_1_14, row4_3_5, row4_6_9] <;> decide

theorem n4_011 : spectrum 4 [(1, 4), (1, 8), (1, 12), (2, 4), (3, 4), (3, 8), (4, 10), (6, 8)] = [1, 0, 4, 12, 8, 8, 2, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 8), hits 4 (1, 12), hits 4 (2, 4), hits 4 (3, 4), hits 4 (3, 8), hits 4 (4, 10), hits 4 (6, 8)] = [1, 0, 4, 12, 8, 8, 2, 0, 0]
  rw [count4, row4_1_4, row4_1_8, row4_1_12, row4_2_4, row4_3_4, row4_3_8, row4_4_10, row4_6_8] <;> decide

theorem n4_012 : spectrum 4 [(3, 12), (4, 9), (4, 10), (7, 10), (7, 11)] = [1, 8, 10, 12, 4, 0] := by
  change histogram (planes 4).length [hits 4 (3, 12), hits 4 (4, 9), hits 4 (4, 10), hits 4 (7, 10), hits 4 (7, 11)] = [1, 8, 10, 12, 4, 0]
  rw [count4, row4_3_12, row4_4_9, row4_4_10, row4_7_10, row4_7_11] <;> decide

theorem n4_013 : spectrum 4 [(1, 10), (3, 4), (4, 10), (6, 8), (7, 11)] = [0, 9, 12, 10, 3, 1] := by
  change histogram (planes 4).length [hits 4 (1, 10), hits 4 (3, 4), hits 4 (4, 10), hits 4 (6, 8), hits 4 (7, 11)] = [0, 9, 12, 10, 3, 1]
  rw [count4, row4_1_10, row4_3_4, row4_4_10, row4_6_8, row4_7_11] <;> decide

theorem n4_014 : spectrum 4 [(1, 14), (2, 9), (3, 5), (5, 8), (5, 11), (6, 9), (7, 10), (7, 11)] = [0, 1, 5, 8, 13, 7, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 14), hits 4 (2, 9), hits 4 (3, 5), hits 4 (5, 8), hits 4 (5, 11), hits 4 (6, 9), hits 4 (7, 10), hits 4 (7, 11)] = [0, 1, 5, 8, 13, 7, 1, 0, 0]
  rw [count4, row4_1_14, row4_2_9, row4_3_5, row4_5_8, row4_5_11, row4_6_9, row4_7_10, row4_7_11] <;> decide

theorem n4_015 : spectrum 4 [(1, 10), (2, 4), (2, 9), (3, 9), (3, 12), (4, 8), (5, 8), (6, 9)] = [0, 0, 7, 8, 11, 8, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 10), hits 4 (2, 4), hits 4 (2, 9), hits 4 (3, 9), hits 4 (3, 12), hits 4 (4, 8), hits 4 (5, 8), hits 4 (6, 9)] = [0, 0, 7, 8, 11, 8, 1, 0, 0]
  rw [count4, row4_1_10, row4_2_4, row4_2_9, row4_3_9, row4_3_12, row4_4_8, row4_5_8, row4_6_9] <;> decide

theorem n4_016 : spectrum 4 [(3, 8), (5, 8), (5, 11), (6, 10)] = [3, 10, 12, 10, 0] := by
  change histogram (planes 4).length [hits 4 (3, 8), hits 4 (5, 8), hits 4 (5, 11), hits 4 (6, 10)] = [3, 10, 12, 10, 0]
  rw [count4, row4_3_8, row4_5_8, row4_5_11, row4_6_10] <;> decide

theorem n4_017 : spectrum 4 [(2, 4), (2, 5), (2, 8), (2, 13), (3, 5), (3, 8), (3, 13), (4, 11), (7, 9), (7, 10)] = [0, 0, 1, 7, 11, 6, 7, 3, 0, 0, 0] := by
  change histogram (planes 4).length [hits 4 (2, 4), hits 4 (2, 5), hits 4 (2, 8), hits 4 (2, 13), hits 4 (3, 5), hits 4 (3, 8), hits 4 (3, 13), hits 4 (4, 11), hits 4 (7, 9), hits 4 (7, 10)] = [0, 0, 1, 7, 11, 6, 7, 3, 0, 0, 0]
  rw [count4, row4_2_4, row4_2_5, row4_2_8, row4_2_13, row4_3_5, row4_3_8, row4_3_13, row4_4_11, row4_7_9, row4_7_10] <;> decide

theorem n4_018 : spectrum 4 [(1, 8), (2, 5), (3, 5), (4, 9), (5, 10)] = [3, 2, 14, 14, 2, 0] := by
  change histogram (planes 4).length [hits 4 (1, 8), hits 4 (2, 5), hits 4 (3, 5), hits 4 (4, 9), hits 4 (5, 10)] = [3, 2, 14, 14, 2, 0]
  rw [count4, row4_1_8, row4_2_5, row4_3_5, row4_4_9, row4_5_10] <;> decide

theorem n4_019 : spectrum 4 [(3, 8), (3, 9), (4, 8), (4, 10), (4, 11), (5, 11), (6, 9), (7, 10)] = [0, 0, 6, 12, 9, 4, 4, 0, 0] := by
  change histogram (planes 4).length [hits 4 (3, 8), hits 4 (3, 9), hits 4 (4, 8), hits 4 (4, 10), hits 4 (4, 11), hits 4 (5, 11), hits 4 (6, 9), hits 4 (7, 10)] = [0, 0, 6, 12, 9, 4, 4, 0, 0]
  rw [count4, row4_3_8, row4_3_9, row4_4_8, row4_4_10, row4_4_11, row4_5_11, row4_6_9, row4_7_10] <;> decide

theorem n4_020 : spectrum 4 [(2, 4), (3, 13), (5, 9), (5, 10)] = [1, 12, 14, 8, 0] := by
  change histogram (planes 4).length [hits 4 (2, 4), hits 4 (3, 13), hits 4 (5, 9), hits 4 (5, 10)] = [1, 12, 14, 8, 0]
  rw [count4, row4_2_4, row4_3_13, row4_5_9, row4_5_10] <;> decide

theorem n4_021 : spectrum 4 [(1, 2), (1, 6), (2, 13), (3, 8), (3, 13), (4, 8), (7, 8)] = [0, 2, 9, 10, 9, 4, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (1, 6), hits 4 (2, 13), hits 4 (3, 8), hits 4 (3, 13), hits 4 (4, 8), hits 4 (7, 8)] = [0, 2, 9, 10, 9, 4, 1, 0]
  rw [count4, row4_1_2, row4_1_6, row4_2_13, row4_3_8, row4_3_13, row4_4_8, row4_7_8] <;> decide

theorem n4_022 : spectrum 4 [(2, 8), (2, 13), (4, 9), (4, 11), (5, 10), (5, 11), (7, 9), (7, 11)] = [0, 1, 5, 10, 11, 5, 3, 0, 0] := by
  change histogram (planes 4).length [hits 4 (2, 8), hits 4 (2, 13), hits 4 (4, 9), hits 4 (4, 11), hits 4 (5, 10), hits 4 (5, 11), hits 4 (7, 9), hits 4 (7, 11)] = [0, 1, 5, 10, 11, 5, 3, 0, 0]
  rw [count4, row4_2_8, row4_2_13, row4_4_9, row4_4_11, row4_5_10, row4_5_11, row4_7_9, row4_7_11] <;> decide

theorem n4_023 : spectrum 4 [(4, 10), (4, 11), (7, 8), (7, 11)] = [3, 10, 14, 6, 2] := by
  change histogram (planes 4).length [hits 4 (4, 10), hits 4 (4, 11), hits 4 (7, 8), hits 4 (7, 11)] = [3, 10, 14, 6, 2]
  rw [count4, row4_4_10, row4_4_11, row4_7_8, row4_7_11] <;> decide

theorem n4_024 : spectrum 4 [(1, 12), (3, 8), (3, 13), (4, 8), (6, 11), (7, 10), (7, 11)] = [0, 4, 8, 8, 9, 4, 2, 0] := by
  change histogram (planes 4).length [hits 4 (1, 12), hits 4 (3, 8), hits 4 (3, 13), hits 4 (4, 8), hits 4 (6, 11), hits 4 (7, 10), hits 4 (7, 11)] = [0, 4, 8, 8, 9, 4, 2, 0]
  rw [count4, row4_1_12, row4_3_8, row4_3_13, row4_4_8, row4_6_11, row4_7_10, row4_7_11] <;> decide

theorem n4_025 : spectrum 4 [(1, 4), (1, 6), (1, 8), (1, 14), (2, 8), (3, 5), (3, 13), (4, 11)] = [0, 1, 4, 12, 9, 7, 2, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 6), hits 4 (1, 8), hits 4 (1, 14), hits 4 (2, 8), hits 4 (3, 5), hits 4 (3, 13), hits 4 (4, 11)] = [0, 1, 4, 12, 9, 7, 2, 0, 0]
  rw [count4, row4_1_4, row4_1_6, row4_1_8, row4_1_14, row4_2_8, row4_3_5, row4_3_13, row4_4_11] <;> decide

theorem n4_026 : spectrum 4 [(1, 6), (2, 5), (2, 9), (2, 13), (3, 4), (6, 11), (7, 8)] = [0, 4, 7, 8, 11, 4, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (2, 5), hits 4 (2, 9), hits 4 (2, 13), hits 4 (3, 4), hits 4 (6, 11), hits 4 (7, 8)] = [0, 4, 7, 8, 11, 4, 1, 0]
  rw [count4, row4_1_6, row4_2_5, row4_2_9, row4_2_13, row4_3_4, row4_6_11, row4_7_8] <;> decide

theorem n4_027 : spectrum 4 [(1, 4), (2, 5), (2, 9), (3, 12), (4, 9), (4, 10), (7, 10)] = [0, 1, 8, 14, 9, 1, 2, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (2, 5), hits 4 (2, 9), hits 4 (3, 12), hits 4 (4, 9), hits 4 (4, 10), hits 4 (7, 10)] = [0, 1, 8, 14, 9, 1, 2, 0]
  rw [count4, row4_1_4, row4_2_5, row4_2_9, row4_3_12, row4_4_9, row4_4_10, row4_7_10] <;> decide

theorem n4_028 : spectrum 4 [(2, 5), (2, 12), (2, 13), (3, 5), (3, 8), (3, 12), (5, 8), (6, 8), (6, 10), (7, 10)] = [0, 0, 2, 5, 13, 6, 4, 5, 0, 0, 0] := by
  change histogram (planes 4).length [hits 4 (2, 5), hits 4 (2, 12), hits 4 (2, 13), hits 4 (3, 5), hits 4 (3, 8), hits 4 (3, 12), hits 4 (5, 8), hits 4 (6, 8), hits 4 (6, 10), hits 4 (7, 10)] = [0, 0, 2, 5, 13, 6, 4, 5, 0, 0, 0]
  rw [count4, row4_2_5, row4_2_12, row4_2_13, row4_3_5, row4_3_8, row4_3_12, row4_5_8, row4_6_8, row4_6_10, row4_7_10] <;> decide

theorem n4_029 : spectrum 4 [(1, 4), (2, 8), (2, 9), (3, 13), (4, 9), (4, 11), (5, 9), (7, 8)] = [0, 0, 5, 12, 11, 4, 3, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (2, 8), hits 4 (2, 9), hits 4 (3, 13), hits 4 (4, 9), hits 4 (4, 11), hits 4 (5, 9), hits 4 (7, 8)] = [0, 0, 5, 12, 11, 4, 3, 0, 0]
  rw [count4, row4_1_4, row4_2_8, row4_2_9, row4_3_13, row4_4_9, row4_4_11, row4_5_9, row4_7_8] <;> decide

theorem n4_030 : spectrum 4 [(1, 4), (1, 14), (2, 12), (3, 5), (3, 13), (5, 9), (5, 11), (6, 10), (7, 8), (7, 11)] = [0, 0, 2, 7, 7, 10, 6, 3, 0, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 14), hits 4 (2, 12), hits 4 (3, 5), hits 4 (3, 13), hits 4 (5, 9), hits 4 (5, 11), hits 4 (6, 10), hits 4 (7, 8), hits 4 (7, 11)] = [0, 0, 2, 7, 7, 10, 6, 3, 0, 0, 0]
  rw [count4, row4_1_4, row4_1_14, row4_2_12, row4_3_5, row4_3_13, row4_5_9, row4_5_11, row4_6_10, row4_7_8, row4_7_11] <;> decide

theorem n4_031 : spectrum 4 [(2, 4), (3, 12), (4, 8), (4, 10), (5, 10), (6, 10), (7, 9)] = [0, 3, 8, 10, 7, 7, 0, 0] := by
  change histogram (planes 4).length [hits 4 (2, 4), hits 4 (3, 12), hits 4 (4, 8), hits 4 (4, 10), hits 4 (5, 10), hits 4 (6, 10), hits 4 (7, 9)] = [0, 3, 8, 10, 7, 7, 0, 0]
  rw [count4, row4_2_4, row4_3_12, row4_4_8, row4_4_10, row4_5_10, row4_6_10, row4_7_9] <;> decide

theorem n4_032 : spectrum 4 [(1, 4), (1, 12), (2, 12), (2, 13), (3, 4), (4, 9), (4, 10), (6, 10)] = [0, 2, 5, 7, 13, 6, 1, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 12), hits 4 (2, 12), hits 4 (2, 13), hits 4 (3, 4), hits 4 (4, 9), hits 4 (4, 10), hits 4 (6, 10)] = [0, 2, 5, 7, 13, 6, 1, 1, 0]
  rw [count4, row4_1_4, row4_1_12, row4_2_12, row4_2_13, row4_3_4, row4_4_9, row4_4_10, row4_6_10] <;> decide

theorem n4_033 : spectrum 4 [(1, 14), (2, 8), (3, 5), (3, 8), (4, 10), (7, 9)] = [1, 3, 8, 16, 6, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 14), hits 4 (2, 8), hits 4 (3, 5), hits 4 (3, 8), hits 4 (4, 10), hits 4 (7, 9)] = [1, 3, 8, 16, 6, 1, 0]
  rw [count4, row4_1_14, row4_2_8, row4_3_5, row4_3_8, row4_4_10, row4_7_9] <;> decide

theorem n4_034 : spectrum 4 [(1, 6), (1, 8), (2, 4), (2, 5), (2, 9), (2, 13), (3, 8), (5, 9), (5, 10)] = [0, 0, 5, 4, 13, 10, 1, 2, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (1, 8), hits 4 (2, 4), hits 4 (2, 5), hits 4 (2, 9), hits 4 (2, 13), hits 4 (3, 8), hits 4 (5, 9), hits 4 (5, 10)] = [0, 0, 5, 4, 13, 10, 1, 2, 0, 0]
  rw [count4, row4_1_6, row4_1_8, row4_2_4, row4_2_5, row4_2_9, row4_2_13, row4_3_8, row4_5_9, row4_5_10] <;> decide

theorem n4_035 : spectrum 4 [(1, 4), (1, 12), (2, 8), (2, 13), (3, 4), (3, 8), (6, 11), (7, 8), (7, 10)] = [0, 1, 1, 11, 9, 7, 5, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 12), hits 4 (2, 8), hits 4 (2, 13), hits 4 (3, 4), hits 4 (3, 8), hits 4 (6, 11), hits 4 (7, 8), hits 4 (7, 10)] = [0, 1, 1, 11, 9, 7, 5, 1, 0, 0]
  rw [count4, row4_1_4, row4_1_12, row4_2_8, row4_2_13, row4_3_4, row4_3_8, row4_6_11, row4_7_8, row4_7_10] <;> decide

theorem n4_036 : spectrum 4 [(1, 4), (1, 8), (1, 10), (2, 5), (3, 4), (3, 9), (3, 12), (5, 9), (6, 10)] = [0, 0, 5, 5, 13, 8, 1, 3, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 8), hits 4 (1, 10), hits 4 (2, 5), hits 4 (3, 4), hits 4 (3, 9), hits 4 (3, 12), hits 4 (5, 9), hits 4 (6, 10)] = [0, 0, 5, 5, 13, 8, 1, 3, 0, 0]
  rw [count4, row4_1_4, row4_1_8, row4_1_10, row4_2_5, row4_3_4, row4_3_9, row4_3_12, row4_5_9, row4_6_10] <;> decide

theorem n4_037 : spectrum 4 [(1, 4), (2, 8), (2, 9), (3, 13), (4, 8), (4, 9), (4, 11), (5, 8), (5, 11)] = [0, 0, 4, 9, 8, 10, 2, 1, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (2, 8), hits 4 (2, 9), hits 4 (3, 13), hits 4 (4, 8), hits 4 (4, 9), hits 4 (4, 11), hits 4 (5, 8), hits 4 (5, 11)] = [0, 0, 4, 9, 8, 10, 2, 1, 1, 0]
  rw [count4, row4_1_4, row4_2_8, row4_2_9, row4_3_13, row4_4_8, row4_4_9, row4_4_11, row4_5_8, row4_5_11] <;> decide

theorem n4_038 : spectrum 4 [(1, 4), (1, 10), (2, 5), (2, 12), (2, 13), (3, 5), (3, 8), (5, 8), (6, 10)] = [0, 0, 4, 7, 9, 12, 2, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 10), hits 4 (2, 5), hits 4 (2, 12), hits 4 (2, 13), hits 4 (3, 5), hits 4 (3, 8), hits 4 (5, 8), hits 4 (6, 10)] = [0, 0, 4, 7, 9, 12, 2, 1, 0, 0]
  rw [count4, row4_1_4, row4_1_10, row4_2_5, row4_2_12, row4_2_13, row4_3_5, row4_3_8, row4_5_8, row4_6_10] <;> decide

theorem n4_039 : spectrum 4 [(1, 2), (2, 13), (3, 4), (3, 13), (5, 8), (5, 9), (7, 10)] = [0, 4, 6, 10, 9, 6, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (2, 13), hits 4 (3, 4), hits 4 (3, 13), hits 4 (5, 8), hits 4 (5, 9), hits 4 (7, 10)] = [0, 4, 6, 10, 9, 6, 0, 0]
  rw [count4, row4_1_2, row4_2_13, row4_3_4, row4_3_13, row4_5_8, row4_5_9, row4_7_10] <;> decide

theorem n4_040 : spectrum 4 [(1, 12), (2, 9), (3, 4), (3, 13), (4, 8), (4, 9)] = [1, 0, 21, 0, 12, 0, 1] := by
  change histogram (planes 4).length [hits 4 (1, 12), hits 4 (2, 9), hits 4 (3, 4), hits 4 (3, 13), hits 4 (4, 8), hits 4 (4, 9)] = [1, 0, 21, 0, 12, 0, 1]
  rw [count4, row4_1_12, row4_2_9, row4_3_4, row4_3_13, row4_4_8, row4_4_9] <;> decide

theorem n4_041 : spectrum 4 [(1, 12), (2, 4), (2, 12), (3, 13), (4, 11), (6, 10)] = [0, 6, 8, 12, 7, 2, 0] := by
  change histogram (planes 4).length [hits 4 (1, 12), hits 4 (2, 4), hits 4 (2, 12), hits 4 (3, 13), hits 4 (4, 11), hits 4 (6, 10)] = [0, 6, 8, 12, 7, 2, 0]
  rw [count4, row4_1_12, row4_2_4, row4_2_12, row4_3_13, row4_4_11, row4_6_10] <;> decide

theorem n4_042 : spectrum 4 [(2, 9), (2, 12), (3, 9), (3, 12), (4, 11), (5, 9), (5, 11), (6, 9), (7, 8), (7, 10)] = [0, 0, 3, 5, 7, 12, 5, 3, 0, 0, 0] := by
  change histogram (planes 4).length [hits 4 (2, 9), hits 4 (2, 12), hits 4 (3, 9), hits 4 (3, 12), hits 4 (4, 11), hits 4 (5, 9), hits 4 (5, 11), hits 4 (6, 9), hits 4 (7, 8), hits 4 (7, 10)] = [0, 0, 3, 5, 7, 12, 5, 3, 0, 0, 0]
  rw [count4, row4_2_9, row4_2_12, row4_3_9, row4_3_12, row4_4_11, row4_5_9, row4_5_11, row4_6_9, row4_7_8, row4_7_10] <;> decide

theorem n4_043 : spectrum 4 [(1, 6), (2, 9), (2, 12), (3, 4), (5, 8), (5, 10), (5, 11)] = [1, 0, 6, 14, 12, 2, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (2, 9), hits 4 (2, 12), hits 4 (3, 4), hits 4 (5, 8), hits 4 (5, 10), hits 4 (5, 11)] = [1, 0, 6, 14, 12, 2, 0, 0]
  rw [count4, row4_1_6, row4_2_9, row4_2_12, row4_3_4, row4_5_8, row4_5_10, row4_5_11] <;> decide

theorem n4_044 : spectrum 4 [(1, 2), (1, 6), (1, 8), (2, 5), (3, 5), (4, 10)] = [1, 4, 8, 14, 6, 2, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (1, 6), hits 4 (1, 8), hits 4 (2, 5), hits 4 (3, 5), hits 4 (4, 10)] = [1, 4, 8, 14, 6, 2, 0]
  rw [count4, row4_1_2, row4_1_6, row4_1_8, row4_2_5, row4_3_5, row4_4_10] <;> decide

theorem n4_045 : spectrum 4 [(1, 6), (2, 8), (2, 12), (3, 4), (3, 12), (6, 9), (7, 11)] = [0, 2, 7, 14, 7, 4, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (2, 8), hits 4 (2, 12), hits 4 (3, 4), hits 4 (3, 12), hits 4 (6, 9), hits 4 (7, 11)] = [0, 2, 7, 14, 7, 4, 1, 0]
  rw [count4, row4_1_6, row4_2_8, row4_2_12, row4_3_4, row4_3_12, row4_6_9, row4_7_11] <;> decide

theorem n4_046 : spectrum 4 [(4, 8), (4, 11), (5, 9), (5, 11), (6, 11), (7, 8)] = [1, 3, 9, 16, 4, 1, 1] := by
  change histogram (planes 4).length [hits 4 (4, 8), hits 4 (4, 11), hits 4 (5, 9), hits 4 (5, 11), hits 4 (6, 11), hits 4 (7, 8)] = [1, 3, 9, 16, 4, 1, 1]
  rw [count4, row4_4_8, row4_4_11, row4_5_9, row4_5_11, row4_6_11, row4_7_8] <;> decide

theorem n4_047 : spectrum 4 [(1, 14), (3, 12), (5, 9), (5, 11), (7, 9)] = [1, 8, 12, 10, 2, 2] := by
  change histogram (planes 4).length [hits 4 (1, 14), hits 4 (3, 12), hits 4 (5, 9), hits 4 (5, 11), hits 4 (7, 9)] = [1, 8, 12, 10, 2, 2]
  rw [count4, row4_1_14, row4_3_12, row4_5_9, row4_5_11, row4_7_9] <;> decide

theorem n4_048 : spectrum 4 [(1, 10), (2, 8), (2, 12), (6, 9), (6, 11)] = [2, 3, 16, 12, 1, 1] := by
  change histogram (planes 4).length [hits 4 (1, 10), hits 4 (2, 8), hits 4 (2, 12), hits 4 (6, 9), hits 4 (6, 11)] = [2, 3, 16, 12, 1, 1]
  rw [count4, row4_1_10, row4_2_8, row4_2_12, row4_6_9, row4_6_11] <;> decide

theorem n4_049 : spectrum 4 [(1, 6), (1, 10), (1, 12), (2, 8), (5, 8)] = [2, 6, 12, 10, 5, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (1, 10), hits 4 (1, 12), hits 4 (2, 8), hits 4 (5, 8)] = [2, 6, 12, 10, 5, 0]
  rw [count4, row4_1_6, row4_1_10, row4_1_12, row4_2_8, row4_5_8] <;> decide

theorem n4_050 : spectrum 4 [(1, 4), (1, 6), (1, 8), (3, 9), (3, 12), (3, 13), (4, 9), (5, 11), (6, 8)] = [0, 0, 3, 10, 7, 10, 5, 0, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 6), hits 4 (1, 8), hits 4 (3, 9), hits 4 (3, 12), hits 4 (3, 13), hits 4 (4, 9), hits 4 (5, 11), hits 4 (6, 8)] = [0, 0, 3, 10, 7, 10, 5, 0, 0, 0]
  rw [count4, row4_1_4, row4_1_6, row4_1_8, row4_3_9, row4_3_12, row4_3_13, row4_4_9, row4_5_11, row4_6_8] <;> decide

theorem n4_051 : spectrum 4 [(1, 4), (1, 8), (1, 10), (1, 14), (3, 5), (4, 10), (5, 10), (5, 11), (6, 9), (7, 9)] = [0, 1, 3, 7, 3, 9, 9, 3, 0, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 8), hits 4 (1, 10), hits 4 (1, 14), hits 4 (3, 5), hits 4 (4, 10), hits 4 (5, 10), hits 4 (5, 11), hits 4 (6, 9), hits 4 (7, 9)] = [0, 1, 3, 7, 3, 9, 9, 3, 0, 0, 0]
  rw [count4, row4_1_4, row4_1_8, row4_1_10, row4_1_14, row4_3_5, row4_4_10, row4_5_10, row4_5_11, row4_6_9, row4_7_9] <;> decide

theorem n4_052 : spectrum 4 [(1, 2), (1, 6), (1, 8), (1, 10), (2, 5), (3, 9), (5, 9), (6, 8), (7, 10), (7, 11)] = [0, 0, 2, 6, 10, 8, 6, 2, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (1, 6), hits 4 (1, 8), hits 4 (1, 10), hits 4 (2, 5), hits 4 (3, 9), hits 4 (5, 9), hits 4 (6, 8), hits 4 (7, 10), hits 4 (7, 11)] = [0, 0, 2, 6, 10, 8, 6, 2, 1, 0, 0]
  rw [count4, row4_1_2, row4_1_6, row4_1_8, row4_1_10, row4_2_5, row4_3_9, row4_5_9, row4_6_8, row4_7_10, row4_7_11] <;> decide

theorem n4_053 : spectrum 4 [(1, 2), (1, 6), (3, 13), (6, 10)] = [2, 12, 12, 8, 1] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (1, 6), hits 4 (3, 13), hits 4 (6, 10)] = [2, 12, 12, 8, 1]
  rw [count4, row4_1_2, row4_1_6, row4_3_13, row4_6_10] <;> decide

theorem n4_054 : spectrum 4 [(1, 8), (1, 12), (3, 9), (3, 12), (5, 10), (7, 8)] = [0, 4, 13, 10, 5, 2, 1] := by
  change histogram (planes 4).length [hits 4 (1, 8), hits 4 (1, 12), hits 4 (3, 9), hits 4 (3, 12), hits 4 (5, 10), hits 4 (7, 8)] = [0, 4, 13, 10, 5, 2, 1]
  rw [count4, row4_1_8, row4_1_12, row4_3_9, row4_3_12, row4_5_10, row4_7_8] <;> decide

theorem n4_055 : spectrum 4 [(1, 6), (1, 14), (2, 5), (4, 10), (5, 8), (7, 9), (7, 11)] = [0, 4, 6, 8, 13, 4, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (1, 14), hits 4 (2, 5), hits 4 (4, 10), hits 4 (5, 8), hits 4 (7, 9), hits 4 (7, 11)] = [0, 4, 6, 8, 13, 4, 0, 0]
  rw [count4, row4_1_6, row4_1_14, row4_2_5, row4_4_10, row4_5_8, row4_7_9, row4_7_11] <;> decide

theorem n4_056 : spectrum 4 [(1, 2), (1, 10), (2, 13), (3, 9), (4, 10), (5, 8)] = [1, 3, 10, 12, 8, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (1, 10), hits 4 (2, 13), hits 4 (3, 9), hits 4 (4, 10), hits 4 (5, 8)] = [1, 3, 10, 12, 8, 1, 0]
  rw [count4, row4_1_2, row4_1_10, row4_2_13, row4_3_9, row4_4_10, row4_5_8] <;> decide

theorem n4_057 : spectrum 4 [(1, 2), (1, 10), (2, 9), (3, 8), (3, 9), (3, 13), (4, 10), (5, 9), (7, 11)] = [0, 1, 4, 7, 9, 7, 6, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (1, 10), hits 4 (2, 9), hits 4 (3, 8), hits 4 (3, 9), hits 4 (3, 13), hits 4 (4, 10), hits 4 (5, 9), hits 4 (7, 11)] = [0, 1, 4, 7, 9, 7, 6, 1, 0, 0]
  rw [count4, row4_1_2, row4_1_10, row4_2_9, row4_3_8, row4_3_9, row4_3_13, row4_4_10, row4_5_9, row4_7_11] <;> decide

theorem n4_058 : spectrum 4 [(2, 5), (3, 12), (5, 10), (5, 11), (6, 8), (7, 8), (7, 11)] = [0, 1, 12, 9, 7, 5, 0, 1] := by
  change histogram (planes 4).length [hits 4 (2, 5), hits 4 (3, 12), hits 4 (5, 10), hits 4 (5, 11), hits 4 (6, 8), hits 4 (7, 8), hits 4 (7, 11)] = [0, 1, 12, 9, 7, 5, 0, 1]
  rw [count4, row4_2_5, row4_3_12, row4_5_10, row4_5_11, row4_6_8, row4_7_8, row4_7_11] <;> decide

theorem n4_059 : spectrum 4 [(1, 2), (2, 4), (3, 5), (3, 12), (3, 13), (4, 10), (6, 8), (6, 9)] = [0, 1, 8, 7, 9, 7, 2, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (2, 4), hits 4 (3, 5), hits 4 (3, 12), hits 4 (3, 13), hits 4 (4, 10), hits 4 (6, 8), hits 4 (6, 9)] = [0, 1, 8, 7, 9, 7, 2, 1, 0]
  rw [count4, row4_1_2, row4_2_4, row4_3_5, row4_3_12, row4_3_13, row4_4_10, row4_6_8, row4_6_9] <;> decide

theorem n4_060 : spectrum 4 [(1, 2), (1, 10), (1, 12), (2, 4), (3, 8), (3, 13), (7, 8)] = [0, 1, 9, 14, 5, 5, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (1, 10), hits 4 (1, 12), hits 4 (2, 4), hits 4 (3, 8), hits 4 (3, 13), hits 4 (7, 8)] = [0, 1, 9, 14, 5, 5, 1, 0]
  rw [count4, row4_1_2, row4_1_10, row4_1_12, row4_2_4, row4_3_8, row4_3_13, row4_7_8] <;> decide

theorem n4_061 : spectrum 4 [(1, 4), (3, 12), (4, 9), (5, 10), (7, 9)] = [1, 6, 14, 10, 4, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (3, 12), hits 4 (4, 9), hits 4 (5, 10), hits 4 (7, 9)] = [1, 6, 14, 10, 4, 0]
  rw [count4, row4_1_4, row4_3_12, row4_4_9, row4_5_10, row4_7_9] <;> decide

theorem n4_062 : spectrum 4 [(1, 2), (1, 10), (3, 9), (3, 12), (4, 11), (5, 8), (7, 8)] = [1, 1, 6, 14, 8, 5, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (1, 10), hits 4 (3, 9), hits 4 (3, 12), hits 4 (4, 11), hits 4 (5, 8), hits 4 (7, 8)] = [1, 1, 6, 14, 8, 5, 0, 0]
  rw [count4, row4_1_2, row4_1_10, row4_3_9, row4_3_12, row4_4_11, row4_5_8, row4_7_8] <;> decide

theorem n4_063 : spectrum 4 [(1, 2), (1, 6), (1, 10), (1, 12), (2, 5), (2, 8), (3, 9), (4, 8), (4, 9), (5, 10)] = [0, 0, 3, 4, 9, 10, 7, 2, 0, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (1, 6), hits 4 (1, 10), hits 4 (1, 12), hits 4 (2, 5), hits 4 (2, 8), hits 4 (3, 9), hits 4 (4, 8), hits 4 (4, 9), hits 4 (5, 10)] = [0, 0, 3, 4, 9, 10, 7, 2, 0, 0, 0]
  rw [count4, row4_1_2, row4_1_6, row4_1_10, row4_1_12, row4_2_5, row4_2_8, row4_3_9, row4_4_8, row4_4_9, row4_5_10] <;> decide

theorem n4_064 : spectrum 4 [(1, 4), (1, 6), (1, 12), (2, 12), (4, 8), (5, 11), (6, 8), (7, 11)] = [0, 0, 7, 12, 8, 4, 3, 0, 1] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 6), hits 4 (1, 12), hits 4 (2, 12), hits 4 (4, 8), hits 4 (5, 11), hits 4 (6, 8), hits 4 (7, 11)] = [0, 0, 7, 12, 8, 4, 3, 0, 1]
  rw [count4, row4_1_4, row4_1_6, row4_1_12, row4_2_12, row4_4_8, row4_5_11, row4_6_8, row4_7_11] <;> decide

theorem n4_065 : spectrum 4 [(2, 13), (3, 9), (6, 11), (7, 9), (7, 10)] = [3, 2, 16, 12, 0, 2] := by
  change histogram (planes 4).length [hits 4 (2, 13), hits 4 (3, 9), hits 4 (6, 11), hits 4 (7, 9), hits 4 (7, 10)] = [3, 2, 16, 12, 0, 2]
  rw [count4, row4_2_13, row4_3_9, row4_6_11, row4_7_9, row4_7_10] <;> decide

theorem n4_066 : spectrum 4 [(2, 9), (2, 13), (3, 12), (4, 9), (4, 11), (5, 8), (7, 8), (7, 9)] = [0, 2, 3, 13, 9, 4, 3, 1, 0] := by
  change histogram (planes 4).length [hits 4 (2, 9), hits 4 (2, 13), hits 4 (3, 12), hits 4 (4, 9), hits 4 (4, 11), hits 4 (5, 8), hits 4 (7, 8), hits 4 (7, 9)] = [0, 2, 3, 13, 9, 4, 3, 1, 0]
  rw [count4, row4_2_9, row4_2_13, row4_3_12, row4_4_9, row4_4_11, row4_5_8, row4_7_8, row4_7_9] <;> decide

theorem n4_067 : spectrum 4 [(1, 14), (2, 4), (3, 5), (3, 13), (4, 11), (5, 8), (5, 10), (6, 8)] = [0, 1, 7, 7, 11, 7, 1, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 14), hits 4 (2, 4), hits 4 (3, 5), hits 4 (3, 13), hits 4 (4, 11), hits 4 (5, 8), hits 4 (5, 10), hits 4 (6, 8)] = [0, 1, 7, 7, 11, 7, 1, 1, 0]
  rw [count4, row4_1_14, row4_2_4, row4_3_5, row4_3_13, row4_4_11, row4_5_8, row4_5_10, row4_6_8] <;> decide

theorem n4_068 : spectrum 4 [(3, 4), (3, 9), (5, 9), (5, 10), (7, 11)] = [1, 7, 14, 8, 4, 1] := by
  change histogram (planes 4).length [hits 4 (3, 4), hits 4 (3, 9), hits 4 (5, 9), hits 4 (5, 10), hits 4 (7, 11)] = [1, 7, 14, 8, 4, 1]
  rw [count4, row4_3_4, row4_3_9, row4_5_9, row4_5_10, row4_7_11] <;> decide

theorem n4_069 : spectrum 4 [(1, 12), (2, 9), (3, 13), (4, 10), (4, 11), (5, 10), (5, 11), (6, 11), (7, 8), (7, 10)] = [0, 0, 2, 8, 5, 10, 8, 2, 0, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 12), hits 4 (2, 9), hits 4 (3, 13), hits 4 (4, 10), hits 4 (4, 11), hits 4 (5, 10), hits 4 (5, 11), hits 4 (6, 11), hits 4 (7, 8), hits 4 (7, 10)] = [0, 0, 2, 8, 5, 10, 8, 2, 0, 0, 0]
  rw [count4, row4_1_12, row4_2_9, row4_3_13, row4_4_10, row4_4_11, row4_5_10, row4_5_11, row4_6_11, row4_7_8, row4_7_10] <;> decide

theorem n4_070 : spectrum 4 [(1, 8), (1, 12), (2, 9), (3, 8), (4, 11), (5, 11), (6, 10), (7, 8), (7, 10)] = [0, 2, 1, 4, 15, 10, 3, 0, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 8), hits 4 (1, 12), hits 4 (2, 9), hits 4 (3, 8), hits 4 (4, 11), hits 4 (5, 11), hits 4 (6, 10), hits 4 (7, 8), hits 4 (7, 10)] = [0, 2, 1, 4, 15, 10, 3, 0, 0, 0]
  rw [count4, row4_1_8, row4_1_12, row4_2_9, row4_3_8, row4_4_11, row4_5_11, row4_6_10, row4_7_8, row4_7_10] <;> decide

theorem n4_071 : spectrum 4 [(1, 10), (2, 8), (3, 13), (4, 8), (4, 11), (6, 10)] = [1, 1, 14, 12, 4, 3, 0] := by
  change histogram (planes 4).length [hits 4 (1, 10), hits 4 (2, 8), hits 4 (3, 13), hits 4 (4, 8), hits 4 (4, 11), hits 4 (6, 10)] = [1, 1, 14, 12, 4, 3, 0]
  rw [count4, row4_1_10, row4_2_8, row4_3_13, row4_4_8, row4_4_11, row4_6_10] <;> decide

theorem n4_072 : spectrum 4 [(2, 5), (4, 11), (5, 11), (6, 8), (6, 10), (7, 9)] = [0, 4, 12, 10, 7, 2, 0] := by
  change histogram (planes 4).length [hits 4 (2, 5), hits 4 (4, 11), hits 4 (5, 11), hits 4 (6, 8), hits 4 (6, 10), hits 4 (7, 9)] = [0, 4, 12, 10, 7, 2, 0]
  rw [count4, row4_2_5, row4_4_11, row4_5_11, row4_6_8, row4_6_10, row4_7_9] <;> decide

theorem n4_073 : spectrum 4 [(1, 4), (1, 6), (1, 10), (2, 5), (3, 4), (3, 13), (4, 8), (5, 8), (5, 11), (6, 9)] = [0, 0, 2, 0, 22, 0, 10, 0, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 6), hits 4 (1, 10), hits 4 (2, 5), hits 4 (3, 4), hits 4 (3, 13), hits 4 (4, 8), hits 4 (5, 8), hits 4 (5, 11), hits 4 (6, 9)] = [0, 0, 2, 0, 22, 0, 10, 0, 1, 0, 0]
  rw [count4, row4_1_4, row4_1_6, row4_1_10, row4_2_5, row4_3_4, row4_3_13, row4_4_8, row4_5_8, row4_5_11, row4_6_9] <;> decide

theorem n4_074 : spectrum 4 [(1, 14), (4, 10), (5, 8), (5, 9), (6, 8), (6, 10)] = [0, 5, 10, 12, 5, 3, 0] := by
  change histogram (planes 4).length [hits 4 (1, 14), hits 4 (4, 10), hits 4 (5, 8), hits 4 (5, 9), hits 4 (6, 8), hits 4 (6, 10)] = [0, 5, 10, 12, 5, 3, 0]
  rw [count4, row4_1_14, row4_4_10, row4_5_8, row4_5_9, row4_6_8, row4_6_10] <;> decide

theorem n4_075 : spectrum 4 [(2, 4), (2, 12), (3, 4), (4, 8), (4, 11)] = [3, 6, 10, 10, 6, 0] := by
  change histogram (planes 4).length [hits 4 (2, 4), hits 4 (2, 12), hits 4 (3, 4), hits 4 (4, 8), hits 4 (4, 11)] = [3, 6, 10, 10, 6, 0]
  rw [count4, row4_2_4, row4_2_12, row4_3_4, row4_4_8, row4_4_11] <;> decide

theorem n4_076 : spectrum 4 [(1, 4), (1, 8), (1, 12), (2, 12), (3, 5), (3, 13), (4, 8), (6, 10), (7, 11)] = [0, 2, 2, 6, 11, 8, 6, 0, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 8), hits 4 (1, 12), hits 4 (2, 12), hits 4 (3, 5), hits 4 (3, 13), hits 4 (4, 8), hits 4 (6, 10), hits 4 (7, 11)] = [0, 2, 2, 6, 11, 8, 6, 0, 0, 0]
  rw [count4, row4_1_4, row4_1_8, row4_1_12, row4_2_12, row4_3_5, row4_3_13, row4_4_8, row4_6_10, row4_7_11] <;> decide

theorem n4_077 : spectrum 4 [(1, 12), (3, 12), (3, 13), (5, 9), (5, 10), (6, 10), (6, 11), (7, 8)] = [0, 1, 8, 6, 9, 9, 2, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 12), hits 4 (3, 12), hits 4 (3, 13), hits 4 (5, 9), hits 4 (5, 10), hits 4 (6, 10), hits 4 (6, 11), hits 4 (7, 8)] = [0, 1, 8, 6, 9, 9, 2, 0, 0]
  rw [count4, row4_1_12, row4_3_12, row4_3_13, row4_5_9, row4_5_10, row4_6_10, row4_6_11, row4_7_8] <;> decide

theorem n4_078 : spectrum 4 [(1, 10), (1, 12), (1, 14), (2, 9), (3, 5), (3, 8), (4, 10), (5, 9), (7, 10), (7, 11)] = [0, 0, 2, 4, 11, 10, 6, 2, 0, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 10), hits 4 (1, 12), hits 4 (1, 14), hits 4 (2, 9), hits 4 (3, 5), hits 4 (3, 8), hits 4 (4, 10), hits 4 (5, 9), hits 4 (7, 10), hits 4 (7, 11)] = [0, 0, 2, 4, 11, 10, 6, 2, 0, 0, 0]
  rw [count4, row4_1_10, row4_1_12, row4_1_14, row4_2_9, row4_3_5, row4_3_8, row4_4_10, row4_5_9, row4_7_10, row4_7_11] <;> decide

theorem n4_079 : spectrum 4 [(1, 8), (2, 4), (3, 4), (4, 8), (4, 9), (7, 9)] = [1, 4, 11, 10, 6, 2, 1] := by
  change histogram (planes 4).length [hits 4 (1, 8), hits 4 (2, 4), hits 4 (3, 4), hits 4 (4, 8), hits 4 (4, 9), hits 4 (7, 9)] = [1, 4, 11, 10, 6, 2, 1]
  rw [count4, row4_1_8, row4_2_4, row4_3_4, row4_4_8, row4_4_9, row4_7_9] <;> decide

theorem n4_080 : spectrum 4 [(1, 2), (1, 10), (1, 14), (2, 5), (2, 13), (5, 8), (6, 11), (7, 8), (7, 10)] = [0, 1, 5, 4, 11, 9, 3, 2, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (1, 10), hits 4 (1, 14), hits 4 (2, 5), hits 4 (2, 13), hits 4 (5, 8), hits 4 (6, 11), hits 4 (7, 8), hits 4 (7, 10)] = [0, 1, 5, 4, 11, 9, 3, 2, 0, 0]
  rw [count4, row4_1_2, row4_1_10, row4_1_14, row4_2_5, row4_2_13, row4_5_8, row4_6_11, row4_7_8, row4_7_10] <;> decide

theorem n4_081 : spectrum 4 [(1, 8), (2, 5), (2, 13), (3, 12), (5, 11), (6, 10)] = [0, 3, 10, 16, 5, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 8), hits 4 (2, 5), hits 4 (2, 13), hits 4 (3, 12), hits 4 (5, 11), hits 4 (6, 10)] = [0, 3, 10, 16, 5, 1, 0]
  rw [count4, row4_1_8, row4_2_5, row4_2_13, row4_3_12, row4_5_11, row4_6_10] <;> decide

theorem n4_082 : spectrum 4 [(1, 14), (2, 8), (2, 9), (3, 4), (3, 13), (4, 10), (4, 11), (5, 8), (6, 11), (7, 10)] = [0, 0, 2, 6, 8, 10, 8, 0, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 14), hits 4 (2, 8), hits 4 (2, 9), hits 4 (3, 4), hits 4 (3, 13), hits 4 (4, 10), hits 4 (4, 11), hits 4 (5, 8), hits 4 (6, 11), hits 4 (7, 10)] = [0, 0, 2, 6, 8, 10, 8, 0, 1, 0, 0]
  rw [count4, row4_1_14, row4_2_8, row4_2_9, row4_3_4, row4_3_13, row4_4_10, row4_4_11, row4_5_8, row4_6_11, row4_7_10] <;> decide

theorem n4_083 : spectrum 4 [(2, 4), (2, 9), (3, 4), (3, 12), (4, 9), (6, 9), (7, 9), (7, 11)] = [0, 1, 7, 9, 9, 5, 3, 1, 0] := by
  change histogram (planes 4).length [hits 4 (2, 4), hits 4 (2, 9), hits 4 (3, 4), hits 4 (3, 12), hits 4 (4, 9), hits 4 (6, 9), hits 4 (7, 9), hits 4 (7, 11)] = [0, 1, 7, 9, 9, 5, 3, 1, 0]
  rw [count4, row4_2_4, row4_2_9, row4_3_4, row4_3_12, row4_4_9, row4_6_9, row4_7_9, row4_7_11] <;> decide

theorem n4_084 : spectrum 4 [(1, 14), (3, 4), (3, 9), (3, 13), (4, 8), (4, 11), (5, 8), (5, 11)] = [0, 2, 4, 8, 13, 6, 2, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 14), hits 4 (3, 4), hits 4 (3, 9), hits 4 (3, 13), hits 4 (4, 8), hits 4 (4, 11), hits 4 (5, 8), hits 4 (5, 11)] = [0, 2, 4, 8, 13, 6, 2, 0, 0]
  rw [count4, row4_1_14, row4_3_4, row4_3_9, row4_3_13, row4_4_8, row4_4_11, row4_5_8, row4_5_11] <;> decide

theorem n4_085 : spectrum 4 [(3, 4), (3, 8), (3, 12), (5, 8), (5, 9), (6, 9), (6, 11), (7, 9), (7, 11)] = [0, 0, 3, 10, 11, 4, 5, 2, 0, 0] := by
  change histogram (planes 4).length [hits 4 (3, 4), hits 4 (3, 8), hits 4 (3, 12), hits 4 (5, 8), hits 4 (5, 9), hits 4 (6, 9), hits 4 (6, 11), hits 4 (7, 9), hits 4 (7, 11)] = [0, 0, 3, 10, 11, 4, 5, 2, 0, 0]
  rw [count4, row4_3_4, row4_3_8, row4_3_12, row4_5_8, row4_5_9, row4_6_9, row4_6_11, row4_7_9, row4_7_11] <;> decide

theorem n4_086 : spectrum 4 [(2, 12), (2, 13), (4, 8), (4, 11), (5, 9), (6, 9), (7, 9)] = [0, 3, 7, 12, 7, 5, 1, 0] := by
  change histogram (planes 4).length [hits 4 (2, 12), hits 4 (2, 13), hits 4 (4, 8), hits 4 (4, 11), hits 4 (5, 9), hits 4 (6, 9), hits 4 (7, 9)] = [0, 3, 7, 12, 7, 5, 1, 0]
  rw [count4, row4_2_12, row4_2_13, row4_4_8, row4_4_11, row4_5_9, row4_6_9, row4_7_9] <;> decide

theorem n4_087 : spectrum 4 [(1, 8), (2, 8), (2, 9), (3, 9), (3, 12), (4, 10), (4, 11), (5, 8), (6, 10)] = [0, 0, 6, 3, 11, 12, 2, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 8), hits 4 (2, 8), hits 4 (2, 9), hits 4 (3, 9), hits 4 (3, 12), hits 4 (4, 10), hits 4 (4, 11), hits 4 (5, 8), hits 4 (6, 10)] = [0, 0, 6, 3, 11, 12, 2, 1, 0, 0]
  rw [count4, row4_1_8, row4_2_8, row4_2_9, row4_3_9, row4_3_12, row4_4_10, row4_4_11, row4_5_8, row4_6_10] <;> decide

theorem n4_088 : spectrum 4 [(3, 8), (3, 13), (4, 9), (6, 10)] = [2, 10, 16, 6, 1] := by
  change histogram (planes 4).length [hits 4 (3, 8), hits 4 (3, 13), hits 4 (4, 9), hits 4 (6, 10)] = [2, 10, 16, 6, 1]
  rw [count4, row4_3_8, row4_3_13, row4_4_9, row4_6_10] <;> decide

theorem n4_089 : spectrum 4 [(1, 8), (2, 13), (3, 4), (3, 5), (3, 9), (3, 13), (4, 10), (5, 11), (6, 11)] = [0, 1, 2, 7, 13, 7, 4, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 8), hits 4 (2, 13), hits 4 (3, 4), hits 4 (3, 5), hits 4 (3, 9), hits 4 (3, 13), hits 4 (4, 10), hits 4 (5, 11), hits 4 (6, 11)] = [0, 1, 2, 7, 13, 7, 4, 1, 0, 0]
  rw [count4, row4_1_8, row4_2_13, row4_3_4, row4_3_5, row4_3_9, row4_3_13, row4_4_10, row4_5_11, row4_6_11] <;> decide

theorem n4_090 : spectrum 4 [(1, 8), (1, 14), (2, 8), (2, 9), (2, 12), (4, 9), (4, 11), (5, 8), (5, 11), (6, 10)] = [0, 0, 0, 7, 12, 10, 2, 3, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 8), hits 4 (1, 14), hits 4 (2, 8), hits 4 (2, 9), hits 4 (2, 12), hits 4 (4, 9), hits 4 (4, 11), hits 4 (5, 8), hits 4 (5, 11), hits 4 (6, 10)] = [0, 0, 0, 7, 12, 10, 2, 3, 1, 0, 0]
  rw [count4, row4_1_8, row4_1_14, row4_2_8, row4_2_9, row4_2_12, row4_4_9, row4_4_11, row4_5_8, row4_5_11, row4_6_10] <;> decide

theorem n4_091 : spectrum 4 [(1, 10), (2, 4), (4, 8), (4, 10), (5, 11), (6, 10), (7, 8), (7, 10)] = [0, 2, 5, 8, 9, 10, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 10), hits 4 (2, 4), hits 4 (4, 8), hits 4 (4, 10), hits 4 (5, 11), hits 4 (6, 10), hits 4 (7, 8), hits 4 (7, 10)] = [0, 2, 5, 8, 9, 10, 1, 0, 0]
  rw [count4, row4_1_10, row4_2_4, row4_4_8, row4_4_10, row4_5_11, row4_6_10, row4_7_8, row4_7_10] <;> decide

theorem n4_092 : spectrum 4 [(1, 6), (1, 14), (2, 13), (3, 9), (3, 12), (5, 8), (5, 9), (7, 8), (7, 10)] = [0, 1, 3, 7, 9, 11, 3, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (1, 14), hits 4 (2, 13), hits 4 (3, 9), hits 4 (3, 12), hits 4 (5, 8), hits 4 (5, 9), hits 4 (7, 8), hits 4 (7, 10)] = [0, 1, 3, 7, 9, 11, 3, 1, 0, 0]
  rw [count4, row4_1_6, row4_1_14, row4_2_13, row4_3_9, row4_3_12, row4_5_8, row4_5_9, row4_7_8, row4_7_10] <;> decide

theorem n4_093 : spectrum 4 [(2, 13), (6, 8), (7, 8), (7, 11)] = [1, 14, 12, 6, 2] := by
  change histogram (planes 4).length [hits 4 (2, 13), hits 4 (6, 8), hits 4 (7, 8), hits 4 (7, 11)] = [1, 14, 12, 6, 2]
  rw [count4, row4_2_13, row4_6_8, row4_7_8, row4_7_11] <;> decide

theorem n4_094 : spectrum 4 [(1, 2), (2, 13), (3, 4), (4, 11), (6, 10)] = [2, 0, 26, 0, 7, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (2, 13), hits 4 (3, 4), hits 4 (4, 11), hits 4 (6, 10)] = [2, 0, 26, 0, 7, 0]
  rw [count4, row4_1_2, row4_2_13, row4_3_4, row4_4_11, row4_6_10] <;> decide

theorem n4_095 : spectrum 4 [(1, 4), (1, 12), (2, 12), (3, 12), (4, 8), (6, 10)] = [3, 4, 4, 14, 8, 2, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 12), hits 4 (2, 12), hits 4 (3, 12), hits 4 (4, 8), hits 4 (6, 10)] = [3, 4, 4, 14, 8, 2, 0]
  rw [count4, row4_1_4, row4_1_12, row4_2_12, row4_3_12, row4_4_8, row4_6_10] <;> decide

theorem n4_096 : spectrum 4 [(2, 9), (3, 4), (4, 8), (4, 10), (4, 11), (5, 8), (6, 9), (7, 9), (7, 10)] = [1, 0, 1, 7, 14, 8, 3, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (2, 9), hits 4 (3, 4), hits 4 (4, 8), hits 4 (4, 10), hits 4 (4, 11), hits 4 (5, 8), hits 4 (6, 9), hits 4 (7, 9), hits 4 (7, 10)] = [1, 0, 1, 7, 14, 8, 3, 1, 0, 0]
  rw [count4, row4_2_9, row4_3_4, row4_4_8, row4_4_10, row4_4_11, row4_5_8, row4_6_9, row4_7_9, row4_7_10] <;> decide

theorem n4_097 : spectrum 4 [(1, 6), (3, 4), (3, 12), (3, 13), (5, 8), (5, 9), (6, 10)] = [1, 1, 5, 16, 8, 3, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (3, 4), hits 4 (3, 12), hits 4 (3, 13), hits 4 (5, 8), hits 4 (5, 9), hits 4 (6, 10)] = [1, 1, 5, 16, 8, 3, 1, 0]
  rw [count4, row4_1_6, row4_3_4, row4_3_12, row4_3_13, row4_5_8, row4_5_9, row4_6_10] <;> decide

theorem n4_098 : spectrum 4 [(1, 6), (1, 10), (1, 12), (1, 14), (4, 9), (5, 9), (6, 9)] = [1, 2, 6, 12, 10, 2, 2, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (1, 10), hits 4 (1, 12), hits 4 (1, 14), hits 4 (4, 9), hits 4 (5, 9), hits 4 (6, 9)] = [1, 2, 6, 12, 10, 2, 2, 0]
  rw [count4, row4_1_6, row4_1_10, row4_1_12, row4_1_14, row4_4_9, row4_5_9, row4_6_9] <;> decide

theorem n4_099 : spectrum 4 [(1, 4), (1, 8), (1, 12), (3, 5), (4, 8), (5, 8), (5, 10), (6, 9), (6, 10), (7, 11)] = [1, 0, 0, 7, 8, 10, 6, 3, 0, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 8), hits 4 (1, 12), hits 4 (3, 5), hits 4 (4, 8), hits 4 (5, 8), hits 4 (5, 10), hits 4 (6, 9), hits 4 (6, 10), hits 4 (7, 11)] = [1, 0, 0, 7, 8, 10, 6, 3, 0, 0, 0]
  rw [count4, row4_1_4, row4_1_8, row4_1_12, row4_3_5, row4_4_8, row4_5_8, row4_5_10, row4_6_9, row4_6_10, row4_7_11] <;> decide

theorem n4_100 : spectrum 4 [(2, 8), (3, 12), (5, 9), (7, 10)] = [3, 8, 16, 8, 0] := by
  change histogram (planes 4).length [hits 4 (2, 8), hits 4 (3, 12), hits 4 (5, 9), hits 4 (7, 10)] = [3, 8, 16, 8, 0]
  rw [count4, row4_2_8, row4_3_12, row4_5_9, row4_7_10] <;> decide

theorem n4_101 : spectrum 4 [(1, 2), (2, 4), (2, 5), (2, 9), (2, 13), (4, 10), (7, 11)] = [1, 4, 4, 8, 14, 4, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (2, 4), hits 4 (2, 5), hits 4 (2, 9), hits 4 (2, 13), hits 4 (4, 10), hits 4 (7, 11)] = [1, 4, 4, 8, 14, 4, 0, 0]
  rw [count4, row4_1_2, row4_2_4, row4_2_5, row4_2_9, row4_2_13, row4_4_10, row4_7_11] <;> decide

theorem n4_102 : spectrum 4 [(4, 10), (5, 8), (5, 10), (6, 11), (7, 8), (7, 10)] = [1, 4, 9, 14, 4, 2, 1] := by
  change histogram (planes 4).length [hits 4 (4, 10), hits 4 (5, 8), hits 4 (5, 10), hits 4 (6, 11), hits 4 (7, 8), hits 4 (7, 10)] = [1, 4, 9, 14, 4, 2, 1]
  rw [count4, row4_4_10, row4_5_8, row4_5_10, row4_6_11, row4_7_8, row4_7_10] <;> decide

theorem n4_103 : spectrum 4 [(1, 8), (2, 8), (3, 4), (3, 13), (4, 9), (7, 10)] = [1, 5, 8, 10, 10, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 8), hits 4 (2, 8), hits 4 (3, 4), hits 4 (3, 13), hits 4 (4, 9), hits 4 (7, 10)] = [1, 5, 8, 10, 10, 1, 0]
  rw [count4, row4_1_8, row4_2_8, row4_3_4, row4_3_13, row4_4_9, row4_7_10] <;> decide

theorem n4_104 : spectrum 4 [(1, 8), (2, 4), (2, 9), (5, 10), (6, 9), (6, 11)] = [1, 4, 10, 10, 8, 2, 0] := by
  change histogram (planes 4).length [hits 4 (1, 8), hits 4 (2, 4), hits 4 (2, 9), hits 4 (5, 10), hits 4 (6, 9), hits 4 (6, 11)] = [1, 4, 10, 10, 8, 2, 0]
  rw [count4, row4_1_8, row4_2_4, row4_2_9, row4_5_10, row4_6_9, row4_6_11] <;> decide

theorem n4_105 : spectrum 4 [(1, 6), (1, 10), (1, 12), (3, 9), (7, 8)] = [2, 6, 10, 14, 3, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (1, 10), hits 4 (1, 12), hits 4 (3, 9), hits 4 (7, 8)] = [2, 6, 10, 14, 3, 0]
  rw [count4, row4_1_6, row4_1_10, row4_1_12, row4_3_9, row4_7_8] <;> decide

theorem n4_106 : spectrum 4 [(2, 9), (2, 13), (3, 5), (3, 8), (7, 11)] = [1, 7, 12, 12, 2, 1] := by
  change histogram (planes 4).length [hits 4 (2, 9), hits 4 (2, 13), hits 4 (3, 5), hits 4 (3, 8), hits 4 (7, 11)] = [1, 7, 12, 12, 2, 1]
  rw [count4, row4_2_9, row4_2_13, row4_3_5, row4_3_8, row4_7_11] <;> decide

theorem n4_107 : spectrum 4 [(1, 12), (2, 4), (4, 9), (4, 11), (5, 8), (6, 10), (7, 8)] = [1, 2, 4, 14, 10, 4, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 12), hits 4 (2, 4), hits 4 (4, 9), hits 4 (4, 11), hits 4 (5, 8), hits 4 (6, 10), hits 4 (7, 8)] = [1, 2, 4, 14, 10, 4, 0, 0]
  rw [count4, row4_1_12, row4_2_4, row4_4_9, row4_4_11, row4_5_8, row4_6_10, row4_7_8] <;> decide

theorem n4_108 : spectrum 4 [(2, 12), (2, 13), (3, 13), (4, 10), (5, 10), (6, 9)] = [1, 2, 14, 10, 4, 4, 0] := by
  change histogram (planes 4).length [hits 4 (2, 12), hits 4 (2, 13), hits 4 (3, 13), hits 4 (4, 10), hits 4 (5, 10), hits 4 (6, 9)] = [1, 2, 14, 10, 4, 4, 0]
  rw [count4, row4_2_12, row4_2_13, row4_3_13, row4_4_10, row4_5_10, row4_6_9] <;> decide

theorem n4_109 : spectrum 4 [(1, 12), (2, 5), (2, 8), (2, 12), (3, 4), (3, 8), (3, 13)] = [1, 0, 8, 13, 10, 2, 0, 1] := by
  change histogram (planes 4).length [hits 4 (1, 12), hits 4 (2, 5), hits 4 (2, 8), hits 4 (2, 12), hits 4 (3, 4), hits 4 (3, 8), hits 4 (3, 13)] = [1, 0, 8, 13, 10, 2, 0, 1]
  rw [count4, row4_1_12, row4_2_5, row4_2_8, row4_2_12, row4_3_4, row4_3_8, row4_3_13] <;> decide

theorem n4_110 : spectrum 4 [(2, 8), (3, 5), (3, 9), (3, 12), (4, 10), (6, 11)] = [1, 4, 8, 12, 10, 0, 0] := by
  change histogram (planes 4).length [hits 4 (2, 8), hits 4 (3, 5), hits 4 (3, 9), hits 4 (3, 12), hits 4 (4, 10), hits 4 (6, 11)] = [1, 4, 8, 12, 10, 0, 0]
  rw [count4, row4_2_8, row4_3_5, row4_3_9, row4_3_12, row4_4_10, row4_6_11] <;> decide

theorem n4_111 : spectrum 4 [(1, 12), (2, 9), (3, 12), (5, 9), (6, 9), (7, 9)] = [1, 6, 6, 12, 8, 2, 0] := by
  change histogram (planes 4).length [hits 4 (1, 12), hits 4 (2, 9), hits 4 (3, 12), hits 4 (5, 9), hits 4 (6, 9), hits 4 (7, 9)] = [1, 6, 6, 12, 8, 2, 0]
  rw [count4, row4_1_12, row4_2_9, row4_3_12, row4_5_9, row4_6_9, row4_7_9] <;> decide

theorem n4_112 : spectrum 4 [(1, 12), (2, 12), (3, 9), (4, 9), (5, 9), (5, 11), (7, 9)] = [1, 3, 5, 12, 8, 5, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 12), hits 4 (2, 12), hits 4 (3, 9), hits 4 (4, 9), hits 4 (5, 9), hits 4 (5, 11), hits 4 (7, 9)] = [1, 3, 5, 12, 8, 5, 1, 0]
  rw [count4, row4_1_12, row4_2_12, row4_3_9, row4_4_9, row4_5_9, row4_5_11, row4_7_9] <;> decide

theorem n4_113 : spectrum 4 [(1, 10), (2, 4), (4, 8), (5, 9), (6, 9)] = [1, 5, 16, 10, 2, 1] := by
  change histogram (planes 4).length [hits 4 (1, 10), hits 4 (2, 4), hits 4 (4, 8), hits 4 (5, 9), hits 4 (6, 9)] = [1, 5, 16, 10, 2, 1]
  rw [count4, row4_1_10, row4_2_4, row4_4_8, row4_5_9, row4_6_9] <;> decide

theorem n4_114 : spectrum 4 [(1, 6), (1, 8), (1, 14), (2, 8), (3, 8), (5, 8), (6, 8), (6, 9), (6, 10)] = [1, 2, 0, 7, 10, 10, 4, 1, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (1, 8), hits 4 (1, 14), hits 4 (2, 8), hits 4 (3, 8), hits 4 (5, 8), hits 4 (6, 8), hits 4 (6, 9), hits 4 (6, 10)] = [1, 2, 0, 7, 10, 10, 4, 1, 0, 0]
  rw [count4, row4_1_6, row4_1_8, row4_1_14, row4_2_8, row4_3_8, row4_5_8, row4_6_8, row4_6_9, row4_6_10] <;> decide

theorem n4_115 : spectrum 4 [(1, 6), (3, 13), (4, 10), (6, 9), (7, 11)] = [1, 6, 12, 14, 2, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (3, 13), hits 4 (4, 10), hits 4 (6, 9), hits 4 (7, 11)] = [1, 6, 12, 14, 2, 0]
  rw [count4, row4_1_6, row4_3_13, row4_4_10, row4_6_9, row4_7_11] <;> decide

theorem n4_116 : spectrum 4 [(1, 6), (2, 8), (2, 9), (3, 9), (5, 10), (5, 11), (6, 11)] = [1, 0, 7, 16, 6, 4, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (2, 8), hits 4 (2, 9), hits 4 (3, 9), hits 4 (5, 10), hits 4 (5, 11), hits 4 (6, 11)] = [1, 0, 7, 16, 6, 4, 1, 0]
  rw [count4, row4_1_6, row4_2_8, row4_2_9, row4_3_9, row4_5_10, row4_5_11, row4_6_11] <;> decide

theorem n4_117 : spectrum 4 [(1, 2), (2, 4), (2, 8), (3, 9), (6, 8), (6, 10), (7, 8)] = [1, 0, 11, 10, 6, 6, 1, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (2, 4), hits 4 (2, 8), hits 4 (3, 9), hits 4 (6, 8), hits 4 (6, 10), hits 4 (7, 8)] = [1, 0, 11, 10, 6, 6, 1, 0]
  rw [count4, row4_1_2, row4_2_4, row4_2_8, row4_3_9, row4_6_8, row4_6_10, row4_7_8] <;> decide

theorem n4_118 : spectrum 4 [(1, 4), (1, 6), (1, 10), (1, 14), (3, 4), (3, 5), (3, 13)] = [1, 2, 6, 14, 6, 4, 2, 0] := by
  change histogram (planes 4).length [hits 4 (1, 4), hits 4 (1, 6), hits 4 (1, 10), hits 4 (1, 14), hits 4 (3, 4), hits 4 (3, 5), hits 4 (3, 13)] = [1, 2, 6, 14, 6, 4, 2, 0]
  rw [count4, row4_1_4, row4_1_6, row4_1_10, row4_1_14, row4_3_4, row4_3_5, row4_3_13] <;> decide

theorem n4_119 : spectrum 4 [(1, 2), (1, 14), (2, 12), (2, 13), (3, 13), (5, 11)] = [3, 4, 6, 10, 10, 2, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (1, 14), hits 4 (2, 12), hits 4 (2, 13), hits 4 (3, 13), hits 4 (5, 11)] = [3, 4, 6, 10, 10, 2, 0]
  rw [count4, row4_1_2, row4_1_14, row4_2_12, row4_2_13, row4_3_13, row4_5_11] <;> decide

theorem n4_120 : spectrum 4 [(1, 8), (2, 8), (3, 13), (5, 8), (6, 8)] = [3, 4, 14, 10, 2, 2] := by
  change histogram (planes 4).length [hits 4 (1, 8), hits 4 (2, 8), hits 4 (3, 13), hits 4 (5, 8), hits 4 (6, 8)] = [3, 4, 14, 10, 2, 2]
  rw [count4, row4_1_8, row4_2_8, row4_3_13, row4_5_8, row4_6_8] <;> decide

theorem n4_121 : spectrum 4 [(1, 6), (2, 12), (3, 5), (4, 10), (6, 10)] = [3, 0, 24, 0, 8, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (2, 12), hits 4 (3, 5), hits 4 (4, 10), hits 4 (6, 10)] = [3, 0, 24, 0, 8, 0]
  rw [count4, row4_1_6, row4_2_12, row4_3_5, row4_4_10, row4_6_10] <;> decide

theorem n4_122 : spectrum 4 [(1, 6), (2, 5), (2, 8), (2, 9), (3, 4)] = [3, 4, 12, 12, 4, 0] := by
  change histogram (planes 4).length [hits 4 (1, 6), hits 4 (2, 5), hits 4 (2, 8), hits 4 (2, 9), hits 4 (3, 4)] = [3, 4, 12, 12, 4, 0]
  rw [count4, row4_1_6, row4_2_5, row4_2_8, row4_2_9, row4_3_4] <;> decide

theorem n4_123 : spectrum 4 [(1, 2), (1, 10), (1, 12), (6, 8), (6, 9), (6, 10), (7, 10), (7, 11)] = [1, 2, 2, 8, 12, 10, 0, 0, 0] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (1, 10), hits 4 (1, 12), hits 4 (6, 8), hits 4 (6, 9), hits 4 (6, 10), hits 4 (7, 10), hits 4 (7, 11)] = [1, 2, 2, 8, 12, 10, 0, 0, 0]
  rw [count4, row4_1_2, row4_1_10, row4_1_12, row4_6_8, row4_6_9, row4_6_10, row4_7_10, row4_7_11] <;> decide

theorem n4_124 : spectrum 4 [(2, 4), (2, 5), (2, 9), (2, 12), (4, 9), (4, 11), (5, 8), (7, 8)] = [1, 0, 5, 10, 10, 6, 3, 0, 0] := by
  change histogram (planes 4).length [hits 4 (2, 4), hits 4 (2, 5), hits 4 (2, 9), hits 4 (2, 12), hits 4 (4, 9), hits 4 (4, 11), hits 4 (5, 8), hits 4 (7, 8)] = [1, 0, 5, 10, 10, 6, 3, 0, 0]
  rw [count4, row4_2_4, row4_2_5, row4_2_9, row4_2_12, row4_4_9, row4_4_11, row4_5_8, row4_7_8] <;> decide

theorem n4_125 : spectrum 4 [(1, 2), (3, 5), (3, 13), (6, 11), (7, 10)] = [1, 9, 10, 10, 4, 1] := by
  change histogram (planes 4).length [hits 4 (1, 2), hits 4 (3, 5), hits 4 (3, 13), hits 4 (6, 11), hits 4 (7, 10)] = [1, 9, 10, 10, 4, 1]
  rw [count4, row4_1_2, row4_3_5, row4_3_13, row4_6_11, row4_7_10] <;> decide

private theorem layout5 : planes 5 = [(1, 2), (1, 4), (1, 6), (1, 8), (1, 10), (1, 12), (1, 14), (1, 16), (1, 18), (1, 20), (1, 22), (1, 24), (1, 26), (1, 28), (1, 30), (2, 4), (2, 5), (2, 8), (2, 9), (2, 12), (2, 13), (2, 16), (2, 17), (2, 20), (2, 21), (2, 24), (2, 25), (2, 28), (2, 29), (3, 4), (3, 5), (3, 8), (3, 9), (3, 12), (3, 13), (3, 16), (3, 17), (3, 20), (3, 21), (3, 24), (3, 25), (3, 28), (3, 29), (4, 8), (4, 9), (4, 10), (4, 11), (4, 16), (4, 17), (4, 18), (4, 19), (4, 24), (4, 25), (4, 26), (4, 27), (5, 8), (5, 9), (5, 10), (5, 11), (5, 16), (5, 17), (5, 18), (5, 19), (5, 24), (5, 25), (5, 26), (5, 27), (6, 8), (6, 9), (6, 10), (6, 11), (6, 16), (6, 17), (6, 18), (6, 19), (6, 24), (6, 25), (6, 26), (6, 27), (7, 8), (7, 9), (7, 10), (7, 11), (7, 16), (7, 17), (7, 18), (7, 19), (7, 24), (7, 25), (7, 26), (7, 27), (8, 16), (8, 17), (8, 18), (8, 19), (8, 20), (8, 21), (8, 22), (8, 23), (9, 16), (9, 17), (9, 18), (9, 19), (9, 20), (9, 21), (9, 22), (9, 23), (10, 16), (10, 17), (10, 18), (10, 19), (10, 20), (10, 21), (10, 22), (10, 23), (11, 16), (11, 17), (11, 18), (11, 19), (11, 20), (11, 21), (11, 22), (11, 23), (12, 16), (12, 17), (12, 18), (12, 19), (12, 20), (12, 21), (12, 22), (12, 23), (13, 16), (13, 17), (13, 18), (13, 19), (13, 20), (13, 21), (13, 22), (13, 23), (14, 16), (14, 17), (14, 18), (14, 19), (14, 20), (14, 21), (14, 22), (14, 23), (15, 16), (15, 17), (15, 18), (15, 19), (15, 20), (15, 21), (15, 22), (15, 23)] := by decide
private theorem count5 : (planes 5).length = 155 := by rw [layout5] <;> decide
private theorem row5_1_2 : hits 5 (1, 2) = [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_1_4 : hits 5 (1, 4) = [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_1_6 : hits 5 (1, 6) = [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_1_8 : hits 5 (1, 8) = [0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_1_10 : hits 5 (1, 10) = [1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_1_12 : hits 5 (1, 12) = [0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_1_14 : hits 5 (1, 14) = [1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_1_16 : hits 5 (1, 16) = [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_1_18 : hits 5 (1, 18) = [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_1_20 : hits 5 (1, 20) = [0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_1_22 : hits 5 (1, 22) = [1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_1_24 : hits 5 (1, 24) = [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_1_26 : hits 5 (1, 26) = [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_1_28 : hits 5 (1, 28) = [0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_1_30 : hits 5 (1, 30) = [1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_2_4 : hits 5 (2, 4) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_2_5 : hits 5 (2, 5) = [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_2_8 : hits 5 (2, 8) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_2_9 : hits 5 (2, 9) = [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_2_12 : hits 5 (2, 12) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_2_13 : hits 5 (2, 13) = [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_2_16 : hits 5 (2, 16) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_2_17 : hits 5 (2, 17) = [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_2_20 : hits 5 (2, 20) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_2_21 : hits 5 (2, 21) = [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_2_24 : hits 5 (2, 24) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_2_25 : hits 5 (2, 25) = [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_2_28 : hits 5 (2, 28) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_2_29 : hits 5 (2, 29) = [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_3_4 : hits 5 (3, 4) = [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_3_5 : hits 5 (3, 5) = [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_3_8 : hits 5 (3, 8) = [0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_3_9 : hits 5 (3, 9) = [1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_3_12 : hits 5 (3, 12) = [0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_3_13 : hits 5 (3, 13) = [1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_3_16 : hits 5 (3, 16) = [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_3_17 : hits 5 (3, 17) = [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_3_20 : hits 5 (3, 20) = [0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_3_21 : hits 5 (3, 21) = [1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_3_24 : hits 5 (3, 24) = [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_3_25 : hits 5 (3, 25) = [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_3_28 : hits 5 (3, 28) = [0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_3_29 : hits 5 (3, 29) = [1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_4_8 : hits 5 (4, 8) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_4_9 : hits 5 (4, 9) = [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_4_10 : hits 5 (4, 10) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_4_11 : hits 5 (4, 11) = [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_4_16 : hits 5 (4, 16) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_4_17 : hits 5 (4, 17) = [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_4_18 : hits 5 (4, 18) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_4_19 : hits 5 (4, 19) = [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_4_24 : hits 5 (4, 24) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_4_25 : hits 5 (4, 25) = [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_4_26 : hits 5 (4, 26) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_4_27 : hits 5 (4, 27) = [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_5_8 : hits 5 (5, 8) = [0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_5_9 : hits 5 (5, 9) = [0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_5_10 : hits 5 (5, 10) = [1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_5_11 : hits 5 (5, 11) = [1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_5_16 : hits 5 (5, 16) = [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_5_17 : hits 5 (5, 17) = [0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_5_18 : hits 5 (5, 18) = [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_5_19 : hits 5 (5, 19) = [1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_5_24 : hits 5 (5, 24) = [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_5_25 : hits 5 (5, 25) = [0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_5_26 : hits 5 (5, 26) = [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_5_27 : hits 5 (5, 27) = [1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_6_8 : hits 5 (6, 8) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_6_9 : hits 5 (6, 9) = [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_6_10 : hits 5 (6, 10) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_6_11 : hits 5 (6, 11) = [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_6_16 : hits 5 (6, 16) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_6_17 : hits 5 (6, 17) = [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_6_18 : hits 5 (6, 18) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_6_19 : hits 5 (6, 19) = [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_6_24 : hits 5 (6, 24) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_6_25 : hits 5 (6, 25) = [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_6_26 : hits 5 (6, 26) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_6_27 : hits 5 (6, 27) = [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_7_8 : hits 5 (7, 8) = [0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_7_9 : hits 5 (7, 9) = [1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_7_10 : hits 5 (7, 10) = [1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_7_11 : hits 5 (7, 11) = [0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_7_16 : hits 5 (7, 16) = [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_7_17 : hits 5 (7, 17) = [1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_7_18 : hits 5 (7, 18) = [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_7_19 : hits 5 (7, 19) = [0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_7_24 : hits 5 (7, 24) = [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_7_25 : hits 5 (7, 25) = [1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_7_26 : hits 5 (7, 26) = [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_7_27 : hits 5 (7, 27) = [0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_8_16 : hits 5 (8, 16) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_8_17 : hits 5 (8, 17) = [0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_8_18 : hits 5 (8, 18) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_8_19 : hits 5 (8, 19) = [0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_8_20 : hits 5 (8, 20) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_8_21 : hits 5 (8, 21) = [0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_8_22 : hits 5 (8, 22) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_8_23 : hits 5 (8, 23) = [0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_9_16 : hits 5 (9, 16) = [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_9_17 : hits 5 (9, 17) = [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_9_18 : hits 5 (9, 18) = [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_9_19 : hits 5 (9, 19) = [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_9_20 : hits 5 (9, 20) = [0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_9_21 : hits 5 (9, 21) = [0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_9_22 : hits 5 (9, 22) = [1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_9_23 : hits 5 (9, 23) = [1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_10_16 : hits 5 (10, 16) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_10_17 : hits 5 (10, 17) = [1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_10_18 : hits 5 (10, 18) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_10_19 : hits 5 (10, 19) = [1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_10_20 : hits 5 (10, 20) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_10_21 : hits 5 (10, 21) = [1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_10_22 : hits 5 (10, 22) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_10_23 : hits 5 (10, 23) = [1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_11_16 : hits 5 (11, 16) = [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_11_17 : hits 5 (11, 17) = [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_11_18 : hits 5 (11, 18) = [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_11_19 : hits 5 (11, 19) = [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_11_20 : hits 5 (11, 20) = [0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_11_21 : hits 5 (11, 21) = [1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_11_22 : hits 5 (11, 22) = [1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_11_23 : hits 5 (11, 23) = [0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_12_16 : hits 5 (12, 16) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_12_17 : hits 5 (12, 17) = [0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_12_18 : hits 5 (12, 18) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_12_19 : hits 5 (12, 19) = [0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_12_20 : hits 5 (12, 20) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_12_21 : hits 5 (12, 21) = [0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_12_22 : hits 5 (12, 22) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_12_23 : hits 5 (12, 23) = [0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_13_16 : hits 5 (13, 16) = [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_13_17 : hits 5 (13, 17) = [0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_13_18 : hits 5 (13, 18) = [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_13_19 : hits 5 (13, 19) = [1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_13_20 : hits 5 (13, 20) = [0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_13_21 : hits 5 (13, 21) = [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_13_22 : hits 5 (13, 22) = [1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_13_23 : hits 5 (13, 23) = [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_14_16 : hits 5 (14, 16) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_14_17 : hits 5 (14, 17) = [1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_14_18 : hits 5 (14, 18) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_14_19 : hits 5 (14, 19) = [1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_14_20 : hits 5 (14, 20) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_14_21 : hits 5 (14, 21) = [1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_14_22 : hits 5 (14, 22) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1] := by rw [hits, layout5] <;> decide
private theorem row5_14_23 : hits 5 (14, 23) = [1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] := by rw [hits, layout5] <;> decide
private theorem row5_15_16 : hits 5 (15, 16) = [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_15_17 : hits 5 (15, 17) = [1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_15_18 : hits 5 (15, 18) = [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_15_19 : hits 5 (15, 19) = [0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_15_20 : hits 5 (15, 20) = [0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
private theorem row5_15_21 : hits 5 (15, 21) = [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_15_22 : hits 5 (15, 22) = [1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rw [hits, layout5] <;> decide
private theorem row5_15_23 : hits 5 (15, 23) = [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] := by rw [hits, layout5] <;> decide
theorem n5_001 : spectrum 5 [(3, 16), (4, 25), (6, 25), (9, 20), (12, 16), (12, 19), (12, 23), (13, 19)] = [1, 17, 29, 40, 36, 21, 9, 2, 0] := by
  change histogram (planes 5).length [hits 5 (3, 16), hits 5 (4, 25), hits 5 (6, 25), hits 5 (9, 20), hits 5 (12, 16), hits 5 (12, 19), hits 5 (12, 23), hits 5 (13, 19)] = [1, 17, 29, 40, 36, 21, 9, 2, 0]
  rw [count5, row5_3_16, row5_4_25, row5_6_25, row5_9_20, row5_12_16, row5_12_19, row5_12_23, row5_13_19] <;> decide

theorem n5_002 : spectrum 5 [(1, 14), (1, 20), (2, 4), (2, 21), (4, 18), (6, 27), (7, 25), (9, 16), (9, 23), (11, 17), (12, 19)] = [0, 1, 7, 29, 41, 39, 25, 11, 2, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 14), hits 5 (1, 20), hits 5 (2, 4), hits 5 (2, 21), hits 5 (4, 18), hits 5 (6, 27), hits 5 (7, 25), hits 5 (9, 16), hits 5 (9, 23), hits 5 (11, 17), hits 5 (12, 19)] = [0, 1, 7, 29, 41, 39, 25, 11, 2, 0, 0, 0]
  rw [count5, row5_1_14, row5_1_20, row5_2_4, row5_2_21, row5_4_18, row5_6_27, row5_7_25, row5_9_16, row5_9_23, row5_11_17, row5_12_19] <;> decide

theorem n5_003 : spectrum 5 [(1, 4), (2, 29), (3, 8), (3, 29), (4, 27), (7, 18), (8, 21), (10, 23), (11, 19), (12, 16), (12, 21), (12, 23), (13, 16)] = [0, 1, 5, 19, 27, 32, 28, 23, 14, 5, 1, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 4), hits 5 (2, 29), hits 5 (3, 8), hits 5 (3, 29), hits 5 (4, 27), hits 5 (7, 18), hits 5 (8, 21), hits 5 (10, 23), hits 5 (11, 19), hits 5 (12, 16), hits 5 (12, 21), hits 5 (12, 23), hits 5 (13, 16)] = [0, 1, 5, 19, 27, 32, 28, 23, 14, 5, 1, 0, 0, 0]
  rw [count5, row5_1_4, row5_2_29, row5_3_8, row5_3_29, row5_4_27, row5_7_18, row5_8_21, row5_10_23, row5_11_19, row5_12_16, row5_12_21, row5_12_23, row5_13_16] <;> decide

theorem n5_004 : spectrum 5 [(1, 14), (2, 17), (2, 29), (4, 17), (5, 27), (6, 8), (6, 16), (7, 17), (7, 26), (10, 19), (10, 20), (10, 21), (13, 16), (14, 21)] = [0, 1, 3, 13, 16, 30, 42, 30, 11, 5, 3, 1, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 14), hits 5 (2, 17), hits 5 (2, 29), hits 5 (4, 17), hits 5 (5, 27), hits 5 (6, 8), hits 5 (6, 16), hits 5 (7, 17), hits 5 (7, 26), hits 5 (10, 19), hits 5 (10, 20), hits 5 (10, 21), hits 5 (13, 16), hits 5 (14, 21)] = [0, 1, 3, 13, 16, 30, 42, 30, 11, 5, 3, 1, 0, 0, 0]
  rw [count5, row5_1_14, row5_2_17, row5_2_29, row5_4_17, row5_5_27, row5_6_8, row5_6_16, row5_7_17, row5_7_26, row5_10_19, row5_10_20, row5_10_21, row5_13_16, row5_14_21] <;> decide

theorem n5_005 : spectrum 5 [(1, 8), (1, 12), (1, 14), (2, 29), (5, 26), (6, 16), (6, 19), (7, 18), (8, 22), (9, 16), (11, 19), (14, 19), (15, 18)] = [0, 1, 5, 12, 31, 30, 43, 16, 12, 5, 0, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 8), hits 5 (1, 12), hits 5 (1, 14), hits 5 (2, 29), hits 5 (5, 26), hits 5 (6, 16), hits 5 (6, 19), hits 5 (7, 18), hits 5 (8, 22), hits 5 (9, 16), hits 5 (11, 19), hits 5 (14, 19), hits 5 (15, 18)] = [0, 1, 5, 12, 31, 30, 43, 16, 12, 5, 0, 0, 0, 0]
  rw [count5, row5_1_8, row5_1_12, row5_1_14, row5_2_29, row5_5_26, row5_6_16, row5_6_19, row5_7_18, row5_8_22, row5_9_16, row5_11_19, row5_14_19, row5_15_18] <;> decide

theorem n5_006 : spectrum 5 [(1, 30), (5, 9), (5, 11), (6, 25), (8, 16), (9, 18), (11, 17), (14, 18)] = [2, 6, 35, 50, 33, 22, 5, 2, 0] := by
  change histogram (planes 5).length [hits 5 (1, 30), hits 5 (5, 9), hits 5 (5, 11), hits 5 (6, 25), hits 5 (8, 16), hits 5 (9, 18), hits 5 (11, 17), hits 5 (14, 18)] = [2, 6, 35, 50, 33, 22, 5, 2, 0]
  rw [count5, row5_1_30, row5_5_9, row5_5_11, row5_6_25, row5_8_16, row5_9_18, row5_11_17, row5_14_18] <;> decide

theorem n5_007 : spectrum 5 [(3, 16), (4, 10), (5, 18), (5, 25), (7, 18), (7, 24), (8, 22), (9, 21), (10, 22), (14, 22)] = [0, 6, 21, 27, 32, 40, 21, 7, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (3, 16), hits 5 (4, 10), hits 5 (5, 18), hits 5 (5, 25), hits 5 (7, 18), hits 5 (7, 24), hits 5 (8, 22), hits 5 (9, 21), hits 5 (10, 22), hits 5 (14, 22)] = [0, 6, 21, 27, 32, 40, 21, 7, 1, 0, 0]
  rw [count5, row5_3_16, row5_4_10, row5_5_18, row5_5_25, row5_7_18, row5_7_24, row5_8_22, row5_9_21, row5_10_22, row5_14_22] <;> decide

theorem n5_008 : spectrum 5 [(1, 24), (2, 21), (3, 4), (4, 9), (4, 16), (5, 10), (5, 18), (6, 11), (10, 17), (10, 23), (11, 17), (13, 18), (14, 17), (15, 17)] = [0, 0, 2, 15, 20, 32, 31, 27, 21, 6, 1, 0, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 24), hits 5 (2, 21), hits 5 (3, 4), hits 5 (4, 9), hits 5 (4, 16), hits 5 (5, 10), hits 5 (5, 18), hits 5 (6, 11), hits 5 (10, 17), hits 5 (10, 23), hits 5 (11, 17), hits 5 (13, 18), hits 5 (14, 17), hits 5 (15, 17)] = [0, 0, 2, 15, 20, 32, 31, 27, 21, 6, 1, 0, 0, 0, 0]
  rw [count5, row5_1_24, row5_2_21, row5_3_4, row5_4_9, row5_4_16, row5_5_10, row5_5_18, row5_6_11, row5_10_17, row5_10_23, row5_11_17, row5_13_18, row5_14_17, row5_15_17] <;> decide

theorem n5_009 : spectrum 5 [(1, 10), (1, 14), (3, 13), (3, 25), (4, 27), (6, 17), (7, 19), (9, 17), (9, 21), (10, 21), (11, 17), (14, 19), (15, 22)] = [0, 0, 3, 13, 32, 40, 31, 21, 9, 6, 0, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 10), hits 5 (1, 14), hits 5 (3, 13), hits 5 (3, 25), hits 5 (4, 27), hits 5 (6, 17), hits 5 (7, 19), hits 5 (9, 17), hits 5 (9, 21), hits 5 (10, 21), hits 5 (11, 17), hits 5 (14, 19), hits 5 (15, 22)] = [0, 0, 3, 13, 32, 40, 31, 21, 9, 6, 0, 0, 0, 0]
  rw [count5, row5_1_10, row5_1_14, row5_3_13, row5_3_25, row5_4_27, row5_6_17, row5_7_19, row5_9_17, row5_9_21, row5_10_21, row5_11_17, row5_14_19, row5_15_22] <;> decide

theorem n5_010 : spectrum 5 [(1, 2), (2, 12), (2, 25), (3, 12), (7, 27), (8, 16), (8, 17), (9, 16), (15, 21), (15, 22)] = [1, 7, 18, 29, 38, 33, 14, 11, 4, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 2), hits 5 (2, 12), hits 5 (2, 25), hits 5 (3, 12), hits 5 (7, 27), hits 5 (8, 16), hits 5 (8, 17), hits 5 (9, 16), hits 5 (15, 21), hits 5 (15, 22)] = [1, 7, 18, 29, 38, 33, 14, 11, 4, 0, 0]
  rw [count5, row5_1_2, row5_2_12, row5_2_25, row5_3_12, row5_7_27, row5_8_16, row5_8_17, row5_9_16, row5_15_21, row5_15_22] <;> decide

theorem n5_011 : spectrum 5 [(1, 10), (2, 9), (3, 16), (7, 27), (9, 22), (13, 23), (15, 21)] = [1, 16, 42, 52, 30, 12, 2, 0] := by
  change histogram (planes 5).length [hits 5 (1, 10), hits 5 (2, 9), hits 5 (3, 16), hits 5 (7, 27), hits 5 (9, 22), hits 5 (13, 23), hits 5 (15, 21)] = [1, 16, 42, 52, 30, 12, 2, 0]
  rw [count5, row5_1_10, row5_2_9, row5_3_16, row5_7_27, row5_9_22, row5_13_23, row5_15_21] <;> decide

theorem n5_012 : spectrum 5 [(1, 12), (2, 25), (4, 11), (5, 27), (6, 8), (6, 11), (9, 21), (11, 16), (11, 23), (13, 18), (15, 19), (15, 20)] = [0, 1, 10, 24, 31, 33, 24, 18, 10, 4, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 12), hits 5 (2, 25), hits 5 (4, 11), hits 5 (5, 27), hits 5 (6, 8), hits 5 (6, 11), hits 5 (9, 21), hits 5 (11, 16), hits 5 (11, 23), hits 5 (13, 18), hits 5 (15, 19), hits 5 (15, 20)] = [0, 1, 10, 24, 31, 33, 24, 18, 10, 4, 0, 0, 0]
  rw [count5, row5_1_12, row5_2_25, row5_4_11, row5_5_27, row5_6_8, row5_6_11, row5_9_21, row5_11_16, row5_11_23, row5_13_18, row5_15_19, row5_15_20] <;> decide

theorem n5_013 : spectrum 5 [(2, 8), (2, 20), (3, 12), (3, 20), (3, 28), (6, 16), (6, 19), (6, 27), (7, 10), (7, 11), (8, 20), (12, 21), (14, 17), (14, 19)] = [0, 0, 3, 11, 21, 33, 38, 26, 12, 9, 1, 1, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 8), hits 5 (2, 20), hits 5 (3, 12), hits 5 (3, 20), hits 5 (3, 28), hits 5 (6, 16), hits 5 (6, 19), hits 5 (6, 27), hits 5 (7, 10), hits 5 (7, 11), hits 5 (8, 20), hits 5 (12, 21), hits 5 (14, 17), hits 5 (14, 19)] = [0, 0, 3, 11, 21, 33, 38, 26, 12, 9, 1, 1, 0, 0, 0]
  rw [count5, row5_2_8, row5_2_20, row5_3_12, row5_3_20, row5_3_28, row5_6_16, row5_6_19, row5_6_27, row5_7_10, row5_7_11, row5_8_20, row5_12_21, row5_14_17, row5_14_19] <;> decide

theorem n5_014 : spectrum 5 [(4, 18), (4, 24), (5, 16), (5, 25), (5, 26), (6, 11), (6, 26), (13, 18), (13, 20), (13, 21), (14, 17), (14, 19), (15, 18), (15, 20)] = [0, 0, 4, 10, 26, 35, 26, 26, 17, 8, 2, 0, 0, 1, 0] := by
  change histogram (planes 5).length [hits 5 (4, 18), hits 5 (4, 24), hits 5 (5, 16), hits 5 (5, 25), hits 5 (5, 26), hits 5 (6, 11), hits 5 (6, 26), hits 5 (13, 18), hits 5 (13, 20), hits 5 (13, 21), hits 5 (14, 17), hits 5 (14, 19), hits 5 (15, 18), hits 5 (15, 20)] = [0, 0, 4, 10, 26, 35, 26, 26, 17, 8, 2, 0, 0, 1, 0]
  rw [count5, row5_4_18, row5_4_24, row5_5_16, row5_5_25, row5_5_26, row5_6_11, row5_6_26, row5_13_18, row5_13_20, row5_13_21, row5_14_17, row5_14_19, row5_15_18, row5_15_20] <;> decide

theorem n5_015 : spectrum 5 [(1, 16), (3, 21), (3, 24), (6, 19), (6, 26), (10, 20), (10, 21), (11, 23), (13, 20)] = [0, 8, 21, 41, 40, 30, 13, 1, 1, 0] := by
  change histogram (planes 5).length [hits 5 (1, 16), hits 5 (3, 21), hits 5 (3, 24), hits 5 (6, 19), hits 5 (6, 26), hits 5 (10, 20), hits 5 (10, 21), hits 5 (11, 23), hits 5 (13, 20)] = [0, 8, 21, 41, 40, 30, 13, 1, 1, 0]
  rw [count5, row5_1_16, row5_3_21, row5_3_24, row5_6_19, row5_6_26, row5_10_20, row5_10_21, row5_11_23, row5_13_20] <;> decide

theorem n5_016 : spectrum 5 [(1, 18), (5, 9), (6, 24), (6, 26), (7, 17), (12, 22), (14, 18)] = [1, 19, 45, 44, 28, 15, 1, 2] := by
  change histogram (planes 5).length [hits 5 (1, 18), hits 5 (5, 9), hits 5 (6, 24), hits 5 (6, 26), hits 5 (7, 17), hits 5 (12, 22), hits 5 (14, 18)] = [1, 19, 45, 44, 28, 15, 1, 2]
  rw [count5, row5_1_18, row5_5_9, row5_6_24, row5_6_26, row5_7_17, row5_12_22, row5_14_18] <;> decide

theorem n5_017 : spectrum 5 [(2, 4), (2, 5), (2, 13), (2, 17), (3, 8), (3, 17), (3, 25), (3, 29), (9, 17), (12, 16), (13, 19)] = [1, 2, 20, 18, 27, 47, 22, 12, 5, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 4), hits 5 (2, 5), hits 5 (2, 13), hits 5 (2, 17), hits 5 (3, 8), hits 5 (3, 17), hits 5 (3, 25), hits 5 (3, 29), hits 5 (9, 17), hits 5 (12, 16), hits 5 (13, 19)] = [1, 2, 20, 18, 27, 47, 22, 12, 5, 1, 0, 0]
  rw [count5, row5_2_4, row5_2_5, row5_2_13, row5_2_17, row5_3_8, row5_3_17, row5_3_25, row5_3_29, row5_9_17, row5_12_16, row5_13_19] <;> decide

theorem n5_018 : spectrum 5 [(1, 2), (2, 12), (2, 13), (2, 25), (5, 16), (7, 17), (8, 18), (9, 16), (11, 18), (11, 21), (12, 22), (13, 20)] = [1, 1, 11, 19, 31, 25, 41, 17, 7, 2, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 2), hits 5 (2, 12), hits 5 (2, 13), hits 5 (2, 25), hits 5 (5, 16), hits 5 (7, 17), hits 5 (8, 18), hits 5 (9, 16), hits 5 (11, 18), hits 5 (11, 21), hits 5 (12, 22), hits 5 (13, 20)] = [1, 1, 11, 19, 31, 25, 41, 17, 7, 2, 0, 0, 0]
  rw [count5, row5_1_2, row5_2_12, row5_2_13, row5_2_25, row5_5_16, row5_7_17, row5_8_18, row5_9_16, row5_11_18, row5_11_21, row5_12_22, row5_13_20] <;> decide

theorem n5_019 : spectrum 5 [(2, 8), (2, 17), (4, 19), (7, 11), (8, 16), (13, 16), (13, 18)] = [1, 21, 38, 47, 34, 11, 2, 1] := by
  change histogram (planes 5).length [hits 5 (2, 8), hits 5 (2, 17), hits 5 (4, 19), hits 5 (7, 11), hits 5 (8, 16), hits 5 (13, 16), hits 5 (13, 18)] = [1, 21, 38, 47, 34, 11, 2, 1]
  rw [count5, row5_2_8, row5_2_17, row5_4_19, row5_7_11, row5_8_16, row5_13_16, row5_13_18] <;> decide

theorem n5_020 : spectrum 5 [(2, 5), (2, 13), (2, 16), (3, 13), (5, 11), (6, 18), (6, 19), (8, 17), (9, 22), (10, 21), (11, 16), (11, 18)] = [0, 1, 6, 23, 35, 36, 24, 19, 10, 1, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 5), hits 5 (2, 13), hits 5 (2, 16), hits 5 (3, 13), hits 5 (5, 11), hits 5 (6, 18), hits 5 (6, 19), hits 5 (8, 17), hits 5 (9, 22), hits 5 (10, 21), hits 5 (11, 16), hits 5 (11, 18)] = [0, 1, 6, 23, 35, 36, 24, 19, 10, 1, 0, 0, 0]
  rw [count5, row5_2_5, row5_2_13, row5_2_16, row5_3_13, row5_5_11, row5_6_18, row5_6_19, row5_8_17, row5_9_22, row5_10_21, row5_11_16, row5_11_18] <;> decide

theorem n5_021 : spectrum 5 [(2, 28), (3, 21), (3, 29), (5, 10), (7, 16), (7, 17), (7, 24), (8, 23), (11, 23), (12, 17), (12, 23), (13, 19)] = [0, 2, 9, 13, 44, 31, 30, 15, 7, 3, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 28), hits 5 (3, 21), hits 5 (3, 29), hits 5 (5, 10), hits 5 (7, 16), hits 5 (7, 17), hits 5 (7, 24), hits 5 (8, 23), hits 5 (11, 23), hits 5 (12, 17), hits 5 (12, 23), hits 5 (13, 19)] = [0, 2, 9, 13, 44, 31, 30, 15, 7, 3, 1, 0, 0]
  rw [count5, row5_2_28, row5_3_21, row5_3_29, row5_5_10, row5_7_16, row5_7_17, row5_7_24, row5_8_23, row5_11_23, row5_12_17, row5_12_23, row5_13_19] <;> decide

theorem n5_022 : spectrum 5 [(3, 29), (5, 27), (6, 16), (7, 24), (9, 17), (9, 22), (11, 20), (12, 21), (13, 21)] = [1, 6, 25, 40, 37, 30, 11, 4, 1, 0] := by
  change histogram (planes 5).length [hits 5 (3, 29), hits 5 (5, 27), hits 5 (6, 16), hits 5 (7, 24), hits 5 (9, 17), hits 5 (9, 22), hits 5 (11, 20), hits 5 (12, 21), hits 5 (13, 21)] = [1, 6, 25, 40, 37, 30, 11, 4, 1, 0]
  rw [count5, row5_3_29, row5_5_27, row5_6_16, row5_7_24, row5_9_17, row5_9_22, row5_11_20, row5_12_21, row5_13_21] <;> decide

theorem n5_023 : spectrum 5 [(2, 8), (4, 9), (4, 25), (4, 27), (5, 19), (6, 10), (6, 16), (6, 17), (7, 11), (8, 23), (11, 21), (12, 22), (13, 19), (15, 22)] = [0, 2, 1, 11, 22, 29, 40, 29, 9, 9, 3, 0, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 8), hits 5 (4, 9), hits 5 (4, 25), hits 5 (4, 27), hits 5 (5, 19), hits 5 (6, 10), hits 5 (6, 16), hits 5 (6, 17), hits 5 (7, 11), hits 5 (8, 23), hits 5 (11, 21), hits 5 (12, 22), hits 5 (13, 19), hits 5 (15, 22)] = [0, 2, 1, 11, 22, 29, 40, 29, 9, 9, 3, 0, 0, 0, 0]
  rw [count5, row5_2_8, row5_4_9, row5_4_25, row5_4_27, row5_5_19, row5_6_10, row5_6_16, row5_6_17, row5_7_11, row5_8_23, row5_11_21, row5_12_22, row5_13_19, row5_15_22] <;> decide

theorem n5_024 : spectrum 5 [(2, 8), (4, 11), (5, 26), (6, 25), (6, 27), (8, 23), (9, 23)] = [2, 20, 39, 48, 29, 12, 5, 0] := by
  change histogram (planes 5).length [hits 5 (2, 8), hits 5 (4, 11), hits 5 (5, 26), hits 5 (6, 25), hits 5 (6, 27), hits 5 (8, 23), hits 5 (9, 23)] = [2, 20, 39, 48, 29, 12, 5, 0]
  rw [count5, row5_2_8, row5_4_11, row5_5_26, row5_6_25, row5_6_27, row5_8_23, row5_9_23] <;> decide

theorem n5_025 : spectrum 5 [(1, 18), (3, 9), (4, 8), (5, 17), (5, 26), (7, 19), (8, 19), (8, 21), (8, 23), (9, 18), (12, 16), (12, 17), (12, 22)] = [0, 2, 7, 14, 24, 35, 33, 24, 9, 5, 2, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 18), hits 5 (3, 9), hits 5 (4, 8), hits 5 (5, 17), hits 5 (5, 26), hits 5 (7, 19), hits 5 (8, 19), hits 5 (8, 21), hits 5 (8, 23), hits 5 (9, 18), hits 5 (12, 16), hits 5 (12, 17), hits 5 (12, 22)] = [0, 2, 7, 14, 24, 35, 33, 24, 9, 5, 2, 0, 0, 0]
  rw [count5, row5_1_18, row5_3_9, row5_4_8, row5_5_17, row5_5_26, row5_7_19, row5_8_19, row5_8_21, row5_8_23, row5_9_18, row5_12_16, row5_12_17, row5_12_22] <;> decide

theorem n5_026 : spectrum 5 [(2, 5), (2, 17), (4, 8), (4, 11), (4, 18), (6, 17), (6, 18), (6, 24), (7, 9), (8, 23), (10, 20), (11, 23), (12, 21), (14, 23)] = [0, 1, 4, 7, 22, 35, 36, 25, 13, 12, 0, 0, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 5), hits 5 (2, 17), hits 5 (4, 8), hits 5 (4, 11), hits 5 (4, 18), hits 5 (6, 17), hits 5 (6, 18), hits 5 (6, 24), hits 5 (7, 9), hits 5 (8, 23), hits 5 (10, 20), hits 5 (11, 23), hits 5 (12, 21), hits 5 (14, 23)] = [0, 1, 4, 7, 22, 35, 36, 25, 13, 12, 0, 0, 0, 0, 0]
  rw [count5, row5_2_5, row5_2_17, row5_4_8, row5_4_11, row5_4_18, row5_6_17, row5_6_18, row5_6_24, row5_7_9, row5_8_23, row5_10_20, row5_11_23, row5_12_21, row5_14_23] <;> decide

theorem n5_027 : spectrum 5 [(1, 8), (1, 14), (2, 17), (3, 4), (3, 21), (3, 24), (6, 11), (7, 19), (7, 27), (10, 16), (11, 17), (12, 16), (12, 17)] = [0, 1, 5, 12, 23, 40, 41, 24, 4, 3, 2, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 8), hits 5 (1, 14), hits 5 (2, 17), hits 5 (3, 4), hits 5 (3, 21), hits 5 (3, 24), hits 5 (6, 11), hits 5 (7, 19), hits 5 (7, 27), hits 5 (10, 16), hits 5 (11, 17), hits 5 (12, 16), hits 5 (12, 17)] = [0, 1, 5, 12, 23, 40, 41, 24, 4, 3, 2, 0, 0, 0]
  rw [count5, row5_1_8, row5_1_14, row5_2_17, row5_3_4, row5_3_21, row5_3_24, row5_6_11, row5_7_19, row5_7_27, row5_10_16, row5_11_17, row5_12_16, row5_12_17] <;> decide

theorem n5_028 : spectrum 5 [(1, 6), (1, 22), (1, 26), (2, 16), (3, 5), (3, 12), (4, 24), (6, 11), (6, 24), (8, 20), (10, 17), (11, 19), (12, 16), (13, 16)] = [0, 1, 3, 9, 25, 28, 33, 34, 14, 7, 0, 1, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 6), hits 5 (1, 22), hits 5 (1, 26), hits 5 (2, 16), hits 5 (3, 5), hits 5 (3, 12), hits 5 (4, 24), hits 5 (6, 11), hits 5 (6, 24), hits 5 (8, 20), hits 5 (10, 17), hits 5 (11, 19), hits 5 (12, 16), hits 5 (13, 16)] = [0, 1, 3, 9, 25, 28, 33, 34, 14, 7, 0, 1, 0, 0, 0]
  rw [count5, row5_1_6, row5_1_22, row5_1_26, row5_2_16, row5_3_5, row5_3_12, row5_4_24, row5_6_11, row5_6_24, row5_8_20, row5_10_17, row5_11_19, row5_12_16, row5_13_16] <;> decide

theorem n5_029 : spectrum 5 [(1, 12), (2, 8), (2, 20), (2, 28), (2, 29), (5, 10), (9, 19), (14, 19)] = [2, 17, 25, 39, 41, 23, 7, 1, 0] := by
  change histogram (planes 5).length [hits 5 (1, 12), hits 5 (2, 8), hits 5 (2, 20), hits 5 (2, 28), hits 5 (2, 29), hits 5 (5, 10), hits 5 (9, 19), hits 5 (14, 19)] = [2, 17, 25, 39, 41, 23, 7, 1, 0]
  rw [count5, row5_1_12, row5_2_8, row5_2_20, row5_2_28, row5_2_29, row5_5_10, row5_9_19, row5_14_19] <;> decide

theorem n5_030 : spectrum 5 [(2, 25), (2, 29), (3, 4), (3, 8), (3, 12), (3, 16), (5, 9), (6, 9), (7, 24), (7, 26), (11, 19), (13, 20), (13, 22)] = [0, 1, 6, 16, 25, 33, 32, 26, 12, 4, 0, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 25), hits 5 (2, 29), hits 5 (3, 4), hits 5 (3, 8), hits 5 (3, 12), hits 5 (3, 16), hits 5 (5, 9), hits 5 (6, 9), hits 5 (7, 24), hits 5 (7, 26), hits 5 (11, 19), hits 5 (13, 20), hits 5 (13, 22)] = [0, 1, 6, 16, 25, 33, 32, 26, 12, 4, 0, 0, 0, 0]
  rw [count5, row5_2_25, row5_2_29, row5_3_4, row5_3_8, row5_3_12, row5_3_16, row5_5_9, row5_6_9, row5_7_24, row5_7_26, row5_11_19, row5_13_20, row5_13_22] <;> decide

theorem n5_031 : spectrum 5 [(1, 16), (3, 4), (5, 26), (6, 8), (9, 22), (11, 21), (12, 22)] = [1, 13, 49, 50, 24, 17, 1, 0] := by
  change histogram (planes 5).length [hits 5 (1, 16), hits 5 (3, 4), hits 5 (5, 26), hits 5 (6, 8), hits 5 (9, 22), hits 5 (11, 21), hits 5 (12, 22)] = [1, 13, 49, 50, 24, 17, 1, 0]
  rw [count5, row5_1_16, row5_3_4, row5_5_26, row5_6_8, row5_9_22, row5_11_21, row5_12_22] <;> decide

theorem n5_032 : spectrum 5 [(1, 4), (1, 30), (4, 16), (4, 19), (6, 8), (7, 9), (7, 17), (13, 20)] = [1, 12, 32, 44, 34, 24, 8, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 4), hits 5 (1, 30), hits 5 (4, 16), hits 5 (4, 19), hits 5 (6, 8), hits 5 (7, 9), hits 5 (7, 17), hits 5 (13, 20)] = [1, 12, 32, 44, 34, 24, 8, 0, 0]
  rw [count5, row5_1_4, row5_1_30, row5_4_16, row5_4_19, row5_6_8, row5_7_9, row5_7_17, row5_13_20] <;> decide

theorem n5_033 : spectrum 5 [(4, 11), (5, 10), (5, 18), (9, 20), (11, 17), (11, 23), (13, 16), (13, 19), (13, 21), (14, 22)] = [1, 4, 17, 31, 36, 38, 21, 7, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (4, 11), hits 5 (5, 10), hits 5 (5, 18), hits 5 (9, 20), hits 5 (11, 17), hits 5 (11, 23), hits 5 (13, 16), hits 5 (13, 19), hits 5 (13, 21), hits 5 (14, 22)] = [1, 4, 17, 31, 36, 38, 21, 7, 0, 0, 0]
  rw [count5, row5_4_11, row5_5_10, row5_5_18, row5_9_20, row5_11_17, row5_11_23, row5_13_16, row5_13_19, row5_13_21, row5_14_22] <;> decide

theorem n5_034 : spectrum 5 [(1, 28), (2, 25), (3, 9), (3, 24), (4, 16), (4, 18), (5, 16), (6, 9), (6, 17), (13, 20)] = [0, 6, 9, 33, 48, 36, 17, 5, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 28), hits 5 (2, 25), hits 5 (3, 9), hits 5 (3, 24), hits 5 (4, 16), hits 5 (4, 18), hits 5 (5, 16), hits 5 (6, 9), hits 5 (6, 17), hits 5 (13, 20)] = [0, 6, 9, 33, 48, 36, 17, 5, 1, 0, 0]
  rw [count5, row5_1_28, row5_2_25, row5_3_9, row5_3_24, row5_4_16, row5_4_18, row5_5_16, row5_6_9, row5_6_17, row5_13_20] <;> decide

theorem n5_035 : spectrum 5 [(1, 2), (1, 6), (3, 5), (3, 29), (4, 17), (4, 18), (5, 26), (6, 26), (7, 19), (9, 20), (10, 20), (10, 22), (15, 16), (15, 22)] = [0, 0, 4, 8, 25, 34, 30, 29, 16, 8, 0, 1, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 2), hits 5 (1, 6), hits 5 (3, 5), hits 5 (3, 29), hits 5 (4, 17), hits 5 (4, 18), hits 5 (5, 26), hits 5 (6, 26), hits 5 (7, 19), hits 5 (9, 20), hits 5 (10, 20), hits 5 (10, 22), hits 5 (15, 16), hits 5 (15, 22)] = [0, 0, 4, 8, 25, 34, 30, 29, 16, 8, 0, 1, 0, 0, 0]
  rw [count5, row5_1_2, row5_1_6, row5_3_5, row5_3_29, row5_4_17, row5_4_18, row5_5_26, row5_6_26, row5_7_19, row5_9_20, row5_10_20, row5_10_22, row5_15_16, row5_15_22] <;> decide

theorem n5_036 : spectrum 5 [(1, 12), (3, 4), (5, 18), (6, 11), (6, 27), (7, 19), (7, 25), (8, 20), (8, 21), (8, 23), (12, 16), (13, 19), (14, 16)] = [0, 1, 3, 16, 28, 39, 29, 22, 13, 2, 2, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 12), hits 5 (3, 4), hits 5 (5, 18), hits 5 (6, 11), hits 5 (6, 27), hits 5 (7, 19), hits 5 (7, 25), hits 5 (8, 20), hits 5 (8, 21), hits 5 (8, 23), hits 5 (12, 16), hits 5 (13, 19), hits 5 (14, 16)] = [0, 1, 3, 16, 28, 39, 29, 22, 13, 2, 2, 0, 0, 0]
  rw [count5, row5_1_12, row5_3_4, row5_5_18, row5_6_11, row5_6_27, row5_7_19, row5_7_25, row5_8_20, row5_8_21, row5_8_23, row5_12_16, row5_13_19, row5_14_16] <;> decide

theorem n5_037 : spectrum 5 [(1, 26), (2, 9), (3, 13), (3, 20), (4, 10), (5, 17), (7, 9), (8, 16), (8, 20), (10, 20), (11, 23), (14, 20), (14, 21), (14, 23)] = [0, 3, 5, 13, 20, 32, 25, 23, 21, 7, 4, 2, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 26), hits 5 (2, 9), hits 5 (3, 13), hits 5 (3, 20), hits 5 (4, 10), hits 5 (5, 17), hits 5 (7, 9), hits 5 (8, 16), hits 5 (8, 20), hits 5 (10, 20), hits 5 (11, 23), hits 5 (14, 20), hits 5 (14, 21), hits 5 (14, 23)] = [0, 3, 5, 13, 20, 32, 25, 23, 21, 7, 4, 2, 0, 0, 0]
  rw [count5, row5_1_26, row5_2_9, row5_3_13, row5_3_20, row5_4_10, row5_5_17, row5_7_9, row5_8_16, row5_8_20, row5_10_20, row5_11_23, row5_14_20, row5_14_21, row5_14_23] <;> decide

theorem n5_038 : spectrum 5 [(1, 18), (1, 30), (2, 24), (3, 12), (4, 8), (5, 19), (6, 9), (6, 26), (7, 9), (8, 18), (9, 16), (15, 18)] = [0, 2, 5, 22, 34, 36, 30, 18, 5, 2, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 18), hits 5 (1, 30), hits 5 (2, 24), hits 5 (3, 12), hits 5 (4, 8), hits 5 (5, 19), hits 5 (6, 9), hits 5 (6, 26), hits 5 (7, 9), hits 5 (8, 18), hits 5 (9, 16), hits 5 (15, 18)] = [0, 2, 5, 22, 34, 36, 30, 18, 5, 2, 1, 0, 0]
  rw [count5, row5_1_18, row5_1_30, row5_2_24, row5_3_12, row5_4_8, row5_5_19, row5_6_9, row5_6_26, row5_7_9, row5_8_18, row5_9_16, row5_15_18] <;> decide

theorem n5_039 : spectrum 5 [(1, 12), (1, 16), (1, 18), (3, 21), (4, 10), (4, 17), (5, 25), (7, 16), (7, 27), (8, 17), (11, 21), (12, 21)] = [0, 1, 6, 27, 33, 32, 26, 19, 8, 1, 2, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 12), hits 5 (1, 16), hits 5 (1, 18), hits 5 (3, 21), hits 5 (4, 10), hits 5 (4, 17), hits 5 (5, 25), hits 5 (7, 16), hits 5 (7, 27), hits 5 (8, 17), hits 5 (11, 21), hits 5 (12, 21)] = [0, 1, 6, 27, 33, 32, 26, 19, 8, 1, 2, 0, 0]
  rw [count5, row5_1_12, row5_1_16, row5_1_18, row5_3_21, row5_4_10, row5_4_17, row5_5_25, row5_7_16, row5_7_27, row5_8_17, row5_11_21, row5_12_21] <;> decide

theorem n5_040 : spectrum 5 [(1, 22), (3, 13), (5, 18), (8, 20), (8, 22), (9, 22), (11, 21), (12, 18), (12, 21), (14, 19), (14, 23)] = [0, 2, 16, 24, 33, 43, 18, 10, 8, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 22), hits 5 (3, 13), hits 5 (5, 18), hits 5 (8, 20), hits 5 (8, 22), hits 5 (9, 22), hits 5 (11, 21), hits 5 (12, 18), hits 5 (12, 21), hits 5 (14, 19), hits 5 (14, 23)] = [0, 2, 16, 24, 33, 43, 18, 10, 8, 1, 0, 0]
  rw [count5, row5_1_22, row5_3_13, row5_5_18, row5_8_20, row5_8_22, row5_9_22, row5_11_21, row5_12_18, row5_12_21, row5_14_19, row5_14_23] <;> decide

theorem n5_041 : spectrum 5 [(1, 2), (1, 20), (4, 17), (5, 9), (6, 27), (8, 18), (10, 23), (11, 19), (12, 19), (13, 17), (13, 20), (13, 21), (15, 23)] = [0, 0, 4, 17, 21, 38, 42, 21, 8, 4, 0, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 2), hits 5 (1, 20), hits 5 (4, 17), hits 5 (5, 9), hits 5 (6, 27), hits 5 (8, 18), hits 5 (10, 23), hits 5 (11, 19), hits 5 (12, 19), hits 5 (13, 17), hits 5 (13, 20), hits 5 (13, 21), hits 5 (15, 23)] = [0, 0, 4, 17, 21, 38, 42, 21, 8, 4, 0, 0, 0, 0]
  rw [count5, row5_1_2, row5_1_20, row5_4_17, row5_5_9, row5_6_27, row5_8_18, row5_10_23, row5_11_19, row5_12_19, row5_13_17, row5_13_20, row5_13_21, row5_15_23] <;> decide

theorem n5_042 : spectrum 5 [(3, 12), (3, 21), (4, 18), (6, 10), (6, 16), (6, 17), (9, 22), (10, 20), (11, 20), (13, 23), (14, 21), (15, 22)] = [0, 2, 11, 17, 35, 34, 22, 25, 6, 2, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (3, 12), hits 5 (3, 21), hits 5 (4, 18), hits 5 (6, 10), hits 5 (6, 16), hits 5 (6, 17), hits 5 (9, 22), hits 5 (10, 20), hits 5 (11, 20), hits 5 (13, 23), hits 5 (14, 21), hits 5 (15, 22)] = [0, 2, 11, 17, 35, 34, 22, 25, 6, 2, 1, 0, 0]
  rw [count5, row5_3_12, row5_3_21, row5_4_18, row5_6_10, row5_6_16, row5_6_17, row5_9_22, row5_10_20, row5_11_20, row5_13_23, row5_14_21, row5_15_22] <;> decide

theorem n5_043 : spectrum 5 [(1, 16), (1, 22), (1, 28), (4, 24), (4, 26), (5, 9), (5, 27), (6, 8), (8, 19), (12, 23), (15, 19)] = [0, 4, 11, 22, 45, 28, 31, 10, 2, 0, 2, 0] := by
  change histogram (planes 5).length [hits 5 (1, 16), hits 5 (1, 22), hits 5 (1, 28), hits 5 (4, 24), hits 5 (4, 26), hits 5 (5, 9), hits 5 (5, 27), hits 5 (6, 8), hits 5 (8, 19), hits 5 (12, 23), hits 5 (15, 19)] = [0, 4, 11, 22, 45, 28, 31, 10, 2, 0, 2, 0]
  rw [count5, row5_1_16, row5_1_22, row5_1_28, row5_4_24, row5_4_26, row5_5_9, row5_5_27, row5_6_8, row5_8_19, row5_12_23, row5_15_19] <;> decide

theorem n5_044 : spectrum 5 [(1, 8), (1, 14), (2, 16), (3, 5), (4, 10), (4, 19), (7, 8), (7, 11), (7, 26), (13, 18), (14, 16), (14, 22)] = [0, 1, 10, 18, 24, 46, 34, 14, 7, 1, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 8), hits 5 (1, 14), hits 5 (2, 16), hits 5 (3, 5), hits 5 (4, 10), hits 5 (4, 19), hits 5 (7, 8), hits 5 (7, 11), hits 5 (7, 26), hits 5 (13, 18), hits 5 (14, 16), hits 5 (14, 22)] = [0, 1, 10, 18, 24, 46, 34, 14, 7, 1, 0, 0, 0]
  rw [count5, row5_1_8, row5_1_14, row5_2_16, row5_3_5, row5_4_10, row5_4_19, row5_7_8, row5_7_11, row5_7_26, row5_13_18, row5_14_16, row5_14_22] <;> decide

theorem n5_045 : spectrum 5 [(1, 30), (2, 17), (5, 9), (6, 16), (7, 10), (7, 25), (13, 20), (14, 22), (15, 20)] = [1, 6, 21, 37, 44, 36, 9, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 30), hits 5 (2, 17), hits 5 (5, 9), hits 5 (6, 16), hits 5 (7, 10), hits 5 (7, 25), hits 5 (13, 20), hits 5 (14, 22), hits 5 (15, 20)] = [1, 6, 21, 37, 44, 36, 9, 1, 0, 0]
  rw [count5, row5_1_30, row5_2_17, row5_5_9, row5_6_16, row5_7_10, row5_7_25, row5_13_20, row5_14_22, row5_15_20] <;> decide

theorem n5_046 : spectrum 5 [(1, 10), (4, 10), (6, 11), (6, 24), (9, 16), (11, 20), (11, 22), (13, 22), (14, 19), (14, 22), (15, 19)] = [0, 5, 12, 22, 43, 26, 31, 10, 4, 1, 1, 0] := by
  change histogram (planes 5).length [hits 5 (1, 10), hits 5 (4, 10), hits 5 (6, 11), hits 5 (6, 24), hits 5 (9, 16), hits 5 (11, 20), hits 5 (11, 22), hits 5 (13, 22), hits 5 (14, 19), hits 5 (14, 22), hits 5 (15, 19)] = [0, 5, 12, 22, 43, 26, 31, 10, 4, 1, 1, 0]
  rw [count5, row5_1_10, row5_4_10, row5_6_11, row5_6_24, row5_9_16, row5_11_20, row5_11_22, row5_13_22, row5_14_19, row5_14_22, row5_15_19] <;> decide

theorem n5_047 : spectrum 5 [(2, 5), (2, 24), (3, 20), (5, 10), (5, 27), (7, 18), (7, 24), (8, 18), (11, 19), (14, 16), (15, 20), (15, 21)] = [0, 3, 7, 21, 33, 34, 29, 18, 6, 3, 0, 1, 0] := by
  change histogram (planes 5).length [hits 5 (2, 5), hits 5 (2, 24), hits 5 (3, 20), hits 5 (5, 10), hits 5 (5, 27), hits 5 (7, 18), hits 5 (7, 24), hits 5 (8, 18), hits 5 (11, 19), hits 5 (14, 16), hits 5 (15, 20), hits 5 (15, 21)] = [0, 3, 7, 21, 33, 34, 29, 18, 6, 3, 0, 1, 0]
  rw [count5, row5_2_5, row5_2_24, row5_3_20, row5_5_10, row5_5_27, row5_7_18, row5_7_24, row5_8_18, row5_11_19, row5_14_16, row5_15_20, row5_15_21] <;> decide

theorem n5_048 : spectrum 5 [(1, 12), (1, 30), (3, 4), (3, 9), (4, 19), (5, 19), (5, 26), (6, 19), (7, 27), (12, 16), (13, 17), (15, 18)] = [1, 0, 4, 24, 30, 40, 32, 16, 8, 0, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 12), hits 5 (1, 30), hits 5 (3, 4), hits 5 (3, 9), hits 5 (4, 19), hits 5 (5, 19), hits 5 (5, 26), hits 5 (6, 19), hits 5 (7, 27), hits 5 (12, 16), hits 5 (13, 17), hits 5 (15, 18)] = [1, 0, 4, 24, 30, 40, 32, 16, 8, 0, 0, 0, 0]
  rw [count5, row5_1_12, row5_1_30, row5_3_4, row5_3_9, row5_4_19, row5_5_19, row5_5_26, row5_6_19, row5_7_27, row5_12_16, row5_13_17, row5_15_18] <;> decide

theorem n5_049 : spectrum 5 [(1, 24), (2, 24), (2, 29), (3, 17), (6, 9), (7, 25), (8, 16), (10, 18), (11, 21), (14, 19), (15, 18)] = [1, 2, 11, 30, 32, 35, 27, 12, 4, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 24), hits 5 (2, 24), hits 5 (2, 29), hits 5 (3, 17), hits 5 (6, 9), hits 5 (7, 25), hits 5 (8, 16), hits 5 (10, 18), hits 5 (11, 21), hits 5 (14, 19), hits 5 (15, 18)] = [1, 2, 11, 30, 32, 35, 27, 12, 4, 1, 0, 0]
  rw [count5, row5_1_24, row5_2_24, row5_2_29, row5_3_17, row5_6_9, row5_7_25, row5_8_16, row5_10_18, row5_11_21, row5_14_19, row5_15_18] <;> decide

theorem n5_050 : spectrum 5 [(2, 9), (2, 21), (3, 29), (4, 10), (4, 26), (5, 11), (7, 17), (11, 20), (12, 22), (13, 21), (14, 23), (15, 16)] = [0, 1, 6, 20, 31, 43, 32, 14, 6, 2, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 9), hits 5 (2, 21), hits 5 (3, 29), hits 5 (4, 10), hits 5 (4, 26), hits 5 (5, 11), hits 5 (7, 17), hits 5 (11, 20), hits 5 (12, 22), hits 5 (13, 21), hits 5 (14, 23), hits 5 (15, 16)] = [0, 1, 6, 20, 31, 43, 32, 14, 6, 2, 0, 0, 0]
  rw [count5, row5_2_9, row5_2_21, row5_3_29, row5_4_10, row5_4_26, row5_5_11, row5_7_17, row5_11_20, row5_12_22, row5_13_21, row5_14_23, row5_15_16] <;> decide

theorem n5_051 : spectrum 5 [(1, 22), (3, 4), (5, 17), (5, 18), (5, 26), (6, 18), (7, 9), (7, 11), (7, 17), (10, 22), (11, 23), (12, 19), (12, 21), (14, 21)] = [0, 0, 1, 16, 26, 26, 32, 28, 13, 10, 3, 0, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 22), hits 5 (3, 4), hits 5 (5, 17), hits 5 (5, 18), hits 5 (5, 26), hits 5 (6, 18), hits 5 (7, 9), hits 5 (7, 11), hits 5 (7, 17), hits 5 (10, 22), hits 5 (11, 23), hits 5 (12, 19), hits 5 (12, 21), hits 5 (14, 21)] = [0, 0, 1, 16, 26, 26, 32, 28, 13, 10, 3, 0, 0, 0, 0]
  rw [count5, row5_1_22, row5_3_4, row5_5_17, row5_5_18, row5_5_26, row5_6_18, row5_7_9, row5_7_11, row5_7_17, row5_10_22, row5_11_23, row5_12_19, row5_12_21, row5_14_21] <;> decide

theorem n5_052 : spectrum 5 [(1, 8), (2, 8), (4, 25), (6, 19), (6, 27), (7, 17), (7, 27), (10, 18), (11, 22), (14, 17), (14, 19)] = [0, 3, 9, 32, 36, 31, 25, 14, 5, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 8), hits 5 (2, 8), hits 5 (4, 25), hits 5 (6, 19), hits 5 (6, 27), hits 5 (7, 17), hits 5 (7, 27), hits 5 (10, 18), hits 5 (11, 22), hits 5 (14, 17), hits 5 (14, 19)] = [0, 3, 9, 32, 36, 31, 25, 14, 5, 0, 0, 0]
  rw [count5, row5_1_8, row5_2_8, row5_4_25, row5_6_19, row5_6_27, row5_7_17, row5_7_27, row5_10_18, row5_11_22, row5_14_17, row5_14_19] <;> decide

theorem n5_053 : spectrum 5 [(1, 6), (3, 24), (3, 28), (5, 16), (9, 20), (12, 20), (13, 20), (14, 17), (15, 18)] = [1, 6, 20, 42, 42, 30, 12, 2, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 6), hits 5 (3, 24), hits 5 (3, 28), hits 5 (5, 16), hits 5 (9, 20), hits 5 (12, 20), hits 5 (13, 20), hits 5 (14, 17), hits 5 (15, 18)] = [1, 6, 20, 42, 42, 30, 12, 2, 0, 0]
  rw [count5, row5_1_6, row5_3_24, row5_3_28, row5_5_16, row5_9_20, row5_12_20, row5_13_20, row5_14_17, row5_15_18] <;> decide

theorem n5_054 : spectrum 5 [(2, 17), (2, 21), (2, 25), (3, 28), (3, 29), (4, 17), (8, 22), (11, 23), (12, 19), (12, 23)] = [1, 6, 15, 34, 38, 31, 19, 8, 2, 1, 0] := by
  change histogram (planes 5).length [hits 5 (2, 17), hits 5 (2, 21), hits 5 (2, 25), hits 5 (3, 28), hits 5 (3, 29), hits 5 (4, 17), hits 5 (8, 22), hits 5 (11, 23), hits 5 (12, 19), hits 5 (12, 23)] = [1, 6, 15, 34, 38, 31, 19, 8, 2, 1, 0]
  rw [count5, row5_2_17, row5_2_21, row5_2_25, row5_3_28, row5_3_29, row5_4_17, row5_8_22, row5_11_23, row5_12_19, row5_12_23] <;> decide

theorem n5_055 : spectrum 5 [(2, 4), (2, 17), (3, 20), (4, 17), (6, 17), (6, 18), (9, 20), (10, 23), (11, 20), (13, 16), (13, 20)] = [1, 7, 14, 27, 28, 29, 22, 17, 10, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 4), hits 5 (2, 17), hits 5 (3, 20), hits 5 (4, 17), hits 5 (6, 17), hits 5 (6, 18), hits 5 (9, 20), hits 5 (10, 23), hits 5 (11, 20), hits 5 (13, 16), hits 5 (13, 20)] = [1, 7, 14, 27, 28, 29, 22, 17, 10, 0, 0, 0]
  rw [count5, row5_2_4, row5_2_17, row5_3_20, row5_4_17, row5_6_17, row5_6_18, row5_9_20, row5_10_23, row5_11_20, row5_13_16, row5_13_20] <;> decide

theorem n5_056 : spectrum 5 [(2, 20), (2, 24), (3, 16), (3, 25), (4, 8), (6, 25), (7, 26), (12, 17)] = [3, 9, 30, 49, 36, 19, 6, 3, 0] := by
  change histogram (planes 5).length [hits 5 (2, 20), hits 5 (2, 24), hits 5 (3, 16), hits 5 (3, 25), hits 5 (4, 8), hits 5 (6, 25), hits 5 (7, 26), hits 5 (12, 17)] = [3, 9, 30, 49, 36, 19, 6, 3, 0]
  rw [count5, row5_2_20, row5_2_24, row5_3_16, row5_3_25, row5_4_8, row5_6_25, row5_7_26, row5_12_17] <;> decide

theorem n5_057 : spectrum 5 [(1, 24), (2, 24), (2, 25), (3, 5), (4, 16), (4, 19), (5, 9), (7, 9), (9, 22), (10, 23)] = [1, 0, 21, 31, 36, 42, 17, 7, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 24), hits 5 (2, 24), hits 5 (2, 25), hits 5 (3, 5), hits 5 (4, 16), hits 5 (4, 19), hits 5 (5, 9), hits 5 (7, 9), hits 5 (9, 22), hits 5 (10, 23)] = [1, 0, 21, 31, 36, 42, 17, 7, 0, 0, 0]
  rw [count5, row5_1_24, row5_2_24, row5_2_25, row5_3_5, row5_4_16, row5_4_19, row5_5_9, row5_7_9, row5_9_22, row5_10_23] <;> decide

theorem n5_058 : spectrum 5 [(1, 10), (3, 16), (3, 20), (6, 11), (9, 19), (11, 19), (12, 23)] = [3, 22, 39, 41, 30, 16, 3, 1] := by
  change histogram (planes 5).length [hits 5 (1, 10), hits 5 (3, 16), hits 5 (3, 20), hits 5 (6, 11), hits 5 (9, 19), hits 5 (11, 19), hits 5 (12, 23)] = [3, 22, 39, 41, 30, 16, 3, 1]
  rw [count5, row5_1_10, row5_3_16, row5_3_20, row5_6_11, row5_9_19, row5_11_19, row5_12_23] <;> decide

theorem n5_059 : spectrum 5 [(1, 24), (1, 28), (1, 30), (2, 8), (3, 16), (5, 19), (6, 8), (6, 19), (10, 22), (13, 17), (13, 21)] = [0, 0, 16, 27, 35, 40, 18, 11, 6, 2, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 24), hits 5 (1, 28), hits 5 (1, 30), hits 5 (2, 8), hits 5 (3, 16), hits 5 (5, 19), hits 5 (6, 8), hits 5 (6, 19), hits 5 (10, 22), hits 5 (13, 17), hits 5 (13, 21)] = [0, 0, 16, 27, 35, 40, 18, 11, 6, 2, 0, 0]
  rw [count5, row5_1_24, row5_1_28, row5_1_30, row5_2_8, row5_3_16, row5_5_19, row5_6_8, row5_6_19, row5_10_22, row5_13_17, row5_13_21] <;> decide

theorem n5_060 : spectrum 5 [(1, 18), (2, 20), (3, 8), (3, 16), (3, 25), (3, 28), (5, 8), (5, 11), (5, 17), (5, 27), (6, 19), (7, 11), (9, 22), (15, 21)] = [0, 2, 4, 11, 17, 29, 35, 33, 18, 5, 1, 0, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 18), hits 5 (2, 20), hits 5 (3, 8), hits 5 (3, 16), hits 5 (3, 25), hits 5 (3, 28), hits 5 (5, 8), hits 5 (5, 11), hits 5 (5, 17), hits 5 (5, 27), hits 5 (6, 19), hits 5 (7, 11), hits 5 (9, 22), hits 5 (15, 21)] = [0, 2, 4, 11, 17, 29, 35, 33, 18, 5, 1, 0, 0, 0, 0]
  rw [count5, row5_1_18, row5_2_20, row5_3_8, row5_3_16, row5_3_25, row5_3_28, row5_5_8, row5_5_11, row5_5_17, row5_5_27, row5_6_19, row5_7_11, row5_9_22, row5_15_21] <;> decide

theorem n5_061 : spectrum 5 [(1, 6), (3, 21), (3, 24), (3, 25), (3, 28), (4, 8), (5, 10), (5, 18), (5, 24), (8, 18), (8, 19), (9, 19), (12, 21)] = [0, 0, 7, 10, 37, 32, 31, 18, 14, 4, 2, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 6), hits 5 (3, 21), hits 5 (3, 24), hits 5 (3, 25), hits 5 (3, 28), hits 5 (4, 8), hits 5 (5, 10), hits 5 (5, 18), hits 5 (5, 24), hits 5 (8, 18), hits 5 (8, 19), hits 5 (9, 19), hits 5 (12, 21)] = [0, 0, 7, 10, 37, 32, 31, 18, 14, 4, 2, 0, 0, 0]
  rw [count5, row5_1_6, row5_3_21, row5_3_24, row5_3_25, row5_3_28, row5_4_8, row5_5_10, row5_5_18, row5_5_24, row5_8_18, row5_8_19, row5_9_19, row5_12_21] <;> decide

theorem n5_062 : spectrum 5 [(1, 10), (1, 12), (5, 8), (6, 17), (7, 19), (9, 21), (11, 22), (15, 19)] = [2, 9, 28, 50, 39, 21, 6, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 10), hits 5 (1, 12), hits 5 (5, 8), hits 5 (6, 17), hits 5 (7, 19), hits 5 (9, 21), hits 5 (11, 22), hits 5 (15, 19)] = [2, 9, 28, 50, 39, 21, 6, 0, 0]
  rw [count5, row5_1_10, row5_1_12, row5_5_8, row5_6_17, row5_7_19, row5_9_21, row5_11_22, row5_15_19] <;> decide

theorem n5_063 : spectrum 5 [(1, 2), (1, 16), (2, 4), (3, 9), (3, 29), (4, 19), (8, 23)] = [3, 20, 42, 40, 28, 20, 2, 0] := by
  change histogram (planes 5).length [hits 5 (1, 2), hits 5 (1, 16), hits 5 (2, 4), hits 5 (3, 9), hits 5 (3, 29), hits 5 (4, 19), hits 5 (8, 23)] = [3, 20, 42, 40, 28, 20, 2, 0]
  rw [count5, row5_1_2, row5_1_16, row5_2_4, row5_3_9, row5_3_29, row5_4_19, row5_8_23] <;> decide

theorem n5_064 : spectrum 5 [(3, 5), (3, 13), (5, 16), (6, 18), (8, 17), (8, 20), (10, 18), (12, 16), (13, 18)] = [1, 10, 21, 37, 40, 28, 13, 5, 0, 0] := by
  change histogram (planes 5).length [hits 5 (3, 5), hits 5 (3, 13), hits 5 (5, 16), hits 5 (6, 18), hits 5 (8, 17), hits 5 (8, 20), hits 5 (10, 18), hits 5 (12, 16), hits 5 (13, 18)] = [1, 10, 21, 37, 40, 28, 13, 5, 0, 0]
  rw [count5, row5_3_5, row5_3_13, row5_5_16, row5_6_18, row5_8_17, row5_8_20, row5_10_18, row5_12_16, row5_13_18] <;> decide

theorem n5_065 : spectrum 5 [(1, 2), (2, 25), (3, 29), (5, 17), (6, 26), (8, 21), (10, 19), (11, 19), (11, 20)] = [1, 4, 22, 46, 38, 28, 14, 2, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 2), hits 5 (2, 25), hits 5 (3, 29), hits 5 (5, 17), hits 5 (6, 26), hits 5 (8, 21), hits 5 (10, 19), hits 5 (11, 19), hits 5 (11, 20)] = [1, 4, 22, 46, 38, 28, 14, 2, 0, 0]
  rw [count5, row5_1_2, row5_2_25, row5_3_29, row5_5_17, row5_6_26, row5_8_21, row5_10_19, row5_11_19, row5_11_20] <;> decide

theorem n5_066 : spectrum 5 [(2, 21), (3, 12), (3, 20), (4, 8), (4, 11), (5, 27), (7, 8), (7, 25), (9, 21), (10, 20), (11, 19), (13, 21), (15, 19)] = [0, 3, 7, 13, 22, 36, 31, 25, 15, 3, 0, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 21), hits 5 (3, 12), hits 5 (3, 20), hits 5 (4, 8), hits 5 (4, 11), hits 5 (5, 27), hits 5 (7, 8), hits 5 (7, 25), hits 5 (9, 21), hits 5 (10, 20), hits 5 (11, 19), hits 5 (13, 21), hits 5 (15, 19)] = [0, 3, 7, 13, 22, 36, 31, 25, 15, 3, 0, 0, 0, 0]
  rw [count5, row5_2_21, row5_3_12, row5_3_20, row5_4_8, row5_4_11, row5_5_27, row5_7_8, row5_7_25, row5_9_21, row5_10_20, row5_11_19, row5_13_21, row5_15_19] <;> decide

theorem n5_067 : spectrum 5 [(1, 12), (1, 20), (1, 30), (5, 16), (5, 18), (6, 11), (7, 9), (7, 18), (7, 24), (8, 21), (11, 18), (12, 21), (13, 18)] = [3, 0, 4, 21, 24, 34, 27, 17, 14, 8, 3, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 12), hits 5 (1, 20), hits 5 (1, 30), hits 5 (5, 16), hits 5 (5, 18), hits 5 (6, 11), hits 5 (7, 9), hits 5 (7, 18), hits 5 (7, 24), hits 5 (8, 21), hits 5 (11, 18), hits 5 (12, 21), hits 5 (13, 18)] = [3, 0, 4, 21, 24, 34, 27, 17, 14, 8, 3, 0, 0, 0]
  rw [count5, row5_1_12, row5_1_20, row5_1_30, row5_5_16, row5_5_18, row5_6_11, row5_7_9, row5_7_18, row5_7_24, row5_8_21, row5_11_18, row5_12_21, row5_13_18] <;> decide

theorem n5_068 : spectrum 5 [(2, 8), (2, 9), (3, 9), (3, 12), (3, 25), (4, 9), (7, 25), (8, 23), (10, 21), (11, 23), (14, 20)] = [1, 0, 15, 25, 36, 42, 15, 13, 8, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 8), hits 5 (2, 9), hits 5 (3, 9), hits 5 (3, 12), hits 5 (3, 25), hits 5 (4, 9), hits 5 (7, 25), hits 5 (8, 23), hits 5 (10, 21), hits 5 (11, 23), hits 5 (14, 20)] = [1, 0, 15, 25, 36, 42, 15, 13, 8, 0, 0, 0]
  rw [count5, row5_2_8, row5_2_9, row5_3_9, row5_3_12, row5_3_25, row5_4_9, row5_7_25, row5_8_23, row5_10_21, row5_11_23, row5_14_20] <;> decide

theorem n5_069 : spectrum 5 [(3, 5), (3, 29), (5, 10), (6, 10), (6, 11), (6, 19), (9, 19), (10, 16), (11, 17), (13, 19), (13, 21), (14, 17), (14, 23), (15, 17)] = [0, 1, 2, 15, 22, 34, 32, 16, 17, 13, 2, 1, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (3, 5), hits 5 (3, 29), hits 5 (5, 10), hits 5 (6, 10), hits 5 (6, 11), hits 5 (6, 19), hits 5 (9, 19), hits 5 (10, 16), hits 5 (11, 17), hits 5 (13, 19), hits 5 (13, 21), hits 5 (14, 17), hits 5 (14, 23), hits 5 (15, 17)] = [0, 1, 2, 15, 22, 34, 32, 16, 17, 13, 2, 1, 0, 0, 0]
  rw [count5, row5_3_5, row5_3_29, row5_5_10, row5_6_10, row5_6_11, row5_6_19, row5_9_19, row5_10_16, row5_11_17, row5_13_19, row5_13_21, row5_14_17, row5_14_23, row5_15_17] <;> decide

theorem n5_070 : spectrum 5 [(1, 16), (2, 25), (3, 5), (4, 11), (6, 27), (7, 9), (10, 22)] = [1, 14, 42, 56, 30, 10, 2, 0] := by
  change histogram (planes 5).length [hits 5 (1, 16), hits 5 (2, 25), hits 5 (3, 5), hits 5 (4, 11), hits 5 (6, 27), hits 5 (7, 9), hits 5 (10, 22)] = [1, 14, 42, 56, 30, 10, 2, 0]
  rw [count5, row5_1_16, row5_2_25, row5_3_5, row5_4_11, row5_6_27, row5_7_9, row5_10_22] <;> decide

theorem n5_071 : spectrum 5 [(2, 5), (2, 16), (2, 17), (3, 4), (3, 28), (5, 10), (6, 10), (6, 27), (9, 17), (12, 18), (13, 18), (13, 20)] = [1, 0, 6, 12, 47, 39, 28, 10, 9, 3, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 5), hits 5 (2, 16), hits 5 (2, 17), hits 5 (3, 4), hits 5 (3, 28), hits 5 (5, 10), hits 5 (6, 10), hits 5 (6, 27), hits 5 (9, 17), hits 5 (12, 18), hits 5 (13, 18), hits 5 (13, 20)] = [1, 0, 6, 12, 47, 39, 28, 10, 9, 3, 0, 0, 0]
  rw [count5, row5_2_5, row5_2_16, row5_2_17, row5_3_4, row5_3_28, row5_5_10, row5_6_10, row5_6_27, row5_9_17, row5_12_18, row5_13_18, row5_13_20] <;> decide

theorem n5_072 : spectrum 5 [(1, 2), (3, 8), (3, 17), (8, 20), (8, 21), (10, 18), (11, 17), (11, 21), (12, 23), (13, 17)] = [0, 6, 16, 36, 37, 30, 19, 8, 2, 0, 1] := by
  change histogram (planes 5).length [hits 5 (1, 2), hits 5 (3, 8), hits 5 (3, 17), hits 5 (8, 20), hits 5 (8, 21), hits 5 (10, 18), hits 5 (11, 17), hits 5 (11, 21), hits 5 (12, 23), hits 5 (13, 17)] = [0, 6, 16, 36, 37, 30, 19, 8, 2, 0, 1]
  rw [count5, row5_1_2, row5_3_8, row5_3_17, row5_8_20, row5_8_21, row5_10_18, row5_11_17, row5_11_21, row5_12_23, row5_13_17] <;> decide

theorem n5_073 : spectrum 5 [(1, 14), (4, 16), (5, 24), (6, 18), (7, 10), (10, 16), (11, 18), (14, 22), (15, 20)] = [0, 10, 18, 40, 46, 26, 10, 4, 1, 0] := by
  change histogram (planes 5).length [hits 5 (1, 14), hits 5 (4, 16), hits 5 (5, 24), hits 5 (6, 18), hits 5 (7, 10), hits 5 (10, 16), hits 5 (11, 18), hits 5 (14, 22), hits 5 (15, 20)] = [0, 10, 18, 40, 46, 26, 10, 4, 1, 0]
  rw [count5, row5_1_14, row5_4_16, row5_5_24, row5_6_18, row5_7_10, row5_10_16, row5_11_18, row5_14_22, row5_15_20] <;> decide

theorem n5_074 : spectrum 5 [(1, 10), (2, 13), (4, 24), (5, 18), (5, 27), (6, 16), (6, 25), (8, 17), (13, 21), (14, 23)] = [0, 5, 10, 35, 45, 36, 20, 3, 0, 1, 0] := by
  change histogram (planes 5).length [hits 5 (1, 10), hits 5 (2, 13), hits 5 (4, 24), hits 5 (5, 18), hits 5 (5, 27), hits 5 (6, 16), hits 5 (6, 25), hits 5 (8, 17), hits 5 (13, 21), hits 5 (14, 23)] = [0, 5, 10, 35, 45, 36, 20, 3, 0, 1, 0]
  rw [count5, row5_1_10, row5_2_13, row5_4_24, row5_5_18, row5_5_27, row5_6_16, row5_6_25, row5_8_17, row5_13_21, row5_14_23] <;> decide

theorem n5_075 : spectrum 5 [(1, 8), (1, 16), (1, 26), (4, 19), (4, 27), (5, 24), (5, 25), (7, 17), (9, 18), (10, 23), (11, 16), (13, 19)] = [0, 2, 8, 21, 27, 38, 34, 17, 6, 2, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 8), hits 5 (1, 16), hits 5 (1, 26), hits 5 (4, 19), hits 5 (4, 27), hits 5 (5, 24), hits 5 (5, 25), hits 5 (7, 17), hits 5 (9, 18), hits 5 (10, 23), hits 5 (11, 16), hits 5 (13, 19)] = [0, 2, 8, 21, 27, 38, 34, 17, 6, 2, 0, 0, 0]
  rw [count5, row5_1_8, row5_1_16, row5_1_26, row5_4_19, row5_4_27, row5_5_24, row5_5_25, row5_7_17, row5_9_18, row5_10_23, row5_11_16, row5_13_19] <;> decide

theorem n5_076 : spectrum 5 [(1, 6), (5, 9), (6, 11), (6, 17), (11, 19), (11, 23), (12, 17), (13, 20), (15, 16)] = [0, 9, 22, 40, 41, 25, 12, 6, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 6), hits 5 (5, 9), hits 5 (6, 11), hits 5 (6, 17), hits 5 (11, 19), hits 5 (11, 23), hits 5 (12, 17), hits 5 (13, 20), hits 5 (15, 16)] = [0, 9, 22, 40, 41, 25, 12, 6, 0, 0]
  rw [count5, row5_1_6, row5_5_9, row5_6_11, row5_6_17, row5_11_19, row5_11_23, row5_12_17, row5_13_20, row5_15_16] <;> decide

theorem n5_077 : spectrum 5 [(1, 10), (1, 20), (3, 28), (4, 11), (4, 17), (6, 19), (7, 16), (7, 18), (15, 19)] = [2, 5, 35, 24, 42, 29, 11, 6, 1, 0] := by
  change histogram (planes 5).length [hits 5 (1, 10), hits 5 (1, 20), hits 5 (3, 28), hits 5 (4, 11), hits 5 (4, 17), hits 5 (6, 19), hits 5 (7, 16), hits 5 (7, 18), hits 5 (15, 19)] = [2, 5, 35, 24, 42, 29, 11, 6, 1, 0]
  rw [count5, row5_1_10, row5_1_20, row5_3_28, row5_4_11, row5_4_17, row5_6_19, row5_7_16, row5_7_18, row5_15_19] <;> decide

theorem n5_078 : spectrum 5 [(1, 26), (5, 8), (5, 10), (5, 16), (6, 8), (6, 10), (8, 18), (9, 21), (11, 21)] = [0, 9, 25, 40, 36, 25, 13, 6, 1, 0] := by
  change histogram (planes 5).length [hits 5 (1, 26), hits 5 (5, 8), hits 5 (5, 10), hits 5 (5, 16), hits 5 (6, 8), hits 5 (6, 10), hits 5 (8, 18), hits 5 (9, 21), hits 5 (11, 21)] = [0, 9, 25, 40, 36, 25, 13, 6, 1, 0]
  rw [count5, row5_1_26, row5_5_8, row5_5_10, row5_5_16, row5_6_8, row5_6_10, row5_8_18, row5_9_21, row5_11_21] <;> decide

theorem n5_079 : spectrum 5 [(2, 8), (2, 24), (6, 18), (6, 27), (7, 19), (9, 21), (10, 20), (10, 23), (11, 19), (12, 21), (15, 18)] = [0, 4, 9, 29, 34, 36, 29, 9, 3, 2, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 8), hits 5 (2, 24), hits 5 (6, 18), hits 5 (6, 27), hits 5 (7, 19), hits 5 (9, 21), hits 5 (10, 20), hits 5 (10, 23), hits 5 (11, 19), hits 5 (12, 21), hits 5 (15, 18)] = [0, 4, 9, 29, 34, 36, 29, 9, 3, 2, 0, 0]
  rw [count5, row5_2_8, row5_2_24, row5_6_18, row5_6_27, row5_7_19, row5_9_21, row5_10_20, row5_10_23, row5_11_19, row5_12_21, row5_15_18] <;> decide

theorem n5_080 : spectrum 5 [(1, 22), (1, 30), (3, 24), (5, 10), (9, 20), (10, 19), (11, 23), (12, 22)] = [1, 10, 30, 44, 42, 26, 2, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 22), hits 5 (1, 30), hits 5 (3, 24), hits 5 (5, 10), hits 5 (9, 20), hits 5 (10, 19), hits 5 (11, 23), hits 5 (12, 22)] = [1, 10, 30, 44, 42, 26, 2, 0, 0]
  rw [count5, row5_1_22, row5_1_30, row5_3_24, row5_5_10, row5_9_20, row5_10_19, row5_11_23, row5_12_22] <;> decide

theorem n5_081 : spectrum 5 [(1, 6), (1, 14), (1, 18), (4, 27), (5, 17), (6, 16), (11, 20), (11, 23), (14, 16), (14, 21)] = [1, 6, 13, 32, 41, 34, 19, 8, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 6), hits 5 (1, 14), hits 5 (1, 18), hits 5 (4, 27), hits 5 (5, 17), hits 5 (6, 16), hits 5 (11, 20), hits 5 (11, 23), hits 5 (14, 16), hits 5 (14, 21)] = [1, 6, 13, 32, 41, 34, 19, 8, 1, 0, 0]
  rw [count5, row5_1_6, row5_1_14, row5_1_18, row5_4_27, row5_5_17, row5_6_16, row5_11_20, row5_11_23, row5_14_16, row5_14_21] <;> decide

theorem n5_082 : spectrum 5 [(2, 4), (2, 5), (3, 13), (4, 11), (4, 27), (5, 26), (6, 11), (7, 27), (8, 22), (11, 23)] = [0, 3, 18, 40, 36, 28, 18, 8, 3, 1, 0] := by
  change histogram (planes 5).length [hits 5 (2, 4), hits 5 (2, 5), hits 5 (3, 13), hits 5 (4, 11), hits 5 (4, 27), hits 5 (5, 26), hits 5 (6, 11), hits 5 (7, 27), hits 5 (8, 22), hits 5 (11, 23)] = [0, 3, 18, 40, 36, 28, 18, 8, 3, 1, 0]
  rw [count5, row5_2_4, row5_2_5, row5_3_13, row5_4_11, row5_4_27, row5_5_26, row5_6_11, row5_7_27, row5_8_22, row5_11_23] <;> decide

theorem n5_083 : spectrum 5 [(2, 17), (3, 20), (3, 28), (4, 8), (6, 8), (9, 22), (10, 18), (11, 21), (12, 23), (13, 18)] = [1, 3, 15, 28, 44, 43, 15, 6, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 17), hits 5 (3, 20), hits 5 (3, 28), hits 5 (4, 8), hits 5 (6, 8), hits 5 (9, 22), hits 5 (10, 18), hits 5 (11, 21), hits 5 (12, 23), hits 5 (13, 18)] = [1, 3, 15, 28, 44, 43, 15, 6, 0, 0, 0]
  rw [count5, row5_2_17, row5_3_20, row5_3_28, row5_4_8, row5_6_8, row5_9_22, row5_10_18, row5_11_21, row5_12_23, row5_13_18] <;> decide

theorem n5_084 : spectrum 5 [(1, 18), (2, 28), (3, 9), (5, 16), (5, 26), (7, 9)] = [3, 26, 52, 48, 20, 6, 0] := by
  change histogram (planes 5).length [hits 5 (1, 18), hits 5 (2, 28), hits 5 (3, 9), hits 5 (5, 16), hits 5 (5, 26), hits 5 (7, 9)] = [3, 26, 52, 48, 20, 6, 0]
  rw [count5, row5_1_18, row5_2_28, row5_3_9, row5_5_16, row5_5_26, row5_7_9] <;> decide

theorem n5_085 : spectrum 5 [(1, 8), (1, 12), (2, 12), (2, 13), (2, 17), (3, 12), (6, 11), (7, 26), (8, 23), (11, 19), (14, 19), (15, 17)] = [0, 1, 12, 23, 24, 37, 28, 17, 11, 2, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 8), hits 5 (1, 12), hits 5 (2, 12), hits 5 (2, 13), hits 5 (2, 17), hits 5 (3, 12), hits 5 (6, 11), hits 5 (7, 26), hits 5 (8, 23), hits 5 (11, 19), hits 5 (14, 19), hits 5 (15, 17)] = [0, 1, 12, 23, 24, 37, 28, 17, 11, 2, 0, 0, 0]
  rw [count5, row5_1_8, row5_1_12, row5_2_12, row5_2_13, row5_2_17, row5_3_12, row5_6_11, row5_7_26, row5_8_23, row5_11_19, row5_14_19, row5_15_17] <;> decide

theorem n5_086 : spectrum 5 [(1, 6), (1, 18), (1, 24), (3, 16), (4, 19), (4, 25), (5, 8), (5, 18), (10, 17), (13, 20)] = [1, 3, 19, 32, 40, 35, 11, 10, 4, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 6), hits 5 (1, 18), hits 5 (1, 24), hits 5 (3, 16), hits 5 (4, 19), hits 5 (4, 25), hits 5 (5, 8), hits 5 (5, 18), hits 5 (10, 17), hits 5 (13, 20)] = [1, 3, 19, 32, 40, 35, 11, 10, 4, 0, 0]
  rw [count5, row5_1_6, row5_1_18, row5_1_24, row5_3_16, row5_4_19, row5_4_25, row5_5_8, row5_5_18, row5_10_17, row5_13_20] <;> decide

theorem n5_087 : spectrum 5 [(2, 8), (3, 25), (3, 28), (6, 18), (13, 22), (14, 17), (14, 20)] = [3, 17, 41, 46, 30, 17, 1, 0] := by
  change histogram (planes 5).length [hits 5 (2, 8), hits 5 (3, 25), hits 5 (3, 28), hits 5 (6, 18), hits 5 (13, 22), hits 5 (14, 17), hits 5 (14, 20)] = [3, 17, 41, 46, 30, 17, 1, 0]
  rw [count5, row5_2_8, row5_3_25, row5_3_28, row5_6_18, row5_13_22, row5_14_17, row5_14_20] <;> decide

theorem n5_088 : spectrum 5 [(1, 6), (3, 4), (3, 12), (3, 24), (4, 9), (4, 16), (6, 11), (7, 16), (7, 27), (9, 23), (11, 21), (12, 16), (13, 16), (14, 22)] = [0, 0, 4, 14, 19, 38, 32, 18, 15, 10, 4, 0, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 6), hits 5 (3, 4), hits 5 (3, 12), hits 5 (3, 24), hits 5 (4, 9), hits 5 (4, 16), hits 5 (6, 11), hits 5 (7, 16), hits 5 (7, 27), hits 5 (9, 23), hits 5 (11, 21), hits 5 (12, 16), hits 5 (13, 16), hits 5 (14, 22)] = [0, 0, 4, 14, 19, 38, 32, 18, 15, 10, 4, 0, 1, 0, 0]
  rw [count5, row5_1_6, row5_3_4, row5_3_12, row5_3_24, row5_4_9, row5_4_16, row5_6_11, row5_7_16, row5_7_27, row5_9_23, row5_11_21, row5_12_16, row5_13_16, row5_14_22] <;> decide

theorem n5_089 : spectrum 5 [(1, 2), (1, 6), (1, 26), (3, 25), (4, 17), (5, 8), (5, 9), (5, 26), (7, 9), (7, 26), (10, 17), (11, 17), (13, 20), (15, 17)] = [0, 0, 6, 12, 23, 31, 24, 32, 18, 3, 4, 2, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 2), hits 5 (1, 6), hits 5 (1, 26), hits 5 (3, 25), hits 5 (4, 17), hits 5 (5, 8), hits 5 (5, 9), hits 5 (5, 26), hits 5 (7, 9), hits 5 (7, 26), hits 5 (10, 17), hits 5 (11, 17), hits 5 (13, 20), hits 5 (15, 17)] = [0, 0, 6, 12, 23, 31, 24, 32, 18, 3, 4, 2, 0, 0, 0]
  rw [count5, row5_1_2, row5_1_6, row5_1_26, row5_3_25, row5_4_17, row5_5_8, row5_5_9, row5_5_26, row5_7_9, row5_7_26, row5_10_17, row5_11_17, row5_13_20, row5_15_17] <;> decide

theorem n5_090 : spectrum 5 [(2, 8), (2, 29), (4, 18), (6, 9), (6, 27), (7, 19), (7, 24), (8, 18), (8, 20), (8, 23), (11, 22)] = [1, 2, 11, 31, 36, 30, 23, 15, 4, 2, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 8), hits 5 (2, 29), hits 5 (4, 18), hits 5 (6, 9), hits 5 (6, 27), hits 5 (7, 19), hits 5 (7, 24), hits 5 (8, 18), hits 5 (8, 20), hits 5 (8, 23), hits 5 (11, 22)] = [1, 2, 11, 31, 36, 30, 23, 15, 4, 2, 0, 0]
  rw [count5, row5_2_8, row5_2_29, row5_4_18, row5_6_9, row5_6_27, row5_7_19, row5_7_24, row5_8_18, row5_8_20, row5_8_23, row5_11_22] <;> decide

theorem n5_091 : spectrum 5 [(2, 12), (5, 27), (6, 27), (9, 17), (11, 19), (14, 22), (15, 17), (15, 18), (15, 20)] = [3, 4, 33, 27, 42, 26, 13, 7, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 12), hits 5 (5, 27), hits 5 (6, 27), hits 5 (9, 17), hits 5 (11, 19), hits 5 (14, 22), hits 5 (15, 17), hits 5 (15, 18), hits 5 (15, 20)] = [3, 4, 33, 27, 42, 26, 13, 7, 0, 0]
  rw [count5, row5_2_12, row5_5_27, row5_6_27, row5_9_17, row5_11_19, row5_14_22, row5_15_17, row5_15_18, row5_15_20] <;> decide

theorem n5_092 : spectrum 5 [(1, 22), (1, 28), (2, 29), (3, 13), (3, 28), (4, 24), (6, 10), (6, 18), (7, 18), (8, 19), (10, 17), (11, 19), (11, 22), (15, 20)] = [0, 0, 3, 10, 18, 35, 40, 29, 13, 5, 1, 1, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 22), hits 5 (1, 28), hits 5 (2, 29), hits 5 (3, 13), hits 5 (3, 28), hits 5 (4, 24), hits 5 (6, 10), hits 5 (6, 18), hits 5 (7, 18), hits 5 (8, 19), hits 5 (10, 17), hits 5 (11, 19), hits 5 (11, 22), hits 5 (15, 20)] = [0, 0, 3, 10, 18, 35, 40, 29, 13, 5, 1, 1, 0, 0, 0]
  rw [count5, row5_1_22, row5_1_28, row5_2_29, row5_3_13, row5_3_28, row5_4_24, row5_6_10, row5_6_18, row5_7_18, row5_8_19, row5_10_17, row5_11_19, row5_11_22, row5_15_20] <;> decide

theorem n5_093 : spectrum 5 [(3, 25), (3, 28), (6, 18), (10, 16), (10, 20), (13, 21), (15, 16), (15, 22)] = [1, 12, 30, 49, 35, 18, 8, 1, 1] := by
  change histogram (planes 5).length [hits 5 (3, 25), hits 5 (3, 28), hits 5 (6, 18), hits 5 (10, 16), hits 5 (10, 20), hits 5 (13, 21), hits 5 (15, 16), hits 5 (15, 22)] = [1, 12, 30, 49, 35, 18, 8, 1, 1]
  rw [count5, row5_3_25, row5_3_28, row5_6_18, row5_10_16, row5_10_20, row5_13_21, row5_15_16, row5_15_22] <;> decide

theorem n5_094 : spectrum 5 [(1, 14), (2, 24), (6, 25), (10, 16), (10, 17), (11, 17), (11, 18), (12, 17), (15, 17), (15, 18)] = [0, 6, 19, 33, 39, 29, 13, 11, 4, 1, 0] := by
  change histogram (planes 5).length [hits 5 (1, 14), hits 5 (2, 24), hits 5 (6, 25), hits 5 (10, 16), hits 5 (10, 17), hits 5 (11, 17), hits 5 (11, 18), hits 5 (12, 17), hits 5 (15, 17), hits 5 (15, 18)] = [0, 6, 19, 33, 39, 29, 13, 11, 4, 1, 0]
  rw [count5, row5_1_14, row5_2_24, row5_6_25, row5_10_16, row5_10_17, row5_11_17, row5_11_18, row5_12_17, row5_15_17, row5_15_18] <;> decide

theorem n5_095 : spectrum 5 [(2, 25), (3, 25), (5, 16), (6, 16), (7, 19), (10, 18), (10, 23), (11, 16), (11, 18), (13, 19), (15, 16)] = [1, 6, 7, 19, 39, 45, 25, 9, 3, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 25), hits 5 (3, 25), hits 5 (5, 16), hits 5 (6, 16), hits 5 (7, 19), hits 5 (10, 18), hits 5 (10, 23), hits 5 (11, 16), hits 5 (11, 18), hits 5 (13, 19), hits 5 (15, 16)] = [1, 6, 7, 19, 39, 45, 25, 9, 3, 1, 0, 0]
  rw [count5, row5_2_25, row5_3_25, row5_5_16, row5_6_16, row5_7_19, row5_10_18, row5_10_23, row5_11_16, row5_11_18, row5_13_19, row5_15_16] <;> decide

theorem n5_096 : spectrum 5 [(3, 20), (6, 8), (6, 18), (8, 21), (9, 23), (11, 23), (12, 20), (13, 19), (13, 21), (14, 22)] = [0, 5, 18, 37, 35, 28, 20, 9, 2, 1, 0] := by
  change histogram (planes 5).length [hits 5 (3, 20), hits 5 (6, 8), hits 5 (6, 18), hits 5 (8, 21), hits 5 (9, 23), hits 5 (11, 23), hits 5 (12, 20), hits 5 (13, 19), hits 5 (13, 21), hits 5 (14, 22)] = [0, 5, 18, 37, 35, 28, 20, 9, 2, 1, 0]
  rw [count5, row5_3_20, row5_6_8, row5_6_18, row5_8_21, row5_9_23, row5_11_23, row5_12_20, row5_13_19, row5_13_21, row5_14_22] <;> decide

theorem n5_097 : spectrum 5 [(1, 10), (1, 26), (2, 8), (6, 11), (9, 23), (11, 21), (13, 20)] = [2, 22, 38, 45, 31, 12, 4, 1] := by
  change histogram (planes 5).length [hits 5 (1, 10), hits 5 (1, 26), hits 5 (2, 8), hits 5 (6, 11), hits 5 (9, 23), hits 5 (11, 21), hits 5 (13, 20)] = [2, 22, 38, 45, 31, 12, 4, 1]
  rw [count5, row5_1_10, row5_1_26, row5_2_8, row5_6_11, row5_9_23, row5_11_21, row5_13_20] <;> decide

theorem n5_098 : spectrum 5 [(2, 29), (3, 5), (3, 9), (5, 9), (5, 19), (6, 27), (9, 16), (9, 21), (9, 22), (12, 17), (12, 19), (12, 23), (14, 18), (15, 22)] = [0, 3, 9, 7, 19, 24, 42, 21, 18, 7, 3, 2, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 29), hits 5 (3, 5), hits 5 (3, 9), hits 5 (5, 9), hits 5 (5, 19), hits 5 (6, 27), hits 5 (9, 16), hits 5 (9, 21), hits 5 (9, 22), hits 5 (12, 17), hits 5 (12, 19), hits 5 (12, 23), hits 5 (14, 18), hits 5 (15, 22)] = [0, 3, 9, 7, 19, 24, 42, 21, 18, 7, 3, 2, 0, 0, 0]
  rw [count5, row5_2_29, row5_3_5, row5_3_9, row5_5_9, row5_5_19, row5_6_27, row5_9_16, row5_9_21, row5_9_22, row5_12_17, row5_12_19, row5_12_23, row5_14_18, row5_15_22] <;> decide

theorem n5_099 : spectrum 5 [(1, 10), (3, 5), (3, 9), (5, 17), (6, 8), (6, 18), (6, 25), (7, 24), (11, 23), (12, 19), (14, 17), (15, 17), (15, 23)] = [0, 2, 6, 16, 27, 31, 28, 26, 14, 5, 0, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 10), hits 5 (3, 5), hits 5 (3, 9), hits 5 (5, 17), hits 5 (6, 8), hits 5 (6, 18), hits 5 (6, 25), hits 5 (7, 24), hits 5 (11, 23), hits 5 (12, 19), hits 5 (14, 17), hits 5 (15, 17), hits 5 (15, 23)] = [0, 2, 6, 16, 27, 31, 28, 26, 14, 5, 0, 0, 0, 0]
  rw [count5, row5_1_10, row5_3_5, row5_3_9, row5_5_17, row5_6_8, row5_6_18, row5_6_25, row5_7_24, row5_11_23, row5_12_19, row5_14_17, row5_15_17, row5_15_23] <;> decide

theorem n5_100 : spectrum 5 [(3, 13), (3, 20), (3, 29), (4, 25), (5, 11), (6, 11), (8, 19), (10, 16), (13, 16), (13, 18)] = [1, 7, 14, 36, 35, 27, 24, 10, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (3, 13), hits 5 (3, 20), hits 5 (3, 29), hits 5 (4, 25), hits 5 (5, 11), hits 5 (6, 11), hits 5 (8, 19), hits 5 (10, 16), hits 5 (13, 16), hits 5 (13, 18)] = [1, 7, 14, 36, 35, 27, 24, 10, 1, 0, 0]
  rw [count5, row5_3_13, row5_3_20, row5_3_29, row5_4_25, row5_5_11, row5_6_11, row5_8_19, row5_10_16, row5_13_16, row5_13_18] <;> decide

theorem n5_101 : spectrum 5 [(1, 12), (3, 8), (5, 11), (5, 19), (6, 26), (7, 24), (8, 20), (9, 19), (10, 19), (13, 16), (13, 22)] = [0, 2, 10, 31, 31, 36, 32, 11, 2, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 12), hits 5 (3, 8), hits 5 (5, 11), hits 5 (5, 19), hits 5 (6, 26), hits 5 (7, 24), hits 5 (8, 20), hits 5 (9, 19), hits 5 (10, 19), hits 5 (13, 16), hits 5 (13, 22)] = [0, 2, 10, 31, 31, 36, 32, 11, 2, 0, 0, 0]
  rw [count5, row5_1_12, row5_3_8, row5_5_11, row5_5_19, row5_6_26, row5_7_24, row5_8_20, row5_9_19, row5_10_19, row5_13_16, row5_13_22] <;> decide

theorem n5_102 : spectrum 5 [(2, 9), (6, 17), (12, 16), (12, 18), (13, 23), (14, 22), (14, 23)] = [3, 18, 38, 48, 32, 14, 2, 0] := by
  change histogram (planes 5).length [hits 5 (2, 9), hits 5 (6, 17), hits 5 (12, 16), hits 5 (12, 18), hits 5 (13, 23), hits 5 (14, 22), hits 5 (14, 23)] = [3, 18, 38, 48, 32, 14, 2, 0]
  rw [count5, row5_2_9, row5_6_17, row5_12_16, row5_12_18, row5_13_23, row5_14_22, row5_14_23] <;> decide

theorem n5_103 : spectrum 5 [(2, 12), (5, 10), (6, 10), (6, 16), (7, 27), (9, 23), (12, 17)] = [2, 18, 45, 36, 41, 10, 3, 0] := by
  change histogram (planes 5).length [hits 5 (2, 12), hits 5 (5, 10), hits 5 (6, 10), hits 5 (6, 16), hits 5 (7, 27), hits 5 (9, 23), hits 5 (12, 17)] = [2, 18, 45, 36, 41, 10, 3, 0]
  rw [count5, row5_2_12, row5_5_10, row5_6_10, row5_6_16, row5_7_27, row5_9_23, row5_12_17] <;> decide

theorem n5_104 : spectrum 5 [(2, 16), (3, 8), (4, 11), (4, 26), (5, 10), (6, 17), (9, 23), (14, 20), (15, 19), (15, 23)] = [0, 8, 17, 29, 32, 38, 25, 5, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 16), hits 5 (3, 8), hits 5 (4, 11), hits 5 (4, 26), hits 5 (5, 10), hits 5 (6, 17), hits 5 (9, 23), hits 5 (14, 20), hits 5 (15, 19), hits 5 (15, 23)] = [0, 8, 17, 29, 32, 38, 25, 5, 1, 0, 0]
  rw [count5, row5_2_16, row5_3_8, row5_4_11, row5_4_26, row5_5_10, row5_6_17, row5_9_23, row5_14_20, row5_15_19, row5_15_23] <;> decide

theorem n5_105 : spectrum 5 [(1, 2), (2, 4), (3, 24), (3, 28), (6, 9), (6, 18), (7, 11), (7, 26), (9, 18), (10, 20), (11, 23), (14, 20)] = [0, 2, 8, 18, 31, 40, 31, 18, 4, 2, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 2), hits 5 (2, 4), hits 5 (3, 24), hits 5 (3, 28), hits 5 (6, 9), hits 5 (6, 18), hits 5 (7, 11), hits 5 (7, 26), hits 5 (9, 18), hits 5 (10, 20), hits 5 (11, 23), hits 5 (14, 20)] = [0, 2, 8, 18, 31, 40, 31, 18, 4, 2, 1, 0, 0]
  rw [count5, row5_1_2, row5_2_4, row5_3_24, row5_3_28, row5_6_9, row5_6_18, row5_7_11, row5_7_26, row5_9_18, row5_10_20, row5_11_23, row5_14_20] <;> decide

theorem n5_106 : spectrum 5 [(2, 17), (2, 25), (3, 4), (3, 12), (3, 20), (3, 21), (4, 8), (4, 10), (4, 16), (6, 18), (9, 23), (13, 20)] = [0, 1, 11, 23, 33, 27, 25, 25, 6, 4, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 17), hits 5 (2, 25), hits 5 (3, 4), hits 5 (3, 12), hits 5 (3, 20), hits 5 (3, 21), hits 5 (4, 8), hits 5 (4, 10), hits 5 (4, 16), hits 5 (6, 18), hits 5 (9, 23), hits 5 (13, 20)] = [0, 1, 11, 23, 33, 27, 25, 25, 6, 4, 0, 0, 0]
  rw [count5, row5_2_17, row5_2_25, row5_3_4, row5_3_12, row5_3_20, row5_3_21, row5_4_8, row5_4_10, row5_4_16, row5_6_18, row5_9_23, row5_13_20] <;> decide

theorem n5_107 : spectrum 5 [(1, 30), (2, 20), (2, 21), (2, 25), (3, 13), (4, 9), (4, 25), (5, 27), (6, 8), (6, 26), (8, 22), (11, 21), (13, 23), (15, 21)] = [0, 1, 2, 11, 27, 29, 28, 34, 14, 4, 4, 1, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 30), hits 5 (2, 20), hits 5 (2, 21), hits 5 (2, 25), hits 5 (3, 13), hits 5 (4, 9), hits 5 (4, 25), hits 5 (5, 27), hits 5 (6, 8), hits 5 (6, 26), hits 5 (8, 22), hits 5 (11, 21), hits 5 (13, 23), hits 5 (15, 21)] = [0, 1, 2, 11, 27, 29, 28, 34, 14, 4, 4, 1, 0, 0, 0]
  rw [count5, row5_1_30, row5_2_20, row5_2_21, row5_2_25, row5_3_13, row5_4_9, row5_4_25, row5_5_27, row5_6_8, row5_6_26, row5_8_22, row5_11_21, row5_13_23, row5_15_21] <;> decide

theorem n5_108 : spectrum 5 [(2, 13), (2, 29), (3, 20), (3, 24), (3, 25), (4, 16), (5, 16), (5, 19), (6, 19), (7, 10), (9, 21)] = [0, 4, 11, 19, 42, 34, 35, 7, 3, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 13), hits 5 (2, 29), hits 5 (3, 20), hits 5 (3, 24), hits 5 (3, 25), hits 5 (4, 16), hits 5 (5, 16), hits 5 (5, 19), hits 5 (6, 19), hits 5 (7, 10), hits 5 (9, 21)] = [0, 4, 11, 19, 42, 34, 35, 7, 3, 0, 0, 0]
  rw [count5, row5_2_13, row5_2_29, row5_3_20, row5_3_24, row5_3_25, row5_4_16, row5_5_16, row5_5_19, row5_6_19, row5_7_10, row5_9_21] <;> decide

theorem n5_109 : spectrum 5 [(1, 16), (3, 13), (3, 24), (3, 25), (6, 9), (6, 19), (7, 26), (9, 19), (10, 17), (12, 16), (13, 16)] = [1, 2, 13, 26, 32, 39, 25, 12, 4, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 16), hits 5 (3, 13), hits 5 (3, 24), hits 5 (3, 25), hits 5 (6, 9), hits 5 (6, 19), hits 5 (7, 26), hits 5 (9, 19), hits 5 (10, 17), hits 5 (12, 16), hits 5 (13, 16)] = [1, 2, 13, 26, 32, 39, 25, 12, 4, 1, 0, 0]
  rw [count5, row5_1_16, row5_3_13, row5_3_24, row5_3_25, row5_6_9, row5_6_19, row5_7_26, row5_9_19, row5_10_17, row5_12_16, row5_13_16] <;> decide

theorem n5_110 : spectrum 5 [(3, 28), (4, 24), (5, 9), (6, 11), (7, 16), (7, 24), (8, 20), (11, 17), (13, 16)] = [1, 10, 16, 40, 46, 26, 12, 4, 0, 0] := by
  change histogram (planes 5).length [hits 5 (3, 28), hits 5 (4, 24), hits 5 (5, 9), hits 5 (6, 11), hits 5 (7, 16), hits 5 (7, 24), hits 5 (8, 20), hits 5 (11, 17), hits 5 (13, 16)] = [1, 10, 16, 40, 46, 26, 12, 4, 0, 0]
  rw [count5, row5_3_28, row5_4_24, row5_5_9, row5_6_11, row5_7_16, row5_7_24, row5_8_20, row5_11_17, row5_13_16] <;> decide

theorem n5_111 : spectrum 5 [(1, 16), (2, 24), (4, 27), (7, 18), (7, 25), (9, 17), (12, 20), (13, 17), (14, 23)] = [1, 5, 23, 42, 40, 29, 11, 4, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 16), hits 5 (2, 24), hits 5 (4, 27), hits 5 (7, 18), hits 5 (7, 25), hits 5 (9, 17), hits 5 (12, 20), hits 5 (13, 17), hits 5 (14, 23)] = [1, 5, 23, 42, 40, 29, 11, 4, 0, 0]
  rw [count5, row5_1_16, row5_2_24, row5_4_27, row5_7_18, row5_7_25, row5_9_17, row5_12_20, row5_13_17, row5_14_23] <;> decide

theorem n5_112 : spectrum 5 [(2, 24), (4, 11), (5, 17), (7, 19), (8, 18), (12, 18), (13, 21)] = [1, 19, 39, 50, 32, 11, 3, 0] := by
  change histogram (planes 5).length [hits 5 (2, 24), hits 5 (4, 11), hits 5 (5, 17), hits 5 (7, 19), hits 5 (8, 18), hits 5 (12, 18), hits 5 (13, 21)] = [1, 19, 39, 50, 32, 11, 3, 0]
  rw [count5, row5_2_24, row5_4_11, row5_5_17, row5_7_19, row5_8_18, row5_12_18, row5_13_21] <;> decide

theorem n5_113 : spectrum 5 [(1, 14), (1, 24), (1, 28), (3, 28), (5, 16), (6, 11), (8, 17), (15, 18)] = [2, 6, 36, 53, 27, 20, 10, 1, 0] := by
  change histogram (planes 5).length [hits 5 (1, 14), hits 5 (1, 24), hits 5 (1, 28), hits 5 (3, 28), hits 5 (5, 16), hits 5 (6, 11), hits 5 (8, 17), hits 5 (15, 18)] = [2, 6, 36, 53, 27, 20, 10, 1, 0]
  rw [count5, row5_1_14, row5_1_24, row5_1_28, row5_3_28, row5_5_16, row5_6_11, row5_8_17, row5_15_18] <;> decide

theorem n5_114 : spectrum 5 [(1, 22), (1, 26), (4, 9), (6, 8), (8, 16), (8, 17), (9, 18), (14, 17), (15, 22)] = [3, 9, 16, 39, 40, 31, 16, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 22), hits 5 (1, 26), hits 5 (4, 9), hits 5 (6, 8), hits 5 (8, 16), hits 5 (8, 17), hits 5 (9, 18), hits 5 (14, 17), hits 5 (15, 22)] = [3, 9, 16, 39, 40, 31, 16, 1, 0, 0]
  rw [count5, row5_1_22, row5_1_26, row5_4_9, row5_6_8, row5_8_16, row5_8_17, row5_9_18, row5_14_17, row5_15_22] <;> decide

theorem n5_115 : spectrum 5 [(1, 18), (1, 30), (6, 18), (7, 19), (8, 20), (12, 17), (12, 18), (12, 19), (13, 21), (15, 17)] = [1, 9, 18, 26, 36, 34, 18, 10, 2, 1, 0] := by
  change histogram (planes 5).length [hits 5 (1, 18), hits 5 (1, 30), hits 5 (6, 18), hits 5 (7, 19), hits 5 (8, 20), hits 5 (12, 17), hits 5 (12, 18), hits 5 (12, 19), hits 5 (13, 21), hits 5 (15, 17)] = [1, 9, 18, 26, 36, 34, 18, 10, 2, 1, 0]
  rw [count5, row5_1_18, row5_1_30, row5_6_18, row5_7_19, row5_8_20, row5_12_17, row5_12_18, row5_12_19, row5_13_21, row5_15_17] <;> decide

theorem n5_116 : spectrum 5 [(2, 9), (3, 13), (4, 11), (7, 25), (8, 17), (8, 19), (9, 18), (9, 19), (11, 16), (15, 22)] = [1, 7, 16, 30, 39, 31, 18, 12, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 9), hits 5 (3, 13), hits 5 (4, 11), hits 5 (7, 25), hits 5 (8, 17), hits 5 (8, 19), hits 5 (9, 18), hits 5 (9, 19), hits 5 (11, 16), hits 5 (15, 22)] = [1, 7, 16, 30, 39, 31, 18, 12, 1, 0, 0]
  rw [count5, row5_2_9, row5_3_13, row5_4_11, row5_7_25, row5_8_17, row5_8_19, row5_9_18, row5_9_19, row5_11_16, row5_15_22] <;> decide

theorem n5_117 : spectrum 5 [(4, 27), (5, 9), (5, 19), (6, 10), (7, 24), (9, 20), (11, 17), (12, 18), (14, 16), (15, 17)] = [1, 2, 20, 21, 53, 36, 14, 5, 3, 0, 0] := by
  change histogram (planes 5).length [hits 5 (4, 27), hits 5 (5, 9), hits 5 (5, 19), hits 5 (6, 10), hits 5 (7, 24), hits 5 (9, 20), hits 5 (11, 17), hits 5 (12, 18), hits 5 (14, 16), hits 5 (15, 17)] = [1, 2, 20, 21, 53, 36, 14, 5, 3, 0, 0]
  rw [count5, row5_4_27, row5_5_9, row5_5_19, row5_6_10, row5_7_24, row5_9_20, row5_11_17, row5_12_18, row5_14_16, row5_15_17] <;> decide

theorem n5_118 : spectrum 5 [(1, 4), (3, 13), (4, 8), (6, 16), (7, 10), (8, 17), (11, 22), (12, 18), (15, 22)] = [2, 7, 19, 37, 45, 33, 9, 3, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 4), hits 5 (3, 13), hits 5 (4, 8), hits 5 (6, 16), hits 5 (7, 10), hits 5 (8, 17), hits 5 (11, 22), hits 5 (12, 18), hits 5 (15, 22)] = [2, 7, 19, 37, 45, 33, 9, 3, 0, 0]
  rw [count5, row5_1_4, row5_3_13, row5_4_8, row5_6_16, row5_7_10, row5_8_17, row5_11_22, row5_12_18, row5_15_22] <;> decide

theorem n5_119 : spectrum 5 [(2, 4), (2, 9), (2, 25), (2, 28), (3, 8), (3, 24), (4, 16), (5, 16), (6, 25), (8, 17), (9, 23), (10, 19), (14, 21)] = [1, 0, 4, 18, 26, 38, 30, 18, 12, 6, 2, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 4), hits 5 (2, 9), hits 5 (2, 25), hits 5 (2, 28), hits 5 (3, 8), hits 5 (3, 24), hits 5 (4, 16), hits 5 (5, 16), hits 5 (6, 25), hits 5 (8, 17), hits 5 (9, 23), hits 5 (10, 19), hits 5 (14, 21)] = [1, 0, 4, 18, 26, 38, 30, 18, 12, 6, 2, 0, 0, 0]
  rw [count5, row5_2_4, row5_2_9, row5_2_25, row5_2_28, row5_3_8, row5_3_24, row5_4_16, row5_5_16, row5_6_25, row5_8_17, row5_9_23, row5_10_19, row5_14_21] <;> decide

theorem n5_120 : spectrum 5 [(1, 14), (1, 16), (1, 18), (2, 12), (2, 24), (4, 19), (4, 26), (5, 10), (6, 24), (7, 24)] = [1, 5, 12, 36, 43, 33, 14, 6, 5, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 14), hits 5 (1, 16), hits 5 (1, 18), hits 5 (2, 12), hits 5 (2, 24), hits 5 (4, 19), hits 5 (4, 26), hits 5 (5, 10), hits 5 (6, 24), hits 5 (7, 24)] = [1, 5, 12, 36, 43, 33, 14, 6, 5, 0, 0]
  rw [count5, row5_1_14, row5_1_16, row5_1_18, row5_2_12, row5_2_24, row5_4_19, row5_4_26, row5_5_10, row5_6_24, row5_7_24] <;> decide

theorem n5_121 : spectrum 5 [(2, 9), (5, 9), (7, 8), (8, 18), (9, 22), (11, 19), (12, 16), (14, 19)] = [2, 12, 29, 44, 37, 24, 7, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 9), hits 5 (5, 9), hits 5 (7, 8), hits 5 (8, 18), hits 5 (9, 22), hits 5 (11, 19), hits 5 (12, 16), hits 5 (14, 19)] = [2, 12, 29, 44, 37, 24, 7, 0, 0]
  rw [count5, row5_2_9, row5_5_9, row5_7_8, row5_8_18, row5_9_22, row5_11_19, row5_12_16, row5_14_19] <;> decide

theorem n5_122 : spectrum 5 [(1, 4), (2, 29), (4, 24), (5, 9), (7, 16), (7, 19), (10, 16), (12, 22), (14, 22), (15, 16)] = [1, 2, 14, 41, 39, 28, 20, 9, 1, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 4), hits 5 (2, 29), hits 5 (4, 24), hits 5 (5, 9), hits 5 (7, 16), hits 5 (7, 19), hits 5 (10, 16), hits 5 (12, 22), hits 5 (14, 22), hits 5 (15, 16)] = [1, 2, 14, 41, 39, 28, 20, 9, 1, 0, 0]
  rw [count5, row5_1_4, row5_2_29, row5_4_24, row5_5_9, row5_7_16, row5_7_19, row5_10_16, row5_12_22, row5_14_22, row5_15_16] <;> decide

theorem n5_123 : spectrum 5 [(2, 28), (3, 5), (3, 9), (3, 24), (3, 28), (4, 9), (5, 26), (9, 21), (10, 16), (15, 22)] = [1, 7, 16, 33, 34, 33, 20, 7, 4, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 28), hits 5 (3, 5), hits 5 (3, 9), hits 5 (3, 24), hits 5 (3, 28), hits 5 (4, 9), hits 5 (5, 26), hits 5 (9, 21), hits 5 (10, 16), hits 5 (15, 22)] = [1, 7, 16, 33, 34, 33, 20, 7, 4, 0, 0]
  rw [count5, row5_2_28, row5_3_5, row5_3_9, row5_3_24, row5_3_28, row5_4_9, row5_5_26, row5_9_21, row5_10_16, row5_15_22] <;> decide

theorem n5_124 : spectrum 5 [(1, 16), (3, 29), (4, 10), (5, 11), (6, 17), (7, 18), (11, 20), (11, 21), (12, 21), (13, 21), (14, 21), (15, 22)] = [1, 0, 11, 23, 23, 35, 33, 21, 7, 1, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (1, 16), hits 5 (3, 29), hits 5 (4, 10), hits 5 (5, 11), hits 5 (6, 17), hits 5 (7, 18), hits 5 (11, 20), hits 5 (11, 21), hits 5 (12, 21), hits 5 (13, 21), hits 5 (14, 21), hits 5 (15, 22)] = [1, 0, 11, 23, 23, 35, 33, 21, 7, 1, 0, 0, 0]
  rw [count5, row5_1_16, row5_3_29, row5_4_10, row5_5_11, row5_6_17, row5_7_18, row5_11_20, row5_11_21, row5_12_21, row5_13_21, row5_14_21, row5_15_22] <;> decide

theorem n5_125 : spectrum 5 [(2, 17), (2, 21), (4, 8), (4, 27), (6, 17), (6, 24), (8, 18), (9, 21), (10, 17), (10, 19), (11, 16), (14, 22)] = [1, 0, 9, 20, 23, 44, 35, 16, 7, 0, 0, 0, 0] := by
  change histogram (planes 5).length [hits 5 (2, 17), hits 5 (2, 21), hits 5 (4, 8), hits 5 (4, 27), hits 5 (6, 17), hits 5 (6, 24), hits 5 (8, 18), hits 5 (9, 21), hits 5 (10, 17), hits 5 (10, 19), hits 5 (11, 16), hits 5 (14, 22)] = [1, 0, 9, 20, 23, 44, 35, 16, 7, 0, 0, 0, 0]
  rw [count5, row5_2_17, row5_2_21, row5_4_8, row5_4_27, row5_6_17, row5_6_24, row5_8_18, row5_9_21, row5_10_17, row5_10_19, row5_11_16, row5_14_22] <;> decide

end ShotD
