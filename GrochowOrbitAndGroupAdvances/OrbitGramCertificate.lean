import Std

namespace OrbitGramCertificate

abbrev Point := List Nat

def digits : List Nat := [0, 1, 2, 3]

-- Encode the elements of F₂[ω]/(ω² + ω + 1) as 0, 1, ω, ω + 1.
def mul4 (a b : Nat) : Nat :=
  let table := [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]
  (table[a]!)[b]!

def conjugate (a : Nat) : Nat := mul4 a a

def points : List Point :=
  [[1,0,0,0], [0,1,0,0], [0,0,1,0], [0,0,0,1],
   [1,2,0,0], [0,1,3,0], [0,0,1,1], [1,0,0,1], [1,1,1,1]]

def allVectors : List Point :=
  digits.flatMap fun a => digits.flatMap fun b =>
    digits.flatMap fun c => digits.map fun d => [a,b,c,d]

def normalized (p : Point) : Bool :=
  p.find? (· != 0) == some 1

def projectivePoints : List Point := allVectors.filter normalized

def scale (a : Nat) (v : Point) : Point := v.map (mul4 a)

def normalize (v : Point) : Point :=
  match v.find? (· != 0) with
  | none => v
  | some a => scale (conjugate a) v

def hermitianUpper (v : Point) : List Nat :=
  (List.range 4).flatMap fun i =>
    ((List.range 4).filter (i ≤ ·)).map fun j =>
      mul4 v[i]! (conjugate v[j]!)

def sums (vs : List (List Nat)) : List (List Nat) :=
  vs.foldl (fun prev v => prev ++ prev.map (List.zipWith Nat.xor v)) [List.replicate 10 0]

def hermitianRankOneCheck : Bool :=
  let span := sums (points.map hermitianUpper)
  projectivePoints.all fun v => span.contains (hermitianUpper v) == points.contains v

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
theorem rank_one_locus_check : hermitianRankOneCheck = true := by
  decide

def line (a b : Point) : List Point :=
  (a :: b :: [1,2,3].map (fun t => normalize (List.zipWith Nat.xor a (scale t b))))

def richLines : List (List Point) :=
  (points.flatMap fun a =>
    (points.filter (· != a)).map fun b => points.filter (line a b).contains).eraseDups.filter
      (fun xs => xs.length >= 3)

theorem rich_lines_check :
    richLines =
      [[points[0]!, points[1]!, points[4]!],
       [points[0]!, points[3]!, points[7]!],
       [points[1]!, points[2]!, points[5]!],
       [points[2]!, points[3]!, points[6]!]] := by
  decide

def frobeniusPermutationCheck : Bool :=
  (allVectors.filter fun p => p.eraseDups.length == 4).all fun p =>
    !(points.all fun v => points.contains (normalize (p.map fun i => conjugate v[i]!)))

theorem no_frobenius_coordinate_permutation : frobeniusPermutationCheck = true := by
  decide

#print axioms rank_one_locus_check
#print axioms rich_lines_check
#print axioms no_frobenius_coordinate_permutation

end OrbitGramCertificate
