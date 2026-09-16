import Mathlib

/-!
# Unequal binary ranks in the bent-design construction

An explicit counterexample to Hyun–Kwon–Wang–Wu (2026), Open Problem 7
(arXiv:2605.24355v1). All finite certificates are checked by kernel reduction.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BentDesign

abbrev F := ZMod 2
abbrev W := Fin 4 → F
abbrev V := W × W

def wordEquiv : W ≃ Fin 16 := finFunctionFinEquiv

def pointEquiv : V ≃ Fin 256 :=
  (Equiv.prodCongr wordEquiv wordEquiv).trans finProdFinEquiv

def dot (x y : W) : F := ∑ i, x i * y i

def sign (a : F) : ℤ := if a = 0 then 1 else -1

lemma sign_add (a b : F) : sign (a + b) = sign a * sign b := by
  revert a b
  decide

lemma dot_add (x y z : W) : dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_comm (x y : W) : dot x y = dot y x := by
  simp [dot, mul_comm]

lemma orthogonality (t : W) : (∑ x : W, sign (dot x t)) = if t = 0 then 16 else 0 := by
  have cert : ∀ t : Fin 16,
      (∑ x : Fin 16, sign (dot (wordEquiv.symm x) (wordEquiv.symm t))) =
        if wordEquiv.symm t = 0 then 16 else 0 := by decide +kernel
  have hs := Equiv.sum_comp wordEquiv.symm (fun x => sign (dot x t))
  rw [← hs]
  simpa using cert (wordEquiv t)

/-- The ordinary Walsh transform on the eight-dimensional binary vector space. -/
def walsh (f : V → F) (a : V) : ℤ :=
  ∑ z : V, sign (f z + dot a.1 z.1 + dot a.2 z.2)

def Bent (f : V → F) : Prop := ∀ a, walsh f a = 16 ∨ walsh f a = -16

/-- The sign convention for the dual of a bent function. -/
def HasDual (f d : V → F) : Prop := ∀ a, walsh f a = 16 * sign (d a)

def mm (p : W → W) (z : V) : F := dot z.1 (p z.2)

lemma walsh_mm (p : W ≃ W) (a : V) :
    walsh (mm p) a = 16 * sign (dot a.2 (p.symm a.1)) := by
  simp only [walsh, mm, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have inner (y : W) :
      (∑ x : W, sign (dot x (p y) + dot a.1 x + dot a.2 y)) =
        (if p y + a.1 = 0 then 16 else 0) * sign (dot a.2 y) := by
    simp_rw [dot_comm a.1, ← dot_add, sign_add]
    rw [← Finset.sum_mul, orthogonality]
  simp_rw [inner]
  have hz (y : W) : p y + a.1 = 0 ↔ y = p.symm a.1 := by
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]
    exact p.eq_symm_apply.symm
  simp_rw [hz]
  simp

/-- The explicit permutation, in least-significant-bit-first coordinates. -/
def piTable : Fin 16 → Fin 16 := ![0,7,14,10,11,13,1,6,5,3,9,15,2,8,12,4]

def pi (y : W) : W := wordEquiv.symm (piTable (wordEquiv y))

lemma pi_cycle (y : W) : pi (pi y) = pi y + y := by
  have cert : ∀ i : Fin 16, pi (pi (wordEquiv.symm i)) =
      pi (wordEquiv.symm i) + wordEquiv.symm i := by decide +kernel
  simpa using cert (wordEquiv y)

lemma pi_cube (y : W) : pi (pi (pi y)) = y := by
  have cert : ∀ i : Fin 16, pi (pi (pi (wordEquiv.symm i))) = wordEquiv.symm i := by
    decide +kernel
  simpa using cert (wordEquiv y)

def piEquiv : W ≃ W where
  toFun := pi
  invFun := pi ∘ pi
  left_inv := pi_cube
  right_inv := pi_cube

def g : V → F := mm (Equiv.refl W)
def h : V → F := mm piEquiv

def unpack {n : ℕ} (v : BitVec n) (j : Fin n) : F :=
  if v.getLsbD j then 1 else 0

def pack {n : ℕ} (v : Fin n → F) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun j => decide (v j = 1)))).cast (List.length_ofFn)

lemma unpack_pack {n : ℕ} (v : Fin n → F) (j : Fin n) : unpack (pack v) j = v j := by
  simp only [unpack, pack, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos j.isLt, Option.getD_some]
  have hv : ∀ a : F, (if decide (a = 1) then (1 : F) else 0) = a := by decide
  exact hv _

lemma unpack_xor {n : ℕ} (u v : BitVec n) (j : Fin n) :
    unpack (u ^^^ v) j = unpack u j + unpack v j := by
  simp only [unpack, BitVec.getLsbD_xor]
  cases u.getLsbD j <;> cases v.getLsbD j <;> decide

lemma unpack_zero {n : ℕ} (j : Fin n) : unpack (0 : BitVec n) j = 0 := by
  simp [unpack]

/-- A packed binary linear combination; its interpretation is proved below. -/
def combine {n : ℕ} : List (F × BitVec n) → BitVec n
  | [] => 0
  | (a,v) :: xs => (if a = 0 then 0 else v) ^^^ combine xs

lemma unpack_combine {n : ℕ} (xs : List (F × BitVec n)) (j : Fin n) :
    unpack (combine xs) j = (xs.map (fun av => av.1 * unpack av.2 j)).sum := by
  induction xs with
  | nil => simp [combine, unpack]
  | cons av xs ih =>
    rcases av with ⟨a,v⟩
    simp only [combine, unpack_xor, ih, List.map_cons, List.sum_cons]
    congr 1
    have ha : a = 0 ∨ a = 1 := by revert a; decide
    rcases ha with rfl | rfl <;> simp [unpack]

def unpackRows {r n : ℕ} (rows : Fin r → BitVec n) : Matrix (Fin r) (Fin n) F :=
  fun i j => unpack (rows i) j

lemma matrix_certificate {m n r : ℕ} (M : Matrix (Fin m) (Fin n) F)
    (U : Matrix (Fin m) (Fin r) F) (rows : Fin r → BitVec n)
    (hc : ∀ i, combine (List.ofFn (fun k => (U i k, rows k))) = pack (M i)) :
    M = U * unpackRows rows := by
  ext i j
  have hh := congrArg (fun v => unpack v j) (hc i)
  simpa [unpack_combine, unpack_pack, List.map_ofFn, List.sum_ofFn, Matrix.mul_apply, unpackRows] using hh.symm

lemma rank_certificate {m n r : ℕ} (M : Matrix (Fin m) (Fin n) F)
    (is : Fin r → Fin m) (js : Fin r → Fin n)
    (R : Matrix (Fin r) (Fin n) F) (T : Matrix (Fin r) (Fin r) F)
    (hU : M = M.submatrix id js * R) (hL : M.submatrix is js * T = 1) :
    M.rank = r := by
  apply Nat.le_antisymm
  · rw [hU]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  · have hh := Matrix.rank_mul_le_left (M.submatrix is js) T
    rw [hL, Matrix.rank_one, Fintype.card_fin] at hh
    exact hh.trans (Matrix.rank_submatrix_le M is js)


lemma sum_mm : g + h = mm piEquiv.symm := by
  funext z
  change dot z.1 z.2 + dot z.1 (pi z.2) = dot z.1 (pi (pi z.2))
  rw [pi_cycle, dot_add, add_comm]

lemma bent_of_hasDual {f d : V → F} (hd : HasDual f d) : Bent f := by
  intro a
  rw [hd a]
  by_cases hz : d a = 0 <;> simp [sign, hz]

/-- The canonical bent dual, read from the sign of the Walsh transform. -/
def dual (f : V → F) (a : V) : F := if walsh f a = 16 then 0 else 1

lemma dual_eq {f d : V → F} (hd : HasDual f d) : dual f = d := by
  funext a
  have hv : d a = 0 ∨ d a = 1 := by generalize d a = v; revert v; decide
  rcases hv with hv | hv <;> simp [dual, hd a, sign, hv]

theorem bent_hypotheses : Bent g ∧ Bent h ∧ Bent (g + h) ∧
    dual (g + h) = dual g + dual h := by
  have hg : HasDual g (fun a => dot a.2 a.1) := walsh_mm (Equiv.refl W)
  have hh : HasDual h (fun a => dot a.2 (pi (pi a.1))) := walsh_mm piEquiv
  have hgh : HasDual (g + h) (fun a => dot a.2 (pi a.1)) := by
    rw [sum_mm]
    exact walsh_mm piEquiv.symm
  refine ⟨bent_of_hasDual hg, bent_of_hasDual hh, bent_of_hasDual hgh, ?_⟩
  rw [dual_eq hg, dual_eq hh, dual_eq hgh]
  funext a
  simp only [Pi.add_apply, pi_cycle, dot_add]
  have hx : ∀ x y : F, y = x + (y + x) := by decide
  exact hx _ _

/-- Incidence matrices of the two designs in the question. -/
def translation (f : V → F) : Matrix V V F := fun b z => f (b + z)
def construction (f q : V → F) : Matrix V V F :=
  fun b z => f b + q (b + z) + f z + q z


private def truthG : BitVec 256 := 0x6996c33ca55a0ff0996633cc55aaff0096963c3c5a5af0f06666ccccaaaa0000
private def truthH : BitVec 256 := 0xb076bf04aae8a59a79d076a2634e6c3cdc4ad338c6d4c9a615ec1a9e0f720000

private def xorWord (a b : Fin 16) : Fin 16 :=
  (BitVec.ofFin (w := 4) a ^^^ BitVec.ofFin (w := 4) b).toFin
private def xorPoint (a b : Fin 256) : Fin 256 :=
  (BitVec.ofFin (w := 8) a ^^^ BitVec.ofFin (w := 8) b).toFin

private lemma word_add (a b : Fin 16) :
    wordEquiv.symm a + wordEquiv.symm b = wordEquiv.symm (xorWord a b) := by
  revert a b
  decide +kernel

private def highCode (a : Fin 256) : Fin 16 := a.divNat (m := 16) (n := 16)
private def lowCode (a : Fin 256) : Fin 16 := a.modNat (m := 16) (n := 16)

private lemma point_add (a b : Fin 256) :
    pointEquiv.symm a + pointEquiv.symm b = pointEquiv.symm (xorPoint a b) := by
  have hc : ∀ a b : Fin 256,
      highCode (xorPoint a b) = xorWord (highCode a) (highCode b) ∧
      lowCode (xorPoint a b) = xorWord (lowCode a) (lowCode b) := by
    decide +kernel
  apply Prod.ext
  · change wordEquiv.symm (highCode a) + wordEquiv.symm (highCode b) =
      wordEquiv.symm (highCode (xorPoint a b))
    rw [word_add, (hc a b).1]
  · change wordEquiv.symm (lowCode a) + wordEquiv.symm (lowCode b) =
      wordEquiv.symm (lowCode (xorPoint a b))
    rw [word_add, (hc a b).2]

private lemma g_table (i : Fin 256) : g (pointEquiv.symm i) = unpack truthG i := by
  fin_cases i <;> decide +kernel
private lemma h_table (i : Fin 256) : h (pointEquiv.symm i) = unpack truthH i := by
  fin_cases i <;> decide +kernel

private def H : Matrix (Fin 256) (Fin 256) F := fun i j => unpack truthH (xorPoint i j)
private def A : Matrix (Fin 256) (Fin 256) F :=
  fun i j => unpack truthG i + H i j + unpack truthG j + unpack truthH j

private lemma H_eq : H = (translation h).submatrix pointEquiv.symm pointEquiv.symm := by
  ext i j
  change unpack truthH (xorPoint i j) = h (pointEquiv.symm i + pointEquiv.symm j)
  rw [point_add, h_table]

private lemma A_eq : A = (construction g h).submatrix pointEquiv.symm pointEquiv.symm := by
  ext i j
  change unpack truthG i + H i j + unpack truthG j + unpack truthH j =
    g (pointEquiv.symm i) + h (pointEquiv.symm i + pointEquiv.symm j) +
      g (pointEquiv.symm j) + h (pointEquiv.symm j)
  rw [point_add, g_table, g_table, h_table, h_table]
  rfl

private def rowsH : Fin 30 → Fin 256 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 25, 26, 32, 33, 34, 35, 64, 65, 128]
private def colsH : Fin 30 → Fin 256 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 25, 26, 32, 33, 34, 35, 64, 65, 128]
private def basisH : Fin 30 → BitVec 256 :=
  ![0x7c0d544ca4bc8cfd85f4adb55d4575048908a14951b979f870f158b0a8408001,
    0x433e6bbca47c8cfeb5389dba527a7af8b9c491465e8676044fc26740a8808002,
    0xa01250f616b6e652f0d200364676b692968466602020d0c4c64436a070e08004,
    0x2f58077067104f384f38671007702f588008a820c840e068e068c840a8208008,
    0xc0961866f18629760036d8c63126e9d6a95071a0984040b069f0b10058e08010,
    0x8020802080208020802080208020802080208020802080208020802080208020,
    0x8040804080408040804080408040804080408040804080408040804080408040,
    0x8080808080808080808080808080808080808080808080808080808080808080,
    0xe19088901800710011607860e8f081f0e160886018f071f011907890e8008100,
    0x2d508750d8007200dd507750280082002d508750d8007200dd50775028008200,
    0xbb308730b8008400bbc087c0b8f084f0bbc087c0b8f084f0bb308730b8008400,
    0x8800880088008800880088008800880088008800880088008800880088008800,
    0x9000900090009000900090009000900090009000900090009000900090009000,
    0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000,
    0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000,
    0xe84dc00ce7bdcffcd2e1faa0dd11f5501d1d355c12ed3aac27b10ff028410000,
    0xebbec33ce77ecffcde12f690d2d2fa5011ee396c1d2e35ac24420cc028820000,
    0xa23e52da698e996aa7c257266c729c963ea8ce4cf51805fc3b54cbb0f0e40000,
    0xee44c66c1824300c24180c30d278fa5014143c3ce274ca5cde48f66028280000,
    0x408698767196a966802658d6b13669c62940f1b01850c0a0e9e03110d8f00000,
    0x609009909900f0009060f96069f000f06060096099f0f0f09090f99069000000,
    0xaf5005505a00f0005f50f550aa000000af5005505a00f0005f50f550aa000000,
    0x3f3003303c0000003fc003c03cf000f03fc003c03cf000f03f3003303c000000,
    0xd77dd77d003c003c7d417d41aa00aa007d7d7d7daa3caa3cd741d74100000000,
    0xebbeebbe003c003cbe82be8255005500bebebebe553c553ceb82eb8200000000,
    0x82288228ff3cff3cd714d714aa00aa0028282828553c553c7d147d1400000000,
    0x41144114ff3cff3ceb28eb285500550014141414aa3caa3cbe28be2800000000,
    0x3cc33cc33cc33cc355aa55aa55aa55aa69696969696969690000000000000000,
    0xc33cc33cc33cc33c55aa55aa55aa55aa96969696969696960000000000000000,
    0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
private def inverseH : Fin 30 → BitVec 30 :=
  ![0x2462a5d6, 0xbbbc9a1, 0x19549e41, 0x29078b90, 0x1edac069, 0x2e8f8012, 0x23e98615, 0xc31030b, 0x3679688b, 0x79038cc, 0x161f5845, 0x3ff1870e, 0x11e28604, 0x38318301, 0x31d90512, 0x387f, 0x6dea, 0x143b, 0x42c, 0x4572, 0x6f96, 0x39c3, 0x5955, 0x5a72, 0x5a4e, 0xf72, 0xfb1, 0x28be, 0x7d14, 0x6969]

private theorem upperH (i : Fin 256) :
    combine (List.ofFn (fun k => (H i (colsH k), basisH k))) = pack (H i) := by
  fin_cases i <;> decide +kernel

private theorem lowerH (i : Fin 30) :
    combine (List.ofFn (fun k => (H (rowsH i) (colsH k), inverseH k))) =
      pack ((1 : Matrix (Fin 30) (Fin 30) F) i) := by
  fin_cases i <;> decide +kernel

private theorem rankH : H.rank = 30 := by
  apply rank_certificate H (rowsH) (colsH) (fun k j => unpack (basisH k) j)
    (fun k j => unpack (inverseH k) j)
  · exact matrix_certificate H (H.submatrix id colsH) basisH upperH
  · exact (matrix_certificate 1 (H.submatrix rowsH colsH) inverseH lowerH).symm

private def rowsA : Fin 29 → Fin 256 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20, 24, 25, 26, 32, 33, 34, 35, 64, 65, 128]
private def colsA : Fin 29 → Fin 256 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 24, 25, 26, 32, 33, 34, 35, 64, 65, 128]
private def basisA : Fin 29 → BitVec 256 :=
  ![0x7c0d544ca4bc8cfd85f4adb55d4575048908a14951b979f870f158b0a8408001,
    0x433e6bbca47c8cfeb5389dba527a7af8b9c491465e8676044fc26740a8808002,
    0xe094c88067204f3470f458e0f740df54bfc497d0387010642fa407b0a8108004,
    0x2f58077067104f384f38671007702f588008a820c840e068e068c840a8208008,
    0x8010801080108010801080108010801080108010801080108010801080108010,
    0x8020802080208020802080208020802080208020802080208020802080208020,
    0x8040804080408040804080408040804080408040804080408040804080408040,
    0x8080808080808080808080808080808080808080808080808080808080808080,
    0xe19088901800710011607860e8f081f0e160886018f071f011907890e8008100,
    0x2d508750d8007200dd507750280082002d508750d8007200dd50775028008200,
    0xbb308730b8008400bbc087c0b8f084f0bbc087c0b8f084f0bb308730b8008400,
    0x8800880088008800880088008800880088008800880088008800880088008800,
    0x9000900090009000900090009000900090009000900090009000900090009000,
    0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000,
    0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000,
    0xe84dc00ce7bdcffcd2e1faa0dd11f5501d1d355c12ed3aac27b10ff028410000,
    0xebbec33ce77ecffcde12f690d2d2fa5011ee396c1d2e35ac24420cc028820000,
    0xe2b8caac1818300c27e40ff0dd44f55017e83ffced48c55cd2b4faa028140000,
    0xee44c66c1824300c24180c30d278fa5014143c3ce274ca5cde48f66028280000,
    0x609009909900f0009060f96069f000f06060096099f0f0f09090f99069000000,
    0xaf5005505a00f0005f50f550aa000000af5005505a00f0005f50f550aa000000,
    0x3f3003303c0000003fc003c03cf000f03fc003c03cf000f03f3003303c000000,
    0xd77dd77d003c003c7d417d41aa00aa007d7d7d7daa3caa3cd741d74100000000,
    0xebbeebbe003c003cbe82be8255005500bebebebe553c553ceb82eb8200000000,
    0x82288228ff3cff3cd714d714aa00aa0028282828553c553c7d147d1400000000,
    0x41144114ff3cff3ceb28eb285500550014141414aa3caa3cbe28be2800000000,
    0x3cc33cc33cc33cc355aa55aa55aa55aa69696969696969690000000000000000,
    0xc33cc33cc33cc33c55aa55aa55aa55aa96969696969696960000000000000000,
    0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
private def inverseA : Fin 29 → BitVec 29 :=
  ![0x123165d6, 0x5d8d972, 0xcaf4be0, 0x1483cb90, 0xf6d451b, 0x1747c012, 0x11f1c601, 0x61d831f, 0x1b3cb84c, 0x3c838cc, 0xb0f8882, 0x1ff8c70e, 0x8f44610, 0x1c18c301, 0x18e98506, 0x387f, 0x3d2d, 0x18e, 0x42c, 0x3f51, 0x39c3, 0x992, 0xab5, 0xa89, 0xf72, 0xfb1, 0x28be, 0x2dd3, 0x39ae]

private theorem upperA (i : Fin 256) :
    combine (List.ofFn (fun k => (A i (colsA k), basisA k))) = pack (A i) := by
  fin_cases i <;> decide +kernel

private theorem lowerA (i : Fin 29) :
    combine (List.ofFn (fun k => (A (rowsA i) (colsA k), inverseA k))) =
      pack ((1 : Matrix (Fin 29) (Fin 29) F) i) := by
  fin_cases i <;> decide +kernel

private theorem rankA : A.rank = 29 := by
  apply rank_certificate A (rowsA) (colsA) (fun k j => unpack (basisA k) j)
    (fun k j => unpack (inverseA k) j)
  · exact matrix_certificate A (A.submatrix id colsA) basisA upperA
  · exact (matrix_certificate 1 (A.submatrix rowsA colsA) inverseA lowerA).symm

theorem translation_rank : (translation h).rank = 30 := by
  have hh := rankH
  rw [H_eq, Matrix.rank_submatrix] at hh
  exact hh

theorem construction_rank : (construction g h).rank = 29 := by
  have hh := rankA
  rw [A_eq, Matrix.rank_submatrix] at hh
  exact hh

/-- Open Problem 7's proposed equality is false, with every bent hypothesis included. -/
theorem counterexample : ∃ f q : V → F,
    Bent f ∧ Bent q ∧ Bent (f + q) ∧ dual (f + q) = dual f + dual q ∧
    (translation q).rank = 30 ∧ (construction f q).rank = 29 := by
  exact ⟨g, h, bent_hypotheses.1, bent_hypotheses.2.1,
    bent_hypotheses.2.2.1, bent_hypotheses.2.2.2, translation_rank, construction_rank⟩

/-- The source's universal rank-equality assertion, specialized to eight variables, is false. -/
theorem rank_equality_false : ¬ (∀ f q : V → F,
    Bent f → Bent q → Bent (f + q) → dual (f + q) = dual f + dual q →
    (construction f q).rank = (translation q).rank) := by
  intro claimed
  have bad := claimed g h bent_hypotheses.1 bent_hypotheses.2.1
    bent_hypotheses.2.2.1 bent_hypotheses.2.2.2
  rw [construction_rank, translation_rank] at bad
  omega

#print axioms counterexample
#print axioms rank_equality_false

end BentDesign
