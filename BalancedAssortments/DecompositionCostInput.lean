import BalancedAssortments.DecompositionCostExecution

namespace BalancedAssortments.Decomposition.CostMachine
open ComplexityTimeBinary CostBinary

/-- Total number of stored input bits, including possible leading zeroes. -/
def bitVolume (xs : List Bits) : ℕ := (xs.map List.length).sum

@[simp] theorem bitVolume_nil : bitVolume [] = 0 := rfl
@[simp] theorem bitVolume_cons (x : Bits) (xs : List Bits) :
    bitVolume (x :: xs) = x.length + bitVolume xs := rfl

/-- Binary product. Each small input operand is the *left* multiplication
argument, preventing padding from growing exponentially across the fold. -/
def productBits : List Bits → Bits × ℕ
  | [] => ([true], 1)
  | x :: xs =>
      let p := productBits xs
      let q := mulBits x p.1
      (q.1, p.2 + q.2 + 4)

theorem productBits_value (xs : List Bits) :
    value (productBits xs).1 = (xs.map value).prod := by
  induction xs <;> simp [productBits, mulBits_value, value, *]

theorem productBits_length (xs : List Bits) :
    (productBits xs).1.length ≤ 2 * bitVolume xs + 1 := by
  induction xs with
  | nil => simp [productBits]
  | cons x xs ih =>
    have hh := mulBits_length x (productBits xs).1
    simp only [productBits, bitVolume_cons]
    omega

/-- Quadratic bit budget for one binary multiplication inside initialization. -/
def inputProductBudget (L : ℕ) : ℕ := 256 * (L + 1) ^ 2

theorem productBits_cost {L : ℕ} (xs : List Bits) (hL : bitVolume xs ≤ L) :
    (productBits xs).2 ≤ xs.length * inputProductBudget L + 1 := by
  induction xs with
  | nil => simp [productBits]
  | cons x xs ih =>
    have hl : bitVolume xs ≤ L := by simp only [bitVolume_cons] at hL; omega
    have hx : x.length ≤ L := by simp only [bitVolume_cons] at hL; omega
    have hi := ih hl
    have hw := productBits_length xs
    have hm := mulBits_cost x (productBits xs).1
    have hp : (productBits xs).1.length ≤ 2 * L + 1 := by omega
    simp only [productBits, List.length_cons]
    dsimp [inputProductBudget] at *
    nlinarith [Nat.mul_self_le_mul_self hx]

/-- Explicit list deletion with a bounded unary index. Its cost charges list
inspection/copying; it never compares binary scalar magnitudes. -/
def eraseAt {α : Type} : ℕ → List α → List α × ℕ
  | _, [] => ([], 1)
  | 0, _ :: xs => (xs, 1)
  | i + 1, x :: xs =>
      let r := eraseAt i xs
      (x :: r.1, r.2 + 4)

@[simp] theorem eraseAt_value {α : Type} (i : ℕ) (xs : List α) :
    (eraseAt i xs).1 = xs.eraseIdx i := by
  induction xs generalizing i with
  | nil => simp [eraseAt]
  | cons x xs ih => cases i <;> simp [eraseAt, ih]

theorem eraseAt_cost {α : Type} (i : ℕ) (xs : List α) :
    (eraseAt i xs).2 ≤ xs.length * 4 + 1 := by
  induction xs generalizing i with
  | nil => simp [eraseAt]
  | cons x xs ih =>
    cases i with
    | zero => simp [eraseAt]
    | succ i => have hh := ih i; simp only [eraseAt, List.length_cons]; omega

theorem eraseAt_length {α : Type} (i : ℕ) (xs : List α) :
    (eraseAt i xs).1.length ≤ xs.length := by
  induction xs generalizing i with
  | nil => simp [eraseAt]
  | cons x xs ih =>
    cases i with
    | zero => simp [eraseAt]
    | succ i => have hh := ih i; simp only [eraseAt, List.length_cons]; omega

theorem eraseAt_volume (i : ℕ) (xs : List Bits) :
    bitVolume (eraseAt i xs).1 ≤ bitVolume xs := by
  induction xs generalizing i with
  | nil => simp [eraseAt]
  | cons x xs ih =>
    cases i with
    | zero => simp only [eraseAt, bitVolume_cons]; omega
    | succ i => have hh := ih i; simp only [eraseAt, bitVolume_cons]; omega

/-- Natural numerators are multiplied by all other denominators. The index
counter is bounded by the input coordinate count and used only for list deletion. -/
def initialBitsCounts (dens : List Bits) : ℕ → List Bits → List Bits × ℕ
  | _, [] => ([], 1)
  | i, x :: xs =>
      let e := eraseAt i dens
      let p := productBits e.1
      let a := mulBits x p.1
      let r := initialBitsCounts dens (i + 1) xs
      (a.1 :: r.1, e.2 + p.2 + a.2 + r.2 + 4)

@[simp] theorem initialBitsCounts_length (dens : List Bits) (i : ℕ) (nums : List Bits) :
    (initialBitsCounts dens i nums).1.length = nums.length := by
  induction nums generalizing i <;> simp [initialBitsCounts, *]

theorem initialBitsCounts_width {L : ℕ} (dens : List Bits) (hd : bitVolume dens ≤ L)
    (i : ℕ) (nums : List Bits) (hn : ∀ x ∈ nums, x.length ≤ L) :
    ∀ x ∈ (initialBitsCounts dens i nums).1, x.length ≤ 4 * L + 1 := by
  induction nums generalizing i with
  | nil => simp [initialBitsCounts]
  | cons x xs ih =>
    have hx := hn x (by simp)
    have hp := productBits_length (eraseAt i dens).1
    have he := (eraseAt_volume i dens).trans hd
    have hm := mulBits_length x (productBits (eraseAt i dens).1).1
    intro y hy
    simp only [initialBitsCounts, List.mem_cons] at hy
    rcases hy with rfl | hy
    · omega
    · exact ih _ (fun x hx => hn x (List.mem_cons_of_mem _ hx)) y hy

theorem initialBitsCounts_cost {L : ℕ} (dens : List Bits) (hd : bitVolume dens ≤ L)
    (i : ℕ) (nums : List Bits) (hn : ∀ x ∈ nums, x.length ≤ L) :
    (initialBitsCounts dens i nums).2 ≤
      nums.length * ((dens.length + 1) * (2 * inputProductBudget L)) + 1 := by
  induction nums generalizing i with
  | nil => simp [initialBitsCounts]
  | cons x xs ih =>
    have hx := hn x (by simp)
    have ht := ih (i + 1) (fun y hy => hn y (List.mem_cons_of_mem _ hy))
    have he := eraseAt_cost i dens
    have hev := (eraseAt_volume i dens).trans hd
    have hel := eraseAt_length i dens
    have hp := productBits_cost (eraseAt i dens).1 hev
    have hpw := productBits_length (eraseAt i dens).1
    have hm := mulBits_cost x (productBits (eraseAt i dens).1).1
    have hprod : (productBits (eraseAt i dens).1).1.length ≤ 2 * L + 1 := by omega
    have hpc : (productBits (eraseAt i dens).1).2 ≤ dens.length * inputProductBudget L + 1 :=
      hp.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hel) 1)
    simp only [initialBitsCounts, List.length_cons]
    dsimp [inputProductBudget] at *
    nlinarith [Nat.mul_self_le_mul_self hx]

/-- Complete binary input initialization and greedy execution. Fractions remain
unreduced, and masks are the binary incidence vectors of output assortments. -/
def binaryGreedy (K : ℕ) (nums dens : List Bits) : Bits × List BitAtom × ℕ :=
  let d := productBits dens
  let a := initialBitsCounts dens 0 nums
  let p := binaryGridAux nums.length K d.1 a.1
  (d.1, p.1, d.2 + a.2 + p.2 + nums.length + 8)

/-- End-to-end binary/list-machine cost of initialization plus the complete
loop. `L` counts actual stored bits and `n` counts coordinates; rank is at most
`n`, as in the paper's input model. This is a bit-operation bound, not a count
of unit-cost rational arithmetic calls. -/
theorem binaryGreedy_bit_cost {n L : ℕ} (K : ℕ) (nums dens : List Bits)
    (hn : nums.length = n) (hd : dens.length = n) (hK : K ≤ n)
    (hL : bitVolume nums + bitVolume dens ≤ L) :
    (binaryGreedy K nums dens).2.2 ≤ 8192 * (n + 1) ^ 2 * (L + 1) ^ 2 := by
  have hvd : bitVolume dens ≤ L := by omega
  have hvn : bitVolume nums ≤ L := by omega
  have hnums : ∀ x ∈ nums, x.length ≤ L := by
    intro x hx
    have hh : x.length ≤ bitVolume nums := List.le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)
    exact hh.trans hvn
  have hdw : (productBits dens).1.length ≤ 4 * L + 1 := by
    have hh := productBits_length dens
    omega
  have haw := initialBitsCounts_width dens hvd 0 nums hnums
  have hp := productBits_cost dens hvd
  have ha := initialBitsCounts_cost dens hvd 0 nums hnums
  have ht := binaryGridAux_bit_cost nums.length K (productBits dens).1
    (initialBitsCounts dens 0 nums).1 hdw haw
  rw [initialBitsCounts_length, hn] at ht
  rw [hd] at hp
  rw [hn, hd] at ha
  have ht' : (binaryGridAux nums.length K (productBits dens).1 (initialBitsCounts dens 0 nums).1).2 ≤
      (n + 1) * (256 * (2 * n + 1) * (4 * L + 2)) := by
    rw [hn]
    apply ht.trans
    dsimp [roundBitBudget]
    gcongr
    omega
  dsimp only [binaryGreedy]
  dsimp [inputProductBudget] at hp ha
  have he : nums.length = n := hn
  rw [he]
  rw [hn] at ht'
  nlinarith

/-- The initializer's coordinate semantics, including its exact erased index. -/
theorem initialBitsCounts_value (dens : List Bits) (i : ℕ) (nums : List Bits) :
    ((initialBitsCounts dens i nums).1.map value) =
      nums.mapIdx (fun j x => value x * ((dens.eraseIdx (i + j)).map value).prod) := by
  induction nums generalizing i with
  | nil => rfl
  | cons x xs ih =>
    simp [initialBitsCounts, mulBits_value, productBits_value, eraseAt_value,
      List.mapIdx_cons, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem get_mul_prod_eraseIdx (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    xs[i] * (xs.eraseIdx i).prod = xs.prod := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      have hh := ih i hi'
      simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ, List.prod_cons]
      nlinarith [hh]

private theorem prod_eraseIdx_ofFn {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (i : Fin n) : ((List.ofFn d).eraseIdx i.val).prod = ∏ j ∈ Finset.univ.erase i, d j := by
  apply Nat.eq_of_mul_eq_mul_left (hd i)
  have hl := get_mul_prod_eraseIdx (List.ofFn d) i.val (by simpa using i.isLt)
  simpa [List.prod_ofFn, Finset.mul_prod_erase _ _ (Finset.mem_univ i)] using hl

def encodedNumerators {n : ℕ} (z : Fin n → ℚ) : List Bits :=
  List.ofFn fun i => (z i).num.natAbs.bits

def encodedDenominators {n : ℕ} (z : Fin n → ℚ) : List Bits :=
  List.ofFn fun i => (z i).den.bits

@[simp] theorem encodedNumerators_length {n : ℕ} (z : Fin n → ℚ) :
    (encodedNumerators z).length = n := by simp [encodedNumerators]
@[simp] theorem encodedDenominators_length {n : ℕ} (z : Fin n → ℚ) :
    (encodedDenominators z).length = n := by simp [encodedDenominators]

theorem encodedDenominators_value {n : ℕ} (z : Fin n → ℚ) :
    value (productBits (encodedDenominators z)).1 = commonDenominator z := by
  simp [productBits_value, encodedDenominators, List.map_ofFn, List.prod_ofFn, commonDenominator]

theorem encodedCounts_value {n : ℕ} (z : Fin n → ℚ) :
    ((initialBitsCounts (encodedDenominators z) 0 (encodedNumerators z)).1.map value) =
      List.ofFn (initialGridCounts z) := by
  rw [initialBitsCounts_value]
  apply List.ext_getElem
  · simp [encodedNumerators]
  · intro j hj hj'
    have hjn : j < n := by simpa using hj'
    simp only [List.getElem_mapIdx, encodedNumerators, List.getElem_ofFn,
      value_bits, zero_add, initialGridCounts]
    congr 1
    rw [← List.eraseIdx_map]
    have he : (encodedDenominators z).map value = List.ofFn (fun i => (z i).den) := by
      simp [encodedDenominators, List.map_ofFn, Function.comp_def]
    rw [he]
    exact prod_eraseIdx_ofFn (fun i => (z i).den) (fun i => Rat.den_pos _) ⟨j, hjn⟩

/-- Actual binary input length of all rational numerators and denominators. -/
def inputRationalBits {n : ℕ} (z : Fin n → ℚ) : ℕ :=
  bitVolume (encodedNumerators z) + bitVolume (encodedDenominators z)

theorem inputRationalBits_eq {n : ℕ} (z : Fin n → ℚ) :
    inputRationalBits z = ∑ i, ((z i).num.natAbs.size + (z i).den.size) := by
  simp [inputRationalBits, bitVolume, encodedNumerators, encodedDenominators,
    List.map_ofFn, List.sum_ofFn, ← Nat.size_eq_bits_len, Finset.sum_add_distrib]

/-- Polynomial running-time bound for the binary implementation on canonical
binary encodings of the actual rational input. -/
theorem encoded_binaryGreedy_bit_cost {n K : ℕ} (hK : K ≤ n) (z : Fin n → ℚ) :
    (binaryGreedy K (encodedNumerators z) (encodedDenominators z)).2.2 ≤
      8192 * (n + 1) ^ 2 * (inputRationalBits z + 1) ^ 2 :=
  binaryGreedy_bit_cost K _ _ (by simp) (by simp) hK (by rfl)

end BalancedAssortments.Decomposition.CostMachine
