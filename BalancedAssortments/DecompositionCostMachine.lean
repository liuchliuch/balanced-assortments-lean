import BalancedAssortments.DecompositionCostBinary
import BalancedAssortments.DecompositionCostGrid

namespace BalancedAssortments.Decomposition.CostMachine
open ComplexityTimeBinary CostBinary

abbrev Bits := List Bool
abbrev Flags := List (Bool × Bool)
abbrev BitAtom := Bits × List Bool

def eqBits (xs ys : Bits) : Bool × ℕ :=
  let r := compareBits xs ys
  (r.1 == Ordering.eq, r.2 + 1)

theorem eqBits_correct (xs ys : Bits) : (eqBits xs ys).1 = true ↔ value xs = value ys := by
  have h := compareBits_correct xs ys
  unfold eqBits
  generalize he : (compareBits xs ys).1 = o at *
  cases o <;> simp_all [comparisonMeaning] <;> omega

theorem eqBits_cost (xs ys : Bits) : (eqBits xs ys).2 = 16 * max xs.length ys.length + 2 := by
  simp [eqBits, compareBits_cost, Nat.add_assoc]

/-- Each coordinate is classified as `(isOne, isPositive)` using only binary
comparators. The first field concerns the current remaining mass `R`. -/
def classify (R : Bits) : List Bits → Flags × ℕ
  | [] => ([], 1)
  | x :: xs =>
      let a := eqBits x R
      let b := eqBits x []
      let r := classify R xs
      ((a.1, !b.1) :: r.1, a.2 + b.2 + r.2 + 8)

@[simp] theorem classify_length (R : Bits) (xs : List Bits) :
    (classify R xs).1.length = xs.length := by
  induction xs <;> simp [classify, *]

theorem classify_value (R : Bits) (xs : List Bits) :
    (classify R xs).1 = xs.map (fun x => (decide (value x = value R), decide (0 < value x))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [classify, List.map_cons, ih]
    congr 2
    · apply Bool.eq_iff_iff.mpr
      simp [eqBits_correct]
    · apply Bool.eq_iff_iff.mpr
      have hh := eqBits_correct x []
      cases he : (eqBits x []).1 <;> simp_all [value] <;> omega

theorem classify_cost {W : ℕ} {R : Bits} (hR : R.length ≤ W) (xs : List Bits)
    (hx : ∀ x ∈ xs, x.length ≤ W) :
    (classify R xs).2 ≤ xs.length * (32 * W + 12) + 1 := by
  induction xs with
  | nil => simp [classify]
  | cons x xs ih =>
    have hi := ih (fun y hy => hx y (List.mem_cons_of_mem x hy))
    have hh := hx x (by simp)
    simp only [classify, eqBits_cost, List.length_nil, Nat.max_zero, List.length_cons]
    have hm : max x.length R.length ≤ W := max_le hh hR
    nlinarith

/-- Unary quota tokens are intentional: rank is bounded by the coordinate count.
Every token deletion is one explicit constant-size list operation. -/
def removeOnes : List Unit → Flags → List Unit × ℕ
  | q, [] => (q, 1)
  | q, f :: fs =>
      let r := removeOnes (if f.1 then q.tail else q) fs
      (r.1, r.2 + 8)

@[simp] theorem removeOnes_cost (q : List Unit) (fs : Flags) :
    (removeOnes q fs).2 = fs.length * 8 + 1 := by
  induction fs generalizing q <;> simp [removeOnes, *, Nat.add_mul]

def buildMask : List Unit → Flags → List Bool × ℕ
  | _, [] => ([], 1)
  | q, f :: fs =>
      if f.1 then
        let r := buildMask q fs
        (true :: r.1, r.2 + 8)
      else if f.2 && !q.isEmpty then
        let r := buildMask q.tail fs
        (true :: r.1, r.2 + 8)
      else
        let r := buildMask q fs
        (false :: r.1, r.2 + 8)

@[simp] theorem buildMask_length (q : List Unit) (fs : Flags) :
    (buildMask q fs).1.length = fs.length := by
  induction fs generalizing q with
  | nil => rfl
  | cons f fs ih => simp only [buildMask]; split_ifs <;> simp [ih]

@[simp] theorem buildMask_cost (q : List Unit) (fs : Flags) :
    (buildMask q fs).2 = fs.length * 8 + 1 := by
  induction fs generalizing q with
  | nil => rfl
  | cons f fs ih => simp only [buildMask]; split_ifs <;> simp [ih, Nat.add_mul] <;> omega

/-- The actual two-pass binary selector. Its quota is represented by unary list
cells, so no unit-cost arithmetic on an unbounded rank is used here. -/
def selectMask (K : ℕ) (R : Bits) (xs : List Bits) : List Bool × ℕ :=
  let f := classify R xs
  let q := removeOnes (List.replicate K ()) f.1
  let m := buildMask q.1 f.1
  (m.1, f.2 + q.2 + m.2 + K + 1)

@[simp] theorem selectMask_length (K : ℕ) (R : Bits) (xs : List Bits) :
    (selectMask K R xs).1.length = xs.length := by simp [selectMask]

theorem selectMask_cost {W : ℕ} {R : Bits} (hR : R.length ≤ W) (K : ℕ) (xs : List Bits)
    (hx : ∀ x ∈ xs, x.length ≤ W) :
    (selectMask K R xs).2 ≤ xs.length * (32 * W + 28) + K + 4 := by
  have hh := classify_cost hR xs hx
  simp only [selectMask, removeOnes_cost, buildMask_cost, classify_length]
  nlinarith

/-- A fully integral flag sequence has no positive non-one coordinate. -/
def allIntegral : Flags → Bool × ℕ
  | [] => (true, 1)
  | f :: fs =>
      let r := allIntegral fs
      ((f.1 || !f.2) && r.1, r.2 + 8)

/-- Minimum boundary distance over all coordinates, seeded with `R`.
Integral coordinates contribute distance `R`, so including them is harmless. -/
def minimumMasked (R : Bits) : List Bits → List Bool → Bits × ℕ
  | [], _ => (R, 1)
  | x :: xs, ms =>
      let d := if ms.headD false then (x, 0) else subBits R x
      let r := minimumMasked R xs ms.tail
      let c := compareBits d.1 r.1
      (if c.1 == Ordering.gt then r.1 else d.1, d.2 + r.2 + c.2 + 8)

theorem minimumMasked_bounds {W : ℕ} {R : Bits} (hR : R.length ≤ W)
    (xs : List Bits) (ms : List Bool) (hx : ∀ x ∈ xs, x.length ≤ W) :
    (minimumMasked R xs ms).1.length ≤ W ∧
    (minimumMasked R xs ms).2 ≤ xs.length * (32 * W + 11) + 1 := by
  induction xs generalizing ms with
  | nil => simpa [minimumMasked] using hR
  | cons x xs ih =>
    have hx0 := hx x (by simp)
    have ht := ih ms.tail (fun y hy => hx y (List.mem_cons_of_mem x hy))
    have hd : (if ms.headD false then (x, 0) else subBits R x).1.length ≤ W ∧
        (if ms.headD false then (x, 0) else subBits R x).2 ≤ 16 * W + 2 := by
      split_ifs
      · exact ⟨hx0, by omega⟩
      · exact ⟨(subBits_length R x).trans (max_le hR hx0), by rw [subBits_cost]; omega⟩
    constructor
    · dsimp only [minimumMasked]
      split_ifs <;> first | exact ht.1 | exact hx0 | exact (subBits_length R x).trans (max_le hR hx0)
    · dsimp only [minimumMasked]
      rw [compareBits_cost]
      simp only [List.length_cons]
      have hm := max_le hd.1 ht.1
      nlinarith [hd.2, ht.2]

/-- Update all integer counts using gate-level subtraction only on selected
coordinates. The incidence mask is reused as a Boolean list. -/
def subtractMasked (m : Bits) : List Bits → List Bool → List Bits × ℕ
  | [], _ => ([], 1)
  | x :: xs, ms =>
      let d := if ms.headD false then subBits x m else (x, 0)
      let r := subtractMasked m xs ms.tail
      (d.1 :: r.1, d.2 + r.2 + 4)

@[simp] theorem subtractMasked_length (m : Bits) (xs : List Bits) (ms : List Bool) :
    (subtractMasked m xs ms).1.length = xs.length := by
  induction xs generalizing ms <;> simp [subtractMasked, *]

theorem subtractMasked_bounds {W : ℕ} {m : Bits} (hm : m.length ≤ W)
    (xs : List Bits) (ms : List Bool) (hx : ∀ x ∈ xs, x.length ≤ W) :
    (∀ x ∈ (subtractMasked m xs ms).1, x.length ≤ W) ∧
    (subtractMasked m xs ms).2 ≤ xs.length * (16 * W + 6) + 1 := by
  induction xs generalizing ms with
  | nil => simp [subtractMasked]
  | cons x xs ih =>
    have hx0 := hx x (by simp)
    have ht := ih ms.tail (fun y hy => hx y (List.mem_cons_of_mem x hy))
    have hd : (if ms.headD false then subBits x m else (x, 0)).1.length ≤ W ∧
        (if ms.headD false then subBits x m else (x, 0)).2 ≤ 16 * W + 2 := by
      split_ifs
      · exact ⟨(subBits_length x m).trans (max_le hx0 hm), by rw [subBits_cost]; omega⟩
      · exact ⟨hx0, by omega⟩
    constructor
    · intro y hy
      simp only [subtractMasked, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hd.1
      · exact ht.1 y hy
    · dsimp only [subtractMasked]
      simp only [List.length_cons]
      nlinarith [hd.2, ht.2]

end BalancedAssortments.Decomposition.CostMachine
