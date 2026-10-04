import BalancedAssortments.DecompositionCostMachine

namespace BalancedAssortments.Decomposition.CostMachine
open ComplexityTimeBinary CostBinary

@[simp] theorem allIntegral_cost (fs : Flags) : (allIntegral fs).2 = fs.length * 8 + 1 := by
  induction fs <;> simp [allIntegral, *, Nat.add_mul]

@[simp] theorem allIntegral_value (fs : Flags) :
    (allIntegral fs).1 = fs.all (fun f => f.1 || !f.2) := by
  induction fs <;> simp [allIntegral, *]

private theorem chosen_min_value (xs ys : Bits) :
    value (if (compareBits xs ys).1 == Ordering.gt then ys else xs) =
      min (value xs) (value ys) := by
  have hh := compareBits_correct xs ys
  cases he : (compareBits xs ys).1 <;> simp_all [comparisonMeaning, min_eq_left, min_eq_right] <;> omega

def minimumNatMasked (R : ℕ) : List ℕ → List Bool → ℕ
  | [], _ => R
  | x :: xs, ms => min (if ms.headD false then x else R - x) (minimumNatMasked R xs ms.tail)

theorem minimumMasked_value (R : Bits) (xs : List Bits) (ms : List Bool) :
    value (minimumMasked R xs ms).1 = minimumNatMasked (value R) (xs.map value) ms := by
  induction xs generalizing ms with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [minimumMasked]
    rw [chosen_min_value, ih]
    simp only [List.map_cons, minimumNatMasked]
    congr 1
    split_ifs <;> simp [subBits_value]

def subtractNatMasked (m : ℕ) : List ℕ → List Bool → List ℕ
  | [], _ => []
  | x :: xs, ms => (if ms.headD false then x - m else x) :: subtractNatMasked m xs ms.tail

theorem subtractMasked_value (m : Bits) (xs : List Bits) (ms : List Bool) :
    ((subtractMasked m xs ms).1.map value) = subtractNatMasked (value m) (xs.map value) ms := by
  induction xs generalizing ms with
  | nil => rfl
  | cons x xs ih =>
    simp only [subtractMasked, List.map_cons, ih, subtractNatMasked]
    congr 1
    split_ifs <;> simp [subBits_value]

/-- Complete integer-grid loop operating on actual bit lists. Selection uses
unary rank tokens, and arithmetic uses only the certified gate-level routines.
The final mathematical interpretation of output fractions is not executed here. -/
def binaryGridAux : ℕ → ℕ → Bits → List Bits → List BitAtom × ℕ
  | 0, _, R, xs =>
      let s := selectMask 0 R xs
      ([(R, s.1)], s.2 + 4)
  | fuel + 1, K, R, xs =>
      let s := selectMask K R xs
      let f := classify R xs
      let d := allIntegral f.1
      if d.1 then ([(R, s.1)], s.2 + f.2 + d.2 + 4) else
        let m := minimumMasked R xs s.1
        let r := subBits R m.1
        let a := subtractMasked m.1 xs s.1
        let p := binaryGridAux fuel K r.1 a.1
        ((m.1, s.1) :: p.1, s.2 + f.2 + d.2 + m.2 + r.2 + a.2 + p.2 + 8)

/-- A concrete conservative bound for one iteration, including binary gates,
list traversal/dispatch, and construction of the rank's unary quota tokens. -/
def roundBitBudget (n K W : ℕ) : ℕ := 256 * (n + K + 1) * (W + 1)

theorem binaryGridAux_bit_cost {W : ℕ} (fuel K : ℕ) (R : Bits) (xs : List Bits)
    (hR : R.length ≤ W) (hx : ∀ x ∈ xs, x.length ≤ W) :
    (binaryGridAux fuel K R xs).2 ≤ (fuel + 1) * roundBitBudget xs.length K W := by
  induction fuel generalizing R xs with
  | zero =>
    have hs := selectMask_cost hR 0 xs hx
    simp only [binaryGridAux, zero_add, one_mul]
    dsimp [roundBitBudget]
    nlinarith
  | succ fuel ih =>
    have hs := selectMask_cost hR K xs hx
    have hf := classify_cost hR xs hx
    have hd : (allIntegral (classify R xs).1).2 = xs.length * 8 + 1 := by simp
    dsimp only [binaryGridAux]
    split_ifs with he
    · dsimp [roundBitBudget]
      have hp : 0 ≤ fuel * (256 * (xs.length + K + 1) * (W + 1)) := Nat.zero_le _
      nlinarith
    · have hm := minimumMasked_bounds hR xs (selectMask K R xs).1 hx
      have hr : (subBits R (minimumMasked R xs (selectMask K R xs).1).1).1.length ≤ W :=
        (subBits_length _ _).trans (max_le hR hm.1)
      have hrc : (subBits R (minimumMasked R xs (selectMask K R xs).1).1).2 ≤ 16 * W + 2 := by
        rw [subBits_cost]
        have := max_le hR hm.1
        omega
      have ha := subtractMasked_bounds hm.1 xs (selectMask K R xs).1 hx
      have ht := ih _ _ hr ha.1
      rw [subtractMasked_length] at ht
      dsimp [roundBitBudget] at ht ⊢
      nlinarith [hm.2, ha.2]

theorem binaryGridAux_length (fuel K : ℕ) (R : Bits) (xs : List Bits) :
    (binaryGridAux fuel K R xs).1.length ≤ fuel + 1 := by
  induction fuel generalizing R xs with
  | zero => simp [binaryGridAux]
  | succ fuel ih =>
    dsimp only [binaryGridAux]
    split_ifs
    · simp
    · simp only [List.length_cons]
      have := ih (subBits R (minimumMasked R xs (selectMask K R xs).1).1).1
        (subtractMasked (minimumMasked R xs (selectMask K R xs).1).1 xs (selectMask K R xs).1).1
      omega

/-- Bit widths never increase in the inner loop, even for padded bit inputs. -/
theorem binaryGridAux_width {W : ℕ} (fuel K : ℕ) (R : Bits) (xs : List Bits)
    (hR : R.length ≤ W) (hx : ∀ x ∈ xs, x.length ≤ W) :
    ∀ a ∈ (binaryGridAux fuel K R xs).1, a.1.length ≤ W ∧ a.2.length = xs.length := by
  induction fuel generalizing R xs with
  | zero =>
    intro a ha
    have he : a = (R, (selectMask 0 R xs).1) := by simpa [binaryGridAux] using ha
    simp [he, hR]
  | succ fuel ih =>
    intro a ha
    dsimp only [binaryGridAux] at ha
    split_ifs at ha with he
    · have hae : a = (R, (selectMask K R xs).1) := by simpa using ha
      simp [hae, hR]
    · have hm := minimumMasked_bounds hR xs (selectMask K R xs).1 hx
      have hr : (subBits R (minimumMasked R xs (selectMask K R xs).1).1).1.length ≤ W :=
        (subBits_length _ _).trans (max_le hR hm.1)
      have hh := subtractMasked_bounds hm.1 xs (selectMask K R xs).1 hx
      rcases List.mem_cons.mp ha with hae | ha
      · simp [hae, hm.1]
      · have ht := ih _ _ hr hh.1 a ha
        simpa using ht

end BalancedAssortments.Decomposition.CostMachine
