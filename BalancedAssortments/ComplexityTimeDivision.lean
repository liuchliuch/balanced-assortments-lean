import BalancedAssortments.DecompositionCostBinary

/-! Binary long division by a positive bit-list divisor. All unbounded operand
arithmetic is implemented on Boolean lists. The cost is the same explicit
bit/list-gate model used by the imported add/compare/subtract routines. -/
namespace BalancedAssortments.ComplexityTimeDivision
open ComplexityTimeBinary Decomposition.CostBinary

structure Division where
  quotient : List Bool
  remainder : List Bool
  cost : ℕ
  deriving Repr

/-- Process the more significant suffix first, then append one quotient bit.
No decoded natural-number division, remainder, subtraction or comparison is
used by this executable routine. -/
def divBits : List Bool → List Bool → Division
  | [], _ => ⟨[], [], 1⟩
  | b :: bs, d =>
      let prev := divBits bs d
      let shifted := b :: prev.remainder
      let cmp := compareBits d shifted
      if cmp.1 != Ordering.gt then
        let sub := subBits shifted d
        ⟨true :: prev.quotient, sub.1, prev.cost + cmp.2 + sub.2 + 12⟩
      else
        ⟨false :: prev.quotient, shifted, prev.cost + cmp.2 + 12⟩

theorem divBits_spec (xs d : List Bool) (hd : 0 < value d) :
    value (divBits xs d).quotient * value d + value (divBits xs d).remainder = value xs ∧
    value (divBits xs d).remainder < value d := by
  induction xs with
  | nil => simp [divBits, value, hd]
  | cons b bs ih =>
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    simp only [divBits]
    split_ifs with hc
    · have hle : value d ≤ value (b :: (divBits bs d).remainder) :=
        (leBits_correct _ _).mp hc
      have hsub := Nat.sub_add_cancel hle
      simp only [subBits_value, value, Bool.toNat_true]
      simp only [value] at hle hsub
      constructor <;> nlinarith [ih.1, ih.2]
    · have hlt : value (b :: (divBits bs d).remainder) < value d := by
        apply Nat.lt_of_not_ge
        intro hh
        exact hc ((leBits_correct _ _).mpr hh)
      simp only [value, Bool.toNat_false, zero_add]
      simp only [value] at hlt
      constructor
      · nlinarith [ih.1]
      · exact hlt

theorem divBits_quotient (xs d : List Bool) (hd : 0 < value d) :
    value (divBits xs d).quotient = value xs / value d := by
  obtain ⟨he, hr⟩ := divBits_spec xs d hd
  exact ((Nat.div_mod_unique hd).mpr ⟨by nlinarith [he], hr⟩).1.symm

theorem divBits_remainder (xs d : List Bool) (hd : 0 < value d) :
    value (divBits xs d).remainder = value xs % value d := by
  obtain ⟨he, hr⟩ := divBits_spec xs d hd
  exact ((Nat.div_mod_unique hd).mpr ⟨by nlinarith [he], hr⟩).2.symm

theorem divBits_lengths (xs d : List Bool) :
    (divBits xs d).quotient.length = xs.length ∧
    (divBits xs d).remainder.length ≤ xs.length + d.length := by
  induction xs with
  | nil => simp [divBits]
  | cons b bs ih =>
    simp only [divBits]
    split_ifs
    · simp only [List.length_cons]
      refine ⟨by omega, ?_⟩
      have hs := subBits_length (b :: (divBits bs d).remainder) d
      simp only [List.length_cons] at hs
      omega
    · simp only [List.length_cons]
      exact ⟨by omega, by omega⟩

/-- Quadratic bit-operation cost for long division, including every comparator
and ripple-borrow subtraction and constant list overhead. -/
theorem divBits_cost (xs d : List Bool) :
    (divBits xs d).cost ≤ 64 * xs.length * (xs.length + d.length + 1) + 1 := by
  induction xs with
  | nil => simp [divBits]
  | cons b bs ih =>
    have hl := (divBits_lengths bs d).2
    have hmax : max d.length (b :: (divBits bs d).remainder).length ≤ bs.length + d.length + 1 := by
      simp only [List.length_cons]; omega
    have hmax' : max (b :: (divBits bs d).remainder).length d.length ≤ bs.length + d.length + 1 := by
      simpa [max_comm] using hmax
    simp only [divBits]
    split_ifs <;> simp only [compareBits_cost, subBits_cost, List.length_cons]
    · simp only [List.length_cons] at hmax hmax'
      nlinarith
    · simp only [List.length_cons] at hmax
      nlinarith

/-- Canonical binary encoding specialization, with an explicit polynomial in
input bit lengths rather than operand magnitudes. -/
theorem divide_standard (m d : ℕ) (hd : 0 < d) :
    value (divBits m.bits d.bits).quotient = m / d ∧
    value (divBits m.bits d.bits).remainder = m % d ∧
    (divBits m.bits d.bits).cost ≤ 64 * m.size * (m.size + d.size + 1) + 1 := by
  have hp : 0 < value d.bits := by simpa using hd
  exact ⟨by simpa using divBits_quotient m.bits d.bits hp,
    by simpa using divBits_remainder m.bits d.bits hp,
    by simpa [Nat.size_eq_bits_len] using divBits_cost m.bits d.bits⟩

example : value (divBits (37 : ℕ).bits (5 : ℕ).bits).quotient = 7 ∧
    value (divBits (37 : ℕ).bits (5 : ℕ).bits).remainder = 2 := by
  have h := divide_standard 37 5 (by decide)
  exact ⟨by simpa using h.1, by simpa using h.2.1⟩

example : value (divBits (0 : ℕ).bits (7 : ℕ).bits).quotient = 0 ∧
    value (divBits (3 : ℕ).bits (7 : ℕ).bits).remainder = 3 := by
  exact ⟨by simpa using (divide_standard 0 7 (by decide)).1,
    by simpa using (divide_standard 3 7 (by decide)).2.1⟩
end BalancedAssortments.ComplexityTimeDivision
