import BalancedAssortments.ComplexityTimeBinary

namespace BalancedAssortments.Decomposition.CostBinary
open ComplexityTimeBinary

/-- Conventional ripple-borrow cell, made only of Boolean gates. -/
def fullSub (a b c : Bool) : Bool × Bool :=
  (xor (xor a b) c, ((!a) && (b || c)) || (b && c))

theorem fullSub_correct (a b c : Bool) :
    (fullSub a b c).1.toNat + b.toNat + c.toNat =
      a.toNat + 2 * (fullSub a b c).2.toNat := by
  cases a <;> cases b <;> cases c <;> decide

structure SubResult where
  bits : List Bool
  borrow : Bool
  cost : ℕ

/-- Subtraction processes one bit position at a time; 16 charges cover the
Boolean gates, list dispatch, reads, and writes for a position. -/
def subBorrow : List Bool → List Bool → Bool → SubResult
  | [], [], c => ⟨[], c, 1⟩
  | a :: as, [], c =>
      let f := fullSub a false c
      let r := subBorrow as [] f.2
      ⟨f.1 :: r.bits, r.borrow, r.cost + 16⟩
  | [], b :: bs, c =>
      let f := fullSub false b c
      let r := subBorrow [] bs f.2
      ⟨f.1 :: r.bits, r.borrow, r.cost + 16⟩
  | a :: as, b :: bs, c =>
      let f := fullSub a b c
      let r := subBorrow as bs f.2
      ⟨f.1 :: r.bits, r.borrow, r.cost + 16⟩

theorem subBorrow_value (xs ys : List Bool) (c : Bool) :
    value (subBorrow xs ys c).bits + value ys + c.toNat =
      value xs + 2 ^ (max xs.length ys.length) * (subBorrow xs ys c).borrow.toNat := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subBorrow, value]
    | cons b bs ih =>
      have hi := ih (fullSub false b c).2
      have hf := fullSub_correct false b c
      simp only [subBorrow, value, List.length_nil, List.length_cons, zero_add,
        Nat.zero_max, pow_succ, Bool.toNat_false] at hi hf ⊢
      nlinarith
  | cons a as ih =>
    cases ys with
    | nil =>
      have hi := ih [] (fullSub a false c).2
      have hf := fullSub_correct a false c
      simp only [subBorrow, value, List.length_nil, List.length_cons, add_zero,
        Nat.max_zero, pow_succ, Bool.toNat_false] at hi hf ⊢
      nlinarith
    | cons b bs =>
      have hi := ih bs (fullSub a b c).2
      have hf := fullSub_correct a b c
      simp only [subBorrow, value, List.length_cons, max_add_add_right, pow_succ] at hi hf ⊢
      nlinarith

theorem subBorrow_length (xs ys : List Bool) (c : Bool) :
    (subBorrow xs ys c).bits.length = max xs.length ys.length := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subBorrow]
    | cons b bs ih => simp [subBorrow, ih]
  | cons a as ih =>
    cases ys with
    | nil => simp [subBorrow, ih]
    | cons b bs => simp [subBorrow, ih, max_add_add_right]

theorem subBorrow_cost (xs ys : List Bool) (c : Bool) :
    (subBorrow xs ys c).cost = 16 * max xs.length ys.length + 1 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subBorrow]
    | cons b bs ih => simp [subBorrow, ih]; omega
  | cons a as ih =>
    cases ys with
    | nil => simp [subBorrow, ih]; omega
    | cons b bs => simp [subBorrow, ih, max_add_add_right]; omega

theorem value_lt_pow_length (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b bs ih =>
    cases b <;> simp only [value, Bool.toNat_false, Bool.toNat_true, List.length_cons, pow_succ] <;>
      omega

/-- Truncated natural subtraction, including an explicit overflow test. -/
def subBits (xs ys : List Bool) : List Bool × ℕ :=
  let r := subBorrow xs ys false
  (if r.borrow then [] else r.bits, r.cost + 1)

theorem subBits_value (xs ys : List Bool) :
    value (subBits xs ys).1 = value xs - value ys := by
  have hv := subBorrow_value xs ys false
  have hb := value_lt_pow_length (subBorrow xs ys false).bits
  rw [subBorrow_length] at hb
  simp only [Bool.toNat_false, add_zero] at hv
  dsimp only [subBits]
  cases he : (subBorrow xs ys false).borrow
  · simp only [he, Bool.false_eq_true, ↓reduceIte]
    rw [he] at hv
    simp only [Bool.toNat_false, mul_zero, add_zero] at hv
    omega
  · simp only [he, ↓reduceIte, value]
    rw [he] at hv
    simp only [Bool.toNat_true, mul_one] at hv
    omega

theorem subBits_length (xs ys : List Bool) :
    (subBits xs ys).1.length ≤ max xs.length ys.length := by
  dsimp only [subBits]
  split_ifs
  · simp
  · exact (subBorrow_length xs ys false).le

theorem subBits_cost (xs ys : List Bool) :
    (subBits xs ys).2 = 16 * max xs.length ys.length + 2 := by
  simp [subBits, subBorrow_cost, Nat.add_assoc]

theorem subtract_standard (m n : ℕ) :
    value (subBits m.bits n.bits).1 = m - n ∧
      (subBits m.bits n.bits).2 ≤ 16 * (m.size + n.size) + 2 := by
  constructor
  · simp [subBits_value]
  · rw [subBits_cost, ← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len]
    omega

end BalancedAssortments.Decomposition.CostBinary
