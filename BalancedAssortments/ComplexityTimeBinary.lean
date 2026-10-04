import Mathlib

/-! Concrete bit-list arithmetic with an instrumented bit-operation cost.
The implementation never invokes natural-number addition/comparison on decoded
unbounded operands. Costs charge Boolean gates, list tests, reads, and writes.
This is an explicit bit/list machine model, not yet a Turing-machine simulation. -/
namespace BalancedAssortments.ComplexityTimeBinary

/-- Little-endian decoding. Leading zeroes are permitted. -/
def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

@[simp] theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n h ih => rw [Nat.bits_append_bit n b h]; simp only [value, ih, Nat.bit_val]; omega

/-- Two XOR, two AND and one OR gate: the conventional full adder. -/
def fullAdd (a b c : Bool) : Bool × Bool :=
  let p := xor a b
  (xor p c, (a && b) || (c && p))

theorem fullAdd_correct (a b c : Bool) :
    (fullAdd a b c).1.toNat + 2 * (fullAdd a b c).2.toNat =
      a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

/-- Ripple-carry implementation. Cost includes the five gates and constant
list dispatch/read/write overhead at each processed bit position. -/
def addCarry : List Bool → List Bool → Bool → List Bool × ℕ
  | [], [], c => ([c], 1)
  | a :: as, [], c =>
      let f := fullAdd a false c
      let r := addCarry as [] f.2
      (f.1 :: r.1, r.2 + 16)
  | [], b :: bs, c =>
      let f := fullAdd false b c
      let r := addCarry [] bs f.2
      (f.1 :: r.1, r.2 + 16)
  | a :: as, b :: bs, c =>
      let f := fullAdd a b c
      let r := addCarry as bs f.2
      (f.1 :: r.1, r.2 + 16)

/-- Correctness for arbitrary padded binary operands. -/
theorem addCarry_value (xs ys : List Bool) (c : Bool) :
    value (addCarry xs ys c).1 = value xs + value ys + c.toNat := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [addCarry, value]
    | cons b bs ih =>
      simp only [addCarry, value]
      rw [ih]
      try simp only [value]
      have h := fullAdd_correct false b c
      simp only [Bool.toNat_false] at h
      omega
  | cons a as ih =>
    cases ys with
    | nil =>
      simp only [addCarry, value]
      rw [ih]
      try simp only [value]
      have h := fullAdd_correct a false c
      simp only [Bool.toNat_false] at h
      omega
    | cons b bs =>
      simp only [addCarry, value]
      rw [ih]
      try simp only [value]
      have h := fullAdd_correct a b c
      omega

/-- Exact running cost, not merely an arithmetic-operation count. -/
theorem addCarry_cost (xs ys : List Bool) (c : Bool) :
    (addCarry xs ys c).2 = 16 * max xs.length ys.length + 1 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [addCarry]
    | cons b bs ih => simp [addCarry, ih]; omega
  | cons a as ih =>
    cases ys with
    | nil => simp [addCarry, ih]; omega
    | cons b bs => simp [addCarry, ih, max_add_add_right]; omega

theorem addCarry_length (xs ys : List Bool) (c : Bool) :
    (addCarry xs ys c).1.length = max xs.length ys.length + 1 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [addCarry]
    | cons b bs ih => simp [addCarry, ih]
  | cons a as ih =>
    cases ys with
    | nil => simp [addCarry, ih]
    | cons b bs => simp [addCarry, ih, max_add_add_right]

/-- Addition on actual standard binary inputs has linear binary cost. -/
theorem add_standard (m n : ℕ) :
    value (addCarry m.bits n.bits false).1 = m+n ∧
    (addCarry m.bits n.bits false).2 ≤ 16 * (m.size+n.size) + 1 := by
  constructor
  · simp [addCarry_value]
  · rw [addCarry_cost, ← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len]
    have : max m.size n.size ≤ m.size+n.size := max_le (by omega) (by omega)
    omega

/-- Refinement of the high-order comparison with one low-order bit pair. -/
def lowCompare (a b : Bool) (high : Ordering) : Ordering :=
  match high with
  | .eq => if a then (if b then .eq else .gt) else (if b then .lt else .eq)
  | .lt => .lt
  | .gt => .gt

def comparisonMeaning (o : Ordering) (x y : ℕ) : Prop :=
  match o with
  | .lt => x < y
  | .eq => x = y
  | .gt => y < x

theorem lowCompare_correct (a b : Bool) (high : Ordering) (x y : ℕ)
    (h : comparisonMeaning high x y) :
    comparisonMeaning (lowCompare a b high) (a.toNat+2*x) (b.toNat+2*y) := by
  cases high <;> cases a <;> cases b <;> simp_all [lowCompare, comparisonMeaning] <;> omega

/-- Comparator scans every bit exactly once; zero padding is handled without
normalization or numerical comparison of unbounded integers. -/
def compareBits : List Bool → List Bool → Ordering × ℕ
  | [], [] => (.eq, 1)
  | a :: as, [] =>
      let r := compareBits as []
      (lowCompare a false r.1, r.2 + 16)
  | [], b :: bs =>
      let r := compareBits [] bs
      (lowCompare false b r.1, r.2 + 16)
  | a :: as, b :: bs =>
      let r := compareBits as bs
      (lowCompare a b r.1, r.2 + 16)

theorem compareBits_correct (xs ys : List Bool) :
    comparisonMeaning (compareBits xs ys).1 (value xs) (value ys) := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [compareBits, comparisonMeaning, value]
    | cons b bs ih =>
      simpa [compareBits, value] using lowCompare_correct false b (compareBits [] bs).1 0 (value bs) ih
  | cons a as ih =>
    cases ys with
    | nil =>
      simpa [compareBits, value] using lowCompare_correct a false (compareBits as []).1 (value as) 0 (ih [])
    | cons b bs =>
      simpa only [compareBits, value] using lowCompare_correct a b (compareBits as bs).1 (value as) (value bs) (ih bs)

theorem compareBits_cost (xs ys : List Bool) :
    (compareBits xs ys).2 = 16 * max xs.length ys.length + 1 := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [compareBits]
    | cons b bs ih => simp [compareBits, ih]; omega
  | cons a as ih =>
    cases ys with
    | nil => simp [compareBits, ih]; omega
    | cons b bs => simp [compareBits, ih, max_add_add_right]; omega

def leBits (xs ys : List Bool) : Bool := (compareBits xs ys).1 != Ordering.gt

theorem leBits_correct (xs ys : List Bool) :
    leBits xs ys = true ↔ value xs ≤ value ys := by
  have h := compareBits_correct xs ys
  unfold leBits
  generalize ho : (compareBits xs ys).1 = o at *
  cases o <;> simp_all [comparisonMeaning] <;> omega

/-- Schoolbook shift-and-add multiplication on raw bit lists. -/
def mulBits : List Bool → List Bool → List Bool × ℕ
  | [], _ => ([], 1)
  | a :: as, ys =>
      let r := mulBits as ys
      if a then
        let z := addCarry ys (false :: r.1) false
        (z.1, r.2 + z.2 + 4)
      else (false :: r.1, r.2 + 4)

theorem mulBits_value (xs ys : List Bool) :
    value (mulBits xs ys).1 = value xs * value ys := by
  induction xs with
  | nil => simp [mulBits, value]
  | cons a as ih =>
    cases a <;> simp [mulBits, value, addCarry_value, ih] <;> ring

theorem mulBits_length (xs ys : List Bool) :
    (mulBits xs ys).1.length ≤ 2*xs.length+ys.length := by
  induction xs with
  | nil => simp [mulBits]
  | cons a as ih =>
    cases a
    · simp only [mulBits, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · simp only [mulBits, ↓reduceIte, addCarry_length, List.length_cons]
      omega

/-- A quadratic bound counting binary gates and list operations of the explicit
schoolbook multiplication, rather than treating multiplication as an oracle. -/
theorem mulBits_cost (xs ys : List Bool) :
    (mulBits xs ys).2 ≤ 64 * xs.length * (xs.length + ys.length + 1) + 1 := by
  induction xs with
  | nil => simp [mulBits]
  | cons a as ih =>
    have hl := mulBits_length as ys
    cases a
    · simp only [mulBits, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      nlinarith
    · simp only [mulBits, ↓reduceIte, addCarry_cost, List.length_cons]
      have hm : max ys.length ((mulBits as ys).1.length + 1) ≤
          2 * as.length + ys.length + 1 := by omega
      nlinarith

theorem multiply_standard (m n : ℕ) :
    value (mulBits m.bits n.bits).1 = m*n ∧
    (mulBits m.bits n.bits).2 ≤ 64 * m.size * (m.size+n.size+1) + 1 := by
  constructor
  · simp [mulBits_value]
  · simpa only [← Nat.size_eq_bits_len] using mulBits_cost m.bits n.bits

end BalancedAssortments.ComplexityTimeBinary
