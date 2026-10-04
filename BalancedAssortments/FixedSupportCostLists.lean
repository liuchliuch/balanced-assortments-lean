import BalancedAssortments.FixedSupportCostRational
import BalancedAssortments.FPTASCostLoops

namespace BalancedAssortments.FixedSupportCostLists
open ComplexityTimeFractions (decode Valid width)
open FixedSupportCostRational

/-- Generic charged map, reusing the proved list-loop implementation. -/
def mapCost {A B : Type*} (f : A → B × ℕ) (xs : List A) : List B × ℕ :=
  FPTASCostLoops.collect (fun x => (some (f x).1, (f x).2)) xs

@[simp] theorem mapCost_value {A B : Type*} (f : A → B × ℕ) (xs : List A) :
    (mapCost f xs).1 = xs.map (fun x => (f x).1) := by
  simp [mapCost, FPTASCostLoops.collect_eq]

@[simp] theorem mapCost_length {A B : Type*} (f : A → B × ℕ) (xs : List A) :
    (mapCost f xs).1.length = xs.length := by simp

theorem mapCost_cost {A B : Type*} (f : A → B × ℕ) (xs : List A) {C : ℕ}
    (hf : ∀ x ∈ xs, (f x).2 ≤ C) : (mapCost f xs).2 ≤ xs.length * (C+4)+1 :=
  FPTASCostLoops.collect_cost _ xs hf

def filterCost {A : Type*} (f : A → Bool × ℕ) (xs : List A) : List A × ℕ :=
  FPTASCostLoops.collect (fun x => (if (f x).1 then some x else none, (f x).2+1)) xs

@[simp] theorem filterCost_value {A : Type*} (f : A → Bool × ℕ) (xs : List A) :
    (filterCost f xs).1 = xs.filter (fun x => (f x).1) := by
  rw [filterCost, FPTASCostLoops.collect_eq]
  induction xs with
  | nil => rfl
  | cons x xs ih => cases he : (f x).1 <;> simp [List.filterMap_cons, List.filter_cons, he, ih]

theorem filterCost_cost {A : Type*} (f : A → Bool × ℕ) (xs : List A) {C : ℕ}
    (hf : ∀ x ∈ xs, (f x).2 ≤ C) : (filterCost f xs).2 ≤ xs.length * (C+5)+1 := by
  have hh := FPTASCostLoops.collect_cost
    (fun x => (if (f x).1 then some x else none, (f x).2+1)) xs
    (C := C+1) (fun x hx => Nat.add_le_add_right (hf x hx) 1)
  simpa [filterCost, Nat.add_assoc] using hh

def flatMapCost {A B : Type*} (f : A → List B × ℕ) : List A → List B × ℕ
  | [] => ([], 1)
  | x :: xs =>
      let a := f x
      let b := flatMapCost f xs
      (a.1 ++ b.1, a.2 + b.2 + a.1.length + 4)

@[simp] theorem flatMapCost_value {A B : Type*} (f : A → List B × ℕ) (xs : List A) :
    (flatMapCost f xs).1 = xs.flatMap (fun x => (f x).1) := by induction xs <;> simp [flatMapCost, *]

theorem flatMapCost_cost {A B : Type*} (f : A → List B × ℕ) (xs : List A) {C H : ℕ}
    (hf : ∀ x ∈ xs, (f x).2 ≤ C ∧ (f x).1.length ≤ H) :
    (flatMapCost f xs).2 ≤ xs.length * (C+H+4)+1 := by
  induction xs with
  | nil => simp [flatMapCost]
  | cons x xs ih =>
    have hh := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp only [flatMapCost, List.length_cons]
    nlinarith

/-- Minimum/maximum is a charged comparison and a choice of an existing record. -/
def choose (small : Bool) (x y : Fraction) : Fraction × ℕ :=
  let c := FixedSupportCostRational.le x y
  (if small then (if c.1 then x else y) else (if c.1 then y else x), c.2 + 2)

def extreme (small : Bool) (a b : ℚ) : ℚ := if small then min a b else max a b

theorem choose_decode (small : Bool) (x y : Fraction) (hx : Valid x) (hy : Valid y) :
    decode (choose small x y).1 = extreme small (decode x) (decode y) := by
  have hh := le_correct x y hx hy
  by_cases hc : (FixedSupportCostRational.le x y).1 = true
  · have hxy := hh.mp hc
    cases small <;> simp [choose, extreme, hc, min_eq_left hxy, max_eq_right hxy]
  · have hyx : decode y ≤ decode x := le_of_not_ge (fun hxy => hc (hh.mpr hxy))
    cases small <;> simp [choose, extreme, hc, min_eq_right hyx, max_eq_left hyx]

theorem choose_valid (small : Bool) (x y : Fraction) (hx : Valid x) (hy : Valid y) :
    Valid (choose small x y).1 := by
  dsimp only [choose]
  split_ifs <;> assumption

theorem choose_width (small : Bool) (x y : Fraction) {B : ℕ}
    (hx : width x ≤ B) (hy : width y ≤ B) : width (choose small x y).1 ≤ B := by
  dsimp only [choose]
  split_ifs <;> assumption

theorem choose_cost (small : Bool) (x y : Fraction) {B : ℕ}
    (hx : width x ≤ B) (hy : width y ≤ B) :
    (choose small x y).2 ≤ 2048*(2*B+1)^2+2 := by
  have hh := le_cost hx hy
  simpa [choose, two_mul, Nat.add_assoc] using Nat.add_le_add_right hh 2

def foldExtreme (small : Bool) : Fraction → List Fraction → Fraction × ℕ
  | a, [] => (a, 1)
  | a, x :: xs =>
      let b := choose small a x
      let r := foldExtreme small b.1 xs
      (r.1, b.2 + r.2 + 4)

theorem foldExtreme_decode (small : Bool) (a : Fraction) (xs : List Fraction)
    (ha : Valid a) (hx : ∀ x ∈ xs, Valid x) :
    decode (foldExtreme small a xs).1 = (xs.map decode).foldl (extreme small) (decode a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    have hh := hx x (by simp)
    simp only [foldExtreme, List.map_cons, List.foldl_cons]
    rw [ih _ (choose_valid small a x ha hh) (fun y hy => hx y (by simp [hy])),
      choose_decode small a x ha hh]

theorem foldExtreme_valid (small : Bool) (a : Fraction) (xs : List Fraction)
    (ha : Valid a) (hx : ∀ x ∈ xs, Valid x) : Valid (foldExtreme small a xs).1 := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih => exact ih _ (choose_valid small a x ha (hx x (by simp))) (fun y hy => hx y (by simp [hy]))

theorem foldExtreme_width_cost (small : Bool) (a : Fraction) (xs : List Fraction) {B : ℕ}
    (ha : width a ≤ B) (hx : ∀ x ∈ xs, width x ≤ B) :
    width (foldExtreme small a xs).1 ≤ B ∧
      (foldExtreme small a xs).2 ≤ xs.length*(2048*(2*B+1)^2+6)+1 := by
  induction xs generalizing a with
  | nil => simpa [foldExtreme] using ha
  | cons x xs ih =>
    have hh := hx x (by simp)
    have hb := choose_width small a x ha hh
    have hc := choose_cost small a x ha hh
    have ht := ih _ hb (fun y hy => hx y (by simp [hy]))
    constructor
    · exact ht.1
    · simp only [foldExtreme, List.length_cons]
      nlinarith [ht.2]

/-- Add fixed-width fresh operands to one accumulator. -/
def sumAcc : Fraction → List Fraction → Fraction × ℕ
  | a, [] => (a, 1)
  | a, x :: xs =>
      let b := addFresh a x
      let r := sumAcc b.1 xs
      (r.1, b.2 + r.2 + 4)

theorem sumAcc_decode (a : Fraction) (xs : List Fraction) (ha : Valid a)
    (hx : ∀ x ∈ xs, Valid x) :
    decode (sumAcc a xs).1 = decode a + (xs.map decode).sum := by
  induction xs generalizing a with
  | nil => simp [sumAcc]
  | cons x xs ih =>
    have hh := hx x (by simp)
    simp only [sumAcc, List.map_cons, List.sum_cons]
    rw [ih _ (addFresh_valid a x ha hh) (fun y hy => hx y (by simp [hy])),
      addFresh_decode a x ha hh]
    ring

theorem sumAcc_valid (a : Fraction) (xs : List Fraction) (ha : Valid a)
    (hx : ∀ x ∈ xs, Valid x) : Valid (sumAcc a xs).1 := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih => exact ih _ (addFresh_valid a x ha (hx x (by simp))) (fun y hy => hx y (by simp [hy]))

theorem sumAcc_width (a : Fraction) (xs : List Fraction) {A B : ℕ}
    (ha : width a ≤ A) (hx : ∀ x ∈ xs, width x ≤ B) :
    width (sumAcc a xs).1 ≤ A + xs.length * (2*B+2) := by
  induction xs generalizing a A with
  | nil => simpa [sumAcc] using ha
  | cons x xs ih =>
    have hh := ih _ (addFresh_width ha (hx x (by simp))) (fun y hy => hx y (by simp [hy]))
    simpa [sumAcc, List.length_cons, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem sumAcc_cost (a : Fraction) (xs : List Fraction) {A B : ℕ}
    (ha : width a ≤ A) (hx : ∀ x ∈ xs, width x ≤ B) :
    (sumAcc a xs).2 ≤ xs.length *
      (4096 * (A + xs.length * (2*B+2) + B + 1)^2 + 4) + 1 := by
  induction xs generalizing a A with
  | nil => simp [sumAcc]
  | cons x xs ih =>
    have hh := hx x (by simp)
    have hw := addFresh_width ha hh
    have ht := ih _ hw (fun y hy => hx y (by simp [hy]))
    have hc := addFresh_cost ha hh
    have he : A + 2*B+2 + xs.length*(2*B+2)+B+1 = A+(xs.length+1)*(2*B+2)+B+1 := by ring
    rw [he] at ht
    have hs := Nat.pow_le_pow_left (show A+B+1 ≤ A+(xs.length+1)*(2*B+2)+B+1 by omega) 2
    simp only [sumAcc, List.length_cons]
    nlinarith

end BalancedAssortments.FixedSupportCostLists
