import Mathlib

/-! Instrumented stable merge sort, exactly matching `List.mergeSort` including
its contiguous split and left-first behavior on equal comparator outcomes.
Split quotas are built structurally from the input, without free division. -/
namespace BalancedAssortments.FixedSupportCostSort

/-- One marker per pair of input elements, rounded upward. -/
def halfTokens {α : Type*} : List α → List Unit × ℕ
  | [] => ([], 1)
  | [_] => ([()], 2)
  | _ :: _ :: xs => let r := halfTokens xs; (()::r.1, r.2+4)

theorem halfTokens_length {α : Type*} : ∀ xs : List α,
    (halfTokens xs).1.length = (xs.length+1)/2
  | [] => by simp [halfTokens]
  | [a] => by simp [halfTokens]
  | a::b::xs => by
      have h := halfTokens_length xs
      simp only [halfTokens, List.length_cons]
      omega

theorem halfTokens_cost {α : Type*} : ∀ xs : List α,
    (halfTokens xs).2 ≤ 4*xs.length+2
  | [] => by simp [halfTokens]
  | [a] => by simp [halfTokens]
  | a::b::xs => by
      have h := halfTokens_cost xs
      simp only [halfTokens, List.length_cons]
      omega

/-- Consume unary quota markers and preserve the order of both contiguous halves. -/
def splitTokens {α : Type*} : List Unit → List α → (List α × List α) × ℕ
  | [], xs => (([], xs), 1)
  | _::_, [] => (([], []), 1)
  | _::ts, x::xs => let r := splitTokens ts xs; ((x::r.1.1, r.1.2), r.2+4)

theorem splitTokens_correct {α : Type*} (ts : List Unit) (xs : List α) :
    (splitTokens ts xs).1 = (xs.take ts.length, xs.drop ts.length) := by
  induction ts generalizing xs with
  | nil => simp [splitTokens]
  | cons t ts ih => cases xs <;> simp [splitTokens, ih]

theorem splitTokens_cost {α : Type*} (ts : List Unit) (xs : List α) :
    (splitTokens ts xs).2 ≤ 4*ts.length+1 := by
  induction ts generalizing xs with
  | nil => simp [splitTokens]
  | cons t ts ih =>
    cases xs with
    | nil => simp [splitTokens]
    | cons x xs => have h := ih xs; simp only [splitTokens, List.length_cons]; omega

def splitHalf {α : Type*} (xs : List α) : (List α × List α) × ℕ :=
  let h := halfTokens xs
  let s := splitTokens h.1 xs
  (s.1, h.2+s.2+4)

theorem splitHalf_correct {α : Type*} (xs : List α) :
    (splitHalf xs).1 = (xs.take ((xs.length+1)/2), xs.drop ((xs.length+1)/2)) := by
  simp [splitHalf, splitTokens_correct, halfTokens_length]

theorem splitHalf_cost {α : Type*} (xs : List α) : (splitHalf xs).2 ≤ 16*(xs.length+1) := by
  have hh := halfTokens_cost xs
  have hs := splitTokens_cost (halfTokens xs).1 xs
  rw [halfTokens_length] at hs
  dsimp only [splitHalf]
  omega

/-- Only comparator calls and inspected/copied list cells are charged. Returning
an untouched tail is a constant-time pointer operation. -/
def merge {α : Type*} (cmp : α → α → Bool × ℕ) : List α → List α → List α × ℕ
  | [], ys => (ys, 1)
  | xs, [] => (xs, 1)
  | x::xs, y::ys =>
      let c := cmp x y
      if c.1 then let r := merge cmp xs (y::ys); (x::r.1, c.2+r.2+4)
      else let r := merge cmp (x::xs) ys; (y::r.1, c.2+r.2+4)
termination_by xs ys => xs.length+ys.length

theorem merge_correct {α : Type*} (cmp : α → α → Bool × ℕ) (xs ys : List α) :
    (merge cmp xs ys).1 = List.merge xs ys (fun x y => (cmp x y).1) := by
  induction xs generalizing ys with
  | nil => simp [merge, List.merge]
  | cons x xs ihx =>
    induction ys with
    | nil => simp [merge, List.merge]
    | cons y ys ihy =>
      simp only [merge, List.merge]
      split_ifs <;> simp [ihx, ihy]

theorem merge_cost {α : Type*} (cmp : α → α → Bool × ℕ) (xs ys : List α) (C : ℕ)
    (hc : ∀ x ∈ xs, ∀ y ∈ ys, (cmp x y).2 ≤ C) :
    (merge cmp xs ys).2 ≤ (xs.length+ys.length)*(C+4)+1 := by
  induction xs generalizing ys with
  | nil => simp [merge]
  | cons x xs ihx =>
    induction ys with
    | nil => simp [merge]
    | cons y ys ihy =>
      have hxy := hc x (by simp) y (by simp)
      simp only [merge]
      split_ifs
      · have hr := ihx (y::ys) (fun a ha b hb => hc a (by simp [ha]) b hb)
        simp only [List.length_cons] at hr ⊢
        nlinarith
      · have hr := ihy (fun a ha b hb => hc a ha b (by simp [hb]))
        simp only [List.length_cons] at hr ⊢
        nlinarith

private theorem splitHalf_smaller {α : Type*} (a b : α) (xs : List α) :
    (splitHalf (a::b::xs)).1.1.length < (a::b::xs).length ∧
      (splitHalf (a::b::xs)).1.2.length < (a::b::xs).length := by
  rw [splitHalf_correct]
  simp only [List.length_take, List.length_drop, List.length_cons]
  omega

/-- This is an actual recursive merge-sort program; proofs only justify its
termination. All split/list/comparator costs are returned explicitly. -/
def sort {α : Type*} (cmp : α → α → Bool × ℕ) : List α → List α × ℕ
  | [] => ([], 1)
  | [a] => ([a], 1)
  | a::b::xs =>
      let halves := splitHalf (a::b::xs)
      let left := sort cmp halves.1.1
      let right := sort cmp halves.1.2
      let out := merge cmp left.1 right.1
      (out.1, halves.2+left.2+right.2+out.2+4)
termination_by xs => xs.length
decreasing_by
  all_goals simp only [splitHalf_correct, List.length_take, List.length_drop, List.length_cons]; omega

/-- Exact library semantics, for any comparator and without order-law premises. -/
theorem sort_correct {α : Type*} (cmp : α → α → Bool × ℕ) (xs : List α) :
    (sort cmp xs).1 = xs.mergeSort (fun x y => (cmp x y).1) := by
  generalize hn : xs.length = n
  induction n using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => simp [sort]
    | cons a xs =>
      cases xs with
      | nil => simp [sort]
      | cons b xs =>
        have hs := splitHalf_smaller a b xs
        have hl := ih _ (by omega : (splitHalf (a::b::xs)).1.1.length < n) _ rfl
        have hr := ih _ (by omega : (splitHalf (a::b::xs)).1.2.length < n) _ rfl
        simp only [sort, merge_correct, hl, hr]
        rw [splitHalf_correct]
        simp [List.mergeSort, List.MergeSort.Internal.splitInTwo_fst,
          List.MergeSort.Internal.splitInTwo_snd]

@[simp] theorem sort_length {α : Type*} (cmp : α → α → Bool × ℕ) (xs : List α) :
    (sort cmp xs).1.length = xs.length := by rw [sort_correct]; simp

@[simp] theorem mem_sort {α : Type*} (cmp : α → α → Bool × ℕ) (xs : List α) (x : α) :
    x ∈ (sort cmp xs).1 ↔ x ∈ xs := by rw [sort_correct]; simp


/-- Explicit quadratic comparator/list bound; no ordering laws are needed for
the cost or exact refinement, and the comparator bound only covers input members. -/
theorem sort_cost {α : Type*} (cmp : α → α → Bool × ℕ) (xs : List α) (C : ℕ)
    (hc : ∀ x ∈ xs, ∀ y ∈ xs, (cmp x y).2 ≤ C) :
    (sort cmp xs).2 ≤ 32*(C+20)*xs.length^2+1 := by
  generalize hn : xs.length = n
  induction n using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => simp [sort] at hn ⊢
    | cons a xs =>
      cases xs with
      | nil => simp only [sort]; simp at hn; subst n; omega
      | cons b xs =>
        let input := a::b::xs
        let L := (splitHalf input).1.1
        let R := (splitHalf input).1.2
        have hsmall := splitHalf_smaller a b xs
        have hLl : L.length < n := by dsimp [L, input]; omega
        have hRl : R.length < n := by dsimp [R, input]; omega
        have hLmem : ∀ x ∈ L, x ∈ input := by
          intro x hx
          change x ∈ (splitHalf input).1.1 at hx
          rw [splitHalf_correct] at hx
          exact List.mem_of_mem_take hx
        have hRmem : ∀ x ∈ R, x ∈ input := by
          intro x hx
          change x ∈ (splitHalf input).1.2 at hx
          rw [splitHalf_correct] at hx
          exact List.mem_of_mem_drop hx
        have hL := ih L.length hLl L (fun x hx y hy => hc x (hLmem x hx) y (hLmem y hy)) rfl
        have hR := ih R.length hRl R (fun x hx y hy => hc x (hRmem x hx) y (hRmem y hy)) rfl
        have hm := merge_cost cmp (sort cmp L).1 (sort cmp R).1 C (by
          intro x hx y hy
          exact hc x (hLmem x ((mem_sort cmp L x).1 hx)) y (hRmem y ((mem_sort cmp R y).1 hy)))
        rw [sort_length, sort_length] at hm
        have hs := splitHalf_cost input
        have hlen : L.length+R.length = n := by
          dsimp [L, R]
          rw [splitHalf_correct]
          simp only [List.length_take, List.length_drop]
          change _ = n
          have he : input.length = n := hn
          omega
        have hLp : 0 < L.length := by
          dsimp [L, input]
          rw [splitHalf_correct]
          simp only [List.length_take, List.length_cons]
          omega
        have hRp : 0 < R.length := by
          dsimp [R, input]
          rw [splitHalf_correct]
          simp only [List.length_drop, List.length_cons]
          omega
        have hprodL : L.length ≤ L.length*R.length := Nat.le_mul_of_pos_right _ hRp
        have hprodR : R.length ≤ L.length*R.length := Nat.le_mul_of_pos_left _ hLp
        have hgap : L.length^2+R.length^2+n ≤ n^2 := by nlinarith only [hlen, hprodL, hprodR]
        have hscaled := Nat.mul_le_mul_left (32*(C+20)) hgap
        have hN : 2 ≤ n := by simp only [List.length_cons] at hn; omega
        have hins : input.length = n := hn
        rw [hins] at hs
        rw [sort]
        change (splitHalf input).2 + (sort cmp L).2 + (sort cmp R).2 +
          (merge cmp (sort cmp L).1 (sort cmp R).1).2 + 4 ≤ 32*(C+20)*n^2+1
        nlinarith only [hL, hR, hm, hs, hscaled, hlen, hN]

end BalancedAssortments.FixedSupportCostSort
