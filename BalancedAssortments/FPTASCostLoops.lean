import BalancedAssortments.FPTASCostCutoff

/-! Structural list loops for the finite scale/revenue search and incumbent scan.
All callback costs and list-copy overhead are included. -/
namespace BalancedAssortments.FPTASCostLoops
open KnapsackCostRational

def collect {α β : Type*} (f : α → Option β × ℕ) : List α → List β × ℕ
  | [] => ([],1)
  | x::xs =>
      let head := f x
      let tail := collect f xs
      (match head.1 with | none => tail.1 | some y => y::tail.1,
        head.2+tail.2+4)

lemma collect_eq {α β : Type*} (f : α → Option β × ℕ) (xs : List α) :
    (collect f xs).1 = xs.filterMap (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [collect,List.filterMap_cons,ih]; cases (f x).1 <;> rfl

lemma collect_length {α β : Type*} (f : α → Option β × ℕ) (xs : List α) :
    (collect f xs).1.length ≤ xs.length := by rw [collect_eq]; exact List.length_filterMap_le _ _

lemma collect_cost {α β : Type*} (f : α → Option β × ℕ) (xs : List α) {C : ℕ}
    (hf : ∀ x ∈ xs, (f x).2 ≤ C) : (collect f xs).2 ≤ xs.length*(C+4)+1 := by
  induction xs with
  | nil => simp [collect]
  | cons x xs ih =>
    have hh := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp only [collect,List.length_cons]
    nlinarith

/-- Enumerate both grids, with the same order as the source flatMap/filterMap. -/
def cross {α β γ : Type*} (f : α → β → Option γ × ℕ) : List α → List β → List γ × ℕ
  | [], _ => ([],1)
  | x::xs, ys =>
      let head := collect (f x) ys
      let tail := cross f xs ys
      (head.1++tail.1,head.2+tail.2+head.1.length+4)

lemma cross_eq {α β γ : Type*} (f : α → β → Option γ × ℕ) (xs : List α) (ys : List β) :
    (cross f xs ys).1 = xs.flatMap (fun x => ys.filterMap (fun y => (f x y).1)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [cross,collect_eq,ih]

lemma cross_cost {α β γ : Type*} (f : α → β → Option γ × ℕ) (xs : List α) (ys : List β) {C : ℕ}
    (hf : ∀ x ∈ xs, ∀ y ∈ ys, (f x y).2 ≤ C) :
    (cross f xs ys).2 ≤ xs.length*(ys.length*(C+5)+5)+1 := by
  induction xs with
  | nil => simp [cross]
  | cons x xs ih =>
    have hh := collect_cost (f x) ys (hf x (by simp))
    have hl := collect_length (f x) ys
    have ht := ih (fun x hx y hy => hf x (by simp [hx]) y hy)
    simp only [cross,List.length_cons]
    nlinarith

def improveAll (prices : List Fraction) : List Fraction → List (List Fraction) → List Fraction × ℕ
  | old, [] => (old,1)
  | old, next::rest =>
      let choice := FPTASCostOutput.improve prices old next
      let result := improveAll prices choice.1 rest
      (result.1,choice.2+result.2+4)

lemma improveAll_member (prices old : List Fraction) (candidates : List (List Fraction)) :
    (improveAll prices old candidates).1 = old ∨ (improveAll prices old candidates).1 ∈ candidates := by
  induction candidates generalizing old with
  | nil => exact Or.inl rfl
  | cons next rest ih =>
    have hh := ih (FPTASCostOutput.improve prices old next).1
    rcases hh with hh | hh
    · rcases FPTASCostOutput.improve_cases prices old next with hc | hc
      · exact Or.inl (hh.trans hc)
      · exact Or.inr (List.mem_cons.mpr (Or.inl (hh.trans hc)))
    · exact Or.inr (List.mem_cons_of_mem _ hh)

lemma improveAll_max (prices old : List Fraction) (candidates : List (List Fraction))
    (hp : ∀ x ∈ prices, x.Valid) (ho : ∀ x ∈ old, x.Valid)
    (hc : ∀ xs ∈ candidates, ∀ x ∈ xs, x.Valid) :
    (FPTASCostOutput.revenue prices (improveAll prices old candidates).1).1.decode =
      (candidates.map fun xs => (FPTASCostOutput.revenue prices xs).1.decode).foldl max
        (FPTASCostOutput.revenue prices old).1.decode := by
  induction candidates generalizing old with
  | nil => rfl
  | cons next rest ih =>
    have hn := hc next (by simp)
    have hv : ∀ x ∈ (FPTASCostOutput.improve prices old next).1, x.Valid := by
      rcases FPTASCostOutput.improve_cases prices old next with he | he
      · simpa only [he] using ho
      · simpa only [he] using hn
    have hh := ih _ hv (fun xs hxs x hx => hc xs (by simp [hxs]) x hx)
    simp only [improveAll,List.map_cons,List.foldl_cons]
    rw [hh,FPTASCostOutput.improve_max prices old next hp ho hn]

lemma improveAll_cost (prices old : List Fraction) (candidates : List (List Fraction)) {N b : ℕ}
    (hplen : prices.length ≤ N) (holen : old.length ≤ N)
    (hp : ∀ x ∈ prices, x.Width b) (ho : ∀ x ∈ old, x.Width b)
    (hc : ∀ xs ∈ candidates, xs.length ≤ N ∧ ∀ x ∈ xs, x.Width b) :
    (improveAll prices old candidates).2 ≤
      candidates.length*(2*FPTASCostOutput.revenueBudget N b+512*(FPTASCostOutput.revenueWidth N b+1)^2+10)+1 := by
  induction candidates generalizing old with
  | nil => simp [improveAll]
  | cons next rest ih =>
    have hn := hc next (by simp)
    have hv : (FPTASCostOutput.improve prices old next).1.length ≤ N ∧
        ∀ x ∈ (FPTASCostOutput.improve prices old next).1, x.Width b := by
      rcases FPTASCostOutput.improve_cases prices old next with he | he
      · simpa only [he] using And.intro holen ho
      · simpa only [he] using hn
    have hs := FPTASCostOutput.improve_cost prices old next hplen holen hn.1 hp ho hn.2
    have ht := ih _ hv.1 hv.2 (fun xs hxs => hc xs (by simp [hxs]))
    simp only [improveAll,List.length_cons]
    nlinarith

end BalancedAssortments.FPTASCostLoops
