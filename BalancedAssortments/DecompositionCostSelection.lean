import BalancedAssortments.DecompositionCostMachine

namespace BalancedAssortments.Decomposition.CostMachine
open ComplexityTimeBinary

/-- Read the selected labels from a parallel incidence mask. -/
def chosen {I : Type*} : List I → List Bool → List I
  | [], _ => []
  | _, [] => []
  | i :: ids, b :: bs => if b then i :: chosen ids bs else chosen ids bs

def oneLabels {I : Type*} : List I → Flags → List I
  | [], _ => []
  | _, [] => []
  | i :: ids, f :: fs => if f.1 then i :: oneLabels ids fs else oneLabels ids fs

def extraLabels {I : Type*} : List I → Flags → List I
  | [], _ => []
  | _, [] => []
  | i :: ids, f :: fs => if !f.1 && f.2 then i :: extraLabels ids fs else extraLabels ids fs

theorem removeOnes_length (q : List Unit) (fs : Flags) :
    (removeOnes q fs).1.length = q.length - (fs.filter Prod.fst).length := by
  induction fs generalizing q with
  | nil => simp [removeOnes]
  | cons f fs ih =>
    rcases f with ⟨a,b⟩
    cases a <;> cases q <;> simp [removeOnes, ih] <;> omega

theorem buildMask_chosen {I : Type*} [DecidableEq I] (ids : List I) (fs : Flags)
    (hlen : ids.length = fs.length) (q : List Unit) :
    (chosen ids (buildMask q fs).1).toFinset =
      (oneLabels ids fs).toFinset ∪ ((extraLabels ids fs).take q.length).toFinset := by
  induction ids generalizing fs q with
  | nil => cases fs <;> simp_all [chosen, oneLabels, extraLabels, buildMask]
  | cons i ids ih =>
    cases fs with
    | nil => simp at hlen
    | cons f fs =>
      have hl : ids.length = fs.length := by simpa using hlen
      rcases f with ⟨a,b⟩
      cases a <;> cases b <;> cases q <;>
        simp [chosen, oneLabels, extraLabels, buildMask, ih fs hl,
          Finset.insert_union, Finset.union_insert, Finset.union_assoc, Finset.union_comm]

theorem oneLabels_map {I : Type*} (ids : List I) (f : I → Bool × Bool) :
    oneLabels ids (ids.map f) = ids.filter (fun i => (f i).1) := by
  induction ids with
  | nil => rfl
  | cons i ids ih => simp only [oneLabels, List.map_cons, List.filter_cons, ih]

theorem extraLabels_map {I : Type*} (ids : List I) (f : I → Bool × Bool) :
    extraLabels ids (ids.map f) = ids.filter (fun i => !(f i).1 && (f i).2) := by
  induction ids with
  | nil => rfl
  | cons i ids ih => simp only [extraLabels, List.map_cons, List.filter_cons, ih]

/-- A Fin-indexed interpretation of an output mask, forgiving absent entries. -/
def maskSet {n : ℕ} (ms : List Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ms[i.val]?.getD false


theorem chosen_map {I J : Type*} (ids : List I) (ms : List Bool) (f : I → J) :
    chosen (ids.map f) ms = (chosen ids ms).map f := by
  induction ids generalizing ms with
  | nil => simp [chosen]
  | cons i ids ih => cases ms with
    | nil => simp [chosen]
    | cons b bs => cases b <;> simp [chosen, ih]

theorem chosen_finRange_mem (n : ℕ) (ms : List Bool) (i : Fin n) :
    i ∈ chosen (List.finRange n) ms ↔ ms[i.val]?.getD false = true := by
  induction n generalizing ms with
  | zero => exact i.elim0
  | succ n ih =>
    cases ms with
    | nil => simp [chosen]
    | cons b bs =>
      cases b <;> refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [List.finRange_succ, chosen, chosen_map, ih]

theorem maskSet_eq_chosen {n : ℕ} (ms : List Bool) :
    maskSet (n := n) ms = (chosen (List.finRange n) ms).toFinset := by
  ext i
  simp [maskSet, chosen_finRange_mem]

theorem selectMask_chosen {I : Type*} [DecidableEq I] (ids : List I)
    (x : I → Bits) (R : Bits) (K : ℕ) :
    (chosen ids (selectMask K R (ids.map x)).1).toFinset =
      (ids.filter fun i => decide (value (x i) = value R)).toFinset ∪
      ((ids.filter fun i => decide (value (x i) ≠ value R ∧ 0 < value (x i))).take
        (K - (ids.filter fun i => decide (value (x i) = value R)).length)).toFinset := by
  dsimp only [selectMask]
  rw [classify_value]
  simp only [List.map_map, Function.comp_def]
  rw [buildMask_chosen ids _ (by simp)]
  rw [oneLabels_map, extraLabels_map, removeOnes_length]
  simp only [List.length_replicate]
  have hc : (List.filter Prod.fst (ids.map (fun i =>
      (decide (value (x i) = value R), decide (0 < value (x i)))))).length =
      (ids.filter fun i => decide (value (x i) = value R)).length := by
    induction ids with
    | nil => rfl
    | cons i ids ih =>
      simp only [List.map_cons, List.filter_cons]
      split_ifs <;> simp_all
  rw [hc]
  congr 3
  apply List.filter_congr
  intro i hi
  simp

theorem sort_filter_finRange {n : ℕ} (p : Fin n → Bool) :
    (Finset.univ.filter fun i => p i).sort (· ≤ ·) = (List.finRange n).filter p := by
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · apply List.perm_of_nodup_nodup_toFinset_eq
    · exact Finset.sort_nodup _ _
    · exact List.Nodup.filter p (List.nodup_finRange n)
    · ext i; simp
  · exact Finset.sort_sorted _ _
  · exact List.Pairwise.filter p (List.pairwise_le_finRange n)

/-- The two-pass Boolean selector exactly implements the integer-grid greedy
selection, including rank zero and insufficient-positive-coordinate cases. -/
theorem selectMask_gridSet {n : ℕ} (K : ℕ) (R : Bits) (x : Fin n → Bits) :
    maskSet (n := n) (selectMask K R ((List.finRange n).map x)).1 =
      gridSet K (value R) (fun i => value (x i)) := by
  rw [maskSet_eq_chosen, selectMask_chosen]
  have hones : ((List.finRange n).filter fun i => decide (value (x i) = value R)).toFinset =
      gridOnes (value R) (fun i => value (x i)) := by
    ext i; simp [gridOnes]
  have hcount : ((List.finRange n).filter fun i => decide (value (x i) = value R)).length =
      (gridOnes (value R) (fun i => value (x i))).card := by
    rw [← hones]
    exact (List.toFinset_card_of_nodup
      (List.Nodup.filter _ (List.nodup_finRange n))).symm
  have hextra : (gridPositive (fun i => value (x i)) \ gridOnes (value R) (fun i => value (x i))).sort (· ≤ ·) =
      (List.finRange n).filter fun i => decide (value (x i) ≠ value R ∧ 0 < value (x i)) := by
    have he : gridPositive (fun i => value (x i)) \ gridOnes (value R) (fun i => value (x i)) =
        Finset.univ.filter fun i => decide (value (x i) ≠ value R ∧ 0 < value (x i)) := by
      ext i; simp [gridPositive, gridOnes, and_comm]
    rw [he]
    exact sort_filter_finRange _
  simp only [gridSet, hones, hcount, hextra]
end BalancedAssortments.Decomposition.CostMachine
