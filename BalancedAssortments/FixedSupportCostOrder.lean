import BalancedAssortments.FixedSupportCostScalars
import BalancedAssortments.FixedSupportCostSort
import BalancedAssortments.FixedSupportAlgorithmOrder
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace BalancedAssortments.FixedSupportCostOrder
open ComplexityTimeFractions (decode Valid width)
open FixedSupportCostRational FixedSupportCostLists FixedSupportCostPoints FixedSupportCostScalars

structure Scored (I : Type*) where
  label : I
  product : Product
  score : Fraction

/-- Labels are copied unchanged; all numerical work is charged binary arithmetic. -/
def prepare {I : Type*} (ps : List (I × Product)) (ρ : Fraction) : List (Scored I) × ℕ :=
  mapCost (fun p => let s := scoreBits p.2 ρ; (⟨p.1,p.2,s.1⟩,s.2+4)) ps

def compare {I : Type*} (a b : Scored I) : Bool × ℕ :=
  let c := FixedSupportCostRational.le b.score a.score
  (c.1,c.2+2)

def ordered {I : Type*} (ps : List (I × Product)) (ρ : Fraction) : List (Scored I) × ℕ :=
  let rows := prepare ps ρ
  let result := FixedSupportCostSort.sort compare rows.1
  (result.1,rows.2+result.2+4)

@[simp] theorem prepare_length {I : Type*} (ps : List (I × Product)) (ρ : Fraction) :
    (prepare ps ρ).1.length = ps.length := by simp [prepare]

@[simp] theorem prepare_labels {I : Type*} (ps : List (I × Product)) (ρ : Fraction) :
    (prepare ps ρ).1.map Scored.label = ps.map Prod.fst := by simp [prepare, List.map_map, Function.comp_def]

@[simp] theorem ordered_length {I : Type*} (ps : List (I × Product)) (ρ : Fraction) :
    (ordered ps ρ).1.length = ps.length := by simp [ordered]

theorem prepare_member {I : Type*} (ps : List (I × Product)) (ρ : Fraction)
    {s : Scored I} (hs : s ∈ (prepare ps ρ).1) :
    (s.label,s.product) ∈ ps ∧ s.score = (scoreBits s.product ρ).1 := by
  rw [prepare, mapCost_value] at hs
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hs
  exact ⟨hp,rfl⟩

theorem ordered_member {I : Type*} (ps : List (I × Product)) (ρ : Fraction)
    {s : Scored I} (hs : s ∈ (ordered ps ρ).1) :
    (s.label,s.product) ∈ ps ∧ s.score = (scoreBits s.product ρ).1 := by
  apply prepare_member ps ρ
  exact (FixedSupportCostSort.mem_sort _ _ _).mp hs

theorem ordered_valid {I : Type*} (ps : List (I × Product)) (ρ : Fraction)
    (hp : ∀ p ∈ ps, p.2.Valid) (hρ : Valid ρ) :
    ∀ s ∈ (ordered ps ρ).1, s.product.Valid ∧ Valid s.score := by
  intro s hs
  have hm := ordered_member ps ρ hs
  refine ⟨hp _ hm.1, ?_⟩
  rw [hm.2]
  exact scoreBits_valid _ _ (hp _ hm.1) hρ

theorem ordered_width {I : Type*} (ps : List (I × Product)) (ρ : Fraction) {A B : ℕ}
    (hp : ∀ p ∈ ps, p.2.Width B) (hρ : width ρ ≤ A) :
    ∀ s ∈ (ordered ps ρ).1, s.product.Width B ∧ width s.score ≤ 2*A+3*B+3 := by
  intro s hs
  have hm := ordered_member ps ρ hs
  refine ⟨hp _ hm.1, ?_⟩
  rw [hm.2]
  exact scoreBits_width _ _ (hp _ hm.1) hρ

def orderCost (n A B : ℕ) : ℕ :=
  (n*(32768*(A+B+1)^2+8)+1) +
    (32*(2048*(2*(2*A+3*B+3)+1)^2+22)*n^2+1)+4

theorem ordered_cost {I : Type*} (ps : List (I × Product)) (ρ : Fraction) {A B : ℕ}
    (hp : ∀ p ∈ ps, p.2.Width B) (hρ : width ρ ≤ A) :
    (ordered ps ρ).2 ≤ orderCost ps.length A B := by
  have hprep := mapCost_cost (fun p : I × Product => let s := scoreBits p.2 ρ;
      ((⟨p.1,p.2,s.1⟩ : Scored I),s.2+4)) ps
    (C := 32768*(A+B+1)^2+4) (fun p hp' => Nat.add_le_add_right (scoreBits_cost p.2 ρ (hp p hp') hρ) 4)
  have hw : ∀ s ∈ (prepare ps ρ).1, width s.score ≤ 2*A+3*B+3 := by
    intro s hs
    have hm := prepare_member ps ρ hs
    rw [hm.2]
    exact scoreBits_width _ _ (hp _ hm.1) hρ
  have hsort := FixedSupportCostSort.sort_cost compare (prepare ps ρ).1
    (2048*(2*(2*A+3*B+3)+1)^2+2) (by
      intro a ha b hb
      have hc := le_cost (hw b hb) (hw a ha)
      dsimp only [compare]
      convert Nat.add_le_add_right hc 2 using 1 <;> ring)
  rw [prepare_length] at hsort
  have hp' : (prepare ps ρ).2 ≤ ps.length*(32768*(A+B+1)^2+8)+1 := by
    simpa only [prepare, Nat.add_assoc, Nat.reduceAdd] using hprep
  have hs' : (FixedSupportCostSort.sort compare (prepare ps ρ).1).2 ≤
      32*(2048*(2*(2*A+3*B+3)+1)^2+22)*ps.length^2+1 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hsort
  dsimp only [ordered, orderCost]
  exact Nat.add_le_add_right (Nat.add_le_add hp' hs') 4

/-- Exact stable-order refinement, including ties. All comparisons are performed
on binary scores, and the result agrees with the certified rational merge sort. -/
theorem ordered_labels {n : ℕ} (r v : Fin n → ℚ) (ps : List (Fin n × Product)) (ρ : Fraction)
    (hlabels : ps.map Prod.fst = List.finRange n)
    (hp : ∀ p ∈ ps, p.2.Valid) (hρ : Valid ρ)
    (hdata : ∀ p ∈ ps, decode p.2.1 = r p.1 ∧ decode p.2.2 = v p.1) :
    (ordered ps ρ).1.map Scored.label = FixedSupportAlgorithm.scoreOrder r v (decode ρ) := by
  have hs : ∀ s ∈ (prepare ps ρ).1,
      Valid s.score ∧ decode s.score = FixedSupportAlgorithm.score r v (decode ρ) s.label := by
    intro s hsm
    have hm := prepare_member ps ρ hsm
    constructor
    · rw [hm.2]
      exact scoreBits_valid _ _ (hp _ hm.1) hρ
    · rw [hm.2, scoreBits_decode _ _ (hp _ hm.1) hρ]
      rw [(hdata _ hm.1).1, (hdata _ hm.1).2]
      rfl
  dsimp only [ordered]
  rw [FixedSupportCostSort.sort_correct]
  rw [List.map_mergeSort (s := fun i j => decide
    (FixedSupportAlgorithm.score r v (decode ρ) j ≤ FixedSupportAlgorithm.score r v (decode ρ) i)) (by
      intro a ha b hb
      apply Bool.eq_iff_iff.mpr
      dsimp only [compare]
      simpa [(hs a ha).2,(hs b hb).2] using le_correct b.score a.score (hs b hb).1 (hs a ha).1)]
  rw [prepare_labels,hlabels]
  rfl

end BalancedAssortments.FixedSupportCostOrder
