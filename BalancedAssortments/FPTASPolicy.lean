import BalancedAssortments.FPTAS
import BalancedAssortments.SalesIntegration

/-! Exact validity of the executable outer algorithm's rational policy output.
No approximation guarantee or bit-time bound is asserted here. -/
noncomputable section
namespace BalancedAssortments.FPTAS
open scoped BigOperators

/-- Aggregate MNL sales of an explicitly listed rational policy. -/
def policySales {n : ℕ} (v : Fin n → ℚ) (p : List (Decomposition.Atom n))
    (i : Fin n) : ℝ :=
  (p.map fun a => if i ∈ a.2 then
    (a.1 : ℝ) * (v i : ℝ) / (1 + ∑ j ∈ a.2, (v j : ℝ)) else 0).sum

/-- The list representation records rational weights; normalization is checked
in ℚ, and only nonzero-probability assortments need satisfy the display limit. -/
def PolicyValid {n : ℕ} (K : ℕ) (p : List (Decomposition.Atom n)) : Prop :=
  (∀ a ∈ p, 0 ≤ a.1) ∧ (p.map Prod.fst).sum = 1 ∧
    ∀ a ∈ p, a.1 ≠ 0 → a.2.card ≤ K

theorem reverse_list_correct {n K : ℕ} (v w : Fin n → ℚ)
    (hv : ∀ i, 0 < v i) {p : List (Decomposition.Atom n)}
    (hp : Decomposition.ValidDecomposition K (fun i => w i / v i) p) :
    let out := p.map fun a =>
      (a.1 * (1 + ∑ i ∈ a.2, v i) / (1 + ∑ i, w i), a.2)
    PolicyValid K out ∧ policySales v out = Sales.compactSales (fun i => (w i : ℝ)) := by
  let f : Decomposition.Atom n → Decomposition.Atom n := fun a =>
    (a.1 * (1 + ∑ i ∈ a.2, v i) / (1 + ∑ i, w i), a.2)
  let pp := Sales.certificateWeights p
  let S := Sales.certificateSets p
  have hpp : Sales.Distribution pp := Sales.certificate_distribution hp
  have hvr : ∀ i, (0 : ℝ) < (v i : ℝ) := fun i => by exact_mod_cast hv i
  have hsum : ∑ i, v i * (w i / v i) = ∑ i, w i := by
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hv i).ne']
  have heq : (fun a : Fin p.length => ((f p[a.val]).1 : ℝ)) =
      Sales.reverseTilt (fun i => (v i : ℝ)) S pp := by
    rw [← Sales.rationalPolicy_cast v hp]
    funext a
    simp [f, Sales.rationalPolicy, hsum]
  have hdist := Sales.reverse_distribution (fun i => (v i : ℝ))
    (fun i => (hvr i).le) S hpp
  rw [← heq] at hdist
  change PolicyValid K (p.map f) ∧ policySales v (p.map f) = _
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ha
      have ht := hdist.1 ⟨i, hi⟩
      dsimp only at ht
      rw [he] at ht
      exact_mod_cast ht
    · have ht := hdist.2
      dsimp only at ht
      rw [Fin.sum_univ_fun_getElem p (fun a => ((f a).1 : ℝ))] at ht
      change ((p.map f).map Prod.fst).sum = 1
      simp only [List.map_map, Function.comp_def]
      apply (Rat.cast_injective (α := ℝ))
      simpa only [Rat.cast_list_sum, Rat.cast_one, List.map_map, Function.comp_def] using ht
    · intro b hb hbn
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      apply hp.2.2.1 a ha
      intro hz
      apply hbn
      simp [f, hz]
  · funext i
    have hs := Sales.reverse_sales (fun j => (v j : ℝ))
      (fun j => (hvr j).le) S pp i
    rw [← heq] at hs
    have hw : (fun j => (v j : ℝ) * Sales.marginal S pp j) =
        (fun j => (w j : ℝ)) := by
      funext j
      rw [Sales.certificate_marginal hp j]
      push_cast
      field_simp [(hvr j).ne']
    rw [hw] at hs
    rw [← hs]
    unfold policySales Sales.sales
    simp only [List.map_map, Function.comp_def]
    change (p.map (fun a => if i ∈ a.2 then ((f a).1 : ℝ) * (v i : ℝ) /
        (1 + ∑ j ∈ a.2, (v j : ℝ)) else 0)).sum =
      ∑ a : Fin p.length, if i ∈ (p[a.val]).2 then ((f p[a.val]).1 : ℝ) * (v i : ℝ) /
        (1 + ∑ j ∈ (p[a.val]).2, (v j : ℝ)) else 0
    exact (Fin.sum_univ_fun_getElem p (fun a => if i ∈ a.2 then ((f a).1 : ℝ) * (v i : ℝ) /
        (1 + ∑ j ∈ a.2, (v j : ℝ)) else 0)).symm


/-- Exact feasibility and linear support hold for the actual executable output,
for every epsilon (approximation guarantees require separate epsilon bounds). -/
theorem runPolicy_valid {n : ℕ} (d : Input n) (ε : ℚ)
    (hv : ∀ i, 0 < d.v i) :
    PolicyValid d.K (runPolicy d ε) ∧
      (runPolicy d ε).length ≤ n + 2 ∧
      policySales d.v (runPolicy d ε) =
        Sales.compactSales (fun i => (runSales d ε i : ℝ)) := by
  have hf := runSales_feasible d ε (fun i => (hv i).le)
  have hz : Decomposition.Feasible d.K (fun i => runSales d ε i / d.v i) := by
    refine ⟨?_, hf.2.1⟩
    intro i
    exact ⟨div_nonneg (hf.1 i).1 (hv i).le, (div_le_one (hv i)).2 (hf.1 i).2⟩
  have hg := Decomposition.greedy_correct hz
  have hout := reverse_list_correct d.v (runSales d ε) hv hg.1
  refine ⟨hout.1, ?_, hout.2⟩
  simpa [runPolicy, Nat.add_assoc] using hg.2


/-- The executable policy preserves BMS exactly and realizes precisely the
objective of the executable selected sales vector. -/
theorem runPolicy_balance_revenue {n : ℕ} (d : Input n) (ε : ℚ)
    (hv : ∀ i, 0 < d.v i) :
    Sales.Balanced (d.α : ℝ) (policySales d.v (runPolicy d ε)) ∧
      Sales.revenue (fun i => (d.r i : ℝ)) (policySales d.v (runPolicy d ε)) =
        (revenue d (runSales d ε) : ℝ) := by
  have hf := runSales_feasible d ε (fun i => (hv i).le)
  rw [(runPolicy_valid d ε hv).2.2]
  constructor
  · apply (Sales.compact_balance (d.α : ℝ) (fun i => (runSales d ε i : ℝ))
      (fun i => by dsimp only; exact_mod_cast (hf.1 i).1)).2
    intro i
    rcases hf.2.2 i with hi | hi
    · left
      dsimp only
      exact_mod_cast hi
    · right
      intro j
      dsimp only
      exact_mod_cast hi j
  · rw [Sales.compact_revenue]
    unfold Sales.objective revenue
    push_cast
    rfl

end BalancedAssortments.FPTAS
