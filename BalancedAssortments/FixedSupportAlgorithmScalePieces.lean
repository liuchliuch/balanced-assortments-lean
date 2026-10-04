import BalancedAssortments.FixedSupportAlgorithmFinite
import BalancedAssortments.FixedSupportAlgorithmEndpoint
import BalancedAssortments.FixedSupportKnapsack

namespace BalancedAssortments.FixedSupportAlgorithm

/-- Rational breakpoints bracket an arbitrary real target without changing
which rational cuts lie strictly inside the resulting interval. -/
theorem rational_adjacent_bracket {C : Finset ℚ} {lo hi : ℚ} {x : ℝ}
    (hlo : lo ∈ C) (hhi : hi ∈ C) (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) :
    ∃ a ∈ C, ∃ b ∈ C, (a : ℝ) ≤ x ∧ x ≤ (b : ℝ) ∧
      ∀ c ∈ C, c ≤ a ∨ b ≤ c := by
  classical
  obtain ⟨a, ha, b, hb, hax, hxb, hgap⟩ := exists_adjacent_bracket
    (C := C.image (fun q : ℚ => (q : ℝ)))
    (Finset.mem_image.mpr ⟨lo, hlo, rfl⟩) (Finset.mem_image.mpr ⟨hi, hhi, rfl⟩) hx
  obtain ⟨a, harat, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b, hbrat, rfl⟩ := Finset.mem_image.mp hb
  refine ⟨a, harat, b, hbrat, hax, hxb, ?_⟩
  intro c hc
  have hh := hgap (c : ℝ) (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  exact_mod_cast hh

/-- Between adjacent attraction cuts, every coordinate has one fixed cap
formula throughout the closed interval, including both boundary ties. -/
theorem capCuts_no_crossing {n : ℕ} (v : Fin n → ℚ) {α T a b : ℚ}
    (hv : ∀ i, 0 < v i) (hα : 0 < α) (hT : 0 ≤ T)
    (hb : b ∈ capCuts v α T)
    (hgap : ∀ c ∈ capCuts v α T, c ≤ a ∨ b ≤ c) (i : Fin n) :
    α * v i ≤ a ∨ b ≤ α * v i := by
  by_cases hi : α * v i ≤ T
  · apply hgap
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      (mul_pos hα (hv i)).le, hi⟩
  · right
    exact (capCuts_bounds v α hT hb).2.trans (le_of_not_ge hi)

def capLine {n : ℕ} (v : Fin n → ℚ) (α a : ℚ) (i : Fin n) : Affine (𝕜 := ℚ) :=
  if α * v i ≤ a then (-(1 / v i), 1) else ((1 / α - 1) * (1 / v i), 0)

def prefixLine {n : ℕ} (v : Fin n → ℚ) (α K a : ℚ) (P : Finset (Fin n)) : Affine (𝕜 := ℚ) :=
  (-prefixDenominator v α P (cappedAt v α a), K - ((P ∩ cappedAt v α a).card : ℚ))

@[simp] theorem prefixLine_root {n : ℕ} (v : Fin n → ℚ) (α K a : ℚ) (P : Finset (Fin n)) :
    affineRoot (prefixLine v α K a P) = prefixRoot v α K a P := by
  unfold affineRoot prefixLine prefixRoot
  dsimp only
  rw [neg_div_neg_eq]

theorem capLine_real {n : ℕ} (v : Fin n → ℚ) {α a b : ℚ}
    (hv : ∀ i, 0 < v i) (hα : 0 < α)
    (hcross : ∀ i, α * v i ≤ a ∨ b ≤ α * v i)
    {t : ℝ} (ht : (a : ℝ) ≤ t ∧ t ≤ (b : ℝ)) (i : Fin n) :
    FixedSupportKnapsack.cap (fun j => (v j : ℝ)) (α : ℝ) t i =
      affineValue (((capLine v α a i).1 : ℝ), ((capLine v α a i).2 : ℝ)) t := by
  have hvR : ∀ j, (0 : ℝ) < v j := fun j => by exact_mod_cast hv j
  have hαR : (0 : ℝ) < α := by exact_mod_cast hα
  by_cases hi : α * v i ≤ a
  · have hit : (α : ℝ) * (v i : ℝ) ≤ t := (by exact_mod_cast hi : (α : ℝ) * v i ≤ (a : ℝ)).trans ht.1
    rw [FixedSupportKnapsack.cap_capped _ hvR hαR i hit]
    simp only [capLine, if_pos hi, affineValue]
    push_cast
    ring
  · have hib : b ≤ α * v i := (hcross i).resolve_left hi
    have hit : t ≤ (α : ℝ) * (v i : ℝ) := ht.2.trans (by exact_mod_cast hib)
    rw [FixedSupportKnapsack.cap_uncapped _ hvR hαR i hit]
    simp only [capLine, if_neg hi, affineValue]
    push_cast
    ring

theorem prefixLine_real {n : ℕ} (v : Fin n → ℚ) {α K a b : ℚ}
    (hv : ∀ i, 0 < v i) (hα : 0 < α)
    (hcross : ∀ i, α * v i ≤ a ∨ b ≤ α * v i)
    {t : ℝ} (ht : (a : ℝ) ≤ t ∧ t ≤ (b : ℝ)) (P : Finset (Fin n)) :
    FixedSupportKnapsack.budget (fun j => (v j : ℝ)) (K : ℝ) t -
      (∑ i ∈ P, FixedSupportKnapsack.cap (fun j => (v j : ℝ)) (α : ℝ) t i) =
      affineValue (((prefixLine v α K a P).1 : ℝ), ((prefixLine v α K a P).2 : ℝ)) t := by
  have hvR : ∀ j, (0 : ℝ) < v j := fun j => by exact_mod_cast hv j
  have hαR : (0 : ℝ) < α := by exact_mod_cast hα
  let C := P ∩ cappedAt v α a
  have hCP : C ⊆ P := Finset.inter_subset_left
  have hC : ∀ i ∈ C, (α : ℝ) * v i ≤ t := by
    intro i hi
    have hh : α * v i ≤ a := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
    exact (by exact_mod_cast hh : (α : ℝ) * v i ≤ (a : ℝ)).trans ht.1
  have hU : ∀ i ∈ P \ C, t ≤ (α : ℝ) * v i := by
    intro i hi
    have hn : ¬α * v i ≤ a := by
      intro hh
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp hi).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩)
    exact ht.2.trans (by exact_mod_cast (hcross i).resolve_left hn)
  rw [FixedSupportKnapsack.prefix_residual_affine _ hvR hαR P C hCP hC hU]
  have hd : P \ C = P \ cappedAt v α a := by
    ext i
    simp [C]
  have hcompl : Pᶜ = Finset.univ \ P := by ext i; simp
  simp only [prefixLine, prefixDenominator, affineValue, hd, hcompl]
  dsimp [C]
  push_cast
  ring

/-- Every finite-prefix affine residual root in the global domain is explicitly
included in the executable candidate set. -/
theorem prefixRoot_mem_scaleSamples {n : ℕ} (r v : Fin n → ℚ) (α K ρ : ℚ)
    {a : ℚ} (ha : a ∈ capCuts v α (scaleUpper v K)) {k : ℕ} (hk : k ≤ n)
    (hr : 0 ≤ prefixRoot v α K a ((scoreOrder r v ρ).take k).toFinset ∧
      prefixRoot v α K a ((scoreOrder r v ρ).take k).toFinset ≤ scaleUpper v K) :
    prefixRoot v α K a ((scoreOrder r v ρ).take k).toFinset ∈ scaleSamples r v α K ρ := by
  apply Finset.mem_union_right
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_image.mpr ⟨(a, k), Finset.mem_product.mpr ⟨ha, Finset.mem_range.mpr (by omega)⟩, rfl⟩, hr⟩

end BalancedAssortments.FixedSupportAlgorithm
