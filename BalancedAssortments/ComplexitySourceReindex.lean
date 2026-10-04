import BalancedAssortments.Sales

namespace BalancedAssortments.Sales
variable {I J : Type*} [Fintype I] [Fintype J]

lemma objective_reindex (e : I ≃ J) (r w : J → ℝ) :
    objective (r ∘ e) (w ∘ e)=objective r w := by
  unfold objective
  simp only [Function.comp_def]
  rw [e.sum_comp (fun j => r j*w j),e.sum_comp w]

lemma balanced_reindex (e : I ≃ J) (alpha : ℝ) (w : J → ℝ) :
    Balanced alpha (w ∘ e) ↔ Balanced alpha w := by
  constructor
  · intro h j
    have hh := h (e.symm j)
    simp only [Function.comp_apply,Equiv.apply_symm_apply] at hh
    rcases hh with hz | hh
    · exact Or.inl hz
    · right; intro k; simpa using hh (e.symm k)
  · intro h i
    rcases h (e i) with hz | hh
    · exact Or.inl hz
    · exact Or.inr (fun j => hh (e j))

lemma compactFeasible_reindex (e : I ≃ J) (v w : J → ℝ) (K : ℕ) :
    CompactFeasible (v ∘ e) (w ∘ e) K ↔ CompactFeasible v w K := by
  unfold CompactFeasible
  simp only [Function.comp_def,e.sum_comp (fun j => w j/v j)]
  constructor
  · rintro ⟨h,hr⟩
    exact ⟨fun j => by simpa using h (e.symm j),hr⟩
  · rintro ⟨h,hr⟩
    exact ⟨fun i => h (e i),hr⟩

/-- A coordinate-renaming bridge for actual model instances, including the
fractional objective and disjunctive zero-or-balanced condition. -/
theorem decision_reindex (e : I ≃ J) (v r : J → ℝ) (alpha H : ℝ) (K : ℕ) :
    (∃ w : I → ℝ,CompactFeasible (v ∘ e) w K ∧ Balanced alpha w ∧ H≤objective (r ∘ e) w) ↔
    ∃ w : J → ℝ,CompactFeasible v w K ∧ Balanced alpha w ∧ H≤objective r w := by
  constructor
  · rintro ⟨w,hf,hb,hr⟩
    refine ⟨w ∘ e.symm,?_,?_,?_⟩
    · have hh := (compactFeasible_reindex e.symm (v ∘ e) w K).mpr hf
      simpa [Function.comp_def] using hh
    · exact (balanced_reindex e.symm alpha w).mpr hb
    · simpa [Function.comp_def] using hr.trans_eq (objective_reindex e.symm (r ∘ e) w).symm
  · rintro ⟨w,hf,hb,hr⟩
    exact ⟨w ∘ e,(compactFeasible_reindex e v w K).mpr hf,
      (balanced_reindex e alpha w).mpr hb,by simpa only [objective_reindex] using hr⟩

end BalancedAssortments.Sales
