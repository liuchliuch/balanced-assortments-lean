import BalancedAssortments.Counterexample
import BalancedAssortments.SalesIntegration

/-! Exact adapter from the independently proved appendix certificate to the
shared finite-vector compact MNL model. -/
noncomputable section
namespace BalancedAssortments.Counterexample

def attractions : Fin 3 → ℝ := ![3,2,14]
def prices : Fin 3 → ℝ := ![65,80,64]
def vector (a b c : ℝ) : Fin 3 → ℝ := ![a,b,c]

lemma feasible_iff_shared (a b c : ℝ) :
    Feasible a b c ↔ Sales.CompactFeasible attractions (vector a b c) 2 ∧
      Sales.Balanced (1/6) (vector a b c) := by
  simp only [Sales.CompactFeasible, Sales.Balanced, attractions, vector,
    Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.forall_fin_zero, add_zero, Nat.cast_ofNat]
  unfold Feasible
  constructor
  · rintro ⟨ha,hb,hc,hac,hbc,hcc,hr,hab,hbb,hcb⟩
    refine ⟨⟨⟨⟨ha,hac⟩,⟨hb,hbc⟩,⟨hc,hcc⟩,trivial⟩, ?_⟩, ?_⟩
    · linarith
    · constructor
      · rcases hab with he | ⟨h1,h2⟩
        · exact Or.inl he
        · right; constructor
          · linarith
          · constructor
            · linarith
            · constructor <;> try linarith
              trivial
      · constructor
        · rcases hbb with he | ⟨h1,h2⟩
          · exact Or.inl he
          · right; constructor
            · linarith
            · constructor
              · linarith
              · constructor <;> try linarith
                trivial
        · constructor
          · rcases hcb with he | ⟨h1,h2⟩
            · exact Or.inl he
            · right; constructor
              · linarith
              · constructor
                · linarith
                · constructor <;> try linarith
                  trivial
          · trivial
  · rintro ⟨⟨⟨⟨ha,hac⟩,⟨hb,hbc⟩,⟨hc,hcc⟩,_⟩,hr⟩,hab,hbb,hcb,_⟩
    refine ⟨ha,hb,hc,hac,hbc,hcc,?_,?_,?_,?_⟩
    · linarith
    · rcases hab with he | ⟨_,h1,h2,_⟩
      · exact Or.inl he
      · right; constructor <;> linarith
    · rcases hbb with he | ⟨h1,_,h2,_⟩
      · exact Or.inl he
      · right; constructor <;> linarith
    · rcases hcb with he | ⟨h1,h2,_,_⟩
      · exact Or.inl he
      · right; constructor <;> linarith

lemma objective_shared (a b c : ℝ) :
    Sales.objective prices (vector a b c) = revenue a b c := by
  simp [Sales.objective, prices, vector, revenue, Fin.sum_univ_succ]
  ring

/-- The appendix optimum is optimal in the same compact model used throughout
the project, with the same exact source constants. -/
theorem shared_global_optimum (w : Fin 3 → ℝ)
    (hc : Sales.CompactFeasible attractions w 2) (hb : Sales.Balanced (1/6) w) :
    Sales.objective prices w ≤ 928/15 := by
  have hw : vector (w 0) (w 1) (w 2) = w := by
    funext i
    fin_cases i <;> rfl
  rw [← hw] at hc hb ⊢
  rw [objective_shared]
  exact global_bound ((feasible_iff_shared _ _ _).2 ⟨hc,hb⟩)

theorem shared_unique_optimizer (w : Fin 3 → ℝ)
    (hc : Sales.CompactFeasible attractions w 2) (hb : Sales.Balanced (1/6) w)
    (he : Sales.objective prices w = 928/15) : w = vector 0 2 12 := by
  have hw : vector (w 0) (w 1) (w 2) = w := by
    funext i
    fin_cases i <;> rfl
  rw [← hw] at hc hb he
  rw [objective_shared] at he
  obtain ⟨h0,h1,h2⟩ := unique_optimizer ((feasible_iff_shared _ _ _).2 ⟨hc,hb⟩) he
  rw [← hw,h0,h1,h2]

/-- The exact appendix bound also holds for arbitrary policies in the original
MNL model, using the proved compact-space correspondence. -/
theorem original_policy_bound {A : Type*} [Fintype A]
    (S : A → Finset (Fin 3)) (q : A → ℝ) (hq : Sales.Distribution q)
    (hK : ∀ a, (S a).card ≤ 2) (hb : Sales.Balanced (1/6) (Sales.sales attractions S q)) :
    Sales.revenue prices (Sales.sales attractions S q) ≤ 928/15 := by
  have hv : ∀ i, 0 < attractions i := by intro i; fin_cases i <;> norm_num [attractions]
  obtain ⟨w,hc,hs⟩ := Sales.policy_to_compact attractions hv S hq 2 hK
  rw [hs] at hb ⊢
  rw [Sales.compact_revenue]
  apply shared_global_optimum w hc
  exact (Sales.compact_balance (1/6) w (fun i => (hc.1 i).1)).1 hb

end BalancedAssortments.Counterexample
