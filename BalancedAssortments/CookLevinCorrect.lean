import BalancedAssortments.CookLevinStepSemantics

/-! Exact bounded nondeterministic machine acceptance and satisfiability of the
explicit global-choice CNF tableau. Complexity of serialization is separate. -/
noncomputable section
namespace BalancedAssortments.CookLevin
open NPCNF NPMachine

def tableauValuation {M : Machine} {W T : ℕ}
    (f : Fin (T+1) → WindowConfig M W) (choices : Fin T → Fin (M.rules.length+1)) :
    TVar M W T → Bool
  | .state t s => decide ((f t).state=s)
  | .head t p => decide ((f t).head=p)
  | .tape t p a => decide ((f t).tape p=a)
  | .choice t r => decide (choices t=r)

def tableauAssignment {M : Machine} {W T : ℕ}
    (f : Fin (T+1) → WindowConfig M W) (choices : Fin T → Fin (M.rules.length+1)) : Assignment :=
  extendAssignment (tableauValuation f choices)

lemma tableauAssignment_shape {M : Machine} {W T : ℕ}
    (f : Fin (T+1) → WindowConfig M W) (choices : Fin T → Fin (M.rules.length+1)) :
    ShapeHolds M W T (tableauAssignment f choices) := by
  constructor
  · intro t
    refine ⟨(f t).state,?_,?_⟩
    · simp [tableauAssignment,extendAssignment_apply,tableauValuation]
    · intro i hi
      have he : (f t).state=i := by simpa [tableauAssignment,extendAssignment_apply,tableauValuation] using hi
      exact he.symm
  · intro t
    refine ⟨(f t).head,?_,?_⟩
    · simp [tableauAssignment,extendAssignment_apply,tableauValuation]
    · intro i hi
      have he : (f t).head=i := by simpa [tableauAssignment,extendAssignment_apply,tableauValuation] using hi
      exact he.symm
  · intro t p
    refine ⟨(f t).tape p,?_,?_⟩
    · simp [tableauAssignment,extendAssignment_apply,tableauValuation]
    · intro i hi
      have he : (f t).tape p=i := by simpa [tableauAssignment,extendAssignment_apply,tableauValuation] using hi
      exact he.symm
  · intro t
    refine ⟨choices t,?_,?_⟩
    · simp [tableauAssignment,extendAssignment_apply,tableauValuation]
    · intro i hi
      have he : choices t=i := by simpa [tableauAssignment,extendAssignment_apply,tableauValuation] using hi
      exact he.symm

lemma decode_tableauAssignment {M : Machine} {W T : ℕ}
    (f : Fin (T+1) → WindowConfig M W) (choices : Fin T → Fin (M.rules.length+1))
    (t : Fin (T+1)) : decodeRow (tableauAssignment_shape f choices) t=f t := by
  apply WindowConfig.ext
  · exact (selected_unique ((tableauAssignment_shape f choices).states t) (f t).state
      (by simp [tableauAssignment,extendAssignment_apply,tableauValuation])).symm
  · exact (selected_unique ((tableauAssignment_shape f choices).heads t) (f t).head
      (by simp [tableauAssignment,extendAssignment_apply,tableauValuation])).symm
  · funext p
    exact (selected_unique ((tableauAssignment_shape f choices).tapes t p) ((f t).tape p)
      (by simp [tableauAssignment,extendAssignment_apply,tableauValuation])).symm

lemma tableau_sat_iff_window (M : Machine) (word : List Bool) (T : ℕ) :
    Sat (tableauFormula M word T) ↔ AcceptingWindowTableau M word T := by
  constructor
  · rintro ⟨σ,hσ⟩
    simp only [tableauFormula,formulaEval_append,Bool.and_eq_true] at hσ
    let h := (eval_shape M (windowWidth word T) T σ).1 hσ.1
    exact ⟨decodeRow h,(eval_initial h _).1 hσ.2.1,
      eval_transitions_sound h hσ.2.2.2,(eval_accept h _).1 hσ.2.2.1⟩
  · rintro ⟨f,hinitial,hsteps,haccept⟩
    have hc : ∀ t : Fin T, ∃ r,ChoiceRealizes (f t.castSucc) (f t.succ) r :=
      fun t => (choiceRealizes_iff_step _ _).2 (hsteps t)
    choose choices hchoices using hc
    let h := tableauAssignment_shape f choices
    refine ⟨tableauAssignment f choices,?_⟩
    simp only [tableauFormula,formulaEval_append,Bool.and_eq_true]
    refine ⟨(eval_shape _ _ _ _).2 h,(eval_initial h _).2 ?_,(eval_accept h _).2 ?_,?_⟩
    · simpa only [h,decode_tableauAssignment] using hinitial
    · simpa only [h,decode_tableauAssignment] using haccept
    · simp only [transitionFormula,eval_allFin,eval_guard]
      intro t r hr
      have he : choices t=r := by
        simpa [tableauAssignment,extendAssignment_apply,tableauValuation] using hr
      apply (eval_choiceBody h t r).2
      simpa only [h,decode_tableauAssignment,← he] using hchoices t

/-- The generated CNF is satisfiable precisely for an accepting computation of
the concrete finite-state, finite-alphabet nondeterministic machine within T. -/
theorem tableau_satisfiable_iff_acceptsWithin (M : Machine) (word : List Bool) (T : ℕ) :
    Sat (tableauFormula M word T) ↔ AcceptsWithin M word T := by
  rw [tableau_sat_iff_window,← bounded_acceptance_iff_window_tableau]

end BalancedAssortments.CookLevin
