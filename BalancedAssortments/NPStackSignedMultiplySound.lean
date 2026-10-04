import BalancedAssortments.NPStackSignedMultiplyBound

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary ComplexityTimeVerifier

private lemma rename_no_choice {K Q K' Q' : Type*} (i : Instr K Q)
    (h : ∀ a b,i≠.choice a b) (fk : K→K') (fq : Q→Q') (a b : Q') :
    i.rename fk fq≠.choice a b := by
  cases i <;> simp [Instr.rename]
  rename_i q r
  exact False.elim (h q r rfl)

lemma signedMultiply_noChoice : NoChoice signedMultiplyProgram := by
  intro q a b
  cases q with
  | copy c q => cases c <;> cases q <;> simp [signedMultiplyProgram,copyProgram,Instr.rename]
  | multiply p q =>
    cases q <;> first
      | (simp only [signedMultiplyProgram]; exact rename_no_choice _ (multiply_noChoice _) _ _ a b)
      | simp [signedMultiplyProgram]
  | add q => exact rename_no_choice _ (signedAdd_noChoice q) _ _ a b

/-- Every halting execution has the proved signed output; arbitrary extra
clock time cannot conceal another result. -/
theorem signedMultiply_accepting_result (x y : ZBits) {t : ℕ} {c : Config SignedMulStack SignedMulState}
    (hr : Run signedMultiplyProgram t ⟨.copy false .readSource,signedMulInitial x y⟩ c)
    (ha : accepts signedMultiplyProgram c) :
    t≤signedMultiplyBudget x y ∧ c=⟨.add (.negative .done),signedMulFinal y (zmul x y).1⟩ := by
  obtain ⟨s,hs,hknown⟩ := signedMultiply_run x y
  have he := hr.halted_unique (noChoice_deterministic signedMultiply_noChoice) hknown ha rfl
  exact ⟨he.1 ▸ hs,he.2⟩

end BalancedAssortments.NPStack
