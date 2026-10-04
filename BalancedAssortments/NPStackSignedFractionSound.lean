import BalancedAssortments.NPStackFractionCompareCorrect
import BalancedAssortments.NPStackArithmeticSound

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary ComplexityTimeVerifier
open ComplexityTimeFractions (Fraction decode Valid)

private lemma rename_ne_choice {K Q K' Q' : Type*} (i : Instr K Q) (fk : K→K') (fq : Q→Q')
    (h : ∀ a b,i≠.choice a b) (a b : Q') : i.rename fk fq≠.choice a b := by
  cases i <;> simp_all [Instr.rename]

theorem signedCompare_noChoice : NoChoice signedCompareProgram := by
  intro q a b
  cases q with
  | addLeft q =>
    cases q <;> try {simp only [signedCompareProgram]; exact rename_ne_choice _ _ _ (add_noChoice _) a b}
    simp [signedCompareProgram]
  | addRight q =>
    cases q <;> try {simp only [signedCompareProgram]; exact rename_ne_choice _ _ _ (add_noChoice _) a b}
    simp [signedCompareProgram]
  | compare q => exact rename_ne_choice _ _ _ (compare_noChoice q) a b

theorem fractionCompare_noChoice : NoChoice fractionCompareProgram := by
  intro q a b
  cases q with
  | multiply p q =>
    cases q <;> try {simp only [fractionCompareProgram]; exact rename_ne_choice _ _ _ (multiply_noChoice _) a b}
    simp [fractionCompareProgram]
  | compare q => exact rename_ne_choice _ _ _ (signedCompare_noChoice q) a b

theorem signedCompare_halted_correct (x y : ZBits) (zs : List Bool) {t : ℕ}
    {c : Config SignedCompareStack SignedCompareState} {b : Bool}
    (h : Run signedCompareProgram t
      (signedConfig (.addLeft (.readX false)) x.1 x.2 y.1 y.2 [] [] [] zs) c)
    (hc : signedCompareProgram.code c.pc=.halt b) :
    t=signedCompareTime x y ∧
      c=signedConfig (.compare .done) [] [] [] [] [] [] [] ((zle x y).1::zs) :=
  h.halted_unique (noChoice_deterministic signedCompare_noChoice) (signedCompare_run x y zs) hc rfl

/-- All halting executions of the composed fraction-comparison bytecode have
exactly the intended answer and obey the quadratic transition bound. -/
theorem fractionCompare_halted_correct (x y : Fraction) (zs : List Bool) {W t : ℕ}
    (hx : Valid x) (hy : Valid y)
    (hxw : ComplexityTimeFractions.width x≤W) (hyw : ComplexityTimeFractions.width y≤W)
    {c : Config FractionCompareStack FractionCompareState} {b : Bool}
    (h : Run fractionCompareProgram t
      ⟨.multiply .ap (.initial .read),fractionInitialStacks x y zs⟩ c)
    (hc : fractionCompareProgram.code c.pc=.halt b) :
    t≤120*W^2+140*W+51 ∧
      c=⟨.compare (.compare .done),fractionFinalStacks x y (decide (decode x≤decode y)::zs)⟩ := by
  obtain ⟨u,hu,hr⟩ := fractionCompare_run x y zs hx hy hxw hyw
  have hh := h.halted_unique (noChoice_deterministic fractionCompare_noChoice) hr hc rfl
  exact ⟨hh.1 ▸ hu,hh.2⟩

end BalancedAssortments.NPStack
