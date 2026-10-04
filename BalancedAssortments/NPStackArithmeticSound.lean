import BalancedAssortments.NPStackMultiplyCorrect
import BalancedAssortments.NPStackDeterministic

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary

lemma reverse_noChoice : NoChoice reverseProgram := by
  intro q a b
  cases q <;> simp [reverseProgram]
lemma copy_noChoice : NoChoice copyProgram := by
  intro q a b
  cases q <;> simp [copyProgram]
lemma add_noChoice : NoChoice addProgram := by
  intro q a b
  cases q <;> simp [addProgram]
lemma multiply_noChoice : NoChoice multiplyProgram := by
  intro q a b
  cases q with
  | initial q => cases q <;> simp [multiplyProgram,reverseProgram,Instr.rename]
  | read flag => simp [multiplyProgram]
  | shift flag bit => simp [multiplyProgram]
  | copy flag q => cases q <;> simp [multiplyProgram,copyProgram,Instr.rename]
  | add flag q => cases q <;> simp [multiplyProgram,addProgram,Instr.rename]
  | finalFirst flag q => cases q <;> simp [multiplyProgram,reverseProgram,Instr.rename]
  | finalSecond q => cases q <;> simp [multiplyProgram,reverseProgram,Instr.rename]
  | done => simp [multiplyProgram]

theorem add_halted_correct (xs ys : List Bool) (carry : Bool) {t : ℕ}
    {out : Config AddStack AddState} {b : Bool}
    (h : Run addProgram t (addConfig (.readX carry) xs ys [] []) out)
    (hh : addProgram.code out.pc=.halt b) :
    t=5*max xs.length ys.length+6 ∧ out=addConfig .done [] [] [] (addCarry xs ys carry).1 :=
  h.halted_unique (noChoice_deterministic add_noChoice) (add_run xs ys carry) hh rfl

theorem copy_halted_correct (xs ys : List Bool) {t : ℕ}
    {out : Config CopyStack CopyState} {b : Bool}
    (h : Run copyProgram t (copyConfig .readSource xs [] ys) out)
    (hh : copyProgram.code out.pc=.halt b) :
    t=5*xs.length+2 ∧ out=copyConfig .done xs [] (xs++ys) :=
  h.halted_unique (noChoice_deterministic copy_noChoice) (copy_run xs ys) hh rfl

/-- No alternative computation can accept a spurious product or exceed the
proved halting time: the entire arithmetic program is deterministic. -/
theorem multiplication_halted_correct (xs factor : List Bool) {t : ℕ}
    {out : Config MulStack MulState} {b : Bool}
    (h : Run multiplyProgram t (multiplicationInput xs factor) out)
    (hh : multiplyProgram.code out.pc=.halt b) :
    t ≤ multiplicationBudget xs.length factor.length ∧
      out=multiplicationOutput factor (mulBits xs factor).1 := by
  obtain ⟨t',ht,hr⟩ := multiplication_run xs factor
  have he := h.halted_unique (noChoice_deterministic multiply_noChoice) hr hh rfl
  exact ⟨he.1 ▸ ht,he.2⟩

end BalancedAssortments.NPStack
