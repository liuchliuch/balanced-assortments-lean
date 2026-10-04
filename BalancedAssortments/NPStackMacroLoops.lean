import BalancedAssortments.NPStackMacroDataRuns

namespace BalancedAssortments.NPStack.Macros
open NPStack
variable {K Q : Type*} [DecidableEq K]

lemma clear_loop (m : Q → Macro K Q) (start : Q) (input output : K)
    (phase done : Q) (r : K) (hm : m phase=.pop r done phase phase)
    (s : K → List Bool) :
    Run (compile m start input output) ((s r).length+1) ⟨.main phase,s⟩
      ⟨.main done,Function.update s r []⟩ := by
  generalize he : s r=xs
  induction xs generalizing s with
  | nil =>
    apply Run.one
    have hh : Function.update s r []=s := by rw [← he,Function.update_eq_self]
    simp [Step,successors,compile,code,hm,he,hh]
  | cons b bs ih =>
    have hs : Step (compile m start input output) ⟨.main phase,s⟩
        ⟨.main phase,Function.update s r bs⟩ := by
      cases b <;> simp [Step,successors,compile,code,hm,he]
    have ht := ih (Function.update s r bs) (by simp)
    have hh := Run.succ hs ht
    simpa using hh

end BalancedAssortments.NPStack.Macros
