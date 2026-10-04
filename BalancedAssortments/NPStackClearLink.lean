import BalancedAssortments.NPStackEmbeddingDeterministic

namespace BalancedAssortments.NPStack
variable {K Q : Type*} [DecidableEq K]

/-- A concrete pop loop clears one stack and leaves every other stack intact.
The empty test is itself a real transition to the supplied continuation. -/
theorem clear_linked {P : Program K Q} (k : K) (q next : Q)
    (hcode : P.code q=.pop k next q q) (store : K→List Bool) :
    Run P ((store k).length+1) ⟨q,store⟩ ⟨next,Function.update store k []⟩ := by
  generalize hs : store k=bits
  induction bits generalizing store with
  | nil =>
    apply Run.one
    simp [Step,successors,hcode,hs]
  | cons b bs ih =>
    have hh : Step P ⟨q,store⟩ ⟨q,Function.update store k bs⟩ := by
      cases b <;> simp [Step,successors,hcode,hs]
    have ht := ih (Function.update store k bs) (by simp)
    have hr := Run.succ hh ht
    simpa only [List.length_cons,Function.update_idem] using hr

end BalancedAssortments.NPStack
