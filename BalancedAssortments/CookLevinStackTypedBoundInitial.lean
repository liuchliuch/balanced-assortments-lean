import BalancedAssortments.CookLevinStackTypedBoundFamilies

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF NPMachine ComplexityTimeBinary

lemma initial_bounded (M : Machine) (word : List Bool) (T : ℕ) :
    fbounded (tableauVariableCount M word.length T) (Typed.initial M)
      (StackInitialize.scalarEnv M word T) (StackInitialize.specStore M word T) := by
  let e := StackInitialize.scalarEnv M word T
  let f := StackInitialize.specStore M word T
  have hd := dimensions_scalar M word T
  change fbounded (V M (windowWidth word T) T) (Typed.initial M) e f
  simp only [Typed.initial,fbounded_all,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp only [fbounded_typed_clause,List.mem_singleton,forall_eq]
    exact state_bound hd _ _ (by simp) (by simpa using M.start.isLt)
  · simp only [fbounded_typed_clause,List.mem_singleton,forall_eq]
    apply head_bound hd
    · simp
    · simp only [denote_x,hd.time];unfold windowWidth;omega
  · rw [fbounded_loop]
    intro p
    simp only [fbounded_typed_clause,List.mem_singleton,forall_eq]
    apply tape_bound (hd.update 6 (by decide) _)
    · simp
    · have hp : p.val<T := by simpa [f] using p.isLt
      simp only [updated_counter];unfold windowWidth;omega
    · simp
  · rw [fbounded_each]
    intro p
    have hp : p.val<word.length := by simpa [f] using p.isLt
    split
    all_goals simp only [fbounded_typed_clause,List.mem_singleton,forall_eq]
    all_goals apply tape_bound (hd.update 8 (by decide) _)
    all_goals simp [Function.update,StackInitialize.scalarEnv_eq,StackCount.counterBits_value,windowWidth,e]
    all_goals omega
  · rw [fbounded_loop]
    intro p
    have hp : p.val<T+1 := by simpa [f] using p.isLt
    simp only [fbounded_typed_clause,List.mem_singleton,forall_eq]
    apply tape_bound (hd.update 6 (by decide) _)
    · simp
    · simp [Function.update,StackInitialize.scalarEnv_eq,StackCount.counterBits_value,windowWidth,e]
      omega
    · simp

lemma final_accept_bounded (M : Machine) (word : List Bool) (T : ℕ) :
    fbounded (tableauVariableCount M word.length T) (Typed.clause (Typed.accepting M (x 3)))
      (StackInitialize.scalarEnv M word T) (StackInitialize.specStore M word T) := by
  rw [fbounded_typed_clause]
  exact accepting_bounded (dimensions_scalar M word T) _ (by simp only [denote_x,(dimensions_scalar M word T).time];omega)
end BalancedAssortments.CookLevin.StackTableau
