import BalancedAssortments.CookLevinStackTypedAddresses
import BalancedAssortments.CookLevinStackInitialPartition

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF NPMachine ComplexityTimeBinary

theorem accepting_holds (M : Machine) (σ : Assignment) (e f) (t : E) :
    fholds σ (Typed.clause (Typed.accepting M t)) e f ↔
      ∃ s : Fin (M.stateExtra+1),M.accepting s=true ∧ σ (denote e (state t (c s.val)))=true := by
  simp only [fholds_typed_clause,Typed.accepting,List.mem_map,List.mem_filter,List.mem_finRange,true_and]
  constructor
  · rintro ⟨l,⟨s,hs,rfl⟩,hl⟩;exact ⟨s,hs,by simpa using hl⟩
  · rintro ⟨s,hs,hl⟩;exact ⟨_,⟨s,hs,rfl⟩,by simpa using hl⟩

theorem final_accept_holds (M : Machine) (word : List Bool) (T : ℕ) (σ : Assignment) :
    fholds σ (Typed.clause (Typed.accepting M (x 3))) (StackInitialize.scalarEnv M word T) (StackInitialize.specStore M word T) ↔
      formulaEval σ (acceptFormula M (W := windowWidth word T) (Fin.last T))=true := by
  rw [accepting_holds,eval_accept_formula]
  simp only [denote_state,denote_c,denote_x,index_state,Fin.val_last]
  have hv := scalar_values M word T
  simp only [show value (StackInitialize.scalarEnv M word T 0)=M.stateExtra+1 from congrFun hv 0,
    show value (StackInitialize.scalarEnv M word T 3)=T from congrFun hv 3]

theorem initial_holds (M : Machine) (word : List Bool) (T : ℕ) (σ : Assignment) :
    fholds σ (Typed.initial M) (StackInitialize.scalarEnv M word T) (StackInitialize.specStore M word T) ↔
      formulaEval σ (initialFormula M (windowWidth word T) T (windowInitial M word T))=true := by
  have hpart := initial_partition M word T (fun p a =>
    σ (((T+1)*(M.stateExtra+1)+(T+1)*windowWidth word T)+(a+(M.symbolExtra+3)*p))=true)
  simp only [initialFormula,formulaEval_append,Bool.and_eq_true,eval_force,eval_allFin,
    index_state,index_head,index_tape,Fin.val_zero,Nat.mul_zero,Nat.add_zero,windowInitial]
  simp only [windowInitial] at hpart
  rw [hpart]
  simp [Typed.initial,Typed.all,fholds_each,StackInitialize.specStore_clock,
    StackInitialize.specStore_word,StackInitialize.specStore_rows,StackInitialize.scalarEnv_eq,
    Function.update,StackCount.counterBits_value,denote_state,denote_head,denote_tape,
    windowWidth,value]
  intro hs hh
  have h11 : (StackInitialize.specStore M word T 11).length=T := by simp
  have h12 : (StackInitialize.specStore M word T 12).length=T+1 := by simp
  have h9 : (StackInitialize.specStore M word T 9).length=word.length := by simp
  rw [h11,h12]
  apply and_congr Iff.rfl
  apply and_congr _ Iff.rfl
  apply forall_congr'
  intro j
  cases hb : word[j.val] <;> simp [hb,Function.update,StackCount.counterBits_value]

end BalancedAssortments.CookLevin.StackTableau
