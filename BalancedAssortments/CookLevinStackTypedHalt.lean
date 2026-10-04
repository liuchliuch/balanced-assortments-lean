import BalancedAssortments.CookLevinStackTypedInitial

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF NPMachine ComplexityTimeBinary

theorem halt_body_holds (M : Machine) (W T : ℕ) (σ : Assignment) (e f)
    (hd : Dimensions M W T e) (hf : (f 13).length=W)
    (t : Fin T) (ht : value (e 5)=t.val) :
    fholds σ (Typed.haltBody M) e f ↔
      formulaEval σ (guard (Var.choice t 0 : TVar M W T) (CookLevin.haltBody M (W := W) t))=true := by
  simp only [eval_guard,CookLevin.haltBody,formulaEval_append,Bool.and_eq_true,
    eval_accept_formula,eval_copyFamily,eval_allFin]
  simp [Typed.haltBody,Typed.all,Typed.accepting,Function.update,StackCount.counterBits_value,
    hd.states,hd.symbols,hd.width,hd.time,hd.rules,ht,
    index_choice,index_state,index_head,index_tape]
  rw [hf]
  cases hg : σ ((T+1)*(M.stateExtra+1)+(T+1)*W+((T+1)*(W*(M.symbolExtra+3))+(M.rules.length+1)*t.val)) <;>
    simp [hg,Fin.forall_iff,imp_iff_not_or]
end BalancedAssortments.CookLevin.StackTableau
