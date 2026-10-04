import BalancedAssortments.CookLevinStackTypedMove

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF NPMachine ComplexityTimeBinary

theorem rule_body_holds (M : Machine) (W T : ℕ) (σ : Assignment) (e f)
    (hd : Dimensions M W T e) (hf : (f 13).length=W)
    (t : Fin T) (ht : value (e 5)=t.val) (j : Fin M.rules.length)
    (r : Rule M.stateExtra M.symbolExtra) :
    fholds σ (Typed.ruleBody M j.val r) e f ↔
      formulaEval σ (guard (Var.choice t j.succ : TVar M W T) (CookLevin.ruleBody M (W := W) t r))=true := by
  have hm (p : Fin W) :
      cholds σ (Typed.cloop 8 13 (Typed.moveTarget r.move))
        (Function.update e 6 (StackCount.counterBits p.val)) f ↔
      formulaEval σ (headTarget M t p r.move)=true :=
    move_target_holds M W T σ _ f (hd.update 6 (by decide) _) hf t p
      (by simpa [Function.update] using ht) (by simp [StackCount.counterBits_value]) r.move
  simp only [eval_guard,CookLevin.ruleBody,formulaEval_append,Bool.and_eq_true,
    eval_force,eval_allFin,eval_guard,eval_guardLiteral,eval_copyFamily,eval_neg]
  simp [-cholds_cloop,Typed.ruleBody,Typed.all,Typed.dynamicClause,Function.update,
    StackCount.counterBits_value,hd.states,hd.symbols,hd.width,hd.time,hd.rules,ht,
    index_choice,index_state,index_head,index_tape]
  rw [hf]
  simp_rw [hm]
  cases hg : σ ((T+1)*(M.stateExtra+1)+(T+1)*W+((T+1)*(W*(M.symbolExtra+3))+(j.val+1+(M.rules.length+1)*t.val))) <;>
    simp only [hg,Bool.false_eq_true,Bool.true_eq_false,false_or,true_or,false_implies,true_implies,
      true_and,and_true,implies_true,or_true,or_false,forall_const]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply and_congr
  · apply forall_congr'
    intro p
    cases hh : σ ((T+1)*(M.stateExtra+1)+(p.val+W*t.val)) <;> simp [hh]
  · apply forall_congr'
    intro p
    cases hh : σ ((T+1)*(M.stateExtra+1)+(p.val+W*t.val)) <;>
      simp [hh,Fin.forall_iff,imp_iff_not_or]
end BalancedAssortments.CookLevin.StackTableau
