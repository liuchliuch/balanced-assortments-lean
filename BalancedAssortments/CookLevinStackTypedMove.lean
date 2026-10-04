import BalancedAssortments.CookLevinStackTypedAddresses
import BalancedAssortments.CookLevinStepSemantics

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF NPMachine ComplexityTimeBinary

theorem move_target_holds (M : Machine) (W T : ℕ) (σ : Assignment) (e f)
    (hd : Dimensions M W T e) (hf : (f 13).length=W)
    (t : Fin T) (p : Fin W) (ht : value (e 5)=t.val) (hp : value (e 6)=p.val) (m : Move) :
    cholds σ (Typed.cloop 8 13 (Typed.moveTarget m)) e f ↔
      formulaEval σ (headTarget M t p m)=true := by
  rw [cholds_cloop,hf]
  simp only [headTarget,formulaEval_cons,formulaEval_nil,Bool.and_true,clauseEval_eq_true_iff,
    List.mem_map,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
  have htarget : (∃ l,(∃ k : Fin W,(k.val : ℤ)=(p.val : ℤ)+m.displacement ∧
      pos (Var.head t.succ k : TVar M W T)=l) ∧ literalEval σ l=true) ↔
      ∃ k : Fin W,(k.val : ℤ)=(p.val : ℤ)+m.displacement ∧ σ (index (Var.head t.succ k : TVar M W T))=true := by
    constructor
    · rintro ⟨l,⟨k,hk,rfl⟩,hl⟩;exact ⟨k,hk,hl⟩
    · rintro ⟨k,hk,hl⟩;exact ⟨_,⟨k,hk,rfl⟩,hl⟩
  rw [htarget]
  apply exists_congr
  intro k
  cases m <;> simp [Typed.moveTarget,Function.update,StackCount.counterBits_value,hd.states,
    hd.time,hd.width,ht,hp,index_head,Move.displacement]
  all_goals omega
end BalancedAssortments.CookLevin.StackTableau
