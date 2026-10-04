import BalancedAssortments.CookLevinStackTypedRule
import BalancedAssortments.CookLevinStackTypedHalt

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF NPMachine ComplexityTimeBinary

lemma forall_zipIdx {α : Type*} (ls : List α) (P : α → ℕ → Prop) :
    (∀ q∈ls.zipIdx,P q.1 q.2) ↔ ∀ j : Fin ls.length,P ls[j.val] j.val := by
  constructor
  · intro h j
    apply h (ls[j.val],j.val)
    rw [List.mk_mem_zipIdx_iff_getElem?]
    simp [List.getElem?_eq_getElem j.isLt]
  · intro h q hq
    obtain ⟨hj,he⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hq)
    simpa [he] using h ⟨q.2,hj⟩

theorem transition_row_holds (M : Machine) (W T : ℕ) (σ : Assignment) (e f)
    (hd : Dimensions M W T e) (hf : (f 13).length=W)
    (t : Fin T) (ht : value (e 5)=t.val) :
    fholds σ (.seq (Typed.haltBody M) (Typed.all (M.rules.zipIdx.map (fun r => Typed.ruleBody M r.2 r.1)))) e f ↔
      ∀ r : Fin (M.rules.length+1),formulaEval σ (guard (Var.choice t r : TVar M W T) (choiceBody M (W := W) t r))=true := by
  rw [fholds_seq,fholds_all,Fin.forall_fin_succ]
  simp only [List.forall_mem_map,choiceBody,Fin.cases_zero,Fin.cases_succ]
  rw [forall_zipIdx M.rules (fun r j => fholds σ (Typed.ruleBody M j r) e f)]
  apply and_congr
  · exact halt_body_holds M W T σ e f hd hf t ht
  · apply forall_congr'
    intro j
    exact rule_body_holds M W T σ e f hd hf t ht j M.rules[j.val]

theorem transitions_holds (M : Machine) (word : List Bool) (T : ℕ) (σ : Assignment) :
    fholds σ (Typed.transitions M) (StackInitialize.scalarEnv M word T) (StackInitialize.specStore M word T) ↔
      formulaEval σ (transitionFormula M (windowWidth word T) T)=true := by
  rw [Typed.transitions,fholds_loop]
  have h11 : (StackInitialize.specStore M word T 11).length=T := by simp
  rw [h11]
  simp only [transitionFormula,eval_allFin]
  apply forall_congr'
  intro t
  exact transition_row_holds M (windowWidth word T) T σ _ _
    ((dimensions_scalar M word T).update 5 (by decide) _) (by simp)
    t (by simp [StackCount.counterBits_value])
end BalancedAssortments.CookLevin.StackTableau
