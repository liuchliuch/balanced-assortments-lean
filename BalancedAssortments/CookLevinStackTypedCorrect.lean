import BalancedAssortments.CookLevinStackTypedShape
import BalancedAssortments.CookLevinStackTypedTransitions
import BalancedAssortments.CookLevinStackTableauRaw
import BalancedAssortments.CookLevinCorrect

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF NPMachine

theorem formula_holds (M : Machine) (word : List Bool) (T : ℕ) (σ : Assignment) :
    fholds σ (Typed.formula M) (StackInitialize.scalarEnv M word T) (StackInitialize.specStore M word T) ↔
      formulaEval σ (tableauFormula M word T)=true := by
  simp only [Typed.formula,Typed.all,fholds_seq,fholds_empty,and_true,
    shape_holds,initial_holds,final_accept_holds,transitions_holds,
    tableauFormula,formulaEval_append,Bool.and_eq_true,eval_shape]

theorem raw_satisfiable_iff (M : Machine) (word : List Bool) (T : ℕ) :
    Sat (raw M word T).decode.formula ↔ AcceptsWithin M word T := by
  rw [← tableau_satisfiable_iff_acceptsWithin]
  unfold Sat
  apply exists_congr
  intro σ
  exact formula_holds M word T σ

end BalancedAssortments.CookLevin.StackTableau
