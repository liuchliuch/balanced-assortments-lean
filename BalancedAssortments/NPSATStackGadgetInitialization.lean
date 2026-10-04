import BalancedAssortments.NPSATStackGadgetComplete

namespace BalancedAssortments.NPSATStackGadget
open NPCNF.Encoding NPStackFields

lemma startStore_fields (labels : List (List Bool)) (F : BitFormula) (fr : List Bool) :
    Function.update
      (Function.update (Function.update (fun _ : Reg=>[]) catalog (dataFields labels))
        formula (dataFields (formulaFields F))) fresh fr=startStore labels F fr := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · cases k <;> simp [catalog,formula,fresh,NPSATStackVariableTokens.catalog,NPSATStackVariableTokens.formula,
            NPSATStackVariableTokens.fresh,NPSATStackVariableTokens.itemMap,startStore,combined,
            NPSATStackVariableTokens.store,NPSATStackItem.store,Function.update]
        · cases k <;> simp [catalog,formula,fresh,NPSATStackVariableTokens.catalog,NPSATStackVariableTokens.formula,
            NPSATStackVariableTokens.fresh,NPSATStackVariableTokens.itemMap,startStore,combined,
            NPSATStackVariableTokens.store,NPSATStackItem.store,Function.update]
      · cases k;simp [catalog,formula,fresh,NPSATStackVariableTokens.catalog,NPSATStackVariableTokens.formula,
          NPSATStackVariableTokens.fresh,NPSATStackVariableTokens.itemMap,startStore,combined,NPSATStackVariableTokens.store,Function.update]
    · cases k;simp [catalog,formula,fresh,NPSATStackVariableTokens.catalog,NPSATStackVariableTokens.formula,
        NPSATStackVariableTokens.fresh,NPSATStackVariableTokens.itemMap,startStore,combined,NPSATStackVariableTokens.store,Function.update]
  · rcases k with k|k <;> cases k <;>
      simp [catalog,formula,fresh,startStore,combined,NPSATStackSlack.store,Function.update]

end BalancedAssortments.NPSATStackGadget
