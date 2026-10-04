import BalancedAssortments.CookLevinStackTypedLower
import BalancedAssortments.CookLevinStackInitialize

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF NPMachine StackBuilder

def catalogPrefix (ls : List (List Bool)) : List (List Bool) := ls.flatMap (fun l => [[true],l])
lemma catalogPrefix_end (ls : List (List Bool)) : catalogPrefix ls++[[false]]=Encoding.catalogFields ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [catalogPrefix,Encoding.catalogFields,List.append_assoc,← ih]

def raw (M : Machine) (word : List Bool) (T : ℕ) : Encoding.Raw where
  catalog := ((List.range (tableauVariableCount M word.length T)).reverse).map StackCount.counterBits
  formula := (Typed.formula M).eval (StackInitialize.scalarEnv M word T) (StackInitialize.specStore M word T)

theorem program_raw (M : Machine) (word : List Bool) (T : ℕ) :
    value (program M) (StackInitialize.scalarEnv M word T) (StackInitialize.specStore M word T)=
      Encoding.encode (raw M word T) := by
  rw [value_fields]
  apply congrArg Encoding.encodeFields
  simp only [program,fields,loop]
  rw [← Typed.formula_lower,FormulaCode.fields_lower]
  rw [StackInitialize.specStore_variables]
  rw [loopFields_replicate]
  simp [x,BitExpr.run,Encoding.fields,raw,← catalogPrefix_end,← formulaPrefix_formula,
    catalogPrefix,List.flatMap_map,Function.comp_def,List.append_assoc,
    tableauVariableCount,windowWidth]
  rw [← List.map_reverse,List.flatMap_map]

end BalancedAssortments.CookLevin.StackTableau
