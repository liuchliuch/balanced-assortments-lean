import BalancedAssortments.CookLevinStackTypedBoundTransitions
import BalancedAssortments.CookLevinStackTypedBoundInitial

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF NPMachine ComplexityTimeBinary

lemma formula_bounded (M : Machine) (word : List Bool) (T : ℕ) :
    fbounded (tableauVariableCount M word.length T) (Typed.formula M)
      (StackInitialize.scalarEnv M word T) (StackInitialize.specStore M word T) := by
  simp only [Typed.formula,fbounded_all,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨shape_bounded M word T,initial_bounded M word T,final_accept_bounded M word T,transitions_bounded M word T⟩

@[simp] lemma raw_catalog (M : Machine) (word : List Bool) (T : ℕ) :
    (raw M word T).decode.catalog=(List.range (tableauVariableCount M word.length T)).reverse := by
  simp [raw,Encoding.Raw.decode,List.map_map,Function.comp_def,StackCount.counterBits_value]

/-- Every emitted label belongs to the explicit, duplicate-free full interval
catalogue. This is unconditional syntactic legality, independent of whether
an accepting assignment exists. -/
theorem raw_valid (M : Machine) (word : List Bool) (T : ℕ) : (raw M word T).decode.Valid := by
  constructor
  · rw [raw_catalog]
    simpa using (List.nodup_reverse.mpr (List.nodup_range (n := tableauVariableCount M word.length T)))
  · intro c hc l hl
    change c∈((Typed.formula M).eval (StackInitialize.scalarEnv M word T) (StackInitialize.specStore M word T)).map (List.map Encoding.BitLiteral.decode) at hc
    obtain ⟨bc,hbc,rfl⟩ := List.mem_map.mp hc
    obtain ⟨bl,hbl,rfl⟩ := List.mem_map.mp hl
    rw [raw_catalog,List.mem_reverse,List.mem_range]
    exact formula_bounded M word T bc hbc bl hbl

end BalancedAssortments.CookLevin.StackTableau
