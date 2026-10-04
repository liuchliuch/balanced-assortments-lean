import BalancedAssortments.NPSATStackTokens
import BalancedAssortments.NPSATStackBounds

namespace BalancedAssortments.NPSATStackFresh
open NPCNF NPCNF.Encoding ComplexityTimeBinary NPStackFields

lemma fresh_catalog (raw : Raw) :
    ∀label∈raw.catalog,value (NPCNF.StackValidate.freshBits raw.catalog)≠value label := by
  intro label hl
  have hm := label_le_max (List.mem_map.mpr ⟨label,hl,rfl⟩ : value label∈raw.catalog.map value)
  rw [NPCNF.StackValidate.freshBits_value]
  omega

lemma fresh_formula (raw : Raw) (hv : raw.decode.Valid) :
    ∀c∈raw.formula,∀l∈c,value (NPCNF.StackValidate.freshBits raw.catalog)≠value l.labelBits := by
  intro c hc l hl
  have hm := hv.2 (c.map BitLiteral.decode) (List.mem_map.mpr ⟨c,hc,rfl⟩)
    l.decode (List.mem_map.mpr ⟨l,hl,rfl⟩)
  change value l.labelBits∈raw.catalog.map value at hm
  have hb := label_le_max hm
  rw [NPCNF.StackValidate.freshBits_value]
  omega

lemma tokens_budget_bound (catalog : List (List Bool)) (F : BitFormula) (query : List Bool) (L : ℕ)
    (hn : catalog.length≤L) (hm : F.length≤L) (hq : query.length≤L)
    (hcat : (dataFields catalog).length≤2*L) (hform : (dataFields (formulaFields F)).length≤2*L)
    (hF : ∀c∈F,c.length≤3) (hw : ∀c∈F,∀l∈c,l.labelBits.length≤L) :
    NPSATStackItem.tokensBudget catalog F query L≤1000*(L+1)^2 := by
  have hf := NPSATStackBounds.formula_budget_bound query F L hq hm hF hw
  have hv := Nat.mul_le_mul (Nat.add_le_add_right hn 1)
    (show query.length+L+1≤2*(L+1) by omega)
  unfold NPSATStackItem.tokensBudget
  nlinarith

/-- The prepared fresh query generates actual variable/clause token stacks
while retaining every source field and the accumulated output. -/
theorem raw_tokens_exec (raw : Raw) (out : List Bool) (hv : raw.decode.Valid)
    (hF : ∀c∈raw.formula,c.length≤3) :
    ∃t ≤ NPSATStackItem.tokensBudget raw.catalog.reverse raw.formula
        (NPCNF.StackValidate.freshBits raw.catalog) (rawMeasure raw),
      NPStack.Structured.Exec NPSATStackItem.tokens
        (NPSATStackItem.store (dataFields raw.catalog.reverse) (dataFields (formulaFields raw.formula))
          (NPCNF.StackValidate.freshBits raw.catalog) [] [] [] [] out)
        (NPSATStackItem.store (dataFields raw.catalog.reverse) (dataFields (formulaFields raw.formula))
          (NPCNF.StackValidate.freshBits raw.catalog) (List.replicate raw.catalog.length false)
          (List.replicate raw.formula.length false) [] [] out) t := by
  have hc : ∀label∈raw.catalog.reverse,label.length≤rawMeasure raw := by
    simpa using (rawMeasure_widths raw).1
  have hf : ∀label∈raw.catalog.reverse,value (NPCNF.StackValidate.freshBits raw.catalog)≠value label := by
    simpa using fresh_catalog raw
  obtain ⟨t,ht,hr⟩ := NPSATStackItem.tokens_exec raw.catalog.reverse raw.formula
    (NPCNF.StackValidate.freshBits raw.catalog) out (rawMeasure raw) hc hF hf (fresh_formula raw hv)
  exact ⟨t,ht,by simpa using hr⟩

end BalancedAssortments.NPSATStackFresh
