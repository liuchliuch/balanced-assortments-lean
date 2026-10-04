import BalancedAssortments.NPSATStackGadgetComplete
import BalancedAssortments.NPSATStackFresh
import BalancedAssortments.NPSATStackOutputBounds
import BalancedAssortments.NPCNFStackReductionBounds

noncomputable section
namespace BalancedAssortments.NPSATStackGadget
open NPStack NPCNF NPCNF.Encoding NPStackFields

lemma slack_total_bound (N : ℕ) : NPSATStackSlack.totalBudget N≤50000*(N+2)^3 := by
  unfold NPSATStackSlack.totalBudget NPSATStackSlack.slackBudget NPSATStackSlack.itemBudget NPSATStackSlack.emitBudget
  nlinarith [Nat.zero_le (N^2),Nat.zero_le (N^3)]

lemma completed_budget_bound (labels : List (List Bool)) (F : BitFormula) (fr : List Bool) (L : ℕ)
    (hn : labels.length≤L) (hm : F.length≤L) (hq : fr.length≤L)
    (hw : ∀q∈labels,q.length≤L)
    (hcat : (dataFields labels).length≤2*L) (hform : (dataFields (formulaFields F)).length≤2*L)
    (hF : ∀c∈F,c.length≤3) (hf : ∀c∈F,∀l∈c,l.labelBits.length≤L) :
    completedBudget labels F fr L≤20000000*(L+1)^3+2*NPSATSubsetSum.fixedYes.length+100 := by
  have hv:=NPSATStackBounds.variables_budget_bound labels F labels L hn hm hn hw hcat hform hF hf
  have ht:=NPSATStackFresh.tokens_budget_bound labels F fr L hn hm hq hcat hform hF hf
  have ho:=NPSATStackOutputBounds.variable_output_polynomial labels F L hn hm
  have hs:=NPSATStackSlack.buildBudget_bound labels.length F.length
  have hb:=slack_total_bound (labels.length+F.length)
  have hh:=Nat.pow_le_pow_left (show labels.length+F.length+2≤2*(L+1) by omega) 3
  have hsb : NPSATStackSlack.totalBudget (labels.length+F.length)≤400000*(L+1)^3 := by
    calc
      _ ≤ 50000*(labels.length+F.length+2)^3 := hb
      _ ≤ 50000*(2*(L+1))^3 := Nat.mul_le_mul_left _ hh
      _ = _ := by ring
  have hsq : (L+1)^2≤(L+1)^3 := by nlinarith [Nat.zero_le (L^2),Nat.zero_le (L^3)]
  have hlin : L≤(L+1)^3 := by nlinarith [Nat.zero_le (L^2),Nat.zero_le (L^3)]
  unfold completedBudget buildBudget
  nlinarith

def completedPolynomial : Polynomial ℕ := 20000000*(Polynomial.X+2)^3+2*Polynomial.C NPSATSubsetSum.fixedYes.length+100

/-- The composed operational generator is bounded solely by the original raw
CNF wire length. All size, fresh-query, token and output bounds are derived. -/
theorem completed_budget_original (raw : Raw) (hF : ∀c∈raw.formula,c.length≤3) :
    completedBudget raw.catalog.reverse raw.formula (StackValidate.freshBits raw.catalog) ((encode raw).length+1)≤
      completedPolynomial.eval (encode raw).length := by
  let N := (encode raw).length
  have hm : rawMeasure raw≤N := parsed_rawMeasure_bound (parse_encode raw)
  have hn : raw.catalog.reverse.length≤N+1 := by have h:=(rawMeasure_counts raw).1;simp only [List.length_reverse];omega
  have hc : raw.formula.length≤N+1 := by have h:=(rawMeasure_counts raw).2.1;omega
  have hq : (StackValidate.freshBits raw.catalog).length≤N+1 := StackReduction.fresh_original_bound raw
  have hcat : (dataFields raw.catalog.reverse).length≤2*(N+1) := by
    rw [StackReduction.dataFields_reverse_length]
    have h:=(StackReduction.original_parts_bound raw).1
    omega
  have hform : (dataFields (formulaFields raw.formula)).length≤2*(N+1) := by
    have h:=(StackReduction.original_parts_bound raw).2
    change (dataFields (formulaFields raw.formula)).length≤N at h
    omega
  have hw : ∀q∈raw.catalog.reverse,q.length≤N+1 := by
    intro q hq
    have h:=(rawMeasure_widths raw).1 q (List.mem_reverse.mp hq)
    omega
  have hf : ∀c∈raw.formula,∀l∈c,l.labelBits.length≤N+1 := by
    intro c hc l hl
    have h:=(rawMeasure_widths raw).2 c hc l hl
    omega
  have h:=completed_budget_bound raw.catalog.reverse raw.formula (StackValidate.freshBits raw.catalog) (N+1)
    hn hc hq hw hcat hform hF hf
  simpa [completedPolynomial,N,Nat.add_assoc] using h

end BalancedAssortments.NPSATStackGadget
