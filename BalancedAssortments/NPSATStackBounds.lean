import BalancedAssortments.NPSATStackVariables
import BalancedAssortments.NPCNFStackValidateBounds

namespace BalancedAssortments.NPSATStackBounds
open NPStackFields NPCNF.Encoding

lemma map_sum_le {α : Type*} (xs : List α) (f : α → ℕ) (B : ℕ) (h : ∀x∈xs,f x≤B) :
    (xs.map f).sum≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro y hy;exact h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

lemma clause_budget_bound (query : List Bool) (c : BitClause) (L : ℕ)
    (hq : query.length≤L) (hc : c.length≤3) (hw : ∀l∈c,l.labelBits.length≤L) :
    NPSATStackClauseDigits.budget query c≤700*(L+1) := by
  have hs := map_sum_le c (fun l=>l.labelBits.length) L hw
  have hmul := Nat.mul_le_mul_right L hc
  have hqmul := Nat.mul_le_mul_right (c.length+1) (Nat.add_le_add_right hq 1)
  have hcmul := Nat.mul_le_mul_left (L+1) (Nat.add_le_add_right hc 1)
  unfold NPSATStackClauseDigits.budget
  nlinarith

lemma formula_budget_bound (query : List Bool) (F : BitFormula) (L : ℕ)
    (hq : query.length≤L) (hm : F.length≤L) (hF : ∀c∈F,c.length≤3)
    (hw : ∀c∈F,∀l∈c,l.labelBits.length≤L) :
    NPSATStackClauseDigits.formulaBudget query F≤720*(L+1)^2 := by
  have hs := map_sum_le F (NPSATStackClauseDigits.budget query) (700*(L+1))
    (by intro c hc;exact clause_budget_bound query c L hq (hF c hc) (hw c hc))
  have hmul := Nat.mul_le_mul_right (700*(L+1)) hm
  unfold NPSATStackClauseDigits.formulaBudget
  nlinarith

lemma item_budget_bound (catalog : List (List Bool)) (F : BitFormula) (query : List Bool) (L : ℕ)
    (hn : catalog.length≤L) (hm : F.length≤L) (hq : query.length≤L)
    (hcat : (dataFields catalog).length≤2*L) (hform : (dataFields (formulaFields F)).length≤2*L)
    (hF : ∀c∈F,c.length≤3) (hw : ∀c∈F,∀l∈c,l.labelBits.length≤L) :
    NPSATStackItem.itemBudget catalog F query L≤60000*(L+1)^2 := by
  have hf := formula_budget_bound query F L hq hm hF hw
  have hv := Nat.mul_le_mul (Nat.add_le_add_right hn 1)
    (show query.length+L+1≤2*(L+1) by omega)
  have hp := Nat.mul_le_mul
    (show catalog.length+F.length+1≤2*(L+1) by omega)
    (show (catalog.length+F.length)*12+4≤24*(L+1) by omega)
  unfold NPSATStackItem.itemBudget
  nlinarith

lemma variables_budget_bound (catalog : List (List Bool)) (F : BitFormula) (labels : List (List Bool)) (L : ℕ)
    (hn : catalog.length≤L) (hm : F.length≤L) (hl : labels.length≤L)
    (hq : ∀q∈labels,q.length≤L)
    (hcat : (dataFields catalog).length≤2*L) (hform : (dataFields (formulaFields F)).length≤2*L)
    (hF : ∀c∈F,c.length≤3) (hw : ∀c∈F,∀l∈c,l.labelBits.length≤L) :
    NPSATStackVariables.budget catalog F labels L≤130000*(L+1)^3 := by
  have hs := map_sum_le labels
    (fun q=>2*NPSATStackItem.itemBudget catalog F q L+8*q.length+14)
    (120100*(L+1)^2) (by
      intro q hmem
      have hqi := hq q hmem
      have hi := item_budget_bound catalog F q L hn hm hqi hcat hform hF hw
      nlinarith)
  have hmul := Nat.mul_le_mul_right (120100*(L+1)^2) hl
  unfold NPSATStackVariables.budget
  nlinarith

end BalancedAssortments.NPSATStackBounds
