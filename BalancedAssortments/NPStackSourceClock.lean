import BalancedAssortments.NPStackSourceFailure

namespace BalancedAssortments.NPStackSourceReduction
open ComplexitySourceModel

def unitBudget (L : ℕ) : ℕ := loopConstant*(L+5)^2
lemma loopBudget_eq (L n : ℕ) : loopBudget L n=(n+1)*unitBudget L := by
  unfold loopBudget unitBudget;ring
lemma unit_le_loop (L n : ℕ) : unitBudget L≤loopBudget L n := by
  rw [loopBudget_eq]
  nlinarith
lemma reject_budget (L : ℕ) :
    6*L*(4*L+7)+11*L+fixedNoSource.length+20≤unitBudget L := by
  have hs : 1≤(L+5)^2 := by
    have hp : 0<(L+5)^2 := by positivity
    omega
  have he := Nat.mul_le_mul_left fixedNoSource.length hs
  unfold unitBudget loopConstant
  nlinarith only [he]
lemma header_budget (L : ℕ) : 280*(3*L+9)+1≤unitBudget L := by
  have hh := Nat.mul_le_mul_right ((L+5)^2) loopConstant_large
  unfold unitBudget
  nlinarith only [hh]
lemma iteration_budget (L : ℕ) : 5000*(L+5)≤unitBudget L := by
  have hh := Nat.mul_le_mul_right ((L+5)^2) loopConstant_large
  unfold unitBudget
  nlinarith only [hh]
lemma loopBudget_step {L n m t s : ℕ} (hm : m<n) (ht : t≤unitBudget L)
    (hs : s≤loopBudget L m) : t+s≤loopBudget L n := by
  rw [loopBudget_eq] at hs ⊢
  have hh := Nat.mul_le_mul_right (unitBudget L) (show m+2≤n+1 by omega)
  nlinarith

end BalancedAssortments.NPStackSourceReduction
