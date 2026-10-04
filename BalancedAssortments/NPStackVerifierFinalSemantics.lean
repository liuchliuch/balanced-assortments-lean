import BalancedAssortments.NPStackVerifierRowSemantics

namespace BalancedAssortments.NPStack.VerifierCommands
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

lemma rankCommand_accepts (s : Registers) :
    (eval rankCommand s).1=(zle (s .rankNum) (zmul (zmul (s .capacity) (s .q)).1 (s .rankDen)).1).1 := by
  simp [rankCommand,eval_script,guardLE_accepts,eval,evalAssignments,finalAssignments,
    evalAssignment,Function.update]

lemma revenueCommand_accepts (s : Registers) :
    (eval revenueCommand s).1=(zle
      (zmul (zmul (s .target) (s .revenueDen)).1 (zadd (s .q) (s .total)).1).1
      (zmul (s .targetDen) (s .revenueNum)).1).1 := by
  simp [revenueCommand,eval_script,guardLE_accepts,eval,evalAssignments,revenueAssignments,
    evalAssignment,Function.update]

lemma balanceCommand_accepts (s : Registers) (active : Bool) :
    (eval (balanceCommand active) s).1=
      (if active then (zle (zmul (s .alpha) (s .maximum)).1 (zmul (s .alphaDen) (s .numerator)).1).1 else true) := by
  cases active <;> simp [balanceCommand,eval_script,guardLE_accepts,eval,evalAssignments,
    balanceAssignments,evalAssignment,Function.update]

lemma headerCommand_accepts (s : Registers) (hz : s .zero=zzero) :
    (eval headerCommand s).1=
      ((zle (s .declaredCount) (s .count)).1 && (zle (s .count) (s .declaredCount)).1 &&
      positive (s .count) && positive (s .capacity) && (zle (s .capacity) (s .count)).1 &&
      positive (s .alpha) && positive (s .alphaDen) && (zle (s .alpha) (s .alphaDen)).1 &&
      positive (s .targetDen) && positive (s .q)) := by
  simp [headerCommand,guardLE_accepts,guardPositive_accepts,eval,positive,hz,Bool.and_assoc]

lemma final_preserves (s : Registers) (k : RowReg) (ht : k≠.term) (hp : k≠.product) :
    (eval rankCommand s).2 k=s k ∧ (eval revenueCommand s).2 k=s k := by
  simp only [rankCommand,revenueCommand,eval_script,guardLE,eval]
  constructor <;> split_ifs <;>
    simp [evalAssignments,finalAssignments,revenueAssignments,evalAssignment,Function.update,ht,hp]

lemma balance_preserves (s : Registers) (active : Bool) (k : RowReg)
    (ht : k≠.term) (hp : k≠.product) : (eval (balanceCommand active) s).2 k=s k := by
  cases active <;> simp only [balanceCommand,Bool.false_eq_true,if_false,if_true,eval_script,guardLE,eval]
  split_ifs <;> simp [evalAssignments,balanceAssignments,evalAssignment,Function.update,ht,hp]

end BalancedAssortments.NPStack.VerifierCommands
