import BalancedAssortments.NPStackVerifierCommands

namespace BalancedAssortments.NPStack.VerifierControl
open NPStack DirectVerifier ComplexityTimeVerifier

lemma assignments_size (ops : List ArithmeticAssignment) (s : Registers) {L : ℕ}
    (hs : ∀ v,width (s v)+1≤L) : ∀ v,width (evalAssignments ops s v)+1≤3^ops.length*L := by
  induction ops generalizing s L with
  | nil => simpa [evalAssignments] using hs
  | cons op ops ih =>
    have hh := ih (evalAssignment op s) (VerifierScripts.evalAssignment_size op s hs)
    simpa [evalAssignments,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh

/-- A constant computed solely from the finite control syntax. -/
def costCoefficient : Command→ℕ
  | .halt _ => 0
  | .script ops next => ops.length*(128*(3^ops.length)^2+1)+1+costCoefficient next*(3^ops.length)^2
  | .branchLE _ _ yes no => 66+costCoefficient yes+costCoefficient no

theorem budget_quadratic (c : Command) (s : Registers) {L : ℕ}
    (hs : ∀ v,width (s v)+1≤L) :
    budget VerifierCommands.compareTime c s≤costCoefficient c*L^2 := by
  have hL : 1≤L := by have hh:=hs .zero;omega
  have hL2 : 1≤L^2 := by nlinarith
  induction c generalizing s L with
  | halt => simp [budget,costCoefficient]
  | script ops next ih =>
    have hscript := VerifierScripts.script_budget_bound ops s hs
    have hnext := ih (evalAssignments ops s) (assignments_size ops s hs)
    have hfactor : 1≤3^ops.length*L := by
      have hh : 1≤3^ops.length := Nat.one_le_pow _ _ (by decide)
      nlinarith
    specialize hnext hfactor (by nlinarith)
    simp only [budget,costCoefficient]
    calc
      _ ≤ ops.length*(128*(3^ops.length*L)^2+1)+1+costCoefficient next*(3^ops.length*L)^2 := Nat.add_le_add (Nat.add_le_add_right hscript 1) hnext
      _ ≤ _ := by nlinarith
  | branchLE a b yes no ihy ihn =>
    have hc := SignedAssignCompare.guardCost_bound (s a) (s b) (W:=L) (by have hh:=hs a;omega) (by have hh:=hs b;omega)
    have hy := ihy s hs hL hL2
    have hn := ihn s hs hL hL2
    dsimp only [budget,costCoefficient,VerifierCommands.compareTime]
    split_ifs <;> nlinarith

end BalancedAssortments.NPStack.VerifierControl
