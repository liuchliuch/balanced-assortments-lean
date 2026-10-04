import BalancedAssortments.NPStackVerifierScripts

namespace BalancedAssortments.NPStack.VerifierScripts
open NPStack DirectVerifier ComplexityTimeVerifier

lemma evalAssignment_size (op : ArithmeticAssignment) (s : RowReg→ZBits) {L : ℕ}
    (hs : ∀ v,width (s v)+1≤L) : ∀ v,width (evalAssignment op s v)+1≤3*L := by
  cases op with
  | add dst a b =>
    have ha:=hs a;have hb:=hs b;have hz:=zadd_width (s a) (s b)
    intro v
    by_cases hv : v=dst
    · subst v;simp only [evalAssignment,Function.update_self];omega
    · simp only [evalAssignment,Function.update_of_ne hv];have hh:=hs v;omega
  | multiply dst a b =>
    have ha:=hs a;have hb:=hs b;have hz:=zmul_width (s a) (s b)
    intro v
    by_cases hv : v=dst
    · subst v;simp only [evalAssignment,Function.update_self];omega
    · simp only [evalAssignment,Function.update_of_ne hv];have hh:=hs v;omega

lemma assignmentTime_bound (op : ArithmeticAssignment) (s : RowReg→ZBits) {L : ℕ}
    (hs : ∀ v,width (s v)+1≤L) : assignmentTime op s≤128*L^2 := by
  have hw : assignmentWidth op s+1≤L := by
    cases op with
    | add dst a b | multiply dst a b =>
      have ha:=hs a;have hb:=hs b;have hd:=hs dst
      dsimp only [assignmentWidth]
      omega
  exact Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left hw 2)

/-- A fixed script has a genuine quadratic operational clock in initial
register width. The exponential depends only on the static script length,
never on input data; verifier scripts have fixed lengths at most twelve. -/
theorem script_budget_bound (ops : List ArithmeticAssignment) (s : RowReg→ZBits) {L : ℕ}
    (hs : ∀ v,width (s v)+1≤L) :
    ArithmeticScript.budget assignmentTime ops s≤ops.length*(128*(3^ops.length*L)^2+1) := by
  induction ops generalizing s L with
  | nil => simp [ArithmeticScript.budget]
  | cons op ops ih =>
    have hc:=assignmentTime_bound op s hs
    have hh:=ih (evalAssignment op s) (evalAssignment_size op s hs)
    have he : 3^ops.length*(3*L)=3^(ops.length+1)*L := by rw [pow_succ];ring
    rw [he] at hh
    have hp : 1≤3^(ops.length+1) := Nat.one_le_pow _ _ (by decide)
    have hL : L≤3^(ops.length+1)*L := by nlinarith
    have hC : 128*L^2≤128*(3^(ops.length+1)*L)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL 2)
    simp only [ArithmeticScript.budget,List.length_cons]
    nlinarith

theorem script_polynomial_run (ops : List ArithmeticAssignment) (s : RowReg→ZBits) {L : ℕ}
    (hs : ∀ v,width (s v)+1≤L) :
    ∃ t≤ops.length*(128*(3^ops.length*L)^2+1),
      Run (program ops) t (cfg ops s) (result ops (evalAssignments ops s)) := by
  obtain ⟨t,ht,hr⟩:=script_run ops s
  exact ⟨t,ht.trans (script_budget_bound ops s hs),hr⟩

/-- Literal twelve-assignment arithmetic block used by the row loop. -/
theorem accumulator_polynomial_run (s : RowReg→ZBits) {L : ℕ}
    (hs : ∀ v,width (s v)+1≤L) :
    ∃ t≤12*(128*(531441*L)^2+1),
      Run (program accumulatorAssignments) t (cfg accumulatorAssignments s)
        (result accumulatorAssignments (evalAssignments accumulatorAssignments s)) := by
  simpa only [accumulatorAssignments,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reducePow] using
    script_polynomial_run accumulatorAssignments s hs

end BalancedAssortments.NPStack.VerifierScripts
