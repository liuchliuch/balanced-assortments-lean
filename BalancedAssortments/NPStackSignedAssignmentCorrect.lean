import BalancedAssortments.NPStackSignedAssignmentClean

namespace BalancedAssortments.NPStack.SignedAssignment
open NPStack ComplexityTimeVerifier
variable {V : Type*} [DecidableEq V]

def assignmentBudget (x y old : ZBits) : ℕ :=
  copyCost x y+signedMultiplyBudget x y+1+
    old.1.length+old.2.length+2+y.1.length+y.2.length+2+
    4*((zmul x y).1.1.length+(zmul x y).1.2.length)+8

/-- Actual alias-safe multiplication assignment. Operands are copied before
the destination is cleared; even dst=a or dst=b is valid. All other registers
are preserved and the complete work allocation is empty on return. -/
theorem assignment_run (a b dst : V) (s : V→ZBits) :
    ∃ t≤assignmentBudget (s a) (s b) (s dst),
      Run (program a b dst) t ⟨.copy .xp .readSource,initialStore s⟩
        ⟨.done,initialStore (Function.update s dst (zmul (s a) (s b)).1)⟩ := by
  obtain ⟨t,ht,hcompute⟩ := compute_run a b dst s
  let z := (zmul (s a) (s b)).1
  let cleared := Function.update s dst ([],[])
  have hd := clearDest_pair_run a b dst s (signedMulFinal (s b) z) [] []
  have hf := clearFactor_pair_run a b dst cleared (s b) z
  have hm := move_pair_run a b dst cleared z (by simp [cleared])
  simp only [cleared,Function.update_idem] at hm
  have h := ((hcompute.trans hd).trans hf).trans hm
  refine ⟨_,?_,h⟩
  dsimp only [assignmentBudget,z] at *
  omega

lemma assignmentBudget_bound (x y old : ZBits) {W : ℕ}
    (hx : width x≤W) (hy : width y≤W) (ho : width old≤W) :
    assignmentBudget x y old≤128*(W+1)^2 := by
  have hm := signedMultiplyBudget_bound x y hx hy
  have hz := zmul_width x y
  have hxp : x.1.length≤W := by unfold width at hx;omega
  have hxn : x.2.length≤W := by unfold width at hx;omega
  have hyp : y.1.length≤W := by unfold width at hy;omega
  have hyn : y.2.length≤W := by unfold width at hy;omega
  have hop : old.1.length≤W := by unfold width at ho;omega
  have hon : old.2.length≤W := by unfold width at ho;omega
  have hzp : (zmul x y).1.1.length≤3*W+1 := by unfold width at hz;omega
  have hzn : (zmul x y).1.2.length≤3*W+1 := by unfold width at hz;omega
  unfold assignmentBudget copyCost
  nlinarith only [hm,hxp,hxn,hyp,hyn,hop,hon,hzp,hzn,Nat.zero_le (W^2),Nat.zero_le W]

/-- Polynomial operational bound depends only on input register widths,
including the old destination whose cells are actually popped and charged. -/
theorem assignment_polynomial (a b dst : V) (s : V→ZBits) {W : ℕ}
    (ha : width (s a)≤W) (hb : width (s b)≤W) (hd : width (s dst)≤W) :
    ∃ t≤128*(W+1)^2,
      Run (program a b dst) t ⟨.copy .xp .readSource,initialStore s⟩
        ⟨.done,initialStore (Function.update s dst (zmul (s a) (s b)).1)⟩ := by
  obtain ⟨t,ht,hr⟩ := assignment_run a b dst s
  exact ⟨t,ht.trans (assignmentBudget_bound _ _ _ ha hb hd),hr⟩

lemma program_noChoice (a b dst : V) : NoChoice (program a b dst) := by
  intro q x y
  cases q with
  | copy o q => cases q <;> simp [program,copyProgram,Instr.rename]
  | multiply q =>
    simp only [program]
    split
    · simp
    · exact Instr.rename_no_choice _ (signedMultiply_noChoice q) _ _ x y
  | clearDest n => cases n <;> simp [program]
  | clearFactor n => cases n <;> simp [program]
  | move n p q => cases q <;> simp [program,reverseProgram,Instr.rename]
  | done => simp [program]

theorem assignment_accepting_result (a b dst : V) (s : V→ZBits)
    {t : ℕ} {c : Config (Stack V) State}
    (hr : Run (program a b dst) t ⟨.copy .xp .readSource,initialStore s⟩ c)
    (ha : accepts (program a b dst) c) :
    t≤assignmentBudget (s a) (s b) (s dst) ∧
      c=⟨.done,initialStore (Function.update s dst (zmul (s a) (s b)).1)⟩ := by
  obtain ⟨u,hu,hknown⟩ := assignment_run a b dst s
  have he := hr.halted_unique (noChoice_deterministic (program_noChoice a b dst)) hknown ha rfl
  exact ⟨he.1 ▸ hu,he.2⟩

end BalancedAssortments.NPStack.SignedAssignment
