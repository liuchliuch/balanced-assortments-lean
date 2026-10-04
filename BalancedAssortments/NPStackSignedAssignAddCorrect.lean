import BalancedAssortments.NPStackSignedAssignAddClean

namespace BalancedAssortments.NPStack.SignedAssignAdd
open NPStack ComplexityTimeVerifier SignedAssignment
variable {V : Type*} [DecidableEq V]

lemma compute_add_run (a b dst : V) (s : V→ZBits) :
    Run (program a b dst) (copyCost (s a) (s b)+signedAddTime (s a) (s b)+2)
      ⟨.copy .xp .readSource,initialStore s⟩
      ⟨.clearDest false,store s (signedMulFinal ([],[]) (zadd (s a) (s b)).1) [] []⟩ := by
  have hc := copy_operands_run a b dst s
  have hstart : Step (program a b dst)
      ⟨.multiply (.copy false .readSource),store s (signedMulInitial (s a) (s b)) [] []⟩
      ⟨.multiply (.add (.positive (.readX false))),store s (signedMulInitial (s a) (s b)) [] []⟩ := by
    simp [Step,successors,program]
  have ha : Run (program a b dst) (signedAddTime (s a) (s b))
      ⟨.multiply (.add (.positive (.readX false))),store s (signedMulInitial (s a) (s b)) [] []⟩
      ⟨.multiply (.add (.negative .done)),store s (signedMulFinal ([],[]) (zadd (s a) (s b)).1) [] []⟩ := by
    apply (signedAdd_run (s a) (s b)).relocate_exact (fun k => Stack.work (addWork k))
      (fun q => State.multiply (.add q)) (SignedAssignment.work_injective.comp addWork_injective) (add_code a b dst)
    · constructor; rfl; intro k;cases k <;> rfl
    · constructor; rfl; intro k;cases k <;> rfl
    · intro k hk
      have h1:=hk .ap;have h2:=hk .an;have h3:=hk .bp;have h4:=hk .bn
      have h5:=hk .scratch;have h6:=hk .positive;have h7:=hk .negative
      cases k with
      | reg v n | copyScratch | transferScratch => rfl
      | work k => cases k <;> simp_all [addWork,store,signedMulInitial,signedMulFinal]
  have hstop : Step (program a b dst)
      ⟨.multiply (.add (.negative .done)),store s (signedMulFinal ([],[]) (zadd (s a) (s b)).1) [] []⟩
      ⟨.clearDest false,store s (signedMulFinal ([],[]) (zadd (s a) (s b)).1) [] []⟩ := by
    simp [Step,successors,program]
  convert (((hc.trans (Run.one hstart)).trans ha).trans (Run.one hstop)) using 1 <;> omega

def assignmentBudget (x y old : ZBits) : ℕ := copyCost x y+signedAddTime x y+2+
  old.1.length+old.2.length+2+2+4*((zadd x y).1.1.length+(zadd x y).1.2.length)+8

/-- Alias-safe concrete signed addition assignment on the shared register
layout. All operands are copied before any destination component is cleared. -/
theorem assignment_run (a b dst : V) (s : V→ZBits) :
    Run (program a b dst) (assignmentBudget (s a) (s b) (s dst))
      ⟨.copy .xp .readSource,initialStore s⟩
      ⟨.done,initialStore (Function.update s dst (zadd (s a) (s b)).1)⟩ := by
  let z := (zadd (s a) (s b)).1
  let cleared := Function.update s dst ([],[])
  have hd := clearDest_pair_run a b dst s (signedMulFinal ([],[]) z) [] []
  have hf := clearFactor_pair_run a b dst cleared ([],[]) z
  have hm := move_pair_run a b dst cleared z (by simp [cleared])
  simp only [cleared,Function.update_idem] at hm
  have hh := (((compute_add_run a b dst s).trans hd).trans hf).trans hm
  convert hh using 1 <;> dsimp [assignmentBudget,z] <;> omega

lemma assignmentBudget_bound (x y old : ZBits) {W : ℕ}
    (hx : width x≤W) (hy : width y≤W) (ho : width old≤W) :
    assignmentBudget x y old≤40*W+47 := by
  have hs := signedAddTime_bound x y
  have hz := zadd_width x y
  unfold width at hx hy ho hz hs
  dsimp only [assignmentBudget,copyCost]
  omega

theorem assignment_polynomial (a b dst : V) (s : V→ZBits) {W : ℕ}
    (ha : width (s a)≤W) (hb : width (s b)≤W) (hd : width (s dst)≤W) :
    ∃ t≤128*(W+1)^2,Run (program a b dst) t ⟨.copy .xp .readSource,initialStore s⟩
      ⟨.done,initialStore (Function.update s dst (zadd (s a) (s b)).1)⟩ := by
  refine ⟨assignmentBudget (s a) (s b) (s dst),?_,assignment_run a b dst s⟩
  have hh := assignmentBudget_bound _ _ _ ha hb hd
  nlinarith

theorem program_noChoice (a b dst : V) : NoChoice (program a b dst) := by
  intro q x y
  cases q with
  | copy o q => cases q <;> simp [program,SignedAssignment.program,copyProgram,Instr.rename]
  | multiply q =>
    cases q with
    | copy n q => cases n <;> cases q <;> simp [program]
    | multiply p q => simp [program]
    | add q => cases q with
      | positive q => cases q <;> simp [program,signedAddProgram,addProgram,Instr.rename]
      | negative q => cases q <;> simp [program,signedAddProgram,addProgram,Instr.rename]
  | clearDest n => cases n <;> simp [program,SignedAssignment.program]
  | clearFactor n => cases n <;> simp [program,SignedAssignment.program]
  | move n p q => cases q <;> simp [program,SignedAssignment.program,reverseProgram,Instr.rename]
  | done => simp [program,SignedAssignment.program]

theorem assignment_accepting_result (a b dst : V) (s : V→ZBits)
    {t : ℕ} {c : Config (Stack V) State}
    (hr : Run (program a b dst) t ⟨.copy .xp .readSource,initialStore s⟩ c)
    (ha : accepts (program a b dst) c) :
    t=assignmentBudget (s a) (s b) (s dst) ∧
      c=⟨.done,initialStore (Function.update s dst (zadd (s a) (s b)).1)⟩ :=
  hr.halted_unique (noChoice_deterministic (program_noChoice a b dst)) (assignment_run a b dst s) ha rfl

end BalancedAssortments.NPStack.SignedAssignAdd
