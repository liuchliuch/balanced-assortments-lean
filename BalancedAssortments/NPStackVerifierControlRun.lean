import BalancedAssortments.NPStackVerifierControl

namespace BalancedAssortments.NPStack.VerifierControl
open NPStack DirectVerifier ComplexityTimeVerifier
variable {Q : Type} [DecidableEq Q]

lemma control_run {A B : Type} {P : Program Stack A} {R : Program Stack B}
    (f : A→B) (he : CodeExtends P R id f) {t : ℕ} {c d : Config Stack A}
    (hr : Run P t c d) : Run R t ⟨f c.pc,c.stk⟩ ⟨f d.pc,d.stk⟩ := by
  apply hr.relocate_exact id f Function.injective_id he
  · exact ⟨rfl,fun _ => rfl⟩
  · exact ⟨rfl,fun _ => rfl⟩
  · intro k hk;exact False.elim (hk k rfl)

/-- Structural total execution of a finite guard/script tree. Calls execute
real compiled primitive code; each return contributes one real jump. -/
theorem run_command (C : RowReg→RowReg→Program Stack Q) (exit : Bool→Q)
    (T : RowReg→RowReg→Registers→ℕ)
    (he : ∀ a b v,(C a b).code (exit v)=.halt v)
    (hr : ∀ a b s,∃ t≤T a b s,Run (C a b) t ⟨(C a b).start,SignedAssignment.initialStore s⟩
      ⟨exit (zle (s a) (s b)).1,SignedAssignment.initialStore s⟩)
    (c : Command) (s : Registers) :
    ∃ t≤budget T c s,Run (program C exit c) t (cfg C c s) (result c s) := by
  induction c generalizing s with
  | halt b => exact ⟨0,le_rfl,Run.zero _⟩
  | script ops next ih =>
    obtain ⟨t,ht,hscript⟩ := VerifierScripts.script_run ops s
    obtain ⟨u,hu,htail⟩ := ih (evalAssignments ops s)
    have h1 := control_run Sum.inl (script_extends C exit ops next) hscript
    have h2 := control_run Sum.inr (script_next_extends C exit ops next) htail
    have hj : Step (program C exit (.script ops next))
        ⟨Sum.inl (ArithmeticScript.done ops),SignedAssignment.initialStore (evalAssignments ops s)⟩
        ⟨Sum.inr (start C next),SignedAssignment.initialStore (evalAssignments ops s)⟩ := by
      simp [Step,successors,program,code]
    refine ⟨t+1+u,by dsimp only [budget];omega,?_⟩
    exact (h1.trans (Run.one hj)).trans h2
  | branchLE a b yes no ihy ihn =>
    obtain ⟨t,ht,hcompare⟩ := hr a b s
    have hcmp := control_run Sum.inl (compare_extends C exit he a b yes no) hcompare
    cases hb : (zle (s a) (s b)).1 with
    | false =>
      obtain ⟨u,hu,huRun⟩ := ihn s
      have htail := control_run (fun q => Sum.inr (Sum.inr q)) (no_extends C exit a b yes no) huRun
      have hn : exit false≠exit true := by
        intro heq
        have hh := congrArg (C a b).code heq
        rw [he a b false,he a b true] at hh
        cases hh
      have hj : Step (program C exit (.branchLE a b yes no))
          ⟨Sum.inl (exit false),SignedAssignment.initialStore s⟩
          ⟨Sum.inr (Sum.inr (start C no)),SignedAssignment.initialStore s⟩ := by
        simp [Step,successors,program,code,hn]
      rw [hb] at hcmp
      refine ⟨t+1+u,?_,?_⟩
      · simp only [budget,hb,Bool.false_eq_true,if_false]
        omega
      · simpa only [cfg,result,terminal,eval,hb,Bool.false_eq_true,if_false,start] using
          (hcmp.trans (Run.one hj)).trans htail
    | true =>
      obtain ⟨u,hu,huRun⟩ := ihy s
      have htail := control_run (fun q => Sum.inr (Sum.inl q)) (yes_extends C exit a b yes no) huRun
      have hj : Step (program C exit (.branchLE a b yes no))
          ⟨Sum.inl (exit true),SignedAssignment.initialStore s⟩
          ⟨Sum.inr (Sum.inl (start C yes)),SignedAssignment.initialStore s⟩ := by
        simp [Step,successors,program,code]
      rw [hb] at hcmp
      refine ⟨t+1+u,?_,?_⟩
      · simp only [budget,hb,if_true]
        omega
      · simpa only [cfg,result,terminal,eval,hb,if_true,start] using
          (hcmp.trans (Run.one hj)).trans htail

theorem program_noChoice (C : RowReg→RowReg→Program Stack Q) (exit : Bool→Q)
    (hn : ∀ a b,NoChoice (C a b)) (c : Command) : NoChoice (program C exit c) := by
  induction c with
  | halt b => intro q x y;simp [program,code]
  | script ops next ih =>
    intro q x y
    cases q with
    | inl q =>
      by_cases he : q=ArithmeticScript.done ops
      · simp [program,code,he]
      · simpa only [program,code,he,if_false] using Instr.rename_no_choice _ (VerifierScripts.script_noChoice ops q) id Sum.inl x y
    | inr q => exact Instr.rename_no_choice _ (ih q) id Sum.inr x y
  | branchLE a b yes no ihy ihn =>
    intro q x y
    cases q with
    | inl q =>
      by_cases ht : q=exit true
      · simp [program,code,ht]
      · by_cases hf : q=exit false
        · dsimp only [program,code]
          rw [if_neg ht,if_pos hf]
          simp
        · simpa only [program,code,ht,hf,if_false] using Instr.rename_no_choice _ (hn a b q) id Sum.inl x y
    | inr q => cases q with
      | inl q => exact Instr.rename_no_choice _ (ihy q) id (fun q => Sum.inr (Sum.inl q)) x y
      | inr q => exact Instr.rename_no_choice _ (ihn q) id (fun q => Sum.inr (Sum.inr q)) x y

/-- Every halting run has the same Boolean answer, exact final register store,
and the proved transition bound. No late or alternative accepting path exists. -/
theorem halted_result (C : RowReg→RowReg→Program Stack Q) (exit : Bool→Q)
    (T : RowReg→RowReg→Registers→ℕ)
    (he : ∀ a b v,(C a b).code (exit v)=.halt v)
    (hr : ∀ a b s,∃ t≤T a b s,Run (C a b) t ⟨(C a b).start,SignedAssignment.initialStore s⟩
      ⟨exit (zle (s a) (s b)).1,SignedAssignment.initialStore s⟩)
    (hn : ∀ a b,NoChoice (C a b)) (c : Command) (s : Registers)
    {t : ℕ} {out : Config Stack (State Q c)} {b : Bool}
    (h : Run (program C exit c) t (cfg C c s) out) (ha : (program C exit c).code out.pc=.halt b) :
    t≤budget T c s ∧ out=result c s := by
  obtain ⟨u,hu,hh⟩ := run_command C exit T he hr c s
  have heq := h.halted_unique (noChoice_deterministic (program_noChoice C exit hn c)) hh ha (terminal_halts C exit c s)
  exact ⟨heq.1 ▸ hu,heq.2⟩

end BalancedAssortments.NPStack.VerifierControl
