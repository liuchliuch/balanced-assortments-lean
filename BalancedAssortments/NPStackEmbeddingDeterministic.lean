import BalancedAssortments.NPStackEmbeddingSound

namespace BalancedAssortments.NPStack
variable {K Q K' Q' : Type*} [DecidableEq K] [DecidableEq K']

lemma Instr.rename_no_choice (i : Instr K Q) (h : ∀ a b,i≠.choice a b)
    (fk : K→K') (fq : Q→Q') (a b : Q') : i.rename fk fq≠.choice a b := by
  cases i <;> simp [Instr.rename]
  rename_i q r
  exact False.elim (h q r rfl)

lemma DeterministicRun.one {P : Program K Q} {c d : Config K Q}
    (hu : UniqueStep P c) (h : Step P c d) : DeterministicRun P 1 c d :=
  .succ hu h (.zero d)

lemma Run.deterministic {P : Program K Q} (hn : NoChoice P) {t : ℕ} {c d : Config K Q}
    (h : Run P t c d) : DeterministicRun P t c d := by
  induction h with
  | zero c => exact .zero c
  | @succ t c d e hs hr ih => exact .succ (uniqueStep_of_code (hn c.pc)) hs ih

/-- Forward relocation retains a locally deterministic path even when the
caller contains nondeterministic certificate guessing or body instructions. -/
theorem Run.relocate_deterministic {P : Program K Q} {R : Program K' Q'}
    (hn : NoChoice P) (fk : K→K') (fq : Q→Q') (hinj : Function.Injective fk)
    (hcode : CodeExtends P R fk fq) {t : ℕ} {c d : Config K Q} {c' : Config K' Q'}
    (h : Run P t c d) (hc : Relocated fk fq c c') :
    ∃ d',DeterministicRun R t c' d' ∧ Relocated fk fq d d' ∧ Frame fk c' d' := by
  induction h generalizing c' with
  | zero c => exact ⟨c',.zero c',hc,fun _ _ => rfl⟩
  | @succ t c d e hs hr ih =>
    have hnh : ∀ b,P.code c.pc≠.halt b := fun b he => halted_no_step he hs
    have hi := hcode c.pc hnh
    rw [← hc.1] at hi
    have hu : UniqueStep R c' := uniqueStep_of_code (by
      intro a b
      rw [hi]
      exact Instr.rename_no_choice _ (hn c.pc) fk fq a b)
    obtain ⟨next,hnext,hrel,hframe⟩ := hs.relocate fk fq hinj hcode hc
    obtain ⟨last,hlast,hlrel,hlframe⟩ := ih hrel
    exact ⟨last,.succ hu hnext hlast,hlrel,fun k hk => (hlframe k hk).trans (hframe k hk)⟩

theorem Run.relocate_deterministic_exact {P : Program K Q} {R : Program K' Q'}
    (hn : NoChoice P) (fk : K→K') (fq : Q→Q') (hinj : Function.Injective fk)
    (hcode : CodeExtends P R fk fq) {t : ℕ} {c d : Config K Q} {c' d' : Config K' Q'}
    (h : Run P t c d) (hc : Relocated fk fq c c') (hd : Relocated fk fq d d') (hf : Frame fk c' d') :
    DeterministicRun R t c' d' := by
  obtain ⟨out,hr,hrel,hframe⟩ := h.relocate_deterministic hn fk fq hinj hcode hc
  rwa [relocated_frame_unique fk fq hrel hd hframe hf] at hr

end BalancedAssortments.NPStack
