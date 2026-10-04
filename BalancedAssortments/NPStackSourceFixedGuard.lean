import BalancedAssortments.NPStackSourceVerifierProgramComplete
import BalancedAssortments.NPStackSourceBalancePreserves
import BalancedAssortments.ComplexityTimeFixedSourceLanguage

namespace BalancedAssortments.NPStack.SourceVerifier.Fixed
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

/-- Numeric equality tests allow every padded and unreduced legal encoding.
The constant two is constructed by a literal signed-add subroutine. -/
def command : Command := .script [.add .term .one .one] <|
  VerifierCommands.guardLE .capacity .term <| VerifierCommands.guardLE .term .capacity <|
  VerifierCommands.guardLE .alpha .alphaDen <| VerifierCommands.guardLE .alphaDen .alpha (.halt true)

lemma command_accepts (s : Registers) (ho : zvalue (s .one)=1) :
    (eval command s).1=true ↔ zvalue (s .capacity)=2 ∧ zvalue (s .alpha)=zvalue (s .alphaDen) := by
  simp only [command,eval,evalAssignments,List.foldl_cons,List.foldl_nil,evalAssignment]
  simp only [VerifierCommands.guardLE_accepts,eval,Bool.and_eq_true,Bool.true_and,Bool.and_true,
    zle_correct,Function.update_apply]
  simp only [show RowReg.capacity≠.term by decide,show RowReg.alpha≠.term by decide,
    show RowReg.alphaDen≠.term by decide,if_false,if_true,zadd_value,ho]
  omega

abbrev GuardState := VerifierControl.State VerifierCommands.Control command
abbrev State := Whole.State Balance.LoopState ⊕ GuardState

def program : Program SourceVerifier.Stack State where
  start := .inl Whole.concreteProgram.start
  inputStack := .source
  outputStack := .source
  code q := match q with
    | .inl q => Handoff.code id Sum.inl (.inr (VerifierCommands.program command).start) (Whole.concreteProgram.code q)
    | .inr q => ((VerifierCommands.program command).code q).rename Whole.globalArithmeticMap Sum.inr

/-- Any accepted restricted execution factors through an actual accepted run of
the full verifier and then the actual numeric-parameter guard. -/
theorem accepting_segments {before : SourceVerifier.Stack→List Bool} {T : ℕ} {out : Config SourceVerifier.Stack State}
    (hr : Run program T ⟨program.start,before⟩ out) (ha : accepts program out) :
    ∃ t u middle,
      Whole.StageRun Whole.concreteProgram id before middle t ∧
      Run program u ⟨.inr (VerifierCommands.program command).start,middle⟩ out ∧ t+1+u=T :=
  Whole.handoff_sound Whole.concreteProgram program id Sum.inl _ Function.injective_id (fun _=>rfl) hr ha

lemma guard_suffix_sound (s : Registers) {t : ℕ} {out : Config SourceVerifier.Stack State}
    (hr : Run program t ⟨.inr (VerifierCommands.program command).start,Whole.globalStore s []⟩ out)
    (ha : accepts program out) : (eval command s).1=true := by
  obtain ⟨e,he,hrel,_⟩ := hr.reflect Whole.globalArithmeticMap Sum.inr Whole.globalArithmeticMap_injective
    (P:=VerifierCommands.program command) (fun _=>rfl)
    (c:=VerifierCommands.cfg command s) ⟨rfl,Whole.global_projection s []⟩
  have hacc := accepts_reflect Whole.globalArithmeticMap Sum.inr (R:=program)
    (P:=VerifierCommands.program command) (fun _=>rfl) hrel ha
  obtain ⟨_,heq⟩ := VerifierCommands.command_halted_result command s he hacc
  rw [heq] at hacc
  have hh := terminal_halts VerifierCommands.comparisons SignedAssignCompare.State.result command s
  change (VerifierCommands.program command).code (terminal command s)=.halt true at hacc
  exact Instr.halt.inj (hh.symm.trans hacc)

lemma append_complete {before : SourceVerifier.Stack→List Bool} {T : ℕ}
    {out : Config SourceVerifier.Stack (Whole.State Balance.LoopState)} (s : Registers)
    (hr : Run Whole.concreteProgram T ⟨Whole.concreteProgram.start,before⟩ out)
    (ha : accepts Whole.concreteProgram out) (hs : out.stk=Whole.globalStore s [])
    (hg : (eval command s).1=true) :
    ∃ t ≤ T+budget VerifierCommands.compareTime command s+1,∃ last,
      Run program t ⟨program.start,before⟩ last ∧ accepts program last := by
  have hstage : Whole.StageRun Whole.concreteProgram id before (Whole.globalStore s []) T := by
    refine ⟨out,hr,ha,?_,?_⟩
    · intro k;exact (congrFun hs k).symm
    · intro k hk; exact False.elim (hk k rfl)
  have hfirst := Whole.handoff_complete Whole.concreteProgram program id Sum.inl _ Function.injective_id (fun _=>rfl) hstage
  obtain ⟨t,ht,e,he,hacc,hproj,hframe⟩ := Whole.command_stage_complete command s [] hg
  have hlast := he.relocate_exact (R:=program) Whole.globalArithmeticMap Sum.inr Whole.globalArithmeticMap_injective
    (fun _ _=>rfl) (c':=⟨.inr (VerifierCommands.program command).start,Whole.globalStore s []⟩)
    (d':=⟨.inr e.pc,Whole.globalStore (eval command s).2 []⟩) ⟨rfl,fun _=>rfl⟩ ⟨rfl,hproj⟩ hframe
  refine ⟨T+1+t,by omega,_,hfirst.trans hlast,?_⟩
  change ((VerifierCommands.program command).code e.pc).rename Whole.globalArithmeticMap Sum.inr=.halt true
  rw [hacc];rfl

end BalancedAssortments.NPStack.SourceVerifier.Fixed
