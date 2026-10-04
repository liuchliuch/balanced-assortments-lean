import BalancedAssortments.NPCNFStackReductionProgram

namespace BalancedAssortments.NPCNF.StackReduction
open NPStack NPStack.Macros Encoding

lemma failure_clear_run (s : Register → List Bool) :
    Run program ((s output).length+1) ⟨.failureClear,s⟩ ⟨.failureEmit 0,Function.update s output []⟩ := by
  generalize he : s output=xs
  induction xs generalizing s with
  | nil =>
    apply Run.one
    have hh : Function.update s output []=s := by rw [← he,Function.update_eq_self]
    simp [Step,successors,program,code,he,hh]
  | cons b bs ih =>
    have hs : Step program ⟨.failureClear,s⟩ ⟨.failureClear,Function.update s output bs⟩ := by
      cases b <;> simp [Step,successors,program,code,he]
    have ht := ih (Function.update s output bs) (by simp)
    simpa using Run.succ hs ht

lemma failure_emit_run (s : Register → List Bool) :
    Run program (failureBits.length+1) ⟨.failureEmit 0,Function.update s output []⟩
      ⟨.accept,Function.update s output failureBits⟩ := by
  apply firstRun_sound
  simp [firstRun,successors,program,code,nextFailure,failureBits,encode,unsatRaw,fields,catalogFields,
    formulaFields,clauseFields,encodeFields,encodePayload]

/-- Invalid input paths terminate with one fixed, valid unsatisfiable output;
any previous output contents are explicitly cleared, bit by bit. -/
theorem failure_run (s : Register → List Bool) :
    Run program ((s output).length+failureBits.length+2) ⟨.failureClear,s⟩
      ⟨.accept,Function.update s output failureBits⟩ := by
  have hh := (failure_clear_run s).trans (failure_emit_run s)
  convert hh using 1 <;> omega

lemma failure_not_threeCNF : ¬ThreeCNFLanguage failureBits := by
  rw [failureBits,ThreeCNFLanguage_encode]
  rintro ⟨_,_,σ,hσ⟩
  simp [unsatRaw,Raw.decode,formulaEval,clauseEval] at hσ

/-- One source-preserving register transfer, including its real return jump. -/
theorem transfer_run (t : Transfer) (s : Register → List Bool) (hw : s scratch=[])
    (ht : s (transferTarget t)=[]) :
    Run program (5*(s (transferSource t)).length+3) ⟨.transfer t .readSource,s⟩
      ⟨afterTransfer t,Function.update s (transferTarget t) (s (transferSource t))⟩ := by
  have hsneq : transferSource t≠transferTarget t := by cases t <;> decide
  have hwneq : scratch≠transferTarget t := by cases t <;> decide
  have h := (copy_run (s (transferSource t)) []).relocate_exact (transferMap t) (State.transfer t)
    (transfer_injective t) (transfer_extends t)
    (c' := ⟨.transfer t .readSource,s⟩)
    (d' := ⟨.transfer t .done,Function.update s (transferTarget t) (s (transferSource t))⟩)
    ⟨rfl,by intro k;cases k <;> simp [transferMap,copyMap,copyConfig,copyStacks,hw,ht]⟩
    ⟨rfl,by intro k;cases k <;> simp [transferMap,copyMap,copyConfig,copyStacks,hw,ht,hsneq,hwneq]⟩
    (by intro k hk;have hn : k≠transferTarget t := Ne.symm (hk .target);simp [hn])
  have hret : Step program ⟨.transfer t .done,Function.update s (transferTarget t) (s (transferSource t))⟩
      ⟨afterTransfer t,Function.update s (transferTarget t) (s (transferSource t))⟩ := by
    simp [Step,successors,program,code,returnCode,copyProgram]
  have hh := h.trans (Run.one hret)
  convert hh using 1 <;> omega

end BalancedAssortments.NPCNF.StackReduction
