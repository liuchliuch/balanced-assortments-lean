import BalancedAssortments.NPStackSourceVerifierBodyEmit

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

def balanceRecord (active : Bool) (s : Registers) : List (List Bool) :=
  [[active],(s .numerator).1,(s .numerator).2]

theorem inner_row_run (s : Registers) (mask balance : List Bool) (active : Bool)
    (hm : NPStackMask.maskValue mask=some active)
    (ha : (eval (VerifierCommands.rowCommand active) s).1=true) :
    ∃ t≤VerifierControl.budget VerifierCommands.compareTime (VerifierCommands.rowCommand active) s,
      Run innerProgram (mask.length+4+t+1+
        (5*((packedStore (VerifierCommands.rowEffect s) [] balance (.inl 7)).length+
          (packedStore (VerifierCommands.rowEffect s) [] balance (.inl 8)).length)+18))
        ⟨.mask .head,packedStore s mask balance⟩
        ⟨.done,emittedRowStore active (packedStore (VerifierCommands.rowEffect s) [] balance)⟩ := by
  obtain ⟨t,ht,hr⟩ := guard_run s balance active
  have he := VerifierCommands.rowCommand_effect active s ha
  rw [he] at hr
  have hj : Step innerProgram
      ⟨guardLabel active (terminal (VerifierCommands.rowCommand active) s),packedStore (VerifierCommands.rowEffect s) [] balance⟩
      ⟨.emit active .negative .reverse,packedStore (VerifierCommands.rowEffect s) [] balance⟩ := by
    simp [Step,successors,guard_exit,ha]
  exact ⟨t,ht,(((mask_run s mask balance active hm).trans hr).trans (Run.one hj)).trans
    (emit_row_run active _ (packed_emitScratch _ _ _) (packed_maskPayload _ _ _))⟩

theorem body_row_run (s : Registers) (mask balance : List Bool) (active : Bool)
    (hm : NPStackMask.maskValue mask=some active)
    (ha : (eval (VerifierCommands.rowCommand active) s).1=true) :
    ∃ t, Run bodyProgram t ⟨bodyProgram.start,packedStore s mask balance⟩
      ⟨.inr (ClearRows.clearDone ClearRows.rowKeys),
        NPStackSourcePairing.rowStore (fun _=>[])
          (workspaceStore (VerifierCommands.rowEffect s)
            (NPStackFields.dataFields (balanceRecord active (VerifierCommands.rowEffect s))++balance))⟩ := by
  obtain ⟨t,ht,hr⟩ := inner_row_run s mask balance active hm ha
  have hh := ClearRows.finish_run innerProgram ClearRows.rowKeys hr (by rfl)
  rw [emitted_row_workspace] at hh
  exact ⟨_,hh⟩

end BalancedAssortments.NPStack.SourceVerifier
