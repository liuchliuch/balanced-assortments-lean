import BalancedAssortments.NPStackSourceVerifierBody

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

lemma body_noChoice : NoChoice bodyProgram := ClearRows.finish_noChoice innerProgram ClearRows.rowKeys inner_noChoice

lemma mask_run (s : Registers) (bits balance : List Bool) (active : Bool)
    (h : NPStackMask.maskValue bits=some active) :
    Run innerProgram (bits.length+4) ⟨.mask .head,packedStore s bits balance⟩
      ⟨guardLabel active (VerifierControl.start VerifierCommands.comparisons (VerifierCommands.rowCommand active)),
        packedStore s [] balance⟩ := by
  let mid := Function.update (packedStore s [] balance) (.inr (.inr .maskFlag)) [active]
  have hm : Run innerProgram (bits.length+2) ⟨.mask .head,packedStore s bits balance⟩ ⟨.mask .accept,mid⟩ := by
    apply (NPStackMask.mask_run bits [] active h).relocate_exact maskMap InnerState.mask maskMap_injective mask_extends
    · constructor; rfl; intro b;cases b <;> simp [maskMap,NPStackMask.cfg,NPStackMask.store]
    · constructor; rfl; intro b;cases b <;> simp [mid,maskMap,NPStackMask.cfg,NPStackMask.store,Function.update]
    · intro k hk
      have hm:=hk false;have hf:=hk true
      dsimp only [maskMap] at hm hf
      simpa [mid,Function.update,Ne.symm hf] using (packed_other_mask s bits balance k (Ne.symm hm)).symm
  have hj : Step innerProgram ⟨.mask .accept,mid⟩ ⟨.choose,mid⟩ := by simp [Step,successors,innerProgram]
  have he : Function.update mid (.inr (.inr .maskFlag)) []=packedStore s [] balance := by
    funext k
    by_cases hk : k=.inr (.inr .maskFlag)
    · subst k;simp [mid]
    · simp [mid,Function.update,hk]
  have hp : Step innerProgram ⟨.choose,mid⟩
      ⟨guardLabel active (VerifierControl.start VerifierCommands.comparisons (VerifierCommands.rowCommand active)),
        packedStore s [] balance⟩ := by
    cases active <;> simp [Step,successors,innerProgram,mid,Function.update_idem,he,guardLabel]
  convert (hm.trans (Run.one hj)).trans (Run.one hp) using 1 <;> omega

lemma guard_run (s : Registers) (balance : List Bool) (active : Bool) :
    ∃ t≤VerifierControl.budget VerifierCommands.compareTime (VerifierCommands.rowCommand active) s,
      Run innerProgram t
        ⟨guardLabel active (VerifierControl.start VerifierCommands.comparisons (VerifierCommands.rowCommand active)),packedStore s [] balance⟩
        ⟨guardLabel active (VerifierControl.terminal (VerifierCommands.rowCommand active) s),
          packedStore (VerifierControl.eval (VerifierCommands.rowCommand active) s).2 [] balance⟩ := by
  obtain ⟨t,ht,hr⟩ := VerifierCommands.command_run (VerifierCommands.rowCommand active) s
  refine ⟨t,ht,hr.relocate_exact arithmeticMap (guardLabel active) arithmeticMap_injective (guard_extends active) ?_ ?_ ?_⟩
  · exact ⟨rfl,packed_projection s [] balance⟩
  · exact ⟨rfl,packed_projection _ [] balance⟩
  · intro k hk
    exact (packed_frame s _ [] balance k hk).symm

lemma guard_exit (s : Registers) (active : Bool) :
    innerProgram.code (guardLabel active (VerifierControl.terminal (VerifierCommands.rowCommand active) s))=
      if (VerifierControl.eval (VerifierCommands.rowCommand active) s).1 then
        .jump (.emit active .negative .reverse) else .halt false := by
  have hh := VerifierControl.terminal_halts VerifierCommands.comparisons SignedAssignCompare.State.result
    (VerifierCommands.rowCommand active) s
  cases active <;> change guardReturn _ _ _=_
  all_goals
    unfold guardReturn
    change (VerifierCommands.program _).code _ = _ at hh
    rw [hh]
    cases he : (VerifierControl.eval (VerifierCommands.rowCommand _) s).1 <;> rfl

def emittedStore (part : EmitPart) (s : BodyStack→List Bool) : BodyStack→List Bool :=
  Function.update (Function.update s (emitSource part) []) (.inr (.inr .balance))
    (NPStackFields.tagBits (s (emitSource part))++false::s (.inr (.inr .balance)))

lemma emit_run (active : Bool) (part : EmitPart) (s : BodyStack→List Bool)
    (hs : s (.inr (.inr .emitScratch))=[]) :
    Run innerProgram (5*(s (emitSource part)).length+4) ⟨.emit active part .reverse,s⟩
      ⟨emitNext active part,emittedStore part s⟩ := by
  have hh : Run innerProgram (5*(s (emitSource part)).length+3) ⟨.emit active part .reverse,s⟩
      ⟨.emit active part .accept,emittedStore part s⟩ := by
    apply (NPStackFieldData.emit_field (s (emitSource part)) (s (.inr (.inr .balance)))).relocate_exact
      (emitMap part) (.emit active part) (emitMap_injective part) (emit_extends active part)
    · constructor; rfl; intro k;cases k <;> simp [emitMap,NPStackFieldData.emitConfig,NPStackFieldData.dataStacks,hs]
    · constructor; rfl; intro k;cases part <;> cases k <;>
        simp [emittedStore,emitSource,emitMap,Function.update,NPStackFieldData.emitConfig,NPStackFieldData.dataStacks,hs]
    · intro k hk
      have hi:=hk .input;have ho:=hk .output
      dsimp only [emitMap] at hi ho
      simp only [emittedStore,Function.update_of_ne (Ne.symm ho),Function.update_of_ne (Ne.symm hi)]
  have hj : Step innerProgram ⟨.emit active part .accept,emittedStore part s⟩
      ⟨emitNext active part,emittedStore part s⟩ := by simp [Step,successors,innerProgram]
  convert hh.trans (Run.one hj) using 1 <;> omega

end BalancedAssortments.NPStack.SourceVerifier
