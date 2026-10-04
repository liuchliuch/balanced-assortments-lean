import BalancedAssortments.NPStackSourceVerifierBodyRun

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

lemma inner_bad_mask (s : Registers) (mask balance : List Bool)
    (hm : NPStackMask.maskValue mask=none) :
    ∃ t e,Run innerProgram t ⟨.mask .head,packedStore s mask balance⟩ e ∧ innerProgram.code e.pc=.halt false := by
  obtain ⟨t,ht,rest,hr⟩ := NPStackMask.mask_reject mask [] hm
  refine ⟨t,⟨.mask .reject,packedStore s rest balance⟩,?_,rfl⟩
  apply hr.relocate_exact maskMap InnerState.mask maskMap_injective mask_extends
  · constructor;rfl;intro b;cases b <;> simp [maskMap,NPStackMask.cfg,NPStackMask.store]
  · constructor;rfl;intro b;cases b <;> simp [maskMap,NPStackMask.cfg,NPStackMask.store]
  · intro k hk
    have h:=hk false
    dsimp only [maskMap] at h
    exact (packed_other_mask s rest balance k (Ne.symm h)).trans
      (packed_other_mask s mask balance k (Ne.symm h)).symm

lemma inner_bad_guard (s : Registers) (mask balance : List Bool) (active : Bool)
    (hm : NPStackMask.maskValue mask=some active)
    (ha : (eval (VerifierCommands.rowCommand active) s).1=false) :
    ∃ t e,Run innerProgram t ⟨.mask .head,packedStore s mask balance⟩ e ∧ innerProgram.code e.pc=.halt false := by
  obtain ⟨t,ht,hr⟩ := guard_run s balance active
  refine ⟨_,_,(mask_run s mask balance active hm).trans hr,?_⟩
  simp [guard_exit,ha]

/-- No accepting inner-body execution bypasses either the mask grammar or
any local rational-domain/capacity check. -/
theorem inner_accepting_result (s : Registers) (mask balance : List Bool)
    {t : ℕ} {out : Config BodyStack InnerState}
    (hr : Run innerProgram t ⟨.mask .head,packedStore s mask balance⟩ out)
    (ha : accepts innerProgram out) :
    ∃ active, NPStackMask.maskValue mask=some active ∧
      (eval (VerifierCommands.rowCommand active) s).1=true ∧
      out=⟨.done,emittedRowStore active (packedStore (VerifierCommands.rowEffect s) [] balance)⟩ := by
  cases hm : NPStackMask.maskValue mask with
  | none =>
    obtain ⟨u,e,he,hfalse⟩ := inner_bad_mask s mask balance hm
    have hh := Run.halted_unique (noChoice_deterministic inner_noChoice) hr he ha hfalse
    rw [hh.2] at ha
    simp [accepts,hfalse] at ha
  | some active =>
    cases hb : (eval (VerifierCommands.rowCommand active) s).1 with
    | false =>
      obtain ⟨u,e,he,hfalse⟩ := inner_bad_guard s mask balance active hm hb
      have hh := Run.halted_unique (noChoice_deterministic inner_noChoice) hr he ha hfalse
      rw [hh.2] at ha
      simp [accepts,hfalse] at ha
    | true =>
      obtain ⟨u,hu,he⟩ := inner_row_run s mask balance active hm hb
      have hh := Run.halted_unique (noChoice_deterministic inner_noChoice) hr he ha (by rfl)
      exact ⟨active,rfl,hb,hh.2⟩

theorem body_accepting_result (s : Registers) (mask balance : List Bool)
    {t : ℕ} {out : Config BodyStack (InnerState ⊕ ClearRows.ClearState ClearRows.rowKeys)}
    (hr : Run bodyProgram t ⟨bodyProgram.start,packedStore s mask balance⟩ out)
    (ha : accepts bodyProgram out) :
    ∃ active, NPStackMask.maskValue mask=some active ∧
      (eval (VerifierCommands.rowCommand active) s).1=true ∧
      out.stk=NPStackSourcePairing.rowStore (fun _=>[])
        (workspaceStore (VerifierCommands.rowEffect s)
          (NPStackFields.dataFields (balanceRecord active (VerifierCommands.rowEffect s))++balance)) := by
  obtain ⟨u,e,he,haccept,hstore⟩ := ClearRows.finish_accepting_store innerProgram ClearRows.rowKeys
    ⟨.mask .head,packedStore s mask balance⟩ hr ha
  obtain ⟨active,hm,hb,heq⟩ := inner_accepting_result s mask balance he haccept
  subst e
  rw [emitted_row_workspace] at hstore
  exact ⟨active,hm,hb,hstore⟩

end BalancedAssortments.NPStack.SourceVerifier
