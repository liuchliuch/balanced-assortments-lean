import BalancedAssortments.NPStackSourcePairingLoop

namespace BalancedAssortments.NPStackSourcePairing
open NPStack
open NPStackFields (dataFields)
variable {W Q : Type*} [DecidableEq W]

lemma source_reject_code (body : Program (Fin 9 ⊕ W) Q) (q : NPStackSourceRecords.State 6)
    (h : (NPStackSourceRecords.program 6).code q=.halt false) :
    (program body).code (.source q)=.halt false := by
  cases q with
  | accept => simp [NPStackSourceRecords.program] at h
  | field i q => cases q <;> simp_all [NPStackSourceRecords.program,NPStackFieldData.readProgram,program,Instr.rename]

lemma certificate_reject_code (body : Program (Fin 9 ⊕ W) Q) (q : NPStackSourceRecords.State 3)
    (h : (NPStackSourceRecords.program 3).code q=.halt false) :
    (program body).code (.certificate q)=.halt false := by
  cases q with
  | accept => simp [NPStackSourceRecords.program] at h
  | field i q => cases q <;> simp_all [NPStackSourceRecords.program,NPStackFieldData.readProgram,program,Instr.rename]

/-- A malformed or truncated six-field source record reaches actual rejection. -/
lemma reject_source (body : Program (Fin 9 ⊕ W) Q) (input cert : List Bool) (work : W → List Bool)
    (h : NPStackSourceRecords.parseFixed 6 input=none) :
    ∃ t≤6*(5*input.length+5),∃ d,
      Run (program body) t
        (cfg (.source (NPStackSourceRecords.atIndex 6 0)) input cert [] (fun _ => []) work) d ∧
      (program body).code d.pc=.halt false := by
  obtain ⟨t,ht,d,hr,hd⟩ := NPStackSourceRecords.reject_malformed 6 input h
  have hrel : Relocated sourceStack (State.source (Q:=Q))
      (NPStackSourceRecords.cfg (NPStackSourceRecords.atIndex 6 0) input [] (fun _ => []))
      (cfg (.source (NPStackSourceRecords.atIndex 6 0)) input cert [] (fun _ => []) work) := by
    exact ⟨rfl,by intro k;cases k <;> rfl⟩
  obtain ⟨e,he,her,_⟩ := hr.relocate sourceStack State.source source_injective (source_code body) hrel
  refine ⟨t,ht,e,he,?_⟩
  rw [her.1]
  exact source_reject_code body d.pc hd

/-- A malformed, truncated, or missing certificate triple reaches rejection,
without using declared dimensions as a fuel or allocation parameter. -/
lemma reject_certificate (body : Program (Fin 9 ⊕ W) Q) (s : Fin 6 → List Bool)
    (srest input : List Bool) (work : W → List Bool)
    (h : NPStackSourceRecords.parseFixed 3 input=none) :
    ∃ t≤3*(5*input.length+5),∃ d,
      Run (program body) t
        (cfg (.certificate (NPStackSourceRecords.atIndex 3 0)) srest input [] (sourceRow s) work) d ∧
      (program body).code d.pc=.halt false := by
  obtain ⟨t,ht,d,hr,hd⟩ := NPStackSourceRecords.reject_malformed 3 input h
  have hrel : Relocated certificateStack (State.certificate (Q:=Q))
      (NPStackSourceRecords.cfg (NPStackSourceRecords.atIndex 3 0) input [] (fun _ => []))
      (cfg (.certificate (NPStackSourceRecords.atIndex 3 0)) srest input [] (sourceRow s) work) := by
    refine ⟨rfl,?_⟩;intro k;cases k <;>
      simp [certificateStack,cfg,store,rowStore,sourceRow,certificateIndex,NPStackSourceRecords.cfg,NPStackSourceRecords.store]
  obtain ⟨e,he,her,_⟩ := hr.relocate certificateStack State.certificate certificate_injective (certificate_code body) hrel
  refine ⟨t,ht,e,he,?_⟩
  rw [her.1]
  exact certificate_reject_code body d.pc hd

end BalancedAssortments.NPStackSourcePairing
