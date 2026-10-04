import BalancedAssortments.NPStackSourceVerifierHeader
import BalancedAssortments.NPStackEmbeddingDeterministic

namespace BalancedAssortments.NPStack.SourceVerifier.Header
open NPStack NPStack.SourceVerifier DirectVerifier
open NPStackFields (dataFields)

lemma program_noChoice : NoChoice program := by
  intro q a b
  cases q with
  | source q => cases q with
    | accept => simp [program]
    | field i q => cases q <;> simp [program,NPStackSourceRecords.program,NPStackFieldData.readProgram,Instr.rename]
  | certificate q => cases q with
    | accept => simp [program]
    | field i q => cases q <;> simp [program,NPStackSourceRecords.program,NPStackFieldData.readProgram,Instr.rename]
  | rank | revenue | one | done => simp [program]

lemma program_deterministic : Deterministic program := noChoice_deterministic program_noChoice

lemma source_reject_code (q : NPStackSourceRecords.State 8) (h : (NPStackSourceRecords.program 8).code q=.halt false) :
    program.code (.source q)=.halt false := by
  cases q with
  | accept => simp [NPStackSourceRecords.program] at h
  | field i q => cases q <;> simp_all [program,NPStackSourceRecords.program,NPStackFieldData.readProgram,Instr.rename]
lemma certificate_reject_code (q : NPStackSourceRecords.State 2) (h : (NPStackSourceRecords.program 2).code q=.halt false) :
    program.code (.certificate q)=.halt false := by
  cases q with
  | accept => simp [NPStackSourceRecords.program] at h
  | field i q => cases q <;> simp_all [program,NPStackSourceRecords.program,NPStackFieldData.readProgram,Instr.rename]

lemma reject_source (input cert : List Bool) (hb : NPStackSourceRecords.parseFixed 8 input=none) :
    ∃ t ≤ 8*(5*input.length+5),∃ d,Run program t
      (cfg (.source (NPStackSourceRecords.atIndex 8 0)) input cert (fun _ => [])) d ∧ program.code d.pc=.halt false := by
  obtain ⟨t,ht,e,he,hh⟩ := NPStackSourceRecords.reject_malformed 8 input hb
  have hrel : Relocated sourceMap State.source
      (NPStackSourceRecords.cfg (NPStackSourceRecords.atIndex 8 0) input [] (fun _ => []))
      (cfg (.source (NPStackSourceRecords.atIndex 8 0)) input cert (fun _ => [])) :=
    ⟨rfl,by intro k;cases k <;> rfl⟩
  obtain ⟨d,hd,hdr,_⟩ := he.relocate sourceMap State.source sourceMap_injective source_code hrel
  refine ⟨t,ht,d,hd,?_⟩
  rw [hdr.1]
  exact source_reject_code e.pc hh

lemma reject_certificate (s : Fin 8 → List Bool) (source input : List Bool)
    (hb : NPStackSourceRecords.parseFixed 2 input=none) :
    ∃ t ≤ 2*(5*input.length+5),∃ d,Run program t
      (cfg (.certificate (NPStackSourceRecords.atIndex 2 0)) source input (sourceValues s)) d ∧ program.code d.pc=.halt false := by
  obtain ⟨t,ht,e,he,hh⟩ := NPStackSourceRecords.reject_malformed 2 input hb
  have hrel : Relocated certificateMap State.certificate
      (NPStackSourceRecords.cfg (NPStackSourceRecords.atIndex 2 0) input [] (fun _ => []))
      (cfg (.certificate (NPStackSourceRecords.atIndex 2 0)) source input (sourceValues s)) := by
    refine ⟨rfl,?_⟩;intro k;cases k <;>
      simp [certificateMap,cfg,store,NPStackSourceRecords.cfg,NPStackSourceRecords.store]
  obtain ⟨d,hd,hdr,_⟩ := he.relocate certificateMap State.certificate certificateMap_injective certificate_code hrel
  refine ⟨t,ht,d,hd,?_⟩
  rw [hdr.1]
  exact certificate_reject_code e.pc hh

/-- Every accepted prefix has exactly eight source fields and two certificate
fields, with exact unconsumed tails and all other workspace initialized. -/
theorem accepting_result (source certificate : List Bool) {T : ℕ} {d : Config SourceVerifier.Stack State}
    (hr : Run program T (cfg (.source (NPStackSourceRecords.atIndex 8 0)) source certificate (fun _ => [])) d)
    (ha : accepts program d) :
    ∃ s : Fin 8 → List Bool,∃ c : Fin 2 → List Bool,∃ sr cr,
      NPStackSourceRecords.parseFixed 8 source=some (List.ofFn s,sr) ∧
      NPStackSourceRecords.parseFixed 2 certificate=some (List.ofFn c,cr) ∧
      d=cfg .done sr cr (preparedValues s c) ∧ T=headerCost s c := by
  cases hs : NPStackSourceRecords.parseFixed 8 source with
  | none =>
    obtain ⟨t,_,e,he,hh⟩ := reject_source source certificate hs
    exact False.elim (rejecting_run_excludes_acceptance program_deterministic he hh hr ha)
  | some p =>
    rcases p with ⟨sf,sr⟩
    obtain ⟨s,hsof,_⟩ := NPStackSourceRecords.parseFixed_run 8 source sf sr hs
    have hsource := (NPStackSourceRecords.parseFixed_sound 8 source sf sr hs).2
    rw [←hsof] at hsource
    have hprefix := source_prefix s sr certificate
    rw [←hsource] at hprefix
    obtain ⟨u,_,hu⟩ := (hprefix.deterministic program_noChoice).factor_halted hr ha
    cases hc : NPStackSourceRecords.parseFixed 2 certificate with
    | none =>
      obtain ⟨t,_,e,he,hh⟩ := reject_certificate s sr certificate hc
      exact False.elim (rejecting_run_excludes_acceptance program_deterministic he hh hu ha)
    | some p =>
      rcases p with ⟨cf,cr⟩
      obtain ⟨c,hcof,_⟩ := NPStackSourceRecords.parseFixed_run 2 certificate cf cr hc
      have hcertificate := (NPStackSourceRecords.parseFixed_sound 2 certificate cf cr hc).2
      rw [←hcof] at hcertificate
      have hknown := header_run s c sr cr
      rw [←hsource,←hcertificate] at hknown
      have he := hknown.halted_unique program_deterministic hr rfl ha
      exact ⟨s,c,sr,cr,by rw [hsof],by rw [hcof],he.2.symm,he.1.symm⟩

@[simp] lemma prepared_source (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) (i : Fin 8) :
    preparedValues s c (sourceHeader i)=s i := by
  fin_cases i <;> simp [preparedValues,rankDen,revenueDen,one,sourceHeader,headerValues,sourceValues,certificateHeader]
@[simp] lemma prepared_certificate (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) (i : Fin 2) :
    preparedValues s c (certificateHeader i)=c i := by
  have h1 : certificateHeader i≠rankDen := by fin_cases i <;> decide
  have h2 : certificateHeader i≠revenueDen := by fin_cases i <;> decide
  have h3 : certificateHeader i≠one := by fin_cases i <;> decide
  simp only [preparedValues,Function.update_of_ne h3,Function.update_of_ne h2,Function.update_of_ne h1,headerValues_certificate]
@[simp] lemma prepared_rankDen (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) : preparedValues s c rankDen=[true] := by
  simp [preparedValues,rankDen,revenueDen,one]
@[simp] lemma prepared_revenueDen (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) : preparedValues s c revenueDen=[true] := by
  simp [preparedValues,rankDen,revenueDen,one]
@[simp] lemma prepared_one (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) : preparedValues s c one=[true] := by
  simp [preparedValues]

lemma prepared_other (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) (k : BodyStack)
    (hs : ∀ i,sourceHeader i≠k) (hc : ∀ i,certificateHeader i≠k)
    (hr : rankDen≠k) (hv : revenueDen≠k) (ho : one≠k) : preparedValues s c k=[] := by
  simp [preparedValues,Function.update_of_ne hr.symm,Function.update_of_ne hv.symm,Function.update_of_ne ho.symm,
    headerValues_frame s c k hc,sourceValues_outside s k hs]

lemma headerCost_formula (s : Fin 8 → List Bool) (c : Fin 2 → List Bool) :
    headerCost s c=5*((List.ofFn s).map List.length).sum+5*((List.ofFn c).map List.length).sum+35 := by
  simp only [headerCost,NPStackSourceRecords.recordCost_formula,List.length_ofFn]
  omega

end BalancedAssortments.NPStack.SourceVerifier.Header
