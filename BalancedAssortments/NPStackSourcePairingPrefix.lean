import BalancedAssortments.NPStackSourcePairingBody
import BalancedAssortments.NPStackEmbeddingDeterministic

namespace BalancedAssortments.NPStackSourcePairing
open NPStack
open NPStackFields (dataFields)
variable {W Q : Type*} [DecidableEq W]

lemma record_noChoice (m : ℕ) : NoChoice (NPStackSourceRecords.program m) := by
  intro q a b
  cases q with
  | accept => simp [NPStackSourceRecords.program]
  | field i q => cases q <;> simp [NPStackSourceRecords.program,NPStackFieldData.readProgram,Instr.rename]

lemma call_deterministic {m : ℕ} (body : Program (Fin 9 ⊕ W) Q)
    (fk : NPStackSourceRecords.Stack m → Stack W) (fq : NPStackSourceRecords.State m → State Q)
    (hinj : Function.Injective fk) (hc : CodeExtends (NPStackSourceRecords.program m) (program body) fk fq)
    {t : ℕ} {a b : Config (NPStackSourceRecords.Stack m) (NPStackSourceRecords.State m)}
    {c d : Config (Stack W) (State Q)} (hr : Run (NPStackSourceRecords.program m) t a b)
    (ha : Relocated fk fq a c) (hb : Relocated fk fq b d) (hf : Frame fk c d) :
    DeterministicRun (program body) t c d :=
  hr.relocate_deterministic_exact (record_noChoice m) fk fq hinj hc ha hb hf

lemma extract_source_deterministic (body : Program (Fin 9 ⊕ W) Q) (s : Fin 6 → List Bool)
    (srest cert : List Bool) (work : W → List Bool) :
    DeterministicRun (program body) (NPStackSourceRecords.recordCost (List.ofFn s))
      (cfg (.source (NPStackSourceRecords.atIndex 6 0)) (dataFields (List.ofFn s)++srest) cert [] (fun _ => []) work)
      (cfg (.source .accept) srest cert [] (sourceRow s) work) := by
  apply call_deterministic body sourceStack State.source source_injective (source_code body)
    (NPStackSourceRecords.extract_record s srest)
  · refine ⟨rfl,?_⟩;intro k;cases k <;> rfl
  · refine ⟨rfl,?_⟩;intro k;cases k <;> simp [sourceStack,cfg,store,rowStore,sourceRow,sourceIndex,NPStackSourceRecords.cfg,NPStackSourceRecords.store]
  · intro k hk
    cases k with
    | source => exact (hk .input rfl).elim
    | scratch => exact (hk .scratch rfl).elim
    | certificate => rfl
    | body k =>
      cases k with
      | inr w => rfl
      | inl i =>
        have hn : ¬i.val < 6 := by
          intro hi
          exact hk (.field ⟨i.val,hi⟩) (by congr 2)
        simp [cfg,store,rowStore,sourceRow,hn]

lemma extract_certificate_deterministic (body : Program (Fin 9 ⊕ W) Q) (s : Fin 6 → List Bool)
    (c : Fin 3 → List Bool) (srest crest : List Bool) (work : W → List Bool) :
    DeterministicRun (program body) (NPStackSourceRecords.recordCost (List.ofFn c))
      (cfg (.certificate (NPStackSourceRecords.atIndex 3 0)) srest (dataFields (List.ofFn c)++crest) [] (sourceRow s) work)
      (cfg (.certificate .accept) srest crest [] (pairedRow s c) work) := by
  apply call_deterministic body certificateStack State.certificate certificate_injective (certificate_code body)
    (NPStackSourceRecords.extract_record c crest)
  · refine ⟨rfl,?_⟩;intro k;cases k <;> simp [certificateStack,cfg,store,rowStore,sourceRow,certificateIndex,NPStackSourceRecords.cfg,NPStackSourceRecords.store]
  · refine ⟨rfl,?_⟩;intro k;cases k <;> simp [certificateStack,cfg,store,rowStore,pairedRow,certificateIndex,NPStackSourceRecords.cfg,NPStackSourceRecords.store]
  · intro k hk
    cases k with
    | source => rfl
    | scratch => exact (hk .scratch rfl).elim
    | certificate => exact (hk .input rfl).elim
    | body k =>
      cases k with
      | inr w => rfl
      | inl i =>
        have hi : i.val < 6 := by
          by_contra hn
          have he : certificateIndex ⟨i.val-6,by omega⟩=i := by apply Fin.ext;simp [certificateIndex];omega
          exact hk (.field ⟨i.val-6,by omega⟩) (by simp [certificateStack,he])
        simp [cfg,store,rowStore,pairedRow,sourceRow,hi]
lemma probe_deterministic (body : Program (Fin 9 ⊕ W) Q) (b : Bool) (rest cert : List Bool)
    (work : W → List Bool) :
    DeterministicRun (program body) 2 (cfg .probe (b::rest) cert [] (fun _ => []) work)
      (cfg (.source (NPStackSourceRecords.atIndex 6 0)) (b::rest) cert [] (fun _ => []) work) := by
  have h1 : Step (program body) (cfg .probe (b::rest) cert [] (fun _ => []) work)
      (cfg (.restore b) rest cert [] (fun _ => []) work) := by
    cases b <;> simp [Step,successors,program,cfg,store] <;> funext k <;> cases k <;> simp [store]
  have h2 : Step (program body) (cfg (.restore b) rest cert [] (fun _ => []) work)
      (cfg (.source (NPStackSourceRecords.atIndex 6 0)) (b::rest) cert [] (fun _ => []) work) := by
    simp [Step,successors,program,cfg,store];funext k;cases k <;> simp [store]
  exact .succ (uniqueStep_of_code (by intro q r;simp [program,cfg])) h1
    (.one (uniqueStep_of_code (by intro q r;simp [program,cfg])) h2)

lemma source_jump (body : Program (Fin 9 ⊕ W) Q) (s : Fin 6 → List Bool)
    (srest cert : List Bool) (work : W → List Bool) :
    DeterministicRun (program body) 1 (cfg (.source .accept) srest cert [] (sourceRow s) work)
      (cfg (.certificate (NPStackSourceRecords.atIndex 3 0)) srest cert [] (sourceRow s) work) := by
  apply DeterministicRun.one
  · apply uniqueStep_of_code;intro q r;simp [program,cfg]
  · simp [Step,successors,program,cfg]

lemma certificate_jump (body : Program (Fin 9 ⊕ W) Q) (s : Fin 6 → List Bool) (c : Fin 3 → List Bool)
    (srest crest : List Bool) (work : W → List Bool) :
    DeterministicRun (program body) 1 (cfg (.certificate .accept) srest crest [] (pairedRow s c) work)
      (cfg (.body body.start) srest crest [] (pairedRow s c) work) := by
  apply DeterministicRun.one
  · apply uniqueStep_of_code;intro q r;simp [program,cfg]
  · simp [Step,successors,program,cfg]

lemma deterministic_reject {P : Program (Stack W) (State Q)} {a b : ℕ}
    {c d e : Config (Stack W) (State Q)} (h : DeterministicRun P a c d)
    (hd : P.code d.pc=.halt false) (hr : Run P b c e) (ha : accepts P e) : False := by
  obtain ⟨t,_,ht⟩ := h.factor_halted hr ha
  have he := ht.from_halted hd
  rw [he.2] at hd
  rw [ha] at hd
  cases hd

lemma bad_source_excludes_acceptance (body : Program (Fin 9 ⊕ W) Q) (input cert : List Bool)
    (work : W → List Bool) (hbad : NPStackSourceRecords.parseFixed 6 input=none)
    {T : ℕ} {d : Config (Stack W) (State Q)}
    (hr : Run (program body) T (cfg (.source (NPStackSourceRecords.atIndex 6 0)) input cert [] (fun _ => []) work) d)
    (ha : accepts (program body) d) : False := by
  obtain ⟨t,_,e,he,hehalt⟩ := NPStackSourceRecords.reject_malformed 6 input hbad
  have hrel : Relocated sourceStack (State.source (Q:=Q))
      (NPStackSourceRecords.cfg (NPStackSourceRecords.atIndex 6 0) input [] (fun _ => []))
      (cfg (.source (NPStackSourceRecords.atIndex 6 0)) input cert [] (fun _ => []) work) := by
    exact ⟨rfl,by intro k;cases k <;> rfl⟩
  obtain ⟨e',hp,hpe,_⟩ := he.relocate_deterministic (record_noChoice 6) sourceStack State.source
    source_injective (source_code body) hrel
  apply deterministic_reject hp _ hr ha
  rw [hpe.1]
  exact source_reject_code body e.pc hehalt

lemma bad_certificate_excludes_acceptance (body : Program (Fin 9 ⊕ W) Q) (s : Fin 6 → List Bool)
    (srest input : List Bool) (work : W → List Bool) (hbad : NPStackSourceRecords.parseFixed 3 input=none)
    {T : ℕ} {d : Config (Stack W) (State Q)}
    (hr : Run (program body) T (cfg (.certificate (NPStackSourceRecords.atIndex 3 0)) srest input [] (sourceRow s) work) d)
    (ha : accepts (program body) d) : False := by
  obtain ⟨t,_,e,he,hehalt⟩ := NPStackSourceRecords.reject_malformed 3 input hbad
  have hrel : Relocated certificateStack (State.certificate (Q:=Q))
      (NPStackSourceRecords.cfg (NPStackSourceRecords.atIndex 3 0) input [] (fun _ => []))
      (cfg (.certificate (NPStackSourceRecords.atIndex 3 0)) srest input [] (sourceRow s) work) := by
    refine ⟨rfl,?_⟩;intro k;cases k <;>
      simp [certificateStack,cfg,store,rowStore,sourceRow,certificateIndex,NPStackSourceRecords.cfg,NPStackSourceRecords.store]
  obtain ⟨e',hp,hpe,_⟩ := he.relocate_deterministic (record_noChoice 3) certificateStack State.certificate
    certificate_injective (certificate_code body) hrel
  apply deterministic_reject hp _ hr ha
  rw [hpe.1]
  exact certificate_reject_code body e.pc hehalt

end BalancedAssortments.NPStackSourcePairing
