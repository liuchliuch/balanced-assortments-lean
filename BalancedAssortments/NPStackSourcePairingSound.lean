import BalancedAssortments.NPStackSourcePairingPrefix

namespace BalancedAssortments.NPStackSourcePairing
open NPStack
open NPStackFields (dataFields)
variable {W Q : Type*} [DecidableEq W]

/-- The concrete row routine releases its nine input registers on successful
return. This is a bytecode contract, not an abstract numerical verifier. -/
def ClearsRows (body : Program (Fin 9 ⊕ W) Q) : Prop :=
  ∀ row work t e,Run body t ⟨body.start,rowStore row work⟩ e → accepts body e →
    ∀ i,e.stk (.inl i)=[]

lemma finish_deterministic (body : Program (Fin 9 ⊕ W) Q) (work : W → List Bool) :
    DeterministicRun (program body) 2 (cfg .probe [] [] [] (fun _ => []) work)
      (cfg .accept [] [] [] (fun _ => []) work) := by
  have h1 : Step (program body) (cfg .probe [] [] [] (fun _ => []) work)
      (cfg .exhausted [] [] [] (fun _ => []) work) := by simp [Step,successors,program,cfg,store]
  have h2 : Step (program body) (cfg .exhausted [] [] [] (fun _ => []) work)
      (cfg .accept [] [] [] (fun _ => []) work) := by simp [Step,successors,program,cfg,store]
  exact .succ (uniqueStep_of_code (by intro q r;simp [program,cfg])) h1
    (.one (uniqueStep_of_code (by intro q r;simp [program,cfg])) h2)

lemma extra_certificate_deterministic (body : Program (Fin 9 ⊕ W) Q) (b : Bool) (rest : List Bool)
    (work : W → List Bool) :
    DeterministicRun (program body) 2 (cfg .probe [] (b::rest) [] (fun _ => []) work)
      (cfg .reject [] rest [] (fun _ => []) work) := by
  have h1 : Step (program body) (cfg .probe [] (b::rest) [] (fun _ => []) work)
      (cfg .exhausted [] (b::rest) [] (fun _ => []) work) := by simp [Step,successors,program,cfg,store]
  have h2 : Step (program body) (cfg .exhausted [] (b::rest) [] (fun _ => []) work)
      (cfg .reject [] rest [] (fun _ => []) work) := by
    cases b <;> simp [Step,successors,program,cfg,store] <;> funext k <;> cases k <;> simp [store]
  exact .succ (uniqueStep_of_code (by intro q r;simp [program,cfg])) h1
    (.one (uniqueStep_of_code (by intro q r;simp [program,cfg])) h2)

/-- Every accepting wrapper execution consumes exactly paired six/three
records and consists of actual accepting body runs. Malformed fields, truncated
records and unequal record counts cannot be hidden by a time bound or caller
nondeterminism. The exact total transition count is recovered. -/
theorem accepting_trace (body : Program (Fin 9 ⊕ W) Q) (hclear : ClearsRows body)
    (input cert : List Bool) (work : W → List Bool) {T : ℕ} {d : Config (Stack W) (State Q)}
    (hr : Run (program body) T (cfg .probe input cert [] (fun _ => []) work) d)
    (ha : accepts (program body) d) :
    ∃ records finish t,sourceStream records=input ∧ certificateStream records=cert ∧
      BodyRuns body records work finish t ∧ d=cfg .accept [] [] [] (fun _ => []) finish ∧ T=t+2 := by
  generalize hn : input.length=n
  induction n using Nat.strong_induction_on generalizing input cert work T d with
  | h n ih =>
    cases input with
    | nil =>
      cases cert with
      | nil =>
        obtain ⟨u,ht,hu⟩ := (finish_deterministic body work).factor_halted hr ha
        have he := hu.from_halted (show (program body).code (cfg .accept [] [] [] (fun _ => []) work).pc=.halt true from rfl)
        refine ⟨[],work,0,rfl,rfl,.nil work,he.2.symm,?_⟩
        omega
      | cons b bs =>
        exact False.elim (deterministic_reject (extra_certificate_deterministic body b bs work) rfl hr ha)
    | cons b bits =>
      obtain ⟨u,ht0,hsource⟩ := (probe_deterministic body b bits cert work).factor_halted hr ha
      cases hs : NPStackSourceRecords.parseFixed 6 (b::bits) with
      | none => exact False.elim (bad_source_excludes_acceptance body (b::bits) cert work hs hsource ha)
      | some ps =>
        rcases ps with ⟨sf,srest⟩
        obtain ⟨s,hsof,_⟩ := NPStackSourceRecords.parseFixed_run 6 (b::bits) sf srest hs
        have hsrc := (NPStackSourceRecords.parseFixed_sound 6 (b::bits) sf srest hs).2
        rw [←hsof] at hsrc
        have hsp := (extract_source_deterministic body s srest cert work).trans (source_jump body s srest cert work)
        rw [←hsrc] at hsp
        obtain ⟨v,ht1,hcert⟩ := hsp.factor_halted hsource ha
        cases hc : NPStackSourceRecords.parseFixed 3 cert with
        | none => exact False.elim (bad_certificate_excludes_acceptance body s srest cert work hc hcert ha)
        | some pc =>
          rcases pc with ⟨cf,crest⟩
          obtain ⟨c,hcof,_⟩ := NPStackSourceRecords.parseFixed_run 3 cert cf crest hc
          have hcrt := (NPStackSourceRecords.parseFixed_sound 3 cert cf crest hc).2
          rw [←hcof] at hcrt
          have hcp := (extract_certificate_deterministic body s c srest crest work).trans
            (certificate_jump body s c srest crest work)
          rw [←hcrt] at hcp
          obtain ⟨z,ht2,hbody⟩ := hcp.factor_halted hcert ha
          obtain ⟨a,z',e,he,hhalt,hrest,ht3⟩ := body_segment body srest crest []
            ⟨body.start,rowStore (pairedRow s c) work⟩ hbody ha
          have hz : (fun i => e.stk (.inl i))=(fun _ => []) := funext (hclear (pairedRow s c) work a e he hhalt)
          rw [hz] at hrest
          let next := fun w => e.stk (.inr w)
          have heq : e=⟨e.pc,rowStore (fun _ => []) next⟩ := by
            cases e with
            | mk q stk =>
              congr 1
              funext k;cases k with
              | inl i => exact congrFun hz i
              | inr w => rfl
          have hshort : srest.length<n := by
            have hh := NPStackSourceRecords.parseFixed_suffix_shorter 6 (by omega) (b::bits) sf srest hs
            simpa [hn] using hh
          obtain ⟨records,finish,t,hsr,hcr,htrace,hfinal,ht4⟩ :=
            ih srest.length hshort srest crest next hrest ha rfl
          refine ⟨(s,c)::records,finish,recordOverhead (s,c)+a+t,?_,?_,?_,hfinal,?_⟩
          · simp only [sourceStream,List.flatMap_cons,dataFields,List.flatMap_append]
            change dataFields (List.ofFn s)++sourceStream records=b::bits
            rw [hsr,←hsrc]
          · simp only [certificateStream,List.flatMap_cons,dataFields,List.flatMap_append]
            change dataFields (List.ofFn c)++certificateStream records=cert
            rw [hcr,←hcrt]
          · apply BodyRuns.cons (q:=e.pc) (t:=a)
            · rw [heq] at he
              exact he
            · exact hhalt
            · exact htrace
          · unfold recordOverhead
            dsimp only [Prod.fst,Prod.snd]
            omega

end BalancedAssortments.NPStackSourcePairing
