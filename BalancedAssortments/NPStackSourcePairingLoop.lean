import BalancedAssortments.NPStackSourcePairing

namespace BalancedAssortments.NPStackSourcePairing
open NPStack
open NPStackFields (dataFields)
variable {W Q : Type*} [DecidableEq W]

abbrev PairRecord := (Fin 6 → List Bool) × (Fin 3 → List Bool)

def sourceStream (records : List PairRecord) : List Bool :=
  dataFields (records.flatMap (fun r => List.ofFn r.1))
def certificateStream (records : List PairRecord) : List Bool :=
  dataFields (records.flatMap (fun r => List.ofFn r.2))

def recordOverhead (r : PairRecord) : ℕ :=
  NPStackSourceRecords.recordCost (List.ofFn r.1)+NPStackSourceRecords.recordCost (List.ofFn r.2)+5

/-- The rows carry actual executions of the supplied finite body, including
its workspace changes, return state and exact primitive transition count. -/
inductive BodyRuns (body : Program (Fin 9 ⊕ W) Q) :
    List PairRecord → (W → List Bool) → (W → List Bool) → ℕ → Prop
  | nil (work) : BodyRuns body [] work work 0
  | cons {r rs work next finish t u q} :
      Run body t ⟨body.start,rowStore (pairedRow r.1 r.2) work⟩ ⟨q,rowStore (fun _ => []) next⟩ →
      body.code q=.halt true → BodyRuns body rs next finish u →
      BodyRuns body (r::rs) work finish (recordOverhead r+t+u)

lemma finish_pairing (body : Program (Fin 9 ⊕ W) Q) (work : W → List Bool) :
    Run (program body) 2 (cfg .probe [] [] [] (fun _ => []) work)
      (cfg .accept [] [] [] (fun _ => []) work) := by
  have h1 : Step (program body) (cfg .probe [] [] [] (fun _ => []) work)
      (cfg .exhausted [] [] [] (fun _ => []) work) := by simp [Step,successors,program,cfg,store]
  have h2 : Step (program body) (cfg .exhausted [] [] [] (fun _ => []) work)
      (cfg .accept [] [] [] (fun _ => []) work) := by simp [Step,successors,program,cfg,store]
  exact .succ h1 (.one h2)

/-- Structural iteration consumes one six-field source record and one
three-field certificate record per supplied finite body execution. -/
theorem loop_run (body : Program (Fin 9 ⊕ W) Q) {records : List PairRecord}
    {work finish : W → List Bool} {t : ℕ} (h : BodyRuns body records work finish t) :
    Run (program body) (t+2)
      (cfg .probe (sourceStream records) (certificateStream records) [] (fun _ => []) work)
      (cfg .accept [] [] [] (fun _ => []) finish) := by
  induction h with
  | nil work => simpa [sourceStream,certificateStream,dataFields] using finish_pairing body work
  | @cons r rs work next finish t u q hr ha htail ih =>
    have hrow := paired_record body r.1 r.2 work next (sourceStream rs) (certificateStream rs) hr ha
    have hall := hrow.trans ih
    simpa [sourceStream,certificateStream,dataFields,List.flatMap_append,recordOverhead,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall

/-- Primitive structural overhead per row, independent of the encoded numeric
values and the source's declared count. -/
lemma recordOverhead_formula (r : PairRecord) :
    recordOverhead r=5*((List.ofFn r.1).map List.length).sum+
      5*((List.ofFn r.2).map List.length).sum+32 := by
  simp [recordOverhead,NPStackSourceRecords.recordCost_formula]
  omega

/-- An explicitly counted body trace with a uniform body bound yields a
polynomial wrapper bound; the actual body costs remain visible in BodyRuns. -/
inductive BoundedBodyRuns (body : Program (Fin 9 ⊕ W) Q) (B : ℕ) :
    List PairRecord → (W → List Bool) → (W → List Bool) → Prop
  | nil (work) : BoundedBodyRuns body B [] work work
  | cons {r rs work next finish t q} : t≤B →
      Run body t ⟨body.start,rowStore (pairedRow r.1 r.2) work⟩ ⟨q,rowStore (fun _ => []) next⟩ →
      body.code q=.halt true → BoundedBodyRuns body B rs next finish →
      BoundedBodyRuns body B (r::rs) work finish

lemma bounded_trace (body : Program (Fin 9 ⊕ W) Q) (B : ℕ) {records : List PairRecord}
    {work finish : W → List Bool} (h : BoundedBodyRuns body B records work finish) :
    ∃ t≤(records.map recordOverhead).sum+records.length*B,BodyRuns body records work finish t := by
  induction h with
  | nil work => exact ⟨0,by simp,.nil work⟩
  | cons ht hr ha htail ih =>
    obtain ⟨u,hu,htrace⟩ := ih
    refine ⟨_,?_,.cons hr ha htrace⟩
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

theorem bounded_loop (body : Program (Fin 9 ⊕ W) Q) (B : ℕ) {records : List PairRecord}
    {work finish : W → List Bool} (h : BoundedBodyRuns body B records work finish) :
    ∃ t≤(records.map recordOverhead).sum+records.length*B+2,
      Run (program body) t (cfg .probe (sourceStream records) (certificateStream records) [] (fun _ => []) work)
        (cfg .accept [] [] [] (fun _ => []) finish) := by
  obtain ⟨t,ht,htrace⟩ := bounded_trace body B h
  exact ⟨t+2,by omega,loop_run body htrace⟩

/-- A leftover certificate record cannot be silently ignored at source EOF. -/
lemma reject_extra_certificate (body : Program (Fin 9 ⊕ W) Q) (b : Bool) (rest : List Bool)
    (work : W → List Bool) :
    Run (program body) 2 (cfg .probe [] (b::rest) [] (fun _ => []) work)
      (cfg .reject [] rest [] (fun _ => []) work) := by
  have h1 : Step (program body) (cfg .probe [] (b::rest) [] (fun _ => []) work)
      (cfg .exhausted [] (b::rest) [] (fun _ => []) work) := by simp [Step,successors,program,cfg,store]
  have h2 : Step (program body) (cfg .exhausted [] (b::rest) [] (fun _ => []) work)
      (cfg .reject [] rest [] (fun _ => []) work) := by
    cases b <;> simp [Step,successors,program,cfg,store] <;> funext k <;> cases k <;> simp [store]
  exact .succ h1 (.one h2)

end BalancedAssortments.NPStackSourcePairing
