import BalancedAssortments.NPStackSourceBalanceLoop

namespace BalancedAssortments.NPStack.SourceVerifier.Balance
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl NPStackFields

def stream (xs : List Triple) : List Bool := dataFields (xs.flatMap List.ofFn)
@[simp] lemma stream_nil : stream []=[] := rfl
@[simp] lemma stream_cons (x : Triple) (xs : List Triple) : stream (x::xs)=dataFields (List.ofFn x)++stream xs := by
  simp [stream,dataFields,List.flatMap_append]

def stepValue (s : Registers) (x : Triple) : Option Registers := do
  let active ← NPStackMask.maskValue (x 0)
  if (eval (VerifierCommands.balanceCommand active) (loaded s x)).1 then
    some (effect active (loaded s x)) else none

def loopValue : Registers → List Triple → Option Registers
  | s,[] => some s
  | s,x::xs => (stepValue s x).bind (fun t=>loopValue t xs)

lemma clearCost_stream (s : Registers) (a b : List Bool) :
    ClearRows.clearCost ClearRows.rowKeys (packedStore s [] a)=
      ClearRows.clearCost ClearRows.rowKeys (packedStore s [] b) := by
  simp [ClearRows.clearCost,ClearRows.rowKeys,List.finRange,packedStore,arithmeticInverse,arithmeticMap,extraStore]

def rowCost (s : Registers) (x : Triple) (active : Bool) : ℕ :=
  NPStackSourceRecords.recordCost (List.ofFn x)+(x 0).length+10+
    budget VerifierCommands.compareTime (VerifierCommands.balanceCommand active) (loaded s x)+
    ClearRows.clearCost ClearRows.rowKeys (packedStore (effect active (loaded s x)) [] [])

def loopCost : Registers → List Triple → ℕ
  | _,[] => 1
  | s,x::xs => match NPStackMask.maskValue (x 0) with
    | none => 0
    | some active => rowCost s x active + loopCost (effect active (loaded s x)) xs

lemma row_success (s : Registers) (x : Triple) (tail : List Bool) (active : Bool)
    (hm : NPStackMask.maskValue (x 0)=some active)
    (ha : (eval (VerifierCommands.balanceCommand active) (loaded s x)).1=true) :
    ∃ t≤rowCost s x active,Run loopProgram t ⟨.probe,stable s (dataFields (List.ofFn x)++tail)⟩
      ⟨.probe,stable (effect active (loaded s x)) tail⟩ := by
  obtain ⟨t,ht,hr⟩ := body_row_run (loaded s x) (x 0) tail active hm ha
  have hb := hr.relocate_exact id LoopState.body Function.injective_id body_loop_extends
    (c':=⟨.body bodyProgram.start,packedStore (loaded s x) (x 0) tail⟩)
    (d':=⟨.body (.inr (ClearRows.clearDone ClearRows.rowKeys)),stable (effect active (loaded s x)) tail⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩ (by intro k hk;exact (hk k rfl).elim)
  have hi : Step loopProgram ⟨.read .accept,packedStore (loaded s x) (x 0) tail⟩
      ⟨.body bodyProgram.start,packedStore (loaded s x) (x 0) tail⟩ := by simp [Step,successors,loopProgram]
  have ho : Step loopProgram
      ⟨.body (.inr (ClearRows.clearDone ClearRows.rowKeys)),stable (effect active (loaded s x)) tail⟩
      ⟨.probe,stable (effect active (loaded s x)) tail⟩ := by
    simp [Step,successors,loopProgram,bodyProgram,ClearRows.finishProgram,ClearRows.clearDone_halts,Instr.rename]
  refine ⟨_,?_,((probe_triple s x tail).trans (extract_triple s x tail)).trans ((Run.one hi).trans (hb.trans (.one ho)))⟩
  rw [clearCost_stream _ tail []] at ht
  unfold rowCost
  omega

lemma body_reject (s : Registers) (x : Triple) (tail : List Bool)
    (h : stepValue s x=none) :
    ∃ t e,Run bodyProgram t ⟨bodyProgram.start,packedStore (loaded s x) (x 0) tail⟩ e ∧ bodyProgram.code e.pc=.halt false := by
  have hinner : ∃ t e,Run innerProgram t ⟨innerProgram.start,packedStore (loaded s x) (x 0) tail⟩ e ∧ innerProgram.code e.pc=.halt false := by
    cases hm : NPStackMask.maskValue (x 0) with
    | none => exact inner_bad_mask _ _ _ hm
    | some active =>
      have ha : (eval (VerifierCommands.balanceCommand active) (loaded s x)).1=false := by
        simpa [stepValue,hm] using h
      exact inner_bad_guard _ _ _ active hm ha
  obtain ⟨t,e,hr,he⟩ := hinner
  refine ⟨t,⟨.inl e.pc,e.stk⟩,?_,?_⟩
  · exact hr.relocate_exact id Sum.inl Function.injective_id (ClearRows.body_extends innerProgram ClearRows.rowKeys)
      ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩ (by intro k hk;exact (hk k rfl).elim)
  · simp [bodyProgram,ClearRows.finishProgram,he]

lemma row_reject (s : Registers) (x : Triple) (tail : List Bool)
    (h : stepValue s x=none) :
    ∃ t e,Run loopProgram t ⟨.probe,stable s (dataFields (List.ofFn x)++tail)⟩ e ∧ loopProgram.code e.pc=.halt false := by
  obtain ⟨t,e,hr,he⟩ := body_reject s x tail h
  have hb := hr.relocate_exact id LoopState.body Function.injective_id body_loop_extends
    (c':=⟨.body bodyProgram.start,packedStore (loaded s x) (x 0) tail⟩)
    (d':=⟨.body e.pc,e.stk⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩ (by intro k hk;exact (hk k rfl).elim)
  have hi : Step loopProgram ⟨.read .accept,packedStore (loaded s x) (x 0) tail⟩
      ⟨.body bodyProgram.start,packedStore (loaded s x) (x 0) tail⟩ := by simp [Step,successors,loopProgram]
  exact ⟨_,_,((probe_triple s x tail).trans (extract_triple s x tail)).trans ((Run.one hi).trans hb),by simp [loopProgram,he]⟩

lemma stepValue_some (s : Registers) (x : Triple) (u : Registers) (h : stepValue s x=some u) :
    ∃ active,NPStackMask.maskValue (x 0)=some active ∧
      (eval (VerifierCommands.balanceCommand active) (loaded s x)).1=true ∧ u=effect active (loaded s x) := by
  cases hm : NPStackMask.maskValue (x 0) with
  | none => simp [stepValue,hm] at h
  | some active =>
    cases ha : (eval (VerifierCommands.balanceCommand active) (loaded s x)).1 with
    | false => simp [stepValue,hm,ha] at h
    | true =>
      have he : effect active (loaded s x)=u := by simpa [stepValue,hm,ha] using h
      exact ⟨active,rfl,ha,he.symm⟩

theorem loop_success (s u : Registers) (xs : List Triple) (h : loopValue s xs=some u) :
    ∃ t≤loopCost s xs,Run loopProgram t ⟨.probe,stable s (stream xs)⟩ ⟨.accept,stable u []⟩ := by
  induction xs generalizing s with
  | nil =>
    have he : s=u := Option.some.inj h
    subst s
    refine ⟨1,by simp [loopCost],Run.one ?_⟩
    simp [Step,successors,loopProgram,stable_balance]
  | cons x xs ih =>
    cases hs : stepValue s x with
    | none => simp [loopValue,hs] at h
    | some v =>
      have ht : loopValue v xs=some u := by simpa [loopValue,hs] using h
      obtain ⟨active,hm,ha,rfl⟩ := stepValue_some s x v hs
      obtain ⟨a,hab,har⟩ := row_success s x (stream xs) active hm ha
      obtain ⟨b,hbb,hbr⟩ := ih _ ht
      exact ⟨a+b,by simp [loopCost,hm];omega,by simpa only [stream_cons] using har.trans hbr⟩

theorem loop_reject (s : Registers) (xs : List Triple) (h : loopValue s xs=none) :
    ∃ t e,Run loopProgram t ⟨.probe,stable s (stream xs)⟩ e ∧ loopProgram.code e.pc=.halt false := by
  induction xs generalizing s with
  | nil => simp [loopValue] at h
  | cons x xs ih =>
    cases hs : stepValue s x with
    | none => simpa only [stream_cons] using row_reject s x (stream xs) hs
    | some v =>
      have ht : loopValue v xs=none := by simpa [loopValue,hs] using h
      obtain ⟨active,hm,ha,rfl⟩ := stepValue_some s x v hs
      obtain ⟨a,_,har⟩ := row_success s x (stream xs) active hm ha
      obtain ⟨b,e,hbr,he⟩ := ih _ ht
      exact ⟨a+b,e,by simpa only [stream_cons] using har.trans hbr,he⟩

theorem loop_accepting_result (s : Registers) (xs : List Triple) {t : ℕ} {out : Config BodyStack LoopState}
    (hr : Run loopProgram t ⟨.probe,stable s (stream xs)⟩ out) (ha : accepts loopProgram out) :
    ∃ u,loopValue s xs=some u ∧ out=⟨.accept,stable u []⟩ ∧ t≤loopCost s xs := by
  cases h : loopValue s xs with
  | none =>
    obtain ⟨v,e,he,hh⟩ := loop_reject s xs h
    exact (rejecting_run_excludes_acceptance (noChoice_deterministic loop_noChoice) he hh hr ha).elim
  | some u =>
    obtain ⟨v,hv,hvr⟩ := loop_success s u xs h
    have he := hr.halted_unique (noChoice_deterministic loop_noChoice) hvr ha (by rfl)
    exact ⟨u,rfl,he.2,he.1 ▸ hv⟩

end BalancedAssortments.NPStack.SourceVerifier.Balance
