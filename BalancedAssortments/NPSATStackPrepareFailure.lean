import BalancedAssortments.NPSATStackPrepareSuccess

namespace BalancedAssortments.NPSATStackPrepare
open NPStack NPStack.Macros NPCNF.Encoding NPStackFields

lemma framing_failure (bits : List Bool) (hp : (EncodingTime.parse bits).1=none) :
    ∃t s,Run program t (initial program bits) ⟨.reject,s⟩ := by
  obtain ⟨t,ht,c,hr,hc⟩ := NPStackFields.parse_reject bits [] hp
  let s0 := combined (NPStackFields.cfg .probe bits [] [] [] []).stk (fun _=>[]) [] []
  let s1 := combined c.stk (fun _=>[]) [] []
  have h1 := hr.relocate_exact parserMap State.parse parser_injective parser_extends
    (c' := ⟨.parse .probe,s0⟩) (d' := ⟨.parse c.pc,s1⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => exact False.elim (hk k rfl)
        | inr k => cases k with
          | inl k => rfl
          | inr k => cases k <;> rfl)
  have h2 : Step program ⟨.parse c.pc,s1⟩ ⟨.reject,s1⟩ := by
    simp [Step,successors,program,code,returnCode,hc]
  refine ⟨t+1,s1,?_⟩
  rw [initial_combined]
  exact h1.trans (Run.one h2)

def parsedStore (fs : List (List Bool)) : Register → List Bool :=
  combined (NPStackFields.cfg .accept [] [] [] (dataFields fs) []).stk
    (NPCNF.StackValidate.store (dataFields fs) [] [] [] [] [] []) [] []

def framingCost (fs : List (List Bool)) : ℕ :=
  14*(fs.map List.length).sum+10*fs.length+5*(dataFields fs).length+6

lemma framing_prefix (bits : List Bool) (fs : List (List Bool)) (hp : (EncodingTime.parse bits).1=some fs) :
    Run program (framingCost fs) (initial program bits)
      ⟨.validate NPCNF.StackValidate.program.start,parsedStore fs⟩ := by
  have he := NPStackFields.parse_sound bits fs hp
  subst bits
  let p0 := (NPStackFields.cfg .probe (encodeFields fs) [] [] [] []).stk
  let p1 := (NPStackFields.cfg .accept [] [] [] (dataFields fs) []).stk
  let v0 : NPCNF.StackValidate.Register → List Bool := fun _=>[]
  let s0 := combined p0 v0 [] []
  let s1 := combined p1 v0 [] []
  have hp := NPStackFields.fields_run fs []
  simp only [List.reverse_nil,List.nil_append,List.length_nil,Nat.mul_zero,Nat.add_zero] at hp
  have h1 := hp.relocate_exact parserMap State.parse parser_injective parser_extends
    (c' := ⟨.parse .probe,s0⟩) (d' := ⟨.parse .accept,s1⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => exact False.elim (hk k rfl)
        | inr k => cases k with
          | inl k => rfl
          | inr k => cases k <;> rfl)
  have h2 : Step program ⟨.parse .accept,s1⟩ ⟨.transfer .parsed .readSource,s1⟩ := by
    simp [Step,successors,program,code,returnCode,NPStackFields.program]
  have h3 := transfer_run .parsed s1 rfl rfl
  have hout : Function.update s1 (transferTarget .parsed) (s1 (transferSource .parsed))=parsedStore fs := by
    funext k;cases k with
    | inl k => rfl
    | inr k => cases k with
      | inl k => cases k with
        | inl k => cases k <;> rfl
        | inr k => cases k <;> simp [s1,p1,v0,combined,parsedStore,transferSource,transferTarget,parserMap,validatorMap,
            NPStackFields.cfg,NPStackFields.output,NPCNF.StackValidate.input,NPCNF.StackValidate.store]
      | inr k => cases k <;> rfl
  rw [hout] at h3
  rw [initial_combined]
  convert h1.trans (Run.succ h2 h3) using 1 <;>
    dsimp only [framingCost,s1,p1,combined,transferSource,parserMap,NPStackFields.cfg,NPStackFields.output] <;> omega

lemma validation_failure (bits : List Bool) (fs : List (List Bool)) (hp : (EncodingTime.parse bits).1=some fs)
    {t : ℕ} {c : Config NPCNF.StackValidate.Register NPCNF.StackValidate.State}
    (hr : Run NPCNF.StackValidate.program t
      ⟨NPCNF.StackValidate.program.start,NPCNF.StackValidate.store (dataFields fs) [] [] [] [] [] []⟩ c)
    (hc : NPCNF.StackValidate.program.code c.pc=.halt false) :
    ∃u s,Run program u (initial program bits) ⟨.reject,s⟩ := by
  let s := combined (NPStackFields.cfg .accept [] [] [] (dataFields fs) []).stk c.stk [] []
  have hh := hr.relocate_exact validatorMap State.validate validator_injective validator_extends
    (c' := ⟨.validate NPCNF.StackValidate.program.start,parsedStore fs⟩) (d' := ⟨.validate c.pc,s⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => rfl
        | inr k => cases k with
          | inl k => exact False.elim (hk k rfl)
          | inr k => cases k <;> rfl)
  have hj : Step program ⟨.validate c.pc,s⟩ ⟨.reject,s⟩ := by
    simp [Step,successors,program,code,returnCode,hc]
  exact ⟨framingCost fs+(t+1),s,(framing_prefix bits fs hp).trans (hh.trans (Run.one hj))⟩

lemma three_failure (raw : Raw) (hv : raw.decode.Valid) (hn : ¬NPCNF.ThreeCNF raw.decode.formula) :
    ∃t s,Run program t (initial program (encode raw)) ⟨.reject,s⟩ := by
  obtain ⟨t,ht,rest,hr⟩ := NPSATStackThreeCheck.formula_reject raw.formula
    (fun h=>hn ((three_raw_iff raw).mpr h))
  let s := combined (NPStackFields.cfg .accept [] [] [] (dataFields (fields raw)) []).stk
    (NPCNF.StackValidate.store [] (dataFields (formulaFields raw.formula)) (NPCNF.StackValidate.freshBits raw.catalog)
      (dataFields raw.catalog.reverse) [] [] []) rest []
  have hh := hr.relocate_exact checkMap State.check check_injective check_extends
    (c' := ⟨.check .formulaTag,checkedStore raw⟩) (d' := ⟨.check .reject,s⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => rfl
        | inr k => cases k with
          | inl k => rfl
          | inr k => cases k with
            | false => exact False.elim (hk () rfl)
            | true => rfl)
  have hj : Step program ⟨.check .reject,s⟩ ⟨.reject,s⟩ := by
    simp [Step,successors,program,code,returnCode,NPSATStackThreeCheck.program]
  exact ⟨validationCost raw+(t+1),s,(validation_prefix raw hv).trans (hh.trans (Run.one hj))⟩

end BalancedAssortments.NPSATStackPrepare
