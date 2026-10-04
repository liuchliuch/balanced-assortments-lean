import BalancedAssortments.NPCNFStackReductionBounds

namespace BalancedAssortments.NPCNF.StackReduction
open NPStack NPStack.Macros NPStackFields Encoding

/-- Actual malformed-framing path, including the fixed unsatisfiable emitter. -/
theorem framing_failure (bits : List Bool) (hp : (EncodingTime.parse bits).1=none) :
    ∃ t≤10*bits.length+failureBits.length+8,∃ s,
      Run program t (initial program bits) ⟨.accept,s⟩ ∧ s output=failureBits := by
  obtain ⟨t,ht,c,hr,hc⟩ := NPStackFields.parse_reject bits [] hp
  let v0 : StackValidate.Register → List Bool := fun _=>[]
  let t0 : StackTransform.Register → List Bool := fun _=>[]
  let s0 := combined (NPStackFields.cfg .probe bits [] [] [] []).stk v0 t0
  let s1 := combined c.stk v0 t0
  have h1 := hr.relocate_exact parserMap State.parse parser_injective parser_extends
    (c' := ⟨.parse .probe,s0⟩) (d' := ⟨.parse c.pc,s1⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => exact False.elim (hk k rfl)
        | inr k => cases k <;> rfl)
  have h2 : Step program ⟨.parse c.pc,s1⟩ ⟨.failureClear,s1⟩ := by
    simp [Step,successors,program,code,returnCode,hc]
  have h3 := failure_run s1
  have hzero : s1 output=[] := rfl
  rw [hzero] at h3
  have hh := h1.trans (Run.succ h2 h3)
  refine ⟨t+1+(failureBits.length+2),by omega,Function.update s1 output failureBits,?_,by simp⟩
  rw [initial_combined]
  convert hh using 1 <;> omega

def parsedStore (fs : List (List Bool)) : Register → List Bool :=
  combined (NPStackFields.cfg .accept [] [] [] (dataFields fs) []).stk
    (StackValidate.store (dataFields fs) [] [] [] [] [] []) (fun _=>[])

def framingCost (fs : List (List Bool)) : ℕ :=
  14*(fs.map List.length).sum+10*fs.length+5*(dataFields fs).length+6

lemma framing_prefix (bits : List Bool) (fs : List (List Bool)) (hp : (EncodingTime.parse bits).1=some fs) :
    Run program (framingCost fs) (initial program bits) ⟨.validate StackValidate.program.start,parsedStore fs⟩ := by
  have he := NPStackFields.parse_sound bits fs hp
  subst bits
  let p0 := (NPStackFields.cfg .probe (encodeFields fs) [] [] [] []).stk
  let p1 := (NPStackFields.cfg .accept [] [] [] (dataFields fs) []).stk
  let v0 : StackValidate.Register → List Bool := fun _=>[]
  let t0 : StackTransform.Register → List Bool := fun _=>[]
  let s0 := combined p0 v0 t0
  let s1 := combined p1 v0 t0
  have hp := NPStackFields.fields_run fs []
  simp only [List.reverse_nil,List.nil_append,List.length_nil,Nat.mul_zero,Nat.add_zero] at hp
  have h1 := hp.relocate_exact parserMap State.parse parser_injective parser_extends
    (c' := ⟨.parse .probe,s0⟩) (d' := ⟨.parse .accept,s1⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => exact False.elim (hk k rfl)
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
        | inr k => cases k <;> simp [s1,p1,v0,t0,combined,parsedStore,transferSource,transferTarget,parserMap,validatorMap,
            NPStackFields.cfg,NPStackFields.output,StackValidate.input,StackValidate.store]
      | inr k => rfl
  rw [hout] at h3
  have hh := h1.trans (Run.succ h2 h3)
  rw [initial_combined]
  convert hh using 1 <;> dsimp only [framingCost,s1,p1,combined,transferSource,parserMap,NPStackFields.cfg,NPStackFields.output] <;> omega

lemma framingCost_bound (bits : List Bool) (fs : List (List Bool)) (hp : (EncodingTime.parse bits).1=some fs) :
    framingCost fs≤15*bits.length+6 := by
  have he := NPStackFields.parse_sound bits fs hp
  have hlen : (dataFields fs).length=bits.length := by rw [he];exact (NPStackFieldsEncode.wireFields_length fs).symm
  have hs := NPStackFields.dataFields_length fs
  unfold framingCost
  omega

/-- Any genuine rejecting validator execution is turned into the same fixed
unsatisfiable encoded output, with every intervening transition counted. -/
theorem validation_failure (bits : List Bool) (fs : List (List Bool)) (hp : (EncodingTime.parse bits).1=some fs)
    {t : ℕ} {c : Config StackValidate.Register StackValidate.State}
    (hr : Run StackValidate.program t
      ⟨StackValidate.program.start,StackValidate.store (dataFields fs) [] [] [] [] [] []⟩ c)
    (hc : StackValidate.program.code c.pc=.halt false) :
    ∃ u≤t+15*bits.length+failureBits.length+9,∃ s,
      Run program u (initial program bits) ⟨.accept,s⟩ ∧ s output=failureBits := by
  let p := (NPStackFields.cfg .accept [] [] [] (dataFields fs) []).stk
  let s1 := combined p c.stk (fun _=>[])
  have h1 := framing_prefix bits fs hp
  have h2 := hr.relocate_exact validatorMap State.validate validator_injective validator_extends
    (c' := ⟨.validate StackValidate.program.start,parsedStore fs⟩) (d' := ⟨.validate c.pc,s1⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => rfl
        | inr k => cases k with
          | inl k => exact False.elim (hk k rfl)
          | inr k => rfl)
  have h3 : Step program ⟨.validate c.pc,s1⟩ ⟨.failureClear,s1⟩ := by
    simp [Step,successors,program,code,returnCode,hc]
  have h4 := failure_run s1
  have hzero : s1 output=[] := rfl
  rw [hzero] at h4
  have hh := h1.trans (h2.trans (Run.succ h3 h4))
  have hcost := framingCost_bound bits fs hp
  refine ⟨framingCost fs+t+1+(failureBits.length+2),by omega,
    Function.update s1 output failureBits,?_,by simp⟩
  convert hh using 1 <;> omega

end BalancedAssortments.NPCNF.StackReduction
