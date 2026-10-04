import BalancedAssortments.NPCNFStackReductionFallback
import BalancedAssortments.NPCNFStackValidateRun

namespace BalancedAssortments.NPCNF.StackReduction
open NPStack NPStack.Macros Encoding NPStackFields

def combined (p : NPStackFields.Stack → List Bool) (v : StackValidate.Register → List Bool)
    (t : StackTransform.Register → List Bool) : Register → List Bool
  | .inl k => p k
  | .inr (.inl k) => v k
  | .inr (.inr k) => t k

def reversedInput (raw : Raw) : Raw := ⟨raw.catalog.reverse,raw.formula⟩
def successResult (raw : Raw) : Raw := StackTransform.result (StackValidate.freshBits raw.catalog) (reversedInput raw)

def parseCost (raw : Raw) : ℕ := 14*((fields raw).map List.length).sum+10*(fields raw).length+2

def successCost (raw : Raw) : ℕ := parseCost raw+StackValidate.preparationCost raw+
  StackTransform.cost (StackValidate.freshBits raw.catalog) (reversedInput raw)+
  5*((dataFields (fields raw)).length+(dataFields (formulaFields raw.formula)).length+
    (StackValidate.freshBits raw.catalog).length+(dataFields raw.catalog.reverse).length)+15

lemma initial_combined (bits : List Bool) : initial program bits=
    ⟨.parse .probe,combined (NPStackFields.cfg .probe bits [] [] [] []).stk (fun _=>[]) (fun _=>[])⟩ := by
  unfold initial program combined parserMap
  congr 1
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [NPStackFields.cfg,NPStackFields.input]
    | inr u => cases u;simp [NPStackFields.cfg,NPStackFields.input]
  | inr k => cases k <;> simp [NPStackFields.input]

/-- Successful literal-input execution of the entire finite reduction pipeline.
No prepared register state is supplied by the caller. -/
theorem valid_run (raw : Raw) (hv : raw.decode.Valid) :
    ∃ finalStore,Run program (successCost raw) (initial program (encode raw)) ⟨.accept,finalStore⟩ ∧
      finalStore output=encode (successResult raw) := by
  let p0 := (NPStackFields.cfg .probe (encode raw) [] [] [] []).stk
  let p1 := (NPStackFields.cfg .accept [] [] [] (dataFields (fields raw)) []).stk
  let v0 : StackValidate.Register → List Bool := fun _=>[]
  let t0 : StackTransform.Register → List Bool := fun _=>[]
  let v1 := StackValidate.store (dataFields (fields raw)) [] [] [] [] [] []
  let v2 := StackValidate.store [] (dataFields (formulaFields raw.formula)) (StackValidate.freshBits raw.catalog)
    (dataFields raw.catalog.reverse) [] [] []
  let s0 := combined p0 v0 t0
  let s1 := combined p1 v0 t0
  let s2 := combined p1 v1 t0
  let s3 := combined p1 v2 t0
  let s4 := Function.update s3 (transferTarget .formula) (dataFields (formulaFields raw.formula))
  let s5 := Function.update s4 (transferTarget .fresh) (StackValidate.freshBits raw.catalog)
  let s6 := Function.update s5 (transferTarget .catalogue) (dataFields raw.catalog.reverse)
  let t1 := StackTransform.store (StackFormula.formulaData raw.formula) (StackValidate.freshBits raw.catalog)
    [] [] (dataFields raw.catalog.reverse)
  let t2 := StackTransform.store (encode (successResult raw))
    (bitFormula (StackValidate.freshBits raw.catalog) raw.formula).1.2 [] [] []
  let s7 := combined p1 v2 t2
  have hp := NPStackFields.fields_run (fields raw) []
  simp only [List.reverse_nil,List.nil_append,List.length_nil,Nat.mul_zero,Nat.add_zero] at hp
  have h1 := hp.relocate_exact parserMap State.parse parser_injective parser_extends
    (c' := ⟨.parse .probe,s0⟩) (d' := ⟨.parse .accept,s1⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => exact False.elim (hk k rfl)
        | inr k => cases k <;> rfl)
  have h12 : Step program ⟨.parse .accept,s1⟩ ⟨.transfer .parsed .readSource,s1⟩ := by
    simp [Step,successors,program,code,returnCode,NPStackFields.program]
  have h2 := transfer_run .parsed s1 rfl rfl
  have h2out : Function.update s1 (transferTarget .parsed) (s1 (transferSource .parsed))=s2 := by
    funext k;cases k with
    | inl k => rfl
    | inr k => cases k with
      | inl k => cases k with
        | inl k => cases k <;> rfl
        | inr k => cases k <;> simp [s1,s2,combined,v0,v1,p1,transferSource,transferTarget,validatorMap,parserMap,
            NPStackFields.cfg,NPStackFields.output,StackValidate.store,StackValidate.input]
      | inr k => rfl
  rw [h2out] at h2
  have hvRun := StackValidate.prepare_run raw hv
  have h3 := hvRun.relocate_exact validatorMap State.validate validator_injective validator_extends
    (c' := ⟨.validate StackValidate.program.start,s2⟩) (d' := ⟨.validate (.outer (.main .accept)),s3⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => rfl
        | inr k => cases k with
          | inl k => exact False.elim (hk k rfl)
          | inr k => rfl)
  have h34 : Step program ⟨.validate (.outer (.main .accept)),s3⟩ ⟨.transfer .formula .readSource,s3⟩ := by
    simp [Step,successors,program,code,returnCode,StackValidate.program,StackValidate.code,StackValidate.macroCode,Macros.code,Instr.rename]
  have h4 := transfer_run .formula s3 rfl rfl
  have h4' : Run program (5*(dataFields (formulaFields raw.formula)).length+3)
      ⟨.transfer .formula .readSource,s3⟩ ⟨.transfer .fresh .readSource,s4⟩ := h4
  have h5 := transfer_run .fresh s4 (by simp [s4,s3,combined,t0,scratch,transformMap,transferTarget])
    (by simp [s4,s3,combined,t0,transformMap,transferTarget])
  have h5' : Run program (5*(StackValidate.freshBits raw.catalog).length+3)
      ⟨.transfer .fresh .readSource,s4⟩ ⟨.transfer .catalogue .readSource,s5⟩ := by
    simpa [s4,s3,combined,v2,transferSource,transferTarget,transformMap,validatorMap,StackValidate.fresh,StackValidate.store] using h5
  have h6 := transfer_run .catalogue s5 (by simp [s5,s4,s3,combined,t0,scratch,transformMap,transferTarget])
    (by simp [s5,s4,s3,combined,t0,transformMap,transferTarget])
  have h6' : Run program (5*(dataFields raw.catalog.reverse).length+3)
      ⟨.transfer .catalogue .readSource,s5⟩ ⟨.transform StackTransform.program.start,s6⟩ := by
    simpa [s5,s4,s3,combined,v2,transferSource,transferTarget,transformMap,validatorMap,StackValidate.catalogue,StackValidate.store] using h6
  have hs6 : s6=combined p1 v2 t1 := by
    funext k;cases k with
    | inl k => rfl
    | inr k => cases k with
      | inl k => rfl
      | inr k => cases k with
        | inl k => cases k <;> simp [s6,s5,s4,s3,combined,t0,t1,StackTransform.store,StackChain.store,transferTarget,transformMap,
            StackFormula.formulaData]
        | inr u => cases u;simp [s6,s5,s4,s3,combined,t0,t1,StackTransform.store,transferTarget,transformMap]
  have htRun := StackTransform.transform_run (StackValidate.freshBits raw.catalog) (reversedInput raw)
  have h7 := htRun.relocate_exact transformMap State.transform transform_injective transform_extends
    (c' := ⟨.transform StackTransform.program.start,combined p1 v2 t1⟩)
    (d' := ⟨.transform (.encode .accept),s7⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => rfl
        | inr k => cases k with
          | inl k => rfl
          | inr k => exact False.elim (hk k rfl))
  rw [← hs6] at h7
  have h8 : Step program ⟨.transform (.encode .accept),s7⟩ ⟨.accept,s7⟩ := by
    simp [Step,successors,program,code,returnCode,StackTransform.program,StackTransform.code,NPStackFieldsEncode.program,Instr.rename]
  have hh := h1.trans (Run.succ h12 (h2.trans (h3.trans (Run.succ h34 (h4'.trans (h5'.trans (h6'.trans (h7.trans (Run.one h8)))))))))
  refine ⟨s7,?_,rfl⟩
  rw [initial_combined]
  convert hh using 1 <;> dsimp only [successCost,parseCost,s1,p1,combined,transferSource,parserMap,NPStackFields.cfg,NPStackFields.output] <;> omega

end BalancedAssortments.NPCNF.StackReduction
