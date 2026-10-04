import BalancedAssortments.NPSATStackPrepare

namespace BalancedAssortments.NPSATStackPrepare
open NPStack NPStack.Macros NPCNF.Encoding NPStackFields

def finalStore (raw : Raw) : Register → List Bool :=
  combined (NPStackFields.cfg .accept [] [] [] (dataFields (fields raw)) []).stk
    (NPCNF.StackValidate.store [] (dataFields (formulaFields raw.formula)) (NPCNF.StackValidate.freshBits raw.catalog)
      (dataFields raw.catalog.reverse) [] [] []) [] []

def parseCost (raw : Raw) : ℕ := 14*((fields raw).map List.length).sum+10*(fields raw).length+2

def successCost (raw : Raw) : ℕ := parseCost raw+NPCNF.StackValidate.preparationCost raw+
  5*(dataFields (fields raw)).length+6*(dataFields (formulaFields raw.formula)).length+10

lemma initial_combined (bits : List Bool) : initial program bits=
    ⟨.parse .probe,combined (NPStackFields.cfg .probe bits [] [] [] []).stk (fun _=>[]) [] []⟩ := by
  unfold initial program combined parserMap
  congr 1
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [NPStackFields.cfg,NPStackFields.input]
    | inr u => cases u;simp [NPStackFields.cfg,NPStackFields.input]
  | inr k => cases k with
    | inl k => simp [NPStackFields.input]
    | inr b => cases b <;> simp [NPStackFields.input]

lemma three_raw_iff (raw : Raw) : NPCNF.ThreeCNF raw.decode.formula ↔ ∀c∈raw.formula,c.length≤3 := by
  simp [NPCNF.ThreeCNF,Raw.decode]

def checkedStore (raw : Raw) : Register → List Bool :=
  combined (NPStackFields.cfg .accept [] [] [] (dataFields (fields raw)) []).stk
    (NPCNF.StackValidate.store [] (dataFields (formulaFields raw.formula)) (NPCNF.StackValidate.freshBits raw.catalog)
      (dataFields raw.catalog.reverse) [] [] []) (dataFields (formulaFields raw.formula)) []

def validationCost (raw : Raw) : ℕ := parseCost raw+NPCNF.StackValidate.preparationCost raw+
  5*(dataFields (fields raw)).length+5*(dataFields (formulaFields raw.formula)).length+8

lemma validation_prefix (raw : Raw) (hv : raw.decode.Valid) :
    Run program (validationCost raw) (initial program (encode raw))
      ⟨.check .formulaTag,checkedStore raw⟩ := by
  let p0 := (NPStackFields.cfg .probe (encode raw) [] [] [] []).stk
  let p1 := (NPStackFields.cfg .accept [] [] [] (dataFields (fields raw)) []).stk
  let v0 : NPCNF.StackValidate.Register → List Bool := fun _=>[]
  let v1 := NPCNF.StackValidate.store (dataFields (fields raw)) [] [] [] [] [] []
  let v2 := NPCNF.StackValidate.store [] (dataFields (formulaFields raw.formula)) (NPCNF.StackValidate.freshBits raw.catalog)
    (dataFields raw.catalog.reverse) [] [] []
  let s0 := combined p0 v0 [] []
  let s1 := combined p1 v0 [] []
  let s2 := combined p1 v1 [] []
  let s3 := combined p1 v2 [] []
  let s4 := combined p1 v2 (dataFields (formulaFields raw.formula)) []
  have hp := NPStackFields.fields_run (fields raw) []
  simp only [List.reverse_nil,List.nil_append,List.length_nil,Nat.mul_zero,Nat.add_zero] at hp
  have h1 := hp.relocate_exact parserMap State.parse parser_injective parser_extends
    (c' := ⟨.parse .probe,s0⟩) (d' := ⟨.parse .accept,s1⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => exact False.elim (hk k rfl)
        | inr k => cases k with
          | inl k => rfl
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
            NPStackFields.cfg,NPStackFields.output,NPCNF.StackValidate.store,NPCNF.StackValidate.input]
      | inr k => cases k <;> rfl
  rw [h2out] at h2
  have hvRun := NPCNF.StackValidate.prepare_run raw hv
  have h3 := hvRun.relocate_exact validatorMap State.validate validator_injective validator_extends
    (c' := ⟨.validate NPCNF.StackValidate.program.start,s2⟩)
    (d' := ⟨.validate (.outer (.main .accept)),s3⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => rfl
        | inr k => cases k with
          | inl k => exact False.elim (hk k rfl)
          | inr k => cases k <;> rfl)
  have h34 : Step program ⟨.validate (.outer (.main .accept)),s3⟩ ⟨.transfer .formula .readSource,s3⟩ := by
    simp [Step,successors,program,code,returnCode,NPCNF.StackValidate.program,NPCNF.StackValidate.code,
      NPCNF.StackValidate.macroCode,Macros.code,Instr.rename]
  have h4 := transfer_run .formula s3 rfl rfl
  have h4out : Function.update s3 (transferTarget .formula) (s3 (transferSource .formula))=s4 := by
    funext k;cases k with
    | inl k => rfl
    | inr k => cases k with
      | inl k => rfl
      | inr k => cases k <;> simp [s3,s4,combined,v2,transferSource,transferTarget,checkMap,original,validatorMap,
          NPCNF.StackValidate.original,NPCNF.StackValidate.store]
  rw [h4out] at h4
  have hall := h1.trans (Run.succ h12 (h2.trans (h3.trans (Run.succ h34 h4))))
  rw [initial_combined]
  convert hall using 1 <;>
    dsimp [validationCost,parseCost,s1,p1,s3,s4,v2,combined,transferSource,parserMap,original,validatorMap,
      NPStackFields.cfg,NPStackFields.output,NPCNF.StackValidate.original,NPCNF.StackValidate.store,checkedStore] <;> omega

theorem valid_run (raw : Raw) (hv : raw.decode.Valid) (hthree : NPCNF.ThreeCNF raw.decode.formula) :
    Run program (successCost raw) (initial program (encode raw)) ⟨.accept,finalStore raw⟩ := by
  have hcheck := NPSATStackThreeCheck.formula_run raw.formula ((three_raw_iff raw).mp hthree)
  have hc := hcheck.relocate_exact checkMap State.check check_injective check_extends
    (c' := ⟨.check .formulaTag,checkedStore raw⟩) (d' := ⟨.check .accept,finalStore raw⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => rfl
        | inr k => cases k with
          | inl k => rfl
          | inr k => cases k with
            | false => exact False.elim (hk () rfl)
            | true => rfl)
  have hj : Step program ⟨.check .accept,finalStore raw⟩ ⟨.accept,finalStore raw⟩ := by
    simp [Step,successors,program,code,returnCode,NPSATStackThreeCheck.program]
  convert (validation_prefix raw hv).trans (hc.trans (Run.one hj)) using 1 <;>
    unfold successCost validationCost <;> omega

lemma successCost_bound (raw : Raw) : successCost raw≤1100*((encode raw).length+1)^3 := by
  have hp := NPCNF.StackValidate.preparationCost_bound raw
  have he := NPStackFields.encoding_length (fields raw)
  have hd := NPStackFields.dataFields_length (fields raw)
  have hf : (dataFields (formulaFields raw.formula)).length≤(dataFields (fields raw)).length := by
    simp only [fields,dataFields,List.flatMap_append,List.length_append]
    omega
  have hlen : (encode raw).length=(dataFields (fields raw)).length := by
    exact he.trans hd.symm
  unfold successCost parseCost NPCNF.StackValidate.prepBudget at *
  rw [hlen]
  have hparse : 14*((fields raw).map List.length).sum+10*(fields raw).length+2≤10*(dataFields (fields raw)).length+2 := by omega
  have hc : (dataFields (fields raw)).length+1≤((dataFields (fields raw)).length+1)^3 := by
    nlinarith [Nat.zero_le ((dataFields (fields raw)).length^3),Nat.zero_le ((dataFields (fields raw)).length^2)]
  omega

end BalancedAssortments.NPSATStackPrepare
