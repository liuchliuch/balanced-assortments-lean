import BalancedAssortments.NPSATStackReductionProgram
import BalancedAssortments.NPSATStackGadgetInitialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 10000
set_option maxRecDepth 4096
noncomputable section
namespace BalancedAssortments.NPSATStackReduction
open NPStack NPStack.Macros NPCNF.Encoding NPStackFields

def constructBudget (raw : Raw) : ℕ :=
  NPSATStackGadget.completedBudget raw.catalog.reverse raw.formula (NPCNF.StackValidate.freshBits raw.catalog)
    ((encode raw).length+1)

def successBudget (raw : Raw) : ℕ := NPSATStackPrepare.successCost raw+constructBudget raw+
  5*((dataFields raw.catalog.reverse).length+(dataFields (formulaFields raw.formula)).length+
    (NPCNF.StackValidate.freshBits raw.catalog).length)+11

def finalStore (raw : Raw) : Reg → List Bool := combined (NPSATStackPrepare.finalStore raw)
  (NPSATStackGadget.completedStore raw.catalog.reverse raw.formula (NPCNF.StackValidate.freshBits raw.catalog))

/-- Successful execution begins with the original wire input and physically
parses, validates, checks clause widths, copies prepared registers and builds
all output integers. No prepared fields or unary dimensions are supplied. -/
theorem valid_run (raw : Raw) (hv : raw.decode.Valid) (ht : NPCNF.ThreeCNF raw.decode.formula) :
    ∃t ≤ successBudget raw,Run program t (initial program (encode raw)) ⟨.accept,finalStore raw⟩ := by
  let p0 := (initial NPSATStackPrepare.program (encode raw)).stk
  let p1 := NPSATStackPrepare.finalStore raw
  let g0 : NPSATStackGadget.Reg → List Bool := fun _=>[]
  let s0 := combined p0 g0
  let s1 := combined p1 g0
  let s2 := Function.update s1 (transferTarget .catalog) (dataFields raw.catalog.reverse)
  let s3 := Function.update s2 (transferTarget .formula) (dataFields (formulaFields raw.formula))
  let s4 := Function.update s3 (transferTarget .fresh) (NPCNF.StackValidate.freshBits raw.catalog)
  have hp := NPSATStackPrepare.valid_run raw hv ht
  have h1 := hp.relocate_exact prepareMap State.prepare Sum.inl_injective prepare_extends
    (c' := ⟨.prepare NPSATStackPrepare.program.start,s0⟩) (d' := ⟨.prepare .accept,s1⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;rcases k with k|k
        · exact False.elim (hk k rfl)
        · rfl)
  have h12 : Step program ⟨.prepare .accept,s1⟩ ⟨.transfer .catalog .readSource,s1⟩ := by
    simp [Step,successors,program,code,returnCode,NPSATStackPrepare.program,NPSATStackPrepare.code]
  have h2 : Run program (5*(dataFields raw.catalog.reverse).length+3)
      ⟨.transfer .catalog .readSource,s1⟩ ⟨.transfer .formula .readSource,s2⟩ :=
    transfer_run .catalog s1 rfl rfl
  have h3 := transfer_run .formula s2
    (by simp [s2,s1,combined,g0,transferTarget,scratch,gadgetMap,NPSATStackGadget.scratch,NPSATStackGadget.catalog])
    (by simp [s2,s1,combined,g0,transferTarget,gadgetMap,NPSATStackGadget.formula,NPSATStackGadget.catalog,
      NPSATStackVariableTokens.formula,NPSATStackVariableTokens.catalog,NPSATStackVariableTokens.itemMap])
  have h3' : Run program (5*(dataFields (formulaFields raw.formula)).length+3)
      ⟨.transfer .formula .readSource,s2⟩ ⟨.transfer .fresh .readSource,s3⟩ := by
    simpa only [s2,transferSource,prepareMap,transferTarget,gadgetMap,Function.update_of_ne (by decide : Sum.inl NPSATStackPrepare.original≠Sum.inr NPSATStackGadget.catalog)] using h3
  have h4 := transfer_run .fresh s3
    (by simp [s3,s2,s1,combined,g0,transferTarget,scratch,gadgetMap,NPSATStackGadget.scratch,NPSATStackGadget.catalog,NPSATStackGadget.formula])
    (by simp [s3,s2,s1,combined,g0,transferTarget,gadgetMap,NPSATStackGadget.fresh,NPSATStackGadget.formula,NPSATStackGadget.catalog,
      NPSATStackVariableTokens.fresh,NPSATStackVariableTokens.formula,NPSATStackVariableTokens.catalog,NPSATStackVariableTokens.itemMap])
  have h4' : Run program (5*(NPCNF.StackValidate.freshBits raw.catalog).length+3)
      ⟨.transfer .fresh .readSource,s3⟩ ⟨.construct (Structured.entry NPSATStackGadget.complete),s4⟩ := by
    convert h4 using 1 <;>
      simp [s3,s2,s1,p1,combined,transferSource,transferTarget,prepareMap,gadgetMap,
        NPSATStackPrepare.finalStore,NPSATStackPrepare.combined,NPSATStackPrepare.validatorMap,
        NPCNF.StackValidate.fresh,NPCNF.StackValidate.store]
  have hs4 : s4=combined p1 (NPSATStackGadget.startStore raw.catalog.reverse raw.formula (NPCNF.StackValidate.freshBits raw.catalog)) := by
    simp only [s4,s3,s2,s1,transferTarget,gadgetMap,combined_update_right,g0,NPSATStackGadget.startStore_fields]
  have hmeasure := NPCNF.StackValidate.measure_le_input raw
  have hlen : (dataFields (fields raw)).length=(encode raw).length :=
    (NPStackFields.dataFields_length _).trans (NPStackFields.encoding_length _).symm
  have hw : ∀label∈raw.catalog.reverse,label.length≤(encode raw).length+1 := by
    intro label hl
    have hh := (rawMeasure_widths raw).1 label (by simpa using hl)
    omega
  have hfcat : ∀label∈raw.catalog.reverse,ComplexityTimeBinary.value (NPCNF.StackValidate.freshBits raw.catalog)≠ComplexityTimeBinary.value label := by
    simpa using NPSATStackFresh.fresh_catalog raw
  obtain ⟨tg,htg,hg⟩ := NPSATStackGadget.complete_run raw.catalog.reverse raw.formula
    (NPCNF.StackValidate.freshBits raw.catalog) ((encode raw).length+1) hw
    ((NPSATStackPrepare.three_raw_iff raw).mp ht) hfcat (NPSATStackFresh.fresh_formula raw hv)
  have h5 := hg.relocate_exact gadgetMap State.construct Sum.inr_injective gadget_extends
    (c' := ⟨.construct (Structured.entry NPSATStackGadget.complete),s4⟩)
    (d' := ⟨.construct (Structured.finish NPSATStackGadget.complete),finalStore raw⟩)
    (by constructor;rfl;intro a;rw [hs4];rfl) ⟨rfl,fun _=>rfl⟩
    (by intro k hk;rcases k with k|k
        · rw [hs4];rfl
        · exact False.elim (hk k rfl))
  have h56 : Step program ⟨.construct (Structured.finish NPSATStackGadget.complete),finalStore raw⟩
      ⟨.accept,finalStore raw⟩ := by
    simp [Step,successors,program,code,returnCode,NPSATStackGadget.program,Structured.program,Structured.code_finish]
  have hall := h1.trans (Run.succ h12 (h2.trans (h3'.trans (h4'.trans (h5.trans (Run.one h56))))))
  refine ⟨NPSATStackPrepare.successCost raw+tg+
    5*((dataFields raw.catalog.reverse).length+(dataFields (formulaFields raw.formula)).length+
      (NPCNF.StackValidate.freshBits raw.catalog).length)+11,?_,?_⟩
  · unfold successBudget constructBudget
    omega
  · rw [initial_combined]
    convert hall using 1 <;> omega

lemma final_output (raw : Raw) : finalStore raw output=NPSATStackGadget.result raw.catalog.reverse raw.formula := by
  exact NPSATStackGadget.completed_output raw.catalog.reverse raw.formula (NPCNF.StackValidate.freshBits raw.catalog)

end BalancedAssortments.NPSATStackReduction
