import BalancedAssortments.NPStackSourceVerifierRowState
import BalancedAssortments.NPStackSourcePairingSound

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

def pairRecord (x : WitnessRecord) (mask : List Bool) : NPStackSourcePairing.PairRecord :=
  (fun i => recordFields x mask ⟨i,by omega⟩,
   fun i => recordFields x mask ⟨6+i,by omega⟩)

lemma pairRecord_fields (x : WitnessRecord) (mask : List Bool) :
    NPStackSourcePairing.pairedRow (pairRecord x mask).1 (pairRecord x mask).2=recordFields x mask := by
  funext i;fin_cases i <;> rfl

abbrev InputRow := WitnessRecord × List Bool

def nextRegisters (s : Registers) (x : WitnessRecord) : Registers := VerifierCommands.rowEffect (loadRecord s x)
def nextBalance (s : Registers) (x : WitnessRecord) (balance : List Bool) : List Bool :=
  NPStackFields.dataFields (balanceRecord x.active (nextRegisters s x))++balance

def traceEnd : List InputRow→Registers→List Bool→Registers×List Bool
  | [],s,b => (s,b)
  | (x,m)::xs,s,b => traceEnd xs (nextRegisters s x) (nextBalance s x b)

def RowsValid : List InputRow→Registers→Prop
  | [],_ => True
  | (x,m)::xs,s => NPStackMask.maskValue m=some x.active ∧
      (eval (VerifierCommands.rowCommand x.active) (loadRecord s x)).1=true ∧ RowsValid xs (nextRegisters s x)

/-- Actual first-pass body executions compose under structural record iteration;
no decoded dimension controls the run. -/
theorem trace_run (rows : List InputRow) (s : Registers) (balance : List Bool)
    (hp : (s .priceDen).2=[]) (hv : (s .attractionDen).2=[])
    (hvalid : RowsValid rows s) :
    ∃ t, NPStackSourcePairing.BodyRuns bodyProgram (rows.map (fun r=>pairRecord r.1 r.2))
      (workspaceStore s balance) (workspaceStore (traceEnd rows s balance).1 (traceEnd rows s balance).2) t := by
  induction rows generalizing s balance with
  | nil => exact ⟨0,.nil _⟩
  | cons r rows ih =>
    rcases r with ⟨x,m⟩
    rcases hvalid with ⟨hm,ha,hrest⟩
    obtain ⟨u,hu⟩ := body_row_run (loadRecord s x) m balance x.active hm ha
    rw [packed_record _ x m balance (loadRecord_holds s x),loadRecord_workspace s x balance hp hv] at hu
    rw [←pairRecord_fields x m] at hu
    have hd := rowEffect_denominators s x
    obtain ⟨v,hv⟩ := ih (nextRegisters s x) (nextBalance s x balance) hd.1 hd.2 hrest
    refine ⟨_,NPStackSourcePairing.BodyRuns.cons hu ?_ hv⟩
    simp [bodyProgram,ClearRows.finishProgram,ClearRows.clearDone_halts,Instr.rename]

end BalancedAssortments.NPStack.SourceVerifier
