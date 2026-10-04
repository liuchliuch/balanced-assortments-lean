import BalancedAssortments.NPStackSourceVerifierProgramStore
import BalancedAssortments.NPStackVerifierControlBound
import BalancedAssortments.NPStackSourceBalanceCorrect

namespace BalancedAssortments.NPStack.SourceVerifier.Whole
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

/-- The final program now has a fixed concrete second-pass implementation. -/
def concreteProgram := program Balance.loopProgram

lemma command_stage_complete (command : Command) (s : Registers) (balance : List Bool)
    (ha : (eval command s).1=true) :
    ∃ t ≤ VerifierControl.budget VerifierCommands.compareTime command s,
      StageRun (VerifierCommands.program command) globalArithmeticMap (globalStore s balance)
        (globalStore (eval command s).2 balance) t := by
  obtain ⟨t,ht,hr⟩ := VerifierCommands.command_run command s
  have hh := VerifierControl.terminal_halts VerifierCommands.comparisons SignedAssignCompare.State.result command s
  have hacc : accepts (VerifierCommands.program command) (VerifierControl.result command s) := by
    change (VerifierCommands.program command).code (terminal command s)=.halt true
    rw [show (VerifierCommands.program command).code (terminal command s)=.halt (eval command s).1 from hh,ha]
  refine ⟨t,ht,stage_mk (VerifierCommands.program command) globalArithmeticMap _ _ hr hacc
    (global_projection s balance) (global_projection (eval command s).2 balance) ?_⟩
  intro k hk
  exact (global_frame s (eval command s).2 balance k hk).symm

/-- Arithmetic guard stages recover the concrete command evaluation and exact
complete global store, not just the values of registers touched by the guard. -/
lemma command_stage_sound (command : Command) (s : Registers) (balance : List Bool)
    {after : SourceVerifier.Stack→List Bool} {t : ℕ}
    (h : StageRun (VerifierCommands.program command) globalArithmeticMap (globalStore s balance) after t) :
    t ≤ VerifierControl.budget VerifierCommands.compareTime command s ∧ (eval command s).1=true ∧
      after=globalStore (eval command s).2 balance := by
  classical
  obtain ⟨e,hr,ha,hproj,hframe⟩ := h
  have hs : (fun k=>globalStore s balance (globalArithmeticMap k))=SignedAssignment.initialStore s := funext (global_projection s balance)
  rw [hs] at hr
  obtain ⟨ht,he⟩ := VerifierCommands.command_halted_result command s hr ha
  rw [he] at ha hproj
  have hterminal := VerifierControl.terminal_halts VerifierCommands.comparisons SignedAssignCompare.State.result command s
  have hbool : (eval command s).1=true := by
    change (VerifierCommands.program command).code (terminal command s)=.halt true at ha
    rw [show (VerifierCommands.program command).code (terminal command s)=.halt (eval command s).1 from hterminal] at ha
    exact Instr.halt.inj ha
  refine ⟨ht,hbool,?_⟩
  funext k
  by_cases hk : ∃ a,globalArithmeticMap a=k
  · obtain ⟨a,rfl⟩ := hk
    rw [hproj a,global_projection]
    rfl
  · have hn : ∀ a,globalArithmeticMap a≠k := by simpa using hk
    rw [hframe k hn]
    exact global_frame s (eval command s).2 balance k hn

def Clean (s : Registers) : Prop :=
  s .price=zzero ∧ s .priceDen=zzero ∧ s .attraction=zzero ∧ s .attractionDen=zzero ∧ s .numerator=zzero

lemma cleanRegisters_clean (s : Registers) : Clean (cleanRegisters s) := by
  simp [Clean,cleanRegisters,loadRecord,emptyRecord,zzero]

lemma initialRegisters_clean (s : Fin 8→List Bool) (c : Fin 2→List Bool) : Clean (initialRegisters s c) := by
  simp [Clean,initialRegisters]

lemma header_state (s : Registers) : (eval VerifierCommands.headerCommand s).2=s := by
  simp only [VerifierCommands.headerCommand,VerifierCommands.guardLE,VerifierCommands.guardPositive,eval]
  split_ifs <;> rfl

lemma rank_clean (s : Registers) (h : Clean s) : Clean (eval VerifierCommands.rankCommand s).2 := by
  simpa only [Clean,
    (VerifierCommands.final_preserves s .price (by decide) (by decide)).1,
    (VerifierCommands.final_preserves s .priceDen (by decide) (by decide)).1,
    (VerifierCommands.final_preserves s .attraction (by decide) (by decide)).1,
    (VerifierCommands.final_preserves s .attractionDen (by decide) (by decide)).1,
    (VerifierCommands.final_preserves s .numerator (by decide) (by decide)).1] using h

lemma revenue_clean (s : Registers) (h : Clean s) : Clean (eval VerifierCommands.revenueCommand s).2 := by
  simpa only [Clean,
    (VerifierCommands.final_preserves s .price (by decide) (by decide)).2,
    (VerifierCommands.final_preserves s .priceDen (by decide) (by decide)).2,
    (VerifierCommands.final_preserves s .attraction (by decide) (by decide)).2,
    (VerifierCommands.final_preserves s .attractionDen (by decide) (by decide)).2,
    (VerifierCommands.final_preserves s .numerator (by decide) (by decide)).2] using h

lemma packed_stable (s : Registers) (stream : List Bool) (h : Clean s) : packedStore s [] stream=Balance.stable s stream := by
  have hholds : HoldsRecord s emptyRecord := by
    rcases h with ⟨hp,hpd,hv,hvd,hn⟩
    simp [HoldsRecord,emptyRecord,hp,hpd,hv,hvd,hn,zzero]
  have hh := packed_record s emptyRecord [] stream hholds
  have hrow : recordFields emptyRecord []=(fun _=>[]) := by funext i;fin_cases i <;> rfl
  rw [hrow] at hh
  exact hh

/-- The clean output of the scalar guards is exactly the real second-pass
loop's stable input representation. -/
lemma balance_projection (s : Registers) (stream : List Bool) (h : Clean s) :
    (fun k=>globalStore s stream (.body k))=Balance.stable s stream := packed_stable s stream h

end BalancedAssortments.NPStack.SourceVerifier.Whole
