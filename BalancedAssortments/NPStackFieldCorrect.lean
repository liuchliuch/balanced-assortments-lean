import BalancedAssortments.NPStackFieldReject
import BalancedAssortments.NPStackDeterministic

namespace BalancedAssortments.NPStackField
open NPStack

lemma program_noChoice : NoChoice program := by
  intro q a b
  cases q <;> simp [program]

lemma program_deterministic : Deterministic program := noChoice_deterministic program_noChoice

/-- Full operational parser equivalence, including all malformed input words.
The finite program cannot accept a different payload or bypass rejection.
Its bound counts real stack transitions and is linear in the original word. -/
theorem field_parser_iff (bits payload : List Bool) :
    (∃ rest,(EncodingTime.parseField bits).1=some (payload,rest)) ↔
      OutputsIn program bits payload (7*bits.length+3) := by
  constructor
  · rintro ⟨rest,h⟩
    have hr := parseField_run bits payload rest h
    have hb := parseField_sound bits payload rest h
    have hl : payload.length≤bits.length := by
      rw [hb]
      simp [FPTASCostProgram.serializeBits]
    refine ⟨7*payload.length+3,by omega,cfg .accept rest [] [] payload,?_,rfl,rfl⟩
    rw [initial_cfg]
    exact hr
  · rintro ⟨t,_,c,hr,hc,hout⟩
    cases hp : (EncodingTime.parseField bits).1 with
    | none =>
      obtain ⟨s,_,d,hs,hd⟩ := parseField_reject bits hp
      exact False.elim (rejecting_run_excludes_acceptance program_deterministic hs hd hr hc)
    | some p =>
      rcases p with ⟨out,rest⟩
      have hs := parseField_run bits out rest hp
      rw [← initial_cfg] at hs
      have he := hs.halted_unique program_deterministic hr (by rfl) hc
      have ho := congrArg (fun c : Config Stack State => c.stk Stack.output) he.2
      change out=c.stk Stack.output at ho
      have hsame : out=payload := ho.trans hout
      refine ⟨rest,?_⟩
      simp only [Option.some.injEq,Prod.mk.injEq]
      exact ⟨hsame,True.intro⟩

def finiteProgram : FiniteProgram where
  K := Stack
  Q := State
  program := program

end BalancedAssortments.NPStackField
