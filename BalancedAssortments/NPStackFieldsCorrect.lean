import BalancedAssortments.NPStackFieldsReject
import BalancedAssortments.NPStackCompile

namespace BalancedAssortments.NPStackFields
open NPStack

lemma program_noChoice : NoChoice program := by
  intro q a b
  cases q <;> try simp [program]
  rename_i q
  cases q <;> simp [program,NPStackField.program,Instr.rename]

lemma program_deterministic : Deterministic program := noChoice_deterministic program_noChoice

def WellFramed : Set (List Bool) := {bits | ∃ fs,(EncodingTime.parse bits).1=some fs}

/-- All accepting executions are sound, even beyond the polynomial clock. -/
theorem accepting_sound (bits : List Bool) (t : ℕ) (c : Config Stack State)
    (hr : Run program t (initial program bits) c) (ha : accepts program c) : bits∈WellFramed := by
  cases hp : (EncodingTime.parse bits).1 with
  | some fs => exact ⟨fs,hp⟩
  | none =>
    obtain ⟨s,_,d,hs,hd⟩ := parse_reject bits [] hp
    rw [← initial_cfg] at hs
    exact False.elim (rejecting_run_excludes_acceptance program_deterministic hs hd hr ha)

theorem accepting_complete (bits : List Bool) (h : bits∈WellFramed) :
    ∃ t≤10*bits.length+2,∃ c,Run program t (initial program bits) c ∧ accepts program c := by
  obtain ⟨fs,hfs⟩ := h
  obtain ⟨t,ht,c,hr,ha,_⟩ := parsed_fields_outputs bits fs hfs
  exact ⟨t,ht,c,hr,ha⟩

/-- Any accepting output is precisely the tagged list produced by the original
raw parser, including empty fields and padded bit representations. -/
theorem accepting_output (bits : List Bool) (t : ℕ) (c : Config Stack State)
    (hr : Run program t (initial program bits) c) (ha : accepts program c) :
    ∃ fs,(EncodingTime.parse bits).1=some fs ∧ c.stk output=dataFields fs := by
  obtain ⟨fs,hfs⟩ := accepting_sound bits t c hr ha
  obtain ⟨u,_,d,hd,had,hout⟩ := parsed_fields_outputs bits fs hfs
  have he := hr.halted_unique program_deterministic hd ha had
  exact ⟨fs,hfs,by rw [he.2];exact hout⟩

/-- End-to-end operational regression for the actual compiler: the original
raw framing language is recognized by a concrete finite one-tape machine with
its proved polynomial clock. This is not a claim about the paper's NP language. -/
theorem wellFramed_inNP : NPMachine.InNP WellFramed := by
  apply Compile.recognition_inNP program (10*Polynomial.X+2) WellFramed accepting_sound
  intro bits h
  simpa using accepting_complete bits h

end BalancedAssortments.NPStackFields
