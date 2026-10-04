import BalancedAssortments.NPStackFieldData
import BalancedAssortments.NPStackFieldEncode
import BalancedAssortments.NPStackDeterministic

namespace BalancedAssortments.NPStackFieldData
open NPStack
open NPStackFields (tagBits dataFields)

lemma read_deterministic : Deterministic readProgram := by
  apply noChoice_deterministic
  intro q a b; cases q <;> simp [readProgram]

lemma emit_deterministic : Deterministic emitProgram := by
  apply noChoice_deterministic
  intro q a b; cases q <;> simp [emitProgram]

lemma readTagged_sound (input bits suffix : List Bool) (h : readTagged input=some (bits,suffix)) :
    input=tagBits bits++false::suffix := by
  induction input using readTagged.induct generalizing bits with
  | case1 => simp [readTagged] at h
  | case2 xs =>
    simp only [readTagged,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩; rfl
  | case3 => simp [readTagged] at h
  | case4 b xs ih =>
    cases hx : readTagged xs with
    | none => simp [readTagged,hx] at h
    | some p =>
      rcases p with ⟨ys,zs⟩
      simp only [readTagged,hx,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have he := ih ys hx
      simp [tagBits,he]

/-- Soundness covers every accepting execution and every input, including
malformed streams; the output and exact halting time are unique. -/
theorem read_accepting_result (input out : List Bool) {t : ℕ} {d : Config Stack ReadState}
    (hr : Run readProgram t (readConfig .tag input [] out) d) (ha : accepts readProgram d) :
    ∃ bits suffix,readTagged input=some (bits,suffix) ∧
      d=readConfig .accept suffix [] (bits++out) ∧ t=5*bits.length+2 := by
  cases hp : readTagged input with
  | none =>
    obtain ⟨u,_,s,hu⟩ := read_rejects input out hp
    exact False.elim (rejecting_run_excludes_acceptance read_deterministic hu rfl hr ha)
  | some p =>
    rcases p with ⟨bits,suffix⟩
    have he := readTagged_sound input bits suffix hp
    have hc := read_field bits suffix out
    rw [←he] at hc
    have hh := hc.halted_unique read_deterministic hr rfl ha
    exact ⟨bits,suffix,rfl,hh.2.symm,hh.1.symm⟩

theorem emit_accepting_result (bits acc : List Bool) {t : ℕ} {d : Config Stack EmitState}
    (hr : Run emitProgram t (emitConfig .reverse bits [] acc) d) (ha : accepts emitProgram d) :
    d=emitConfig .accept [] [] (tagBits bits++false::acc) ∧ t=5*bits.length+3 := by
  have hh := (emit_field bits acc).halted_unique emit_deterministic hr rfl ha
  exact ⟨hh.2.symm,hh.1.symm⟩

def finiteReader : FiniteProgram where
  K := Stack
  Q := ReadState
  program := readProgram

def finiteEmitter : FiniteProgram where
  K := Stack
  Q := EmitState
  program := emitProgram

end BalancedAssortments.NPStackFieldData

namespace BalancedAssortments.NPStackFieldEncode
open NPStack

lemma program_deterministic : Deterministic program := by
  apply noChoice_deterministic
  intro q a b; cases q <;> simp [program]

theorem encode_accepting_result (bits suffix : List Bool) {t : ℕ} {d : Config Stack State}
    (hr : Run program t (cfg .scan bits [] [] suffix) d) (ha : accepts program d) :
    d=cfg .accept [] [] [] (List.replicate bits.length true++false::(bits++suffix)) ∧
      t=7*bits.length+4 := by
  have hh := (encode_field bits suffix).halted_unique program_deterministic hr rfl ha
  exact ⟨hh.2.symm,hh.1.symm⟩

end BalancedAssortments.NPStackFieldEncode
