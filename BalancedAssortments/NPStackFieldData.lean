import BalancedAssortments.NPStackFields

/-! Finite Boolean-stack operations on tagged field streams. A true tag is
followed by one payload bit; false terminates a field, including an empty one.
Every transition is a primitive stack push/pop, with explicit linear counts. -/
namespace BalancedAssortments.NPStackFieldData
open NPStack
open NPStackFields (tagBits dataFields)

inductive Stack | input | scratch | output deriving DecidableEq, Fintype
inductive ReadState | tag | bit | save (b : Bool) | reverse | emit (b : Bool) | accept | reject
  deriving DecidableEq, Fintype

def dataStacks (i s o : List Bool) : Stack → List Bool
  | .input => i
  | .scratch => s
  | .output => o

def readConfig (q : ReadState) (i s o : List Bool) : Config Stack ReadState := ⟨q,dataStacks i s o⟩

@[simp] lemma update_input (i s o x : List Bool) : Function.update (dataStacks i s o) .input x=dataStacks x s o := by
  funext k; cases k <;> simp [dataStacks]
@[simp] lemma update_scratch (i s o x : List Bool) : Function.update (dataStacks i s o) .scratch x=dataStacks i x o := by
  funext k; cases k <;> simp [dataStacks]
@[simp] lemma update_output (i s o x : List Bool) : Function.update (dataStacks i s o) .output x=dataStacks i s x := by
  funext k; cases k <;> simp [dataStacks]

def readProgram : Program Stack ReadState where
  start := .tag
  inputStack := .input
  outputStack := .output
  code
    | .tag => .pop .input .reject .reverse .bit
    | .bit => .pop .input .reject (.save false) (.save true)
    | .save b => .push .scratch b .tag
    | .reverse => .pop .scratch .accept (.emit false) (.emit true)
    | .emit b => .push .output b .reverse
    | .accept => .halt true
    | .reject => .halt false

lemma read_pair (b : Bool) (i s o : List Bool) :
    Run readProgram 3 (readConfig .tag (true::b::i) s o) (readConfig .tag i (b::s) o) := by
  have h1 : Step readProgram (readConfig .tag (true::b::i) s o) (readConfig .bit (b::i) s o) := by
    simp [Step,successors,readProgram,readConfig,dataStacks]
  have h2 : Step readProgram (readConfig .bit (b::i) s o) (readConfig (.save b) i s o) := by
    cases b <;> simp [Step,successors,readProgram,readConfig,dataStacks]
  have h3 : Step readProgram (readConfig (.save b) i s o) (readConfig .tag i (b::s) o) := by
    simp [Step,successors,readProgram,readConfig,dataStacks]
  exact .succ h1 (.succ h2 (.one h3))

lemma read_pairs (bits i s o : List Bool) :
    Run readProgram (3*bits.length) (readConfig .tag (tagBits bits++i) s o)
      (readConfig .tag i (bits.reverse++s) o) := by
  induction bits generalizing s with
  | nil => simpa [tagBits] using Run.zero (P:=readProgram) (readConfig .tag i s o)
  | cons b bs ih =>
    have hh := (read_pair b (tagBits bs++i) s o).trans (ih (b::s))
    simpa [tagBits,List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh

lemma read_reverse (i s o : List Bool) :
    Run readProgram (2*s.length+1) (readConfig .reverse i s o)
      (readConfig .accept i [] (s.reverse++o)) := by
  induction s generalizing o with
  | nil => apply Run.one; simp [Step,successors,readProgram,readConfig,dataStacks]
  | cons b bs ih =>
    have h1 : Step readProgram (readConfig .reverse i (b::bs) o) (readConfig (.emit b) i bs o) := by
      cases b <;> simp [Step,successors,readProgram,readConfig,dataStacks]
    have h2 : Step readProgram (readConfig (.emit b) i bs o) (readConfig .reverse i bs (b::o)) := by
      simp [Step,successors,readProgram,readConfig,dataStacks]
    have hh := Run.succ h1 (Run.succ h2 (ih (b::o)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

/-- Extract exactly one field, preserving the remaining stream and an optional
existing output suffix. Empty fields are distinguished from an empty stream. -/
theorem read_field (bits suffix out : List Bool) :
    Run readProgram (5*bits.length+2)
      (readConfig .tag (tagBits bits++false::suffix) [] out)
      (readConfig .accept suffix [] (bits++out)) := by
  have h1 := read_pairs bits (false::suffix) [] out
  simp only [List.append_nil] at h1
  have h2 : Step readProgram (readConfig .tag (false::suffix) bits.reverse out)
      (readConfig .reverse suffix bits.reverse out) := by
    simp [Step,successors,readProgram,readConfig,dataStacks]
  have hh := h1.trans (Run.succ h2 (read_reverse suffix bits.reverse out))
  simp only [List.length_reverse,List.reverse_reverse] at hh
  convert hh using 1 <;> omega

def readTagged : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false::xs => some ([],xs)
  | true::[] => none
  | true::b::xs => (readTagged xs).map (fun p => (b::p.1,p.2))

theorem readTagged_field (bits suffix : List Bool) :
    readTagged (tagBits bits++false::suffix)=some (bits,suffix) := by
  induction bits with
  | nil => simp [tagBits,readTagged]
  | cons b bs ih => simpa [tagBits,readTagged] using congrArg (Option.map (fun p => (b::p.1,p.2))) ih

lemma readTagged_failure (input : List Bool) (h : readTagged input=none) :
    ∃ bits,input=tagBits bits ∨ input=tagBits bits++[true] := by
  induction input using readTagged.induct with
  | case1 => exact ⟨[],Or.inl rfl⟩
  | case2 xs => simp [readTagged] at h
  | case3 => exact ⟨[],Or.inr rfl⟩
  | case4 b xs ih =>
    have hx : readTagged xs=none := by simpa [readTagged] using h
    obtain ⟨bits,hb|hb⟩ := ih hx
    · exact ⟨b::bits,Or.inl (by simp [tagBits,hb])⟩
    · exact ⟨b::bits,Or.inr (by simp [tagBits,hb])⟩

lemma reject_missing_terminator (bits out : List Bool) :
    Run readProgram (3*bits.length+1) (readConfig .tag (tagBits bits) [] out)
      (readConfig .reject [] bits.reverse out) := by
  have h1 := read_pairs bits [] [] out
  simp only [List.append_nil] at h1
  have h2 : Step readProgram (readConfig .tag [] bits.reverse out) (readConfig .reject [] bits.reverse out) := by
    simp [Step,successors,readProgram,readConfig,dataStacks]
  exact h1.trans (.one h2)

lemma reject_missing_bit (bits out : List Bool) :
    Run readProgram (3*bits.length+2) (readConfig .tag (tagBits bits++[true]) [] out)
      (readConfig .reject [] bits.reverse out) := by
  have h1 := read_pairs bits [true] [] out
  simp only [List.append_nil] at h1
  have h2 : Step readProgram (readConfig .tag [true] bits.reverse out) (readConfig .bit [] bits.reverse out) := by
    simp [Step,successors,readProgram,readConfig,dataStacks]
  have h3 : Step readProgram (readConfig .bit [] bits.reverse out) (readConfig .reject [] bits.reverse out) := by
    simp [Step,successors,readProgram,readConfig,dataStacks]
  exact h1.trans (.succ h2 (.one h3))

@[simp] lemma tagBits_length (bits : List Bool) : (tagBits bits).length=2*bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [tagBits] at *; omega

/-- Every malformed first-field encoding is rejected by the actual finite
program within a linear number of primitive transitions. -/
theorem read_rejects (input out : List Bool) (h : readTagged input=none) :
    ∃ t≤3*input.length+2,∃ scratch,Run readProgram t (readConfig .tag input [] out)
      (readConfig .reject [] scratch out) := by
  obtain ⟨bits,hb|hb⟩ := readTagged_failure input h
  · subst input
    exact ⟨3*bits.length+1,by simp;omega,bits.reverse,reject_missing_terminator bits out⟩
  · subst input
    exact ⟨3*bits.length+2,by simp;omega,bits.reverse,reject_missing_bit bits out⟩

inductive EmitState | reverse | save (b : Bool) | delimiter | read | bit (b : Bool) | tag | accept
  deriving DecidableEq, Fintype

def emitConfig (q : EmitState) (i s o : List Bool) : Config Stack EmitState := ⟨q,dataStacks i s o⟩

def emitProgram : Program Stack EmitState where
  start := .reverse
  inputStack := .input
  outputStack := .output
  code
    | .reverse => .pop .input .delimiter (.save false) (.save true)
    | .save b => .push .scratch b .reverse
    | .delimiter => .push .output false .read
    | .read => .pop .scratch .accept (.bit false) (.bit true)
    | .bit b => .push .output b .tag
    | .tag => .push .output true .read
    | .accept => .halt true

lemma emit_reverse (i s o : List Bool) :
    Run emitProgram (2*i.length+1) (emitConfig .reverse i s o)
      (emitConfig .delimiter [] (i.reverse++s) o) := by
  induction i generalizing s with
  | nil => apply Run.one; simp [Step,successors,emitProgram,emitConfig,dataStacks]
  | cons b bs ih =>
    have h1 : Step emitProgram (emitConfig .reverse (b::bs) s o) (emitConfig (.save b) bs s o) := by
      cases b <;> simp [Step,successors,emitProgram,emitConfig,dataStacks]
    have h2 : Step emitProgram (emitConfig (.save b) bs s o) (emitConfig .reverse bs (b::s) o) := by
      simp [Step,successors,emitProgram,emitConfig,dataStacks]
    have hh := Run.succ h1 (Run.succ h2 (ih (b::s)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

lemma emit_pairs (bits i out : List Bool) :
    Run emitProgram (3*bits.length+1) (emitConfig .read i bits out)
      (emitConfig .accept i [] (tagBits bits.reverse++out)) := by
  induction bits generalizing out with
  | nil => apply Run.one; simp [Step,successors,emitProgram,emitConfig,dataStacks,tagBits]
  | cons b bs ih =>
    have h1 : Step emitProgram (emitConfig .read i (b::bs) out) (emitConfig (.bit b) i bs out) := by
      cases b <;> simp [Step,successors,emitProgram,emitConfig,dataStacks]
    have h2 : Step emitProgram (emitConfig (.bit b) i bs out) (emitConfig .tag i bs (b::out)) := by
      simp [Step,successors,emitProgram,emitConfig,dataStacks]
    have h3 : Step emitProgram (emitConfig .tag i bs (b::out)) (emitConfig .read i bs (true::b::out)) := by
      simp [Step,successors,emitProgram,emitConfig,dataStacks]
    have hh := Run.succ h1 (Run.succ h2 (Run.succ h3 (ih (true::b::out))))
    simpa [tagBits,List.reverse_cons,List.flatMap_append,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

/-- Consume a raw payload and prepend one complete tagged field to the
accumulator. Both empty payloads and empty accumulators are supported. -/
theorem emit_field (bits acc : List Bool) :
    Run emitProgram (5*bits.length+3) (emitConfig .reverse bits [] acc)
      (emitConfig .accept [] [] (tagBits bits++false::acc)) := by
  have h1 := emit_reverse bits [] acc
  simp only [List.append_nil] at h1
  have h2 : Step emitProgram (emitConfig .delimiter [] bits.reverse acc)
      (emitConfig .read [] bits.reverse (false::acc)) := by
    simp [Step,successors,emitProgram,emitConfig,dataStacks]
  have hh := h1.trans (Run.succ h2 (emit_pairs bits.reverse [] (false::acc)))
  simp only [List.length_reverse,List.reverse_reverse] at hh
  convert hh using 1 <;> omega

end BalancedAssortments.NPStackFieldData
