import BalancedAssortments.NPStackMachine

/-! An actual finite stack program for the self-delimiting raw wire field
`true^length ++ false :: payload`. It consumes a raw payload and prepends its
encoding to an existing suffix, charging every unary count and bit transfer. -/
namespace BalancedAssortments.NPStackFieldEncode
open NPStack

inductive Stack | input | reversed | count | output deriving DecidableEq, Fintype
inductive State | scan | save (b : Bool) | mark | restore | emit (b : Bool) | delimiter | header | one | accept
  deriving DecidableEq, Fintype

def store (i r c o : List Bool) : Stack → List Bool
  | .input => i
  | .reversed => r
  | .count => c
  | .output => o

def cfg (q : State) (i r c o : List Bool) : Config Stack State := ⟨q,store i r c o⟩

@[simp] lemma update_input (i r c o x : List Bool) : Function.update (store i r c o) .input x=store x r c o := by
  funext k; cases k <;> simp [store]
@[simp] lemma update_reversed (i r c o x : List Bool) : Function.update (store i r c o) .reversed x=store i x c o := by
  funext k; cases k <;> simp [store]
@[simp] lemma update_count (i r c o x : List Bool) : Function.update (store i r c o) .count x=store i r x o := by
  funext k; cases k <;> simp [store]
@[simp] lemma update_output (i r c o x : List Bool) : Function.update (store i r c o) .output x=store i r c x := by
  funext k; cases k <;> simp [store]

def program : Program Stack State where
  start := .scan
  inputStack := .input
  outputStack := .output
  code
    | .scan => .pop .input .restore (.save false) (.save true)
    | .save b => .push .reversed b .mark
    | .mark => .push .count true .scan
    | .restore => .pop .reversed .delimiter (.emit false) (.emit true)
    | .emit b => .push .output b .restore
    | .delimiter => .push .output false .header
    | .header => .pop .count .accept .one .one
    | .one => .push .output true .header
    | .accept => .halt true

lemma scan_run (i r c o : List Bool) :
    Run program (3*i.length+1) (cfg .scan i r c o)
      (cfg .restore [] (i.reverse++r) (List.replicate i.length true++c) o) := by
  induction i generalizing r c with
  | nil => apply Run.one; simp [Step,successors,program,cfg,store]
  | cons b bs ih =>
    have h1 : Step program (cfg .scan (b::bs) r c o) (cfg (.save b) bs r c o) := by
      cases b <;> simp [Step,successors,program,cfg,store]
    have h2 : Step program (cfg (.save b) bs r c o) (cfg .mark bs (b::r) c o) := by
      simp [Step,successors,program,cfg,store]
    have h3 : Step program (cfg .mark bs (b::r) c o) (cfg .scan bs (b::r) (true::c) o) := by
      simp [Step,successors,program,cfg,store]
    have hh := Run.succ h1 (Run.succ h2 (Run.succ h3 (ih (b::r) (true::c))))
    have he : List.replicate bs.length true++true::c=List.replicate (bs.length+1) true++c := by
      rw [List.replicate_succ']; simp only [List.append_assoc,List.singleton_append]
    rw [he] at hh
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

lemma restore_run (i r c o : List Bool) :
    Run program (2*r.length+1) (cfg .restore i r c o)
      (cfg .delimiter i [] c (r.reverse++o)) := by
  induction r generalizing o with
  | nil => apply Run.one; simp [Step,successors,program,cfg,store]
  | cons b bs ih =>
    have h1 : Step program (cfg .restore i (b::bs) c o) (cfg (.emit b) i bs c o) := by
      cases b <;> simp [Step,successors,program,cfg,store]
    have h2 : Step program (cfg (.emit b) i bs c o) (cfg .restore i bs c (b::o)) := by
      simp [Step,successors,program,cfg,store]
    have hh := Run.succ h1 (Run.succ h2 (ih (b::o)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

lemma header_run (i r c o : List Bool) :
    Run program (2*c.length+1) (cfg .header i r c o)
      (cfg .accept i r [] (List.replicate c.length true++o)) := by
  induction c generalizing o with
  | nil => apply Run.one; simp [Step,successors,program,cfg,store]
  | cons b bs ih =>
    have h1 : Step program (cfg .header i r (b::bs) o) (cfg .one i r bs o) := by
      cases b <;> simp [Step,successors,program,cfg,store]
    have h2 : Step program (cfg .one i r bs o) (cfg .header i r bs (true::o)) := by
      simp [Step,successors,program,cfg,store]
    have hh := Run.succ h1 (Run.succ h2 (ih (true::o)))
    have he : List.replicate bs.length true++true::o=List.replicate (bs.length+1) true++o := by
      rw [List.replicate_succ']; simp only [List.append_assoc,List.singleton_append]
    rw [he] at hh
    simpa [Nat.mul_add,Nat.add_assoc] using hh

/-- Fully charged wire serialization, with exact payload order and an arbitrary
already-serialized suffix. No length or encoding operation is a primitive. -/
theorem encode_field (bits suffix : List Bool) :
    Run program (7*bits.length+4) (cfg .scan bits [] [] suffix)
      (cfg .accept [] [] [] (List.replicate bits.length true++false::(bits++suffix))) := by
  have h1 := scan_run bits [] [] suffix
  simp only [List.append_nil] at h1
  have h2 := restore_run [] bits.reverse (List.replicate bits.length true) suffix
  simp only [List.length_reverse,List.reverse_reverse] at h2
  have h3 : Step program (cfg .delimiter [] [] (List.replicate bits.length true) (bits++suffix))
      (cfg .header [] [] (List.replicate bits.length true) (false::(bits++suffix))) := by
    simp [Step,successors,program,cfg,store]
  have h4 := header_run [] [] (List.replicate bits.length true) (false::(bits++suffix))
  simp only [List.length_replicate] at h4
  have hh := h1.trans (h2.trans (Run.succ h3 h4))
  convert hh using 1 <;> omega

def finiteEncoder : FiniteProgram where
  K := Stack
  Q := State
  program := program

end BalancedAssortments.NPStackFieldEncode
