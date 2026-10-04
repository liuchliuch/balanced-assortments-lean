import BalancedAssortments.NPStackMachine
import BalancedAssortments.EncodingTime
import BalancedAssortments.FPTASCostSerialization

/-! Concrete finite Boolean-stack implementation of one self-delimiting raw
field parser. No list recursion or arithmetic is an instruction. -/
namespace BalancedAssortments.NPStackField
open NPStack

inductive Stack | input | count | reversed | output deriving DecidableEq, Fintype
inductive State | header | mark | consume | readBit | putFalse | putTrue |
  reverse | reverseFalse | reverseTrue | accept | reject deriving DecidableEq, Fintype

def program : Program Stack State where
  code
    | .header => .pop .input .reject .consume .mark
    | .mark => .push .count true .header
    | .consume => .pop .count .reverse .readBit .readBit
    | .readBit => .pop .input .reject .putFalse .putTrue
    | .putFalse => .push .reversed false .consume
    | .putTrue => .push .reversed true .consume
    | .reverse => .pop .reversed .accept .reverseFalse .reverseTrue
    | .reverseFalse => .push .output false .reverse
    | .reverseTrue => .push .output true .reverse
    | .accept => .halt true
    | .reject => .halt false
  start := .header
  inputStack := .input
  outputStack := .output

def cfg (q : State) (input count reversed output : List Bool) : Config Stack State :=
  ⟨q,fun k => match k with
    | .input => input
    | .count => count
    | .reversed => reversed
    | .output => output⟩

private lemma cfg_update (q : State) (i c r o xs : List Bool) (k : Stack) :
    (Function.update (cfg q i c r o).stk k xs) =
      (cfg q (if k=.input then xs else i) (if k=.count then xs else c)
        (if k=.reversed then xs else r) (if k=.output then xs else o)).stk := by
  funext j
  cases k <;> cases j <;> simp [cfg]

lemma header_true (i c r o : List Bool) :
    Run program 2 (cfg .header (true::i) c r o) (cfg .header i (true::c) r o) := by
  apply Run.succ (d := cfg .mark i c r o)
  · simp [Step,successors,program,cfg]; funext k; cases k <;> simp
  · apply Run.one
    simp [Step,successors,program,cfg]; funext k; cases k <;> simp

lemma header_false (i c r o : List Bool) :
    Run program 1 (cfg .header (false::i) c r o) (cfg .consume i c r o) := by
  apply Run.one
  simp [Step,successors,program,cfg]; funext k; cases k <;> simp

lemma header_prefix (payload suffix count rev out : List Bool) :
    Run program (2*payload.length+1)
      (cfg .header (List.replicate payload.length true ++ false::payload ++ suffix) count rev out)
      (cfg .consume (payload++suffix) (List.replicate payload.length true++count) rev out) := by
  generalize payload.length = n
  induction n generalizing count with
  | zero => simpa using header_false (payload++suffix) count rev out
  | succ n ih =>
    have hh := header_true (List.replicate n true ++ false::payload ++ suffix) count rev out
    have ht := ih (true::count)
    have he : List.replicate n true ++ true::count = List.replicate (n+1) true ++ count := by
      rw [List.replicate_succ']; simp only [List.append_assoc,List.singleton_append]
    rw [he] at ht
    have h := hh.trans ht
    simpa [List.replicate_succ,List.cons_append,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma consume_bit (b : Bool) (i c r o : List Bool) :
    Run program 3 (cfg .consume (b::i) (true::c) r o) (cfg .consume i c (b::r) o) := by
  apply Run.succ (d := cfg .readBit (b::i) c r o)
  · simp [Step,successors,program,cfg]; funext k; cases k <;> simp
  · cases b
    · apply Run.succ (d := cfg .putFalse i c r o)
      · simp [Step,successors,program,cfg]; funext k; cases k <;> simp
      · apply Run.one; simp [Step,successors,program,cfg]; funext k; cases k <;> simp
    · apply Run.succ (d := cfg .putTrue i c r o)
      · simp [Step,successors,program,cfg]; funext k; cases k <;> simp
      · apply Run.one; simp [Step,successors,program,cfg]; funext k; cases k <;> simp

lemma consume_empty (i r o : List Bool) :
    Run program 1 (cfg .consume i [] r o) (cfg .reverse i [] r o) := by
  apply Run.one; simp [Step,successors,program,cfg]

lemma consume_payload (payload suffix rev out : List Bool) :
    Run program (3*payload.length+1)
      (cfg .consume (payload++suffix) (List.replicate payload.length true) rev out)
      (cfg .reverse suffix [] (payload.reverse++rev) out) := by
  induction payload generalizing rev with
  | nil => simpa using consume_empty suffix rev out
  | cons b bs ih =>
    have hh := consume_bit b (bs++suffix) (List.replicate bs.length true) rev out
    have ht := ih (b::rev)
    have h := hh.trans ht
    simpa [List.replicate_succ,List.cons_append,List.reverse_cons,List.append_assoc,
      Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma reverse_bit (b : Bool) (i c r o : List Bool) :
    Run program 2 (cfg .reverse i c (b::r) o) (cfg .reverse i c r (b::o)) := by
  cases b
  · apply Run.succ (d := cfg .reverseFalse i c r o)
    · simp [Step,successors,program,cfg]; funext k; cases k <;> simp
    · apply Run.one; simp [Step,successors,program,cfg]; funext k; cases k <;> simp
  · apply Run.succ (d := cfg .reverseTrue i c r o)
    · simp [Step,successors,program,cfg]; funext k; cases k <;> simp
    · apply Run.one; simp [Step,successors,program,cfg]; funext k; cases k <;> simp

lemma reverse_empty (i c o : List Bool) :
    Run program 1 (cfg .reverse i c [] o) (cfg .accept i c [] o) := by
  apply Run.one; simp [Step,successors,program,cfg]

lemma reverse_payload (i c r o : List Bool) :
    Run program (2*r.length+1) (cfg .reverse i c r o) (cfg .accept i c [] (r.reverse++o)) := by
  induction r generalizing o with
  | nil => simpa using reverse_empty i c o
  | cons b r ih =>
    have hh := reverse_bit b i c r o
    have ht := ih (b::o)
    have h := hh.trans ht
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Seven concrete bytecode transitions per payload bit, plus three terminal
phase transitions. The untouched suffix remains on the input stack. -/
theorem field_run (payload suffix : List Bool) :
    Run program (7*payload.length+3)
      (cfg .header (FPTASCostProgram.serializeBits payload++suffix) [] [] [])
      (cfg .accept suffix [] [] payload) := by
  have hh := header_prefix payload suffix [] [] []
  have hc := consume_payload payload suffix [] []
  have hr := reverse_payload suffix [] payload.reverse []
  simp only [List.append_nil,List.reverse_reverse] at hh hc hr
  have h := (hh.trans hc).trans hr
  convert h using 1 <;> simp [FPTASCostProgram.serializeBits,List.append_assoc] <;> omega

end BalancedAssortments.NPStackField
