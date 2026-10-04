import BalancedAssortments.NPStackFieldCorrect
import BalancedAssortments.NPStackFieldsCorrect

/-! Executed operational regressions, separate from kernel-proved correctness.
No native evaluation is used to prove a theorem. -/
namespace BalancedAssortments.NPStackFieldExamples
open NPStack

def executeFuel {K Q : Type} [DecidableEq K] (P : Program K Q) : ℕ → Config K Q → Config K Q
  | 0,c => c
  | n+1,c => match (successors P c).head? with
    | none => c
    | some d => executeFuel P n d

def accepted {K Q : Type} (P : Program K Q) (c : Config K Q) : Bool :=
  match P.code c.pc with | .halt b => b | _ => false

def checkField (bits expected : List Bool) (accept : Bool) : Bool :=
  let P := NPStackField.program
  let c := executeFuel P (7*bits.length+5) (initial P bits)
  accepted P c==accept && (!accept || c.stk P.outputStack==expected)

def checkFields (bits expected : List Bool) (accept : Bool) : Bool :=
  let P := NPStackFields.program
  let c := executeFuel P (10*bits.length+5) (initial P bits)
  accepted P c==accept && (!accept || c.stk P.outputStack==expected)

#eval do
  let tests := [
    ("empty field",checkField [false] [] true),
    ("padded zero field",checkField [true,true,false,false,false] [false,false] true),
    ("unterminated header",checkField [true,true] [] false),
    ("short payload",checkField [true,true,false,true] [] false),
    ("empty field list",checkFields [] [] true),
    ("two empty fields",checkFields [false,false] [false,false] true),
    ("two fields",checkFields [true,false,true,false] [true,true,false,false] true),
    ("invalid suffix",checkFields [false,true] [] false)]
  for (name,ok) in tests do
    if !ok then throw (IO.userError s!"operational regression failed: {name}")
  IO.println "PASS: raw-field and field-list finite-program operational regressions"

end BalancedAssortments.NPStackFieldExamples
