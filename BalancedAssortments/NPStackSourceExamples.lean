import BalancedAssortments.NPStackSourcePolynomial

/-! Executed smoke checks of the actual primitive transducer, not merely its
semantic reduction specification. The universal correctness proof is separate. -/
namespace BalancedAssortments.NPStackSourceReduction
open NPStack ComplexityEncoding

def smokeRun : ℕ → Config Reg (Macros.Label Stage) → Option (List Bool)
  | 0,_ => none
  | fuel+1,c =>
    match program.code c.pc with
    | .halt true => some (c.stk .wireOut)
    | .halt false => none
    | _ => match successors program c with
      | [] => none
      | next::_ => smokeRun fuel next

def smokeCheck (bits : List Bool) : Bool :=
  (smokeRun 20000 (initial program bits)).map (fun out => out==reductionSpec bits) |>.getD false

#guard smokeCheck (encodeFields [3,1,2])
#guard smokeCheck (encodeFields [3,4])
#guard smokeCheck (encodeFields [3,0])
#guard smokeCheck (encodeFields [3])
#guard smokeCheck (encodeFields [0,1])
#guard smokeCheck []
#guard smokeCheck [true]
#guard smokeCheck (FPTASCostProgram.serializeBits [true,false,false]++FPTASCostProgram.serializeBits [true,false])

end BalancedAssortments.NPStackSourceReduction
