import BalancedAssortments.NPStackSourceFixedMembership
import BalancedAssortments.NPStackFieldExamples

namespace BalancedAssortments.NPStack.SourceVerifier.Fixed
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

/-- Run the literal signed-add/comparison instruction graph, rather than merely
its rational specification. Six minus three over three encodes alpha one. -/
private def redundantRegisters (capacity : List Bool) (negative : List Bool) : Registers
  | .capacity => (capacity,[])
  | .alpha => ([false,true,true],negative)
  | .alphaDen => ([true,true],[])
  | .one => zOne
  | _ => zzero

private def runGuard (s : Registers) : Bool :=
  let P := VerifierCommands.program command
  NPStackFieldExamples.accepted P (NPStackFieldExamples.executeFuel P 10000 (VerifierCommands.cfg command s))

#guard runGuard (redundantRegisters [false,true,false] [true,true])
#guard runGuard (redundantRegisters [false,true] [true,true])
#guard !runGuard (redundantRegisters [true] [true,true])
#guard !runGuard (redundantRegisters [true,true] [true,true])
#guard !runGuard (redundantRegisters [false,true] [])
#guard !runGuard (redundantRegisters [false,true] [true,false,true])

private def malformedRejects : Bool :=
  let out := NPStackFieldExamples.executeFuel program 100
    ⟨program.start,Header.store [true] [] (fun _=>[])⟩
  match program.code out.pc with | .halt false => true | _ => false

#guard malformedRejects

end BalancedAssortments.NPStack.SourceVerifier.Fixed
