import BalancedAssortments.NPCNFStackReductionTotal

/-! Executable end-to-end bytecode regressions. These execute the concrete
finite raw-input pipeline, not the semantic reduction specification. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace BalancedAssortments.NPCNF.StackReduction.Examples
open NPStack Encoding StackReduction

def outputAt (n : ℕ) (bits : List Bool) : Option (List Bool) :=
  (firstRun program n (initial program bits)).map (fun c=>c.stk output)

def emptyFormula : Raw := ⟨[],[]⟩
def emptyClause : Raw := ⟨[],[[]]⟩
def zeroUnit : Raw := ⟨[[]],[[⟨[],true⟩]]⟩

#guard outputAt (successCost emptyFormula) (encode emptyFormula)=some (encode (successResult emptyFormula))
#guard outputAt (successCost emptyClause) (encode emptyClause)=some (encode (successResult emptyClause))
#guard outputAt (successCost zeroUnit) (encode zeroUnit)=some (encode (successResult zeroUnit))

def repeatedPadded : Raw := ⟨[[false,false]],[[⟨[],true⟩,⟨[],true⟩,⟨[],false⟩,⟨[],true⟩]]⟩
#guard outputAt (successCost repeatedPadded) (encode repeatedPadded)=some (encode (successResult repeatedPadded))

/-- Bounded executable test harness, separate from the compiled source program. -/
def outputWithinAux : ℕ → Config Register State → Option (List Bool)
  | 0,_ => none
  | n+1,c => match program.code c.pc with
    | .halt _ => some (c.stk output)
    | _ => match successors program c with
      | [] => none
      | d::_ => outputWithinAux n d

def outputWithin (fuel : ℕ) (bits : List Bool) := outputWithinAux fuel (initial program bits)

#guard outputWithin 100 []=some failureBits
#guard outputWithin 3000 (encode (⟨[[],[false]],[]⟩ : Raw))=some failureBits
#guard outputWithin 3000 (encode (⟨[],[[⟨[],true⟩]]⟩ : Raw))=some failureBits

end BalancedAssortments.NPCNF.StackReduction.Examples
