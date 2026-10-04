import BalancedAssortments.NPStackClockedCorrect
import BalancedAssortments.NPStackFiniteExec

/-! Executable checks of real timeout/fallback wiring, including a looping
source whose nonempty output register must be cleared on fuel exhaustion. -/
namespace BalancedAssortments.NPStack.Clocked.Examples
open NPStack

def identitySource : FiniteProgram where
  K := Bool
  Q := Unit
  program := ⟨fun _=>.halt true,(),false,false⟩

def loopingSource : FiniteProgram where
  K := Bool
  Q := Unit
  program := ⟨fun _=>.jump (),(),false,false⟩

def zeroClock : FiniteProgram where
  K := Bool
  Q := Unit
  program := ⟨fun _=>.halt true,(),false,true⟩

def resultAt (P : FiniteProgram) (fallback word : List Bool) (fuel : ℕ) : Option (List Bool) :=
  (firstRun (program P zeroClock fallback) fuel (initial (program P zeroClock fallback) word)).map
    (fun c=>c.stk (output P zeroClock))

#guard resultAt identitySource [false] [true,false,true] 23=some [true,false,true]
#guard resultAt loopingSource [false] [true,false,true] 30=some [false]
#guard resultAt loopingSource [true,false] [] 13=some [true,false]

end BalancedAssortments.NPStack.Clocked.Examples
