import BalancedAssortments.NPCNFStackReductionTotal
import BalancedAssortments.NPStackClockedCorrect

/-! Unconditional operational CNF-to-three-CNF many-one reduction on literal
Boolean inputs. Clock generation, source simulation, physical timeout and
invalid-input fallback are all finite primitive stack programs. -/
namespace BalancedAssortments.NPCNF.StackReduction
open NPStack Encoding

def finiteSource : FiniteProgram where
  K := Register
  Q := State
  program := program

/-- Genuine finite-program polynomial computability on EVERY binary input.
The unary clock is itself computed by certified finite bytecode, not supplied
by the input or treated as a free numerical limit. -/
theorem reduction_polyComputable : PolyComputable reduction := by
  apply Clocked.polyComputable finiteSource reduction GoodInput validClock failureBits program_noChoice
  · intro word t c hr ha
    exact accepting_output word hr ha
  · exact good_computes
  · exact reduction_of_not_good

/-- Total polynomial-time many-one reduction, using the project's explicit
finite Boolean-stack operational definition and its one-tape compiler. -/
theorem cnf_to_three_cnf : PolyManyOne {bits | CNFLanguage bits} {bits | ThreeCNFLanguage bits} :=
  ⟨reduction,reduction_polyComputable,fun bits=>(reduction_correct bits).symm⟩

end BalancedAssortments.NPCNF.StackReduction
