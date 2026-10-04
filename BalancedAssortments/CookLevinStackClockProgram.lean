import BalancedAssortments.CookLevinStackClockCorrect
import BalancedAssortments.NPPolynomialPrograms

noncomputable section
namespace BalancedAssortments.CookLevin.StackClock
open NPStack NPStack.Structured

def clockBits (e : FuelExpr) (word : List Bool) : List Bool :=
  List.replicate (e.polynomial.eval word.length) false

def clockProgram (e : FuelExpr) : FiniteProgram := finiteBlock (compile 1 e) 0 1

lemma clockProgram_noChoice (e : FuelExpr) : NoChoice (clockProgram e).program :=
  restrictProgram_noChoice (program (compile 1 e) 0 1) _
    (finiteRegisterBound_code _) (finiteRegisterBound_input _) (finiteRegisterBound_output _) (program_noChoice _ _ _)

lemma clockProgram_outputs (e : FuelExpr) (word : List Bool) :
    OutputsIn (clockProgram e).program word (clockBits e word) (timePolynomial e |>.eval word.length) := by
  let P := program (compile 1 e) 0 1
  let s : Store ℕ := Function.update (fun _ => []) 0 word
  have hf : Fresh s 1 (slots e) := by
    intro k hk hk'
    simp [s,Function.update,show k≠0 by omega]
  have he := compile_exec e 1 s (by decide) hf
  have hs0 : s 0=word := by simp [s]
  rw [hs0] at he
  have hout : OutputsIn P word (clockBits e word) ((timePolynomial e).eval word.length) := by
    refine ⟨_,le_rfl,⟨finish (compile 1 e),Function.update s 1 (clockBits e word)⟩,?_,?_,?_⟩
    · exact he.compiles 0 1
    · exact code_finish _
    · simp [P,program]
  exact finitelyNamed_outputs P hout

/-- Genuine finite Boolean-stack implementation of the entire polynomial-clock
front-end. Its time is bounded in original input length by a fixed polynomial,
and its original input register is preserved by the stronger source theorem. -/
def clockPolynomialProgram (e : FuelExpr) : PolynomialProgram (clockBits e) where
  code := clockProgram e
  noChoice := clockProgram_noChoice e
  clock := timePolynomial e
  computes := clockProgram_outputs e

/-- Every natural polynomial has a genuine primitive finite-stack unary-clock
transducer; this is stronger than a function with an attached semantic clock. -/
theorem every_polynomial_clock (p : Polynomial ℕ) :
    PolyComputable (fun word => List.replicate (p.eval word.length) false) := by
  obtain ⟨e,he⟩ := polynomial_has_fuel_program p
  have hh := clockPolynomialProgram e
  have hf : clockBits e=(fun word => List.replicate (p.eval word.length) false) := by
    funext word;simp [clockBits,he]
  rw [← hf]
  exact ⟨hh⟩

end BalancedAssortments.CookLevin.StackClock
