import BalancedAssortments.NPStackCompile
import BalancedAssortments.NPStackDeterministic

/-! Polynomial reductions are certified by actual finite deterministic
Boolean-stack programs, not by a semantic map with an attached clock. The
existing quantitative compiler supplies concrete one-tape realizations. -/
namespace BalancedAssortments.NPStack

structure PolynomialProgram (f : List Bool → List Bool) where
  code : FiniteProgram
  noChoice : NoChoice code.program
  clock : Polynomial ℕ
  computes : ∀ bits,OutputsIn code.program bits (f bits) (clock.eval bits.length)

def PolyComputable (f : List Bool → List Bool) : Prop := Nonempty (PolynomialProgram f)

/-- Actual deterministic polynomial-time many-one reduction between total
binary languages. Every input has a bounded accepting output computation. -/
def PolyManyOne (A B : Set (List Bool)) : Prop :=
  ∃ f : List Bool → List Bool,PolyComputable f ∧ ∀ bits,bits∈A ↔ f bits∈B

def NPComplete (L : Set (List Bool)) : Prop :=
  NPMachine.InNP L ∧ ∀ A,NPMachine.InNP A → PolyManyOne A L

/-- No different output is possible, including on executions beyond the clock.
This follows from the finite program, not from restricting its semantics. -/
theorem PolynomialProgram.output_unique {f : List Bool → List Bool} (p : PolynomialProgram f)
    (bits : List Bool) (t : ℕ) (c : Config p.code.K p.code.Q)
    (hr : Run p.code.program t (initial p.code.program bits) c) (ha : accepts p.code.program c) :
    c.stk p.code.program.outputStack=f bits := by
  obtain ⟨s,_,d,hd,haccept,hout⟩ := p.computes bits
  have he := hr.halted_unique (noChoice_deterministic p.noChoice) hd ha haccept
  rw [he.2]
  exact hout

/-- Output size is bounded by the input and actual transition clock because
one primitive step pushes at most one Boolean cell. -/
theorem PolynomialProgram.output_length {f : List Bool → List Bool} (p : PolynomialProgram f)
    (bits : List Bool) : (f bits).length≤bits.length+p.clock.eval bits.length := by
  obtain ⟨t,ht,c,hr,_,hout⟩ := p.computes bits
  have hh := hr.stack_length p.code.program.outputStack
  have hi : ((initial p.code.program bits).stk p.code.program.outputStack).length≤bits.length := by
    by_cases h : p.code.program.outputStack=p.code.program.inputStack
    · simp [initial,h]
    · simp [initial,Function.update_apply,h]
  rw [hout] at hh
  omega

end BalancedAssortments.NPStack
