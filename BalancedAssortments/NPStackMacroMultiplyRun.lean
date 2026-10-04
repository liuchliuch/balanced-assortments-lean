import BalancedAssortments.NPStackMacroData

namespace BalancedAssortments.NPStack.Macros
open NPStack
variable {K Q : Type*} [DecidableEq K]

/-- Multiplication is expanded into the finite bitwise primitive program.
The factor and every register outside the supplied map are preserved. -/
theorem multiply_call (m : Q → Macro K Q) (start : Q) (input output : K)
    {q next : Q} {regs : MulStack → K} (hm : m q=.multiply regs next)
    (hi : Function.Injective regs) (s : K → List Bool)
    (hz : ∀k,k≠.input → k≠.factor → s (regs k)=[]) :
    ∃t ≤ multiplicationBudget (s (regs .input)).length (s (regs .factor)).length+2,
      Run (compile m start input output) t ⟨.main q,s⟩
        ⟨.main next,writes s [(regs .input,[]),(regs .output,
          (ComplexityTimeBinary.mulBits (s (regs .input)) (s (regs .factor))).1)]⟩ := by
  obtain ⟨t,ht,hr⟩ := multiplication_run (s (regs .input)) (s (regs .factor))
  refine ⟨t+2,by omega,?_⟩
  have hh := call_run_writes (R := compile m start input output) regs
    (fun st => Label.local q (.multiply st)) hi (multiply_extends m start input output hm)
    hr (.main q) (.main next) s
    [(MulStack.input,[]),(MulStack.output,(ComplexityTimeBinary.mulBits (s (regs .input)) (s (regs .factor))).1)]
    (by simp [compile,code,hm,multiplicationInput])
    (by simp [compile,code,hm,multiplicationOutput,returnCode,multiplyProgram])
    (by intro k;cases k <;> simp [multiplicationInput,mulStacks,hz])
    (by funext k;cases k <;> simp [writes,multiplicationInput,mulStacks,multiplicationOutput])
  simpa using hh

end BalancedAssortments.NPStack.Macros
