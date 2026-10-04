import BalancedAssortments.NPStackStructuredAtoms
import BalancedAssortments.NPStackMultiplyCorrect

noncomputable section
namespace BalancedAssortments.NPStack.Structured
open NPStack
variable {K : Type*} [DecidableEq K]

def addMacro (a b work out : K) : Bool → Macros.Macro K Bool
  | false => .add a b work out false true
  | true => .halt true

def addAtom (a b work out : K) : Atom K :=
  let P := Macros.compile (addMacro a b work out) false a out
  atomOfProgram P (.main true) rfl (Macros.compile_noChoice _ _ _ _)

lemma addAtom_exec (a b work out : K) (hi : Function.Injective (Macros.addMap a b work out))
    (s : Store K) (hw : s work=[]) (ho : s out=[]) :
    Exec (.atom (addAtom a b work out)) s
      (Macros.writes s [(a,[]),(b,[]),(out,(ComplexityTimeBinary.addCarry (s a) (s b) false).1)])
      (5*max (s a).length (s b).length+8) := by
  let P := Macros.compile (addMacro a b work out) false a out
  have hh := Macros.add_call (addMacro a b work out) false a out (q := false) (next := true) rfl hi s hw ho
  exact Exec.of_program_run P (.main true) rfl (Macros.compile_noChoice _ _ _ _) hh a out

def multiplyAtom (regs : MulStack → K) : Atom K :=
  let P := relocateProgram multiplyProgram regs (regs .input) (regs .output)
  atomOfProgram P .done rfl (relocateProgram_noChoice _ _ _ _ multiply_noChoice)

lemma multiplyAtom_exec (regs : MulStack → K) (hi : Function.Injective regs) (s : Store K)
    (hz : ∀ k,k≠.input → k≠.factor → s (regs k)=[]) :
    ∃ n ≤ multiplicationBudget (s (regs .input)).length (s (regs .factor)).length,
      Exec (.atom (multiplyAtom regs)) s
        (Function.update (Function.update s (regs .input) []) (regs .output)
          (ComplexityTimeBinary.mulBits (s (regs .input)) (s (regs .factor))).1) n := by
  let P := relocateProgram multiplyProgram regs (regs .input) (regs .output)
  obtain ⟨n,hn,hr⟩ := multiplication_run (s (regs .input)) (s (regs .factor))
  have hneq (i j : MulStack) (h : i≠j) : regs i≠regs j := fun he => h (hi he)
  let target := Function.update (Function.update s (regs .input) []) (regs .output)
    (ComplexityTimeBinary.mulBits (s (regs .input)) (s (regs .factor))).1
  have he := hr.relocate_exact regs id hi (relocateProgram_extends multiplyProgram regs (regs .input) (regs .output))
    (c' := ⟨MulState.initial .read,s⟩) (d' := ⟨MulState.done,target⟩)
    (by
      constructor
      · rfl
      · intro k
        cases k <;> simp [multiplicationInput,mulStacks,hz])
    (by
      constructor
      · rfl
      · intro k
        cases k <;> simp [target,multiplicationOutput,Function.update,hneq,hz])
    (by
      intro k hk
      have h1 := Ne.symm (hk .input)
      have h2 := Ne.symm (hk .output)
      simp [target,Function.update,h1,h2])
  exact ⟨n,hn,Exec.of_program_run P .done rfl (relocateProgram_noChoice _ _ _ _ multiply_noChoice) he (regs .input) (regs .output)⟩

end BalancedAssortments.NPStack.Structured
