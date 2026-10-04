import BalancedAssortments.NPStackStructuredAtoms
import BalancedAssortments.NPStackLabelEqual
import BalancedAssortments.NPStackMacroDataRuns

noncomputable section
namespace BalancedAssortments.NPStack.Structured
open NPStack ComplexityTimeBinary
variable {K : Type*} [DecidableEq K]

def equalAtom (left right out : K) : Atom K :=
  let P := relocateProgram NPStackLabelEqual.program (Macros.normalizeMap left right out) left out
  atomOfProgram P .done rfl (relocateProgram_noChoice _ _ _ _ NPStackLabelEqual.program_noChoice)

lemma equalAtom_exec (left right out : K) (hi : Function.Injective (Macros.normalizeMap left right out))
    (s : Store K) :
    Exec (.atom (equalAtom left right out)) s
      (Macros.writes s [(left,[]),(right,[]),(out,decide (value (s left)=value (s right))::s out)])
      (2*max (s left).length (s right).length+3) := by
  let P := relocateProgram NPStackLabelEqual.program (Macros.normalizeMap left right out) left out
  have hr := NPStackLabelEqual.equal_run (s left) (s right) (s out)
  have hneq (i j : CompareStack) (h : i≠j) :
      Macros.normalizeMap left right out i≠Macros.normalizeMap left right out j := fun he => h (hi he)
  have hlr : left≠right := hneq .left .right (by decide)
  have hlo : left≠out := hneq .left .result (by decide)
  have hro : right≠out := hneq .right .result (by decide)
  have he := hr.relocate_exact (Macros.normalizeMap left right out) id hi
    (relocateProgram_extends NPStackLabelEqual.program _ left out)
    (c' := ⟨CompareState.readLeft .eq,s⟩)
    (d' := ⟨CompareState.done,Macros.writes s [(left,[]),(right,[]),(out,decide (value (s left)=value (s right))::s out)]⟩)
    (by constructor;rfl;intro k;cases k <;> rfl)
    (by constructor;rfl;intro k;cases k <;> simp [Macros.writes,Macros.normalizeMap,compareConfig,compareStacks,Function.update,hlr,hlo,hro])
    (by
      intro k hk
      have h1 := Ne.symm (hk .left)
      have h2 := Ne.symm (hk .right)
      have h3 := Ne.symm (hk .result)
      change k≠left at h1
      change k≠right at h2
      change k≠out at h3
      simp [Macros.writes,Function.update,h1,h2,h3])
  exact Exec.of_program_run P .done rfl (relocateProgram_noChoice _ _ _ _ NPStackLabelEqual.program_noChoice) he left out

def taggedReadMacro (input scratch out : K) : Option Bool → Macros.Macro K (Option Bool)
  | none => .taggedRead input scratch out (some true) (some false)
  | some b => .halt b

def taggedReadAtom (input scratch out : K) : Atom K :=
  let P := Macros.compile (taggedReadMacro input scratch out) none input out
  atomOfProgram P (.main (some true)) rfl (Macros.compile_noChoice _ _ _ _)

lemma taggedReadAtom_exec (input scratch out : K)
    (his : input≠scratch) (hio : input≠out) (hso : scratch≠out)
    (s : Store K) (bits rest : List Bool)
    (hi : s input=NPStackFields.tagBits bits++false::rest) (hs : s scratch=[]) :
    Exec (.atom (taggedReadAtom input scratch out)) s
      (Function.update (Function.update s input rest) out (bits++s out))
      (5*bits.length+4) := by
  let P := Macros.compile (taggedReadMacro input scratch out) none input out
  have hh := Macros.taggedRead_call (taggedReadMacro input scratch out) none input out
    (q := none) (yes := some true) (no := some false) rfl his hio hso s bits rest hi hs
  exact Exec.of_program_run P (.main (some true)) rfl (Macros.compile_noChoice _ _ _ _) hh input out

end BalancedAssortments.NPStack.Structured
