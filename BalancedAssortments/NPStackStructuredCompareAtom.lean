import BalancedAssortments.NPStackStructuredAtoms
import BalancedAssortments.NPStackCompareNormalizeSound

noncomputable section
namespace BalancedAssortments.NPStack.Structured
open NPStack ComplexityTimeBinary
variable {K : Type*} [DecidableEq K]

def compareAtom (left right out : K) : Atom K :=
  let P := relocateProgram compareProgram (Macros.normalizeMap left right out) left out
  atomOfProgram P .done rfl (relocateProgram_noChoice _ _ _ _ compare_noChoice)

lemma compareAtom_exec (left right out : K) (hi : Function.Injective (Macros.normalizeMap left right out))
    (s : Store K) :
    Exec (.atom (compareAtom left right out)) s
      (Macros.writes s [(left,[]),(right,[]),(out,decide (value (s left)≤value (s right))::s out)])
      (2*max (s left).length (s right).length+3) := by
  let P := relocateProgram compareProgram (Macros.normalizeMap left right out) left out
  have hr := compare_truth_run (s left) (s right) (s out)
  have hneq (i j : CompareStack) (h : i≠j) :
      Macros.normalizeMap left right out i≠Macros.normalizeMap left right out j := fun he => h (hi he)
  have hlr : left≠right := hneq .left .right (by decide)
  have hlo : left≠out := hneq .left .result (by decide)
  have hro : right≠out := hneq .right .result (by decide)
  have he := hr.relocate_exact (Macros.normalizeMap left right out) id hi
    (relocateProgram_extends compareProgram _ left out)
    (c' := ⟨CompareState.readLeft .eq,s⟩)
    (d' := ⟨CompareState.done,Macros.writes s [(left,[]),(right,[]),(out,decide (value (s left)≤value (s right))::s out)]⟩)
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
  exact Exec.of_program_run P .done rfl (relocateProgram_noChoice _ _ _ _ compare_noChoice) he left out

end BalancedAssortments.NPStack.Structured
