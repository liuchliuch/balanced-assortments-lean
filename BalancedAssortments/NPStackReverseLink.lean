import BalancedAssortments.NPStackEmbedding
import BalancedAssortments.NPStackReverse

namespace BalancedAssortments.NPStack
variable {K Q : Type*} [DecidableEq K]

def reverseStackMap (source target : K) (b : Bool) : K := if b then target else source

lemma reverseStackMap_injective {source target : K} (hne : source≠target) :
    Function.Injective (reverseStackMap source target) := by
  intro a b h
  cases a <;> cases b <;> simp_all [reverseStackMap]

/-- A linked reversal on arbitrary surrounding stores, with every untouched
stack preserved and no assumption that the caller's other registers are empty. -/
theorem reverse_linked {P : Program K Q} (source target : K) (hne : source≠target)
    (labels : ReverseState → Q)
    (hcode : CodeExtends reverseProgram P (reverseStackMap source target) labels)
    (store : K → List Bool) :
    Run P (2*(store source).length+1) ⟨labels .read,store⟩
      ⟨labels .done,Function.update (Function.update store source []) target ((store source).reverse++store target)⟩ := by
  apply (reverse_run (store source) (store target)).relocate_exact
    (reverseStackMap source target) labels (reverseStackMap_injective hne) hcode
  · refine ⟨rfl,?_⟩
    intro k; cases k <;> rfl
  · refine ⟨rfl,?_⟩
    intro k
    cases k <;> simp [reverseStackMap,reverseConfig,twoStacks,Function.update,hne,Ne.symm hne]
  · intro k hk
    have hs : source≠k := hk false
    have ht : target≠k := hk true
    simp [Function.update,Ne.symm hs,Ne.symm ht]

end BalancedAssortments.NPStack
