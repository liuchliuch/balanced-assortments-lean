import BalancedAssortments.NPStackComposition
import BalancedAssortments.NPStackReverseLink

namespace BalancedAssortments.NPStack.Composition
open NPStack
variable {K₁ Q₁ K₂ Q₂ : Type*} [DecidableEq K₁] [DecidableEq K₂]

def store (s : K₁ → List Bool) (t : K₂ → List Bool) (u : List Bool) : Stack K₁ K₂ → List Bool
  | .inl k => s k
  | .inr (.inl k) => t k
  | .inr (.inr _) => u

def cfg (q : Label Q₁ Q₂) (s : K₁ → List Bool) (t : K₂ → List Bool) (u : List Bool) :
    Config (Stack K₁ K₂) (Label Q₁ Q₂) := ⟨q,store s t u⟩

lemma first_run {P : Program K₁ Q₁} (R : Program K₂ Q₂) {n : ℕ} {c d : Config K₁ Q₁}
    (h : Run P n c d) (t : K₂ → List Bool) (u : List Bool) :
    Run (program P R) n (cfg (.first c.pc) c.stk t u) (cfg (.first d.pc) d.stk t u) := by
  apply h.relocate_exact firstStack Label.first Sum.inl_injective (first_extends P R)
  · exact ⟨rfl,fun _ => rfl⟩
  · exact ⟨rfl,fun _ => rfl⟩
  · intro k hk
    cases k with
    | inl k => exact False.elim (hk k rfl)
    | inr k => cases k <;> rfl

lemma secondStack_injective : Function.Injective (secondStack : K₂ → Stack K₁ K₂) := by
  intro a b h
  exact Sum.inl.inj (Sum.inr.inj h)

lemma second_run (P : Program K₁ Q₁) {R : Program K₂ Q₂} {n : ℕ} {c d : Config K₂ Q₂}
    (h : Run R n c d) (s : K₁ → List Bool) (u : List Bool) :
    Run (program P R) n (cfg (.second c.pc) s c.stk u) (cfg (.second d.pc) s d.stk u) := by
  apply h.relocate_exact secondStack Label.second secondStack_injective (second_extends P R)
  · exact ⟨rfl,fun _ => rfl⟩
  · exact ⟨rfl,fun _ => rfl⟩
  · intro k hk
    cases k with
    | inl k => rfl
    | inr k => cases k with
      | inl k => exact False.elim (hk k rfl)
      | inr u => rfl

lemma transfer_first (P : Program K₁ Q₁) (R : Program K₂ Q₂)
    (s : K₁ → List Bool) (t : K₂ → List Bool) (u : List Bool) :
    Run (program P R) (2*(s P.outputStack).length+1)
      (cfg (.transfer false .read) s t u)
      (cfg (.transfer false .done) (Function.update s P.outputStack []) t ((s P.outputStack).reverse++u)) := by
  have hc : CodeExtends reverseProgram (program P R)
      (reverseStackMap (firstStack P.outputStack) scratch) (.transfer false) :=
    transfer_extends P R false
  have hr := reverse_linked (firstStack P.outputStack) (scratch : Stack K₁ K₂) (by simp [firstStack,scratch])
    (Label.transfer false) hc (store s t u)
  have he : Function.update (Function.update (store s t u) (firstStack P.outputStack) []) scratch
      ((store s t u (firstStack P.outputStack)).reverse++store s t u scratch) =
      store (Function.update s P.outputStack []) t ((s P.outputStack).reverse++u) := by
    funext k
    cases k with
    | inl k => by_cases h : k=P.outputStack <;> simp [store,firstStack,scratch,Function.update,h]
    | inr k => cases k <;> simp [store,firstStack,scratch,Function.update]
  rw [he] at hr
  exact hr

lemma transfer_second (P : Program K₁ Q₁) (R : Program K₂ Q₂)
    (s : K₁ → List Bool) (t : K₂ → List Bool) (u : List Bool) :
    Run (program P R) (2*u.length+1)
      (cfg (.transfer true .read) s t u)
      (cfg (.transfer true .done) s (Function.update t R.inputStack (u.reverse++t R.inputStack)) []) := by
  have hc : CodeExtends reverseProgram (program P R)
      (reverseStackMap scratch (secondStack R.inputStack)) (.transfer true) :=
    transfer_extends P R true
  have hr := reverse_linked (scratch : Stack K₁ K₂) (secondStack R.inputStack) (by simp [secondStack,scratch])
    (Label.transfer true) hc (store s t u)
  have he : Function.update (Function.update (store s t u) scratch []) (secondStack R.inputStack)
      ((store s t u scratch).reverse++store s t u (secondStack R.inputStack)) =
      store s (Function.update t R.inputStack (u.reverse++t R.inputStack)) [] := by
    funext k
    cases k with
    | inl k => simp [store,secondStack,scratch,Function.update]
    | inr k => cases k with
      | inl k => by_cases h : k=R.inputStack <;> simp [store,secondStack,scratch,Function.update,h]
      | inr u => cases u; simp [store,secondStack,scratch,Function.update]
  rw [he] at hr
  exact hr

end BalancedAssortments.NPStack.Composition
