import BalancedAssortments.NPStackSourceBalanceCorrect

namespace BalancedAssortments.NPStack.SourceVerifier.Balance
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

def modifiedRegisters : List RowReg := [.price,.priceDen,.attraction,.attractionDen,.numerator,.term,.product]

lemma loaded_preserves (s : Registers) (x : Triple) (k : RowReg) (hk : k∉modifiedRegisters) : loaded s x k=s k := by
  cases k <;> simp_all [modifiedRegisters,loaded]

lemma effect_loaded_preserves (s : Registers) (x : Triple) (active : Bool) (k : RowReg)
    (hk : k∉modifiedRegisters) : effect active (loaded s x) k=s k := by
  have ht : k≠.term := by intro h;subst k;simp [modifiedRegisters] at hk
  have hp : k≠.product := by intro h;subst k;simp [modifiedRegisters] at hk
  rw [effect,VerifierCommands.balance_preserves _ _ _ ht hp,loaded_preserves s x k hk]

theorem loopValue_preserves (s u : Registers) (xs : List Triple)
    (h : loopValue s xs=some u) (k : RowReg) (hk : k∉modifiedRegisters) : u k=s k := by
  induction xs generalizing s with
  | nil => have he:=Option.some.inj h;subst s;rfl
  | cons x xs ih =>
    cases hs : stepValue s x with
    | none => simp [loopValue,hs] at h
    | some v =>
      have ht : loopValue v xs=some u := by simpa [loopValue,hs] using h
      obtain ⟨active,_,_,rfl⟩ := stepValue_some s x v hs
      exact (ih _ ht).trans (effect_loaded_preserves s x active k hk)

theorem loopValue_denominators (s u : Registers) (xs : List Triple)
    (h : loopValue s xs=some u) : (u .priceDen).2=(s .priceDen).2 ∧
      (u .attractionDen).2=(s .attractionDen).2 := by
  induction xs generalizing s with
  | nil => have he:=Option.some.inj h;subst s;exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    cases hs : stepValue s x with
    | none => simp [loopValue,hs] at h
    | some v =>
      have ht : loopValue v xs=some u := by simpa [loopValue,hs] using h
      obtain ⟨active,_,_,rfl⟩ := stepValue_some s x v hs
      have hh:=ih _ ht
      simpa only [effect,VerifierCommands.balance_preserves _ _ .priceDen (by decide) (by decide),
        VerifierCommands.balance_preserves _ _ .attractionDen (by decide) (by decide),loaded] using hh

end BalancedAssortments.NPStack.SourceVerifier.Balance
